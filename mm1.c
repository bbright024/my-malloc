/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 * 
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "bbbteam",
    /* First member's full name */
    "Brian Bright",
    /* First member's email address */
    "tychocel@u.washington.edu",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

/* 
 * Basic constants and macros 
 */
#define WSIZE      8  	     	/* Word and header/footer size (bytes) */
#define DSIZE      16 		    /* Double word size (bytes) */
#define CHUNKSIZE  (1<<8)	    /* Extend heap by this amount (bytes) */
#define MIN_SIZE   (4 * WSIZE)	/* Minimum block size  */
#define SPLIT_MIN  (1<<6)	/* Minimum split block size */
#define TOT_LISTS  16			/* Total number of explicit lists */
#define MIN_LIST_SIZE ((SPLIT_MIN)<<2)	/* The smallest power of 2 list */
#define MAX_LIST_SIZE ((MIN_LIST_SIZE)<<(TOT_LISTS)) /* Maximum power of 2 in the list, anything higher in here */
#define P_AND_E_SIZE  (3)		   /* Total words of the prologue and epilogue */


#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/* grabs higher value of 2 args */
#define MAX(x, y) ((x) > (y) ? (x) : (y))

/* Pack a size, previous block allocated bit, and allocated bit into a word */
#define PACK(size, prev_alloc, alloc)   ((size) | (prev_alloc) | (alloc))

/* Read and write 8 byte unsigned int at address p */
#define GET(p)              (*(size_t *)(p))
#define PUT(p, val)         (*(size_t *)(p) = (size_t)(val))

/* Read and write 8 bytes at address p */
//#define GET_PTRP(p)         (*(size_t *)(p))
//#define PUT_PTRP(p, val)    (*(size_t *)(p) = (size_t)(val))

/* Read the size and allocated status fields from address p */
#define GET_SIZE(p)         (GET(p) & ~0x7)
#define GET_ALLOC(p)        (GET(p) & 0x1)
#define GET_PREV_ALLOC(p)   (GET(p) & 0x2)

/* Change only a certain bit in status field */
#define CHANGE_SIZE(p, val)  (PUT((p), PACK((val), GET_PREV_ALLOC(p), GET_ALLOC(p))))  
#define CHANGE_ALLOC(p, val) (PUT((p), PACK(GET_SIZE(p), GET_PREV_ALLOC(p), (val))))  
#define CHANGE_PREV(p, val)  (PUT((p), PACK(GET_SIZE(p), (val), GET_ALLOC(p))))  

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)            ((char *)(bp) - WSIZE)
#define FTRP(bp)            ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp in free list, compute address containing 
   successor & predecessor block address */
#define SUCC(bp)            ((char *)(bp))
#define PRED(bp)            ((char *)(bp) + WSIZE)

/* Given block ptr bp, compute address of next and prev blocks */
#define NEXT_BLKP(bp)       ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)       ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

/* Given block ptr bp in free list, compute address of next and prev free list blocks */
#define SUCC_FREP(bp)       ((char *)GET(bp))
#define PRED_FREP(bp)       ((char *)GET(PRED(bp)))

/* Get and set the first node in a free list of list_num */
#define GET_ROOT(heap, list)              ((char *)GET((heap) + ((list) * WSIZE)))
#define SET_ROOT(heap, list, new_root)    (PUT((heap) + ((list) * WSIZE), (new_root)))

static void * heap_list_p; 	/* points to prologue header  */
static void * heap_list_e; 	/* points to epilogue header  */
static void * heap_start;	/* points to first block in heap */
static void * free_list_r;	/* points to array of different list node starters */

/* function prototypes */

static void mm_print_free();
static void remove_block(void *bp);
static void add_block(void *bp);
static void *coalesce(void *bp);
static void *extend_heap(size_t words);
static void mm_print_block(char *bp);
static void mm_check_block(char *bp, int block_num);
static void mm_check();
static int get_list(size_t size);
static size_t adjust_size(size_t size);
static void *find_fit(size_t size);
static void *place(void *bp, size_t size);
int mm_init(void);
void * mm_malloc(size_t size);
void mm_free(void *bp);
void *mm_realloc(void *ptr, size_t size);

void *seg_free_lists[TOT_LISTS];


/* 
 * returns the list that size should fit in, where a list is a range of
 * powers of 2.
 */
static int get_list(size_t size)
{
	int i = 0;
	int x = size;//MIN_LIST_SIZE;

	while( (x > 0) && (i < (TOT_LISTS-1)) )
	//	for(i = 0; (x < size) && ; i++);
		{
			i++;
			x /= 2;
		}
	return i;
}

/* 
 *  Removes a node from the free list it was in, stitching together the successor 
 *  and predecessor nodes.
 */
static void remove_block(void *bp)
{
	int list_num = get_list(GET_SIZE(HDRP(bp)));
	char *pred_node;
	char *succ_node;

	pred_node = PRED_FREP(bp);
	succ_node = SUCC_FREP(bp);

	if((pred_node == NULL) && (succ_node == NULL))  /* case 1: bp was only node in list */
		{
			SET_ROOT(free_list_r, list_num, NULL);
		}

	else if(pred_node == NULL) 	                    /* case 2: bp was first node in list */
		{
			SET_ROOT(free_list_r, list_num, succ_node);
		    PUT(PRED(succ_node), NULL);
		}

	else if(succ_node == NULL) 	                   /* case 3: bp was last node in list */
		{
			PUT(SUCC(pred_node), NULL);
		}

	else 						                  /* case 4: bp was a mid node */
		{
			/* stitch nodes together */
			PUT(SUCC(pred_node), succ_node);
			PUT(PRED(succ_node), pred_node);
		}

	/* zero out the current block, in case space not overwritten before returned to list */
	PUT(SUCC(bp), NULL);
	PUT(PRED(bp), NULL);
}

/* 
 *  adds block at bp to beginnning of a free list 
 */
static void add_block(void *bp)
{
	int list_num = get_list(GET_SIZE(HDRP(bp)));

	/* zero out space where pointers will be placed in bp */
	PUT(PRED(bp), NULL);
	PUT(SUCC(bp), NULL);

	char *old_root = GET_ROOT(free_list_r, list_num);

	SET_ROOT(free_list_r, list_num, bp);

	if(old_root == NULL) 		/* list was empty */
		return;

	/* stitch the new root to the old root */
	PUT(SUCC(bp), old_root);
	PUT(PRED(old_root), bp);
}

/* 
 * combines empty blocks around the given pointer to a block
 */
static void * coalesce(void * bp)
{
	size_t prev_blk_alloc;
	size_t next_blk_alloc;
	size_t bp_size;
	char *prev_blk;
	char *next_blk;
	size_t list_num;
	size_t other_blk_size;
	
	prev_blk_alloc = GET_PREV_ALLOC(HDRP(bp));
	
	next_blk = NEXT_BLKP(bp);
	next_blk_alloc = GET_ALLOC(HDRP(next_blk));
	
	bp_size = GET_SIZE(HDRP(bp));

	/* 
	 * each case needs to accomplish 2 tasks:
	 *     1: stitch any changes in free list
	 *     2: change headers of affected blocks
	 */
	
	/* case 1: bp is in-between 2 used blks */
	if(prev_blk_alloc && next_blk_alloc)        
		{
			/* nothing needs to be changed, can freely add block bp to free list */
			add_block(bp);
		}
	
	/* case 2: free prior blk but used next blk */
	else if(!prev_blk_alloc && next_blk_alloc)	
		{
			prev_blk = PREV_BLKP(bp);
			other_blk_size = GET_SIZE(HDRP(prev_blk));
			bp_size += other_blk_size;

			list_num = get_list(other_blk_size);

			/* only remove from list if new size will push the block out of it's current class */
	
			if((1 << list_num) >  bp_size) 
				{
					bp = prev_blk;
					PUT(HDRP(bp), PACK(bp_size, 2, 0));
					PUT(FTRP(bp), PACK(bp_size, 2, 0));
					return bp;
				}
			else
				{
					remove_block(prev_blk);
					/* tast 2: prior and bp become one */
					bp = prev_blk;
					/* the block in front of prev is allocated because no 2 adj free blocks */
					PUT(HDRP(bp), PACK(bp_size, 2, 0));
					PUT(FTRP(bp), PACK(bp_size, 2, 0));
					/* task 1 part 2: insert new combo block into a list */
					add_block(bp);
					return bp;
				}
		}
	
	/* case 3: used prior blk but free next blk */
	else if(prev_blk_alloc && !next_blk_alloc) 
		{
			bp_size += GET_SIZE(HDRP(next_blk));

			/* check to see if blocks remain in same free list afterwards */
			/* task 1: part 1: remove next_blk from it's list */
			remove_block(next_blk);
			
			/* task 2: change header & footer in bp */

			PUT(HDRP(bp), PACK(bp_size, 2, 0));
			PUT(FTRP(bp), PACK(bp_size, 2, 0));

			/* finish task 1 */
			add_block(bp);
		}
	
	/* case 4: both next blk and prior blk are free */
	else	
		{
			prev_blk = PREV_BLKP(bp);
			
			/* task 1: part1: stitch out both surrounding blocks */
			remove_block(next_blk);

			bp_size += GET_SIZE(HDRP(prev_blk)) + GET_SIZE(HDRP(next_blk));

			list_num = get_list(GET_SIZE(HDRP(prev_blk)));

			
			if( (1 << list_num) > bp_size)
				{
					bp = prev_blk;
					PUT(HDRP(bp), PACK(bp_size, 2, 0));
					PUT(FTRP(bp), PACK(bp_size, 2, 0));
					return bp;
				}
			else
				{
					
					remove_block(prev_blk);

					/* task 2: set header and footer of the new coalesced block */
			
					bp = prev_blk;
					PUT(HDRP(bp), PACK(bp_size, 2, 0));
					PUT(FTRP(bp), PACK(bp_size, 2, 0));

					/* task 1 part 2: add the new combo block */
					add_block(bp);
									}
		}
	
	return bp;
}

/* 
 * Extends heap by the multiplicand of WSIZE and words argument.
 */
static void * extend_heap(size_t words)
{
	char *bp;
	size_t size;
	
	/* saves allocation status of last block before epilogue */
	size_t end_alloc = GET_PREV_ALLOC(heap_list_e);

	/* allocate an even number of words to maintain alignment */
	size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE;

	if((long)(bp = mem_sbrk(size)) == -1)
		return NULL;
	
	PUT(HDRP(bp), PACK(size, end_alloc, 0));
	PUT(FTRP(bp), PACK(size, end_alloc, 0));
	PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 0, 1));
	heap_list_e = HDRP(NEXT_BLKP(bp));

	/* coalesce if prev block was free, otherwise add the block and return */
	if(!end_alloc)
		{
			return coalesce(bp);
		}
	else
		{
			add_block(bp);
			return bp;
		}
}

/* 
 * searches all lists whose block sizez are greater than size for a free block 
 * and returns a pointer to the word following the header of the block.
 * returns null if no fit is found in the current heap.
 * worst case O(n^2), could be a bottleneck
 */
static void * find_fit(size_t size)
{
	int list_num = get_list(size);
	char *bp;
	int i = list_num;

	while(i < TOT_LISTS)
		{
			bp = GET_ROOT(free_list_r, i);
			while(bp != NULL)
				{
					if( size <= GET_SIZE(HDRP(bp)) )
						return bp;
					
					bp = SUCC_FREP(bp);
				}
					i++;
		}
    return NULL;
}

/* 
 * sets up the header in an allocated block and changes flags in next block
 * also splits block if possible.
 * Assumes that passed in size is less than or equal to size already set in bp header.
 */
static void * place(void *bp, size_t size)
{
	
	char *next_blk;
	size_t next_blk_size;

	/* next block & prev block are always allocated bc of coalescing */
	next_blk = NEXT_BLKP(bp);
	next_blk_size = GET_SIZE(HDRP(next_blk));
	
	size_t old_size;
	size_t internal_frag;

	old_size = GET_SIZE(HDRP(bp));
	internal_frag = old_size - size;

	/* 
	 * note: could add a "zero out" flag into one of the free header bits that 
	 * tells "place" to zero all the bits in the newly allocated block before returning
	 */
	
	remove_block(bp);
	
	/* case 1: too much internal fragmentation, will split the block */
	if(internal_frag > SPLIT_MIN) 	
		{
			PUT(HDRP(next_blk), PACK(next_blk_size, 0, 1));
			PUT(HDRP(bp), PACK(size, 2, 1));

			/* establish the split blk */
			char *split_blk;
			split_blk = NEXT_BLKP(bp);
			PUT(HDRP(split_blk), PACK(internal_frag, 2, 0));
			PUT(FTRP(split_blk), PACK(internal_frag, 2, 0));

			/* no need for coalescing, split blk is between two allocated blks */
			add_block(split_blk);
		}
	
	/* case 2: not splitting block */
	else						
		{
			PUT(HDRP(next_blk), PACK(next_blk_size, 2, 1));
			PUT(HDRP(bp), PACK(old_size, 2, 1));
		}

	return bp;
}


/* 
 * prints a graphical image of EVERY free list
 */
static void mm_print_free()
{
	
	char *bp;
	size_t size;
	size_t alloc;
	size_t prev_alloc;
	char *succ;
	char *pred;
	int tot_nodes;
	printf("\n\n\n");

	int i = 0;
	for(; i < TOT_LISTS; i++)
		{
			tot_nodes = 0;
			//			printf("\nFREE LIST %d\n", i+1);
			bp = GET_ROOT(free_list_r, i);
		
			while(bp != NULL)
				{
					/* grab data about the block... would be a lot nicer with structs */
					size = GET_SIZE(HDRP(bp));
					alloc = GET_ALLOC(HDRP(bp));
					prev_alloc = GET_PREV_ALLOC(HDRP(bp));
					succ = SUCC_FREP(bp);
					pred = PRED_FREP(bp);
					
					//printf("[Head][BP = %p ", bp);
					//printf(" Succ = %p ][Pred = %p]", succ, pred);
					//printf("[ ---- BLOCK SIZE %d  ---- ]\n", size);
					
					
					tot_nodes++;
					bp = SUCC_FREP(bp);
				}
			printf("There are %d nodes in free list %d\n", tot_nodes, i+1);
		}

}
static void mm_print_block(char * bp)
{

	/* grab meta data of block */
	size_t prev_alloc = GET_PREV_ALLOC(HDRP(bp));
    size_t size = GET_SIZE(HDRP(bp));
    int alloc = GET_ALLOC(HDRP(bp));
	printf("\n[Head-- PrevAll = %d -- All = %d ]", prev_alloc, alloc);
    printf("[ -- BLOCK SIZE %d  -- ]\n", size);
	/* 
	

	if(!allocH)
		{
			size_t prev_allocF = GET_PREV_ALLOC(FTRP(bp));
			size_t sizeF = GET_SIZE(FTRP(bp));
			int allocF = GET_ALLOC(FTRP(bp));
			printf("[F- Size = %d -- PrevAl = %d -- All = %d]", sizeF, prev_allocF, allocF);
		}
	else
		printf("\n");
		 */
}

/* consistency checking, make sure all headers and footers have equal block sizes/allocated bits,
 * and all blocks are properly aligned.
 */
static void mm_check_block(char * bp, int block_num)
{
	size_t sizeH = GET_SIZE(HDRP(bp));
    size_t allocH = GET_ALLOC(HDRP(bp));
	size_t prev_alloc = GET_PREV_ALLOC(HDRP(bp));
	
	if(!allocH)
		{
			size_t sizeF = GET_SIZE(FTRP(bp));
			size_t allocF = GET_ALLOC(FTRP(bp));
			size_t prev_alloc_f = GET_PREV_ALLOC(FTRP(bp));
			char *succ = SUCC_FREP(bp);
			char *pred = PRED_FREP(bp);

			if(sizeH != sizeF)
				{
					printf("\nHeader size does not equal footer size\n");
					printf("%d    %d  block = %d\n",  sizeH, sizeF, block_num);
					sleep(1);
				}
			if(allocF != allocH)
				{
					printf("\nAllocs do not match in block %d\n", block_num);
					sleep(1);
				}
			if(prev_alloc != prev_alloc_f)
				{
					printf("\nPrev_allocs do not match in block %d! H %d F %d  \n",
						   block_num, prev_alloc, prev_alloc_f);
					if(GET_SIZE(HDRP(NEXT_BLKP(bp))) == 0)
						printf("yup right before epilogue");
					sleep(1);
		 		}
			if(succ == pred && succ != NULL)
				{
					printf("\nCircular list error\n");
					sleep(1);
				}
			
		}
    int ali = (unsigned int)bp % WSIZE;
    if(ali)
		{
			printf("\nalign off in block %d, mod of bp and WSIZE is %d\n", block_num, ali);
			sleep(1);
		}
    return;

}

static void mm_check()
{

    int total_blocks = 0;			
    int free_blocks = 0;		    
	char *bp;

	//	printf("\n\nNEW CHECK\n\n");
	mm_print_free();

	for (bp = heap_list_p; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp))
		{

			if(!GET_ALLOC(HDRP(bp)))
				free_blocks++;
			
			//			mm_print_block(bp);
			mm_check_block(bp, total_blocks);
			total_blocks++;

		}

	
	//printf("\nPRO = %p    EPI = %p    HEAPSIZE = %d\n", heap_list_p, heap_list_e, mem_heapsize());
	//	printf("Total free blocks = %d\nTotal blocks = %d\n", free_blocks, total_blocks);
	//sleep(1);    
}

/* 
 * mm_init - initialize the malloc package.
 * create beginning of heap, must be able to fit a root for each free list 
 * in front of the prologue and epilogue, and align everything properly.
 * might have to check back later and properly align the start of the prologue to DSIZE.
 */
int mm_init(void)
{

	/* check if enough memory */
	if( (heap_list_p = mem_sbrk( (TOT_LISTS + P_AND_E_SIZE) * WSIZE)) == (void *)-1 )
		return -1;

	/* set start address of free list array */
	free_list_r = heap_list_p;

	/* set heap_list_p to the word following prologue header and free list roots */
	heap_list_p += ((TOT_LISTS + 1) * WSIZE);

	/* create space for TOT_LISTS number of words */
	int i = 0;
	while(i < TOT_LISTS)
		{
			PUT(free_list_r + (i * WSIZE), NULL);
			i++;
		}
	
	PUT(HDRP(heap_list_p), PACK(DSIZE, 2, 1)); /* Prologue header */
	PUT(FTRP(heap_list_p), PACK(DSIZE, 2, 1)); /* Prologue footer */

	heap_list_e = HDRP(NEXT_BLKP(heap_list_p));
	PUT(heap_list_e, PACK(0, 2, 1));           /* Epilogue footer */

	if((heap_start = extend_heap(CHUNKSIZE/WSIZE)) == NULL)
		return -1;

	return 0;
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
	if(size == 0)
		return NULL;

	size_t adj_size; 		/* size after alignment */
	size_t extend_size;			/* size to extend heap, if necessary */
	char *bp;

	adj_size = adjust_size(size);

	/* check for a suitable free block */
	if( (bp = find_fit(adj_size)) != NULL )
		{
			place(bp, adj_size);
			//		mm_check();
			return bp;
		}

	/* No fit found.  Get memory, then place block. */
	extend_size = MAX(adj_size, CHUNKSIZE);
	if( (bp = extend_heap(extend_size/WSIZE)) == NULL )
		return NULL;
	
	place(bp, adj_size);
	//	mm_check();
	return bp;
}

/*
 * mm_free - Freeing a block at ptr
 *      changes allocation value of current block to 0,
 *      changes next block's previous allocation bits to 0,
 *      and runs immediate coalescing.
 */
void mm_free(void *bp)
{
	size_t bp_size;

	char *next_blk;
	
	/* make sure these stay the same as before. could optimize this away with macros */
	size_t prev_blk_alloc;
	size_t next_blk_size;
	size_t next_blk_alloc; 		/* if next blk is unallocated, need to change footer too */
	
	bp_size = GET_SIZE(HDRP(bp));

	next_blk = NEXT_BLKP(bp);
	
	prev_blk_alloc = GET_PREV_ALLOC(HDRP(bp));
	next_blk_size = GET_SIZE(HDRP(next_blk));
	next_blk_alloc = GET_ALLOC(HDRP(next_blk));
	
	PUT(HDRP(bp), PACK(bp_size, prev_blk_alloc, 0));
	PUT(FTRP(bp), PACK(bp_size, prev_blk_alloc, 0));

	PUT(HDRP(next_blk), PACK(next_blk_size, 0, next_blk_alloc));

	if(!next_blk_alloc)
		PUT(FTRP(next_blk), PACK(next_blk_size, 0, 0));

	coalesce(bp);
}
/* 
 *  corrects the passed in size to be of a size suitable for a block.
 *  needs to be aligned and able to hold a header, footer, and two pointers.
 */
static size_t adjust_size(size_t size)
{
	size_t adjust_size;
	
	if(size <= MIN_SIZE)
		{
			adjust_size = 2 * MIN_SIZE;
		}
	else
		{
			adjust_size = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);
		}
	
	return adjust_size;
}
/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *bp, size_t size)
{
	
	if(bp == NULL)
		return mm_malloc(size);
	if(size == 0)
		{
			mm_free(bp);
			return NULL;
		}
		 
	/* ptr must have been returned by an earlier call, so change the size of
     * the block to be size and return addy of the new block. 
	 * contents of the new block are same as old ptr block up to min(oldsize, size)
	 * 
	 */

	/* 
	void *old_bp = bp;
	size_t old_size = GET_SIZE(HDRP(bp));
	void *new_bp;
	size_t split_size;
	size_t adj_size;
	char *split_bp;
	size_t old_prev;

	adj_size = adjust_size(size);
	
	if(old_size == adj_size)
		return bp;


	if(old_size > adj_size)
		{
			old_prev = GET_PREV_ALLOC(HDRP(old_bp));
			split_size = old_size - adj_size;
			

			PUT(HDRP(old_bp), PACK(adj_size, old_prev, 1));

			split_bp = NEXT_BLKP(old_bp);
			
			PUT(HDRP(split_bp), PACK(split_size, 2, 0));
			PUT(FTRP(split_bp), PACK(split_size, 2, 0));
			coalesce(split_bp);
			
			return old_bp;
		}

	else
		{
			new_bp = mm_malloc(size);
			if(new_bp == NULL)
				return NULL;
			
			memcpy(new_bp, old_bp, size);
			mm_free(old_bp);
			return new_bp;
		}
	
 */

    void *oldptr = bp;
    void *newptr;	
    size_t copySize;
	copySize = GET_SIZE(HDRP(bp));

    newptr = mm_malloc(size);
    if (newptr == NULL)
      return NULL;
	
    if (size < copySize)
      copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;

	
}

