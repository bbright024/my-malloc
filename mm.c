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

/* 
 * Basic constants and macros 
 */
#define WSIZE      8  	     	/* Word and header/footer size (bytes) */
#define DSIZE      16 		    /* Double word size (bytes) */
#define CHUNKSIZE  (1<<12)	    /* Extend heap by this amount (bytes) */
#define MIN_SIZE   4 * WSIZE	/* Minimum block size  */
#define SPLIT_MIN  4 * WSIZE	/* Minimum split block size */

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

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
#define GET_ROOT(heap, list_num)               ((char *)GET((heap) + ((list_num) * WSIZE)))
#define SET_ROOT(heap, list_num, new_start)    (PUT((heap) + ((list_num) * WSIZE), (new_start)))

static void * heap_list_p; 	/* points to prologue header  */
static void * heap_list_e; 	/* points to epilogue header  */
static void * heap_start;	/* points to first block in heap */
static void * free_list_r;	/* points to array of different list node starters */

/* function prototypes */

static void mm_print_free();
static void remove_block(void *bp);
static void add_block(void *bp);
static void * coalesce(void *bp);
static void * extend_heap(size_t words);
static void mm_print_block(char *bp);
static void mm_check_block(char *bp, int block_num);
static void mm_check();
int mm_init(void);
void * mm_malloc(size_t size);
void mm_free(void *bp);
void *mm_realloc(void *ptr, size_t size);


/* 
 *  Removes a node from the free list it was in, stitching together the successor 
 *  and predecessor nodes.
 */
static void remove_block(void *bp)
{
	char *pred_node;
	char *succ_node;

	pred_node = PRED_FREP(bp);
	succ_node = SUCC_FREP(bp);

	if((pred_node == NULL) && (succ_node == NULL))  /* case 1: bp was only node in list */
		{
			SET_ROOT(free_list_r, 0, NULL);
			//			free_list_r = NULL;
		}
	else if(pred_node == NULL) 	/* case 2: bp was first node in list */
		{
			SET_ROOT(free_list_r, 0, succ_node);
			//			free_list_r = succ_node;
		    PUT(PRED(succ_node), NULL);
		}
	else if(succ_node == NULL) 	/* case 3: bp was last node in list */
		{
			PUT(SUCC(pred_node), NULL);
		}
	else 						/* case 4: bp was a mid node */
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
	PUT(PRED(bp), NULL);
	PUT(SUCC(bp), NULL);

	char *old_root = GET_ROOT(free_list_r, 0);  //free_list_r;

	SET_ROOT(free_list_r, 0, bp);
	//	free_list_r = bp;

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

	prev_blk_alloc = GET_PREV_ALLOC(HDRP(bp));
	
	next_blk = NEXT_BLKP(bp);
	next_blk_alloc = GET_ALLOC(HDRP(next_blk));
	
	bp_size = GET_SIZE(HDRP(bp));

	/* 
	 * each case needs to accomplish 2 tasks:
	 *     1: stitch any changes in free list
	 *     2: change headers of affected blocks
	 */
	
	if(prev_blk_alloc && next_blk_alloc)        /* case 1: bp is in-between 2 used blks */
		{
			/* nothing needs to be changed, can freely add block bp to free list */
			add_block(bp);
		}
	
	else if(!prev_blk_alloc && next_blk_alloc)	/* case 2: free prior blk but used next blk */
		{
			prev_blk = PREV_BLKP(bp);
			
			/* task 1: nothing changes in singly linked list, node just gets bigger */

			/* tast 2: prior block eats bp */
			bp_size += GET_SIZE(HDRP(prev_blk));

			bp = prev_blk; 		/* bp is now the prior block */

			/* the block prior to the prior is always allocated because no 2 adj free blocks */
			PUT(HDRP(bp), PACK(bp_size, 2, 0));
			PUT(FTRP(bp), PACK(bp_size, 2, 0));
		}
	
	else if(prev_blk_alloc && !next_blk_alloc)  /* case 3: used prior blk but free next blk */
		{
			/* tast 1: change location of node pointers */
			PUT(PRED(bp), NULL);
			PUT(SUCC(bp), NULL);

			PUT(PRED(bp), PRED_FREP(next_blk));
			PUT(SUCC(bp), SUCC_FREP(next_blk));

			/* task 2: change header & footer in bp */
			bp_size += GET_SIZE(HDRP(next_blk));
			PUT(HDRP(bp), PACK(bp_size, 2, 0));
			PUT(FTRP(bp), PACK(bp_size, 2, 0));
		}
	
	else						                /* case 4: both next blk and prior blk are free */
		{
			prev_blk = PREV_BLKP(bp);
			
			/* task 1: stitch out the next block, combine the latter two blocks into the earliest */
			remove_block(next_blk);

			/* task 2: set header and footer of the new coalesced block */
			bp_size += GET_SIZE(HDRP(prev_blk)) + GET_SIZE(HDRP(next_blk));
			bp = prev_blk;
			PUT(HDRP(bp), PACK(bp_size, 2, 0));
			PUT(FTRP(bp), PACK(bp_size, 2, 0));
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

	/* coalesce if previous block was free, otherwise add the block and return */
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

/* searches the heap for an open space of size and returns a pointer to the first word 
 * in the block following the header.  
 */
static void * find_fit(size_t size)
{
	char *bp;// = GET_ROOT(free_list_r, 0);
	//mm_print_free();
	//	while(bp != NULL)
	for(bp = heap_list_p; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp))
		{
			if(!GET_ALLOC(HDRP(bp)) && (size < GET_SIZE(HDRP(bp))))
					return bp;

			//		bp = SUCC_FREP(bp);
		}

    return NULL; 		/* no blocks available */
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
	 *  two tasks to fulfill
	 *    1: remove allocated block from free list
	 *    2: change header in current bp and header in following block
	 */

	/* task 1 */
	remove_block(bp);
	
	
	if(internal_frag > SPLIT_MIN) 	/* case 1: too much internal fragmentation, will split the block */
		{
			/* task 2 */
			PUT(HDRP(next_blk), PACK(next_blk_size, 0, 1));
			PUT(HDRP(bp), PACK(size, 2, 1));

			char *split_blk;
			split_blk = NEXT_BLKP(bp);
			PUT(HDRP(split_blk), PACK(internal_frag, 2, 0));
			PUT(FTRP(split_blk), PACK(internal_frag, 2, 0));
			/* no need for coalescing, this split block stands alone */
			add_block(split_blk);
		}
	else						/* case 2: not splitting block */
		{
			/* tast 2 */
			PUT(HDRP(next_blk), PACK(next_blk_size, 2, 1));
			PUT(HDRP(bp), PACK(old_size, 2, 1));
		}

	return bp;
}


/* 
 * prints a graphical image of the free list
 */
static void mm_print_free()
{
	/* 
	char *bp = free_list_r;
	size_t size;
	size_t alloc;
	size_t prev_alloc;
	char *succ;
	char *pred;
	int i = 0;
	printf("\n\n\n");
	while(bp != NULL)
		{
			size = GET_SIZE(HDRP(bp));
			alloc = GET_ALLOC(HDRP(bp));
			prev_alloc = GET_PREV_ALLOC(HDRP(bp));
			succ = SUCC_FREP(bp);
			pred = PRED_FREP(bp);
			
			printf("\n[Head][BP = %p ", bp);
			printf(" Successor = %#lx ][Predecessor = %#lx ]", (unsigned long)succ, (unsigned long)pred);
			printf("[ ---- BLOCK SIZE %d  ---- ]\n", size);

			i++;
			bp = SUCC_FREP(bp);
		}
	printf("\n\n There are %d nodes in free list\n", i);
	 NNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNNnnnn*/

}
static void mm_print_block(char * bp)
{

	/* 





	size_t prev_allocH = GET_PREV_ALLOC(HDRP(bp));
    size_t sizeH = GET_SIZE(HDRP(bp));
    int allocH = GET_ALLOC(HDRP(bp));
	printf("\n[Head-- PrevAll = %d -- All = %d ]", prev_allocH, allocH);
    printf("[ ---- BLOCK SIZE %d  ---- ]", sizeH);
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
		}
    int ali = (unsigned int)bp % WSIZE;
    if(ali)
		{
			printf("\nalignment is off in block %d, the modulus of bp and WSIZE is %d\n", block_num, ali);
			sleep(1);
		}
    return;

}

static void mm_check()
{


	//size_t heap_size = mem_heapsize(); /* number of bytes in heap */
    int total_blocks = 0;			/* all blocks in  */
    int free_blocks = 0;		    /*  */
	char *bp;
	//size_t payloads = tot_payload_request;

	//	printf("\n\n\n ");
    for (bp = heap_list_p; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp))
	{
	    if(!GET_ALLOC(HDRP(bp)))
			free_blocks++;
			
		//		myprintblock(bp);
	    mm_check_block(bp, total_blocks);
		total_blocks++;
	}
	//		mm_print_free();
	//	printf("\nFirst byte heap = %p    Last byte heap = %p    Size of heap = %d\n", heap_list_p,
	// heap_list_e, heap_size);
	//		printf("Total free blocks = %d\nTotal blocks = %d\n", free_blocks, total_blocks);


		//	sleep(1);    
}

/* 
 * mm_init - initialize the malloc package.
  */
int mm_init(void)
{
	/* create beginning of heap, must be DSIZE aligned so grabbed 48 bytes */
	if((heap_list_p = mem_sbrk(6 * WSIZE)) == (void *)-1)
		return -1;

	/* sets the array of free lists to be at start of heap, before prologue */
	free_list_r = heap_list_p;

	/* Space for 3 words here for 3 different free list root pointers */
	PUT(heap_list_p + (0 * WSIZE), NULL);
	PUT(heap_list_p + (1 * WSIZE), NULL);
	PUT(heap_list_p + (2 * WSIZE), NULL);

	PUT(heap_list_p + (3 * WSIZE), PACK(DSIZE, 2, 1)); /* Prologue header */
	PUT(heap_list_p + (4 * WSIZE), PACK(DSIZE, 2, 1)); /* Prologue footer */
	
	PUT(heap_list_p + (5 * WSIZE), PACK(0, 2, 1));     /* Epilogue footer */

	heap_list_p += (4 * WSIZE);	                      
	heap_list_e = HDRP(NEXT_BLKP(heap_list_p));

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

	size_t adjust_size; 		/* size after alignment */
	size_t extend_size;			/* size to extend heap, if necessary */
	char *bp;

	/* adjust block size to include the 4 word overhead (MIN_SIZE) and alignment reqs */
	if(size <= MIN_SIZE)
		{
			adjust_size = 2 * MIN_SIZE;
		}
	else
		{
			adjust_size = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);
		}

	/* check for a suitable free block */
	if((bp = find_fit(adjust_size)) != NULL)
		{
			place(bp, adjust_size);
			mm_check();
			return bp;
		}

	/* No fit found.  Get memory, then place block. */
	extend_size = MAX(adjust_size, CHUNKSIZE);
	if((bp = extend_heap(extend_size/WSIZE)) == NULL)
		return NULL;
	
	place(bp, adjust_size);
	mm_check();
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
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
	/* 
	if(ptr == NULL)
		return mm_malloc(size);
	if(size == 0)
		{
			mm_free(ptr);
			return;
		}
		 */
	/* ptr must have been returned by an earlier call, so change the size of
     * the block to be size and return addy of the new block. 
	 * contents of the new block are same as old ptr block up to min(oldsize, size)
	 * 
	 */

    void *oldptr = ptr;
    void *newptr;
    size_t copySize;
    newptr = mm_malloc(size);
    if (newptr == NULL)
      return NULL;
    copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
    if (size < copySize)
      copySize = size;
    memcpy(newptr, oldptr, copySize);
    mm_free(oldptr);
    return newptr;


	

	
}














