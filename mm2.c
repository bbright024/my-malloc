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

/* Read and write 4 bytes at address p */
#define GET(p)              (*(unsigned int *)(p))
#define PUT(p, val)         (*(unsigned int *)(p) = (val))

/* Read and write 8 bytes at address p */
#define GET_PTRP(p)         (*(size_t *)(p))
#define PUT_PTRP(p, val)    (*(size_t *)(p) = (size_t)(val))

/* Read the size and allocated status fields from address p */
#define GET_SIZE(p)         (GET(p) & ~0x7)
#define GET_ALLOC(p)        (GET(p) & 0x1)
#define GET_PREV_ALLOC(p)   (GET(p) & 0x2)
	
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
#define SUCC_FREP(bp)       ((char *)GET_PTRP(bp))
#define PRED_FREP(bp)       ((char *)GET_PTRP(PRED(bp)))

static void * heap_list_p; 	/* points to prologue header  */
static void * heap_list_e; 	/* points to epilogue header  */
static void * heap_start;	/* points to first block in heap */
static void * free_list_r;	/* Root node of free list */
/* Heap check variables */

//static size_t tot_payload_request;
//static size_t internal_frag;

/* function prototypes */

void mm_print_free();

/* 
 *  removes the block at bp from the free list and rearranges the pointers
 *  in that block
 */
static void remove_block(void *bp)
{

	
	char *pred = PRED_FREP(bp);         /* block prior to bp in free list */
	char *succ = SUCC_FREP(bp);       /* pointer to block following bp in free list */

	/* zero out the pointers */
		
	if((pred == NULL)  && (succ == NULL)) /* case 1: bp was only block */
		{
			free_list_r = NULL;           /* assign the root to point to block after bp */
			return;
		}

	else if(pred == NULL) 		/* case 2: bp was first block of n blocks */
		{
			free_list_r = succ;
		}
    else if(succ == NULL) 		/* case 3: bp was last block of n blocks*/
		{
			PUT_PTRP(SUCC(pred), NULL);
		}

	else						/* case 4: bp was in between 2 blocks */
		{
			PUT_PTRP(SUCC(pred), succ);
			PUT_PTRP(PRED(succ), pred);
		}

}

/* 
 *  adds block at bp to the free list and rearranges pointers
 *
 */
static void add_block(void *bp)
{
	/* zero out ptr areas */
	PUT_PTRP(PRED(bp), NULL);
	PUT_PTRP(SUCC(bp), NULL);

	char *old_first = free_list_r; /* first free block in list */

	/* set up new first block in free list */
	free_list_r = bp;
	
	if(old_first == NULL)			 /* list was empty */
		return;

	PUT_PTRP(SUCC(bp), old_first);
	PUT_PTRP(PRED(old_first), bp);	/* bp now has a pointer back to list_p  */
}

/* 
 * combines empty blocks around the given pointer to a block
 */
static void * coalesce(void * bp)
{
    size_t size = GET_SIZE(HDRP(bp));  /* allocations and sizes of the 3 blocs involved */
	char *next_bp;
	char *prev_bp;
    int prev_alloc = GET_PREV_ALLOC(HDRP(bp));
    int next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t prev_size;
    size_t next_size;
	size_t pre_pre_alloc;	/* only use if starting from at least heap_start; wont work with hlp */

	
    if (prev_alloc && next_alloc)      /* case 1, no free blocks to coalesce */
		{
			return bp;
		}
    else if(prev_alloc && !next_alloc) /* case 2; occupied previous block, empty next block */
	{
		next_bp = NEXT_BLKP(bp);
		
		/* fix up the implicit stuff */
		size += GET_SIZE(HDRP(next_bp));
	    PUT(HDRP(bp), PACK(size, 2, 0));
	    PUT(FTRP(bp), PACK(size, 2, 0));
		//remove_block(bp);
				
	}

    else if(!prev_alloc && next_alloc) /* case 3; free prev block, occupied next block */
	{
		prev_bp = PREV_BLKP(bp);
		size += GET_SIZE(HDRP(prev_bp));
		pre_pre_alloc = GET_PREV_ALLOC(HDRP(PREV_BLKP(bp)));

		/* implicit stuff */
		PUT(FTRP(bp), PACK(size, pre_pre_alloc, 0));
	    PUT(HDRP(PREV_BLKP(bp)), PACK(size, pre_pre_alloc, 0));

		//		remove_block(bp);
		bp = PREV_BLKP(bp);
		/* no free list changes; new block becomes part of prev block */
	}
	
    else 	                   		   /* case 4: both previous and next block free */
	{
		/* stitch out next block's ptrs.  */
		prev_bp = PREV_BLKP(bp);
		next_bp = NEXT_BLKP(bp);
		next_size = GET_SIZE(FTRP(NEXT_BLKP(bp)));
		prev_size = GET_SIZE(HDRP(PREV_BLKP(bp)));
	    size += prev_size + next_size;
		pre_pre_alloc = GET_PREV_ALLOC(HDRP(PREV_BLKP(bp)));

		//		remove_block(next_bp);
		//		remove_block(bp);
		
		PUT(HDRP(PREV_BLKP(bp)), PACK(size, pre_pre_alloc, 0));
		PUT(FTRP(NEXT_BLKP(bp)), PACK(size, pre_pre_alloc, 0)); 

		bp = PREV_BLKP(bp);
	}
    return bp;
}

/* 
 * scans entire heap and coalesces any adjacent free blocks
 * for use with deferred coalescing
 */
/* 
static void full_coalesce()
{
	char *bp;

    for (bp = heap_start; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp))
		{
			if(!GET_ALLOC(HDRP(bp)))
				bp = coalesce(bp);
		}
}
*/

/* 
 * Extends heap by the multiplicand of WSIZE and words argument.
 */
static void * extend_heap(size_t words)
{
    char * p;
    size_t size;
	
	/* saves the prev_alloc flag of current epilogue */
	size_t end_alloc = GET_PREV_ALLOC(heap_list_e); 
	
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE; /* aligning payload size to WSIZE*/

    if((long)(p = mem_sbrk(size)) == -1) /* not enough memory! */
		return NULL;

    PUT(HDRP(p), PACK(size, end_alloc, 0));	/* Free block header */
    PUT(FTRP(p), PACK(size, end_alloc, 0));	/* Free block footer */
    PUT(HDRP((NEXT_BLKP(p))), PACK(0, 0, 1));     /* new epilogue header */
    heap_list_e = HDRP(NEXT_BLKP(p));
	add_block(p);
	return coalesce(p);              
	//return p;  					         /* deferred coalescing if coalesce(p) is gone */
	
}

/* searches the heap for an open space of size and returns a pointer to the first word 
 * in the block following the header.  
 */
static void * find_fit(size_t size)
{
    char *bp;// = free_list_r;
	//mm_print_free();
	//	while(bp != NULL)
	for (bp = heap_list_p; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp))
		{
			if(!GET_ALLOC(HDRP(bp)) && (size < GET_SIZE(HDRP(bp))))
					return bp;

			//		bp = SUCC_FREP(bp);
		}

    return NULL; 		/* no blocks available */
}

/* 
 * sets up the header and footer in an allocated block
 * also sets up next block if block is split.
 */
static void * place(void *bp, size_t size)
{
    size_t old_size = GET_SIZE(HDRP(bp));    /* size of block before splitting it */
    size_t split_size = old_size - size;	 /* size of leftover space after splitting */


	char * next_bp = NEXT_BLKP(bp);			/* pointer to next block */
	/* for cleaner code, can remove to optimize */
	size_t next_blk_size =  GET_SIZE(HDRP(next_bp));
	
    if((split_size == 0) || (split_size < (SPLIT_MIN))) /* not enough room to split */
		{
			PUT(HDRP(bp), PACK(old_size, 2, 1));
			PUT(HDRP(next_bp), PACK(next_blk_size, 2, 1));
			remove_block(bp);
			return bp;
		}


	/* if code gets to here, we are splitting the block */
	PUT(HDRP(NEXT_BLKP(bp)), PACK(next_blk_size, 0, 1));
	/* assign header  */
	PUT(HDRP(bp), PACK(size, 2, 1));
	
	char * split_bp;
	split_bp = NEXT_BLKP(bp);

	/* split block header */
	PUT(HDRP(split_bp), PACK(split_size, 2, 0));
	

	/* moves the pointers from this block up a bit to the new split block. */
	/* smaller block, but gets rid of the need of coalescing. */
	PUT_PTRP(SUCC(split_bp), SUCC_FREP(bp));
	PUT_PTRP(PRED(split_bp), PRED_FREP(bp));
	
	return bp;
}
/* 
 * prints a graphical image of the free list
 */
void mm_print_free()
{
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


}
void myprintblock(char * bp)
{
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
}

/* consistency checking, make sure all headers and footers have equal block sizes/allocated bits,
 * and all blocks are properly aligned.
 */
void mycheckblock(char * bp)
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
					printf("%d    %d \n",  sizeH, sizeF);
					sleep(1);
				}
			if(allocF != allocH)
				{
					printf("\nAllocs do not match!\n");
					sleep(1);
				}
			if(prev_alloc != prev_alloc_f)
				{
					printf("\nPrev_allocs do not match! H %d F %d \n", prev_alloc, prev_alloc_f);
					if(GET_SIZE(HDRP(NEXT_BLKP(bp))) == 0)
						printf("yup right before epilogue");
					sleep(1);
		 		}
		}
    int ali = (unsigned int)bp % WSIZE;
    if(ali)
		{
			printf("alignment is off, the modulus of bp and WSIZE is %d\n", ali);
			sleep(1);
		}
    return;
}

void mm_check()
{
    //size_t heap_size = mem_heapsize(); /* number of bytes in heap */
    int total_blocks = 1;			/* all blocks in  */
    int free_blocks = 0;		    /*  */
	char *bp;
	//size_t payloads = tot_payload_request;

	//	printf("\n\n\n ");
    for (bp = heap_list_p; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp))
	{
	    if(!GET_ALLOC(HDRP(bp)))
			free_blocks++;
			
		//		myprintblock(bp);
	    mycheckblock(bp);
			total_blocks++;
	}
		mm_print_free();
	//	printf("\nFirst byte heap = %p    Last byte heap = %p    Size of heap = %d\n", heap_list_p,
	// heap_list_e, heap_size);
		printf("Total free blocks = %d\nTotal blocks = %d\n", free_blocks, total_blocks);

		//	sleep(1);    
}

/* 
 * mm_init - initialize the malloc package.
  */
int mm_init(void)
{
    /* creates the beginning of the heap */
    if ((heap_list_p = mem_sbrk(4 * WSIZE)) == (void *)-1)
		return -1;
    
    PUT(heap_list_p, 0);		                    /* Alignment padding */
    PUT(heap_list_p + (1 * WSIZE), PACK(DSIZE, 2, 1)); /* Prologue header */
    PUT(heap_list_p + (2 * WSIZE), PACK(DSIZE, 2, 1)); /* Prologue footer */
	PUT(heap_list_p + (3 * WSIZE), PACK(0, 2, 1));     /* Epilogue header */

    heap_list_p += (2 * WSIZE);			            /* heap_list_p is now set at prologue header */
	heap_list_e = HDRP(NEXT_BLKP(heap_list_p));
	free_list_r = NULL;

	/* Extend the empty heap with a free block of CHUNKSIZE bytes */
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

    if (size == 0)
		return NULL;

    size_t adj_size;		/* size after alignment */
    size_t exp_size;		/* size of expansion if needed */
    char *bp;	   		    /* pointer that will point to word after header in allocated block */
    
    if(size <= MIN_SIZE)   	/* check if enough space for pointers, header, and footer when free */
	{
	    adj_size = 2 * MIN_SIZE; 
	}
    else					/* align to nearest upper WSIZE multiple */
	{
	    adj_size = WSIZE * ((size + (WSIZE) + (WSIZE-1)) /  WSIZE);
	}

	//bp = find_fit(adj_size); 	
	/* deferred coalescing */
	/* 
	if(bp == NULL)				
		{
			full_coalesce();
			bp = find_fit(adj_size);
		}
	 */
    if((bp = find_fit(adj_size)) != NULL) 				/* there is enough space */
		{
			remove_block(bp); 	/* take it out of free list pool */
			place(bp, adj_size);
			/* TEST HEAP */
			mm_check();
			/* TEST END */
			return bp;
		}

    /* no fit found; get more memory and place block */
    exp_size = MAX(adj_size, CHUNKSIZE);

	if((bp = extend_heap(exp_size/WSIZE)) == NULL)
		return NULL; 		/* out of memory */

	remove_block(bp);		 /* remove block from the pool prior to placement */
    place(bp, adj_size); 	/* sets up header/footer for new block */
	/* TEST HEAP */
	mm_check();
	/* TEST END */

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
    size_t size = GET_SIZE(HDRP(bp));				/* size of current block */
	size_t prev_alloc = GET_PREV_ALLOC(HDRP(bp));	/* allocation status of previous block */
	
   	void *next_head = HDRP(NEXT_BLKP(bp));         /* block following the free'd block */
	size_t next_size = GET_SIZE(next_head);			/* block size of following block */
	size_t next_alloc = GET_ALLOC(next_head);		/* next block allocation status */
	
	/* set prev_alloc flag in the following block */
	PUT(next_head, PACK(next_size, 0, next_alloc));

	/* if next block is not allocated, need to change footer	 */
	if(!next_alloc)				
		PUT(FTRP(NEXT_BLKP(bp)), PACK(next_size, 0, 0));

	/* set alloc flag in current block and create a footer */
    PUT(HDRP(bp), PACK(size, prev_alloc, 0));
    PUT(FTRP(bp), PACK(size, prev_alloc, 0));

	/* set pointers in the new free block to be in the free list */
	add_block(bp);
	/* if commented out, using deferred coalescing */
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
		return mm_free(ptr);
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














