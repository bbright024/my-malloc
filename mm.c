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
#define GET_PTRP(p)         (*(unsigned long *)(p))
#define PUT_PTRP(p, val)         (*(unsigned long *)(p) = ((unsigned long)(val)))

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
#define SUCC_FREP(bp)       ((char *)GET_PTRP(SUCC(bp)))
#define PRED_FREP(bp)       ((char *)GET_PTRP(PRED(bp)))

static void * heap_list_p; 	/* points to prologue header  */
static void * heap_list_e; 	/* points to epilogue header  */
static void * heap_start;	/* points to first block in heap */
static void * free_list_r;	/* Root node of free list */
/* Heap check variables */

//static size_t tot_payload_request;
//static size_t internal_frag;

/* 
 *  removes the block at bp from the free list and rearranges the pointers
 *  in that block
 */
static void remove_block(void *bp)
{

	char *list_p = PRED_FREP(bp);         /* block prior to bp in free list */
	char *third_bp = SUCC_FREP(bp);       /* pointer to block following bp in free list */
	
	if(list_p == NULL) 			          /* bp was first block in free list */
		free_list_r = third_bp;           /* assign the root to point to block after bp */
	else
		PUT_PTRP(SUCC(list_p), third_bp); /* change node prior to bp to skip bp */

	if(third_bp != NULL) 		          /* bp not last node in free list */
		PUT_PTRP(PRED(third_bp), list_p); /* change block after bp's prev node pointer */
	
}

/* 
 *  adds block at bp to the free list and rearranges pointers
 *
 */
static void add_block(void *bp)
{
	char *old_first = free_list_r; /* first free block in list */

	/* set up new first block in free list */
	free_list_r = bp;
	PUT_PTRP(PRED(bp), NULL);
	
	if(old_first == NULL)			 /* list was empty */
		{
			PUT_PTRP(SUCC(bp), NULL);
			return;
		}

	PUT_PTRP(SUCC(bp), old_first);
	PUT_PTRP(PRED(old_first), bp);	/* bp now has a pointer back to list_p  */
}

/* 
 * combines empty blocks around the given pointer to a block
 */
static void * coalesce(void * bp)
{
    if (GET_ALLOC(HDRP(bp))) 	       /* in case accidentally called on allocated bp */
		return bp;

    size_t size = GET_SIZE(HDRP(bp));  /* allocations and sizes of the 3 blocs involved */
    int prev_alloc = GET_PREV_ALLOC(HDRP(bp));
    int next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t prev_size;
    size_t next_size;
	size_t pre_pre_alloc;	/* only use if starting from at least heap_start; wont work with hlp */
	
    if (prev_alloc && next_alloc)      /* case 1, no free blocks to coalesce */
		return bp;
    
    else if(prev_alloc && !next_alloc) /* case 2; occupied previous block, empty next block */
	{
		size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
	    PUT(HDRP(bp), PACK(size, 2, 0));
	    PUT(FTRP(bp), PACK(size, 2, 0));
	}

    else if(!prev_alloc && next_alloc) /* case 3; free prev block, occupied next block */
	{
		size += GET_SIZE(HDRP(PREV_BLKP(bp)));
		pre_pre_alloc = GET_PREV_ALLOC(HDRP(PREV_BLKP(bp)));

		PUT(FTRP(bp), PACK(size, pre_pre_alloc, 0));
	    PUT(HDRP(PREV_BLKP(bp)), PACK(size, pre_pre_alloc, 0));
	    bp = PREV_BLKP(bp);
	}
    else 	                   		   /* case 4: both previous and next block free */
	{
		next_size = GET_SIZE(FTRP(NEXT_BLKP(bp)));
		prev_size = GET_SIZE(HDRP(PREV_BLKP(bp)));
	    size += prev_size + next_size;
		pre_pre_alloc = GET_PREV_ALLOC(HDRP(PREV_BLKP(bp)));

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

	return coalesce(p);              
	//return p;  					         /* deferred coalescing if coalesce(p) is gone */
	
}

/* searches the heap for an open space of size and returns a pointer to the first word 
 * in the block following the header.  
 */
static void * find_fit(size_t size)
{
    char *bp;
	
    for (bp = free_list_r; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp))
		{
			if(!GET_ALLOC(HDRP(bp)) && (size < GET_SIZE(HDRP(bp))))
					return bp;
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
    size_t prev_alloc = GET_PREV_ALLOC(HDRP(bp)); /* not needed if immediate coalescing; always 2 */

	char * next_blk;			/* pointer to next block */
	int splitting = 1;			/* flag in case of splitting block */
	int no_prev_split = 0;			/* sets prev_alloc for the last block affected by place*/

	/* for cleaner code, can remove to optimize */
	size_t next_blk_size;
	size_t next_blk_alloc;
	
    if((split_size == 0) || (split_size < (SPLIT_MIN))) /* not enough room to split */
		{
			splitting = 0;
			size = old_size;
			no_prev_split = 2;
		}

	/* assign newly allocated block header  */
	PUT(HDRP(bp), PACK(size, prev_alloc, 1));

	/* remove block from free list */
	remove_block(bp);

	next_blk = NEXT_BLKP(bp);

	if(splitting)
		{
			/* split block header/footer */
			PUT(HDRP(next_blk), PACK(split_size, 2, 0));
			PUT(FTRP(next_blk), PACK(split_size, 2, 0));

			/* split block added to free list */
			add_block(next_blk);
			
			/* dont forget block after the split to update prev_alloc */
			next_blk = NEXT_BLKP(next_blk); 
		}

	/* whether splitting or not, this stuff is the block after the original free one */
	next_blk_size = GET_SIZE(HDRP(next_blk));
	next_blk_alloc = GET_ALLOC(HDRP(next_blk));

	/* final block is always allocated because of coalesce;dont worry bout footer. */
	PUT(HDRP(next_blk), PACK(next_blk_size, no_prev_split, next_blk_alloc));
	if(!next_blk_alloc)
		PUT(FTRP(next_blk), PACK(next_blk_size, no_prev_split, 0));
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
	
	while(bp != NULL)
		{
			size = GET_SIZE(HDRP(bp));
			alloc = GET_ALLOC(HDRP(bp));
			prev_alloc = GET_PREV_ALLOC(HDRP(bp));
			succ = SUCC_FREP(bp);
			pred = PRED_FREP(bp);
			
			printf("\n[Head-- PrevAll = %d -- All = %d ]", prev_alloc, alloc);
			printf("[ Successor = %#lx ][Predecessor = %#lx ]", (unsigned long)succ, (unsigned long)pred);
			printf("[ ---- BLOCK SIZE %d  ---- ]\n", size);

			
			bp = SUCC_FREP(bp);
		}
	
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

	printf("\n\n\n\n\n ");
    size_t sizeH = GET_SIZE(HDRP(bp));
    size_t allocH = GET_ALLOC(HDRP(bp));
	size_t prev_alloc = GET_PREV_ALLOC(HDRP(bp));
	mm_print_free();
	if(!allocH)
		{
			size_t sizeF = GET_SIZE(FTRP(bp));
			size_t allocF = GET_ALLOC(FTRP(bp));
			size_t prev_alloc_f = GET_PREV_ALLOC(FTRP(bp));
			if(sizeH != sizeF)
				{
					printf("\nHeader size does not equal footer size\n");
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

    for (bp = heap_list_p; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp))
	{
	    if(!GET_ALLOC(HDRP(bp)))
			free_blocks++;
			
		myprintblock(bp);
	    mycheckblock(bp);
		total_blocks++;
	}
	
	//	printf("\nFirst byte heap = %p    Last byte heap = %p    Size of heap = %d\n", heap_list_p,
	// heap_list_e, heap_size);
	//    printf("Total free blocks = %d\nTotal blocks = %d\n", free_blocks, total_blocks);

		sleep(1);    
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

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
	if((heap_start = extend_heap(CHUNKSIZE/WSIZE)) == NULL)
		return -1;

	add_block(heap_start);
	
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

	bp = find_fit(adj_size); 	
	/* deferred coalescing */
	/* 
	if(bp == NULL)				
		{
			full_coalesce();
			bp = find_fit(adj_size);
		}
	 */
    if(bp != NULL) 				/* there is enough space */
		{
			place(bp, adj_size);
			
			/* TEST HEAP */
												mm_check();
			//internal_frag = adj_size - size;
			//printf("Infrag = %d\nPayload = %d\nBlock size = %d\n", internal_frag, size, adj_size);
			/* TEST END */
			
			return bp;
		}

    /* no fit found; get more memory and place block */
    exp_size = MAX(adj_size, CHUNKSIZE);

	if((bp = extend_heap(exp_size/WSIZE)) == NULL)
		return NULL; 		/* out of memory */
    
    place(bp, adj_size); 	/* sets up header/footer for new block */
	/* TEST HEAP */

			mm_check();
	//internal_frag = adj_size - size;
	//printf("Infrag = %d\nPayload = %d\nBlock size = %d\n", internal_frag, size, adj_size);
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

	/* if next block is not allocated, need to change footer.
	 * UNLESS USING IMMEDIATE COALESCING, because it will just be 
	 * combined if free and changed immediately.
	 */
	//	if(!next_alloc)				
	//	PUT(FTRP(NEXT_BLKP(bp)), PACK(next_size, 0, 0));

	/* set alloc flag in current block and create a footer */
    PUT(HDRP(bp), PACK(size, prev_alloc, 0));
    PUT(FTRP(bp), PACK(size, prev_alloc, 0));

	/* if commented out, using deferred coalescing */
	bp = coalesce(bp);

	/* set pointers in the new free block to be in the free list */
	add_block(bp);
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














