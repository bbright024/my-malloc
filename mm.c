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

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/* Basic constants and macros */
#define WSIZE      8  		/* Word and header/footer size (bytes) */
#define DSIZE      16 		/* Double word size (bytes) */
#define CHUNKSIZE  (1<<12)	/* Extend heap by this amount (bytes) */

#define MAX(x, y) ((x) > (y) ? (x) : (y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)   ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p)              (*(unsigned int *)(p))
#define PUT(p, val)         (*(unsigned int *)(p) = (val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)         (GET(p) & ~0x7)
#define GET_ALLOC(p)        (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)            ((char *)(bp) - WSIZE)
#define FTRP(bp)            ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and prev blocks */
#define NEXT_BLKP(bp)       ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp)       ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))


static void * heap_list_p; 	/* points to prologue header  */
static void * heap_list_e; 	/* points to epilogue header  */
static void * heap_start;	/* points to first block in heap */

/* combines empty blocks around the given pointer to a block */
static void * coalesce(void * bp)
{
    if (GET_ALLOC(HDRP(bp))) 	/* in case accidentally called on an allocated block */
	return bp;

    size_t size = GET_SIZE(HDRP(bp));       /* allocations and sizes of the 3 bloc */
    int prev_alloc = GET_ALLOC(HDRP(PREV_BLKP(bp)));
    int next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t prev_size = GET_SIZE(HDRP(PREV_BLKP(bp)));
    size_t next_size = GET_SIZE(HDRP(NEXT_BLKP(bp)));

    if (prev_alloc && next_alloc) /* case 1, no free blocks to coalesce */
	return bp;
    
    else if(prev_alloc && !next_alloc) /* case 2; occupied previous block, empty next block */
	{
	    size += next_size;
	    PUT(HDRP(bp), PACK(size, 0));
	    PUT(FTRP(bp), PACK(size, 0));
	}

    else if(!prev_alloc && next_alloc) /* case 3; free prev block, occupied next block */
	{
	    size += prev_size;
	    PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
	    PUT(FTRP(bp), PACK(size, 0));
	    bp = PREV_BLKP(bp);
	}
    else 			/* case 4: both previous and next block free */
	{
	    size += prev_size + next_size;
	    PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
	    PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0)); 
	    bp = PREV_BLKP(bp);
	}
    return bp;

}

static void * extend_heap(size_t words)
{
    char * p;
    size_t size;
    
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE; /* padding added to payload size */

    if((long)(p = mem_sbrk(size)) == -1)
	return NULL;

    /* TEST */
    //        printf("\n%d this is size\n", size);
    /* TEST END */

    PUT(HDRP(p), PACK(size, 0));	 /* header for new block; overwrites previous epilogue*/
    PUT(FTRP(p), PACK(size, 0));	 /* create footer value for new block */
    PUT(HDRP(NEXT_BLKP(p)), PACK(0, 1)); /* new epilogue value */
    heap_list_e = HDRP(NEXT_BLKP(p));
    return coalesce(p);
}

/* searches the heap for an open space of size and returns a pointer to the first word 
 * in the block following the header.  
 */
static void * find_fit(size_t size)
{

    char * heap_end; 		/* last byte in the heap */
    char * curr_ptr; 		/* current pointer */

    size_t curr_alloc;
    size_t curr_size;    
    size_t max_fit;

    curr_ptr = heap_list_p;
    heap_end = heap_list_e;
    while(curr_ptr < heap_end)
	{
	    curr_alloc = GET_ALLOC(HDRP(curr_ptr));
	    curr_size = GET_SIZE(HDRP(curr_ptr));
	    max_fit = curr_size - DSIZE;           /* gotta subtract out the footer/header */

	    /* TEST */
	    //	    if(curr_size == 0)
	    //	{
	    //	    printf("\nthe size of this block is 0, you're at epi or else error...\n");
	    //	    break;
	    //	}
	    /* END TEST */

	    if(!curr_alloc && (size <= max_fit)) /* block can fit the request */
		{
		    /* TEST */
		    //	    printf("fit was found in find_fit because %d is LESS THAN %d \n", size,
		    //	   max_fit);
		    /* TEST END */
		    return curr_ptr;
		}

	    curr_ptr = NEXT_BLKP(curr_ptr); /* get pointer to word after next block header */
	}
    
    return NULL; 		/* no blocks available */
}

/* 
 * sets up the header and footer in an allocated block
 * also sets up next block if block is split.
 */
static void * place(void *bp, size_t size)
{
    size_t old_size = GET_SIZE(HDRP(bp)); /* size of block before splitting it */
    size_t split_size = old_size - size;	 /* size of leftover space after splitting */
    char *split_bp;			 /* address of bp of leftover space block */
    
    if((split_size == 0) || (split_size < DSIZE)) /* when leftover space too small for hdr/ftr */
	return bp;

    PUT(HDRP(bp), PACK(size, 1));
    PUT(FTRP(bp), PACK(size, 1));

    /* fixes up the empty space following the newly allocated block. */
    split_bp = NEXT_BLKP(bp);
    PUT(HDRP(split_bp), PACK(split_size, 0));
    PUT(FTRP(split_bp), PACK(split_size, 0));
    return bp;
}

/* 
 *  prints out info on the current heap
 */
void test_heap()
{
    int heap_size = mem_heapsize();
    void *first = heap_list_p;
    void *last = mem_heap_hi();
    printf("First byte heap = %p    Last byte heap = %p    Size of heap = %d\n", first,
	   last, heap_size);
    sleep(1);
    int total_blocks = 0;
    int free_blocks = 0;
    size_t curr_size;
    size_t curr_alloc;

    while(first < last)
	{
	    curr_size = GET_SIZE(HDRP(first));
	    curr_alloc = GET_ALLOC(FTRP(first));
	    if(!curr_alloc)
		{
		    free_blocks++;
		}
	    total_blocks++;
	    printf("[BLOCK %d SIZE = %d ALLO = %d]\n", total_blocks, curr_size, curr_alloc);
	    first += curr_size;

	    
	}
    printf("Total free blocks = %d\nTotal blocks = %d\n\n", free_blocks, total_blocks);
	    sleep(1);    
}

/* 
 * prints contents of header and footer of block bp on a single output line
 */
void myprintblock(char * bp)
{
    size_t sizeH = GET_SIZE(HDRP(bp));
    int allocH = GET_ALLOC(HDRP(bp));
    size_t sizeF = GET_SIZE(FTRP(bp));
    int allocF = GET_ALLOC(FTRP(bp));
    printf("\n[H- S = %d -- A = %d ]", sizeH, allocH);
    printf("[ ---- PAYLOAD OF SIZE %d  ---- ]", sizeH);
    printf("[F- S = %d -- A = %d]\n", sizeF, allocF);
}

/* consistency checking, make sure all headers and footers have equal block sizes/allocated bits,
 * and all blocks are properly aligned.
 */
void mycheckblock(char * bp)
{
    size_t sizeH = GET_SIZE(HDRP(bp));
    int allocH = GET_ALLOC(HDRP(bp));
    size_t sizeF = GET_SIZE(FTRP(bp));
    int allocF = GET_ALLOC(FTRP(bp));
    if(sizeH != sizeF)
	printf("Header size does not equal footer size\n");
    if(allocH != allocF)
	printf("Allocs do not match!\n");

    int ali = (unsigned int)bp % WSIZE;
    if(ali)
	printf("alignment is off, the modulus of bp and WSIZE is %d\n", ali);
    return;
}

void myheapcheck()
{
    char *bp;
    for (bp = heap_list_p; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp))
	{
	    myprintblock(bp);
	    mycheckblock(bp);
	}
}

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{

    /* creates the beginning of the heap */
    if ((heap_list_p = mem_sbrk(4 * WSIZE)) == (void *)-1)
	return -1;
    
    PUT(heap_list_p, 0);		                   /* Alignment padding */
    PUT(heap_list_p + (1 * WSIZE), PACK(DSIZE, 1)); /* Prologue header */
    PUT(heap_list_p + (2 * WSIZE), PACK(DSIZE, 1)); /* Prologue footer */
    PUT(heap_list_p + (3 * WSIZE), PACK(0, 1));     /* Epilogue header */
    heap_list_p += (1 * WSIZE);			    /* heap_list_p is now set at prologue header */

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if((heap_start = extend_heap(CHUNKSIZE/WSIZE)) == NULL)
	return -1;

    /* TEST */
    //    printf("\n\n\n %d  %p  %p %p  \n", mem_heapsize(), heap_start, mem_heap_lo(), mem_heap_hi());
    //    printf("%d    %d   \n", GET_SIZE(HDRP(heap_start)), mem_heap_hi() - mem_heap_lo());
    //    printf("%p    %d  %d \n", heap_list_p, GET_SIZE(heap_list_p), GET_SIZE(NEXT_BLKP(heap_list_p)));
     // sleep(30);
    /* TEST END */

    return 0;
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    /* old code from handout */
    /*    int newsize = ALIGN(size + SIZE_T_SIZE);
    void *p = mem_sbrk(newsize);
    if (p == (void *)-1)
	return NULL;
    else {
        *(size_t *)p = size;
        return (void *)((char *)p + SIZE_T_SIZE);
    }
    */

    if (size == 0)
	return NULL;

    size_t adj_size;		/* size after alignment */
    size_t exp_size;		/* size of expansion if needed */
    char *bp;			/* pointer that will eventually point to new block and be returned */
    
    /* TESTING */
    //    test_heap();
    //    printf("\n\ntrying to malloc a block of size %d  \n total heap size is %d \n", 
    //	    size, mem_heapsize());
    /* TEST END */

    if(size < DSIZE) 		/* need to make sure header/footer will fit */
	{
	    adj_size = 2*DSIZE;
	}
    else
	{
	    adj_size = DSIZE * ((size + (DSIZE) + (DSIZE-1)) /  DSIZE);
	}

    /* now search free list for a fit */
    if((bp = find_fit(adj_size)) != NULL)
	{
	    /* TEST */
	    //	    printf("Between find_fit and place\n");
	    //if(adj_size == 31520)
	    //	test_heap();
	    /* TEST END */
	    place(bp, adj_size);
	    return bp;
	}

    /* no fit found; get more memory and place block */
    exp_size = MAX(adj_size, CHUNKSIZE);

    /* Test */
    //    printf("fit not found, extending \n");
    /* TEST END */

    if((bp = extend_heap(exp_size/WSIZE)) == NULL)
	return NULL; 		/* out of memory */
    
    place(bp, adj_size); 	/* sets up header/footer for new block */

    /* TEST */
        myheapcheck();
    /* TEST END */

    return bp;
}

/*
 * mm_free - Freeing a block changes allocation value to 0 in header and footer, then 
 *      attempts to coalesce adjacent blocks.
 */
void mm_free(void *ptr)
{
    size_t size = GET_SIZE(HDRP(ptr));
    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));

    coalesce(ptr);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *ptr, size_t size)
{
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














