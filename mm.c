/*
 * Copy the implicit free list implementation from the book
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
    "peanutbutterjellytime",
    /* First member's full name */
    "Guyu Fan",
    /* First member's email address */
    "gf940@nyu.edu",
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

/* Macros from CS:APP3e */
#define WSIZE 4 // single word size in bytes
#define DSIZE 8 // double word size 
#define CHUNKSIZE (1<<12) // extend the heap by this many bytes

#define MAX(x, y) ((x) > (y)? (x): (y))
#define MIN(x, y) ((x) > (y)? (y): (x))

// pack a size and allocated bit into a word to be used as header/footer
#define PACK(size, alloc) ((size) | (alloc))

// read/write a word at address p (a void pointer)
#define GET(p) (*(unsigned int *) (p))
#define PUT(p, val) (*(unsigned int *) (p) = (val))

// read the size/allocated info from p (pointing to a header/footer)
#define GET_SIZE(p) (GET(p) & ~0x7) // zero out the last 3 bits
#define GET_ALLOC(p) (GET(p) & 0x1) // get the last bit

// given block pointer (first payload byte), compute addresses of header/footer
#define HDRP(bp) ((char *) (bp) - WSIZE) // convert to char pointer so that pointer arithmetics operate in bytes
#define FTRP(bp) ((char *) (bp) + GET_SIZE(HDRP(bp)) - DSIZE)

// given block pointer, computer addresses of next/previous block pointers
#define NEXT_BLKP(bp) ((char *) (bp) + GET_SIZE(HDRP(bp)))
#define PREV_BLKP(bp) ((char *) (bp) - GET_SIZE(((char *) (bp) - DSIZE))) // use footer info
/* End of Macros from CS:APP3e */


/* private global variables */
static char *heap_listp = 0; // pointer to the first block of the heap

/* private helper function definitions */
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);


/*
 * Heap consistency checker
 */
int mm_check(void) {
    return 0;
}


/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    // create initial empty heap
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *) -1)
        return -1;
    PUT(heap_listp, 0); // unused padding word for alignment purposes
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1)); // prologue header
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1)); // prologue footer
    PUT(heap_listp + (3*WSIZE), PACK(0, 1)); // epilogue header
    heap_listp += (2*WSIZE); // block pointer of prologue block

    // extend the empty heap with a free block of CHUNKSIZE bytes
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
        return -1;
    return 0;
}

/* 
 * mm_malloc - adjust the size and allocate a block of that size from the free list
 */
void *mm_malloc(size_t size)
{
    size_t asize; // adjusted block size
    size_t extendsize; // the amount to extend the heap by if there's no fit
    char *bp;

    // ignore non-positive values
    if (size <= 0)
        return NULL;

    // adjust block size to include overhead and satisfy 8-byte alignment
    if (size <= DSIZE) {
        asize = 2*DSIZE;
    } else {
        asize = DSIZE * ((size + DSIZE + (DSIZE-1)) / DSIZE);
    }

    // search the free list for a fit
    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }

    // no fit found. extend the heap and place
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    return bp;
}

/*
 * mm_free - Freeing a block by setting the header/footer and coalescing
 */
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp));
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *bp, size_t size)
{
    size_t copySize;
    void *oldbp = bp;
    void *newbp;

    // bp is NULL, equivalent to malloc call
    if (bp == NULL) {
       return mm_malloc(size);
    }
    // size is 0, equivalent to free
    if (size == 0) {
        mm_free(bp);
        return NULL;
    }
    // otherwise, allocate new block, copy contents over, and free old block
    newbp = mm_malloc(size);
    copySize = MIN(GET_SIZE(bp) - DSIZE, size);
    memcpy(newbp, oldbp, copySize);
    mm_free(bp);
    return newbp;
}

/*
 * Extend the heap by a given number of words
 */
static void *extend_heap(size_t words) {
    char *bp;
    size_t size;

    // allocate an even number of words to maintain double-word alignment
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
    if ((long) (bp = mem_sbrk(size)) == -1)
        return NULL; // extension failed

    // extension successful, bp now points to the first byte after allocated space
    // initialize free block header/footer and epilogue headers
    PUT(HDRP(bp), PACK(size, 0)); // must populate header first
    PUT(FTRP(bp), PACK(size, 0)); // footer uses header size info
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); // new epilogue

    // coalesce if previous block was free
    return coalesce(bp);
}

static void *coalesce(void *bp) {
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc) {
        // nothing to do
        return bp;
    }

    else if (prev_alloc && !next_alloc) {
        // combine with next block
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }

    else if (!prev_alloc && next_alloc) {
        // combine with previous block
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    else {
        // combine with both previous and next block
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    return bp;
}


/*
 * find first free block that fit the size of request
 */
static void *find_fit(size_t asize) {
    void *bp;
    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        if (!GET_ALLOC(HDRP(bp))) {
            if (asize <= GET_SIZE(HDRP(bp))) {
                return bp;
            }
        }
    }

    return NULL; // no fit found
}


static void place(void *bp, size_t asize) {
    size_t csize = GET_SIZE(HDRP(bp));

    if ((csize - asize) >= (2*DSIZE)) {
        // the remaineder size is greater than minimum block size
        // split the block
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));
    } else {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}




