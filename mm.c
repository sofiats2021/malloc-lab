/*
 * Segregated Free List, First-fit strategy
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


/* Macros (partially from CS:APP3e) */
#define WSIZE 4 // single word size in bytes
#define DSIZE 8 // double word size 
#define CHUNKSIZE (1<<12) // extend the heap by this many bytes
#define NUM_SIZE_CLASS 11 // number of size classes
#define MIN_BLOCK_SIZE (4*WSIZE) // header, footer, pred, succ

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

// given block pointer (first payload byte), compute addresses of header/footer/pred/succ
#define HDRP(bp) ((char *) (bp) - WSIZE) // convert to char pointer so that pointer arithmetics operate in bytes
#define FTRP(bp) ((char *) (bp) + GET_SIZE(HDRP(bp)) - DSIZE)
#define PRED(bp) ((char *) (bp))
#define SUCC(bp) ((char *) (bp + WSIZE))

// given block pointer, compute addresses of previous/next block pointers
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)))

// given block pointer, compute addresses of predeccsor/successor block pointers
#define PRED_BLKP(bp) ((char *) GET(PRED(bp)))
#define SUCC_BLKP(bp) ((char *) GET(SUCC(bp)))


/* End of Macros (partially from CS:APP3e) */


/* private global variables */
static char *heap_listp = 0; // first block pointer of the heap (prologue block)
static char **freelist_p = 0; // pointer to the start an array of block pointers (free blocks) of different size classes

/* private helper function definitions */
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
static void insert(void* bp);
static void delete(void* bp);
static int get_size_class(size_t asize);
static void print_block(void *bp);
static void check_block(void *bp);


static void print_block(void *bp) {
    printf("\t\t\tp: %p; ", bp);
    printf("allocated: %s; ", GET_ALLOC(HDRP(bp))? "yes": "no" );
    printf("hsize: %d; ", GET_SIZE(HDRP(bp)));
    printf("fsize: %d; ", GET_SIZE(FTRP(bp)));
    printf("pred: %p, succ: %p\n", (void *) GET(PRED(bp)), (void *) GET(SUCC(bp)));
}

static void check_block(void *bp) {
    if (GET_SIZE(HDRP(bp)) % DSIZE)
        printf("\terror: not doubly aligned\n");
    if (GET(HDRP(bp)) != GET(FTRP(bp)))
        printf("\terror: header & foot do not match\n");
}

static void check_list() {
    void *size_class_ptr, *bp;
    printf("\tSegregated Free List Info:\n");
    for (int i = 0; i < NUM_SIZE_CLASS; i++) {
        size_class_ptr = freelist_p + i;
        if (GET(size_class_ptr) == 0) {
            printf("\t\tsize class %d: empty\n", i);
        } else {
            printf("\t\tsize class %d: not empty\n", i);
            bp = (void *) GET(size_class_ptr);
            while (bp != ((void *) 0)) {
                print_block(bp);
                bp = SUCC_BLKP(bp);
            }
        }
    }
    printf("\n");
}

/*
 * Heap consistency checker
 */
int mm_check() {
    printf("\n");
    char *bp = heap_listp;
    // check prologue
    if (GET_SIZE(HDRP(heap_listp)) != DSIZE || !GET_ALLOC(HDRP(heap_listp)))
        printf("\terror: bad prologue header\n");

    printf("\tprinting every block in the heap: \n");
    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        check_block(bp);
        print_block(bp);
    }

    // check epilogue
    if (GET_SIZE(HDRP(bp)) != 0 || !(GET_ALLOC(HDRP(bp))))
        printf("\terror: bad epilogue header\n");
    printf("\n");

    // check list
    check_list();
    return 0;
}


/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    setbuf(stdout, NULL);

    // create initial empty heap, no alignment padding needed
    // array (13 * 4) + prologue (2 * 4) + epilogue (4)
    if ((heap_listp = mem_sbrk(WSIZE*(NUM_SIZE_CLASS + 2 + 1))) == (void *) -1)
        return -1;

    // first, initialize an array of pointers (with initial value 0)
    // each pointer in the array points to the first block of a certain
    // class size
    // size here means adjusted size.
    // minimum size of a size class is 16 bytes

    /* there are 11 size classes
     * [1-2^4], [2^4+1 - 2^5] ... [2^12+1, 2^13], [2^13+1 - +inf]
     */

    memset(heap_listp, 0, NUM_SIZE_CLASS*WSIZE);
    freelist_p = (char **) heap_listp;

    // next, initialize the prologue and epilogue block
    heap_listp += NUM_SIZE_CLASS * WSIZE;
    PUT(heap_listp, PACK(DSIZE, 1)); // prologue header
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1)); // prologue footer
    PUT(heap_listp + (2*WSIZE), PACK(0, 1)); // epilogue header
    heap_listp += (1*WSIZE); // set heap_listp as block pointer to prologue block

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
    // set pred/succ to 0 before coalescing, because coalesce involves deletion of
    // blocks from the free list
    PUT(PRED(bp), 0);
    PUT(SUCC(bp), 0);
    insert(coalesce(bp));
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
    size_t size; // in bytes

    // allocate an even number of words to maintain double-word alignment
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
    if ((long) (bp = mem_sbrk(size)) == -1)
        return NULL; // extension failed

    // extension successful, bp now points to the first byte after allocated space
    // initialize free block header/footer and epilogue header
    // pred/succ are handled by insert call below
    PUT(HDRP(bp), PACK(size, 0)); // must populate header first
    PUT(FTRP(bp), PACK(size, 0)); // footer uses header size info
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); // new epilogue

    // coalesce if previous block was free
    bp = coalesce(bp);
    // insert the block into the segregated list
    insert(bp);

    return bp;
}


/*
 * Coalesce a free block with ajacent free blocks to form a larger free block
 */
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
        // first, delete next block from free list
        delete(NEXT_BLKP(bp));
        // then, update the size information
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }

    else if (!prev_alloc && next_alloc) {
        // combine with previous block
        // first, delete this block from free list
        delete(bp);
        // then, update the size information
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    else {
        // combine with both previous and next block
        // first, delete both this and next block from free list
        delete(bp);
        delete(NEXT_BLKP(bp));
        // then, update the size information
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
    int size_class = get_size_class(asize);
    void *class_p, *bp;
    size_t blk_size;

    // while fit is not found
    while (size_class < NUM_SIZE_CLASS) {
        class_p = freelist_p + size_class;

        // if the current size class is not empty
        // go through the free list to find a fit
        if (GET(class_p) != 0) {
            bp = (void *) GET(class_p);
            while (bp != ((void *) 0)) {
                // print_block(bp);
                blk_size = GET_SIZE(HDRP(bp));
                if (asize <= blk_size) {
                    return bp;
                }
                bp = SUCC_BLKP(bp);
            }
        }
        // no fit is found in the current list
        size_class++;
    }

    return NULL; // no fit found
}


/*
 * Place a block of certain size at bp, split if necessary
 */
static void place(void *bp, size_t asize) {
    size_t csize = GET_SIZE(HDRP(bp));

    if ((csize - asize) >= MIN_BLOCK_SIZE) {
        // the remainder size is greater than minimum block size
        // allocate the block
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        // delete allocated block from free list
        delete(bp);
        // create new free block from the remainder
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));
        // insert new block into free list
        insert(bp);
    } else {
        // just allocate the whole block
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
        delete(bp);
    }
}

/*
 * insert a free block at bp into the segregated list
 */
static void insert(void *bp) {
    size_t size = GET_SIZE(HDRP(bp)); // adjusted size
    int size_class; // the size class (0 - 12)
    char **size_class_ptr; // the pointer to the address of the first free block of the size class
    unsigned int bp_val = (unsigned int) bp;

    // get appropriate size class
    size_class_ptr = freelist_p + get_size_class(size);
    // the appropriate size class is empty
    if (GET(size_class_ptr) == 0) {
        // change heap array
        PUT(size_class_ptr, bp_val);
        // set pred/succ of new free block
        PUT(PRED(bp), 0);
        PUT(SUCC(bp), 0);
    }
    // the appropriate size class is not empty
    // insert the free block at the beginning of the size class
    else {
        // set pred/succ of new free block
        PUT(PRED(bp), 0);
        PUT(SUCC(bp), GET(size_class_ptr));
        // connect the previous head of the size class
        PUT(PRED(GET(size_class_ptr)), bp_val);
        // change heap array
        PUT(size_class_ptr, bp_val);
    }
}


/*
 * delete a block from free list
 */
static void delete(void *bp) {
    int pre = GET(PRED(bp));
    int suc = GET(SUCC(bp));
    int size_class = get_size_class(GET_SIZE(HDRP(bp)));
    unsigned int bp_val = (unsigned int) bp;

    // no predecessor or successor
    if (pre == 0 && suc == 0) {
        // check if the block is the lone head of a free list
        if (GET(freelist_p + size_class) == bp_val)
            // if it is, set the heap array entry to 0
            PUT(freelist_p + size_class, 0);
    }

    // has predecessor but no successor
    else if (pre != 0 && suc == 0) {
        // set its predecessor's succ pointer to 0
        PUT(SUCC(PRED_BLKP(bp)), 0);
    }

    // has both predecessor and successor
    else if (pre != 0 && suc != 0) {
        // set its predecessor's succ pointer to its succ
        PUT(SUCC(PRED_BLKP(bp)), GET(SUCC(bp)));
        // set its successor's pred pointer to its pred
        PUT(PRED(SUCC_BLKP(bp)), GET(PRED(bp)));
    }

    // has no predecessor but has a successor
    // this means the block is the head of a free list
    else {
        // set heap array entry to the address of its succ
        PUT(freelist_p + size_class, GET(SUCC(bp)));
        // set its successor's pred pointer to 0
        PUT(PRED(SUCC_BLKP(bp)), 0);
    }
}

/*
 * get size class based on the adjusted size
 * asize is in bytes
 */
static int get_size_class(size_t asize) {
    int size_class = 0;
    while (asize > MIN_BLOCK_SIZE && size_class < NUM_SIZE_CLASS-1) {
        size_class++;
        asize /= 2;
    }
    return size_class;
}
