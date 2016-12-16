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

#define DEBUG_MALLOC 0
#define DEBUG_FREE 0
#define DEBUG_PLACE 0
#define DEBUG_INSERT 0
#define DEBUG_DELETE 0

/* Macros (partially from CS:APP3e) */
#define WSIZE 4 // single word size in bytes
#define DSIZE 8 // double word size 
#define CHUNKSIZE (1<<12) // extend the heap by this many bytes
#define NUM_SIZE_CLASS 17 // number of size classes
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
static int is_list_ptr(void *ptr);
static void print_block(void *bp);
static void print_heap();
static void check_block(void *bp);


static void print_block(void *bp) {
    printf("\tp: %p; ", bp);
    printf("allocated: %s; ", GET_ALLOC(HDRP(bp))? "yes": "no" );
    printf("hsize: %d; ", GET_SIZE(HDRP(bp)));
    printf("fsize: %d; ", GET_SIZE(FTRP(bp)));
    printf("pred: %p, succ: %p\n", (void *) GET(PRED(bp)), (void *) GET(SUCC(bp)));
}

static void print_heap() {
    printf("heap\n");
    void *bp;
    for (bp = heap_listp+DSIZE; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        check_block(bp);
        print_block(bp);
    }
    printf("heap-end\n");
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

    // mm_check();
    return 0;
}

/* 
 * mm_malloc - adjust the size and allocate a block of that size from the free list
 */
void *mm_malloc(size_t size)
{
    if (DEBUG_MALLOC) {
        printf("before malloc\n");
        print_heap();
    }

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

    if (DEBUG_MALLOC) {
        printf("after malloc\n");
        print_block(bp);
        print_heap();
    }

    return bp;
}

/*
 * mm_free - Freeing a block by setting the header/footer and coalescing
 */
void mm_free(void *bp)
{
    if (DEBUG_FREE) {
        printf("before free %p\n", bp);
        print_heap();
    }

    size_t size = GET_SIZE(HDRP(bp));
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    // zero out the pred/succ to be safe
    PUT(PRED(bp), 0);
    PUT(SUCC(bp), 0);
    insert(coalesce(bp));

    if (DEBUG_FREE) {
        printf("after free %p\n", bp);
        print_heap();
    }
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *bp, size_t size)
{
    // bp is NULL, equivalent to malloc call
    if (bp == NULL) {
       return mm_malloc(size);
    }

    // size is 0, equivalent to free
    if (size == 0) {
        mm_free(bp);
        return NULL;
    }

    size_t old_size = GET_SIZE(HDRP(bp));
    size_t asize, nextblc_size, copy_size;
    void *oldbp = bp;
    void *newbp;

    // check whether realloc is shrinking or expanding
    // get the adjusted size of the request
    if (size <= DSIZE) {
        asize = 2*DSIZE;
    } else {
        asize = DSIZE * ((size + DSIZE + (DSIZE-1)) / DSIZE);
    }

    // if the same size
    if (asize == old_size) {
        return bp;
    }
    // if shrinking
    if (asize < old_size) {
        // we split the block if the remainder is big enough
        if (old_size - asize >= MIN_BLOCK_SIZE) {
            // shrink the old block
            PUT(HDRP(bp), PACK(asize, 1));
            PUT(FTRP(bp), PACK(asize, 1));
            // construct the new block
            newbp = NEXT_BLKP(bp);
            PUT(HDRP(newbp), PACK(old_size - asize, 0));
            PUT(FTRP(newbp), PACK(old_size - asize, 0));
            // insert new block into free list
            // zero out pred/succ to be safe
            PUT(PRED(newbp), 0);
            PUT(SUCC(newbp), 0);
            insert(newbp);
        }
        // otherwise we don't do anything
        return oldbp;
    }

    // if expanding
    else {
        // we check if we can make the block large enough by
        // coalescing with the block to its right
        nextblc_size = GET_SIZE(HDRP(NEXT_BLKP(bp)));
        if (!GET_ALLOC(HDRP(NEXT_BLKP(bp)))) {
            if (nextblc_size + old_size >= asize) {
                // we coalesce
                // first, delete the next block from free list
                delete(NEXT_BLKP(bp));
                // then we construct a large allocated block
                PUT(HDRP(bp), PACK(old_size + nextblc_size, 1));
                PUT(FTRP(bp), PACK(old_size + nextblc_size, 1));
                return oldbp;
            }
        }

        // coalescing with the left won't do any good because
        // everything still needs to be copied over so in all
        // other cases, we free the current block and allocate
        // a new block and copy everything over
        newbp = mm_malloc(size);
        copy_size = old_size - DSIZE;
        memcpy(newbp, oldbp, copy_size);
        mm_free(bp);
        return newbp;
    }
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

    // mm_check();
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

    // coalesce is always called on block that was
    // just freed, so no need to delete bp from free list

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
        // first, delete previous block from free list
        delete(PREV_BLKP(bp));
        // then, update the size information
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    else {
        // combine with both previous and next block
        // first, delete both previous and next block
        delete(PREV_BLKP(bp));
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
    if (DEBUG_PLACE) {
        printf("place at %p %d bytes\n", bp, asize);
    }

    size_t csize = GET_SIZE(HDRP(bp));

    if ((csize - asize) >= MIN_BLOCK_SIZE) {
        // the remainder size is greater than minimum block size
        // delete block from free list
        delete(bp);
        // allocate the block
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        // create new free block from the remainder
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize - asize, 0));
        PUT(FTRP(bp), PACK(csize - asize, 0));
        // insert new block into free list
        // zero out pred/succ to be safe
        PUT(PRED(bp), 0);
        PUT(SUCC(bp), 0);
        insert(bp);
    } else {
        // just allocate the whole block
        delete(bp);
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

/*
 * insert a free block at bp into the segregated list
 */
static void insert(void *bp) {
    if (DEBUG_INSERT) {
        printf("before insert");
        print_block(bp);
        print_heap();
        check_list();
    }

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
        PUT(PRED(bp), (unsigned int) size_class_ptr);
        PUT(SUCC(bp), 0);
    }
    // the appropriate size class is not empty
    // insert the free block at the beginning of the size class
    else {
        // set pred/succ of new free block
        PUT(PRED(bp), (unsigned int) size_class_ptr);
        PUT(SUCC(bp), GET(size_class_ptr));
        // connect the previous head of the size class
        PUT(PRED(GET(size_class_ptr)), bp_val);
        // change heap array
        PUT(size_class_ptr, bp_val);
    }

    if (DEBUG_INSERT) {
        printf("after insert\n");
        print_block(bp);
        print_heap();
        check_list();
    }

}


/*
 * delete a block from free list
 */
static void delete(void *bp) {
    int pre = !is_list_ptr(PRED_BLKP(bp));
    int suc = (SUCC_BLKP(bp) != (void *) 0);

    if (DEBUG_DELETE) {
        printf("before delete");
        print_block(bp);
        print_heap();
        check_list();
    }

    if (GET_ALLOC(HDRP(bp))) {
        printf("calling delete on an allocated block\n");
        return;
    }

    // if bp is the first block of a free list and has successors
    if (!pre && suc) {
        PUT(PRED_BLKP(bp), (unsigned int) SUCC_BLKP(bp));
        PUT(PRED(SUCC_BLKP(bp)), (unsigned int) PRED_BLKP(bp));
    }

    // if bp is both the first and the last block of a list
    else if (!pre && !suc) {
        PUT(PRED_BLKP(bp), (unsigned int) SUCC_BLKP(bp));
    }

    // if bp is an intermediate block
    else if (pre && suc) {
        PUT(SUCC(PRED_BLKP(bp)), (unsigned int) SUCC_BLKP(bp));
        PUT(PRED(SUCC_BLKP(bp)), (unsigned int) PRED_BLKP(bp));
    }

    // if bp is the last block
    else {
        PUT(SUCC(PRED_BLKP(bp)), 0);
    }

    // finally, zero out the pred and succ of bp to be safe
    PUT(PRED(bp), 0);
    PUT(SUCC(bp), 0);

    if (DEBUG_DELETE) {
        printf("after delete");
        print_block(bp);
        print_heap();
        check_list();
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

static int is_list_ptr(void *ptr) {
    unsigned int ptr_val = (unsigned int) ptr;
    unsigned int start = (unsigned int) freelist_p;
    unsigned int end = start + WSIZE*(NUM_SIZE_CLASS-1);

    // printf("p: %p, end: %p, start: %p", (void *)ptr_val, (void *)end, (void *)start);

    if (ptr_val > end || ptr_val < start)
        return 0;
    if ((end - ptr_val) % WSIZE)
        return 0;
    return 1;
}
