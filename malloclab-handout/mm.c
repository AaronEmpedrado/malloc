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

//Test2
//test again

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "team cool",    
    /* First member's full name */
    "Aaron-Patrick Empedrado",
    /* First member's NetID */
    "abe0859",
    /* Second member's full name (leave blank if none) */
    "Rochelle Compendio",
    /* Second member's NetID */
    "rac2061"
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)


#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

//prototypes for static functions
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);

static int mm_check(void);

/* Global Variables */
static char *heap_listp = 0;    //points to the prologue block
static char *freeblk_root = NULL;   //points to the first block of the explicit list
static char *rover;                 //for next fit implementation


/* Basic constants and macros */
#define WSIZE 4     /* Word and header/footer size (bytes)  => 32 bit system */
#define DSIZE 8     /* Double word size (bytes) */
#define CHUNKSIZE (1<<12) /* Extend heap by this amount (4096 bytes) */
#define MIN_BLK_SIZE 2*DSIZE  /* For implicit free list, using header and footer (nonzero payload) */        

/* Macros for offset from bp (pointer to payload) */
#define NEXT_OFFSET WSIZE
#define PREV_OFFSET 0

#define MAX(x, y) ((x) > (y)? (x) : (y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc) ((size) | (alloc))        //basically initializes a header or footer

/* Read and write a word at address p */
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p) (GET(p) & ~0x7)     //zero out last 3 bits (only consider size)
#define GET_ALLOC(p) (GET(p) & 0x1)     //obtain last bit (allocated or not)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))     //((char *)(bp) - WSIZE)) points to header
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))     //((char *)(bp) - DSIZE)) points to footer of prev block

/* Explicit List macros */
/* Get ptr to next or prev free block in explicit list */
#define GET_NEXT_FREE(bp) (GET(bp + NEXT_OFFSET))
#define GET_PREV_FREE(bp) (GET(bp + PREV_OFFSET))

/* Macros to update pointers */
#define SET_NEXT_PTR(bp, newptr) (PUT(bp + NEXT_OFFSET, newptr))
#define SET_PREV_PTR(bp, newptr) (PUT(bp + PREV_OFFSET, newptr))


/* Prototypes for helper functions */
static int multofeight(size_t asize);
static void delete_freeblk(void *bp);
static void add_freeblk(void *bp);

/* Prototypes for heap checker helper functions */
static int check_invariant(void);

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    /* Create the initial empty heap */
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1)
        return -1;
    PUT(heap_listp, 0); /* Alignment padding */
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1)); /* Prologue header */
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1)); /* Prologue footer */
    PUT(heap_listp + (3*WSIZE), PACK(0, 1)); /* Epilogue header */
    heap_listp += (2*WSIZE);

    rover = heap_listp; //initialize the rover to first block

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    void *new_blkp = extend_heap(CHUNKSIZE/WSIZE);
    if (new_blkp == NULL)
        return -1;              //if any error occurred
    freeblk_root = new_blkp;
    /* Initialize pointers */
    SET_NEXT_PTR(freeblk_root, NULL);
    SET_PREV_PTR(freeblk_root, NULL);
    return 0;                   //we're all good
}


// added for implicit list book code
static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc) {                 /* Case 1 */
        return bp;                                  /* Previous and next blocks both allocated */
    }

    else if (prev_alloc && !next_alloc) {           /* Case 2 */
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));      /* Previous block allocated, next block free */
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size,0));
    }

    else if (!prev_alloc && next_alloc) {           /* Case 3 */
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));      /* Previous block free, next block allocated */
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    else {                                          /* Case 4 */
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) +     /* Previous and next blocks both free */
            GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    return bp;
}


void *mm_malloc(size_t size)
{
    size_t asize; /* Adjusted block size */
    size_t extendsize; /* Amount to extend heap if no fit */
    char *bp;

    /* Ignore spurious requests */
    if (size == 0)
        return NULL;

    /* Adjust block size to include overhead and alignment reqs. */
    if (size <= DSIZE)
        asize = 2*DSIZE;
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);

    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL) {
        place(bp, asize);
        return bp;
    }

    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize,CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    return bp;
}


/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 *  memcpy(x,y,z): copies z bytes from y to x
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *oldptr = ptr;
    void *newptr;
    size_t aSize;
    size_t oldSize, newSize = size;

    if(size == 0) {         //size == 0  case
        mm_free(ptr);
        return freeblk_root;    //or should it be NULL?
    }

    // newptr = mm_malloc(size);
    // if (newptr == NULL)     
    //     return NULL;
    if(ptr == NULL){        //ptr is null case
        return mm_malloc(size);
    }

    //Falls through if ptr is not NULL and we actually reallocate
    oldSize = GET_SIZE(HDRP(oldptr));       
    aSize = multofeight(size);              //adjust the realloc size

    /* No change in size => don't do anything */
    if(oldSize == aSize) {
        return oldptr;
    }

    /* Initialize some useful pointers and relevant data */
    void   *nextptr = NEXT_BLKP(ptr);    
    size_t nextalloc = GET_ALLOC(HDRP(nextptr)); 
    size_t nextptr_size = GET_SIZE(HDRP(nextptr));

    void   *prevptr = PREV_BLKP(ptr);  
    size_t prevalloc = GET_ALLOC(FTRP(prevptr));
    size_t prevptr_size = GET_SIZE(FTRP(prevptr)); 


    size_t mergeSize = oldSize;
    /* Case where previous block is allocated */
    if(prevalloc) {
        /* Previous Allocated, Next is free */
        if(!nextalloc) {
            mergeSize += nextptr_size;
            delete_freeblk(nextptr);
        }
        /* Check if we need to re-align */
        if(mergeSize >= aSize) {
            /* Do we need to realign? */
            if((mergeSize - aSize) < MIN_BLK_SIZE) {
                PUT(HDRP(ptr), PACK(mergeSize, 1));     //update tags
                PUT(FTRP(ptr), PACK(mergeSize, 1));
            } else {
                PUT(HDRP(ptr), PACK(aSize, 1));
                PUT(FTRP(ptr), PACK(aSize, 1));

                /* Now free the next */
                PUT(HDRP(nextptr), PACK(mergeSize - aSize, 0));
                PUT(FTRP(nextptr), PACK(mergeSize - aSize, 0));

                addfreeblock(nextptr);
            }
            return ptr;
        }
    } else {  /* Case where previous block was free */
        /* Update mergeSize */
        /* Previous free, next is free */
        if(!nextalloc) {
            mergeSize += prevptr_size + nextptr_size;
            delete_freeblk(nextptr);
        } else {    /* Previous free, next allocated */
            mergeSize += prevptr_size;
        }

        if(mergeSize >= aSize) {
            delete_freeblk(prevptr);
            memcpy(prevptr, ptr, (oldSize - DSIZE));

            if((mergeSize - aSize) < MIN_BLK_SIZE) {
                PUT(HDRP(prevptr), PACK(mergeSize, 1));
                PUT(FTRP(prevptr), PACK(mergeSize, 1));
            } else {
                PUT(HDRP(prevptr), PACK(aSize, 1));
                PUT(FTRP(prevptr), PACK(aSize, 1));

                PUT(HDRP(ptr), PACK(mergeSize - aSize, 0));
                PUT(FTRP(ptr), PACK(mergeSize - aSize, 0));
                addfreeblock(ptr);
            }
            return  prevptr;
        }
    }
    newptr = mm_malloc(size);
    memcpy(newptr, ptr, oldSize);
    mm_free(ptr);
    return newptr;
}


/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{
    /* check if bp is a valid ptr */
    if(bp == NULL) {
        return;
    }

    coalesce(bp);                       //coalesce if contiguous free blocks
    addfreeblock(bp);                   //add to explicit free list
}

/*
 * Helper functions 
 *
 */

/* Finds where the block we want to allocate should go */
static void *find_fit(size_t asize) {
    /* Changed first fit to a next fit search */
    char *old_rover = rover;        //make a copy of rover

    /* Traverse the list to the end, looking for a fit */
    while(GET_SIZE(HDRP(rover)) != 0) {         //size 0 block indicates end
        if(!GET_ALLOC(HDRP(rover)) && (asize <= GET_SIZE(HDRP(rover)))) {  
            return rover;
        }
        rover = NEXT_BLKP(rover);       //point to next rover
    }
    /* Traverse the first half of list [root, rover] if still haven't found a fit */
    for(rover = freeblk_root; rover < old_rover; rover = NEXT_BLKP(rover)){
        if(!GET_ALLOC(HDRP(rover)) && (asize <= GET_SIZE()HDRP(rover))){
            return rover;
        }
    }
    return NULL;       //no fit found :[
}


/* Function to actually place the allocated block */
static void place(void *bp, size_t asize) {
    size_t csize = GET_SIZE(HDRP(bp));
    delete_freeblk(bp);
    
    if ((csize - asize) >= MIN_BLK_SIZE) {         /* Splits only if remainder is at least minimum block size */
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize-asize, 0));
        PUT(FTRP(bp), PACK(csize-asize, 0));

        addfreeblock(bp);
    }
    else {                                     /* Remainder not enough for another free => have unused bytes */
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}


/* Extends the heap by the CHUNKSIZE */
static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;

    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0)); /* Free block header */
    PUT(FTRP(bp), PACK(size, 0)); /* Free block footer */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */

    /* Coalesce if the previous end of heap block was free */
    return coalesce(bp);
}

/* Rounds sizes to align by DWORDs */
static int multofeight(size_t asize) {
    if(asize <= DSIZE) {
        return MIN_BLK_SIZE;
    } else{
        return (asize + (DSIZE - (asize % DSIZE)) );    //round up to next mult of 8
    }
}

/* Deleting a free block from the explicit list, updating pointers appropriately */
static void delete_freeblk(void *bp) {
    void *prev_blk = (void *)(GET_PREV_FREE(bp));
    void *next_blk = (void *)(GET_NEXT_FREE(bp));

    /* check for edge case => are we root? */
    if(bp == (void *)freeblk_root) {
        freeblk_root = (char *) next_blk;       //update root
    }

    /* if not root, update pointers appropriately */
    if(prev_blk != NULL && GET_NEXT_FREE(prev_blk) == bp) {
        SET_NEXT_PTR(prev_blk, next_blk);       //link prev to next
    }
    if(next_blk != NULL && GET_PREV_FREE(next_blk) == bp) {
        SET_PREV_PTR(next_blk, prev_blk);       //link next to prev
    }
}


/* Adding a free block to the front of explicit list, updating pointers appropriately */
static void add_freeblk(void *bp) {
    //Initialize new block's pointers
    SET_PREV_PTR(bp, NULL);     
    SET_NEXT_PTR(bp, freeblk_root);
    //Update Root
    if(freeblk_root != NULL) {
        SET_PREV_PTR(freeblk_root, bp);     //link root blk to bp
    }
    freeblk_root = (char *)bp;              //update the addition as the new root
}


/* Heap Checker */
static int mm_check(void) {
    int sum = 0;

    sum += check_invariant();
    /*
     * Implement this
     //is every block in the free list marked as free?
     //are there any contiguous free blocks that somehow escaped coalescing?
     //is every free block actually in the free list?
     //do the pointers in the free list point to valid free blocks?
     //do any allocated blocks overlap?
     //do the pointers in a heap block point to valid heap addresses?

    //check invariants
        //prologue block is 8byte allocated
        //epilogue block is 0 byte allocated

     * 
     * write subroutines for each check and call in here
     * have them return 0 if they're good and keep adding the values
     * if our sum ends up being 0, return the invert of that (nonzero means we good)
     */
    return sum;
}

/*
 * Helper functions for the heap checker
 */

/* Check invariant of the prologue and epilogue blocks */
static int check_invariant(void){
     // Check the prologue block is 8 byte allocated 
    char *PRO_BLKP = heap_listp;
    char *PRO_HDRP = HDRP(PRO_BLKP);
    char *PRO_FTRP = FTRP(PRO_BLKP);
    char *EPI_BLPK = mem_heap_hi();

    //Check the prologue block's invariance
    if(!(GET_SIZE(PRO_HDRP) == 8 && GET_ALLOC(PRO_HDRP) == 1 &&
         GET_SIZE(PRO_FTRP) == 8 && GET_ALLOC(PRO_FTRP) == 1)) {
        printf("Prologue invariant failed.");
        return 1;       //error
    }   //Check the epilogue invariance 
    else if(GET_SIZE(EPI_BLPK) == 0 && GET_ALLOC(EPI_BLPK) == 1) {
        printf("Epilogue invariant failed.");
        return 1;       //error
    }
    //Both invariants pass
    return 0;
}




