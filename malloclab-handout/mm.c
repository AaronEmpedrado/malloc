/*
 * mm.c - Aaron and Chelly's Version
 * 
 * Implementation: Explicit Free List using Doubly Link Lists for free blocks 
 *
 * Blocks are organized like the following:
 * Header | Prev_Ptr | Next_Ptr | Payload | Footer
 * Optimized further by taking out pointers from allocated blocks
 *
 * Insertions into the free list are at the root/head for simplicity
 *
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
    "team swiggity swag",    
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

/* Prototypes for static functions */
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);

static int mm_check(void);

/* Global Variables */
static void *heap_listp = 0;    //points to the prologue block
static void *freeblk_root = 0;   //points to the first block of the explicit list
// static char *rover;                 //for next fit implementation


/* Basic constants and macros */
#define WSIZE 4     /* Word and header/footer size (bytes)  => 32 bit system */
#define DSIZE 8     /* Double word size (bytes) */
#define CHUNKSIZE (1<<13) /* Extend heap by this amount (4096*2 bytes) */
#define MIN_BLK_SIZE 3*DSIZE  /* For explicit free list, HDR,PTRS,Payload,FTR = 24bytes */        

/* Macros for offset from bp (pointer to payload) */
#define NEXT_OFFSET WSIZE
#define PREV_OFFSET 0

#define MAX(x, y) ((x) > (y)? (x) : (y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc) ((size) | (alloc))        //basically initializes a header or footer

/* Read and write a word at address p */
#define GET(p) (*(size_t *)(p))
#define PUT(p, val) (*(size_t *)(p) = (val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p) (GET(p) & ~0x7)     //zero out last 3 bits (only consider size)
#define GET_ALLOC(p) (GET(p) & 0x1)     //obtain last bit (allocated or not)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp) ((void *)(bp) - WSIZE)
#define FTRP(bp) ((void *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp) ((void *)(bp) + GET_SIZE(HDRP(bp)))     //((char *)(bp) - WSIZE)) points to header
#define PREV_BLKP(bp) ((void *)(bp) - GET_SIZE(HDRP(bp) - WSIZE))     //((char *)(bp) - DSIZE)) points to footer of prev block

/* Explicit List macros */
/* Get ptr to next or prev free block in explicit list */
#define GET_NEXT_FREE(bp) (*(void **)(bp + NEXT_OFFSET))
#define GET_PREV_FREE(bp) (*(void **)(bp + PREV_OFFSET))

/* Macros to update pointers */
#define SET_NEXT_PTR(bp, newptr) (GET_NEXT_FREE(bp) = newptr)
#define SET_PREV_PTR(bp, newptr) (GET_PREV_FREE(bp) = newptr)


/* Prototypes for helper functions */
// static int multofeight(size_t asize);
static void delete_freeblk(void *bp);
// static void add_freeblk(void *bp); => replaced with more convenient insert func for new DLL implementation (below)
static void insertAtRoot(void *bp);

/* Prototypes for heap checker helper functions */
static int check_invariant(void);
static void printBLK(void *bp);
static void checkBLK(void *bp);


/*******************************************************************************/

/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    /* Create the initial empty heap */
    if ((heap_listp = mem_sbrk(2*MIN_BLK_SIZE)) == (void *)-1)
        return -1;
    PUT(heap_listp, 0); /* Alignment padding */
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1)); /* Prologue header */
    PUT(heap_listp + (2*WSIZE), 0); /* Prologue footer */
    PUT(heap_listp + (3*WSIZE), 0); /* Epilogue header */
    freeblk_root = heap_listp + DSIZE;  /* initialize root */

    /* Extend the empty heap with a free block of 4 bytes */
    if (extend_heap(WSIZE) == NULL)
        return -1;              //if any error occurred (weren't able to extend)
    return 0;                   //we're all good => return 0
}

/*
 * Coalesce if necessary (contiguous free blocks) to avoid false fragmentation 
 */
static void *coalesce(void *bp)
{
    //printf("Inside coalesce! \n");        //for debugging
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))) || PREV_BLKP(bp) == bp;
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    // /* Added pointers for xlist */
    // void *prev_blk = PREV_BLKP(bp);
    // void *next_blk = NEXT_BLKP(bp);
    /* Found a way to avoid having to declare ptrs => helper funcs*/

    if (prev_alloc && next_alloc) {                 /* Case 1 */
        insertAtRoot(bp);
        return bp;                                  /* Previous and next blocks both allocated */
    }

    else if (prev_alloc && !next_alloc) {           /* Case 2 */
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));      /* Previous block allocated, next block free */
        delete_freeblk(NEXT_BLKP(bp));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size,0));
    }

    else if (!prev_alloc && next_alloc) {           /* Case 3 */
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));      /* Previous block free, next block allocated */
        delete_freeblk(PREV_BLKP(bp));
        PUT(FTRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    else {                                          /* Case 4 */
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) +     /* Previous and next blocks both free */
                GET_SIZE(HDRP(NEXT_BLKP(bp)));
        delete_freeblk(NEXT_BLKP(bp));
        delete_freeblk(PREV_BLKP(bp));                   //remember to delete both prev and next in case 4
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }
    insertAtRoot(bp);   /* Handled cases, now insert it in front of free list */
    return bp;
}

/*
 * mm_malloc which allocates blocks according to the alignment
 * the allocater shouldn't collide with other allocated blocks
 * allocated by incrementing our ptr
 */
void *mm_malloc(size_t size)
{
    size_t asize;           /* Adjusted block size */
    size_t extendsize;      /* Amount to extend heap if no fit */
    void *bp;

    /* Ignore spurious requests */
    if (size == 0)
        return NULL;

    /* Figure out how much we should allocate */
    asize = MAX(MIN_BLK_SIZE, ALIGN(size) + DSIZE);

    /* Adjust block size to include overhead and alignment reqs. */
    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL) {
        //printf("Attempting to allocate: searching free list atm.\n");         //For debugging
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
    size_t oldSize = GET_SIZE(HDRP(ptr));
    size_t aSize = MAX(ALIGN(size) + DSIZE, 2*DSIZE);

    /* A couple simple check cases */
    if(size == 0) {         //size == 0  case
        mm_free(ptr);
        return NULL;
    }
    if(ptr == NULL){        //ptr is null case
        return mm_malloc(size);
    }
    if(aSize <= oldSize) {
        return ptr;
    } else {        //aSize > oldSize
        size_t isNextAlloc = GET_ALLOC(HDRP(NEXT_BLKP(ptr)));
        size_t mergeSize = oldSize + GET_SIZE(HDRP(NEXT_BLKP(ptr)));
        if(!isNextAlloc && (mergeSize >= aSize)) {
            /* Readjust to bigger block size, update tags */
            delete_freeblk(NEXT_BLKP(ptr));
            PUT(HDRP(ptr), PACK(mergeSize, 1));
            PUT(FTRP(ptr), PACK(mergeSize, 1));
            return ptr;
        } else {
            void *newptr = mm_malloc(aSize);
            place(newptr, aSize);            
            memcpy(newptr, ptr, aSize);
            mm_free(ptr);
            return newptr;
        }
    }
}


/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{
    /* check if bp is a valid ptr */
    if(bp == 0) {
        return;
    }
    /* Check that we have initialized the heap */
    if(heap_listp == 0) {
        mm_init();
    }

    size_t size = GET_SIZE(HDRP(bp));
    /* Update Tags (free) */
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));

    coalesce(bp);                       //coalesce if contiguous free blocks
}

/*********************************************************************************************/
/*
 * Helper functions 
 *
 */
/*********************************************************************************************/

/* Finds where the block we want to allocate should go */
static void *find_fit(size_t asize) {
    /* Went back to first fit search approach for simplicity */
    void *bp;
    /* Just traverse the list until we find a fit */
    for(bp = freeblk_root; GET_ALLOC(HDRP(bp)) == 0; bp = GET_NEXT_FREE(bp)){
        if(!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {     /* Fit found */
            return bp;
        }
    }
    return NULL;       //no fit found :[
}


/* Function to actually place the allocated block */
static void place(void *bp, size_t asize) {
    size_t csize = GET_SIZE(HDRP(bp));
    
    if ((csize - asize) >= (4*WSIZE)) {         /* Splits only if remainder is at least minimum block size */
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        delete_freeblk(bp);
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize-asize, 0));
        PUT(FTRP(bp), PACK(csize-asize, 0));

        insertAtRoot(bp);
    }
    else {                                     /* Remainder not enough for another free => have unused bytes */
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
        delete_freeblk(bp);
    }
}


/* Extends the heap by the CHUNKSIZE */
static void *extend_heap(size_t words)
{
    void *bp;
    size_t size;

    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
    if((bp = mem_sbrk(size)) == (void *)-1){
        return NULL;
    }
    if (size < MIN_BLK_SIZE){
        size = MIN_BLK_SIZE;        /* Round it up to align */
    }

    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0)); /* Free block header */
    PUT(FTRP(bp), PACK(size, 0)); /* Free block footer */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */

    /* Coalesce if the previous end of heap block was free */
    return coalesce(bp);
}


/* Opted to just use the align macro instead */
// /* Rounds sizes to align by DWORDs */
// static int multofeight(size_t asize) {
//     if(asize <= DSIZE) {
//         return MIN_BLK_SIZE;
//     } else{
//         return (asize + (DSIZE - (asize % DSIZE)) );    //round up to next mult of 8
//     }
// }

/* Deleting a free block from the explicit list, updating pointers appropriately */
static void delete_freeblk(void *bp) {
    /* Having implementation insert only at head simplifies immensely! */
    /* Update forward links */
    if(GET_PREV_FREE(bp)){  /* Case: Not root */
        SET_NEXT_PTR(GET_PREV_FREE(bp), GET_NEXT_FREE(bp));
    }else {
        /* Case: We are root */
        freeblk_root = GET_NEXT_FREE(bp);
    }
    /* Now we can update backwards links */
    SET_PREV_PTR(GET_NEXT_FREE(bp), GET_PREV_FREE(bp));
}


/* Replacing this with a more convenient insert func for new DLL implementation */
// /* Adding a free block to the front of explicit list, updating pointers appropriately */
// static void add_freeblk(void *bp) {
//     //Initialize new block's pointers
//     SET_PREV_PTR(bp, NULL);     
//     SET_NEXT_PTR(bp, freeblk_root);
//     //Update Root
//     if(freeblk_root != NULL) {
//         SET_PREV_PTR(freeblk_root, bp);     //link root blk to bp
//     }
//     freeblk_root = (char *)bp;              //update the addition as the new root
// }



/*
 * insertAtRoot adds our free block into the beginning of the list for simplicity
 */
static void insertAtRoot(void *bp) {
    /* Prep bp as a root node */
    SET_PREV_PTR(bp, NULL);
    if((GET_NEXT_FREE(bp) = freeblk_root) == NULL)  //bp is first node
        SET_NEXT_PTR(bp, freeblk_root);     //link new root to old root
    SET_PREV_PTR(freeblk_root, bp);         //link old root to new root
    freeblk_root = bp;                      //update global root ptr
}


/* Heap Checker */
// static int mm_check(void) {
//     int sum = 0;

//     sum += check_invariant();
    
//      * Implement this
//      //is every block in the free list marked as free?
//      //are there any contiguous free blocks that somehow escaped coalescing?
//      //is every free block actually in the free list?
//      //do the pointers in the free list point to valid free blocks?
//      //do any allocated blocks overlap?
//      //do the pointers in a heap block point to valid heap addresses?

//     //check invariants
//         //prologue block is 8byte allocated
//         //epilogue block is 0 byte allocated

//      * 
//      * write subroutines for each check and call in here
//      * have them return 0 if they're good and keep adding the values
//      * if our sum ends up being 0, return the invert of that (nonzero means we good)
     
//     return sum;
// }

/*
 * Helper functions for the heap checker
 */

/* Check invariant of the prologue and epilogue blocks */
// static int check_invariant(void){
//      // Check the prologue block is 8 byte allocated 
//     char *PRO_BLKP = heap_listp;
//     char *PRO_HDRP = HDRP(PRO_BLKP);
//     char *PRO_FTRP = FTRP(PRO_BLKP);
//     char *EPI_BLPK = mem_heap_hi();

//     //Check the prologue block's invariance
//     if(!(GET_SIZE(PRO_HDRP) == 8 && GET_ALLOC(PRO_HDRP) == 1 &&
//          GET_SIZE(PRO_FTRP) == 8 && GET_ALLOC(PRO_FTRP) == 1)) {
//         printf("Prologue invariant failed.");
//         return 1;       //error
//     }   //Check the epilogue invariance 
//     else if(GET_SIZE(EPI_BLPK) == 0 && GET_ALLOC(EPI_BLPK) == 1) {
//         printf("Epilogue invariant failed.");
//         return 1;       //error
//     }
//     //Both invariants pass
//     return 0;
// }




