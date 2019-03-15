
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
    "Magma",
    /* First member's full name */
    "Richard Huang",
    /* First member's email address */
    "richardhuang2019@u.northwestern.edu", "by", "himself"
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)


#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/* $begin mallocmacros */
/* Basic constants and macros */
#define WSIZE       4       /* Word and header/footer size (bytes) */ //line:vm:mm:beginconst
#define DSIZE       8       /* Double word size (bytes) */
#define CHUNKSIZE  (1<<14)  /* Extend heap by this amount (bytes) */  //line:vm:mm:endconst 
#define MINSIZE     24
#define MAX(x, y) ((x) > (y)? (x) : (y))  

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc)) //line:vm:mm:pack

#define PACK_COLOR(size, alloc, color)  (((size) | (alloc)) | (color)) 

/* Read and write a word at address p */
#define GET(p)       (*(unsigned int *)(p))            //line:vm:mm:get
#define PUT(p, val)  (*(unsigned int *)(p) = (val))    //line:vm:mm:put

#define GETQ(p)     (*(unsigned long *) (p))
#define PUTQ(p, val)     (*(unsigned long *) (p) = (val))


/* Read the size and allocated fields from address p */
#define GET_SIZE(p)  (GET(p) & ~0x7)                   //line:vm:mm:getsize
#define GET_ALLOC(p) (GET(p) & 0x1)                    //line:vm:mm:getalloc
#define GET_COLOR(p) (GET(p) & 0x2)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)       ((char *)(bp) - WSIZE)                      //line:vm:mm:hdrp
#define FTRP(bp)       ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) //line:vm:mm:ftrp

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE))) //line:vm:mm:nextblkp
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE))) //line:vm:mm:prevblkp
/* $end mallocmacros */

/*Get Ptr to next free block if available*/
#define GET_NEXT_FREE(bp) (GETQ(bp + 0x8)) //should address of next free block
#define GET_PREV_FREE(bp) (GETQ(bp)) //should address of PREVIOUS free block

/*Get Ptr to next free block if available*/
#define GET_RIGHT_CHILD(bp) (GETQ(bp + 0x8)) //should address of next free block
#define GET_LEFT_CHILD(bp) (GETQ(bp)) //should address of PREVIOUS free block


/*set ptr macros*/
#define SET_NEXT_PTR(bp, newptr)   (PUTQ((bp+0x8), newptr))//sets the next pointer
#define SET_PREV_PTR(bp, newptr)   (PUTQ(bp, newptr)) //sets the previous pointer 

/*set ptr macros*/
#define SET_RIGHT_CHILD(bp, newptr)   (PUTQ((bp+0x8), newptr))//sets the next pointer
#define SET_LEFT_CHILD(bp, newptr)   (PUTQ(bp, newptr)) //sets the previous pointer 

// function prototypes
static int normalize(size_t size); 
static void removefreeblock(void *bp);
static void *coalesce(void *bp);
static void place(void *bp, size_t size); 
static void addfreeblock(void *bp);


// pointer to the first block 
static char *firstBlock = 0; 

// pointer to the first block of the explicit list and rover
static char * firstFreeBlock = NULL; 
static char *rover;













//----------------------------------------------------------------------------------------------
/* addfreeblock adds memory block with block pointer bp. It also does all of the needed changes.  
*/

static void addfreeblock(void *bp) {
    SET_PREV_PTR(bp, NULL); 
        SET_NEXT_PTR(bp, firstFreeBlock);

        // point the prev first to new block
        if (firstFreeBlock != NULL) {
            SET_PREV_PTR(firstFreeBlock, bp); 
        }
        firstFreeBlock = (char *) bp;
}


/* 
 * removefreeblock removes block pointed to by bp, and updates the next / prev block pointers (if they exist.) 
 * If bp is the first free block of the list, then we also need to update firstFreeBlock as well
 */
static void removefreeblock(void * bp) {
    

    

    void* bp_prev = (void*) GET_PREV_FREE(bp); 
    void* bp_next = (void*) GET_NEXT_FREE(bp);

    //check if bp is the first free block pointer: 
    if (bp == (void*)firstFreeBlock){
       firstFreeBlock = (char*) bp_next;   
    }
   
    // adjust pointers accordingly
    if( bp_prev != NULL && GET_NEXT_FREE(bp_prev) == bp ){
        SET_NEXT_PTR(bp_prev, bp_next);  
    } 
    if ( bp_next != NULL && GET_PREV_FREE(bp_next) == bp) {
        SET_PREV_PTR(bp_next, bp_prev); 
    } 

}



static void *find_fit(size_t asize) {  
    /* Next fit search */
    char *oldrover = rover;

    /* Search from the rover to the end of list */
    for ( ; GET_SIZE(HDRP(rover)) > 0; rover = NEXT_BLKP(rover))
        if (!GET_ALLOC(HDRP(rover)) && (asize <= GET_SIZE(HDRP(rover))))
            return rover;

    /* search from start of list to old rover */
    for (rover = firstBlock; rover < oldrover; rover = NEXT_BLKP(rover))
        if (!GET_ALLOC(HDRP(rover)) && (asize <= GET_SIZE(HDRP(rover))))
            return rover;

    return NULL;  /* no fit found */
}















/*
 * coalesce takes a [pointer] to a block bp, and coalesces it with adjacent blocks, if they are free, and removes
 * the reference to all blocks other than the final block. 
 * 
 * 
 * 
 */ 

static void* coalesce(void *bp) {


    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    void *prevBlock = PREV_BLKP(bp); 
    void *nextBlock = NEXT_BLKP(bp); 

    if (prev_alloc && next_alloc){
        PUT(HDRP(bp), PACK(size, 0)); 
        PUT(FTRP(bp), PACK(size, 0)); 
        return bp; 
    } 
  
    else if(prev_alloc && !next_alloc){
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        removefreeblock(nextBlock); 
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));  
    } 
    else if(!prev_alloc && next_alloc){
        size+= GET_SIZE(HDRP(prevBlock));
        PUT(FTRP(bp), PACK(size, 0)); 
        PUT(HDRP(prevBlock), PACK(size, 0));
        removefreeblock(PREV_BLKP(bp)); 
        bp = prevBlock; 
    }
    else{
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        removefreeblock(NEXT_BLKP(bp)); 
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0)); 
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        removefreeblock(prevBlock);
        bp = prevBlock; 
    }
    if ((rover > (char *)bp && rover < NEXT_BLKP(bp))) {
        rover = bp;
    }
    return bp; 
}


/*
 * extendHeap extends the heap with a free block and returns its block pointer 
 * working with a min block size of 24 bytes. round up to 8 otherwise  
 * 
 */
static void *extend_heap(size_t words) {
    char *bp;

    // allocate an even number to maintain alignment
    size_t size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE; 

    // error check sbrk 
    if ((long) (bp = mem_sbrk(size)) == -1) {
        return NULL; 
    }
    // initialize header and footer of freeblock
    PUT(HDRP(bp), PACK(size, 0)); 
    PUT(FTRP(bp), PACK(size, 0)); 

    // set the epilogue block
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); 

    // coalesce if the prev block is free, return a pointer to the new memory
    return coalesce(bp); 
}


/*
 * normalize takes in a size request and calculates the amount of space needed to make it a 
 * proper aligned block 
 * 
 */
static int normalize(size_t size) {

    // round up to nearest multiple of 8
    if (size <= 16) {
        return MINSIZE; 
    }
    size += DSIZE - 1; 
    size /= DSIZE; 
    size *= DSIZE; 
    return size + DSIZE; 
}

/*
 * place block of size bytes at start of free block bp and split if remainder 
 * would be as large as th min block size 
 *
 */

static void place(void *bp, size_t size) {

    size_t blockSize = GET_SIZE(HDRP(bp));   
    removefreeblock(bp); 

    if ((blockSize - size) >= MINSIZE) {
         
        PUT(HDRP(bp), PACK(size, 1)); 
        PUT(FTRP(bp), PACK(size, 1)); 

       // go to the next block and split it off  
        bp = NEXT_BLKP(bp); 
        PUT(HDRP(bp), PACK(blockSize - size, 0)); 
        PUT(FTRP(bp), PACK(blockSize - size, 0)); 

        addfreeblock(bp);  
    } else {
        PUT(HDRP(bp), PACK(blockSize, 1)); 
        PUT(FTRP(bp), PACK(blockSize, 1)); 

    }
}



/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void) //only called once, so do some good stuff with this. 
{
    // make enough room for our seglist and the initial blocks
    if((firstBlock = mem_sbrk(4 * WSIZE + 10 * DSIZE) ) == (void *) -1) {
        return -1; 
    }

    // increment firstBlock to point to the first free blocks to store our seglist. 
    firstBlock += 10 * DSIZE; 

    // alignment and prologue blocks to help with edge cases (coalescing a boundary block )
    PUT(firstBlock, 0);
    
    // prologue header
    PUT(firstBlock + (1 * WSIZE), PACK(DSIZE, 1));

    // prologue footer
    PUT(firstBlock + (2 * WSIZE), PACK(DSIZE, 1));

    // epilogue header 
    PUT(firstBlock + (3 * WSIZE), PACK(0, 1)); 

    // point firstBlock at start of prlogue footer (the first byte of the prologue block cuz its empty)
    firstBlock += (2 * WSIZE); 

    rover = firstBlock;
    void *newBlock = extend_heap(CHUNKSIZE/WSIZE); 
    if (newBlock == NULL) {
        return -1; 
    }
    firstFreeBlock = newBlock;
    SET_NEXT_PTR(firstFreeBlock, NULL); 
    SET_PREV_PTR(firstFreeBlock, NULL); 
    return 0;
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{ 
    if (size == 0) {
        return NULL; 
    }
    if (firstBlock == 0) {
        mm_init();
    }
        
    size = normalize(size); 
    void *fitBlock; 
    fitBlock = find_fit(size); 

    if ((fitBlock != NULL)) {
        place(fitBlock, size);  
        return fitBlock;
    }
    size_t extendSize = MAX(size, CHUNKSIZE); 
    void *bp = extend_heap(extendSize/WSIZE); 

    if (bp == NULL) {
        return NULL; 
    }


   addfreeblock(bp); 
   place (bp, size); 
   return bp;  
}


void mm_free(void *ptr)
{
    // ensure validity
    if (ptr == 0) {
        return;
    }   

    // coalesce if necessary and then add to freelist 
    void *bp = coalesce(ptr); 
    addfreeblock(bp); 
    
} 

/*
 * realloc takes dynamically allocated memory at location ptr and changes its current size to the parameter
 * size
 *
 * 
 */
void *mm_realloc(void *ptr, size_t size)
{
    size_t oldsize;
        void *newptr;

        if(size == 0) {
            mm_free(ptr);
            return firstFreeBlock; 
        }

        if(ptr == NULL) {
            return mm_malloc(size);
        }

    oldsize = GET_SIZE(HDRP(ptr)); 

        size_t asize = normalize(size);
        if(asize == oldsize){
        return ptr;     
    }

    if (asize < MINSIZE){
        asize = MINSIZE;
    }

    void * nextptr = NEXT_BLKP(ptr);    
    size_t nextalloc = GET_ALLOC(HDRP(nextptr)); 
    size_t nextptr_size = GET_SIZE(HDRP(nextptr));

    void * prevptr = PREV_BLKP(ptr);  
    size_t prevptr_size = GET_SIZE(FTRP(PREV_BLKP(ptr))); 
    size_t prevalloc = GET_ALLOC(FTRP(PREV_BLKP(ptr)));

    if(prevalloc) {  
        size_t combinedsize = oldsize;

        // the next block is free
        if(!nextalloc) {  
            combinedsize = oldsize + nextptr_size;  
            removefreeblock(nextptr); 
        }
        

        if (combinedsize >= asize){
        
            if((combinedsize - asize) < MINSIZE){
                PUT(HDRP(ptr), PACK(combinedsize, 1));  
                PUT(FTRP(ptr), PACK(combinedsize, 1));          
            } else {
                PUT(HDRP(ptr), PACK(asize, 1));  
                PUT(FTRP(ptr), PACK(asize, 1));  
                void * splitptr = NEXT_BLKP(ptr); 

    
                PUT(HDRP(splitptr), PACK(combinedsize - asize, 0));  
                PUT(FTRP(splitptr), PACK(combinedsize - asize, 0)); 

                addfreeblock(splitptr);
        
            }
            return ptr;
        }
        

    } else {
        //check size; 
        size_t combinedsize = oldsize;
        if(!nextalloc) {
            combinedsize = oldsize + prevptr_size  + nextptr_size; 
            removefreeblock(nextptr); 
        }
        else {
            combinedsize = oldsize + prevptr_size;
        }

        if (combinedsize >= asize){
            
            
            removefreeblock(prevptr); 
            memcpy(prevptr, ptr, (oldsize-8));
        
            if((combinedsize - asize) < MINSIZE){
                PUT(HDRP(prevptr), PACK(combinedsize, 1)); 
                PUT(FTRP(prevptr), PACK(combinedsize, 1));          
            } else {
                PUT(HDRP(prevptr), PACK(asize, 1)); 
                PUT(FTRP(prevptr), PACK(asize, 1)); 
                void * splitptr = NEXT_BLKP(prevptr);

                PUT(HDRP(splitptr), PACK(combinedsize - asize, 0)); 
                PUT(FTRP(splitptr), PACK(combinedsize - asize, 0)); 

                addfreeblock(splitptr);
        
            }
            return prevptr;
        }
    }
    newptr = mm_malloc(size);
    memcpy(newptr, ptr, oldsize);
    mm_free(ptr); 
        return newptr;

}

/*
 *
 * various heap checkers to help with debugging
 *
 */

static void printblock(void *bp) 
{
    size_t hsize, halloc, fsize, falloc;

    hsize = GET_SIZE(HDRP(bp));
    halloc = GET_ALLOC(HDRP(bp));  
    fsize = GET_SIZE(FTRP(bp));
    falloc = GET_ALLOC(FTRP(bp));  

    if (hsize == 0) {
        printf("%p: EOL\n", bp);
        return;
    }

    printf("%p: header: [%ld:%c] footer: [%ld:%c]\n", bp, 
           hsize, (halloc ? 'a' : 'f'), 
           fsize, (falloc ? 'a' : 'f')); 
}

static void checkblock(void *bp) 
{
    
    if ((size_t)bp % 8)
        printf("Error: %p is not doubleword aligned\n", bp);
    if (GET(HDRP(bp)) != GET(FTRP(bp)))
        printf("Error: header does not match footer\n");
}


static void checkList (int verbose) 
{
    printf("@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@ LIST @@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@\n"); 
    char *bp = firstBlock;


    if (verbose)
        printf("Heap (%p):\n", firstBlock);

    if ((GET_SIZE(HDRP(firstBlock)) != DSIZE) || !GET_ALLOC(HDRP(firstBlock)))
        printf("Bad prologue header\n");

    for (bp = firstFreeBlock; bp != NULL; bp = GET_NEXT_FREE(bp)) {
        if (verbose) 
            printblock(bp);
        checkblock(bp);
    }

    if (bp == NULL) {
        return;
    }
    if (verbose)
        printblock(bp);
    if ((GET_SIZE(HDRP(bp)) != 0) || !(GET_ALLOC(HDRP(bp))))
        printf("Bad epilogue header\n");

} 

static void checkheap(int verbose) 
{
    printf("%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% HEAP %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%\n"); 
    char *bp = firstBlock;

    if (verbose)
        printf("Heap (%p):\n", firstBlock);

    if ((GET_SIZE(HDRP(firstBlock)) != DSIZE) || !GET_ALLOC(HDRP(firstBlock)))
        printf("Bad prologue header\n");
    checkblock(firstBlock);

    for (bp = firstBlock; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
        if (verbose) 
            printblock(bp);
        checkblock(bp);
    }

    if (verbose)
        printblock(bp);
    if ((GET_SIZE(HDRP(bp)) != 0) || !(GET_ALLOC(HDRP(bp))))
        printf("Bad epilogue header\n");
}







