/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 * 
 * For out implementation of a dybnamic memory allocator, we used an doubly-linked explicit list to store the freed blocks.
 * To search for the appropriate block size for where to store new allocated blocks, we used a next-fit search method. We 
 * implemented realloc by using mm_malloc and mm_free.

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
    "we <3 popcorn aka group 13",
    /* First member's full name */
    "Ariela Deleon",
    /* First member's email address */
    "Arieladeleon2020@u.northwestern.edu",
    /* Second member's full name (leave blank if none) */
    "Emily Nee",
    /* Second member's email address (leave blank if none) */
    "Emilynee2020@u.northwestern.edu"
};


#define WSIZE 4  /* Word and header/footer size (bytes) */

#define DSIZE 8  /* Double word size (bytes) */

//a heap with a chunk size of 2^16 has optimal performance with this implementation 
#define CHUNKSIZE (1<<16)  /* Extend heap by this amount (bytes) */ 

#define MIN 2*DSIZE // including the header & footer, the minimum value must always be 16 bytes

#define MAX(x, y) ((x) > (y)? (x) : (y) ) 

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc)) 

/* Read and write a word at address p */
#define GET(p)       (*(unsigned int *)(p)) 
#define PUT(p, val) (*(unsigned int *)(p) = (val)) 

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)  (GET(p) & ~0x7) 
#define GET_ALLOC(p) (GET(p) & 0x1) 

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp)       ((char *)(bp) - WSIZE) 
#define FTRP(bp)       ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) 

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp)  ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE))) 
#define PREV_BLKP(bp)  ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE))) 

//additional definitions: 
/* If the block is free, get its next and prev pointers */
#define GET_NEXT(bp) (GET(bp)) //tells you the address of the next block 
#define GET_PREV(bp) (GET(bp + 0x4)) //tells you the address of the previous block 

/* Set the next and previous pointers of bp */
#define SET_NEXT(bp, newptr) (PUT(bp, newptr))
#define SET_PREV(bp, newptr) (PUT((bp + 0x4), newptr))

/* Global variables */ 
static char *heap_listp = 0;  /* Pointer to first block */ 
static char *root_ptr = NULL; 
static char *nextrover; /* next fit rover */ 
static char *rover;

/* Function prototypes for helper functions */
static void *extend_heap(size_t words);
static void place(void *bp, size_t asize);
static void *find_fit(size_t asize);
static void *coalesce(void *bp);
static void printblock(void *bp); 
static void checkheap(int verbose);
static void checkblock(void *bp);

/*Additional function prototypes */ 
static void add_fblock(void *bp); 
static void rem_fblock(void *bp); //frees the block from the list but not from memory
static int multofeight(size_t size); 

/* mm_init - initialize the malloc package */
int mm_init(void)
{
     /* Create the initial empty heap */
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1) // create heap thats 16 bytes large, pointer is called heap_listp
        return -1;
    PUT(heap_listp, 0);                          /* Alignment padding */
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1)); /* Prologue header */ 
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1)); /* Prologue footer */ 
    PUT(heap_listp + (3*WSIZE), PACK(0, 1));     /* Epilogue header */
    heap_listp += (2*WSIZE);                       
   
    rover = heap_listp;

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    void *New_Block = extend_heap(CHUNKSIZE/WSIZE);
    if (New_Block == NULL) {
        return -1;
    }

    root_ptr = New_Block;
    SET_NEXT(root_ptr, NULL);
    SET_PREV(root_ptr, NULL);
    
    return 0;
}

/*   *mm_malloc - Allocate a block with at least size bytes of payload  */
void *mm_malloc(size_t size)
{
    size_t asize;      /* Adjusted block size */
    size_t extendsize; /* Amount to extend heap if no fit */
    char *bp;      

    if (heap_listp == 0){ // if the heap has not been initialized, initialize it
        mm_init();
    }

    /* Ignore spurious requests */
    if (size == 0)
        return NULL;
    
    /* Adjust block size to include overhead and alignment reqs. */
    asize = multofeight(size); // get the adjusted block size (rounds up the given size to a multiple of 8)
    // 

    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL) {  //if there's a block that can fit the data then place the data in the block, update the header and footer of the block, potentially split the block, and return the block pointer 
        place(bp, asize);                  
        return bp;
    }

    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize,CHUNKSIZE); //need to make more space 
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL) //if we can't expand the heap anymore, return NULL
        return NULL;
    
    add_fblock(bp); //add the heap extension to the linked list of freed blocks

    place(bp, asize);
    return bp;
}

/* Free a block */
void mm_free(void *bp)
{
    if (bp == 0) 
        return;

    if (heap_listp == 0){
        mm_init();
    }
 
    void *ptr = coalesce(bp); 
    add_fblock(ptr);
}

/* coalesce - Boundary tag coalescing. Return ptr to coalesced block */
static void *coalesce(void *bp) 
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))); // get the previous block's allocated bit
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp))); // get the next block's allocated bit
    size_t size = GET_SIZE(HDRP(bp)); //get the size of the current block

    void *prev_block = PREV_BLKP(bp); //make a pointer to the previous block
    void *next_block = NEXT_BLKP(bp); //make a pointer to the next block

    // Case 1: Neither the previous nor the next block are free/unallocated, so we can't coalesce 
    if (prev_alloc && next_alloc) { 
        PUT(HDRP(bp), PACK(size, 0)); //update the header & footer's allocated bit to zero
        PUT(FTRP(bp), PACK(size, 0)); 
        return bp;
    }


    // Case 2: The next block is free but the previous is allocated
    else if (prev_alloc && !next_alloc) { 
        size += GET_SIZE(HDRP(NEXT_BLKP(bp))); // update the size to include the next block's size
        PUT(HDRP(bp), PACK(size, 0)); //update the header & footer's allocated bit to zero
        PUT(FTRP(bp), PACK(size,0)); 
        
        rem_fblock(next_block); // remove the next block from the linked list of free blocks
    }

    // Case 3: The previous block is free but the next is allocated
    else if (!prev_alloc && next_alloc) {   
        size += GET_SIZE(HDRP(PREV_BLKP(bp))); // update the size to include the previous block's size
        PUT(FTRP(bp), PACK(size, 0)); //update the footer's allocated bit to zero
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0)); //update the previous block's header's allocated bit to zero

        rem_fblock(PREV_BLKP(bp)); // remove the previous block from the linked list of free blocks
        
        bp = prev_block; //update the pointer to point to the previous block instead
    }

    // Case 4: Both the previous & next block are free/unallocated
    else {    
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + //update the size to include both the previous & next block's size
            GET_SIZE(FTRP(NEXT_BLKP(bp))); 

        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0)); //update the previous block's header's allocated bit to zero
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0)); //update the next block's footer's allocated bit to zero
        
        rem_fblock(prev_block); //remove the previous & next block from the linked list of free blocks
        rem_fblock(next_block);

        bp = prev_block; //update the pointer to point to the previous block instead
    }

    //make sure the rover isn't pointing into the free block that we just coalesced
    if ((rover > (char *)bp && rover < NEXT_BLKP(bp))) { 
        rover = bp;
    }

    return bp;
}

/* mm_realloc - implemented using mm_malloc and mm_free */
void *mm_realloc(void *ptr, size_t size)
{

    size_t old_size; //the size of the current block 
    void *newptr; 
    void *pointer;

    if(size == 0) { //if the new size given is 0, then free the block and return the root pointer to the newly freed block
        mm_free(ptr);
        return root_ptr; 
    }

    if(ptr == NULL) { //if there is no pointer given or given NULL, then allocate a block of the given size
        return mm_malloc(size);
    }

    old_size = GET_SIZE(HDRP(ptr)); // get the current size of the block, before reallocating
    
    size_t asize = multofeight(size); //round up to the nearest multiple of 8

    if(asize == old_size){ //if the current & new size are no different, then simply return the same pointer
        return ptr;     
    }

    size_t new_size = old_size; //first set the combined size to the old size, in case we can't expand left or right 

    void * prev_ptr = PREV_BLKP(ptr); // get the pointer of the previous block
    size_t prevalloc = GET_ALLOC(FTRP(PREV_BLKP(ptr))); // get the allocated bit of the previous block
    size_t prev_ptr_size = GET_SIZE(FTRP(PREV_BLKP(ptr))); // get the size of the previous block

    void * next_ptr = NEXT_BLKP(ptr); // get the pointer of the next block   
    size_t nextalloc = GET_ALLOC(HDRP(next_ptr)); // get the allocated bit of the block (1 or 0)
    size_t next_ptr_size = GET_SIZE(HDRP(next_ptr)); // get the size of the next block

    if(prevalloc) { // if the previous block is allocated/not free

        if(!nextalloc) {  // if the next block is not allocated/free
            new_size = old_size + next_ptr_size; // combine the sizes of current & next 
            rem_fblock(next_ptr); // take the next block out of the linked list of free blocks
        }
        
        pointer = ptr; // set the pointer returned to the pointer provided
    }

    else { //if the previous block is unallocated/free

        if(!nextalloc) { //if the next block is also unallocated/free
            new_size += prev_ptr_size  + next_ptr_size; // add both the previous block size and the next block size
            rem_fblock(next_ptr); // remove the next block from the linked list of free blocks
        }
        else { //only the previous block is free
            new_size += prev_ptr_size; // add the previous block size
        }

        pointer = prev_ptr; // set the pointer returned to the pointer provided's previous block's pointer

        if (new_size >= asize){ //if the combined size is large enough for the size we want (rounded up)

            rem_fblock(prev_ptr); //remove the previous block from the linked list of free blocks
            memcpy(prev_ptr, ptr, (old_size-8)); //copy over the data from the current block to the previous block, minus the header & footer

        }
    }

    if (new_size >= asize){ //if the combined size is large enough for the size we want (rounded up)

        if((new_size - asize) < MIN){ // if the remaining uninitialized space is less than the minimum size, then it cannot be split so we just update the header & footer
            PUT(HDRP(pointer), PACK(new_size, 1)); 
            PUT(FTRP(pointer), PACK(new_size, 1));          
        } 

        else { //if the remaining uninitialized space IS more than or equal to the minimum size, then we can split the current or next block
            PUT(HDRP(pointer), PACK(asize, 1)); //updating the header & footer with only the rounded-up size requested
            PUT(FTRP(pointer), PACK(asize, 1)); 
                //void * splitptr = NEXT_BLKP(prevptr);

            PUT(HDRP(NEXT_BLKP(pointer)), PACK(new_size - asize, 0)); //updating the header & footer of the next block with the uninitilaized remainder size & an allocated bit of 0
            PUT(FTRP(NEXT_BLKP(pointer)), PACK(new_size - asize, 0)); 

            add_fblock(NEXT_BLKP(pointer)); //since the next block is labeled as unallocated, add it to the linked list of free blocks

        }

        return pointer;
        }

        else {        
        
        //copy the old data:
        newptr = mm_malloc(size); //if the combined size is NOT large enough for the size we want, we allocate the new size in a completely new block
        memcpy(newptr, ptr, old_size); //copy over the current pointer's data to the new pointer, keeping the old size
        
        //free the old block:
        mm_free(ptr); //free the current pointer's block and add it to thene linked list of free blocks
        return newptr;
    }
}

/* mm_checkheap - check the heap for correctness */ 
void mm_checkheap(int verbose)  
{ 
    checkheap(verbose);
}


 /* The remaining functions are internal helper functions */

/*extend_heap - extend heap with free block and return its block pointer */
static void *extend_heap(size_t words) 
{ 
    char *bp;
    size_t size;

    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
    if ((long)(bp = mem_sbrk(size)) == -1)  
        return NULL;                                        

    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0));         /* Free block header */  
    PUT(FTRP(bp), PACK(size, 0));         /* Free block footer */
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */


    /* Coalesce if the previous block was free */
    return coalesce(bp);                                       
}

//place - Place block of asize bytes at start of free block bp and split if remainder would be at least minimum block size
static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp));   //gets the block's size 

    if ((csize - asize) >= (MIN)) { //if the remainder of the block after splitting would be greater than or equal to the minimum block size, then split the block. 
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1)); //you need to place the new allocated block before moving to the next block 
        rem_fblock(bp); 
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize-asize, 0)); //mark the second half of the split block as unallocated 
        PUT(FTRP(bp), PACK(csize-asize, 0));
        add_fblock(bp); 
    }
    else { //if it's not necessary to split the block 
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
        rem_fblock(bp); 
    }
}

/* find_fit - Find a fit for a block with asize bytes */
static void *find_fit(size_t asize)
{
    char *oldrover = rover;

    /* Search from the rover to the end of list */
    for ( ; GET_SIZE(HDRP(rover)) > 0; rover = NEXT_BLKP(rover))
        if (!GET_ALLOC(HDRP(rover)) && (asize <= GET_SIZE(HDRP(rover))))
            return rover;

    /* Search from start of list to old rover */
    for (rover = heap_listp; rover < oldrover; rover = NEXT_BLKP(rover))
        if (!GET_ALLOC(HDRP(rover)) && (asize <= GET_SIZE(HDRP(rover))))
            return rover;

    return NULL; /* no fit found */
}

static void printblock(void *bp) 
{
    size_t hsize, halloc, fsize, falloc;

    checkheap(0);
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

void checkheap(int verbose) 
{
    char *bp = heap_listp; 
    if (verbose)
        printf("Heap (%p):\n", heap_listp);

    if ((GET_SIZE(HDRP(heap_listp)) != DSIZE) || !GET_ALLOC(HDRP(heap_listp))) 
        printf("Bad prologue header\n"); 
    checkblock(heap_listp);

    for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) { 
        if (verbose) 
            printblock(bp);
        checkblock(bp);
    }

    if (verbose)
        printblock(bp);
    if ((GET_SIZE(HDRP(bp)) != 0) || !(GET_ALLOC(HDRP(bp)))) 
        printf("Bad epilogue header\n");
}

static void add_fblock(void *bp) //add a newly freed block to the linked list of freed blocks
{
    SET_PREV(bp, NULL); // set the previous pointer to NULL, since the block is now at the front of the list with no predecessor
    SET_NEXT(bp, root_ptr); // set the next pointer to what the root pointer was pointing to previously

    if (root_ptr != NULL){ // as long as the linked list of freed blocks is not empty
        SET_PREV(root_ptr, bp); // set the first freed block's previous pointer to the newly freed block
    }
    
    root_ptr = (char *) bp; // the root pointer now points to the block you just added to the linked list
}

void rem_fblock(void *bp) //remove a block from the linked list of freed blocks
{
  void * next_ptr = (void *) GET_NEXT(bp); //pointer to the next free block
  void * prev_ptr = (void *) GET_PREV(bp); //pointer to the previous free block

  if (bp == (void *)root_ptr) //if the block you're removing is the latest added to the list
  {
    root_ptr = (char *)next_ptr; //make the root pointer point to the next free block instead
  }

  if ( prev_ptr != NULL && GET_NEXT(prev_ptr) == (void *)bp ) //as long as the previous block is not NULL (current block is not the latest added) & the previous block's next pointer is indeed the current block
  {
    SET_NEXT(prev_ptr, next_ptr); //set the previous block's next pointer to the current block's next block
  }

  if ( next_ptr != NULL && GET_PREV(next_ptr) == (void *)bp ) //as long as the next block is not NULL (current block is not the last in the list) & the next block's previous pointer is indeed the current block
  {
    SET_PREV(next_ptr, prev_ptr); //set the next block's previous pointer to the current block's previous block
  }
}

/* rounds up size and returns the nearest multiple of 8 or returns 16 if size <= 8 */ 
static int multofeight(size_t size) {
    if (size <= DSIZE) { //if size is <= 8, then return 16
        return MIN; 
    }

    //if size > 8 then round up size to the nearest multiple of 8 
    return (DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE));
}




