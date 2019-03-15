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
/*
 *
 *
 *
 * todo dchange removefreerblock function, see where used 
 * change mm_free
 */

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
    "richardhuang2019@u.northwestern.edu",
    /* Second member's full name (leave blank if none) */
    "Thomas Yang",
    /* Second member's email address (leave blank if none) */
    "thomasyang@u.northwestern.edu"
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
#define CHUNKSIZE  (1<<10)  /* Extend heap by this amount (bytes) */  //line:vm:mm:endconst 
#define MINSIZE     24
#define MAX(x, y) ((x) > (y)? (x) : (y))  

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc)  ((size) | (alloc)) //line:vm:mm:pack

/* Read and write a word at address p */
#define GET(p)       (*(unsigned int *)(p))            //line:vm:mm:get
#define PUT(p, val)  (*(unsigned int *)(p) = (val))    //line:vm:mm:put
#define PUT_TAG(p, val) (*(unsigned int *)(p) = (val)|| (0x2) 

#define GETQ(p)     (*(unsigned long *) (p))
#define PUTQ(p, val)     (*(unsigned long *) (p) = (val))


/* Read the size and allocated fields from address p */
#define GET_SIZE(p)  (GET(p) & ~0x7)                   //line:vm:mm:getsize
#define GET_ALLOC(p) (GET(p) & 0x1)                    //line:vm:mm:getalloc
#define GET_TAG(p)   (GET(p) & 0x2)

#define CLEAR_TAG(p) (*(unsigned int *)(p) = (val)&&(~0x2))

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


/*set ptr macros*/
#define SET_NEXT_PTR(bp, newptr)   (PUTQ((bp+0x8), newptr))//sets the next pointer
#define SET_PREV_PTR(bp, newptr)   (PUTQ(bp, newptr)) //sets the previous pointer 

// function prototypes, yayyyyy
static int normalize(size_t size); 
static void removefreeblock(void *bp);
static void *coalesce(void *bp);
static void place(void *bp, size_t size); 
static void checkList(int verbose); 
static void checkheap(int verbose); 
static int getBucket(int size); 
static void putInSegList(void *bp); 
// pointer to the first block 
static char *firstBlock = 0; 

// pointer to the seglist
static int **segList;
static long * sizeList; 


// pointer to the first free block in the explicit list 
static char *firstFreeBlock = NULL; //(?) - do you wanna make the global pointer?

// index of the minmium size free list 
static char *minFree; // just minimum size? 

/* 
 * removefreeblock removes block pointed to by bp, and updates the next / prev block pointers (if they exist.) 
 * If bp is the first free block of the list, then we also need to update firstFreeBlock as well
 *
 *
 */
static void removefreeblock(void * bp) {

                                                                /*printf("******************remove block*****\n");*/
    //make sure it isn't a prologue or epilogue block 
    size_t self_size = GET_SIZE(HDRP(bp));
    if (self_size < (size_t)24 ){
        return;
    }
    
    //check if bp is a valid block pointer? 

    if((unsigned long)bp % 8){
        return; // pointer isn't 8-byte aligned;
    } 

                                                                                                                /*printf("~`````````````````````````````````````````````````````````````````````````\n\n\nself alloc"); */
    size_t self_alloc = GET_ALLOC(HDRP(bp)); 
                                                                                                                                            /*printf("%d\n", (int) self_alloc); */
    if(self_alloc){
        return; //cannot remove a non-free block
    } 







// the real stuff starts here







    
    void* bp_prev = (void*) GET_PREV_FREE(bp); 
    void* bp_next = (void*) GET_NEXT_FREE(bp);

    //check if bp is the first free block pointer of a seg list : 
    int idx = getBucket((int) GET_SIZE(HDRP(bp))); 
                                                                                                                /*printf("#######################################################################################\n\n"); */
                                                                                                            /*printf("this is the index %d\n", idx);  */
                                                                                                                                        /*printf("%d\n", (int) self_size); */
                                                                                                                    /*printf(" do i even try to remove it\n\n\n"); */
    /*if (bp == (void*) segList[idx]) {*/
                                                                                                                                                                /*printf(" i try to remove it\n\n\n"); */
       /*segList[idx] = (int*) bp_next;   */
    /*}*/
    // add next and prev checks here 
    /*if( bp_prev != NULL && GET_NEXT_FREE(bp_prev) == bp ){*/
        /*SET_NEXT_PTR(bp_prev, bp_next);  */
    /*} */
    /*if ( bp_next != NULL && GET_PREV_FREE(bp_next) == bp) {*/
        /*SET_PREV_PTR(bp_next, bp_prev); */
    /*} */
    if (bp_next != NULL) {
        if (bp_prev != NULL) {
            SET_NEXT_PTR(bp_prev, bp_next); 
            SET_PREV_PTR(bp_next, bp_prev); 
        } else {
            // bp_prev is null, and you're at the start of a list'
            SET_PREV_PTR(bp_next, NULL); 
            segList[idx] = bp_next;
        }
    } else {
        // youre at the end of a list 
        if (bp_prev == NULL) {
            segList[idx] = NULL; 
        } else {
            SET_NEXT_PTR(bp_prev, NULL); 
        }
    }
    return; 

}


/*
 * coalesce takes a [pointer] to a block bp, and coalesces it with adjacent blocks, if they are free, and removes
 * the reference to all blocks other than the final block. 
 * 
 * 
 * 
 * 
 */ 

static void* coalesce(void *bp) {
                                                                                                                                                /*printf("///////////////////////////////////coalescing////////////////////////////\n\n"); */
    size_t self_alloc = GET_ALLOC(HDRP(bp));
    
                                                                                                                                                /*printf("line 172\n"); */

                                                                                                                                                            /*printf("line 177\n"); */

                                                                                                                                                /*printf("line 183\n"); */
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    void *prevBlock = PREV_BLKP(bp); 
    void *nextBlock = NEXT_BLKP(bp); 

    if(size < (size_t)24){
        return bp; 
    }
                                                                                                                                                                 /*printf("line 188\n"); */
    // if nothing next to it is free
    if (prev_alloc && next_alloc){
        PUT(HDRP(bp), PACK(size, 0)); 
        PUT(FTRP(bp), PACK(size, 0)); 
                                                    /*printf("line 219]n"); */
        return bp; // do nothing  
    } 
// if the thing after is free but not the block before  
    else if(prev_alloc && !next_alloc){
        removefreeblock(bp);          
                                                                                                                                             /*printf("line 194\n"); */
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));                                                  
                                                                                                                                                                /*printf("line 196\n"); */
        //Remove the next block. 
        removefreeblock(nextBlock); 
                                                                                                                                                    /*printf("line 199\n"); */
        PUT(HDRP(bp), PACK(size, 0));
                                                                                                                                                            /*printf("line 201\n"); */
        PUT(FTRP(bp), PACK(size, 0)); //don't remove block bp; 
                                                                                                                                                        /*printf("line 203\n"); */

    } 
    else if(!prev_alloc && next_alloc){
                                                                                                                                                              /*printf("line 207\n"); */
        removefreeblock(bp); 
        removefreeblock(PREV_BLKP(bp)); 
        size+= GET_SIZE(HDRP(prevBlock));
                                                                                                                                                        /*printf("line 209\n"); */
        PUT(FTRP(bp), PACK(size, 0)); 
                                                                                                                                /*printf("line 211\n"); */
        PUT(HDRP(prevBlock), PACK(size, 0));
                                                                                                                                                                /*printf("line 213\n"); */
                                                                                                                                                                /*printf("line 215\n"); */
        bp = prevBlock; 
                                                                                                                                                            /*printf("line 217\n"); */
    }
    else{
        
                                                                                                                                                                /*printf("line 220\n"); */
        removefreeblock(bp);

        removefreeblock(prevBlock);
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));

                                                                                                                                                                        /*printf("line 222\n"); */

        removefreeblock(NEXT_BLKP(bp)); 

                                                                                                                                                                         /*printf("line 224\n"); */

        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0)); 

                                                                                                                                                                                    /*printf("line 226\n"); */

        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));

                                                                                                                                                                                    /*printf("line 228\n"); */

        // remove the previous block from the free list 
        // if this is allocated, should we do this? 
        // maybe pass a pointer to removefreeblock to make sure it points to it
        bp = prevBlock; 
    }
    putInSegList(bp);
    return bp; 
}


/*
 * extendHeap extends the heap with a free block and returns its block pointer 
 * working with a min block size of 24 bytes. round up to 8 otherwise  
 * 
 */

static void *extend_heap(size_t words) {
    /*checkList(1); */

    char *bp;

    // allocate an even number to maintain alignment
    size_t size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE; 

    // error check sbrk 
    if ((long) (bp = mem_sbrk(size)) == -1) {
        return NULL; 
    }
                                                                                                                                                                                                               /*printf("sbreak\n");  */
    // initialize header and footer of freeblock
    PUT(HDRP(bp), PACK(size, 0)); 
    PUT(FTRP(bp), PACK(size, 0)); 

    // set the epilogue block
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); 

                                                                                                                                             /*printf("extending heap$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$\n\n");*/
    // coalesce if the prev block is free, return a pointer to the new memory
    // coalescing order??????
    putInSegList(bp);
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
   /* 
    if (bp == firstFreeBlockPointer) {
        firstFreeBlockPointer = NULL; 
    }*/ 
                                                                                                                                                                        /*printf("a\n");  */
    size_t blockSize = GET_SIZE(HDRP(bp)); 

                                                                                                                                                                                /*printf("b\n"); */
    // remove the block from the freelist 
    
                                                                                                /*printf("~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~`\n\n");  */
                                                                                    /*printf("d\n"); */
    int idx = getBucket((int) GET_SIZE(HDRP(bp))); 
                                                                                                                /*printf("this is in bucket %d: %p\n\n",  segList[idx], idx); */

    removefreeblock(bp); 
                                                                                            /*printf("%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%"); */
                                                                                                                /*printf("this is in bucket %d: %p\n\n",  segList[idx], idx); */

                                                                                            /*printf("~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~`\n\n");  */
    // if the next free block exists, remove this free block from its prev pointer 
 /*   if (nextFree != NULL && GET_PREV_FREE(nextFree) == bp) {
        printf("e\n"); 
        SET_PREV_PTR(nextFree, prevFree);  
    }

    printf("f\n"); 
    // if the previous free block exists, fremove this block from its next pointer
        printf("pointer of prevFree: %p\n", prevFree); 
    if (prevFree != NULL && GET_NEXT_FREE(prevFree) == bp) {
        SET_NEXT_PTR(prevFree, nextFree); 
    printf("g\n"); 
    }
*/
                                                                                                                                                    /*printf("h\n"); */

    if ((blockSize - size) >= MINSIZE) {
        
                                                                                                                                                                /*printf("i\n"); */

       // allocate this block 
        PUT(HDRP(bp), PACK(size, 1)); 
        PUT(FTRP(bp), PACK(size, 1)); 

       // go to the next block and split it off  
        bp = NEXT_BLKP(bp); 
        PUT(HDRP(bp), PACK(blockSize - size, 0)); 
        PUT(FTRP(bp), PACK(blockSize - size, 0)); 

        // place the split block into the free list 
        
        putInSegList(bp);
        // point the prev first to new block
    } else {
        PUT(HDRP(bp), PACK(blockSize, 1)); 
        PUT(FTRP(bp), PACK(blockSize, 1)); 
                                                                                                /*printf("j\n"); */
    }
}

static void *find_fit(size_t asize) {
    void *bp;
    int idx = getBucket((int) asize); // 

    idx = (idx > minFree) ? idx : minFree; // HERE KEEP THIS; 
    for (; idx < 13; idx++) { // still looking for love in all the wrong places. 

        if (asize <= sizeList[idx]) {                                                                                                                                                                        /*printf("q\n"); */
            for (bp = segList[idx]; bp != NULL ; bp = GET_NEXT_FREE(bp)) {
                                                                                                                                                                /*printf("r\n"); */
                    if ((asize <= GET_SIZE(HDRP(bp)))) {
                                                                                                                                                                                            /*printf("s\n"); */
                        return bp; 
                    }
            }
    }
    }
    return NULL; 
}


/* 
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
                                                                                /*printf("\n\n\n ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^6 INITIALIZING ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^\n\n"); */
    // make enough room for our seglist and the initial blocks
    if((firstBlock = mem_sbrk(4 * WSIZE + 26 * DSIZE) ) == (void *) -1) {
        return -1; 
    }

    // set a pointer to the seglist
    segList = (int **) firstBlock; 
    int i = 0;
    for (i = 0; i < 13; i++) {
        segList[i] = NULL;
    }

    sizeList = (char*)( (long) segList + 13 * DSIZE);

    for (i = 0; i < 13; i++) {
        sizeList[i] = (long) 0; // size is currently 0. max size at each i is currently zero. 
    } 

                                                                                                                                                /*printf("this is the location of the seglist: %p\n", segList); */



    // increment firstBlock to point to the first free blocks 
    firstBlock += 26 * DSIZE; 

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


    void *newBlock = extend_heap(CHUNKSIZE/WSIZE); 
    if (newBlock == NULL) {
        return -1; 
    }
    
    putInSegList(newBlock); 
    minFree = getBucket(GET_SIZE(newBlock)); 
    SET_NEXT_PTR(newBlock, NULL); 
    SET_PREV_PTR(newBlock, NULL); 
    return 0;
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    /*checkheap(1); */
    /*printf("################################# malloc %d ###############################\n", size); */
    /*checkList(1); */
    
    
    
   // ignore 0  
    if (size == 0) {
        return NULL; 
    }
    

    if (firstBlock == 0) {
        mm_init();
    }
        
    size = normalize(size); 

///////////////////////////////////////////////////////////////////////////////////
                                                                                                                                                /*printf("part 3\n");*/
    void *fitBlock;
                                                                                                                                                /*printf("part 3.5\n"); */
    fitBlock = find_fit(size);  
                                                                                                                                                    /*printf("part 4\n"); */
/////////////////////////////////////////////////////////////////////////////
//
//

                                                                                                                                                    /*printf("part 12\n"); */
    // if fit found 
    if ((fitBlock != NULL)) {

                                                                                                                                /*printf("part 13\n"); */

        place(fitBlock, size);  

                                                                                                                                                    /*printf("part 14\n"); */
       
        return fitBlock;
    }

                                                                                                                                                                /*printf("part 5\n"); */

    // if no fit found 
    size_t extendSize = MAX(size, CHUNKSIZE); 


                                                                                                                                                            /*printf("part 6\n"); */
    void *bp = extend_heap(extendSize/WSIZE); 
/*checkList(1); */
/*checkheap(1); */

                                                                                                                                                            /*printf("part 8\n"); */
    if (bp == NULL) {
        return NULL; 
    }
    
                                                                                                                                                        /*printf("part 9\n"); */
  

    place (bp, size); 
    return bp; 
}

/*
 * * add checks o make sure the thing was previously allocated 
 */
void mm_free(void *ptr)
{
    /*checkList(1); */
    /*checkheap(1); */
                                                                                                                        /*printf("///////////////////////////////// free ///////////////////////////////////////////\n\n"); */


                                                                                                            /*printf("################################# %p ###############################\n", ptr); */
    /*if (ptr == 0) {*/
        /*return;*/
    /*} //Make sure we're actually freeing valid memory!  */

    /*if (firstBlock == 0) {*/
        /*mm_init(); */
    /*}*/
   

    // make sure that it's aligned, if it's not, return
    /*if ((unsigned long)ptr % 8){*/
        /*return; */
    /*}*/
    
    /*if (!(((unsigned long)mem_heap_lo() <= (unsigned long)ptr) && ((unsigned long)ptr <= (unsigned long)mem_heap_hi()))){*/
        /*return; //check whether the pointeir is actually inside the block! */
    /*}*/

    //Once we have verified that we MIGHT have a valid pointer, we need to check its information. 
    size_t self_alloc = GET_ALLOC(HDRP(ptr)); 
    size_t self_size = GET_SIZE(FTRP(ptr));
    if (!(self_alloc)){
        return; 
    }
    
    if ((unsigned int)self_size < MINSIZE){
        return; 
    }

    /*void * bp_next =  (void*)GET_NEXT_FREE(ptr); */
    /*void * bp_prev =  (void*)GET_PREV_FREE(ptr);*/

    PUT(HDRP(ptr), PACK(self_size, 0)); 
    PUT(FTRP(ptr), PACK(self_size, 0)); 
    

    putInSegList(ptr);
    coalesce(ptr); 
    /*if (firstFreeBlock != NULL) {*/
        /*SET_PREV_PTR(firstFreeBlock, bp); */
    /*}*/
    
/*// update the pointers */
    /*SET_PREV_PTR(bp, NULL); */
    /*SET_NEXT_PTR(bp, firstFreeBlock);*/
    /*firstFreeBlock = (char *) bp; */
    
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
/*void *mm_realloc(void *ptr, size_t size)*/
/*{*/
    /*size_t oldsize;*/
    /*void *newptr;*/

    /*[> If size == 0 then this is just free, and we return NULL. <]*/
    /*if(size == 0) {*/
        /*mm_free(ptr);*/
        /*return 0;*/
    /*}*/

    /*[> If oldptr is NULL, then this is just malloc. <]*/
    /*if(ptr == NULL) {*/
        /*return mm_malloc(size);*/
    /*}*/

    /*newptr = mm_malloc(size);*/
    
    /*[> If realloc() fails the original block is left untouched  <]*/
    /*if(!newptr) {*/
        /*return 0;*/
    /*}*/

    /*[> Copy the old data. <]*/
    /*oldsize = GET_SIZE(HDRP(ptr));*/
    /*if(size < oldsize) oldsize = size;*/
    /*memcpy(newptr, ptr, oldsize);*/

    /*[> Free the old block. <]*/
    /*mm_free(ptr);*/

    /*return newptr;*/
/*}*/
/*
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

/* 
 * checkList - Minimal check of the heap for consistency 
 */
static void checkList (int verbose) 
{
                                                                                                            printf("@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@ LIST @@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@\n"); 
    char *bp = firstBlock;


    if (verbose)
                                                                                                                                printf("Heap (%p):\n", firstBlock);

    if ((GET_SIZE(HDRP(firstBlock)) != DSIZE) || !GET_ALLOC(HDRP(firstBlock))) {

                                                                                                                                                printf("Bad prologue header\n");
    }

    int i; 
    for (i = 0; i < 13; i++) {
        int idx = i;

    
                                                                                                                                    printf("\n\n&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&& index %i &&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&\n\n", idx); 
        for (bp = segList[idx]; bp != NULL; bp = GET_NEXT_FREE(bp)) {
            if (verbose) 
                printblock(bp);
            checkblock(bp);
        }
                                                                                                                    printf("\n\n&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&& index %i &&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&&\n\n", idx); 
    
    }
    if (bp == NULL) {
        return;
    }
    if (verbose)
        printblock(bp);

} 

/*
 * checkHeap goes through heap
 *
 */


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


/*
 * return what bucket of the seg list a size block can be found in
 */
static int getBucket (int size) {
    if (size < 2 + 24) {
        return 0; 
    } else if (size < 4 + 24) {
        return 1; 
    } else if (size < 8 + 24) {
        return 2; 
    } else if (size < 16 + 24) {
        return 3; 
    } else if (size < 32 + 24) {
        return 4; 
    } else if (size < 64  + 24) {
        return 5; 
    } else if (size < 128 + 24) {
        return 6; 
    } else if (size < 256 + 24) {
        return 7; 
    } else if (size < 512 + 24) {
        return 8;
    } else if (size < 1024 + 24) {
        return 9; 
    } else if (size < 2048 + 24) {
        return 10;
    } else if (size < 4096 + 24) {
        return 11; 
    } else {
        return 12; 
    }
}

static void putInList(void *bp, int seglist_num) {
    void * head = segList[seglist_num]; 
    size_t bp_size = GET_SIZE(HDRP(bp)); 

    if (bp_size > sizeList[seglist_num]){
        sizeList[seglist_num] = (long) bp_size; //apparently here is where everything goes wrong... what is sizeList[seglist_num] 
    }

    // case 1: list is NULL; 
    if(head == NULL){
        segList[seglist_num] = bp;
        SET_NEXT_PTR(bp, NULL);
        
    }
    else {
        void* next = GET_NEXT_FREE(head); 

        while(next != NULL){
            if (GET_SIZE(HDRP(next)) >= bp_size ){
                //the case where we can insert.
                SET_NEXT_PTR(head, bp); 
                SET_PREV_PTR(next, bp); 

                SET_PREV_PTR(bp, head); 
                SET_NEXT_PTR(bp, next); 
                return;         
            } else {
                head = next; 
                next = GET_NEXT_FREE(head); 
            }
            
        }

        SET_NEXT_PTR(head, bp); //head is at the end of the list. after head, we have bp; which SHOULD make sense? 

        SET_PREV_PTR(bp, head); 
        SET_NEXT_PTR(bp, NULL); 
        
    }
}

static void putInSegList(void *bp) {
                                                                                                                /*printf("!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!111 putInSegList() !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!11\n\n"); */
    int idx = getBucket(GET_SIZE(HDRP(bp)));
                                                                                                                                                /*printf("%d\n", idx); */
    SET_PREV_PTR(bp, NULL); 

    /*if (segList[idx] == NULL) {
        segList[idx] = bp; 
        SET_NEXT_PTR(bp, NULL); 
        
        if (minFree > idx) {
            minFree = idx; 
        }
    } else {
        SET_NEXT_PTR(bp, segList[idx]);
        SET_PREV_PTR(segList[idx], bp); 
        ssegList[idx] = bp; 
    } 
    */
    putInList(bp, idx); 
}

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


    if(prevalloc) { // previous block is allocated; cannot 
        //check size; 
        size_t combinedsize = oldsize;

        if(!nextalloc) { // the block after this is FREE! 
            combinedsize = oldsize + nextptr_size; // then we can use the next memory block (if it is free). 
            removefreeblock(nextptr); 
        }
        

        if (combinedsize >= asize){
        
            if((combinedsize - asize) < MINSIZE){
                // I think this part might be causing some problems? 
                PUT(HDRP(ptr), PACK(combinedsize, 1)); //unchanged 
                PUT(FTRP(ptr), PACK(combinedsize, 1));          
            } else {
                PUT(HDRP(ptr), PACK(asize, 1)); // also should be unchanged. 
                PUT(FTRP(ptr), PACK(asize, 1)); // 
                void * splitptr = NEXT_BLKP(ptr); //

    
                PUT(HDRP(splitptr), PACK(combinedsize - asize, 0)); //Only  
                PUT(FTRP(splitptr), PACK(combinedsize - asize, 0)); // still the remaining blocks.

                putInSegList(splitptr);
        
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

                PUT(HDRP(splitptr), PACK(combinedsize - asize, 0)); //Only  
                PUT(FTRP(splitptr), PACK(combinedsize - asize, 0)); // still the remaining blocks.

                putInSegList(splitptr);
        
            }
            return prevptr;
        }
    }

    newptr = mm_malloc(size);
    memcpy(newptr, ptr, oldsize);
    mm_free(ptr); 
        return newptr;

}
