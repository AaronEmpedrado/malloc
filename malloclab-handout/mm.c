/*
 * mm.c - Jon and Joe's version
 * 
 * Implementation: Explicit free list 
 * (doubly linked list of free blocks)
 * 
 * Blocks organization
 * Free block:      HEADER | PRED FREE | SUCC FREE | PAYLOAD | FOOTER
 * Allocated block: HEADER | PAYLOAD| FOOTER
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
    /* Team Jon and Joe */
    "Team Jon and Joe",
    /* Jonathan Huang */
    "Jonathan Huang",
    /* jonhuang@u.northwestern.edu */
    "jonhuang@u.northwestern.edu",
    /* Joe Chookaszian */
    "Joe Chookaszian",
    /* josephchookaszian@u.northwestern.edu */
    "josephchookaszian@u.northwestern.edu"
};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

/*
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))
*/

// macros and constants 

#define WSIZE 4
#define DSIZE 8
#define CHUNKSIZE 8192 // (1<<13) = 8192, (1<<12) = 4096
#define OVERHEAD 24 // header + pred + succ + footer = 16

#define MAX(x, y) ((x) > (y) ? (x) : (y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc) ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p)      (*(size_t *)(p)) //read
#define PUT(p, val) (*(size_t *)(p) = (val)) //write

/* Read the size and allocated fields from address p */
#define GET_SIZE(p)   (GET(p) & ~0x7)
#define GET_ALLOC(p)  (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HEADER_PTR(bp) ((void *)(bp) - WSIZE)
#define FOOTER_PTR(bp) ((void *)(bp) + GET_SIZE(HEADER_PTR(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLOCK_PTR(bp) ((void *)(bp) + GET_SIZE(HEADER_PTR(bp)))
#define PREV_BLOCK_PTR(bp) ((void *)(bp) - GET_SIZE(HEADER_PTR(bp) -WSIZE)) 

/* Given block ptr bp, compute address of predecessor and successor free blocks in linked list */
#define SUCC(bp)(*(void **)(bp + WSIZE))
#define PRED(bp)(*(void **)(bp))

#define SET_NEXT(bp, lp) (SUCC(bp) = lp)
#define SET_PREV(bp, lp) (PRED(bp) = lp)

/* global decs */
static void *heap_listp=0;
static void *list_head =0;

/* helper functions in order they appear */
static void *coalesce(void *bp);
static void *extend_heap(size_t words);
static void insertAtHead(void *bp);
static void *findFit(size_t asize);
static void removeBlock(void *bp);
static void place(void *bp, size_t asize);
static void printBlock(void *bp);
static void checkBlock(void *bp);

// helper functions below // 

// Coalesce combines the new blocc with the adjacent free bloccs 
static void *coalesce(void *bp)
{
 //  printf("IN COAL \n");
    /* if the prev blocc is allocated or its size is =0 then previous allc will be set */
    size_t prev_alloc = GET_ALLOC(FOOTER_PTR(PREV_BLOCK_PTR(bp))) || PREV_BLOCK_PTR(bp) == bp;
    size_t next_alloc = GET_ALLOC(HEADER_PTR(NEXT_BLOCK_PTR(bp)));
    size_t size = GET_SIZE(HEADER_PTR(bp));
   
//CASE 1: NO BLOCC
    if(prev_alloc && next_alloc){
        insertAtHead(bp);
        return bp;
    }
//CASE 2: if the next blocc is free 
     else if (prev_alloc && !next_alloc) {
        size += GET_SIZE(HEADER_PTR(NEXT_BLOCK_PTR(bp)));
        removeBlock(NEXT_BLOCK_PTR(bp));
        PUT(HEADER_PTR(bp), PACK(size, 0));
        PUT(FOOTER_PTR(bp), PACK(size, 0));
    }
//CASE 3:  if the prev blocc is free 
    else if (!prev_alloc && next_alloc) {
        size += GET_SIZE(HEADER_PTR(PREV_BLOCK_PTR(bp)));
    removeBlock(PREV_BLOCK_PTR(bp));
        PUT(HEADER_PTR(PREV_BLOCK_PTR(bp)), PACK(size, 0));
        PUT(FOOTER_PTR(PREV_BLOCK_PTR(bp)), PACK(size, 0));
        bp = PREV_BLOCK_PTR(bp);
    }
//CASE 4: if both bloccs are free 
    else if (!prev_alloc && !next_alloc) {
        size += GET_SIZE(HEADER_PTR(PREV_BLOCK_PTR(bp))) 
        + GET_SIZE(HEADER_PTR(NEXT_BLOCK_PTR(bp)));
    removeBlock(PREV_BLOCK_PTR(bp));
        removeBlock(NEXT_BLOCK_PTR(bp));
        PUT(HEADER_PTR(PREV_BLOCK_PTR(bp)), PACK(size, 0));
        PUT(FOOTER_PTR(NEXT_BLOCK_PTR(bp)), PACK(size, 0));
    bp = PREV_BLOCK_PTR(bp);
    }
// now insert bp into free list and return bp 
    insertAtHead(bp);
    return bp;
}

// extend_heap expands the heap for the free blocc
static void *extend_heap(size_t words)
{
    void *bp;
    size_t size;
    
    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
    
    if (size < OVERHEAD) {
    size = OVERHEAD;
    }
    if ((bp = mem_sbrk(size)) == -1)
    {
    return NULL;
    }
    /* Initialize free block header/footer and the epilogue header */
    PUT(HEADER_PTR(bp), PACK(size, 0));         /* Free block header */
    PUT(FOOTER_PTR(bp), PACK(size, 0));         /* Free block footer */
    PUT(HEADER_PTR(NEXT_BLOCK_PTR(bp)), PACK(0, 1)); /* New epilogue header */
    
    /* Coalesce if the previous block was free */
    return coalesce(bp);
}

//insertAtHead inserts the block at the front of the list
static void insertAtHead(void *bp)
{
    SET_PREV(bp,NULL); // Sets PRED pointer to NULL
    if ((SUCC(bp) = list_head) == NULL) 
    SET_NEXT(bp,list_head); //Sets SUCC ptr to start of free list
    SET_PREV(list_head,bp); //Sets current's PRED to new block
    list_head = bp; // Sets head of free list as new block

}

//findFit finds a fit for the block with the designated size
static void *findFit(size_t asize)//implementing the first find
{
    void *bp;
    for (bp = list_head; GET_ALLOC(HEADER_PTR(bp)) ==  0; bp = SUCC(bp)) {
        if (!GET_ALLOC(HEADER_PTR(bp)) && (asize <= GET_SIZE(HEADER_PTR(bp)))) { 
            return bp;            
        }
    }
    return NULL; //no fit found
}

//removeBlock is opposite of insertAtHead, removes the block
static void removeBlock(void *bp) 
{
    if (PRED(bp))
    {
    SET_NEXT(PRED(bp), SUCC(bp));
    }
    else
    {
        list_head = SUCC(bp);
    }
        SET_PREV(SUCC(bp), PRED(bp));
}

//place places the block of designated size at the start of the block
static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HEADER_PTR(bp));
    if ((csize - asize) >= (2*DSIZE)) {
    PUT(HEADER_PTR(bp), PACK(asize, 1));
        PUT(FOOTER_PTR(bp), PACK(asize, 1));
        removeBlock(bp);
        bp = NEXT_BLOCK_PTR(bp);
        PUT(HEADER_PTR(bp), PACK(csize-asize, 0));
        PUT(FOOTER_PTR(bp), PACK(csize-asize, 0));
    insertAtHead(bp);
    }
    else {
        PUT(HEADER_PTR(bp), PACK(csize, 1));
        PUT(FOOTER_PTR(bp), PACK(csize, 1));
        removeBlock(bp);
    }
}

//printBlock prints the contents of the block
static void printBlock(void *bp)
{
    int headSize, headAlloc, footSize, footAlloc;
    
    
    headSize = GET_SIZE(HEADER_PTR(bp));
    headAlloc = GET_ALLOC(HEADER_PTR(bp));
    footSize = GET_SIZE(FOOTER_PTR(bp));
    footAlloc = GET_ALLOC(FOOTER_PTR(bp));
    
    if (headSize == 0)
    {
        printf("%p: EOL\n", bp);
        return;
    }
    
    if (headAlloc)
        printf("%p: header:[%d:%c] footer:[%d:%c]\n", bp,
               headSize, (headAlloc ? 'a' : 'f'),
               footSize, (footAlloc ? 'a' : 'f'));
    else
        printf("%p:header:[%d:%c] prev:%p next:%p footer:[%d:%c]\n",
               bp, headSize, (headAlloc ? 'a' : 'f'), PRED(bp),
               SUCC(bp), footSize, (footAlloc ? 'a' : 'f'));
}

// //checks block for consistency
// static void checkBlock(void *bp)
// {
    
//     if (SUCC(bp)< mem_heap_lo() || SUCC(bp) > mem_heap_hi())
//         printf("Error: SUCC pointer %p is not within heap bounds \n"
//                , SUCC(bp));
//     if (PRED(bp)< mem_heap_lo() || PRED(bp) > mem_heap_hi())
//         printf("Error: PRED pointer %p is not within heap bounds \n"
//                , PRED(bp));
    

//     if ((size_t)bp % 8)
//         printf("Error: %p is not aligned\n", bp);
    

//     if (GET(HEADER_PTR(bp)) != GET(FOOTER_PTR(bp)))
//         printf("Error: header does not match footer\n");
// }

// //checks heap for consistency
// int mm_checkheap(int x)
// {
//     char *temp_ptr=0;

//     void *bp = list_head;
//     if (x)
//         printf("Heap (%p):\n", list_head);
    
//     if ((GET_SIZE(HEADER_PTR(heap_listp)) != OVERHEAD) ||
//         !GET_ALLOC(HEADER_PTR(heap_listp)))
//         printf("Corrupt prologue header\n");
//     checkBlock(heap_listp); //
    
//     for (bp = list_head; GET_ALLOC(HEADER_PTR(bp))==0; bp = SUCC(bp))
//     {
//         if (x)
//             printBlock(bp);
//         checkBlock(bp);
//     }
    
//     if (x)
//         printBlock(bp);
    
//     if ((GET_SIZE(HEADER_PTR(bp)) != 0) || !(GET_ALLOC(HEADER_PTR(bp))))
//         printf("Corrupt epilogue header\n");

        
//     temp_ptr = list_head;
//     while((*temp_ptr) != NULL) {
//         if(FOOTER_PTR(temp_ptr) >= HEADER_PTR(NEXT_BLOCK_PTR(temp_ptr))) {
//             printf("block at %p overlaps with block at %p", 
//                 temp_ptr, NEXT_BLOCK_PTR(temp_ptr));
//             return 0;
//         }
//         temp_ptr = NEXT_BLOCK_PTR(temp_ptr);
//     }
//     return 1;
// }

/* mm_init - initialize the malloc package.
 * 
 * the application program will call mm_init to perform any necessary initializations, such as
 * Allocating the initial heap area,
 * The return value should be -1 if there are issues in performing initialization
 * The return value should be 0 if there are no issues
*/
int mm_init(void)
{
    /* Create the initial empty heap */ 
    if ((heap_listp = mem_sbrk(2*OVERHEAD)) == (void *) -1) 
    return -1;

PUT(heap_listp, 0);
PUT(heap_listp + WSIZE, PACK(DSIZE,1));
PUT(heap_listp + DSIZE, 0);
PUT(heap_listp + DSIZE + WSIZE, 0);
list_head = heap_listp + DSIZE;
    
    
    /*return -1 if unable to get heap space*/
    if (extend_heap(WSIZE) == NULL)
        return -1;
    return 0;
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 * and should not overlap with any other allocated chunk. 
 */
void *mm_malloc(size_t size)
{
    size_t asize;       /* Adjusted block size */
    size_t extend;  /* Amount to extend heap if no fit */
    void *bp; 
    
    /* Ignore spurious requests */
    if (size == 0)
        return NULL;
    asize = MAX(ALIGN(size) + DSIZE, OVERHEAD);
    /* adjust blocc size to include overhead and alignment reqs*/
    /* Search the free list for a fit */
    if ((bp = findFit(asize)) != NULL) {
        place(bp, asize);
    //printf("searching free list for a fit in malloc \n");
        return bp;
    }
    /* No fit found. Get more memory and place the block */
    extend = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extend/WSIZE)) == NULL)
    return NULL;

    place(bp, asize);
    return bp;
}



/*
 * mm_free - Freeing a block does nothing.
 * The mm_free routine frees the block pointed to by ptr. 
 * It returns nothing.
 * This routine is only guaranteed to work when 
 * the passed pointer (ptr) was returned by an earlier call to 
 * mm_malloc or mm_realloc and has not yet been freed.
 */
void mm_free(void *ptr)
{
    size_t size = GET_SIZE(HEADER_PTR(ptr));    
    PUT(HEADER_PTR(ptr), PACK(size, 0));
    PUT(FOOTER_PTR(ptr), PACK(size, 0));
    
    coalesce(ptr);
}



/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 * 
 * The mm_realloc routine returns a pointer to an allocated region
 * of at least 'size' bytes with the following constraints
 * 
 * - if the ptr is NULL, the call is equivalent to mm_malloc(size);
 * - if the size is equal to zero, the call is equivalent to mm_free(ptr);
 * - if the ptr is NOT NULL, it must have been returned by an earlier call to malloc or realloc
 *   The call to realloc changes the size of the memory block pointed to by ptr 
 *   (the old block) to 'size' bytes and returns the address of the new block. 
 *   Notice that the address of the new block might be the same as the old block,
 *   but it might be different, depending on 
 *   - your implementation
 *   - the amount of internal fragmentation in the old block
 *   - and the size of the realloc request
 *
 * - The contents of the new block are the same as those of the old ptr block,
 *   up to the minimum of the old and new sizes. 
 *   Everything else is unititiated.
 *
 *   i.e., if the old block is 8 bytes and the new block is 12 bytes,
 *   then the first first 8 bytes of the new bock are identical that of the old block
 *   and the last 4 bytes are unititialized. 
 *   
 *   i.e. if the old block is 8 bytes and the new block is 4 bytes
 *   then the contents of the new block are identical to the first 4 bytes of the old. 
 */

void *mm_realloc(void *ptr, size_t size)
{

size_t oSize = GET_SIZE(HEADER_PTR(ptr));
size_t nSize = MAX(ALIGN(size) + DSIZE, 2*DSIZE);

if(!ptr)
{   
    return mm_malloc(size);
} 

 
if(size == 0) 
{
    mm_free(ptr);
    return NULL;
}

if(nSize <= oSize)
{
    return ptr;
}
else
{
    size_t next = GET_ALLOC(HEADER_PTR(NEXT_BLOCK_PTR(ptr)));
    size_t total_size = oSize + GET_SIZE(HEADER_PTR(NEXT_BLOCK_PTR(ptr)));
    
    if(!next && (total_size >= nSize))
    {   
        removeBlock(NEXT_BLOCK_PTR(ptr));
        PUT(HEADER_PTR(ptr), PACK(total_size,1));
        PUT(FOOTER_PTR(ptr), PACK(total_size, 1));
        return ptr;
    }
    else 
    {
        void *newptr = mm_malloc(nSize);
        place(newptr, nSize);
        memcpy(newptr, ptr, nSize);
        mm_free(ptr);
        return newptr;
    }
}
}

