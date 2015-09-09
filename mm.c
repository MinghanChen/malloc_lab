/*
Andrew ID : minghan2
Name : Minghan Chen
Email : minghan2@andrew.cmu.edu
    
*/
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "mm.h"
#include "memlib.h"



#ifdef DRIVER

#define malloc mm_malloc
#define free mm_free
#define realloc mm_realloc
#define calloc mm_calloc
#endif 
/* def DRIVER */


//Word, 4 bytes
#define WSIZE 4
//Double words, 8 bytes
#define DSIZE 8
//HDRPer and FTRPer sign, 8 bytes
#define ALIGN_REQ 8
//Alignment request, 8 bytes
#define ALIGNMENT 8
//size of 16-byte block
#define BLOCK_16 16
//size of 8-byte block
#define BLOCK_8 8
//Minimum block size
#define MIN_SIZE_IN_TREE 24
//Extend heap by this amount(bytes)
#define CHUNKSIZE (1<<8)

/*Macros*/
#define MAX(x, y) ( (x)>(y)? (x): (y) )
#define MIN(x, y) ( (x)<(y)? (x): (y) )

/*Make the block to meet with the standard alignment requirements*/
#define ALIGN_SIZE(size) (((size) + (ALIGNMENT-1)) & ~0x7)

/*Pack a size and allocated bit into a word*/
#define PACK(size, alloc) ((size)|(alloc))

/*Read and write a word at address p*/
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p)=(val))

/*Read the size and allocated fields from address p*/
#define SIZE(p) (GET(p) & (~0x7))
#define ALLOC(p) (GET(p) & (0x1))
#define PRE_ALLOC_INFO(p) (GET(p) & (0x2))
#define PRE_8_INFO(p) (GET(p) & (0x4))

/*Given block pointer bp, read the size and allocated fields*/
#define GET_SIZE(bp) ((GET(HDRP(bp)))&~0x7)
#define GET_ALLOC(bp) ((GET(HDRP(bp)))&0x1)
#define GET_PRE_ALLOC_INFO(bp) ((GET(HDRP(bp)))&0x2)
#define GET_PRE_8_INFO(bp) ((GET(HDRP(bp)))&0x4)

#define SET_PREALLOC_INFO(bp) (GET(HDRP(bp)) |= 0x2)
#define RESET_PREALLOC_INFO(bp) (GET(HDRP(bp)) &= ~0x2)
#define SET_PRE_8_INFO(bp) (GET(HDRP(bp)) |= 0x4)
#define RESET_PRE_8_INFO(bp) (GET(HDRP(bp)) &= ~0x4)
/*Given pointer p at the second word of the data structure, compute addresses
of its HDRP,LEFT,RIGHT,PARENT,BROTHER and FTRP pointer*/
#define HDRP(p) ((void *)(p) - WSIZE)
#define LEFT(p) ((void *)(p))
#define RIGHT(p) ((void *)(p) + WSIZE)
#define PARENT(p) ((void *)(p) + 2 * WSIZE)
#define BROTHER(p) ((void *)(p) + 3 * WSIZE)
#define FTRP(p) ((void *)(p) + SIZE(HDRP(p)) - DSIZE)

/*Given block pointer bp, get the POINTER of its directions*/
#define GET_PREV(bp) ( GET_PRE_8_INFO(bp) ? ((void *)bp - BLOCK_8 ): ((void *)(bp) - SIZE((void *)(bp) - DSIZE)) )
#define GET_NEXT(bp) ((void *)(bp) + SIZE(((void *)(bp) - WSIZE)))

/*Get the LEFT,RIGHT,PARENT,BROTHER and FTRP pointer of the block to which bp points*/
#define GET_LEFT(bp) ((long)GET(LEFT(bp))|(0x800000000))
#define GET_RIGHT(bp) ((long)GET(RIGHT(bp))|(0x800000000))
#define GET_PARENT(bp) ((long)GET(PARENT(bp))|(0x800000000))
#define GET_BROTHER(bp) ((long)GET(BROTHER(bp))|(0x800000000))

/*Define value to each character in the block bp points to.*/
#define PUT_HDRP(bp, val) (PUT(HDRP(bp), val))
#define PUT_FTRP(bp, val) (PUT(FTRP(bp), val))
#define PUT_LEFT(bp, val) (PUT(LEFT(bp), ((unsigned int)(long)val)))
#define PUT_RIGHT(bp, val) (PUT(RIGHT(bp), ((unsigned int)(long)val)))
#define PUT_PARENT(bp, val) (PUT(PARENT(bp), ((unsigned int)(long)val)))
#define PUT_BROTHER(bp, val) (PUT(BROTHER(bp), ((unsigned int)(long)val)))

//All functions and global variables used in the program:

/* static functions */
static void *coalesce ( void *bp );
static void *extend_heap ( size_t size );
static void place ( void *ptr, size_t asize );
static void insert_node ( void *bp );
static int get_direction(void * bp);
static void delete(void *bp);
static void delete_node ( void *bp );
static void delete_first_node(void * bp, int direction);
static void *match ( size_t asize );
static void printBlock(void *bp);
//static void block_checker(void *bp);
//static void heap_checker(void * temp);
static void list_for_8_checker(); 
static void list_for_16_checker();
static void BST_checker(void * bp);
void mm_checkheap(int verbose);
/* Global variables */
static void *heap_list_ptr;//HDRP block node of all heap blocks
static void *root;//root of the BST
static void *list_for_16;//HDRP of the 16-bit list
static void *list_for_8;//HDRP of the 8-byte list
static void *NULL_POINTER;//virtual NULL pointer (0x800000000)

/*
mm_init add two more words. The first word, which address is 0x800000000, is pointed by the 
root pointer of BST, the begin pointer of list_for_8 and list_for_16 
*/

int mm_init(void)
{
    /* create the initial empty heap */
    if( (heap_list_ptr = mem_sbrk(6 * WSIZE)) == (void *)-1 )
        return -1;
    PUT( heap_list_ptr + (2 * WSIZE), 0 ); // alignment padding
    PUT( heap_list_ptr + (3 * WSIZE), PACK(DSIZE, 1) ); // prologue HDRPer
    PUT( heap_list_ptr + (4 * WSIZE), PACK(DSIZE, 1) ); // prologue FTRPer
    PUT( heap_list_ptr + (5 * WSIZE), PACK(0, 3) ); // epilogue HDRPer
    heap_list_ptr += (4 * WSIZE);
    /*init the global variables*/
    NULL_POINTER = (void *)0x800000000; 
    root = NULL_POINTER;
    list_for_16 = NULL_POINTER;
    list_for_8 = NULL_POINTER;
    /* Extend the empty heap with a free block of CHUNKSIZE bytes */
    if( extend_heap(MIN_SIZE_IN_TREE)==NULL )
        return -1;
    return 0;
}

/*extend_heap function is used when the heap is firstly initialized, or there isn't enough
space when invoking the malloc or realloc. The extend_heap when judge whether there is space
left in the tail of the former block, it is a method to enhance the space utility.*/
void *extend_heap(size_t size_)
{
    void *bp;
    void *end = mem_heap_hi() - 3;

    int size = size_;
    if( !PRE_ALLOC_INFO(end) ){
        if(PRE_8_INFO(end)) size -= BLOCK_8;
        else size -= SIZE(end - 4);
    }
    if(size <= 0) return NULL;
    
    size = MAX(CHUNKSIZE, size);

    if((long)(bp = mem_sbrk(size)) == -1)
        return NULL;
    /* Initialize free block HDRPer/FTRPer and the epilogue HDRPer */
    size_t sign = 0 | GET_PRE_ALLOC_INFO(bp) | GET_PRE_8_INFO(bp);
    PUT_HDRP(bp, PACK(size,sign) ); /* free block HDRPer */
    PUT_FTRP(bp, PACK(size,sign) ); /* free block FTRPer */

    PUT_HDRP(GET_NEXT(bp), PACK(0,1) ); /* new epilogue HDRPer */
    
    insert_node(coalesce(bp));
    return (void *)bp;
}

/*The malloc function firstly judge whether the input argument is a legitimate value. If not,
It just return null. Then it will make the size to the multiple of the data alignment size.
If there are available space , it will simply get the space from the existing block. Else, it
will extend the heap.*/

void *malloc(size_t size)
{
    size_t asize; /* adjusted block size */
    void *bp;
    /* Ignore spurious requests */
    if( size <= 0 )
        return NULL;
    /* tune the size due to the data alignment*/
    asize = ALIGN_SIZE( size + WSIZE );
    /* Search the free list for a fit */
    if( (bp = match(asize)) == NULL_POINTER ){
        extend_heap( asize );
        /*This is used when there isn't enough space for us even if we have extend the heap.*/
        if( (bp = match(asize)) == NULL_POINTER )
            return NULL;
    }
    place(bp, asize);
    return bp;
}

/*When a malloc block is freed, it will check if the former or successive block is also free.
If is, it will coalesce them and insert the total block into the BST or list. If not, it
just simply insert itself.*/

void free(void *bp)
{
    if(bp == NULL) return;
    size_t size = GET_SIZE(bp);
    size_t checkalloc = GET_ALLOC(bp);
    if(checkalloc == 0) return;
    size_t sign = 0 | GET_PRE_ALLOC_INFO(bp) | GET_PRE_8_INFO(bp);
    PUT_HDRP(bp, PACK(size, sign) );
    PUT_FTRP(bp, PACK(size, sign) );

    insert_node(coalesce(bp));
}

/*Firstly, the realloc judge the pointer. if the pointer points to nothing, it just simply
malloc. If the size is zero, it return null. If the size greater than 0, it judge whether the old
size is greater than the newsize. If is, the realloc would use the previous address. If not,
the realloc function would malloc a new block.*/
void *realloc(void *ptr, size_t size) {
    if( ptr==NULL ) {
    	return malloc(size);
    }
    if( size == 0 ){
        free(ptr);
        return NULL;
    }
    if( size > 0 ){
        size_t oldsize = GET_SIZE( ptr );
        size_t newsize = ALIGN_SIZE( size + WSIZE );
        if( oldsize >= newsize ){ /* newsize is less than oldsize */
            
            /* the next block is allocated */
                if( (oldsize-newsize) >= ALIGNMENT ){
                /* used to miss GET_PRE_ALLOC_INFO with PRE_ALLOC_INFO*/
                    size_t head = 1 | GET_PRE_ALLOC_INFO(ptr) | GET_PRE_8_INFO(ptr);
                    PUT_HDRP(ptr, PACK(newsize, head) );
                    size_t leftsize = oldsize - newsize;
		    void *next = GET_NEXT(ptr);
                    PUT_HDRP( next, PACK(leftsize, 0x2) );
                    PUT_FTRP( next, PACK(leftsize, 0x2) );
                   
                    insert_node( coalesce(next) );
                }
                return ptr;
        } else { /* newsize is greater than oldsize */
            void * newptr = malloc(size);
            memcpy(newptr, ptr, GET_SIZE(ptr));
            free(ptr);
            return newptr;
         }
    }
    return NULL; 
}

/*the coalesce function is used to coalesce the block the pointer points to with the
previous and successive free block.It is divided into four circumstances, which is the
same as the previous code.*/

static void *coalesce(void *bp)
{	
	size_t size = GET_SIZE(bp);

	size_t prev_alloc = GET_PRE_ALLOC_INFO(bp);
	
	size_t next_alloc = GET_ALLOC( GET_NEXT(bp) );
	
	if ( prev_alloc && next_alloc ){ /* Case 0 */
        return bp;
	} else if ( !prev_alloc && next_alloc ) { /* Case 1*/
	    void * prev = (void *)GET_PREV(bp);
	    size_t sign = 0 | GET_PRE_ALLOC_INFO(prev) | GET_PRE_8_INFO(prev);
	    delete_node(prev);
		size += GET_SIZE( prev );
		PUT_HDRP( prev, PACK(size, sign) );
		PUT_FTRP( prev, PACK(size, sign) );
		return prev;
	} else if ( prev_alloc && !next_alloc ) { /* Case 2 */
	    size += GET_SIZE( GET_NEXT(bp) );
	    delete_node( GET_NEXT(bp) );
		size_t sign = 0 | GET_PRE_ALLOC_INFO(bp) | GET_PRE_8_INFO(bp);
		PUT_HDRP( bp, PACK(size,sign) );
		PUT_FTRP( bp, PACK(size,sign) );
		return bp;
	} else { /* Case 3 */
	    void * prev = (void *)GET_PREV(bp);
	    void * next = (void *)GET_NEXT(bp);
	    size += GET_SIZE( prev ) + GET_SIZE( next );
	    
		delete_node( prev );
		delete_node( next );
		
		size_t sign = 0 | GET_PRE_ALLOC_INFO(bp) | GET_PRE_8_INFO(bp);
        PUT_HDRP( prev, PACK(size,sign) );
		PUT_FTRP( prev, PACK(size,sign) );
		return prev;
	}
}

/*place function is used to assign a free block to a malloc or realloc function. Firstly,
it delete the node from the corresponding place(list or BST). Secondly, it check if the remain
size is greater than 8 word(the minimum size). If so, put the remainder to the list or BST*/

static void place(void *bp,size_t asize)
{
	size_t csize = GET_SIZE(bp);
	delete_node( bp );
	if((csize-asize) >= ALIGN_REQ){
	    size_t sign = 1 | GET_PRE_ALLOC_INFO(bp) | GET_PRE_8_INFO(bp);
		PUT_HDRP( bp,PACK(asize,sign) );

		void * temp = GET_NEXT(bp);
		PUT_HDRP( temp, PACK(csize-asize,2) );
		PUT_FTRP( temp, PACK(csize-asize,2) );
		
		insert_node( coalesce(temp) );
	} else{
	    size_t sign = 1 | GET_PRE_ALLOC_INFO(bp) | GET_PRE_8_INFO(bp);
		PUT_HDRP(bp,PACK(csize, sign) );
	}
}

/*the match function divides the argument value into three situations:
1. The size = 8. Search from the list_for_8(single direction linklist).
2. The size = 16. Search from the list_for_16(double directions linklist)
3. The size >= 24. Search from the Binary Search Tree */

static void *match( size_t asize )
{
    if(asize == 8 && list_for_8 != NULL_POINTER) return list_for_8;
    if(asize <= 16 && list_for_16 != NULL_POINTER) return list_for_16;
	/* the most fit block */
	void *fit = NULL_POINTER;
	/* temporary location of the search */
	void *temp = root;
	/* use tree to implement a comparative best fit search */
	while(temp != NULL_POINTER){
		if( asize <= GET_SIZE(temp) ){
			fit = temp;
			temp = (void *)GET_LEFT(temp);
		} else
			temp = (void *)GET_RIGHT(temp);
	}
	return fit;
}

/*insert_node function frist get the size of the block the pointer points to.
1. Size = 8. Put the block into the list_for_8 single direction linkedlist. Reset the
list header. Meanwhile set the third bit of the header of the next block to 1.
2. Size = 16. Put the block into the list_for_16 double directions linkedlist. Reset the
list header.
3. Size >= 24. Put the block into the BST. The situation itself can also be divided into 
three situations, the insert node would be the node, or the left child or the right child.*/

inline static void insert_node( void *bp ) {

	RESET_PREALLOC_INFO(GET_NEXT(bp)); //reset the second bit of the HDRPer of the next block

    if (GET_SIZE(bp) == 8) {
    	PUT_LEFT(bp, list_for_8);
    	list_for_8 = bp;
    	/*used to be wrong with mistaking SET to RESET */
    	SET_PRE_8_INFO(GET_NEXT(bp)); 
    	
    	return;
    } else if (GET_SIZE(bp) == 16){
    	if (list_for_16 == NULL_POINTER) {
    		PUT_RIGHT(bp, list_for_16);
    		PUT_LEFT(bp, NULL_POINTER);
    		list_for_16 = bp;
    		return;
    	}
    	PUT_RIGHT(bp, list_for_16);
    	PUT_LEFT(list_for_16, bp);
    	PUT_LEFT(bp, NULL_POINTER);
    	list_for_16 = bp;
    } else {					//use BST when block size > 16
    	if (root == NULL_POINTER) {
    		PUT_LEFT(bp, NULL_POINTER);
    		PUT_RIGHT(bp, NULL_POINTER);
    		PUT_PARENT(bp, NULL_POINTER);
    		PUT_BROTHER(bp, NULL_POINTER);
    		root = bp;   //root is also an address.
    		return;
    	} else {
    		void *parent = root;
    		void *temp = root;
    		int flag = 0; 
    		/*flag = 0 : the root itself; flag = 1 : left; flag = 2 : right*/
    		while (temp != NULL_POINTER) {
    			/*when finding the free block in BST with the same size*/
    			if (GET_SIZE(temp) == GET_SIZE(bp)) {
    				PUT_LEFT(bp, GET_LEFT(temp));
    				PUT_RIGHT(bp, GET_RIGHT(temp));
    				PUT_BROTHER(bp, temp);
    				PUT_PARENT(GET_LEFT(temp), bp);
    				PUT_PARENT(GET_RIGHT(temp), bp);
    				PUT_LEFT(temp, bp);

    				PUT_PARENT(bp, GET_PARENT(temp));
    				if (flag == 0) {
    					root = bp;
    				} else if (flag == 1) {
    					PUT_LEFT(parent, bp);
    				} else {
    					PUT_RIGHT(parent, bp);
    				}
    				
    				return;
    				/*SEARCH RIGHT CHILD*/
    			} else if (GET_SIZE(temp) < GET_SIZE(bp)) {
    				parent = temp;
    				temp = (void *)GET_RIGHT(temp);
    				flag = 2;
    				/*SEARCH LEFT CHILD*/
    			} else {
    				parent = temp;
    				temp = (void *)GET_LEFT(temp);
    				flag = 1;
    			}
    		
    		}
    		/*insert new node*/
    		if (flag == 1) {
    			PUT_LEFT(parent, bp);
    		} else {
    			PUT_RIGHT(parent, bp);
    		}
    		
    		PUT_LEFT(bp, NULL_POINTER);
    		PUT_RIGHT(bp, NULL_POINTER);
			PUT_PARENT(bp, parent);
			PUT_BROTHER(bp, NULL_POINTER);   		
    	
    	}
    
    }
      //BST_checker(root);
}


/*this is used by the first node of a size*/
inline static int get_direction(void * bp) {
	void * parent = (void *)GET_PARENT(bp);
	if (parent == NULL_POINTER) {
		return 0;
	}
	if ((void *)GET_LEFT(parent) == bp) {
		return 1;
	}
	if ((void *)GET_RIGHT(parent) == bp) {
		return 2;
	}
	
	return -1;

}

/*delete_node function divide the delete operation into three situations by the size
of the block the pointer points to.
1. the size = 8. Delete it from the list_for_8 single direction linked list
2. the size = 16. Delete it from the list_for_16 double directions linked list
3. Others. Call the function delete to delete a node in the Binary Search Tree*/
inline static void delete_node(void *bp)
{
    SET_PREALLOC_INFO(GET_NEXT(bp));
    
    if (GET_SIZE(bp) == 8) {
    	/*the previous free block condition can be judged by the third bit*/
    	RESET_PRE_8_INFO(GET_NEXT(bp));
    	if (bp == list_for_8) {
    		list_for_8 = (void *)GET_LEFT(bp);
    		return;
    	}
    	/*search the position of bp when bp is not the first node*/
    	void * finder = list_for_8;
    	void * before = finder;
    	while (finder != bp) {
    		before = finder;
    		finder = (void *)GET_LEFT(finder);
    	}
    	PUT_LEFT(before, GET_LEFT(finder));
    	
    } else if (GET_SIZE(bp) == 16) {
    	if (bp == list_for_16) {
    		list_for_16 = (void *)GET_RIGHT(bp);
    		PUT_LEFT(list_for_16, NULL_POINTER);
    		return;
    	} 
    	
    	void * bpleft = (void *)GET_LEFT(bp);
    	void * bpright = (void *)GET_RIGHT(bp);
    	
    	PUT_RIGHT(GET_LEFT(bp), bpright);
    	PUT_LEFT(GET_RIGHT(bp), bpleft);
    		
    	return;
    } else {
    	/*delete a node in the BST*/
    	
		delete(bp);
		
    	
    }
		
}

/*The delete function is used to delete a node in the binary search tree. If mainly divide
the operation into three situations.
1. bp points to the first element of the size but it is ot the only node of the size
2. bp points to the only element of the size. In this situation, call the delet_first_node
function to do further operations.
3. bp points to a node which is not the first node of the size.
The variable direction, is used to judge either the node to be delete is the left child,
or the right child, or the root itself.*/
inline static void delete(void *bp) {

	/*if bp points to the first element of the size*/
	void * left = (void *)GET_LEFT(bp);
	if ((left == NULL_POINTER) || (GET_SIZE(left) != GET_SIZE(bp))) {
		int direction = get_direction(bp);
		if (direction == -1) {
			printf("sth wrong with direction ! /n");
		}
		/*when the node to be delete is not the only node of the size*/
		if ((void *)GET_BROTHER(bp) != NULL_POINTER) {
			void * nextbrother = (void *)GET_BROTHER(bp);
			PUT_LEFT(nextbrother, GET_LEFT(bp));
			PUT_RIGHT(nextbrother, GET_RIGHT(bp));
			PUT_PARENT(nextbrother, GET_PARENT(bp));
			
			if ((void *)GET_LEFT(bp) != NULL_POINTER) {
				PUT_PARENT((void *)GET_LEFT(bp), nextbrother);
			}
			
			if ((void *)GET_RIGHT(bp) != NULL_POINTER) {
				PUT_PARENT((void *)GET_RIGHT(bp), nextbrother);
			}
			
			if (direction == 1) {
				PUT_LEFT((void *)GET_PARENT(bp), nextbrother);
			} else if (direction == 2){
				PUT_RIGHT((void *)GET_PARENT(bp), nextbrother);
			} else {
				root = nextbrother;
				PUT_PARENT(root, NULL_POINTER);
				
			}
			
		} else {
			/*when the node to be delete is the only node of the size*/
			delete_first_node(bp, direction);
		}
		
	} else {
		void * left = (void *)GET_LEFT(bp);
		void * brother = (void *)GET_BROTHER(bp);
		PUT_BROTHER(left, brother);
		if (brother != NULL_POINTER) {
			PUT_LEFT(brother, left);
		}
		
		
	
	} 

}

/*The delete_first_node function divide the operation into four situations
1. The node to be deleted has no child.
2. The node to be deleted has no right child.
3. The node to be deleted has no left child.
4. The node to be deleted has both child */
inline static void delete_first_node(void * bp, int direction) {
	void * parent = (void *)GET_PARENT(bp);
	if (((void *)GET_LEFT(bp) == NULL_POINTER) &&  ((void *)GET_RIGHT(bp) == NULL_POINTER)) {
		if (direction == 1) {
			PUT_LEFT(parent, NULL_POINTER);
		} else if (direction == 2){
			PUT_RIGHT(parent, NULL_POINTER);
		} else {
			root = NULL_POINTER;
		}
		
		return;
	}

	/*when the node to be deleted has no left child*/
	if ((void *)GET_LEFT(bp) == NULL_POINTER) {
		if (direction == 1) {
			PUT_LEFT(parent, GET_RIGHT(bp));
			PUT_PARENT((void *)GET_RIGHT(bp), parent);
		} else if (direction == 2){
			PUT_RIGHT(parent, GET_RIGHT(bp));
			PUT_PARENT((void *) GET_RIGHT(bp), parent);
		} else {
			root = (void *)GET_RIGHT(bp);
			PUT_PARENT((void *)GET_RIGHT(bp), NULL_POINTER);
		}
			
		return;
	} 
	/*when the node to be deleted has no right child*/
	if ((void *)GET_RIGHT(bp) == NULL_POINTER) {
		if (direction == 1) {
			PUT_LEFT(parent, GET_LEFT(bp));
			PUT_PARENT((void *)GET_LEFT(bp), parent);
		} else if (direction == 2){
			PUT_RIGHT(parent, GET_LEFT(bp));
			PUT_PARENT((void *) GET_LEFT(bp), parent);
		} else {
			root = (void *)GET_LEFT(bp);
			PUT_PARENT((void *)GET_LEFT(bp), NULL_POINTER);
		}
		
		return;
	}
	
	/*when the node to be deleted has both children*/
	void * maxparent = bp;
	void * max = (void *)GET_LEFT(bp);
	while ((void *)GET_RIGHT(max) != NULL_POINTER) {
		maxparent = max;
		max = (void *)GET_RIGHT(max);
	}
	if (maxparent != bp) {
		/*parent of the max node in the left branch*/
		PUT_RIGHT(maxparent, GET_LEFT(max));
		if ((void *)GET_LEFT(max) != NULL_POINTER) {
			PUT_PARENT(GET_LEFT(max), maxparent);
		}
		
		/*when maxparent = bp, it is not needed to change the left child of the max*/
		PUT_LEFT(max, GET_LEFT(bp));
		
		if ((void *)GET_LEFT(bp) != NULL_POINTER) {
			PUT_PARENT(GET_LEFT(bp), max);
		}
	} 
	
	PUT_RIGHT(max, GET_RIGHT(bp));
	if ((void *)GET_RIGHT(bp) != NULL_POINTER) {
			PUT_PARENT(GET_RIGHT(bp), max);
		}
	
	PUT_PARENT(max, GET_PARENT(bp));
		
	if (direction == 1) {
		PUT_LEFT(parent, max);
	} else if (direction == 2){
		PUT_RIGHT(parent, max);
	} else {
		root = max;
	}
	
}

/*verbose = 0: list_for_8_checker
  verbose = 1: list_for_16_checker
  verbose = 2: BST checker
  */
void mm_checkheap(int verbose) 
{
	if (verbose == 0) {
		list_for_8_checker();
	} else if (verbose == 1) {
		list_for_16_checker();
	} else if (verbose == 2) {
		BST_checker(root);
	} else {
		printf("invalid verbose !\n");
	}
}

inline static void list_for_8_checker() {
	void * check_pointer = list_for_8;
	
	while (check_pointer != NULL_POINTER) {
		printBlock(check_pointer);
		check_pointer = (void *)GET_LEFT(check_pointer);
	}
}

inline static void list_for_16_checker() {
	void * check_pointer = list_for_16;
	
	while (check_pointer != NULL_POINTER) {
		printBlock(check_pointer);
		check_pointer = (void *)GET_RIGHT(check_pointer);
	}
}

inline static void BST_checker(void * bp) {
	void * check_pointer = bp;
	
	if (check_pointer == NULL_POINTER) {
		return;
	}
	printBlock(check_pointer);
	BST_checker((void *)GET_LEFT(bp));
	BST_checker((void *)GET_RIGHT(bp));
}

inline static void printBlock(void * bp) {
	if (GET_SIZE(bp) == 8) {
		printf("Address = %p, LEFT = %p\n", bp, (void *)GET_LEFT(bp));
	} else if (GET_SIZE(bp) == 16) {
		printf("Address = %p, LEFT = %p, RIGHT = %p\n", bp, (void *)GET_LEFT(bp),
				(void *)GET_RIGHT(bp));
	} else if (GET_SIZE(bp) >= 24) {
		printf("Below is the brother: \n\n");
		while (bp != NULL_POINTER) {
			printf("Address = %p, Parent = %p, Brother = %p, Left = %p, Right = %p \n",
				bp, (void *)GET_PARENT(bp), (void *)GET_BROTHER(bp), (void *)GET_LEFT(bp),
				(void *)GET_RIGHT(bp));
			bp = (void *)GET_BROTHER(bp);
		}
		printf("\n\n");
		
	} else {
		printf("wrong in data alignment!\n");
	}
}

