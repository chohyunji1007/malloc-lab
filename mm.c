// week05는 나만의 malloc. realloc, free 함수를 구현하는 것! 
// implicit 방법으로 구현해 ./mdriver가 정상 작동하도록 코드 완성하기
// malloc 구현은 항상 8바이트에 정렬된 포인터를 반환해야 합니다.
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


/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "ateam",
    /* First member's full name */
    "Harry Bovik",
    /* First member's email address */
    "bovik@cs.cmu.edu",
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

// Basic constants and macros
#define WSIZE 4 // Word and Header/Footer size (bytes)
#define DSIZE 8 // Double word size
#define CHUNKSIZE (1<<12) // extend heap by this amount (bytes)

#define MAX(x, y) ((x)>(y)?(x):(y))

//Pack a size and allocated bit into a word
#define PACK(size, alloc) ((size)|(alloc))

//Read and write a word at address p
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

//Read the size and allocated fields from address p
#define GET_SIZE(p) (GET(p) & ~0x7) // block size 는 뒤 세자리 빼고 쓰는거라 ~0x7 = 1111 1000 이므로 AND연산자를 이용해 뒷자리 3자리는 날림
#define GET_ALLOC(p) (GET(p) & 0x1) // allocated 인지 free인지는 맨 뒷자리 1자리만 보면 되므로 0000 0001 과 AND 연산자를 이용해 맨 뒷자리 확인

//Given block ptr bp, compute address of its header and footer
#define HDRP(bp) ((char *)(bp) - WSIZE) //block pointer - word size = header pointer
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) //block pointer + header size - 

//Given block ptr bp, compute address of next and previous blocks
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))

static char *mem_heap;
static char *mem_brk;
static char *mem_max_addr;

void *heap_listp;
void *next_heap_listp;
static void *next_fit(size_t adjusted_size);



static void *coalesce(void *bp){ //free하고 나서 이어져 붙어 있는 남은 공간을 확인해 합치는 함수
  size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
  size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
  size_t size = GET_SIZE(HDRP(bp));

  if(prev_alloc && next_alloc){ //case 1 // 앞 뒤로 꽉차있고 현재 free 한곳만 비어있는 경우 합체 할 필요 없음
    next_heap_listp = bp;
    return bp;
  }
  else if(prev_alloc && !next_alloc){ //case 2 // free 한 부분 다음이 비어있던 경우
    size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
  }
  else if(!prev_alloc && next_alloc){ //case 3 // free 한 부분 이전이 비어있던 경우
    size += GET_SIZE(HDRP(PREV_BLKP(bp)));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(PREV_BLKP(bp)), PACK(size,0));
    bp = PREV_BLKP(bp);
  }
  else{ //case 4 // free 한 부분의 이전과 후가 모두 비어있던 경우
    size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
    PUT(HDRP(PREV_BLKP(bp)), PACK(size,0));
    PUT(FTRP(NEXT_BLKP(bp)), PACK(size,0));
    bp = PREV_BLKP(bp);
    
  }
  next_heap_listp = bp;
  return bp;
}


static void *find_fit(size_t asize){ 
  //first-fit search
  void *bp;
  // for(bp = heap_listp; GET_SIZE(HDRP(bp))>0; bp=NEXT_BLKP(bp)){
  //   if(!GET_ALLOC(HDRP(bp)) && (asize <=GET_SIZE(HDRP(bp)))){ //bp가 0(할당되지 않음) && asize가 bp의 크기보다 작다면 할당 가능!
  //     return bp;
  //   }
  // }
  // return NULL; //No  fit

  //best fit
  void *best_fit = NULL;

  for(bp = heap_listp; GET_SIZE(HDRP(bp))>0; bp = NEXT_BLKP(bp)){
    if(!GET_ALLOC(HDRP(bp)) && (asize <=GET_SIZE(HDRP(bp)))){
      if(!best_fit || GET_SIZE(HDRP(bp)) < GET_SIZE(HDRP(best_fit))){
        best_fit = bp;
      }
    }
  }return best_fit;
}

static void *next_fit(size_t adjusted_size) { //현재 할당 된 다음 가용 블럭에서부터 탐색 시작
    char *bp = next_heap_listp;

    for (bp = NEXT_BLKP(bp); GET_SIZE(HDRP(bp)) != 0; bp = NEXT_BLKP(bp)) {
        if (!GET_ALLOC(HDRP(bp)) && GET_SIZE(HDRP(bp)) >= adjusted_size) {
            next_heap_listp = bp;
            return bp;
        }
    }

    bp = heap_listp;
    while (bp < next_heap_listp) {
        bp = NEXT_BLKP(bp);
        if (!GET_ALLOC(HDRP(bp)) && GET_SIZE(HDRP(bp)) >= adjusted_size) {
            next_heap_listp = bp;
            return bp;
        }
    }

    return NULL;
}

static void place(void *bp, size_t asize){ //분할 후 남은 블록의 크기가 최소블록(16bytes)라면 블록을 하나 더 분할 해야 함.
  size_t csize = GET_SIZE(HDRP(bp));

  if((csize - asize)>=(2*DSIZE)){ //할당하고 남은 블럭이 16바이트 보다 크다면 블록 하나 더 분할
    PUT(HDRP(bp), PACK(asize, 1));
    PUT(FTRP(bp), PACK(asize, 1));
    bp = NEXT_BLKP(bp);
    PUT(HDRP(bp), PACK(csize-asize, 0));
    PUT(FTRP(bp), PACK(csize-asize, 0));
  }else{ //작다면 그냥 그대로 할당~ 
    PUT(HDRP(bp), PACK(csize, 1));
    PUT(FTRP(bp), PACK(csize, 1));
  }
}
static void *extend_heap(size_t words) //heap의 저장공간이 모자라다면 늘려주기!
{
    char *bp;
    size_t size;

    //Allocate an even number of words to maintain alignment
    size = (words % 2)?(words+1)*WSIZE : words * WSIZE;
    if((long)(bp = mem_sbrk(size))==-1)
      return NULL;
    //Initialize free block header/footer and the epilogue header
    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));

    //coalesce(합체v) is the previous block was free
    return coalesce(bp);
}
/* 
 * mm_init - initialize the malloc package.
 mm_malloc, mm_realloc 또는 mm_free를 호출하기 전에 응용 프로그램(즉, 구현을 평가할 때 사용할 추적 드라이버 프로그램)은 
 초기 힙 영역을 할당하는 등 필요한 초기화를 수행하기 위해 mm_init을 호출합니다. 
 초기화 수행에 문제가 발생한 경우 반환값은 -1이어야 하며, 그렇지 않으면 0이어야 합니다.
 */
// heap에서 edge condition을 없애주기 위해 초기화 작업 진행
int mm_init(void)
{   
    // 4word가 필요하므로 heap 전체 영역이 4워드 미만이면 안됨
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1)
        return -1;

    PUT(heap_listp, 0); // alignment padding
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1)); // prologue header // DSIZE = prologue header + footer size
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1)); // prologue footer
    PUT(heap_listp + (3*WSIZE), PACK(0, 1)); // epliogue header
    heap_listp += (2*WSIZE);
    next_heap_listp = heap_listp;
    
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL)
        return -1;
    return 0;
}

/* 
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 * mm_malloc 루틴은 적어도 size 바이트 크기의 할당된 블록 페이로드를 가리키는 포인터를 반환합니다. 
 * 전체 할당된 블록은 힙 영역 내에 있어야 하며 다른 할당된 청크와 겹치지 않아야 합니다.
 */ 
void *mm_malloc(size_t size)
{
    size_t asize;
    size_t extendsize;
    char *bp;
    
    if (size == 0)
        return NULL;
    if (size <= DSIZE) //최소 할당 단위를 2*8바이트 = 16바이트로 할당 하기 위함
        asize = 2*DSIZE;
    else 
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE);

    if ((bp = next_fit(asize)) != NULL) { //next fit을 실행해 할당할 bp를 찾아줌
        place(bp, asize);
        next_heap_listp = bp;
        return bp;
    }
    //next_fit()==NULL //할당 가능한 남은 블록이 없으므로 extend_heap을 이용해 heap영역을 늘려줌
    extendsize = MAX(asize, CHUNKSIZE);
    if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
        return NULL;
    place(bp, asize);
    next_heap_listp = bp;
    return bp;
}


/*
 * mm_free - Freeing a block does nothing.
   mm_free 루틴은 ptr이 가리키는 블록을 해제, 반환값 X
   이 루틴은 ptr이 이전에 mm_malloc 또는 mm_realloc을 호출하여 반환된 포인터인 경우에만 보장되어 작동해야 합니다.
 */

void mm_free(void *bp) {
    size_t size = GET_SIZE(HDRP(bp));
    PUT(HDRP(bp), PACK(size, 0)); 
    PUT(FTRP(bp), PACK(size, 0)); 
    coalesce(bp); 
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
   mm_realloc 루틴은 적어도 size 바이트 크기의 할당된 영역을 가리키는 포인터를 반환하며 다음 제약 사항을 따릅니다.
   - ptr이 NULL이면 호출은 mm_malloc(size)와 동등합니다.
   - size가 0과 같으면 호출은 mm_free(ptr)와 동등합니다.
   - ptr이 NULL이 아닌 경우, 이전에 mm_malloc 또는 mm_realloc을 호출하여 반환된 것이어야 합니다. 
   mm_realloc 호출은 ptr이 가리키는 메모리 블록(이전 블록)의 크기를 size 바이트로 변경하고 새 블록의 주소를 반환합니다. 
   새 블록의 주소는 구현 방법, 이전 블록의 내부 조각 양 및 재할당 요청의 크기에 따라 이전 블록과 동일하거나 다를 수 있습니다.
 */
void *mm_realloc(void *ptr, size_t size)
{
    void *old_ptr = ptr; // 이전 포인터
    void *new_ptr; // 새로 메모리 할당할포인터

    size_t old_size = GET_SIZE(HDRP(ptr)); // 원본 사이즈
    size_t asize = size + DSIZE; // 새 사이즈

    
    if (asize <= old_size) { // size 가 더 작은 경우 기존 bp 그대로 사용
        return old_ptr;
    } else {
        size_t addSize = old_size + GET_SIZE(HDRP(NEXT_BLKP(old_ptr))); // 추가 사이즈 -> 헤더 포함 사이즈
        if (!GET_ALLOC(HDRP(NEXT_BLKP(old_ptr))) && (asize <= addSize)){ // 가용 블록이고 사이즈 충분
            PUT(HDRP(old_ptr), PACK(addSize, 1)); // new header
            PUT(FTRP(old_ptr), PACK(addSize, 1)); // new footer
            return old_ptr;
        } else {
            new_ptr = mm_malloc(asize);
            if (new_ptr == NULL)
                return NULL;
            memmove(new_ptr, old_ptr, asize); // memcpy 사용 시, memcpy-param-overlap (memcpy : 겹치는 메모리는 지원하지 않음)발생
            mm_free(old_ptr);
            return new_ptr;
            
        }
    }
}
