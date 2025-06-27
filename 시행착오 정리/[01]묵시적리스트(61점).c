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
#include <math.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "방법이있지",
    /* First member's full name */
    "송상록",
    /* First member's email address */
    "drinkingstraw33@gmail.com",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

// 기본 매크로 상수
#define WSIZE 4                 // 워드, 헤더, 푸터의 크기 (4바이트)
#define DSIZE 8                 // 더블 워드의 크기 (8바이트)
#define CHUNKSIZE (1 << 12)     // 힙 연장 시 이만큼 (4096 바이트)

// 기본 매크로 함수
#define MAX(x, y) ((x) > (y)? (x): (y))         // 두 값 중 더 큰 값
// 크기 비트와 할당 비트 통합 -> 헤더, 푸터 저장용
#define PACK(size, alloc) ((size) | (alloc))    
// p는 (void *)일 수 있으니 (unsigned char *)로 변환. 포인터가 참조하는 워드 리턴.
#define GET(p) (*(unsigned int *)(p))         
 // 포인터가 참조하는 워드에 val을 저장.  
#define PUT(p, val) (*(unsigned int *)(p) = (val)) 
// 주소 p가 헤더일 때, 저장된 size를 반환
#define GET_SIZE(p) (GET(p) & ~0x7)     
 // 주소 p가 헤더일 때, 저장된 유효 비트를 반환        
#define GET_ALLOC(p) (GET(p) & 0x1)            

// 이로서 힙의 각 영역은 일단 char 형임을 알 수 있다
// 블록 주소는 헤더 끝, 실제 할당 메모리 영역 사이임을 잊지 말아라

// 블록 주소로, 헤더의 주소 계산 (헤더의 크기만큼 빼줌)
#define HDRP(bp) ((char *)(bp) - WSIZE)             

// 블록 주소로, 푸터의 주소 계산 (푸터 및 다음 헤더의 크기만큼 빼줌)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)          

// 다음 블록 주소 계산.
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))             
// 이전 블록 주소 계산.
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE)))             

static char *heap_listp;                    // 첫 블록을 가리킴
static void *extend_heap(size_t);
static void *coalesce(void *);
static void *find_fit(size_t);
static void place(void *bp, size_t asize);
static void check_all();

/*
 * mm_init - initialize the malloc package.
 * 필요한 초기화 수행 (e.g., 초기 힙 영역을 할당한다)
 */
int mm_init(void)
{
    // mem_init()은 해줄 필요 없음. 이미 mdriver.c에 있음.

    // (1) 메모리 시스템에서 4워드(16바이트)를 가져와서, 빈 가용 리스트를 만듦
    heap_listp = (char *)mem_sbrk(4 * WSIZE);
    if (heap_listp == (void *) -1) return -1;   // 메모리 할당에 실패했을 때

    // (2) 16바이트를 채워야 함
    PUT(heap_listp, 0);                             // (A) 맨 처음 비어 있는 4바이트
    PUT(heap_listp + WSIZE, PACK(DSIZE, 1));        // (B) 프롤로그 블록의 헤더 (8 / 1)
    PUT(heap_listp + WSIZE * 2, PACK(DSIZE, 1));    // (C) 프롤로그 블록의 푸터 (8 / 1)
    PUT(heap_listp + WSIZE * 3, PACK(0, 1));        // (D) 에필로그 블록의 헤더

    heap_listp += WSIZE * 2;      

    // 힙 확장하기
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
        return -1;
                      
}

// 힙이 초기화될 때 OR mm_malloc이 fit을 찾지 못했을 때, 힙을 요청크기 만큼 확장
static void *extend_heap(size_t words){
    size_t size = ALIGN(words * WSIZE);
    char *bp;

    // 메모리 시스템에서 추가공간 요청
    bp = mem_sbrk(size);                        // 새로 할당된 블록의 포인터
    if (bp == (void *) -1) return NULL;         // 메모리 할당에 실패했을 때

    // 이전 에필로그 블록 자리에, 새로운 헤더가 옴
    PUT(HDRP(bp), PACK(size, 0));                       // 헤더

    // 새로운 푸터 및 에필로그 블록
    PUT(FTRP(bp), PACK(size, 0));                       // 푸터
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1));       // 에필로그블록
    
    // Coalesce 함수로 병합
    return coalesce(bp);

}

/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 * 최소 size 바이트로 메모리를 할당한 후, 시작 주소를 담은 포인터를 반환한다.
 * 힙 영역 내 위치해야 하며, 다른 할당 영역과 겹치면 안 된다.
 * 8바이트 단위로 정렬한다.
 */
void *mm_malloc(size_t size)
{
    size_t asize;       // 실제로 할당되는 블록의 크기
    size_t extendsize;  // fit이 없는 경우 이만큼 힙을 연장
    char *bp;

    // size == 0인 경우 NULL을 반환
    if (size == 0) return NULL;

    // 현재 size에 헤더 + 푸터를 포함하고, 인접한 DSIZE의 배수로 올림 (패딩)
    asize = ALIGN(size + DSIZE);
        
    // 맞는 칸이 있는지 확인
    bp = find_fit(asize);
    if (bp != NULL){
        place(bp, asize);   // 주소 bp에서 asize만큼 할당
        return bp;          // 할당된 블록 주소 반환 
    }

    // 맞는 칸이 없으면 힙을 연장
    extendsize = MAX(asize, CHUNKSIZE);
    bp = extend_heap(extendsize / WSIZE);

    if (bp == NULL){
        return NULL;
    } else {
        place(bp, asize);
        return bp;
    }
}

/*
 * mm_free - Freeing a block does nothing.
 * ptr가 가리키는 블록의 메모리 할당을 해제한다.
 * 반환값이 없다.
 * mm_malloc, mm_realloc으로 할당된 포인터를 매개변수로 대입해야 한다.
 */
void mm_free(void *ptr)
{
    // 요청한 블록을 반환
    // 그러면 해당 주소의 할당 비트는 1 -> 0이 되지 않을까?
    size_t size = GET_SIZE(HDRP(ptr));
    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));

    // 인접 가용 블록을 통합
    coalesce(ptr);
}

// ptr이 가리키는 블록과 인접 블록을 연결 후, 연결된 블록의 주소 반환
static void *coalesce(void *ptr){
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(ptr)));    // 이전블록 할당비트
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(ptr)));    // 다음블록 할당비트
    size_t size = GET_SIZE(HDRP(ptr));

    if (prev_alloc && next_alloc){
        // 연결 불가능. 현재 블록의 주소 return
    } else if (prev_alloc) {
        // 다음 블록과 연결 가능.
        size += GET_SIZE(HDRP(NEXT_BLKP(ptr)));     // 다음 블록의 크기 더하기
        PUT(HDRP(ptr), PACK(size, 0));             // 현재 블록의 헤더 수정
        PUT(FTRP(ptr), PACK(size, 0));             // 다음 블록의 푸터 수정 (한 블록으로 통합되었음에 유의할 것.)
    } else if (next_alloc) {
        // 이전 블록과 연결 가능.
        size += GET_SIZE(HDRP(PREV_BLKP(ptr)));     // 이전 블록의 크기 더하기
        PUT(FTRP(ptr), PACK(size, 0));             // 현재 블록의 푸터 수정
        PUT(HDRP(PREV_BLKP(ptr)), PACK(size, 0));  // 이전 블록의 헤더 수정
        ptr = PREV_BLKP(ptr);                       // 통합된 블록으로 주소 갱신
    } else {
        // 이전, 다음 블록과 연결 가능.
        size += GET_SIZE(HDRP(PREV_BLKP(ptr)));     // 이전 블록의 크기 더하기
        size += GET_SIZE(FTRP(NEXT_BLKP(ptr)));     // 다음 블록의 크기 더하기
        PUT(HDRP(PREV_BLKP(ptr)), PACK(size, 0));  // 이전 블록의 헤더 수정
        PUT(FTRP(NEXT_BLKP(ptr)), PACK(size, 0));  // 다음 블록의 푸터 수정
        ptr = PREV_BLKP(ptr);                       // 통합된 블록으로 주소 갱신
    }
    return ptr;
}

// 묵시적 가용 리스트에서 first fit 검색을 수행.
static void *find_fit(size_t asize){
    void *bp;      // 현재 검색중인 블록
    size_t block_size;          // 현재 블록의 크기
    // 에필로그 블록 도달 시 종료
    for (bp = heap_listp; (block_size = GET_SIZE(HDRP(bp))) != 0; bp = NEXT_BLKP(bp)){
        // 사이즈에 맞는 가용 블록이 있는 경우, 해당 블록 주소를 반환
        if (asize <= block_size && GET_ALLOC(HDRP(bp)) == 0){
            return bp;
        }
    }
    return NULL;
}

// 요청한 블록을 가용 블록의 시작에 배치.
// 분할은 나머지 부분의 크기가 최소 블록 크기 이상일 때만 수행.
static void place(void *bp, size_t asize){
    size_t curr_size, rest_size;
    
    // 나머지 부분의 크기를 계산한다
    curr_size = GET_SIZE(HDRP(bp));
    rest_size = curr_size - asize;

    if (rest_size >= 4 * WSIZE){
        // 최소 블록 크기 이상인 경우 분할을 수행한다

        // 앞 블록의 헤더
        PUT(HDRP(bp), PACK(asize, 1));
        // 앞 블록의 푸터
        PUT(FTRP(bp), PACK(asize, 1));
        // 뒷 헤더 만들기
        PUT(HDRP(NEXT_BLKP(bp)), PACK(rest_size, 0));
        // 뒷 블록의 푸터 만들기
        PUT(FTRP(NEXT_BLKP(bp)), PACK(rest_size, 0));
    } else {
        // 최소 블록 크기 이상이 아닌 경우, 분할을 수행하지 않는다
        // 헤더, 푸터만 0에서 1로 바꾸기
        PUT(HDRP(bp), PACK(curr_size, 1));
        PUT(FTRP(bp), PACK(curr_size, 1));
    }
}

static void check_all(){
    char *bp = heap_listp;
    size_t block_size;
    
    // 에필로그 블록 도달 시 종료
    while (1){
        block_size = GET_SIZE(HDRP(bp));
        printf("(%d/%d) ", block_size, GET_ALLOC(HDRP(bp)));
        if (block_size == 0) break;
        bp = NEXT_BLKP(bp);
    }
    printf("\n"); 
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 * 최소 size 크기의 메모리 할당 후 포인터를 반환한다.
 * ptr가 NULL -> mm_malloc(size)와 동일.
 * size가 0 -> mm_free(ptr)과 동일.
 * 둘 다 아닌 겨우(정상적인 경우), ptr가 가리키는 메모리 블록의 크기를 size로 바꾸고 새 블록을 반환. 이때 주소는 같을 수도 있고 다를 수도 있음.
 * 블록 내 데이터는 이전 블록의 크기와 이후 블록의 크기 중 최솟값을 기준.
 */
void *mm_realloc(void *ptr, size_t size)
{
    if (ptr == NULL){
        return mm_malloc(size);
    } else if (size == 0){
        mm_free(ptr);
        return NULL;
    }

    void *oldPtr = ptr;
    void *newPtr = mm_malloc(size);

    // 이전 블록의 크기
    size_t copySize = GET_SIZE(HDRP(ptr));

    if (size < copySize){
        copySize = size;
    }

    // 이전 블록의 내용을 새 블록으로 복사
    memcpy(newPtr, oldPtr, copySize);

    // 이전 블록에 할당된 메모리 free
    mm_free(oldPtr);

    return newPtr;
}