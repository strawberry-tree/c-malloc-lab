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

// 이로서 힙의 각 영역은 일단 char 형임을 알 수 있다
// 블록 주소는 헤더 끝, 실제 할당 메모리 영역 사이임을 잊지 말아라

// 블록 주소로, 다음 노드를 가리키는 포인터의 주소 반환
#define HDRP(bp) ((char *)(bp) - WSIZE);
#define NXTP(bp) ((char *)(bp))             
         

char *heaps[14] = {NULL};           
static void *extend_heap(size_t);
static void *coalesce(void *);
static void *find_fit(size_t);
static void place(void *bp, size_t asize);
// static void check_all();
static size_t round(asize);

size_t round(asize){
    size_t sizes = [3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13];
    for (int i = 0; i < 12; i++){
        if asize <= (1 << sizes[i]) break;
    }
    return i;
}

/*
 * mm_init - initialize the malloc package.
 * 필요한 초기화 수행 (e.g., 초기 힙 영역을 할당한다)
 */
int mm_init(void)
{
    // mem_init()은 해줄 필요 없음. 이미 mdriver.c에 있음.
    // 12개의 빈 가용 리스트를 만듦

    // (1) 메모리 시스템에서 12워드(48바이트)를 가져옴
    heap_listp = (char *)mem_sbrk(12 * WSIZE);
    if (heap_listp == (void *) -1) return -1;   // 메모리 할당에 실패했을 때

    // (2) 각 워드는, 각 분리 가용 리스트의 첫 바이트 (값 없이 포인터만 저장함)
    // 각 분리 가용 리스트의 시작 주소는 heaps[i]에 저장됨
    for (int i = 0; i < 12; i++){
        heaps[i] = heap_listp + DSIZE * i;  
        PUT(heaps[i], 0);       // 나중에 각 분리 가용 리스트의 head 주소가 저장됨 
    }

    return 0;         
}

// 힙이 초기화될 때 OR mm_malloc이 fit을 찾지 못했을 때, 힙을 요청크기 만큼 확장
// 확장 후, 메모리를 동일 크기의 블록 'size'로 나누며, 함께 연결해 가용 리스트를 만듦 (이때 크기는 blockSize)
static void *extend_heap(size_t words, int bIndex){
    size_t bsize = 1 << (bIndex + 3);
    size_t size = ALIGN(words * WSIZE);
    char *bp;

    // 메모리 시스템에서 추가공간 요청
    bp = mem_sbrk(size);                         // 새로 할당된 블록의 포인터
    if (bp == (void *) -1) return NULL;          // 메모리 할당에 실패했을 때

    // 할당받은 공간을 나누어 분리 리스트에 넣기.
    for (int k = 0; k < size / bIndex; k++){
        PUT(bp + bSize * k, bIndex);   // 헤더에 해당. 인덱스를 저장. 유효비트는 저장 안해도됨.
        PUT(bp + bSize * k + WSIZE, heaps[bIndex]);      // 포인터에 해당. 현재 헤드를 저장.
        heaps[bIndex] = bp + bSize * k + WSIZE;          // 헤드를 갱신.
    }

    return heaps[bIndex];
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
    int asize;          // 몇번째 분리 리스트
    size_t extendsize;  // fit이 없는 경우 이만큼 힙을 연장
    char *bp;

    // size == 0인 경우 NULL을 반환
    if (size == 0) return NULL;

    // 현재 size를 특정 구간 (8, 16, 32, 64....)으로 올림
    bIndex = round(size);
        
    // 가용 리스트가 비었는지 확인
    if (heaps[bIndex] == NULL){
        // 비어 있으면 연장해야함
        extendsize = MAX(asize, CHUNKSIZE);
        extend_heap(extendsize / WSIZE, bIndex);
    }

    place(heaps[bIndex], bIndex);   // 주소 bp의 블록 할당
    return bp;           // 할당된 블록 주소 반환 
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
    // 해당 블록은 가용 리스트 맨 앞으로 이동

    // 여기서 해당 크기만 보여있는 bIndex를 찾아야 함
    // TODO 1. 여기서 크기를 어케 확인하지...?
    int bIndex = GET(HDRP(ptr));
    PUT(ptr, heaps[bIndex]);
    PUT(heaps[bIndex], ptr);

}


// 요청한 블록을 가용 블록의 시작에 배치.
static void place(void *bp, int bIndex){
    PUT(heaps[bIndex], GET(bp));
    return bp;
}

// static void check_all(){
//     char *bp = heap_listp;
//     size_t block_size;
    
//     // 에필로그 블록 도달 시 종료
//     while (1){
//         block_size = GET_SIZE(HDRP(bp));
//         printf("(%d/%d) ", block_size, GET_ALLOC(HDRP(bp)));
//         if (block_size == 0) break;
//         bp = NEXT_BLKP(bp);
//     }
//     printf("\n"); 
// }

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
    size_t copySize = 1 << GET(HDRP(ptr));

    if (size < copySize){
        copySize = size;
    }

    // 이전 블록의 내용을 새 블록으로 복사
    memcpy(newPtr, oldPtr, copySize);

    // 이전 블록에 할당된 메모리 free
    mm_free(oldPtr);

    return newPtr;
}