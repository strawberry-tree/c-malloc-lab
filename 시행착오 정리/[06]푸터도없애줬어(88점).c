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
#include <stdint.h>

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
#define PACK(size, preloc, alloc) ((size) | (preloc) << 1 | (alloc))    
// p는 (void *)일 수 있으니 (unsigned int *)로 변환. 포인터가 참조하는 워드 리턴.
#define GET(p) (*(uintptr_t *)(p))         
 // 포인터가 참조하는 워드에 val을 저장.  
#define PUT(p, val) (*(uintptr_t *)(p) = (uintptr_t)(val)) 
// 주소 p가 헤더일 때, 저장된 size를 반환
#define GET_SIZE(p) (GET(p) & ~0x7)     
// 주소 p가 헤더일 때, 앞 블록의 유효 비트를 반환
#define GET_PRELOC(p) ((GET(p) >> 1) & 0x1)
// 주소 p가 헤더일 때, 저장된 유효 비트를 반환        
#define GET_ALLOC(p) (GET(p) & 0x1)            

// 이로서 힙의 각 영역은 일단 char 형임을 알 수 있다
// 블록 주소는 헤더 끝, 실제 할당 메모리 영역 사이임을 잊지 말아라

// 블록 주소로, 헤더의 주소 계산 (헤더의 크기만큼 빼줌)
#define HDRP(bp) ((char *)(bp) - 1 * WSIZE)     

// 블록 주소로, prev 주소 포인터 계산 (빈 블록만)
#define PRVP(bp) ((char *)(bp))

// 블록 주소로, next 포인터 주소 계산 (빈 블록만)
#define NXTP(bp) ((char *)(bp) + 1 * WSIZE)

// 블록 주소로, 푸터의 주소 계산 (푸터 및 다음 헤더의 크기만큼 빼줌)
// 할당 블록인 경우 적용 불가능
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - 2 * WSIZE)   

// 다음 블록 주소 계산.
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))             
// 이전 블록 주소 계산.
// 이전 블록이 할당 블록인 경우 적용 불가능
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - 2 * WSIZE)))   

// 연결 리스트상 이전 가용 블록의 주소 반환
#define PREV_NODE(bp) ((char *)(GET(PRVP(bp))))

// 연결 리스트상 다음 가용 블록의 주소 반환.
#define NEXT_NODE(bp) ((char *)(GET(NXTP(bp))))

// 연결 리스트상 이전 가용 블록의 주소 설정.
#define SET_PRVP(bp, prev_bp) PUT(PRVP(bp), (uintptr_t)(prev_bp))

// 연결 리스트상 이후 가용 블록의 주소 설정.
#define SET_NXTP(bp, next_bp) PUT(NXTP(bp), (uintptr_t)(next_bp))

#define INDEX_COUNT 18


static char *heap_listp;                    // 프롤로그 블록을 가리킴
static void *headp = NULL;                         // 헤드를 가리킴
static void *extend_heap(size_t);
static void *coalesce(void *);
static void *find_fit(size_t);
static void place(void *bp, size_t asize);
static void pushNode(void *newNode);
static void removeNode(void *erase);
static void check_all();
static int get_index(size_t);
static void *r_split_block(char *, size_t, size_t);

void *heap_heads[INDEX_COUNT];

// // 크기를 입력받고, 어느 인덱스로 갈지 확인
// static int get_index(size_t size){
//     int index;
//     for (index = 4; index < INDEX_COUNT - 1; index++){
//         if (size <= (1 << index)) break;
//     }
//     return index;
// }

int get_index(size_t size) {
    if (size <= 16) return 0;
    else if (size <= 32) return 1;
    else if (size <= 48) return 2;
    else if (size <= 64) return 3;
    else if (size <= 96) return 4;
    else if (size <= 128) return 5;
    else if (size <= 192) return 6;
    else if (size <= 256) return 7;
    else if (size <= 384) return 8;
    else if (size <= 512) return 9;
    else if (size <= 768) return 10;
    else if (size <= 1024) return 11;
    else if (size <= 2048) return 12;
    else if (size <= 4096) return 13;
    else if (size <= 8192) return 14;
    else if (size <= 16384) return 15;
    else if (size <= 32768) return 16;
    else return 17;
}
/*
 * mm_init - initialize the malloc package.
 * 필요한 초기화 수행 (e.g., 초기 힙 영역을 할당한다)
 */
int mm_init(void)
{
    //printf("힙 초기화: ");
    // mem_init()은 해줄 필요 없음. 이미 mdriver.c에 있음.

    for (int i = 0; i < INDEX_COUNT; i++){
        heap_heads[i] = NULL;
    }

    // (1) 메모리 시스템에서 4워드(16바이트)를 가져와서, 빈 가용 리스트를 만듦
    heap_listp = (char *)mem_sbrk(4 * WSIZE);
    if (heap_listp == (void *) -1) return -1;   // 메모리 할당에 실패했을 때

    // (2) 16바이트를 채워야 함
    PUT(heap_listp, 0);                                 // (A) 안 쓰는 블록
    PUT(heap_listp + WSIZE, PACK(WSIZE * 2, 1, 1));        // (B) 프롤로그 블록의 헤더 (8 / 1)
    PUT(heap_listp + WSIZE * 2, 0);    // (C) 패딩
    PUT(heap_listp + WSIZE * 3, PACK(0, 1, 1));            // (E) 에필로그 블록의 헤더

    heap_listp += WSIZE * 2;  


    return 0;
}

// 힙이 초기화될 때 OR mm_malloc이 fit을 찾지 못했을 때, 힙을 요청크기 만큼 확장
static void *extend_heap(size_t words){
   
    size_t size = ALIGN(words * WSIZE);
    char *bp;

    // 메모리 시스템에서 추가공간 요청
    bp = mem_sbrk(size);             // 새로 할당된 블록의 포인터
    if (bp == (void *) -1) return NULL;         // 메모리 할당에 실패했을 때

    // 이전 에필로그 블록 자리에, 새로운 헤더가 옴
    char get_preloc = GET_PRELOC(HDRP(bp));
    PUT(HDRP(bp), PACK(size, get_preloc, 0));                       // 헤더
    PUT(FTRP(bp), PACK(size, get_preloc, 0));                       // 푸터
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 0, 1));               // 에필로그블록
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

    // 현재 size에 헤더를 포함하고, 인접한 DSIZE의 배수로 올림 (패딩)
    // 이때 푸터와 포인터는 저장할 필요가 없음에 유의.
    asize = ALIGN(size + WSIZE);
        
    // 맞는 칸이 있는지 확인
    bp = find_fit(asize);
    
    if (bp != NULL){
        place(bp, asize);   // 주소 bp에서 asize만큼 할당
        return bp;          // 할당된 블록 주소 반환 
    }

    // 맞는 칸이 없으면 힙을 연장
    extendsize = MAX(asize, CHUNKSIZE);
    bp = extend_heap(extendsize / WSIZE);
    // bp = extend_heap(asize / WSIZE);
    //printf("최종: ", asize);
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
    PUT(HDRP(ptr), PACK(size, GET_PRELOC(HDRP(ptr)), 0));
    PUT(FTRP(ptr), PACK(size, GET_PRELOC(HDRP(ptr)), 0));

    // 인접 가용 블록을 통합. 연결도 여기서 이루어짐.
    coalesce(ptr);
}

// 연결 리스트에서 노드 erase를 제거.
static void removeNode(void *erase){
    if (erase == NULL)
        return;

    int index = get_index(GET_SIZE(HDRP(erase)));

    void *prev = PREV_NODE(erase);
    void *next = NEXT_NODE(erase);

    if (prev == NULL) heap_heads[index] = next;
    else {
        SET_NXTP(prev, next);
    }

    if (next != NULL){
        SET_PRVP(next, prev);
    }   
    
}

// 연결 리스트의 맨 앞에 노드를 연결.
static void pushNode(void *newNode){
    int index = get_index(GET_SIZE(HDRP(newNode)));
    SET_PRVP(newNode, NULL);
    SET_NXTP(newNode, heap_heads[index]);
    if (heap_heads[index] != NULL){
        SET_PRVP(heap_heads[index], newNode);
    }
    heap_heads[index] = newNode;
}

// ptr이 가리키는 블록과 인접 블록을 연결 후, 연결된 블록의 주소 반환. 얜 리스트랑 상관없이 인접하면 병합.
// 대신 이걸로 통합되면 연결관계를 바꿔주긴 해야 함.
static void *coalesce(void *ptr){
    size_t prev_alloc = GET_PRELOC(HDRP(ptr));              // 이전블록 할당비트
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(ptr)));    // 다음블록 할당비트
    size_t size = GET_SIZE(HDRP(ptr));
    char get_preloc;                                        // 현재 블록의 이전블록할당비트 설정


    if (!prev_alloc && !next_alloc){
        // 이전, 다음 블록과 연결 가능.
        get_preloc = GET_PRELOC(HDRP(PREV_BLKP(ptr)));

        // 이전, 다음 블록을 연결 리스트에서 제거
        removeNode(PREV_BLKP(ptr));
        removeNode(NEXT_BLKP(ptr));

        size += GET_SIZE(HDRP(PREV_BLKP(ptr)));     // 이전 블록의 크기 더하기
        size += GET_SIZE(HDRP(NEXT_BLKP(ptr)));     // 다음 블록의 크기 더하기
        PUT(HDRP(PREV_BLKP(ptr)), PACK(size, get_preloc, 0));   // 이전 블록의 헤더 수정
        PUT(FTRP(NEXT_BLKP(ptr)), PACK(size, get_preloc, 0));   // 다음 블록의 푸터 수정
        ptr = PREV_BLKP(ptr);                       // 통합된 블록으로 주소 갱신
    } else if (!next_alloc) {
        // 다음 블록과 연결 가능.
        get_preloc = GET_PRELOC(HDRP(ptr));

        // 다음 블록을 연결 리스트에서 제거
        removeNode(NEXT_BLKP(ptr));

        size += GET_SIZE(HDRP(NEXT_BLKP(ptr)));     // 다음 블록의 크기 더하기
        PUT(HDRP(ptr), PACK(size, get_preloc, 0));              // 현재 블록의 헤더 수정
        PUT(FTRP(ptr), PACK(size, get_preloc, 0));              // 다음 블록의 푸터 수정 (한 블록으로 통합되었음에 유의할 것.)
        
    } else if (!prev_alloc) {
        // 이전 블록과 연결 가능.
        get_preloc = GET_PRELOC(HDRP(PREV_BLKP(ptr)));

        // 이전 블록을 연결 리스트에서 제거
        removeNode(PREV_BLKP(ptr));

        size += GET_SIZE(HDRP(PREV_BLKP(ptr)));     // 이전 블록의 크기 더하기
        PUT(FTRP(ptr), PACK(size, get_preloc, 0));              // 현재 블록의 푸터 수정
        PUT(HDRP(PREV_BLKP(ptr)), PACK(size, get_preloc, 0));   // 이전 블록의 헤더 수정

        ptr = PREV_BLKP(ptr);                       // 통합된 블록으로 주소 갱신
    }
    pushNode(ptr);
    char *next = NEXT_BLKP(ptr);
    PUT(HDRP(next), PACK(GET_SIZE(HDRP(next)), 0, GET_ALLOC(HDRP(next))));
    return ptr;
}

// 분리 가용 리스트에서 first fit 검색을 수행.
// 현재 크기의 가용 리스트부터 탐색. 없으면 다음 크기로.
static void *find_fit(size_t asize){
    void *bp;      // 현재 검색중인 블록
    int min_index = get_index(asize);   // 처음으로 시작할 인덱스

    for (int index = min_index; index < INDEX_COUNT; index++){
        for (bp = heap_heads[index]; bp != NULL; bp = NEXT_NODE(bp)){
            if (asize <= GET_SIZE(HDRP(bp))) return bp;
        }
    }
    return NULL;
}

// 요청한 블록을 가용 블록의 시작에 배치.
// 분할은 나머지 부분의 크기가 최소 블록 크기 이상일 때만 수행.
static void place(void *bp, size_t asize){ 
    size_t curr_size = GET_SIZE(HDRP(bp));
    size_t rest_size = curr_size - asize;
    char get_preloc = GET_PRELOC(HDRP(bp));
    // 현재 블록을 가용 리스트에서 제거

    removeNode(bp);

    if (rest_size >= 4 * WSIZE){
        // 최소 블록 크기 이상인 경우 분할을 수행한다
        // 앞 블록의 헤더
        PUT(HDRP(bp), PACK(asize, get_preloc, 1));
        // 뒷 헤더 만들기
        PUT(HDRP(NEXT_BLKP(bp)), PACK(rest_size, 1, 0));
        // 뒷 블록의 푸터 만들기
        PUT(FTRP(NEXT_BLKP(bp)), PACK(rest_size, 1, 0));
        // 가용 리스트에 뒷 블록 추가
        coalesce(NEXT_BLKP(bp));    
    } else {
        // 최소 블록 크기 이상이 아닌 경우, 분할을 수행하지 않는다
        // 헤더, 푸터 0에서 1로 바꾸기
        PUT(HDRP(bp), PACK(curr_size, get_preloc, 1));
        char *next = NEXT_BLKP(bp);
        PUT(HDRP(next), PACK(GET_SIZE(HDRP(next)), 1, GET_ALLOC(HDRP(next))));
    }
}

static void check_all(){
    char *bp = heap_listp;
    char *llp = headp;
    size_t block_size;
    
    // 에필로그 블록 도달 시 종료
    while (1){
        block_size = GET_SIZE(HDRP(bp));
        if (block_size == 0) break;
        bp = NEXT_BLKP(bp);
    }
    // printf("\n"); 
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 * 최소 size 크기의 메모리 할당 후 포인터를 반환한다.
 * ptr가 NULL -> mm_malloc(size)와 동일.
 * size가 0 -> mm_free(ptr)과 동일.
 * 둘 다 아닌 겨우(정상적인 경우), ptr가 가리키는 메모리 블록의 크기를 size로 바꾸고 새 블록을 반환. 이때 주소는 같을 수도 있고 다를 수도 있음.
 * 블록 내 데이터는 이전 블록의 크기와 이후 블록의 크기 중 최솟값을 기준.
 */

static void *r_split_block(char *bp, size_t totalSize, size_t cutSize){
    char get_preloc = GET_PRELOC(HDRP(bp));
    // 앞 블록의 헤더
    PUT(HDRP(bp), PACK(cutSize, get_preloc, 1));
    // 뒷 헤더 만들기
    PUT(HDRP(NEXT_BLKP(bp)), PACK(totalSize - cutSize, 1, 0));
    // 뒷 블록의 푸터 만들기
    PUT(FTRP(NEXT_BLKP(bp)), PACK(totalSize - cutSize, 1, 0));
    // 가용 리스트에 뒷 블록 추가
    coalesce(NEXT_BLKP(bp));    


    // 앞 블록을 반환
    return bp;    
}

void *mm_realloc(void *bp, size_t size)
{
    if (bp == NULL){
        return mm_malloc(size);
    } else if (size == 0){
        mm_free(bp);
        return NULL;
    }

    // 이전 블록의 크기
    size_t newSize = ALIGN(size + WSIZE);
    size_t oldSize = GET_SIZE(HDRP(bp));
    char get_preloc;


    // 이전 블록의 크기가 큰 경우 -> 자른 뒤 남은 건 free
    if (oldSize >= (4 * WSIZE) + newSize){
        return r_split_block(bp, oldSize, newSize);
    } else if (oldSize >= newSize){

        return bp;
    } else {
        // 새 블록의 크기가 큰 경우
        // 오른쪽 블록이 미할당 + 확장할 만큼 클 때
        char *next = NEXT_BLKP(bp);
        size_t allocSize = oldSize + GET_SIZE(HDRP(next));
        get_preloc = GET_PRELOC(HDRP(bp));
        if (!GET_ALLOC(HDRP(next)) && (allocSize >= newSize)){
            removeNode(next);
            PUT(HDRP(bp), PACK(allocSize, get_preloc, 1));              // 현재 블록의 헤더 수정

            if (allocSize >= newSize + 4 * WSIZE){
                return r_split_block(bp, allocSize, newSize);
            }
            //printf("\n");
            return bp;
        } else {
            char *prev = PREV_BLKP(bp);
            size_t allocSize = GET_SIZE(HDRP(prev)) + oldSize;
            if (!GET_ALLOC(HDRP(prev)) && (allocSize >= newSize)){
                get_preloc = GET_PRELOC(HDRP(prev));
                removeNode(prev);
                PUT(HDRP(prev), PACK(allocSize, get_preloc, 1));   // 이전 블록의 헤더 수정
                memmove(prev, bp, oldSize);

                if (allocSize >= newSize + 4 * WSIZE){
                    return r_split_block(prev, allocSize, newSize);
                }
                return prev;
            } else {
            void *newBp = mm_malloc(size);
            //이전 블록의 내용을 새 블록으로 복사
            memmove(newBp, bp, oldSize);

            // 이전 블록에 할당된 메모리 free
            mm_free(bp);

            return newBp;
        }
    
    }        
    }
}
