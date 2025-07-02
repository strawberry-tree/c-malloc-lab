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

/* 정렬단위 바이트 수 8바이트 단위로 정렬 */
#define ALIGNMENT 8

/* 가장 가까운 ALIGNMENT의 배수로 올림 */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~(ALIGNMENT - 1))

/* 기본 매크로 상수 */
#define WSIZE 4                 // 워드, 헤더, 푸터의 크기 (4 바이트)
#define DSIZE 8                 // 더블 워드의 크기 (8 바이트)
#define CHUNKSIZE (1 << 12)     // 힙 연장 시 이만큼 (4096 바이트)

/* 기본 매크로 함수 */
#define MAX(x, y) ((x) > (y)? (x): (y))         // 두 값 중 더 큰 값

// 크기 비트 / 이전블록 할당비트 / 현재블록 할당비트 통합 -> 헤더 저장용
#define PACK(size, preloc, alloc) ((size) | (preloc) << 1 | (alloc))    
// 포인터 p가 참조하는 워드 리턴
#define GET(p) (*(uintptr_t *)(p))         
// 포인터 p가 참조하는 워드에 val을 저장
#define PUT(p, val) (*(uintptr_t *)(p) = (uintptr_t)(val)) 


// 주소 p가 헤더일 때, 저장된 size를 반환
#define GET_SIZE(p) (GET(p) & ~0x7)   
// 주소 p가 헤더일 때, 이전블록 할당비트를 반환
#define GET_PRELOC(p) ((GET(p) >> 1) & 0x1)
// 주소 p가 헤더일 때, 현재블록 할당비트를 반환        
#define GET_ALLOC(p) (GET(p) & 0x1)            

// 블록 주소로, 헤더의 주소 계산
#define HDRP(bp) ((char *)(bp) - 1 * WSIZE)     
// 블록 주소로, prev 주소가 저장된 주소 계산 (bp가 가용 블록일 때만 정상동작)
#define PRVP(bp) ((char *)(bp))
// 블록 주소로, next 주소가 저장된 주소 계산 (bp가 가용 블록일 때만 정상동작)
#define NXTP(bp) ((char *)(bp) + 1 * WSIZE)
// 블록 주소로, 푸터의 주소 계산 (bp가 가용 블록일 때만 정상동작)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - 2 * WSIZE)   

// 다음 블록 주소 계산
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE)))             
// 이전 블록 주소 계산 (이전 블록이 가용 블록일 때만 정상동작)
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - 2 * WSIZE)))   

// 연결 리스트상 이전 가용 블록의 주소 반환
#define PREV_NODE(bp) ((char *)(GET(PRVP(bp))))
// 연결 리스트상 다음 가용 블록의 주소 반환
#define NEXT_NODE(bp) ((char *)(GET(NXTP(bp))))

// 연결 리스트상 이전 가용 블록의 주소 설정
#define SET_PRVP(bp, prev_bp) PUT(PRVP(bp), (uintptr_t)(prev_bp))
// 연결 리스트상 이후 가용 블록의 주소 설정
#define SET_NXTP(bp, next_bp) PUT(NXTP(bp), (uintptr_t)(next_bp))

// 분리 가용 리스트의 수
#define INDEX_COUNT 23

/* 함수 선언 */
static void *extend_heap(size_t);
static void *coalesce(void *);
static void *find_fit(size_t);
static void place(void *, size_t);
static void pushNode(void *newNode);
static void removeNode(void *erase);
static int get_index(size_t);
static void *r_split_block(char *, size_t, size_t);

/* 전역 변수 */
// 각 분리 리스트의 머리 노드를 가리키는 포인터로 구성된 배열
static void *heap_heads[INDEX_COUNT];

// 프롤로그 블록을 가리키는 포인터
static char *heap_listp;                    

/* 함수 정의 */
// 할당할 메모리 크기를 입력받으면, 대응되는 인덱스 반환
static int get_index(size_t size) {
    if (size <= 16) return 0;
    else if (size <= 32) return 1;
    else if (size <= 48) return 2;
    else if (size <= 64) return 3;
    else if (size <= 96) return 4;
    else if (size <= 128) return 5;
    else if (size <= 192) return 6;
    else if (size <= 256) return 7;
    else if (size <= 378) return 8;
    else if (size <= 512) return 9;
    else if (size <= 768) return 10;
    else if (size <= 1024) return 11;
    else if (size <= 2048) return 12;
    else if (size <= 4096) return 13;
    else if (size <= 8192) return 14;
    else if (size <= 16384) return 15;
    else if (size <= 32768) return 16;
    else if (size <= 65536) return 17;
    else if (size <= 131072) return 18;
    else if (size <= 262144) return 19;
    else if (size <= 524288) return 20;
    else if (size <= 1048576) return 21;
    else return 22;
}

/*
 * mm_init - 필요한 초기화 수행 (e.g., 초기 힙 영역을 할당한다)
 */
int mm_init(void)
{

    // heap_heads의 각 원소를 NULL로 초기화
    for (int i = 0; i < INDEX_COUNT; i++){
        heap_heads[i] = NULL;
    }

    // (1) 메모리 시스템에서 4워드(16바이트)를 가져와서, 빈 가용 리스트를 만듦
    heap_listp = (char *)mem_sbrk(4 * WSIZE);
    if (heap_listp == (void *) -1) return -1;   // 메모리 할당에 실패했을 때

    // (2) 16바이트를 채워야 함
    PUT(heap_listp, 0);                                    // (A) 패딩을 위한 4바이트
    PUT(heap_listp + WSIZE, PACK(WSIZE * 2, 1, 1));        // (B) 프롤로그 블록의 헤더 (8 / 1 / 1)
    PUT(heap_listp + WSIZE * 2, 0);                        // (C) 패딩을 위한 4바이트      
    PUT(heap_listp + WSIZE * 3, PACK(0, 1, 1));            // (E) 에필로그 블록의 헤더 (0 / 1 / 1)

    heap_listp += WSIZE * 2;                               // 프롤로그 블록을 가리킴
    return 0;
}

/*
 * extend_heap - 힙이 초기화될 때 OR mm_malloc이 fit을 찾지 못했을 때, 힙을 요청크기 만큼 확장
 */
static void *extend_heap(size_t words){
    size_t size = ALIGN(words * WSIZE);
    char *bp;

    // 메모리 시스템에서 추가공간 요청
    bp = mem_sbrk(size);                        // 새로 할당된 블록의 포인터
    if (bp == (void *) -1) return NULL;         // 메모리 할당에 실패했을 때

    // 이전 에필로그 블록 자리에, 새로운 헤더가 옴
    char get_preloc = GET_PRELOC(HDRP(bp));
    PUT(HDRP(bp), PACK(size, get_preloc, 0));   // 새로운 가용블록의 헤더
    PUT(FTRP(bp), size);                        // 새로운 가용블록의 푸터
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 0, 1));    // 에필로그 블록
    return coalesce(bp);                        // 가용블록 병합

}

/*
 * mm_malloc - 최소 size 바이트의 메모리를 할당한 후, 블록의 시작 주소를 담은 포인터를 반환
 */
void *mm_malloc(size_t size)
{
    size_t asize;       // 실제로 할당되는 블록의 크기
    size_t extendsize;  // fit이 없는 경우 이만큼 힙을 연장
    char *bp;           // 할당받은 블록의 시작 주소를 담는 포인터

    // size == 0인 경우 NULL을 반환
    if (size == 0) return NULL;

    // 입력받은 size에 헤더의 크기를 (4바이트) 포함하고,
    // 인접한 8의 배수로 올려서 실제 할당받을 크기를 구함
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
    if (bp == NULL){
        return NULL;
    } else {
        // 힙 연장 이후 연장된 영역에서 블록 할당
        place(bp, asize);
        return bp;
    }
    
}

/*
 * mm_free - ptr가 가리키는 블록의 메모리 할당을 해제. 반환값 없음
 */
void mm_free(void *ptr)
{
    // 요청한 블록을 반환 -> 할당 비트를 1에서 0으로 전환
    size_t size = GET_SIZE(HDRP(ptr));
    PUT(HDRP(ptr), PACK(size, GET_PRELOC(HDRP(ptr)), 0));
    PUT(FTRP(ptr), size);

    // 인접 가용 블록을 통합
    coalesce(ptr);
}

/*
 * removeNode - 연결 리스트에서 블록 erase를 제거
 */
static void removeNode(void *erase){
    if (erase == NULL) return;

    // 삭제할 블록의 크기를 통해, 알맞는 분리 리스트의 헤드로 이동
    int index = get_index(GET_SIZE(HDRP(erase)));

    void *before = PREV_NODE(erase);
    void *after = NEXT_NODE(erase);

    // 이전 노드와 다음 노드를 연결시킴 (next 포인터 설정)
    if (before == NULL) {
        heap_heads[index] = after;
    } else {
        SET_NXTP(before, after);
    }

    // 이전 노드와 다음 노드를 연결시킴 (prev 포인터 설정)
    if (after != NULL){
        SET_PRVP(after, before);
    }   
    
}

/*
 * pushNode - 연결 리스트의 맨 앞에 노드를 연결.
 */
static void pushNode(void *newNode){
    if (newNode == NULL) return;

    // 삭제할 블록의 크기를 통해, 알맞는 분리 리스트의 헤드로 이동
    int index = get_index(GET_SIZE(HDRP(newNode)));
    
    // newNode는 분리 리스트의 기존 머리 노드를 가리킴
    SET_PRVP(newNode, NULL);
    SET_NXTP(newNode, heap_heads[index]);
    if (heap_heads[index] != NULL){
        SET_PRVP(heap_heads[index], newNode);
    }

    // newNode를 분리 리스트의 머리 노드로 설정
    heap_heads[index] = newNode;
}

/*
 * coalesce -  ptr이 가리키는 블록과 인접 블록을 병합 후, 연결된 블록의 주소 반환
 */
 static void *coalesce(void *ptr){

    // 이전블록 할당비트: 현재블록의 헤더에 저장되어 있음
    size_t prev_alloc = GET_PRELOC(HDRP(ptr));
    // 다음블록 할당비트: 다음블록의 주소 계산 -> 헤더 확인              
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(ptr)));

    size_t size = GET_SIZE(HDRP(ptr));                      // 현재 블록의 크기
    char get_preloc;                                        // 현재 블록의 이전블록할당비트 값 저장
    if (next_alloc && prev_alloc){
        // 병합 불가능, 할 게 없음
    } else if (!next_alloc && prev_alloc) {
        // 다음 블록과 병합
        get_preloc = GET_PRELOC(HDRP(ptr));

        // 다음 블록을 연결 리스트에서 제거
        removeNode(NEXT_BLKP(ptr));

        size += GET_SIZE(HDRP(NEXT_BLKP(ptr)));                 // 다음 블록의 크기 더하기
        PUT(HDRP(ptr), PACK(size, get_preloc, 0));              // 현재 블록의 헤더 수정
        PUT(FTRP(ptr), size);                                   // 다음 블록의 푸터 수정 (한 블록으로 통합되었음에 유의할 것.)
        
    } else if (!prev_alloc && next_alloc) {
        // 이전 블록과 병합
        get_preloc = GET_PRELOC(HDRP(PREV_BLKP(ptr)));

        // 이전 블록을 연결 리스트에서 제거
        removeNode(PREV_BLKP(ptr));

        size += GET_SIZE(HDRP(PREV_BLKP(ptr)));                 // 이전 블록의 크기 더하기
        PUT(FTRP(ptr), size);                                   // 현재 블록의 푸터 수정
        PUT(HDRP(PREV_BLKP(ptr)), PACK(size, get_preloc, 0));   // 이전 블록의 헤더 수정

        ptr = PREV_BLKP(ptr);                                   // 통합된 블록으로 주소 갱신
    } else {
        // 이전, 다음 블록과 병합
        get_preloc = GET_PRELOC(HDRP(PREV_BLKP(ptr)));

        // 이전, 다음 블록을 연결 리스트에서 제거
        removeNode(PREV_BLKP(ptr));
        removeNode(NEXT_BLKP(ptr));

        // 이전, 다음 블록의 크기 더하기
        size += GET_SIZE(HDRP(PREV_BLKP(ptr))) + GET_SIZE(HDRP(NEXT_BLKP(ptr)));                 
        PUT(HDRP(PREV_BLKP(ptr)), PACK(size, get_preloc, 0));   // 이전 블록의 헤더 수정
        PUT(FTRP(NEXT_BLKP(ptr)), size);                        // 다음 블록의 푸터 수정
        ptr = PREV_BLKP(ptr);                                   // 통합된 블록으로 주소 갱신
    }
    pushNode(ptr);                                              // 통합된 블록을 연결 리스트에 추가
    
    // 블록을 반환한 후, 다음 블록의 이전할당비트를 0으로 갱신
    char *next = NEXT_BLKP(ptr);
    PUT(HDRP(next), PACK(GET_SIZE(HDRP(next)), 0, GET_ALLOC(HDRP(next))));
    return ptr;
}

/*
 * find_fit: 분리 가용 리스트에서 할당할 블록을 검색
*/

static void *find_fit(size_t asize){
    void *bp;                           // 현재 검색중인 블록
    int min_index = get_index(asize);   // 검색을 시작할 분리 리스트

    if (asize <= 1024){
        // 크기가 1024 이하일 시 First Fit
        for (int index = min_index; index < INDEX_COUNT; index++){
            for (bp = heap_heads[index]; bp != NULL; bp = NEXT_NODE(bp)){
                // First Fit을 찾자마자 바로 Return
                if (asize <= GET_SIZE(HDRP(bp))) return bp;
                }
            }
        return NULL;
    } else {
        // 크기가 1024 초과일 시 Best Fit
        size_t min_diff = SIZE_MAX;         // 블록사이즈 - asize의 최솟값
        size_t block_size;                  // 현재 블록의 크기
        void *result = NULL;                // Best Fit으로 찾은 블록의 주소
        for (int index = min_index; index < INDEX_COUNT; index++){
            // 현재 분리 리스트의 모든 노드 탐색하며 Best Fit 찾음
            for (bp = heap_heads[index]; bp != NULL; bp = NEXT_NODE(bp)){
                block_size = GET_SIZE(HDRP(bp));
                if ((asize <= block_size) && (block_size - asize < min_diff) ){
                    result = bp;
                    min_diff = block_size - asize;
                }
            }
            // 현재 분리 리스트에 Best Fit이 존재하는 경우, 다음 리스트로 안 넘어가고 종료
            // 존재하지 않으면 result는 NULL이므로 다음 리스트로 넘어감
            if (result != NULL) return result;
        }
        return NULL;
    }
}

/*
 * r_split_block: totalSize 크기의 블록을, cutSize의 할당 블록과 나머지 크기의 가용 블록으로 자르고, 할당 블록을 반환
*/
static void *r_split_block(char *bp, size_t totalSize, size_t cutSize){
    char get_preloc = GET_PRELOC(HDRP(bp));
    // 앞 블록의 헤더
    PUT(HDRP(bp), PACK(cutSize, get_preloc, 1));
    // 뒷 헤더 만들기
    PUT(HDRP(NEXT_BLKP(bp)), PACK(totalSize - cutSize, 1, 0));
    // 뒷 블록의 푸터 만들기
    PUT(FTRP(NEXT_BLKP(bp)), totalSize - cutSize);
    // 가용 리스트에 뒷 블록 추가
    coalesce(NEXT_BLKP(bp));    

    // 앞 블록을 반환
    return bp;    
}

/*
 * place - 요청한 블록을 가용 블록의 시작에 배치하고, 필요에 따라 분할.
*/
// 요청한 블록을 가용 블록의 시작에 배치.
static void place(void *bp, size_t asize){ 
    size_t curr_size = GET_SIZE(HDRP(bp));
    size_t rest_size = curr_size - asize;
    char get_preloc = GET_PRELOC(HDRP(bp));
    // 현재 블록을 가용 리스트에서 제거

    removeNode(bp);

    if (rest_size >= 4 * WSIZE){
        // 최소 블록 크기 이상인 경우 분할을 수행한다 
        r_split_block(bp, curr_size, asize);
    } else {
        // 최소 블록 크기 이상이 아닌 경우, 분할을 수행하지 않는다
        // 헤더 1로 바꾸기
        PUT(HDRP(bp), PACK(curr_size, get_preloc, 1));
        char *next = NEXT_BLKP(bp);
        // 블록을 할당하고, 다음 블록의 이전 할당비트를 1로 갱신
        PUT(HDRP(next), PACK(GET_SIZE(HDRP(next)), 1, GET_ALLOC(HDRP(next))));
    }
}

/*
 * mm_realloc - 최소 size 크기의 메모리 할당 후 포인터를 반환.
 * ptr가 NULL -> mm_malloc(size)와 동일.
 * size가 0 -> mm_free(ptr)과 동일.
 * 둘 다 아닌 경우, ptr가 가리키는 메모리 블록의 크기를 size로 바꾸고 새 블록을 반환..
 */

void *mm_realloc(void *bp, size_t size)
{
    if (bp == NULL){
        return mm_malloc(size);
    } else if (size == 0){
        mm_free(bp);
        return NULL;
    }

    size_t newSize = ALIGN(size + WSIZE);   // 새로 할당할 메모리 크기
    size_t oldSize = GET_SIZE(HDRP(bp));    // 기본 블록의 메모리 크기
    char get_preloc;


    
    if (oldSize >= (4 * WSIZE) + newSize){
        // 기존 블록의 크기가 큰 경우 -> 자른 뒤 남은 건 free
        return r_split_block(bp, oldSize, newSize);
    } else if (oldSize >= newSize){
        // 단, 자를 때 남은 블록의 크기가 최소 블록크기보다 작은 경우, 기존 블록을 유지
        return bp;
    } else {
        // 새로 할당할 블록의 크기가 큰 경우
        char *next = NEXT_BLKP(bp);
        size_t allocSize = oldSize + GET_SIZE(HDRP(next));
        get_preloc = GET_PRELOC(HDRP(bp));
        if (!GET_ALLOC(HDRP(next)) && (allocSize >= newSize)){
            // (1) 다음 블록이 가용 블록이며
            // (2) (현재 블록 크기 + 다음 블록 크기) >= (새로 할당할 크기)일 때
            // 다음 블록을 병합해 할당 후, 필요에 따라 자름
            removeNode(next);                                           // 다음 블록을 가용 리스트에서 제거
            PUT(HDRP(bp), PACK(allocSize, get_preloc, 1));              // 병합된 블록의 헤더 수정

            
            if (allocSize >= newSize + 4 * WSIZE){
                // 최소 블록크기 이상이 남는 경우 자름 
                return r_split_block(bp, allocSize, newSize);
            } else {
                // 최소 블록크기만큼 남지 않는 경우, 자르지 않음
                next = NEXT_BLKP(bp);
                // 블록을 할당하고, 다음 블록의 이전 할당비트를 1로 갱신
                PUT(HDRP(next), PACK(GET_SIZE(HDRP(next)), 1, GET_ALLOC(HDRP(next))));
            }
            return bp;
        } else {
            // 새로운 블록 할당
            void *newBp = mm_malloc(size);
            // 이전 블록의 내용을 새 블록으로 복사
            memcpy(newBp, bp, oldSize - WSIZE);
            // 이전 블록에 할당된 메모리 free
            mm_free(bp);
            // 새로운 블록 주소 반환
            return newBp;
        }
    }        
}
