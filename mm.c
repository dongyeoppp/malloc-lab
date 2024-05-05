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
    "team 10",
    /* First member's full name */
    "dongyeop ko",
    /* First member's email address */
    "ds06041@gmail.com",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""};

// /* single word (4) or double word (8) alignment */
// #define ALIGNMENT 8

// /* rounds up to the nearest multiple of ALIGNMENT */
// #define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

// #define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/* 기본 상수 및 매크로 */
/* 기본 size 상수를 정의*/
#define WSIZE 4                           // 워드 크기 (bytes)
#define DSIZE 8                           // 더블 워드 (bytes)
#define CHUNKSIZE (1 << 12)               // 초기 가용 블록과 힙 확장을 위한 기본 크기(1 << 12 는 2의 12승 = 4096-> 약 4kb-> 힙을 늘릴 때 약  4kb 분량을 늘린다. )(bytes)
                                          // 1을 이진수로 표기하면 0000 0000 0000 0001 -> 1 << 12(시프트 연산) -> 0001 0000 0000 0000 -> 2^12
#define MAX(x, y) ((x) > (y) ? (x) : (y)) // 삼항 연산자를 활용해 ? 앞에 있는 조건인 x가 더 크다는 조건이 참이면 왼쪽 표현식 반환(x를 반환), 조건이 참이 아니라면 그 다음 표현식 반환(y 반환)

/*하나의 word에 size(메모리 블록의 크기)와 allocated bit (해당 메모리 블록이 할당되었는지 여부를 확인)를 패킹한다. */
#define PACK(size, alloc) ((size) | (alloc)) // 크기와 할당 비트를 통합해서 헤더와 풋터에 저장할 수 있는 값을 리턴한다.

/*메모리 주소 'p'가 가리키는 위치에서 메모리를 읽거나 쓰기*/
#define GET(p) (*(unsigned int *)(p))              // 인자 p가 참조하는 워드를 읽어서 리턴한다. // (unsigned int *)은 주소 'p'를 정수 포인터로 캐스팅하는 것을 의미한다. // unsigned int 자료형은 부호없는 정수를 나타내며 음수값을 허용하지 않는다.
                                                   // 음수를 쓰지 않을 것이므로 같은 공간에 더 많은 양수를 표현할 수 있는 unsigned int를 사용하자
                                                   // 캐스팅이란 변수나 값을 하나의 자료형에서 다른 자료형으로 변환하는 것을 의미한다.  // 인자 p는 대개 (void *) 포인터이며, 이것은 직접적으로 역참조할 수 없다. // 자료형을 변환하여 메모리에 있는 값을 읽거나 쓸 수 있도록 한다.
#define PUT(p, val) (*(unsigned int *)(p) = (val)) // 인자 p가 가리키는 워드에 val을 저장한다.

/* 주소 'p'에서 사이즈와 할당 여부를 읽는 것은 해당 주소에서 워드를 읽고, 그 값을 해석한다.*/
// 각각 주소 p에 있는 헤더 또는 풋터의 size와 할당 비트를 리턴한다.
#define GET_SIZE(p) (GET(p) & ~0x7) // size만 가져오기
#define GET_ALLOC(p) (GET(p) & 0x1) // 가용여부만 가져오기

/* 주어진 블록 포인터 'bp'로부터 해당 블록의 헤더와 풋터의 주소를 계산한다.*/
// bp는 header와 payload 사이의 경계를 가르키고 있다.
#define HDRP(bp) ((char *)(bp) - WSIZE)                      // 블록 헤더를 가리키는 포인터를 리턴한다.     // bp를 한 블록 뒤로 옮기면 bp가 header 블록 앞 경계를 가르키게 된다.
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) // 블록 풋터를 가리키는 포인터를 리턴한다.     // 다음 블록의 header로 bp 이동 (size만큼 뒤로) 이후 더블 워드 만큼 뒤로 가면 footer 블록 앞에 경계로 bp 이동

/* 주어진 블록 포인터 'bp'로부터 다음 블록과 이전 블록의 주소를 계산한다.*/
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE))) // 다음 블록의 포인터 주소를 리턴한다.
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE))) // 이전 블록의 포인터 주소를 리턴한다.

static void *heap_listp = NULL;
static void *last_bp = NULL;
/* 인접한 블록들과 병합하기 */
static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))); // 이전 블록의 footer 정보를 읽어와서 할당여부 저장
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp))); // 다음 블록의 header 정보를 읽어와서 할당여부 저장
    size_t size = GET_SIZE(HDRP(bp));                   // 현재 블록의 header 정보를 읽어와서 size 저장

    if (prev_alloc && next_alloc) // 둘 다 사용중일 경우 (case1)
    {
        return bp; // 현재 블록의 포인터 return
    }
    else if (prev_alloc && !next_alloc) // 다음 블록만 가용블록 (case2)
    {
        size += GET_SIZE(HDRP(NEXT_BLKP(bp))); // 다음 블록의 header정보를 읽어와서 size값 만큼 +
        PUT(HDRP(bp), PACK(size, 0));          // size값 갱신
        PUT(FTRP(bp), PACK(size, 0));          // header 값 갱신 후 footer size 갱신
    }
    else if (!prev_alloc && next_alloc) // 이전 블록만 가용블록 (case3)
    {
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));   // 이전 블록의 header에서 size값 만큼 +
        PUT(FTRP(bp), PACK(size, 0));            // 현재 블록의 footer에 size값 갱신
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0)); // 이전 블록의 header에 size값 갱신
        bp = PREV_BLKP(bp);                      // bp를 이전 블록의 포인터로 변경
    }
    else
    {                                                                          //  이전블록과 다음 볼록이 모두 가용상태일 경우 (case 4)
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp))); // size = 이전블록의 header-> size + 다음 블록의 footer -> size
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));                               // 이전 블록의 header에 size값 갱신
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));                               // 다음 블록의 footer에 size값 갱신
        bp = PREV_BLKP(bp);                                                    // bp를 이전 블록의 포인터로 변경
    }
    last_bp = bp;
    return bp; // 현재 블록의 포인터 return
}

/*할당된 블록 해제하기*/
void mm_free(void *bp)
{
    size_t size = GET_SIZE(HDRP(bp)); // header에 담겨 있는 크기 정보 = size

    PUT(HDRP(bp), PACK(size, 0)); // block header를 업데이트 -> 할당 비트를 0으로
    PUT(FTRP(bp), PACK(size, 0)); // block footer를 업데이트 -> 할당 비트를 0으로
    coalesce(bp);
}

/* 새 가용블록으로 힙 확장하기 */
static void *extend_heap(size_t words)
{
    char *bp;
    size_t size;
    /*만약 words가 홀수라면 한 블록을 추가하여 짝수 개의 words를 할당할 수 있도록 한다.*/
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE; // 주어진 words의 크기를 기준으로 size(새로운 블록의 크기)를 결정한다. // 워드 단위의 정렬을 보장하기 위함
    if ((long)(bp = mem_sbrk(size)) == -1)                    // bp는 mem_sbrk 함수에서 반환한 old_brk를 가지고 있다.
        return NULL;

    PUT(HDRP(bp), PACK(size, 0));         // free block header    // 원래있던 epilogue 블록에 덮어씌여져 새로운 블록의 header가 된다.
    PUT(FTRP(bp), PACK(size, 0));         // free block footer
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); // new epilogue header      // 가장 마지막 블록은 새로운 epilogue가 된다.

    return coalesce(bp); // 이전블록과 다음 블록의 가용상태를 체크하고 통합해준다.
}

// 할당기(힙) 초기화하기(성공이면 0 아니면 -1을 리턴한다.)
int mm_init(void)
{
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1) // mem_sbrk 함수는 memlib.c에서 불러와 사용하고 있다. incur 값이 음수 이거나 mex_heap 범위를 초과하면 -1 return
        return -1;
    PUT(heap_listp, 0);                            // 정렬 요건을 맞추기 위한 1워드(value = 0)(alignment padding)
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); // 다음 블록에 크기(DSIZE=8)와 할당 비트(1)를 통합한 값을 넣는다.(prologue header)
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); // 다음 블록도 동일(prologue footer)
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));     // 다음 블록은 epilogue header를 나타내며 크기는 0이고 할당비트는 1이다.
    heap_listp += (2 * WSIZE);                     // 포인터를 prologue header와 prologue footer 사이에 위치 시킨다.

    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
        return -1;
    return 0;
}

/* 적절한 메모리 블록찾기 (first_fit)*/
// static void *find_fit(size_t asize)
// {
//     void *bp;
//     for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp))   //  bp가 epilogue블록에 도달할때까지 순회
//     {
//         if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp))))     // 들어갈 수 있는 블록이 있으면 바로 해당 bp를 return
//         {
//             return bp;
//         }
//     }
//     return NULL;
// }

/* 적절한 메모리 블록찾기 (next_fit)*/
static void *find_fit(size_t asize) // last_bp는 이전에 탐색을 종료한 위치를 기억한다.
{
    void *bp;
    if (last_bp == NULL) // 이전에 탐색한 적이 없을 경우
    {
        last_bp = heap_listp; // 초기 bp값을 last_bp에 저장
    }
    for (bp = last_bp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) // last_bp에서 시작해서 epilogue블록에 도달할때까지 순회
    {
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) // 가용상태 블록에 size가 들어갈 수 있는 경우
        {
            last_bp = bp; // last_bp갱신
            return bp;
        }
    }
    for (bp = heap_listp; bp != last_bp; bp = NEXT_BLKP(bp)) // epilogue블록까지 할당가능한 블록을 찾지 못했을 경우, 다시 처음부터 last_bp까지 탐색
    {
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) // 가용상태 블록에 size가 들어갈 수 있는 경우
        {
            last_bp = bp; // last_bp 갱신
            return bp;
        }
    }
    return NULL; // 없을 경우 null 반환
}

// /* 적절한 메모리 블록찾기 (best_fit)*/
// static void *find_fit(size_t asize)
// {
//     void *bp;
//     void *best = NULL;

//     for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp))
//     {
//         if (!GET_ALLOC(HDRP(bp)) && GET_SIZE(HDRP(bp)) >= asize)
//         {
//             if (best == NULL)
//             {
//                 best = bp;
//                 continue;
//             }
//             if (GET_SIZE(best) > GET_SIZE(bp))
//             {
//                 best = bp;
//             }
//         }
//     }

//     return best;
// }

// /* 적절한 메모리 블록찾기 (worst_fit)*/
// static void *find_fit(size_t asize)
// {
//     void *bp;
//     void *worst = NULL;

//     for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp))
//     {
//         if (!GET_ALLOC(HDRP(bp)) && GET_SIZE(HDRP(bp)) >= asize)
//         {
//             if (worst == NULL)
//             {
//                 worst = bp;
//                 continue;
//             }
//             if (GET_SIZE(worst) < GET_SIZE(bp))
//             {
//                 worst = bp;
//             }
//         }
//     }

//     return worst;
// }

/* 메모리 블록의 할당 및 분할 */
static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp)); // csize = 현재 bp블록의 사이즈 // chunksize보다 asize가 작을경우 -> csize= chunksize

    if ((csize - asize) >= (2 * DSIZE)) // csize와 asize의 차이가 4개 블럭 이상일경우 (헤더와 풋터를 제외하고 데이터를 저장할 수 있는 공간이 두블럭 이상일 때)
    {
        PUT(HDRP(bp), PACK(asize, 1));
        PUT(FTRP(bp), PACK(asize, 1));
        bp = NEXT_BLKP(bp);                    // 가용블록에 할당이후 다음블록의 포인터로 bp 갱신
        PUT(HDRP(bp), PACK(csize - asize, 0)); // 남은 블록의 size와 할당상태 =0 으로 갱신
        PUT(FTRP(bp), PACK(csize - asize, 0));
        // bp = PREV_BLKP(bp); // 0으로 할당상태 체크헤준이후 다시 사용하고 있는 블록으로 bp 갱신// 인줄 알았지만 함수안에서 bp 변경은 함수를 나가면 반영되지 않아서 필요없는 코드였다.
    }
    else // 현재 블록의 header와 footer 할당상태 1로 변경  , 현재 블록의 사이즈는 csize
    {
        PUT(HDRP(bp), PACK(csize, 1));
        PUT(FTRP(bp), PACK(csize, 1));
    }
}

// bkr 포인터를 증가시켜 블록을 할당한다. 항상 크기가 정렬의 배수인 블록을 할당한다.
void *mm_malloc(size_t size)
{
    size_t asize; // 블록 사이즈 정의
    size_t extendsize;
    char *bp;

    if (size == 0)
        return NULL;

    if (size <= DSIZE)     // size가 8바이트 이하일 경우
        asize = 2 * DSIZE; // 헤더(4byte) + 풋터(4byte) + 정렬 조건을 맞춰주기 위한 패딩 바이트 추가 => asize = 최소 16바이트
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE); // 블록이 가질 수 있는 크기 중에 최적화된 크기로 재조정

    if ((bp = find_fit(asize)) != NULL) // find_fit을 통해 정상적으로 할당이 되었을 경우
    {
        place(bp, asize); // 메모리 할당
        return bp;
    }
    // 적절한 블록을 찾지 못했을 경우
    extendsize = MAX(asize, CHUNKSIZE);                 // 힙을 확장할 때 적어도 asize 보다 큰 블록을 할당할 수 있도록 한다.// asize가 더 작다면 chunksize만큼 공간을 늘리고 asize만큼 남은 부분은 place에서 처리해준다.
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL) // 힙을 정상적으로 늘리지 못했다면 NULL  (bp는 마지막 블록의 )
        return NULL;
    place(bp, asize); // asize만큼 할당하고 남은 공간을 처리한다.

    return bp;
}

/*메모리 재할당*/
//

// void *mm_realloc(void *ptr, size_t size) // ptr은 이전에 할당된 메모리 블록의 포인터, size는 새로운 메모리 블록의 크기
// {
//     void *oldptr = ptr;
//     void *newptr;
//     size_t copySize;

//     newptr = mm_malloc(size); // 힙 확장이 정상적으로 되지 않았을 경우 null을 반환
//     if (newptr == NULL)
//         return NULL;
//     // copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
//     copySize = GET_SIZE(ptr) - DSIZE; // 기존 블록의 사이즈에서 - 8(header와 footer블록의 크기)
//     if (size < copySize)              // 새로 만든 블록보다 이전 블록의 크기가 더 크다면 이전 블록의 size만큼만 복사한다. //
//         copySize = size;
//     memcpy(newptr, oldptr, copySize); // memcpy(복사 받을 메모리를 가리키는 포인터, 복사할 메모리를 가리키는 포인터, 복사할 데이터의 길이)
//     mm_free(oldptr);                  // 새로운 블록에 복사한 이후 이전 블록 할당 해제 (header와 footer의 할당상태를 0으로 바꾸면 나중에 해당 블록을 사용할 수 있다. -> 안에 있는 데이터는 덮어쓰기 된다.)
//     return newptr;
// }




void *mm_realloc(void *ptr, size_t size) // ptr은 이전에 할당된 메모리 블록의 포인터, size는 새로운 메모리 블록의 크기
{
    void *oldptr = ptr; // 현재 블록 포인터
    void *newptr;
    size_t oldsize = GET_SIZE(HDRP(oldptr)); // 현재 블록 사이즈 = oldsize
    if (size + DSIZE <= oldsize)             // 새로 할당하려는 블록사이즈가 현재 블록 사이즈보다 작을 경우
    {
        place(ptr, size + DSIZE); // 현재 블록을 새로 할당하려는 블록 사이즈로 나눠준다.
        return oldptr;
    }
    else if (GET_SIZE(HDRP(NEXT_BLKP(ptr))) != 0 && size > oldsize) // 다음 블록이 epilogue block이 아니고, 재할당할 블록의 사이즈가 현재 블록의 사이즈 보다 클 경우 -> 이전 블록과 다음 블록을 합쳐서 재할당하기
    {
        size_t nextsize = GET_SIZE(HDRP(NEXT_BLKP(oldptr)));            // 다음 블륵의 크기 = nextsize
        size_t addsize = size - oldsize + DSIZE;                        // add size = size와 old size와의 차이(DSIZE는 블록과 헤더 크기)
        if (!GET_ALLOC(HDRP(NEXT_BLKP(oldptr))) && addsize <= nextsize) // 다음 블록이 가용상태이고, 다음블록의 크기가 add 블록의 크기 보다 작은 경우
        {
            if (nextsize - addsize > 2 * DSIZE) // nextsize - addsize 만큼 뺀 값이 16 바이트 이상일 경우 -> 할당할 블록과 가용 블록을 나눠준다.
            {
                PUT(HDRP(oldptr), PACK(addsize + oldsize, 1)); // size만큼 블록 할당하기
                PUT(FTRP(oldptr), PACK(addsize + oldsize, 1));
                PUT(HDRP(NEXT_BLKP(oldptr)), PACK(nextsize - addsize, 0)); // 남음 블록 가용블록으로 만들기 (size만 헤더, 푸터에 넣어주기)
                PUT(FTRP(NEXT_BLKP(oldptr)), PACK(nextsize - addsize, 0));
            }
            else // 조건보다 블록이 작을 경우 나누지 않고 현재블록과 다음 블록을 합쳐준다.
            {
                PUT(HDRP(oldptr), PACK(nextsize + oldsize, 1)); // 할당상태로 만들기
                PUT(FTRP(oldptr), PACK(nextsize + oldsize, 1));
            }
            return oldptr;
        }
    }
    // 다음 블록이 free가 아니거나 현재 블록과 다음 블록의 합보다 size값이 클 경우 힙을 늘려 재할당을 한다.
    newptr = mm_malloc(size);
    if (newptr == NULL)
        return NULL;
    oldsize = GET_SIZE(ptr) - DSIZE;
    if (size < oldsize)
        oldsize = size;
    memcpy(newptr, oldptr, oldsize);
    mm_free(oldptr);
    return newptr;
}
