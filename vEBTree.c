#include <stdio.h>
#include <stdlib.h>
#include <math.h>

// van Emde Boas (vEB) Tree implementation in C/C++
// If compiled as C++, explicit casts on malloc/calloc are required

typedef struct vEBNode {
    int u;                 // universe size
    int min, max;          // minimum and maximum values in the tree
    struct vEBNode* summary;
    struct vEBNode** cluster;
    int lower_sqrt;
    int upper_sqrt;
} vEBNode;

// Helper: compute integer log2 (U must be power of two)
static int log2_int(int x) {
    return (int)round(log2(x));
}

// Create a new vEB tree of size U (must be power of two ≥2)
// Exits on invalid U or memory allocation failure
vEBNode* vEB_create(int U) {
    if (U < 2) {
        fprintf(stderr, "Error: U=%d must be ≥ 2\n", U);
        exit(EXIT_FAILURE);
    }
    if ((U & (U - 1)) != 0) {
        fprintf(stderr, "Error: U=%d must be a power of two\n", U);
        exit(EXIT_FAILURE);
    }

    // allocate node (with explicit cast for C++)
    vEBNode* V = (vEBNode*)malloc(sizeof(vEBNode));
    if (!V) {
        perror("malloc vEBNode");
        exit(EXIT_FAILURE);
    }
    V->u = U;
    V->min = V->max = -1;

    if (U <= 2) {
        V->summary = NULL;
        V->cluster = NULL;
        V->lower_sqrt = V->upper_sqrt = 0;
    }
    else {
        int lg = log2_int(U);
        int half = lg / 2;
        V->lower_sqrt = 1 << half;
        V->upper_sqrt = 1 << (lg - half);

        // create summary recursively
        V->summary = vEB_create(V->upper_sqrt);
        if (!V->summary) {
            fprintf(stderr, "Failed to create summary (U=%d)\n", V->upper_sqrt);
            exit(EXIT_FAILURE);
        }

        // allocate cluster pointer array (explicit cast for C++)
        V->cluster = (vEBNode**)calloc(V->upper_sqrt, sizeof(vEBNode*));
        if (!V->cluster) {
            perror("calloc cluster array");
            exit(EXIT_FAILURE);
        }

        // eager-init each cluster
        for (int i = 0; i < V->upper_sqrt; i++) {
            V->cluster[i] = vEB_create(V->lower_sqrt);
            if (!V->cluster[i]) {
                fprintf(stderr, "Failed to create cluster[%d] (U=%d)\n", i, V->lower_sqrt);
                exit(EXIT_FAILURE);
            }
        }
    }
    return V;
}

// Helpers to split/join keys
static int high(vEBNode* V, int x) { return x / V->lower_sqrt; }
static int low(vEBNode* V, int x) { return x % V->lower_sqrt; }
static int idx(vEBNode* V, int h, int l) { return h * V->lower_sqrt + l; }

// Insert into empty tree
void vEB_empty_insert(vEBNode* V, int x) {
    V->min = V->max = x;
}

// MEMBER (find)
int vEB_member(vEBNode* V, int x) {
    if (!V) return 0;
    if (x == V->min || x == V->max) return 1;
    if (V->u <= 2) return 0;
    return vEB_member(V->cluster[high(V, x)], low(V, x));
}

// INSERT
void vEB_insert(vEBNode* V, int x) {
    if (x < 0 || x >= V->u) {
        fprintf(stderr, "Error: Value %d out of bounds (U = %d)\n", x, V->u);
        return;
    }

    if (vEB_member(V, x)) return; // 이미 있으면 삽입하지 않음

    if (V->min == -1) {
        vEB_empty_insert(V, x);
        return;
    }
    if (x < V->min) {
        int tmp = x; x = V->min; V->min = tmp;
    }
    if (V->u > 2) {
        int h = high(V, x), l = low(V, x);
        if (V->cluster[h]->min == -1) {
            vEB_insert(V->summary, h);
            vEB_empty_insert(V->cluster[h], l);
        }
        else {
            vEB_insert(V->cluster[h], l);
        }
    }
    if (x > V->max) V->max = x;
}

// SUCCESSOR / PREDECESSOR helpers
static int vEB_min(vEBNode* V) { return V->min; }
static int vEB_max(vEBNode* V) { return V->max; }

// SUCCESSOR
int vEB_successor(vEBNode* V, int x) {
    if (V->u <= 2) {
        if (x == 0 && V->max == 1) return 1;
        return -1;
    }
    if (V->min != -1 && x < V->min) return V->min;
    int h = high(V, x), l = low(V, x);
    int max_low = vEB_max(V->cluster[h]);
    if (max_low != -1 && l < max_low) {
        int off = vEB_successor(V->cluster[h], l);
        return idx(V, h, off);
    }
    int succ_c = vEB_successor(V->summary, h);
    if (succ_c == -1) return -1;
    int off = vEB_min(V->cluster[succ_c]);
    return idx(V, succ_c, off);
}

// PREDECESSOR
int vEB_predecessor(vEBNode* V, int x) {
    if (V->u <= 2) {
        if (x == 1 && V->min == 0) return 0;
        return -1;
    }
    if (V->max != -1 && x > V->max) return V->max;
    int h = high(V, x), l = low(V, x);
    int min_low = vEB_min(V->cluster[h]);
    if (min_low != -1 && l > min_low) {
        int off = vEB_predecessor(V->cluster[h], l);
        return idx(V, h, off);
    }
    int pred_c = vEB_predecessor(V->summary, h);
    if (pred_c == -1) {
        if (V->min != -1 && x > V->min) return V->min;
        return -1;
    }
    int off = vEB_max(V->cluster[pred_c]);
    return idx(V, pred_c, off);
}

// DELETE
void vEB_delete(vEBNode* V, int x) {

    if (x < 0 || x >= V->u) {
        fprintf(stderr, "Error: Value %d out of bounds (U = %d)\n", x, V->u);
        return;
    }

    if (V->min == V->max) {
        V->min = V->max = -1;
        return;
    }
    if (V->u == 2) {
        V->min = V->max = (x == 0) ? 1 : 0;
        return;
    }
    if (x == V->min) {
        int first = vEB_min(V->summary);
        int off = vEB_min(V->cluster[first]);
        x = idx(V, first, off);
        V->min = x;
    }
    int h = high(V, x), l = low(V, x);
    vEB_delete(V->cluster[h], l);
    if (vEB_min(V->cluster[h]) == -1) {
        vEB_delete(V->summary, h);
        if (x == V->max) {
            int smax = vEB_max(V->summary);
            V->max = (smax == -1) ? V->min : idx(V, smax, vEB_max(V->cluster[smax]));
        }
    }
    else if (x == V->max) {
        V->max = idx(V, h, vEB_max(V->cluster[h]));
    }
}

// FREE
void vEB_free(vEBNode* V) {
    if (!V) return;

    if (V->cluster) {
        for (int i = 0; i < V->upper_sqrt; i++) {
            vEB_free(V->cluster[i]);
        }
        free(V->cluster);
    }

    vEB_free(V->summary);
    free(V);
}
// 빈 트리 상태에서 작업: 트리가 비어있을 때, 다양한 연산이 잘 동작하는지 확인
void testcase_empty_tree() {
    vEBNode* tree = vEB_create(16);

    // 빈 트리에서 Member 테스트 (값이 트리에 존재하지 않으면 0 반환)
    printf("Empty tree: Member 5? %d\n", vEB_member(tree, 5)); // 0
    // 빈 트리에서 Successor 테스트 (값이 없으면 -1 반환)
    printf("Empty tree: Successor of 5? %d\n", vEB_successor(tree, 5)); // -1
    // 빈 트리에서 Predecessor 테스트 (값이 없으면 -1 반환)
    printf("Empty tree: Predecessor of 5? %d\n", vEB_predecessor(tree, 5)); // -1
    vEB_free(tree);
}

// U=2인 트리에서 다양한 조작: `U=2`인 트리에서 삽입, 삭제, 후속 및 전임자 테스트
void testcase_u2_edge() {
    vEBNode* tree = vEB_create(2);

    // 0만 삽입 후 0 존재 여부 체크
    vEB_insert(tree, 0);
    printf("Member 0? %d\n", vEB_member(tree, 0)); // 1
    // 1은 트리에 존재하지 않음
    printf("Member 1? %d\n", vEB_member(tree, 1)); // 0

    // 1 삽입 후 Successor와 Predecessor 테스트
    vEB_insert(tree, 1);
    printf("Successor of 0: %d\n", vEB_successor(tree, 0)); // 1
    printf("Predecessor of 1: %d\n", vEB_predecessor(tree, 1)); // 0

    // 1 삭제 후 존재 여부 확인
    vEB_delete(tree, 1);
    printf("Member 1 after delete: %d\n", vEB_member(tree, 1)); // 0

    // 0 삭제 후 트리가 비어있는지 확인
    vEB_delete(tree, 0);
    printf("Empty tree: Min: %d, Max: %d\n", tree->min, tree->max); // -1, -1
    vEB_free(tree);
}

// 가장 큰/작은 값 삭제 후 동작: 최소값 및 최대값을 삭제한 후 트리가 정상적으로 동작하는지 확인
void testcase_min_max_delete() {
    vEBNode* tree = vEB_create(16);

    // 값 삽입
    vEB_insert(tree, 1);
    vEB_insert(tree, 5);
    vEB_insert(tree, 10);
    vEB_insert(tree, 15);

    // 최소값과 최대값이 정상적으로 삽입되었는지 확인
    printf("Min: %d, Max: %d\n", tree->min, tree->max); // 1, 15

    // 최소값 삭제 후 확인
    vEB_delete(tree, 1);
    printf("After deleting min (1), Min: %d\n", tree->min); // 5

    // 최대값 삭제 후 확인
    vEB_delete(tree, 15);
    printf("After deleting max (15), Max: %d\n", tree->max); // 10
    vEB_free(tree);
}

// 값의 범위가 매우 큰 트리: U 값이 매우 클 때 트리의 동작 및 메모리 할당을 확인
void testcase_large_universe() {
    int U = 1024; // 큰 트리 크기 설정
    vEBNode* tree = vEB_create(U);

    // 여러 값 삽입 후 Member 테스트
    vEB_insert(tree, 100);
    vEB_insert(tree, 500);
    vEB_insert(tree, 900);
    printf("Member 100: %d\n", vEB_member(tree, 100)); // 1
    printf("Member 500: %d\n", vEB_member(tree, 500)); // 1
    printf("Member 900: %d\n", vEB_member(tree, 900)); // 1

    // Successor 및 Predecessor 테스트
    printf("Successor of 100: %d\n", vEB_successor(tree, 100)); // 500
    printf("Predecessor of 500: %d\n", vEB_predecessor(tree, 500)); // 100
    vEB_free(tree);
}

// 완전한 트리 구조에서의 성능 테스트: 트리의 모든 값을 삽입하고, 후속 및 전임자 테스트를 통해 트리 동작 확인
void testcase_full_tree() {
    vEBNode* tree = vEB_create(16);

    // 0부터 15까지 모든 값 삽입
    for (int i = 0; i < 16; i++) {
        vEB_insert(tree, i);
    }
    // 최소값과 최대값 확인
    printf("Min after full insert: %d\n", vEB_min(tree)); // 0
    printf("Max after full insert: %d\n", vEB_max(tree)); // 15

    // Successor 및 Predecessor 테스트
    for (int i = 0; i < 15; i++) {
        printf("Successor of %d: %d\n", i, vEB_successor(tree, i)); // i+1
        printf("Predecessor of %d: %d\n", i + 1, vEB_predecessor(tree, i + 1)); // i
    }
    vEB_free(tree);
}

// 잘못된 입력 값 처리: `U` 값이 1이거나 2의 거듭제곱이 아닌 경우 에러가 발생하는지 확인
void testcase_invalid_U() {
    printf("Creating tree with U=1 (invalid case):\n");
    vEBNode* tree = vEB_create(1); // U=1은 유효하지 않음, 에러 발생
    vEB_free(tree);
}

// 빈 트리에서 삭제 연산 테스트: 빈 트리에서 delete 연산이 정상적으로 동작하는지 확인
void testcase_empty_tree_delete() {
    vEBNode* tree = vEB_create(16);

    // 빈 트리에서 삭제 연산을 실행
    printf("Delete in empty tree:\n");
    vEB_delete(tree, 5);  // 삭제 연산이 잘 동작하는지 확인
    printf("After delete: Min: %d, Max: %d\n", tree->min, tree->max); // -1, -1
    vEB_free(tree);
}

// 연속된 삽입 및 삭제 테스트: 삽입과 삭제를 반복하여 트리의 동작을 확인
void testcase_insert_delete_sequence() {
    vEBNode* tree = vEB_create(16);

    // 삽입 후 삭제를 반복적으로 수행
    for (int i = 0; i < 10; i++) {
        vEB_insert(tree, i);
        printf("Inserted: %d, Min: %d, Max: %d\n", i, tree->min, tree->max);
    }
    // 삭제
    for (int i = 0; i < 5; i++) {
        vEB_delete(tree, i);
        printf("Deleted: %d, Min: %d, Max: %d\n", i, tree->min, tree->max);
    }
    vEB_free(tree);
}

// 최소값과 최대값을 여러 번 삭제 후 트리의 상태를 확인
void testcase_multiple_min_max_deletion() {
    vEBNode* tree = vEB_create(16);

    // 여러 값 삽입
    vEB_insert(tree, 1);
    vEB_insert(tree, 5);
    vEB_insert(tree, 10);
    vEB_insert(tree, 15);

    printf("Before deletion - Min: %d, Max: %d\n", tree->min, tree->max); // 1, 15

    // 최소값 삭제
    vEB_delete(tree, 1);
    printf("After deleting Min (1): Min: %d, Max: %d\n", tree->min, tree->max); // 5, 15

    // 최대값 삭제
    vEB_delete(tree, 15);
    printf("After deleting Max (15): Min: %d, Max: %d\n", tree->min, tree->max); // 5, 10

    // 최대값 다시 삭제
    vEB_delete(tree, 10);
    printf("After deleting Max (10): Min: %d, Max: %d\n", tree->min, tree->max); // 5, 5

    // 마지막 값 삭제 후 확인
    vEB_delete(tree, 5);
    printf("After deleting last value: Min: %d, Max: %d\n", tree->min, tree->max); // -1, -1
    vEB_free(tree);
}

// U=4인 경우에 대한 테스트: 중간 크기 트리에서 동작 확인
void testcase_u4() {
    vEBNode* tree = vEB_create(4);

    // 값 삽입
    vEB_insert(tree, 0);
    vEB_insert(tree, 3);
    printf("Member 0: %d\n", vEB_member(tree, 0)); // 1
    printf("Member 3: %d\n", vEB_member(tree, 3)); // 1

    // Successor와 Predecessor 테스트
    printf("Successor of 0: %d\n", vEB_successor(tree, 0)); // 3
    printf("Predecessor of 3: %d\n", vEB_predecessor(tree, 3)); // 0

    // 삭제
    vEB_delete(tree, 3);
    printf("Member 3 after delete: %d\n", vEB_member(tree, 3)); // 0

    // 마지막 값 삭제 후 트리가 비어있는지 확인
    vEB_delete(tree, 0);
    printf("After deleting last value: Min: %d, Max: %d\n", tree->min, tree->max); // -1, -1
    vEB_free(tree);
}

// summary와 cluster 동작 테스트: summary와 cluster가 올바르게 작동하는지 확인
void testcase_summary_cluster() {
    vEBNode* tree = vEB_create(16);

    // 여러 값 삽입
    vEB_insert(tree, 2);
    vEB_insert(tree, 5);
    vEB_insert(tree, 9);
    vEB_insert(tree, 12);

    printf("Min: %d, Max: %d\n", tree->min, tree->max); // 2, 12
    // summary와 cluster의 동작을 의도한 대로 확인
    printf("Summary Min: %d\n", tree->summary->min); // 0 또는 1

    // 삽입 및 삭제 후 상태 확인
    vEB_insert(tree, 15);
    vEB_delete(tree, 5);
    printf("After insert 15 and delete 5, Min: %d, Max: %d\n", tree->min, tree->max); // 2, 15

    vEB_free(tree);
}

// 트리의 메모리 해제 및 리소스 관리: 트리 사용 후 메모리가 정상적으로 해제되는지 확인
void testcase_memory_leak() {
    vEBNode* tree = vEB_create(16);

    // 값 삽입
    vEB_insert(tree, 1);
    vEB_insert(tree, 3);
    vEB_insert(tree, 7);
    printf("Before deleting: Min: %d, Max: %d\n", tree->min, tree->max); // 1, 7

    // 삭제 후 메모리 해제
    vEB_delete(tree, 1);
    vEB_delete(tree, 3);
    vEB_delete(tree, 7);

    // 트리 메모리 해제 후 상태
    vEB_free(tree);  // 실제로 트리의 메모리가 해제되었는지 확인
    printf("After deleting all values, Memory should be free.\n");
}

// U가 2의 거듭제곱이 아닌 경우에 대한 테스트
void testcase_non_power_of_two_U() {
    printf("Creating tree with U=6 (non-power-of-two case):\n");
    vEBNode* tree = vEB_create(6); // U=6은 유효하지 않음, 에러가 발생할 것으로 예상됨

    vEB_free(tree);
}

// x 값이 트리의 범위를 초과하는 경우
void testcase_out_of_bounds() {
    vEBNode* tree = vEB_create(16);
    vEB_insert(tree, 16);  // 잘못된 삽입 (범위 초과)
    vEB_insert(tree, -1);  // 잘못된 삽입 (음수)
    vEB_delete(tree, 20);  // 잘못된 삭제

    vEB_free(tree);
}

// 트리 크기가 커질 때 성능 테스트
void testcase_large_tree_performance() {
    int U = 1024; // 큰 트리 크기 설정
    vEBNode* tree = vEB_create(U);

    // 여러 값 삽입
    for (int i = 0; i < 100; i++) {
        vEB_insert(tree, i);
    }

    // 트리에서 값 검색
    for (int i = 0; i < 100; i++) {
        printf("Member %d: %d\n", i, vEB_member(tree, i)); // 1
    }

    vEB_free(tree);
}

// 특정 값에 대한 연속된 Insert, Delete 동작 테스트
void testcase_insert_delete_duplicates() {
    vEBNode* tree = vEB_create(16);

    // 중복 값 삽입
    vEB_insert(tree, 5);
    vEB_insert(tree, 5);
    vEB_insert(tree, 5);

    // 삽입 후 확인
    printf("After inserting 5 three times: Member 5? %d\n", vEB_member(tree, 5)); // 1

    // 삭제 후 확인
    vEB_delete(tree, 5);
    printf("After deleting 5: Member 5? %d\n", vEB_member(tree, 5)); // 0

    vEB_free(tree);
}

// 최소값과 최대값 경계 처리 테스트
void testcase_min_max_boundary() {
    vEBNode* tree = vEB_create(16);

    // 0과 15를 동시에 삽입
    vEB_insert(tree, 0);
    vEB_insert(tree, 15);

    // 트리의 최소값과 최대값 확인
    printf("Min: %d, Max: %d\n", tree->min, tree->max); // 0, 15

    // 삽입된 값에 대해 Successor, Predecessor 테스트
    printf("Successor of 0: %d\n", vEB_successor(tree, 0)); // 15
    printf("Predecessor of 15: %d\n", vEB_predecessor(tree, 15)); // 0

    vEB_free(tree);
}

// 연속된 Insert, Delete 후 트리 상태 확인
void testcase_insert_delete_sequence_state() {
    vEBNode* tree = vEB_create(16);

    // 값 삽입
    for (int i = 0; i < 10; i++) {
        vEB_insert(tree, i);
        printf("Inserted %d, Min: %d, Max: %d\n", i, tree->min, tree->max);
    }

    // 값 삭제
    for (int i = 0; i < 5; i++) {
        vEB_delete(tree, i);
        printf("Deleted %d, Min: %d, Max: %d\n", i, tree->min, tree->max);
    }

    vEB_free(tree);
}

// Example usage
int main() {
    printf("\n======== testcase empty tree ========\n\n");
    testcase_empty_tree();
    printf("\n======== testcase U2 edge ========\n\n");
    testcase_u2_edge();
    printf("\n======== testcase min max delete ========\n\n");
    testcase_min_max_delete();
    printf("\n======== testcase large universe ========\n\n");
    testcase_large_universe();
    printf("\n======== testcase full tree ========\n\n");
    testcase_full_tree();
    //printf("\n======== testcase invalid u ========\n\n");
    //testcase_invalid_U();
    printf("\n======== testcase empty tree delete ========\n\n");
    testcase_empty_tree_delete();
    printf("\n======== testcase insert delete sequenece ========\n\n");
    testcase_insert_delete_sequence();
    printf("\n======== testcase min max deletion ========\n\n");
    testcase_multiple_min_max_deletion();
    printf("\n======== testcase U4 ========\n\n");
    testcase_u4();
    printf("\n======== testcase summary cluster ========\n\n");
    testcase_summary_cluster();
    printf("\n======== testcase memory leak ========\n\n");
    testcase_memory_leak();
    //printf("\n======== testcase non power of two U ========\n\n");
    //testcase_non_power_of_two_U();
    printf("\n======== testcase out of bounds ========\n\n");
    testcase_out_of_bounds();
    printf("\n======== testcase large tree performance ========\n\n");
    testcase_large_tree_performance();
    printf("\n======== testcase insert delete duplication ========\n\n");
    testcase_insert_delete_duplicates();
    printf("\n======== testcase min max boundary ========\n\n");
    testcase_min_max_boundary();
    printf("\n======== testcase insert delete sequence state ========\n\n");
    testcase_insert_delete_sequence_state();

    return 0;
}
