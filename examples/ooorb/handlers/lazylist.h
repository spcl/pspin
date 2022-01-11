#ifndef __LAZYLIST_H__
#define __LAZYLIST_H__

#include <stdint.h>

#include <stdio.h>
#include <stdlib.h>
/*
Properties assumed:
  - no overlaps

*/


//#define USE_LRSC

#define NUM_SEGMENTS 128
#define EOL ((uint32_t) -1)
#define RANGE_START_ANY ((uint32_t) -1)
#define GET_NODE_PTR(list, idx) (&(list->nodes[idx]))
#define IS_NODE_MARKED(list, idx) (list->marks[idx])

#define S_ASSERT(X) { if (!(X)) { printf("Assert " #X " failed!\n");}}

typedef struct lazylist_range
{
    int32_t left;
    int32_t right;
} lazylist_range_t;

typedef struct lazylist_node
{
    uint32_t idx; // this can be optimized for space (pointer subtraction)
    lazylist_range_t range;
    volatile spin_lock_t lock;
    volatile uint32_t next_idx;
} lazylist_node_t;

typedef struct lazylist
{
    uint32_t head_idx;
    uint32_t free_head_idx;
#ifndef USE_LRSC
    volatile uint32_t free_head_lock;
#endif
    lazylist_node_t nodes[NUM_SEGMENTS + 2];
    uint8_t marks[NUM_SEGMENTS];
} lazylist_t;

void lazylist_init(lazylist_t *list, uint32_t capacity)
{
    uint32_t num_actual_nodes = capacity - 2; //account for sentinels

    for (uint32_t i = 0; i < num_actual_nodes; i++)
    {
        list->nodes[i].idx = i;
        list->nodes[i].next_idx = i + 1;
        list->marks[i] = 0;
        list->nodes[i].lock = 0;
    }

    // here it's EOL because this is now the free list and there are no sentinels
    list->nodes[num_actual_nodes - 1].next_idx = EOL;

    lazylist_node_t *sentinel_left = &(list->nodes[num_actual_nodes]);
    lazylist_node_t *sentinel_right = &(list->nodes[num_actual_nodes + 1]);

    sentinel_left->idx = num_actual_nodes;
    sentinel_left->lock = 0;
    sentinel_left->next_idx = num_actual_nodes + 1;
    sentinel_left->range.left = INT32_MIN;
    sentinel_left->range.right = INT32_MIN;

    sentinel_right->idx = num_actual_nodes + 1;
    sentinel_right->lock = 0;
    sentinel_right->next_idx = EOL;
    sentinel_right->range.left = INT32_MAX;
    sentinel_right->range.right = INT32_MAX;

    list->head_idx = sentinel_left->idx;
    list->free_head_idx = 0;

#ifndef USE_LRSC
    list->free_head_lock = 0;
#endif
}

/*
Return values:
 - 0: no space
 - >0: success
 */
uint32_t lazylist_get_free_node(lazylist_t *list, lazylist_node_t **free_node)
{
#ifdef USE_LRSC
    uint32_t sc_success;
    uint32_t curr_free_idx;
    do
    {
        curr_free_idx = (uint32_t)load_reserved((volatile uint32_t*) &list->free_head_idx);
        if (curr_free_idx == EOL)
        {
            return 0;
        }
        uint32_t next_free_idx = list->nodes[curr_free_idx].next_idx;
        sc_success = store_conditional((volatile uint32_t*) &list->free_head_idx, (uint32_t) next_free_idx);
    } while (sc_success != 0);

    *free_node = GET_NODE_PTR(list, curr_free_idx);

    return 1;
#else
    uint32_t res = 0;
    spin_lock_lock(&list->free_head_lock);
    if (list->free_head_lock != EOL)
    {
        res = 1;
        *free_node = GET_NODE_PTR(list, list->free_head_idx);
        list->free_head_idx = (*free_node)->next_idx;
    }
    spin_lock_unlock(&list->free_head_lock);

    return res;
#endif
}

/*
Return values:
 - >0: success
 */
uint32_t lazylist_put_free_node(lazylist_t *list, lazylist_node_t *freed_node)
{
#ifdef USE_LRSC
    uint32_t sc_success;
    do
    {
        uint32_t curr_free_idx = (uint32_t) load_reserved((volatile uint32_t*) &list->free_head_idx);
        freed_node->next_idx = curr_free_idx;
        sc_success = store_conditional((volatile uint32_t*) &list->free_head_idx, (uint32_t) freed_node->idx);
    } while (sc_success != 0);

    return 1;
#else
    spin_lock_lock(&list->free_head_lock);

    freed_node->next_idx = list->free_head_idx;
    list->free_head_idx = freed_node->idx;

    spin_lock_unlock(&list->free_head_lock);

    return 1;
#endif
}

/*
Finds the node in the list
*/
uint32_t lazylist_find_pred(lazylist_t *list, lazylist_range_t range, lazylist_node_t **pred_node, lazylist_node_t **curr_node)
{

    uint32_t curr_idx = list->head_idx;
    uint32_t pred_idx = curr_idx;

    lazylist_node_t *curr = GET_NODE_PTR(list, curr_idx);
    lazylist_node_t *pred = curr;

    // this works without checking EOL because of the sentinels
    while (curr->range.right < range.left)
    {
        pred = curr;
        curr_idx = curr->next_idx;
        curr = GET_NODE_PTR(list, curr_idx);
    }

    // check if range_left is already included in another range -> overlap -> possible double insertion
    if (curr->range.left <= range.right)
    {
        printf("Overlapping insertion detected (curr range: [%lu, %lu]; new range: [%lu, %lu]!\n", curr->range.left, curr->range.right, range.left, range.right);
        return 0;
    }

    *pred_node = pred;
    *curr_node = curr;

    return 1;
}


bool lazylist_validate(lazylist_t *list, lazylist_node_t *pred, lazylist_node_t *curr)
{
    return !IS_NODE_MARKED(list, pred->idx) && !IS_NODE_MARKED(list, curr->idx) && pred->next_idx == curr->idx;
}

uint32_t lazylist_insert(lazylist_t *list, lazylist_range_t range)
{
    S_ASSERT(range.left > INT32_MIN && range.right < INT32_MAX);
    // find pred
    lazylist_node_t *pred_node, *curr_node, *to_delete=NULL;
    uint32_t res;

    uint32_t error = 0;
    uint32_t terminate = 0;

    while (!terminate)
    {
        res = lazylist_find_pred(list, range, &pred_node, &curr_node);
        if (!res)
            return res;

        // make sure we are not inserting after the right sentinel! 
        S_ASSERT(pred_node->range.left < INT32_MAX);

        spin_lock_lock(&pred_node->lock);
        spin_lock_lock(&curr_node->lock);

        if (lazylist_validate(list, pred_node, curr_node))
        {
            // check if we have to merge
            bool connects_left = pred_node->range.right + 1 == range.left && pred_node->range.left > INT32_MIN /* sentinels are not extended */;
            bool connects_right = range.right + 1 == curr_node->range.left && curr_node->range.left < INT32_MAX /* sentinels are not extended */;

            if (connects_left && connects_right)
            {
                pred_node->range.right = curr_node->range.right;

                // remove curr
                list->marks[curr_node->idx] = 1;
                pred_node->next_idx = curr_node->next_idx;

                // GC
                to_delete = curr_node;
            }
            else if (connects_left)
            {
                pred_node->range.right = range.right;
            }
            else if (connects_right)
            {
                curr_node->range.left = range.left;
            }
            else
            {
                lazylist_node_t *new_node = NULL;
                uint32_t got_free_node = lazylist_get_free_node(list, &new_node);
                if (!got_free_node)
                {
                    error = 1;
                }
                else
                {
                    new_node->range = range;
                    list->marks[new_node->idx] = 0;
                    new_node->lock = 0;
                    new_node->next_idx = curr_node->idx;
                    pred_node->next_idx = new_node->idx;
                }
            }
            terminate = 1;
        }

        spin_lock_unlock(&curr_node->lock);
        spin_lock_unlock(&pred_node->lock);
    }

    if (to_delete) 
    { 
        lazylist_put_free_node(list, to_delete);
    }

    return error;
}

uint32_t lazylist_pop_front(lazylist_t *list, int32_t range_left, lazylist_range_t *range)
{
    uint32_t to_delete_idx;
    uint32_t popped = 0;

    while (!popped)
    {
        if (list->head_idx == EOL) return 0;

        lazylist_node_t *head_sentinel = GET_NODE_PTR(list, list->head_idx);

        lazylist_node_t *front = GET_NODE_PTR(list, head_sentinel->next_idx);
        lazylist_node_t *front_next = GET_NODE_PTR(list, front->next_idx);

        // nothing to do if list is empty
        if (front->range.left == INT32_MAX) return 0;

        // nothing to do if the list doesn't start where we expect 
        if (range_left != RANGE_START_ANY && front->range.left != range_left) return 0;

        spin_lock_lock(&front->lock);
        spin_lock_lock(&front_next->lock);

        if (lazylist_validate(list, front, front_next) && (front->range.left == range_left || range_left == RANGE_START_ANY)) {    
            *range = front->range;
            list->marks[front->idx] = 1;
            popped = 1;
            head_sentinel->next_idx = front_next->idx;
            to_delete_idx = front->idx;       
        } 

        spin_lock_unlock(&front_next->lock);
        spin_lock_unlock(&front->lock);
    }

    if (popped) 
    {
        lazylist_put_free_node(list, GET_NODE_PTR(list, to_delete_idx));
    }

    return 1;
}

// uint32_t lazylist_compare_and_shift_right(lazylist_t *list, uint32_t left, lazylist_range_t *range)
// {
//     bool terminate = 0;
//     lazylist_node_t *to_delete = NULL;
    
//     while (!terminate) {
//         lazylist_node_t *head = GET_NODE_PTR(list, list->head_idx);

//         lazylist_node_t *pred = head;
//         lazylist_node_t *curr = GET_NODE_PTR(list, head->next_idx);


//         if (curr->range.left == left) {
//             spin_lock_lock(&pred->lock);
//             spin_lock_lock(&curr->lock);


//             // WRONG --> REMOVE CURR, NOT PRED
//             if (lazylist_validate(pred, curr)) {    
//                 *range = curr->range;
//                 curr->marked = 1;

//                 list->head->next_idx = curr->idx;
//                 to_delete = curr;       
//             } 

//             spin_lock_unlock(&curr->lock);
//             spin_lock_unlock(&pred->lock);
//         }
//     }

//     if (to_delete) {
//         lazylist_put_free_node(list, to_delete);
//     }

//     return 1;
// }

#endif /* __LAZYLIST_H__ */
