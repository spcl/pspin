#include <math.h>
#include <stddef.h>

#include "pulp.h" // PULP API
#include "spinningpulp.h"

#include "spin_conf.h"
#include "hpu.h"
#include "handler.h"
#include "util.h"

// Shared variables in L1 of each cluster, initialized to zero.
//volatile __attribute__ ((section(".data_tiny_l1"))) uint8_t* volatile l1_buf;
volatile uint32_t finished[NB_CLUSTERS];

void success()
{
    return;
}

void core_entry(void *arg)
{
    int core_id = rt_core_id();
    hpu_entry();
}

void cluster_entry(void *arg)
{
    int cluster_id = rt_cluster_id();
    rt_team_fork(NB_CORES, core_entry, NULL);
    finished[cluster_id] = 1;
}

int main()
{
    // Allocate event so clusters can be mounted and started without blocking.
    rt_event_alloc(NULL, 1);
    rt_event_t *event = rt_event_get(NULL, success, 0);

    // hack to keep the functions in the binary (THIS POINTERS ARE NOT BEING USED!)
    handler_fn hh, ph, th;
    void *handler_mem;
    init_handlers(&hh, &ph, &th, &handler_mem);

    // Mount clusters.
    for (unsigned i = 0; i < NB_CLUSTERS; i++)
    {
        rt_cluster_mount(1, i, 0, event);
    }

    // Start execution on other clusters.
    for (unsigned i = 1; i < NB_CLUSTERS; i++)
    {
        rt_cluster_call(NULL, i, cluster_entry, NULL, NULL, 0, 0, NB_CORES, event);
    }

    // Start execution on own cluster.
    cluster_entry(NULL);

    // Wait for other clusters to complete execution and then unmount them.
    for (unsigned i = 1; i < NB_CLUSTERS; i++)
    {
        while (!finished[i])
        {
            rt_time_wait_cycles(256);
        }
        rt_cluster_mount(0, i, 0, NULL);
    }

    // Send EOC.
    *(volatile unsigned int *)0x1B200000 = 1;

    return 0;
}
