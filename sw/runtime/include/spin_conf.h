#pragma once

/* PULP settings */
// number of cores per cluster
#ifndef NB_CORES
    #define NB_CORES    8
#endif

// number of clusters
#ifndef NB_CLUSTERS
    #define NB_CLUSTERS 4
#endif
#define CORE_COUNT (NB_CORES * NB_CLUSTERS)

/* Packet settings */
// length of the input packet queue [B]
// Warning: modify spin_types.h if you increase this size!
#define PacketQueueLength (4 * (1 << 20) - 3 * 4) // 4 MiB minus three words meta data

// size of data payload in each packet [B]
#ifndef PKT_SIZE
#define PKT_SIZE 1024
#endif

// number of HPUs per each cluster
#define NUM_CLUSTER_HPUS (NB_CORES)

