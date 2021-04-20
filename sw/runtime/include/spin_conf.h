// Copyright 2020 ETH Zurich
// 
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
// 
//     http://www.apache.org/licenses/LICENSE-2.0
// 
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

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

