// Copyright 2022 ETH Zurich
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

#include <stdint.h>
#include "gdriver.h"

int main(int argc, char**argv)
{
    const char *handlers_file = "build/aggregate_and_reduce";
    const char *hh_aggregate = NULL;
    const char *ph_aggregate = "aggregate_global_ph";
    const char *th_aggregate = "aggregate_global_th";
    const char *hh_reduce = NULL;
    const char *ph_reduce = "reduce_l1_ph";
    const char *th_reduce = "reduce_l1_th";
    int ectx_num;
    
    gdriver_init(argc, argv, NULL, &ectx_num);

    gdriver_add_ectx(handlers_file, hh_aggregate, ph_aggregate, th_aggregate,
	NULL, NULL, 0, NULL, 0);
    gdriver_add_ectx(handlers_file, hh_reduce, ph_reduce, th_reduce,
	NULL, NULL, 0, NULL, 0);

    gdriver_run();

    gdriver_fini();

    return 0;
}
