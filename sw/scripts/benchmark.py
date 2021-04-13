#!/bin/python3

# Copyright (C) 2020 ETH Zurich
# 
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
# 
#     https://www.apache.org/licenses/LICENSE-2.0
# 
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
#
# Authors: 
#   Elias Stalder, ETH (staldere@student.ethz.ch)

import pandas as pd
import subprocess
import os
from pathlib import Path
import sys
import argparse

def to_name(make_defs, code_defs):
    return ('.'.join([f'{key}={value}'for key, value in make_defs.items()]) \
        + ('.' if len(make_defs) > 0 and len(code_defs) > 0 else '') \
        + '.'.join(code_defs)).replace('=', '-')

def get_filename(cmd, name, suffix):
    return f'{cmd}.{name}.{suffix}'

def run(folder, name, cmd_name, cmd, environment, cwd, suffix='log', to_stdout=False):
    if to_stdout:
        subprocess.run(cmd, env=environment, check=True, cwd=cwd)
    else:
        with open(os.path.join(folder, get_filename(cmd_name, name, suffix)), 'w') as f:
            subprocess.run(cmd, stdout=f, env=environment, check=True, cwd=cwd)

START_COLS = ['CLUSTER', 'CORE', 'START_TIME']
END_COLS = ['CLUSTER', 'CORE', 'END_TIME', 'MSG_ID', 'PKT_SIZE']
COLS = ['CLUSTER', 'CORE', 'END_TIME', 'START_TIME', 'LATENCY', 'MSG_ID', 'PKT_SIZE']

def handler_latencies(folder, name):
    with open(os.path.join(folder, get_filename('sim', name, 'log')), 'r') as f:
        starts = []
        ends = []
        for line in f:
            if 'HANDLER_START' in line:
                line = line.strip()
                parts = line.split(':')
                time = parts[0][1:-7]
                parts = parts[1].split(' ')
                starts += [[int(parts[3]), int(parts[4]), int(time)]]
            elif 'HANDLER_TIME' in line:
                line = line.strip()
                parts = line.split(':')
                time = parts[0][1:-7]
                parts = parts[1].split(' ')
                ends += [[int(parts[3]), int(parts[4]), int(time), int(parts[5]), int(parts[8])]]

    df_start = pd.DataFrame(data=starts, columns=START_COLS).sort_values(by=START_COLS).reset_index()[START_COLS].reset_index()
    df_end = pd.DataFrame(data=ends, columns=END_COLS).sort_values(by=['CLUSTER', 'CORE', 'END_TIME']).reset_index()[END_COLS].reset_index()
    df = df_start.merge(df_end, on=['index', 'CORE', 'CLUSTER'])
    df['START_TIME'] = df['START_TIME'] / 1000
    df['END_TIME'] = df['END_TIME'] / 1000
    df['LATENCY'] = df['END_TIME'] - df['START_TIME']
    df[['START_TIME', 'END_TIME', 'LATENCY']] = df[['START_TIME', 'END_TIME', 'LATENCY']].astype(int)
    df = df[COLS]
    df.to_csv(
        path_or_buf=os.path.join(folder, get_filename('handlers', name, 'csv')),
        sep=' ',
        index=False,
        header=True
    )

def run_benchmark(out_folder, make_defs, code_defs, args):
    name = to_name(make_defs, code_defs)
    environment = {**dict(os.environ), **make_defs}
    defs = ' '.join([f'-D{d}' for d in code_defs])
    environment['DEFINITIONS'] = f'{defs}'

    print(name)
    print(environment)

    if (not args.repeat) and (os.path.isfile(os.path.join(out_folder, get_filename('handlers', name, 'csv')))):
        print('skip')
        return

    run(out_folder, name, 'patch', ['make', 'patch'], environment, args.cwd)
    run(out_folder, name, 'deploy', ['make', 'deploy'], environment, args.cwd)
    if args.generator:
        run(out_folder, name, 'generator', ['make', 'generator'], environment, args.cwd)
    run(out_folder, name, 'packets', ['make', 'packets'], environment, args.cwd)
    sim_cmd = 'simulate'
    if args.debug:
        sim_cmd = 'simulate-debug'
    try:
        run(out_folder, name, 'simulate', ['make', sim_cmd], environment, args.cwd, to_stdout=True)
    except KeyboardInterrupt as e:
        print(e)
    run(out_folder, name, 'sim', ['make', 'transcript'], environment, args.cwd)
    run(out_folder, name, 'trace', ['make', 'trace-stdout'], environment, args.cwd, suffix='txt')
    run(out_folder, name, 'trace', ['make', 'trace-chrome-stdout'], environment, args.cwd, suffix='json')

    handler_latencies(out_folder, name)

def convert_dict_entry(entry):
    key, value = entry
    if value == False or value == 'False':
        return None
    elif value == True or value == 'True':
        return f'{key}'
    else:
        return f'{key}={value}'

parser = argparse.ArgumentParser(description='')
parser.add_argument('--debug', dest='debug', action='store_true', help='to enable debuggin mode of simulator')
parser.add_argument('--generator', dest='generator', action='store_true', help='to also build packet-generator (make generator has to be defined)')
parser.add_argument('--repeat', dest='repeat', action='store_true', help='to override existing benchmarks with same names')
parser.add_argument('--cwd', dest='cwd', action='store', default='./', type=str, help='to set working directory')
parser.add_argument('--code', dest='code_defs', action='store', default='definitions.code.csv', type=str, help='to specify c flags')
parser.add_argument('--make', dest='make_defs', action='store', default='definitions.make.csv', type=str, help='to specify make definitions')
args = parser.parse_args()

df_make = pd.read_csv(
    filepath_or_buffer=args.make_defs,
    sep="\\s+",
    quotechar='"',
    comment='#',
)
df_make = df_make.astype(str)

df_code = pd.read_csv(
    filepath_or_buffer=args.code_defs,
    sep="\\s+",
    quotechar='"',
    comment='#',
)
code_definitions = [
    list(filter(None, [convert_dict_entry(e) for e in list(d.items())])) for d in df_code.to_dict(orient='records')
]

OUT_FOLDER = os.path.join(os.path.join(args.cwd, 'out'), os.environ['CONTAINER_NAME'])
Path(OUT_FOLDER).mkdir(parents=True, exist_ok=True)

try:
    for make_defs in df_make.to_dict(orient='records'):
        for code_defs in code_definitions:
            run_benchmark(OUT_FOLDER, make_defs, code_defs, args)
except subprocess.CalledProcessError as e:
    print(e)
