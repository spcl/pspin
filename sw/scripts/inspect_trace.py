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
import os
import sys
import argparse

parser = argparse.ArgumentParser(description='')
parser.add_argument('--min', dest='min_time', action='store', default=0, type=int)
parser.add_argument('--max', dest='max_time', action='store', default=-1, type=int)
parser.add_argument('--cluster', dest='cluster', action='store', default=-1, type=int)
parser.add_argument('--core', dest='core', action='store', default=-1, type=int)
parser.add_argument('--head', dest='head', action='store', default=-1, type=int)
parser.add_argument('--tail', dest='tail', action='store', default=-1, type=int)
parser.add_argument('--pc', dest='pc', action='store', default='', type=str)
parser.add_argument('--pa', dest='pa', action='store', default='', type=str)
parser.add_argument('--sort', dest='sort', action='store', default='', type=str)
parser.add_argument('--file', dest='file', action='store', default='', type=str)
parser.add_argument('--next_file', dest='next_file', action='store', default='', type=str)
parser.add_argument('--trace', dest='filename', action='store', default='', type=str)
parser.add_argument('--op', dest='op', action='append', default=[])
parser.add_argument('--user-only', dest='user_only', action='store_true')
args = parser.parse_args()

homedir = os.path.join(os.path.dirname(sys.argv[0]), os.pardir)

filename = args.filename
if len(filename) <= 0: 
    print('You have to specify a trace (--trace)')
    exit()

df = pd.read_csv(
    filepath_or_buffer=filename,
    sep=" ",
    quotechar='"',
    comment='#',
    names=['TIME', 'CYCLE', 'LATENCY', 'CLUSTER', 'CORE', 'FUN', 'PC', 'FILE', 'OPERATOR', 'OP'],
)

df = df[['CYCLE', 'LATENCY', 'CLUSTER', 'CORE', 'FUN', 'PC', 'FILE', 'OPERATOR', 'OP']]
df['FILE'] = df['FILE'].fillna('None')

df = df[df['CYCLE'] >= args.min_time]
if args.max_time >= 0:
    df = df[df['CYCLE'] < args.max_time]
if args.cluster >= 0:
    df = df[df['CLUSTER'] == args.cluster]
if args.core >= 0:
    df = df[df['CORE'] == args.core]
if len(args.next_file) > 0:
    df = df.reset_index()
    df['TO_KEEP'] = False
    df['NEXT_FILE'] = 'file'
    for i in range(len(df)-1):
        df.loc[i, 'TO_KEEP'] = df.loc[i+1, 'FILE'] == args.next_file
        df.loc[i, 'NEXT_FILE'] = df.loc[i+1, 'FILE']
    df = df[df['TO_KEEP']]
if len(args.pc) > 0:
    df = df[df['PC'] == args.pc]
if len(args.pa) > 0:
    df = df[df['OP'].str.contains(f'PA:{args.pa}')]
if len(args.file) > 0:
    df = df[df['FILE'].str.contains(args.file)]
for op in args.op:
    df = df[df['OP'].str.match(op)]
if args.user_only:
    df = df[df['FILE'].str.contains('init.c:') == False]
    df = df[df['FILE'].str.contains('hpu.c:') == False]
    df = df[df['FILE'].str.contains('riscv_v4.h:') == False]
    df = df[df['FILE'].str.contains('icache_ctrl_v2.h:') == False]
    df = df[df['FILE'].str.contains('pspin_rt.h:') == False]
    df = df[df['FILE'] != 'None']

if len(args.sort) > 0:
    df = df.sort_values(by=[args.sort])
else:
    df = df.sort_values(by=['CYCLE'])

if args.head >= 0:
    df = df.head(args.head)
if args.tail >= 0:
    df = df.tail(args.tail)

pd.set_option('display.max_rows', None)
pd.set_option('display.max_columns', None)
pd.set_option('display.width', None)
pd.set_option('display.max_colwidth', None)

print(df.reset_index())

