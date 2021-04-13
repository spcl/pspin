#!/usr/bin/python2

# ////////////////////////////////////////////////////////////////////////////////
# // Company:        Multitherman Laboratory @ DEIS - University of Bologna     //
# //                    Viale Risorgimento 2 40136                              //
# //                    Bologna - fax 0512093785 -                              //
# //                                                                            //
# // Engineer:       Davide Rossi - davide.rossi@unibo.it                       //
# //                                                                            //
# // Additional contributions by:                                               //
# //                 Andreas Traber - atraber@student.ethz.ch                   //
# //                                                                            //
# // Create Date:    05/04/2013                                                 // 
# // Design Name:    ULPSoC                                                     //
# // Project Name:   ULPSoC                                                     //
# // Language:       tcl, now python                                            //
# //                                                                            //
# // Description:    s19 to slm conversion tool for stxp70 cluster compilation  //
# //                                                                            //
# // Revision:                                                                  //
# // Revision v0.1 - File Created                                               //
# // Revision v0.2 - Modification: Compiler does now generate little endian     //
# //                 directly. revert bytes!                                    //
# // Revision v0.3 - Moved from 128 bit s19 to 8 bit s19 file. This solves our  //
# //                 problems with misaligned addresses in s19 files.           //
# // Revision v0.4 - Added TCDM memory initialization                           //
# // Revision v0.5 - Rewrote the whole thing in python as tcl cannot handle     //
# //                 long file names properly
# ////////////////////////////////////////////////////////////////////////////////

import sys
import math


###############################################################################
# Function to dump single bytes of a string to a file
###############################################################################
def dump_bytes( filetoprint, addr, data_s):
    for i in range(0,4,1):
        filetoprint.write("@%08X %s\n" % ( addr+i,  data_s[i*2:(i+1)*2] ))


###############################################################################
# Start of file
###############################################################################
if(len(sys.argv) < 2):
    print("Usage s19toslm.py FILENAME")
    quit()

l2_hnd_start     = 0x1C000000
l2_hnd_end       = l2_hnd_start + 4*1024*1024 - 1
l2_pkt_start     = l2_hnd_end + 1
l2_pkt_end       = l2_pkt_start + 4*1024*1024 - 1
l2_hnd_width     = 32
l2_pkt_width     = 32

prog_mem_start = 0x1D000000
prog_mem_end = prog_mem_start + 32*1024 - 1
prog_mem_width = 64

#tcdm_banks     = 32
#tcdm_bank_size = 8192 # in words (32 bit)
tcdm_banks     = 64
tcdm_bank_size = 4096 # in words (32 bit)
tcdm_start     = 0x10000000
tcdm_end       = tcdm_start + tcdm_banks * tcdm_bank_size * 4 - 1
tcdm_bank_bits = int(math.log(tcdm_banks, 2))
tcdm_width     = 32

###############################################################################
# Parse s19 file
###############################################################################
s19_file = open(sys.argv[1], 'r')
s19_dict = {}

for line in s19_file:
    rec_field = line[:2]
    prefix    = line[:4]

    if rec_field == "S0" or prefix == "S009" or prefix == "S505" or prefix == "S705" or prefix == "S017" or line == "":
        continue

    addr = int("0x%s" % line[4:12], 0)
    data = line[12:14]

    s19_dict[addr] = data

s19_file.close()

def bytes_to_words(word_width, start_addr, end_addr):
    word_dict = {}
    num_bytes = word_width / 8
    shamt = int(math.log(num_bytes, 2))
    for addr in s19_dict:
        if addr < start_addr or addr > end_addr:
            continue

        word_addr = addr >> shamt
        if word_addr in word_dict:
            data = word_dict[word_addr]
        else:
            data = '00' * num_bytes

        byte_num = addr % num_bytes
        data = list(data)
        upper = 2 * (num_bytes - byte_num)
        lower = upper - 2
        data[lower:upper] = list(s19_dict[addr])
        data = ''.join(data)
        word_dict[word_addr] = data
    return word_dict

slm_dict = {}
for addr in s19_dict:
    wordaddr = addr >> 2
    data = "00000000"

    if wordaddr in slm_dict:
        data = slm_dict[wordaddr]

    byte = addr % 4
    byte0 = data[0:2]
    byte1 = data[2:4]
    byte2 = data[4:6]
    byte3 = data[6:8]
    new   = s19_dict[addr]

    if byte == 0:
        data = "%s%s%s%s" % (byte0, byte1, byte2, new)
    elif byte == 1:
        data = "%s%s%s%s" % (byte0, byte1, new,   byte3)
    elif byte == 2:
        data = "%s%s%s%s" % (byte0, new,   byte2, byte3)
    elif byte == 3:
        data = "%s%s%s%s" % (new,   byte1, byte2, byte3)

    slm_dict[wordaddr] = data

# word align all addresses
#l2_start   = l2_start   >> 2
#l2_end     = l2_end     >> 2
#prog_mem_start = prog_mem_start >> 2
#prog_mem_end = prog_mem_end >> 2
tcdm_start = tcdm_start >> 2
tcdm_end   = tcdm_end   >> 2


l2_hnd_dict = bytes_to_words(l2_hnd_width, l2_hnd_start, l2_hnd_end) 
l2_pkt_dict = bytes_to_words(l2_pkt_width, l2_pkt_start, l2_pkt_end)
prog_mem_dict = bytes_to_words(prog_mem_width, prog_mem_start, prog_mem_end)


###############################################################################
# open files
###############################################################################
tcdm_files = {}
for i in range(0, tcdm_banks):
    tcdm_files[i] = open("tcdm_bank%d.slm" % i, 'w')
l2_hnd_stim = open("l2_hnd_stim.slm", 'w')
l2_pkt_stim = open("l2_pkt_stim.slm", 'w')
prog_mem_stim = open("prog_mem_stim.slm", 'w')

###############################################################################
# write the stimuli
###############################################################################
def write_file(f, entries, start_addr, word_width):
    num_bytes = word_width / 8
    start_word_addr = start_addr >> int(math.log(num_bytes, 2))
    for word_addr in sorted(entries.keys()):
        word = entries[word_addr]
        entry_addr = word_addr - start_word_addr
        f.write("@%08X %s\n" % (entry_addr, word))

for addr in sorted(slm_dict.keys()):
    data = slm_dict[addr]

    ## l2 address range
    #if(addr >= l2_start and addr <= l2_end):
    #    l2_base = addr - l2_start
    #    l2_stim.write("@%08X %s\n" % (l2_base, data))

    ## program memory address range
    #if(addr >= prog_mem_start and addr <= prog_mem_end):
    #    prog_mem_base = addr - prog_mem_start
    #    prog_mem_stim.write("@%08X %s\n" % (prog_mem_base, data))

    # tcdm address range
    if(addr >= tcdm_start and addr <= tcdm_end):
        tcdm_addr = (addr - tcdm_start) >> tcdm_bank_bits
        bank      = addr % tcdm_banks
        tcdm_files[bank].write("@%08X %s\n" % (tcdm_addr, data))
        #tcdm_size += 1 

write_file(l2_hnd_stim, l2_hnd_dict, l2_hnd_start, l2_hnd_width)
write_file(l2_pkt_stim, l2_pkt_dict, l2_pkt_start, l2_pkt_width)

write_file(prog_mem_stim, prog_mem_dict, prog_mem_start, prog_mem_width)

###############################################################################
# close all files
###############################################################################

for i in tcdm_files:
    tcdm_files[i].close()

prog_mem_stim.close()
l2_hnd_stim.close()
l2_pkt_stim.close()

