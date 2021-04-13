import glob
import os
from shutil import copyfile
import sys

for file in glob.glob("./*.slm"):
    if "l2" not in file and "tcdm" not in file and "prog_mem" not in file:
        dir = os.path.dirname(file)
        target = os.path.join(dir, "l2_{}_{}".format(sys.argv[1], os.path.basename(file)))
        copyfile(file, target)

