#!/bin/sh
# This small helper scripts automates the Heptagon -> VHDL translation.
# You need GHDL and optionally GTKWave for user-friendly visualization.

if [ $# -lt 1 ]
then
  echo Usage: $0 file.ept
  exit 1
fi

compile=1

if [ $# -gt 2 ];
then
  nocompile=0
fi

F=$1
REP=`basename $F .ept`_vhdl
shift

# Compile source file to VHDL, flattening node calls
if [ $compile -eq 1 ]; then
  heptc.native $@ -s main -target vhdl $F $@ > tmp.sh || exit 1
fi

# Display the resulting VHDL code
for i in $REP/*.vhd
do
  echo File $i
  cat -n $i
done

cd $REP || exit 1

# Properly compile it with GHDL; order matters
ghdl -a types.vhd `grep node ../$F | perl -pe 's/node (.*?)\b*\(.*$/$1.vhd/'` \
  main_tb.vhd || exit 1

# Link everything using the generated test-bench
ghdl -e main_tb || exit 1

# Run the simulation for 50 nanoseconds, and output the signals to simu.vcd.
./main_tb --stop-time=12ns --vcd=simu.vcd || exit 1

# Call GTKWave for visualization only if it is not already running.
ps aux | grep -v grep | grep -q gtkwave || gtkwave simu.vcd&
