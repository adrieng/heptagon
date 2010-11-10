#!/bin/sh
# This small helper scripts automates the Heptagon -> C translation.

if [ $# -lt 1 ]
then
  echo Usage: $0 file.ept
  exit 1
fi

if `which heptc.native` 2>/dev/null; then
  HEPTC=heptc.native
else
  HEPTC=heptc.byte
fi

compile=1

if [ $# -gt 2 ];
then
  nocompile=0
fi

F=$1
REP=`basename $F .ept`_c
shift

# Compile source file to VHDL, flattening node calls
if [ $compile -eq 1 ]; then
  $HEPTC $@ -s main -target c $F $@ || exit 1
fi

# Compile it with GCC
cc -std=c99 $REP/*.c -o `basename $F .ept` || exit 1
