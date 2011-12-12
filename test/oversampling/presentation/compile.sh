#!/bin/bash
for f in *.ept; do
	heptc -O -s main -target c -target java $f
	pushd ${f/.ept/_c}
	gcc -I ~/heptagon/lib/c *.c
	popd
done
