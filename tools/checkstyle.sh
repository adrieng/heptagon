#!/bin/sh

[ -f $1 ] || $(echo "File $1 does not exists." && exit 1)

bad=0

if [ `wc -L $1 | awk '{ print $1 }'` -gt 80 ]; then
  echo "File \"$1\" has lines with more than 80 columns."
  bad=1
fi

grep -P '\t' $1 > /dev/null
if [ $? -eq 0 ]; then
  echo "File \"$1\" has tabulations in it."
  bad=1
fi

grep -P ' +$' $1 > /dev/null
if [ $? -eq 0 ]; then
  echo "File \"$1\" has trailing whitespace."
  bad=1
fi

exit $bad
