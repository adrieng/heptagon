#!/bin/sh

find . \( -iname "*.ml" -or -iname "*.mli" \) -exec perl -pi -e 's/( |\t)+$//g' {} \;
find . \( -iname "*.ml" -or -iname "*.mli" \) -exec perl -pi -e 's/\t/  /g' {} \;
