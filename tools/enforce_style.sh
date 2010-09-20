#!/bin/sh
find . \! -path "*_build*" -and \( -iname "*.ml" -or -iname "*.mli" \) -exec perl -pi -e 's/( |\t)+$//gi; s/\t/  /g' {} \;
