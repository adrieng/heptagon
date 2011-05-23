#!/bin/sh
find . \! -path "*_build*" -and \( -iname "*.ml" -or -iname "*.mli" -or -iname "*.mly" -or -iname "*.mll" -or -iname "*.ept" \) -exec perl -pi -e 's/( |\t)+$//gi; s/\t/  /g' {} \;
