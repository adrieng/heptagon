#!/bin/sh
find . \! -path "*_build*" -and \( -iname "*.ml" -or -iname "*.mli" -or -iname "*.mly" -or -iname "*.mll" \) -exec perl -pi -e 's/( |\t)+$//gi; s/\t/  /g' {} \;
