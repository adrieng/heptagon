#!/bin/sh
find . \! -path "*build*" -and \( -iname "*.ml" -or -iname "*.mli" -or -iname "*.mly" -or -iname "*.mll" -or -iname "*.ept" -or -iname "*.txt" \) -exec perl -pi -e 's/( |\t)+$//gi; s/\t/        /g' {} \;
