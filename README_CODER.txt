
*** Scripts:

** clean_heptc
* Arguments: none.
* Usages: used to remove heptc binaries and compiled files. It's main goal is to do a fresh compilation. heptc script may be called right after this to recompile all the things needed.

** heptc
* Arguments: see heptc -h
* Usages: wrap the real compiler in order to recompile it if it doesn't exists, and to recompile pervasives if needed. calling clean_heptc before it will ensure recompilation of everything.

*** Code organization:

