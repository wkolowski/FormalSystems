#!/bin/sh

# Generate a makefile.
coq_makefile -R "." FormalSystems -o makefile $(find -name "*v")

# Build the library.
make -j `nproc`

# Delete the makefile and related files.
rm makefile makefile.conf
