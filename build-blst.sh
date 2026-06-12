#!/bin/bash
# Build the blst shared library used by the BLS12-381 builtins.
# Produces blst/libblst.dylib (macOS) which src/bls.ss dlopens.
set -e
if [ ! -d blst ]; then
  git clone --depth 1 https://github.com/supranational/blst.git
fi
cd blst
[ -f build/assembly.S ] || ./build.sh
cc -dynamiclib -O2 -fno-builtin -fPIC -o libblst.dylib src/server.c build/assembly.S
echo "built blst/libblst.dylib"
