#!/bin/bash
num_cores=${1:-1}
if [ ! -d "build" ]; then
	mkdir build
fi
cd build
cmake -DCMAKE_BUILD_TYPE=release -DCMAKE_AR="/usr/bin/gcc-ar" -DCMAKE_RANLIB="/usr/bin/gcc-ranlib" -DCMAKE_CXX_ARCHIVE_CREATE="<CMAKE_AR> qcs <TARGET> <LINK_FLAGS> <OBJECTS>" ..
make run_snark -j $num_cores
