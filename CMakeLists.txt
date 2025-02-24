cmake_minimum_required(VERSION 3.10)
project(hyrax_bls12_381)
set(CMAKE_CXX_STANDARD 14)
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -mcmodel=large -O3 -lpthread -pthread")

set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} -Wl,--no-relax,-z,notext")

set(THREADS_PREFER_PTHREAD_FLAG ON)
find_package(Threads REQUIRED)
#target_link_libraries(hyrax_time  PRIVATE Threads::Threads)
#target_link_libraries(hyrax_lib  PRIVATE Threads::Threads)

include_directories(src)

include_directories(..)

add_subdirectory(src)

