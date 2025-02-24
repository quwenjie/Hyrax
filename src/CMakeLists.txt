aux_source_directory(. LIB_SRC)
list(FILTER LIB_SRC EXCLUDE REGEX "main*")
find_library(MCL_LIBRARY NAMES mcl PATHS /usr/local/lib)
find_path(MCL_INCLUDE_DIR NAMES mcl/mcl.h PATHS /usr/local/include)

add_library(hyrax_lib ${LIB_SRC})
add_executable(hyrax_time main.cpp hyrax.cpp timer.cpp)


target_include_directories(hyrax_time PRIVATE  ${MCL_INCLUDE_DIR})
target_link_libraries(hyrax_time PRIVATE ${MCL_LIBRARY})