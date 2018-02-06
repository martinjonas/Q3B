#specify the version being used aswell as the language
cmake_minimum_required(VERSION 2.6)
#Name your project here
project(q3b)

SET(CMAKE_CXX_STANDARD 17)

if(NOT CMAKE_BUILD_TYPE)
    message(STATUS "No Build type specified; using RELEASE.")
    set(CMAKE_BUILD_TYPE Release)
endif(NOT CMAKE_BUILD_TYPE)

file(GLOB Q3B_SRC
    "lib/*.h"
    "lib/*.cpp"
    "BDD/cudd/bvec_cudd.h"
    "BDD/cudd/bvec_cudd.cpp"
    "BDD/maybeBdd/maybeBdd.h"
    "BDD/maybeBdd/maybeBdd.cpp"
)

SET(CMAKE_FIND_LIBRARY_SUFFIXES ".a")
SET(BUILD_SHARED_LIBRARIES OFF)
#SET(CMAKE_EXE_LINKER_FLAGS "-static")
set(CMAKE_EXE_LINKER_FLAGS "-static-libgcc -static-libstdc++")

#set( CMAKE_CXX_FLAGS "-fstack-protector -fstack-protector-all" )
set(CMAKE_CXX_FLAGS_DEBUG "${CMAKE_CXX_FLAGS_DEBUG} -Wall")
set(CMAKE_CXX_FLAGS_RELEASE "${CMAKE_CXX_FLAGS_RELEASE} -Wall")

find_library(LibZ3 z3 PATHS /usr/lib DOC "z3 library")

if(NOT LibZ3)
  message(FATAL_ERROR "Library libz3 required, but not found!")
endif(NOT LibZ3)

include_directories(${LibZ3_INCLUDE_DIRS})
set(LIBS ${LIBS} ${LibZ3})

find_library(LibCUDD cudd PATHS /usr/local/lib DOC "bdd library")
if(NOT LibCUDD)
  message(FATAL_ERROR "Library libcudd required, but not found!")
endif(NOT LibCUDD)

set(LIBS ${LIBS} ${LibCUDD})

find_package(OpenMP)
if (OPENMP_FOUND)
    set (CMAKE_C_FLAGS "${CMAKE_C_FLAGS} ${OpenMP_C_FLAGS}")
    set (CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} ${OpenMP_CXX_FLAGS}")
endif()

find_package (Threads)

add_library(q3blib ${Q3B_SRC})
target_link_libraries(q3blib ${CMAKE_THREAD_LIBS_INIT})
target_link_libraries(q3blib ${LIBS})

add_executable(q3b app/main.cpp)
target_link_libraries(q3b q3blib)

### CATCH ###

# Prepare "Catch" library for other executables
set(CATCH_INCLUDE_DIR ${CMAKE_CURRENT_SOURCE_DIR}/tests/catch)
add_library(Catch INTERFACE)
target_include_directories(Catch INTERFACE ${CATCH_INCLUDE_DIR})

# Make test executable
set(TEST_SOURCES ${CMAKE_CURRENT_SOURCE_DIR}/tests/main.cpp)
add_executable(tests ${TEST_SOURCES})
target_link_libraries(tests q3blib)
target_link_libraries(tests Catch)
