#specify the version being used aswell as the language
cmake_minimum_required(VERSION 2.6)
#Name your project here
project(q3b)

#set(CMAKE_MODULE_PATH ${CMAKE_MODULE_PATH} "${CMAKE_SOURCE_DIR}/cmake/Modules/")

#Sends the -std=c99 flag to the gcc compiler
add_definitions(-std=c++0x)
#This tells CMake to fib.c and name it fibonacci
file(GLOB Q3B_SRC
    "*.h"
    "*.cpp"
)

SET(CMAKE_FIND_LIBRARY_SUFFIXES ".a")
SET(BUILD_SHARED_LIBRARIES OFF)
#SET(CMAKE_EXE_LINKER_FLAGS "-static")
set(CMAKE_EXE_LINKER_FLAGS "-static-libgcc -static-libstdc++")

add_executable(q3b ${Q3B_SRC})

#set( CMAKE_CXX_FLAGS "-fstack-protector -fstack-protector-all" )
set(CMAKE_CXX_FLAGS_DEBUG "${CMAKE_CXX_FLAGS_DEBUG} -Wall")
set(CMAKE_CXX_FLAGS_RELEASE "${CMAKE_CXX_FLAGS_RELEASE} -Wall")

find_library(LibZ3 z3 PATHS /usr/lib DOC "z3 library")

if(NOT LibZ3)
  message(FATAL_ERROR "Library libz3 required, but not found!")
endif(NOT LibZ3)

include_directories(${LibZ3_INCLUDE_DIRS})
set(LIBS ${LIBS} ${LibZ3})

find_library(LibBDD bdd PATHS /usr/local/lib DOC "bdd library")

if(NOT LibBDD)
  message(FATAL_ERROR "Library libbdd required, but not found!")
endif(NOT LibBDD)

find_package(OpenMP)
if (OPENMP_FOUND)
    set (CMAKE_C_FLAGS "${CMAKE_C_FLAGS} ${OpenMP_C_FLAGS}")
    set (CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} ${OpenMP_CXX_FLAGS}")
endif()

set(LIBS ${LIBS} ${LibBDD})

target_link_libraries(q3b ${LIBS})
