#specify the version being used aswell as the language
cmake_minimum_required(VERSION 2.6)
#Name your project here
project(q3b)

SET(CMAKE_CXX_STANDARD 17)
SET(LIB_DIR "C:/lib")

if(NOT CMAKE_BUILD_TYPE)
    message(STATUS "No Build type specified; using RELEASE.")
    set(CMAKE_BUILD_TYPE Release)
endif(NOT CMAKE_BUILD_TYPE)

#include_directories(cudd)
file(GLOB Q3B_SRC
    "lib/*.h"
    "lib/*.cpp"
    "lib/cudd/*.h"
    "lib/cudd/*.c"
        "lib/cudd/*.cpp"
    "lib/epd/*.h"
    "lib/epd/*.c"
        "lib/mtr/*.h"
        "lib/mtr/*.c"
    "lib/util/*.h"
    "lib/util/*.c"
    "lib/st/*.h"
    "lib/st/*.c"
    "lib/maybeBdd/maybeBdd.h"
    "lib/maybeBdd/maybeBdd.cpp"
    "lib/cuddCpp/*.cc"
    "lib/cuddCpp/*.hh"
)

SET(CMAKE_FIND_LIBRARY_SUFFIXES ".a" ".dll")
SET(BUILD_SHARED_LIBRARIES OFF)
#SET(CMAKE_EXE_LINKER_FLAGS "-static")
#set(CMAKE_EXE_LINKER_FLAGS "-static-libgcc -static-libstdc++")

#set( CMAKE_CXX_FLAGS "-fstack-protector -fstack-protector-all" )
set(CMAKE_CXX_FLAGS_DEBUG "${CMAKE_CXX_FLAGS_DEBUG} -Wall")
set(CMAKE_CXX_FLAGS_RELEASE "${CMAKE_CXX_FLAGS_RELEASE} -Wall")

find_library(LibZ3 libz3 PATHS "${LIB_DIR}/z3/bin/" DOC "z3 library")

if(NOT LibZ3)
  message(FATAL_ERROR "Library libz3 required, but not found!")
endif(NOT LibZ3)

include_directories("${LIB_DIR}/z3/include/")
set(LIBS ${LIBS} ${LibZ3})

#find_library(LibOBJ "${LIB_DIR}/cudd/libobj.a" DOC "bdd_cpp library")
#if(NOT LibOBJ)
#    message(FATAL_ERROR "Library libobj required, but not found!")
#endif(NOT LibOBJ)
#find_library(LibCUDD "${LIB_DIR}/cudd/libcudd.a" DOC "bdd library")
#if(NOT LibCUDD)
#    message(FATAL_ERROR "Library libcudd required, but not found!")
#endif(NOT LibCUDD)

#include_directories("${LIB_DIR}/cudd/include/")
#set(LIBS ${LIBS} ${LibOBJ} ${LibCUDD})
#set(LIBS ${LIBS} ${LibCUDD})

# find_package(OpenMP)
# if (OPENMP_FOUND)
#    set (CMAKE_C_FLAGS "${CMAKE_C_FLAGS} ${OpenMP_C_FLAGS}")
#     set (CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} ${OpenMP_CXX_FLAGS}")
# endif()

# find_package (Threads)

message(STATUS "q3b_src: ${Q3B_SRC}")
add_library(q3blib ${Q3B_SRC})
# target_link_libraries(q3blib ${CMAKE_THREAD_LIBS_INIT})
target_link_libraries(q3blib ${LIBS})

add_executable(q3b app/main.cpp)
message(STATUS "libs: ${LIBS}")
target_link_libraries(q3b q3blib)

### CATCH ###

# Prepare "Catch" library for other executables
set(CATCH_INCLUDE_DIR ${CMAKE_CURRENT_SOURCE_DIR}/tests/catch)
add_library(Catch INTERFACE)
target_include_directories(Catch INTERFACE ${CATCH_INCLUDE_DIR})

# Make test executable
set(TEST_SOURCES ${CMAKE_CURRENT_SOURCE_DIR}/tests/main.cpp)
add_executable(tests ${TEST_SOURCES})
target_link_libraries(tests q3blib Catch ${LIBS})

SET(COVERAGE OFF CACHE BOOL "Coverage")
if (COVERAGE)
    target_compile_options(tests PRIVATE --coverage)
    target_link_libraries(tests PRIVATE --coverage)
    set(CMAKE_CXX_FLAGS_DEBUG "${CMAKE_CXX_FLAGS_DEBUG} -fprofile-arcs -ftest-coverage")
    set(CMAKE_CXX_FLAGS_RELEASE "${CMAKE_CXX_FLAGS_RELEASE} -fprofile-arcs -ftest-coverage")
endif()

enable_testing()

add_test(NAME BddBasicOperations COMMAND ./tests [bdd_basic])
add_test(NAME BddBasicOperationsExtended COMMAND ./tests [bdd_basic_ex])
add_test(NAME UnsignedLthOperation COMMAND ./tests [u_lth])
add_test(NAME UnsignedLteOperation COMMAND ./tests [u_lte])
add_test(NAME EquOperation COMMAND ./tests [equ])

add_test(NAME RegressionNoApprox COMMAND ./tests [noapprox])
add_test(NAME RegressionVariableApprox COMMAND ./tests [variableapprox])
add_test(NAME RegressionBothLimitApprox COMMAND ./tests [bothlimitapprox])
add_test(NAME RegressionBothLimitApprox-TCI COMMAND ./tests [bothlimitapprox-ti])
add_test(NAME RegressionOperationLimitApprox-ITE COMMAND ./tests [opapproxlimit-ite])
