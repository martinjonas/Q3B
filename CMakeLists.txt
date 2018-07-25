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
set(TEST_SOURCES ${CMAKE_CURRENT_SOURCE_DIR}/tests/main.cpp ${CMAKE_CURRENT_SOURCE_DIR}/tests/testUnconstrained.cpp)
add_executable(tests ${TEST_SOURCES})
target_link_libraries(tests q3blib)
target_link_libraries(tests Catch)

SET(COVERAGE OFF CACHE BOOL "Coverage")
if (COVERAGE)
    target_compile_options(tests PRIVATE --coverage)
    target_link_libraries(tests PRIVATE --coverage)
    set(CMAKE_CXX_FLAGS_DEBUG "${CMAKE_CXX_FLAGS_DEBUG} -fprofile-arcs -ftest-coverage")
    set(CMAKE_CXX_FLAGS_RELEASE "${CMAKE_CXX_FLAGS_RELEASE} -fprofile-arcs -ftest-coverage")
endif()

enable_testing()
add_test(NAME RegressionNoApprox COMMAND ./tests [noapprox])
add_test(NAME RegressionVariableApprox COMMAND ./tests [variableapprox])
add_test(NAME RegressionBothLimitApprox COMMAND ./tests [bothlimitapprox])
add_test(NAME RegressionBothLimitApprox-TCI COMMAND ./tests [bothlimitapprox-tci])
add_test(NAME RegressionOperationLimitApprox-ITE COMMAND ./tests [operationapproxlimit-ite])
add_test(NAME RegressionSMTCOMP2018 COMMAND ./tests [smtcomp18])
add_test(NAME RegressionGoalUnconstrained COMMAND ./tests [goalunconstrained])

add_test(NAME UnconstrainedBinaryTests COMMAND ./tests [unconstrained-binary-functions])

### STAREXEC ###

add_custom_command(OUTPUT ${LIBFOO_TAR_HEADERS}
  COMMAND rm -rf bin
  COMMAND mkdir bin
  COMMAND cp "${CMAKE_CURRENT_SOURCE_DIR}/app/starexec_run_default" bin
  COMMAND cp q3b bin
  COMMAND tar -czf q3b_starexec.tar.gz bin
  COMMAND rm -rf bin
  OUTPUT q3b_starexec.tar.gz
  COMMENT "Generating starexec archive"
  VERBATIM
)

add_custom_target(starexec DEPENDS q3b_starexec.tar.gz)
