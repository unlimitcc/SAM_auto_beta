cmake_minimum_required(VERSION 3.26)
project(SAM_AUTO)


add_executable(main)
file(GLOB_RECURSE sources CONFIGURE_DEPENDS *.cpp *.h)
target_sources(main PUBLIC ${sources})
set(CMAKE_BUILD_TYPE DEBUG)