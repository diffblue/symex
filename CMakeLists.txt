cmake_minimum_required(VERSION 3.10)
project(symex)

find_program(CCACHE_PROGRAM ccache)
if(CCACHE_PROGRAM)
    set_property(GLOBAL PROPERTY RULE_LAUNCH_COMPILE "${CCACHE_PROGRAM}")
    message(STATUS "Rule launch compile: ${CCACHE_PROGRAM}")
endif()

set(CMAKE_CXX_STANDARD 11)

#   Set the public include locations for a target.
macro(generic_includes name)
    target_include_directories(${name}
            PUBLIC
            ${CBMC_BINARY_DIR}
            ${CBMC_SOURCE_DIR}
            ${CMAKE_CURRENT_BINARY_DIR}
            ${CMAKE_CURRENT_SOURCE_DIR}
            )
endmacro(generic_includes)

add_subdirectory(lib/cbmc)
add_subdirectory(src)

set_target_properties(
        symex

        PROPERTIES
        CXX_STANDARD 11
        CXX_STANDARD_REQUIRED true
)