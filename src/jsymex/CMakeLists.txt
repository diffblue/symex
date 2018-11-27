file(GLOB_RECURSE sources "*.cpp")
file(GLOB_RECURSE headers "*.h")
list(REMOVE_ITEM sources
    ${CMAKE_CURRENT_SOURCE_DIR}/jsymex_main.cpp
)

add_library(jsymex-lib ${sources} ${headers})

target_link_libraries(jsymex-lib
    ansi-c
    cpp
    linking
    big-int
    goto-programs
    analyses
    langapi
    xml
    assembler
    solvers
    util
    goto-locs
    goto-symex
    pointer-analysis
    goto-instrument-lib
    path-symex
    java_bytecode
    symex-lib
)

generic_includes(jsymex-lib)

add_executable(jsymex jsymex_main.cpp)

target_link_libraries(jsymex jsymex-lib)
