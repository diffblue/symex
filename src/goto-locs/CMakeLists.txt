file(GLOB_RECURSE sources "*.cpp")
file(GLOB_RECURSE headers "*.h")
add_library(goto-locs
        ${sources}
        ${headers}
        )

generic_includes(goto-locs)
target_link_libraries(goto-locs util)
