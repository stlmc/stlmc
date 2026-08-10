cmake_minimum_required(VERSION 3.15)
project(stlmc)

install(FILES ${CMAKE_SOURCE_DIR}/3rd_party/dReal3/dReal DESTINATION stlmc/3rd_party/dReal3 
    PERMISSIONS OWNER_EXECUTE OWNER_WRITE OWNER_READ
                GROUP_EXECUTE GROUP_READ)
