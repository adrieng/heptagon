# -----------------------------------------------------------  
# -- Get environment
# -----------------------------------------------------------  

## -- Set hostname
## --------------------------
find_program(HOSTNAME_CMD NAMES hostname)
exec_program(${HOSTNAME_CMD} ARGS OUTPUT_VARIABLE HOSTNAME)

set(CTEST_SITE                          "${HOSTNAME}")

## -- Set site / build name
## --------------------------

find_program(UNAME NAMES uname)
macro(getuname name flag)
  exec_program("${UNAME}" ARGS "${flag}" OUTPUT_VARIABLE "${name}")
endmacro(getuname)

getuname(osname -s)
getuname(osrel  -r)
getuname(cpu    -m)

set(CTEST_BUILD_NAME                    "${osname}-${cpu}-prod")

## -- SVN command
## ----------------
find_program(CTEST_GIT_COMMAND NAMES git)

## -- make command
## -----------------
find_program(MAKE NAMES make)

# -----------------------------------------------------------  
# -- build specific
# -----------------------------------------------------------  

set(MODEL                               "Experimental")

## -- DashBoard Root
set(CTEST_DASHBOARD_ROOT                "$ENV{HOME}/automatedBuild")

## -- SRC Dir
#set(CTEST_SOURCE_DIRECTORY              "${CTEST_DASHBOARD_ROOT}/src")
find_program(PWD_CMD NAMES pwd)
exec_program(${PWD_CMD} ARGS OUTPUT_VARIABLE CTEST_SOURCE_DIRECTORY)


## -- BIN Dir                                            
set(CTEST_BINARY_DIRECTORY              "${CTEST_SOURCE_DIRECTORY}/build-${CTEST_BUILD_NAME}")

## -- Build options
#set(OPTION_BUILD                        "-j16")

# -----------------------------------------------------------  
# -- commands
# -----------------------------------------------------------  

## -- Checkout command
if(NOT EXISTS "${CTEST_SOURCE_DIRECTORY}")
	set(CTEST_CHECKOUT_COMMAND     "${CTEST_GIT_COMMAND} clone git+ssh://scm.gforge.inria.fr//gitroot/heptagon/heptagon.git ${CTEST_SOURCE_DIRECTORY}; ${CTEST_GIT_COMMAND} checkout decade")
endif(NOT EXISTS "${CTEST_SOURCE_DIRECTORY}")

## -- Update Command
set(CTEST_UPDATE_COMMAND               "${CTEST_GIT_COMMAND}")

## -- Configure Command
set(CTEST_CONFIGURE_COMMAND            "${CTEST_SOURCE_DIRECTORY}/configure")

## -- Build Command
set(CTEST_BUILD_COMMAND                "${MAKE} ${OPTION_BUILD}")

# -----------------------------------------------------------  
# -- Configure CTest
# -----------------------------------------------------------  

## -- CTest Config
#configure_file($ENV{HOME}/CTestConfiguration/CTestConfig.cmake	${CTEST_SOURCE_DIRECTORY}/CTestConfig.cmake)

## -- CTest Custom
#configure_file($ENV{HOME}/CTestConfiguration/CTestCustom.cmake ${CTEST_BINARY_DIRECTORY}/CTestCustom.cmake)

## -- CTest Testfile
#configure_file($ENV{HOME}/CTestConfiguration/CTestTestfile.cmake ${CTEST_BINARY_DIRECTORY}/CTestTestfile.cmake)

## -- read CTestCustom.cmake file
#ctest_read_custom_files("${CTEST_BINARY_DIRECTORY}")

# -----------------------------------------------------------  
# -- Settings
# -----------------------------------------------------------  

## -- Process timeout in seconds
set(CTEST_TIMEOUT           "7200")

## -- Set output to english
set( $ENV{LC_MESSAGES}      "en_EN" )

# -----------------------------------------------------------  
# -- Run CTest
# -----------------------------------------------------------  

## -- Start
message(" -- Start dashboard ${MODEL} - ${CTEST_BUILD_NAME} --")
ctest_start(${MODEL} TRACK ${MODEL})

## -- Update
message(" -- Update ${MODEL} - ${CTEST_BUILD_NAME} --")
ctest_update(           SOURCE "${CTEST_SOURCE_DIRECTORY}" RETURN_VALUE res)

## -- Run autoreconf
# message(" -- Autoreconf ${MODEL} - ${CTEST_BUILD_NAME} --")
# execute_process(COMMAND "/usr/bin/autoreconf" "-f" "-i" WORKING_DIRECTORY ${CTEST_SOURCE_DIRECTORY} RESULT_VARIABLE autoreconfResult
# 	OUTPUT_VARIABLE autoreconfLog ERROR_VARIABLE autoreconfLog)
# file(WRITE ${CTEST_BINARY_DIRECTORY}/Testing/autoreconf.log "${autoreconfLog}")

## -- Configure	
message(" -- Configure ${MODEL} - ${CTEST_BUILD_NAME} --")
ctest_configure(BUILD  "${CSET_SOURCE_DIRECTORY}" RETURN_VALUE res)

## -- BUILD
message(" -- Build ${MODEL} - ${CTEST_BUILD_NAME} --")
ctest_build(    BUILD  "${CTEST_SOURCE_DIRECTORY}" RETURN_VALUE res)

## -- INSTALL
# message(" -- Install ${MODEL} - ${CTEST_BUILD_NAME} --")
# execute_process(COMMAND "${MAKE} install ${OPTION_BUILD}" WORKING_DIRECTORY ${CTEST_BINARY_DIRECTORY} 
#   RESULT_VARIABLE makeInstallResult OUTPUT_VARIABLE makeInstallLog ERROR_VARIABLE makeInstallLog)
# file(WRITE ${CTEST_BINARY_DIRECTORY}/Testing/makeinstall.log "${makeInstallLog}")

## -- TEST
message(" -- Test ${MODEL} - ${CTEST_BUILD_NAME} --")
ctest_test(     BUILD  "${CTEST_SOURCE_DIRECTORY}" RETURN_VALUE res)


## -- SUBMIT
message(" -- Submit ${MODEL} - ${CTEST_BUILD_NAME} --")
ctest_submit(                                              RETURN_VALUE res)

message(" -- Finished ${MODEL}  - ${CTEST_BUILD_NAME} --")
