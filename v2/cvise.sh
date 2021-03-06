#!/bin/bash

set -eu

cflags="-DBOOST_ALL_NO_LIB -DBOOST_CONTEXT_DYN_LINK -DBOOST_FILESYSTEM_DYN_LINK -DBOOST_PROGRAM_OPTIONS_DYN_LINK -DBOOST_REGEX_DYN_LINK -DBOOST_SYSTEM_DYN_LINK -DBOOST_THREAD_DYN_LINK -DFMT_LOCALE -DFMT_SHARED -DFOLLY_XLOG_STRIP_PREFIXES=\"/home/avj/clones/folly/folly:/home/avj/clones/folly/folly/_build\" -DGFLAGS_IS_A_DLL=0 -DGTEST_LINKED_AS_SHARED_LIBRARY=1 -D_GNU_SOURCE -D_REENTRANT -g -I. -I/home/avj/clones/folly_reduce/v2/folly -std=gnu++1z -finput-charset=UTF-8 -fsigned-char -Wall -Wno-deprecated -Wno-deprecated-declarations -Wno-sign-compare -Wno-unused -Wunused-label -Wunused-result -Wshadow-compatible-local -Wno-noexcept-type -faligned-new -fopenmp -pthread -std=gnu++17 -Werror"

fname="/home/avj/clones/folly_reduce/v2/test.cpp"

g++ -c ${cflags} ${fname} 1>/dev/null 2>&1

output=output.txt

rm -f ${output}

ret=0
g++ -c ${cflags} -DBAD ${fname} 1>${output} 2>&1 || ret=$?

if [[ ${ret} -eq 0 ]]; then
    exit 1
fi

str1="error: ‘__builtin_strlen(((const char*)(&<anonymous>)))’ is not a constant expression"
str2="error: non-constant condition for static assertion"

fgrep "${str1}" ${output} 1>/dev/null 2>&1
fgrep "${str2}" ${output} 1>/dev/null 2>&1

ret=0
grep "error:" ${output} | fgrep -v "${str1}" | fgrep -v "${str2}" || ret=$?

if [[ ${ret} -eq 0 ]]; then
    exit 1
fi

exit 0

# EOF
