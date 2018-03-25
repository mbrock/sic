#!/usr/bin/env bash
set -ex
code=$(out/bin/Example)
address=$(seth send --create $code)
result=$(seth call $address 'add(int128,int128)' 5 2)
test $result = 0x0000000000000000000000000000000000000000000000000000000000000007
result=$(seth call $address 'add(int128,int128)' 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff 1)
test $result = 0x
result=$(seth call $address 'sub(int128,int128)' 5 2)
test $result = 0x0000000000000000000000000000000000000000000000000000000000000003
result=$(seth call $address 'sub(int128,int128)' 0x8000000000000000000000000000000000000000000000000000000000000000 1)
test $result = 0x
result=$(seth call $address 'mul(int128,int128)' $(bin/ray 5) $(bin/ray 2))
test $result = $(bin/ray 10)
result=$(seth call $address 'mul(int128,int128)' 0x00000000000000000000004f3a68dbc8f03f243baf513267aa9a3ee524f8e028 $(bin/ray 1.000000000000000000000000001))
result=$(seth call $address 'mul(int128,int128)' 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff $(bin/ray 2))
test $result = 0x
