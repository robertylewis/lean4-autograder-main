#!/usr/bin/env bash

curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y --default-toolchain leanprover/lean4:nightly-2023-01-16

# ~/.elan/bin/elan default leanprover/lean4:nightly

~/.elan/bin/lean --version

apt-get install -y python3 python3-pip python3-dev

cd /autograder/source

~/.elan/bin/lake update 

~/.elan/bin/lake exe cache get 

~/.elan/bin/lake clean

~/.elan/bin/lake build autograder AutograderTests 
