#!/usr/bin/env bash

zip -r autograder.zip AutograderTests/ PythonScripts/ lakefile.lean lean-toolchain Main.lean run_autograder setup.sh autograder_config.json
