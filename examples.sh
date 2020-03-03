#!/bin/bash

for e in mwem.ed.duet adaptive-learning.ed.duet ; do
    echo "================================================================================"
    echo "Running example:" $e
    echo "================================================================================"
    stack run -- check examples/complete/${e}
done
