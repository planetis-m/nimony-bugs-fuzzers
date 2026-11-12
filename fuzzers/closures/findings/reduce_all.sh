#!/bin/bash
cd /home/ageralis/Projects/nimony-fuzz/closures
cat findings/reduce_list2.txt | xargs -P 1 -I{} sh -c 'timeout 420 python3 -I cfuzz.py reduce findings/raw/{} --budget 100 > findings/raw/{}/reduce.log 2>&1; echo "{} $(tail -1 findings/raw/{}/reduce.log)"'
