#!/bin/bash
# Assemble every findings/repro/*.nif with nifasm and show its disassembly; the matching .s (if any) is the GNU as reference.
cd "$(dirname "$0")/repro"
for f in *.nif; do
  n=${f%.nif}; echo "=== $n"
  /home/ageralis/Projects/nimony/bin/nifasm -o:/tmp/claude-1000/-home-ageralis-Projects-nimony/7cd2a8a0-69d3-48b6-be85-1ec31bd3a385/scratchpad/$n.out $f 2>&1 | head -3
  [ -f /tmp/claude-1000/-home-ageralis-Projects-nimony/7cd2a8a0-69d3-48b6-be85-1ec31bd3a385/scratchpad/$n.out ] && objdump -d -M intel /tmp/claude-1000/-home-ageralis-Projects-nimony/7cd2a8a0-69d3-48b6-be85-1ec31bd3a385/scratchpad/$n.out | sed -n '/main.0>:/,$p' | tail -n +2
  if [ -f $n.s ]; then as --64 -o /tmp/claude-1000/-home-ageralis-Projects-nimony/7cd2a8a0-69d3-48b6-be85-1ec31bd3a385/scratchpad/$n.o $n.s 2>&1 | head -2 && objdump -d -M intel /tmp/claude-1000/-home-ageralis-Projects-nimony/7cd2a8a0-69d3-48b6-be85-1ec31bd3a385/scratchpad/$n.o | tail -n +8 | sed 's/^/  gas: /'; fi
done
