Distinct bugs (NN.md), repro files in repros/. log.csv: every raw finding of the 35-min extended run with its bug id.
New: 01 JS f32 literal | 02 j/w keepovf folded crash | 03 LLVM narrow case label | 04 j/w non-int case label |
05 LLVM constant int conversion | 06 LLVM `not` folded literal type | 07 native u64->f64 array element |
08 native uint16(not int8) not zero-extended | 09 native 2-D array store | 10 native staging-register exhaustion |
11 LLVM "(err)" type | 12 native -d:danger segfault. Known: 13 = nativenif#201, 14 = report 90, 15 = report 89.
Baseline (base/, original difffuzz, 10 min, 233 programs): 500025/500185/500232 = 13; 500085/500184 = 07;
500003/500094/500180/500208 = 08-family (uint32 printed with upper bits set, not separately confirmed); 500132 = 09-family.
