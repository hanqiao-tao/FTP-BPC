# FTP-BPC
This repository includes the test instances, source codes, and computational results for the **flight test planning (FTP) problem** introduced in [1].

If you encounter any issues or have questions, please feel free to contact taohanqiao19@nudt.edu.cn.

## Instances
All test instances used in this work are stored in the "Instances" folder, with the directory structure detailed as follows.

```text
Instances/                      # Full set of test instances
├── Classical dataset/          # Classical benchmark dataset for the simple assembly line balancing problem of type 1 (SALBP-1) from https://assembly-line-balancing.de/
│   ├── precedence graphs/      # Precedence graph files for classical SALBP-1 benchmarks
│   │   ├── [Full set of .IN2 precedence graph files]
│   │   └── README.DOC
│   └── SALBP data sets.xlsx    # Supplementary summary of classical SALBP-1 benchmark datasets
├── Otto dataset/               # Latest SALBP-1 benchmark datasets
│   ├── large data set_n=100/   # Benchmark dataset proposed by [2]
│   ├── data set_n=110/         # Benchmark dataset generated via the method proposed in [3]
│   ├── data set_n=120/
│   ├── data set_n=130/
│   ├── data set_n=140/
│   ├── data set_n=150/
│   ├── data set_n=160/
│   ├── data set_n=170/
│   ├── data set_n=180/
│   ├── data set_n=190/
│   └── data set_n=200/
└── Configuration/              # Compatible relationships between each pair of task and configuration
    ├── Sensitivity_n/          # Compatible relationships for sensitivity analysis on the number of tasks
    │   └── S_110_3_1.txt to S_200_3_1.txt
    ├── Sensitivity_r/          # Compatible relationships for sensitivity analysis on the versatility level
    │   └── S_100_3_1.txt to S_100_3_10.txt
    └── S_100_1_1.txt to S_100_4_1.txt
                                # Compatible relationships for the main experiments
```

## Algorithm
This repository implements a branch-price-and-cut (BPC) algorithm for exactly solving the FTP.

- The algorithm is implemented in C++ and executed in single-threaded mode.
- All mixed-integer programming (MIP) formulations in this work are solved using the Cardinal Optimizer (COPT) 7.2.11 [4] via its C++ API. The solver is configured to run in single-threaded mode, with all other parameters set to their default values.
- This code has the following required dependencies:
  - **Boost ≥ 1.80.0**   (https://www.boost.org/)
  - **xxHash**           (https://github.com/Cyan4973/xxHash)
- We gratefully acknowledge Prof. Jordi Pereira for kindly sharing the source code developed in his work [5], which served as a valuable reference for our algorithm implementation.
- We directly use the combo algorithm proposed in [6] for solving 0-1 knapsack problem in the separation procedure.

## Computational Results
Full computational results for all test instances are documented in the Excel file "FTP results.xlsx".

## Reference
[1] Tao, H., et al. (2026). Planning the Flight Tests of Newly Developed Aircraft (to be submitted). 

[2] Álvarez-Miranda, E., Pereira, J., & Vilà, M. (2023). Analysis of the simple assembly line balancing problem complexity. Computers & Operations Research, 159, 106323.

[3] Otto, A., Otto, C., & Scholl, A. (2013). Systematic data generation and test design for solution algorithms on the example of SALBPGen for assembly line balancing. European Journal of Operational Research, 228, 33–45.

[4] D. Ge, Q. Huangfu, Z. Wang, J. Wu and Y. Ye. Cardinal Optimizer (COPT) user guide. https://guide.coap.online/copt/en-doc, 2023.

[5] Pereira, J. (2016). Procedures for the bin packing problem with precedence constraints. European Journal of Operational Research, 250, 794–806.

[6] Martello, S., Pisinger, D., & Toth, P. (1999). Dynamic Programming and Strong Bounds for the 0-1 Knapsack Problem. Management Science, 45(3), 414–424.
