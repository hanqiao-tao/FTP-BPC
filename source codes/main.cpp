#include "FTP.h"

#pragma region Definition
// control parameters
double runTimeLimit = 3600;         // total time limit for the branch and price and cut
double initTimeLimit = 10;          // total time for obtaining an initial solution
bool logOrNot = true;               // whether to log or output to screen or not
bool addCPcuts = true;              // whether add CP cut or not
bool addTCcuts = false;             // whether add TC cut or not
bool addNonrobustCut = true;        // whether add non-robust cut or not
bool ifExtensionLifting = true;     // whether extend and lift the CP cut or not
bool instanceType;                  // old benchmark or new benchmark

// statstics
double globalUpperbound;            // the best upperbound obtained
double rootLB;                      // the global lowerbound 
int initUB;                         // initial solution(upperbound)

int numNodeExplored;                // the number of nodes explored in the BPC
int maxBBTreeDepth;                 // the maximum deep of the nodes in the BPC
int totalColNum;                    // the number of columns added in the BPC
int CPcutNum;                       // the number of CP cuts added
int TCcutNum;                       // the number of TC cuts added

double totalTime;                   // total time consumption
double LBTime;                      // lower bound consumption
double initTime;                    // initial solution consumption
double pricingTime;                 // time used for solving the pricing problem
double separateCPTime;              // time used for separating CP cuts
double separateTCTime;              // time used for separating TC cuts


bool overTime;                      // whether the BPC stopped due to the time limit or not
bool overStack;                     // whether the BPC stopped due to the size limit of the stack or not

bool initFeasiblity;                // whether the BPC obtains an feasible initial solution
int instanceFeasibility;            // whether the instance is feasible, 1 = feasible, 0 = infeasible, -1 = unknown

// instance
std::string instanceName;
int numTasks;
int timeCap;
int taskTime[NUMTASK];
double taskTimeInv[NUMTASK];
std::vector<std::pair<int, int>> precdenceRelation;
int E[NUMTASK];
int L[NUMTASK];
int numConfig;
std::vector<int> Ck;
std::vector<int> CkBar;
std::vector<int> CkSum;
int CkLabel;

bool adjMatr[NUMTASK][NUMTASK];
int directSucs[NUMTASK][NUMTASK];
int directPreds[NUMTASK][NUMTASK];

bool transMatr[NUMTASK][NUMTASK];
int allSucs[NUMTASK][NUMTASK];
int allPreds[NUMTASK][NUMTASK];


bool gammaMatr[NUMTASK][NUMTASK];
int allGamma[NUMTASK][NUMTASK];

bool configMatr[5][NUMTASK];
bool configMatrTranspose[NUMTASK][5];
char compatibleSet[NUMTASK][5];

int positionalWeight[NUMTASK];
bool potentiallyDominate[NUMTASK][NUMTASK];
boost::unordered_flat_map<CutValue2, std::pair<int, int>, DataHashCut2> cutMap2;
boost::unordered_flat_map<CutValue3, std::pair<int, int>, DataHashCut3> cutMap3;

std::string fileName, fileSolName;
std::string outName;
std::vector<std::vector<int>> incumbentSol;
#pragma endregion

bool FTP_initialize(std::vector<int> ins_dd, int ins_c)
{
    std::vector<std::string> FILES = { "ARC83.IN2", "ARC111.IN2", "BARTHOL2.IN2", "BARTHOLD.IN2", "BOWMAN8.IN2", "BUXEY.IN2", "GUNTHER.IN2", "HAHN.IN2",
                             "HESKIA.IN2", "JACKSON.IN2", "JAESCHKE.IN2", "KILBRID.IN2", "LUTZ1.IN2", "LUTZ2.IN2", "LUTZ3.IN2", "MANSOOR.IN2", "MERTENS.IN2",
                             "MITCHELL.IN2", "MUKHERJE.IN2", "ROSZIEG.IN2", "SAWYER30.IN2", "SCHOLL.IN2", "TONGE70.IN2", "WARNECKE.IN2", "WEE-MAG.IN2" };
    globalUpperbound = NUMTASK;
    rootLB = 0;
    numNodeExplored = 0;
    maxBBTreeDepth = 0;
    totalColNum = 0;
    CPcutNum = 0;
    TCcutNum = 0;

    totalTime = 0.0;
    initTime = 0;
    pricingTime = 0.0;
    LBTime = 0.0;
    separateCPTime = 0.0;
    separateTCTime = 0.0;

    overTime = false;
    overStack = false;

    initFeasiblity = false;
    instanceFeasibility = -1;

    timeCap = 0;
    memset(taskTime, 0, sizeof(taskTime));
    memset(taskTimeInv, 0, sizeof(taskTimeInv));
    std::vector<std::pair<int, int>>().swap(precdenceRelation);
    memset(E, 0, sizeof(E));
    memset(L, 0, sizeof(L));

    memset(adjMatr, 0, sizeof(adjMatr));
    memset(directSucs, 0, sizeof(directSucs));
    memset(directPreds, 0, sizeof(directPreds));

    memset(transMatr, 0, sizeof(transMatr));
    memset(allSucs, 0, sizeof(allSucs));
    memset(allPreds, 0, sizeof(allPreds));

    memset(gammaMatr, 0, sizeof(gammaMatr));
    memset(allGamma, 0, sizeof(allGamma));

    memset(configMatr, 0, sizeof(configMatr));
    memset(configMatrTranspose, 0, sizeof(configMatrTranspose));
    memset(compatibleSet, 0, sizeof(compatibleSet));
    memset(configurationSubsetC, 0, sizeof(configurationSubsetC));
    memset(dualCol, 0, sizeof(dualCol));
    memset(xSol, 0, sizeof(xSol));
    memset(ySol, 0, sizeof(ySol));

    memset(positionalWeight, 0, sizeof(positionalWeight));
    memset(potentiallyDominate, 0, sizeof(potentiallyDominate));

    cutMap2 = boost::unordered_flat_map<CutValue2, std::pair<int, int>, DataHashCut2>();
    cutMap3 = boost::unordered_flat_map<CutValue3, std::pair<int, int>, DataHashCut3>();
    
    std::string fileName, fileSolName;
    if (numTasks == 20)
    {
        instanceName = "instance_n=20_" + std::to_string(ins_dd[ins_c]) + ".alb";
        fileName = "E:\\0.ฬีบบวล\\6.Studies\\Benchmark\\01 SALBP dataset\\Otto dataset\\small data set_n=20\\instance_n=20_" + std::to_string(ins_dd[ins_c]) + ".alb";
    }
    else if (numTasks == 50)
    {
        instanceName = "instance_n=50_" + std::to_string(ins_dd[ins_c]) + ".alb";
        fileName = "E:\\0.ฬีบบวล\\6.Studies\\Benchmark\\01 SALBP dataset\\Otto dataset\\medium data set_n=50\\instance_n=50_" + std::to_string(ins_dd[ins_c]) + ".alb";
    }
    else if (numTasks == 100)
    {
        instanceName = "instance_n=100_" + std::to_string(ins_dd[ins_c]) + ".alb";
        fileName = "E:\\0.ฬีบบวล\\6.Studies\\Benchmark\\01 SALBP dataset\\Otto dataset\\large data set_n=100\\instance_n=100_" + std::to_string(ins_dd[ins_c]) + ".alb";
    }
    else if (numTasks > 100 && numTasks <= 250)
    {
        instanceName = "instance_n=" + std::to_string(numTasks) + "_" + std::to_string(ins_dd[ins_c]) + ".alb";
        fileName = "E:\\0.ฬีบบวล\\6.Studies\\Benchmark\\01 SALBP dataset\\Otto dataset\\data set_n=" + std::to_string(numTasks) + "\\instance_n="+ std::to_string(numTasks)+"_" + std::to_string(ins_dd[ins_c]) + ".alb_";
    }
    else if (numTasks == 1000)
    {
        instanceName = "instance_n=1000_" + std::to_string(ins_dd[ins_c]) + ".alb";
        fileName = "E:\\0.ฬีบบวล\\6.Studies\\Benchmark\\01 SALBP dataset\\Otto dataset\\very large data set_n=1000\\instance_n=1000_" + std::to_string(ins_dd[ins_c]) + ".alb";
    }
    else if (numTasks == 0)
    {
        instanceName = FILES[ins_c];
        fileName = "E:\\0.ฬีบบวล\\6.Studies\\Benchmark\\01 SALBP dataset\\Classical dataset\\precedence graphs\\" + instanceName;
    }
    else { std::cout << "fileName error!"; exit(-1); }
    fileSolName = ".\\instance_n=" + std::to_string(numTasks) + "_" + std::to_string(ins_dd[ins_c]) + ".sol";
    bool read_ins;
    std::vector<std::vector<int>>().swap(incumbentSol);
    if (numTasks > 0) 
    {
        read_ins = instanceReader(fileName);
        std::cout << "instance_n = " << numTasks << "_" << ins_dd[ins_c] << ".alb " << std::endl;
    }
    else if (numTasks == 0)
    {
        if (numConfig > 1) std::cerr << "number of configuration error! should be 1!\n";
        read_ins = instanceReaderOld(fileName);
        std::cout << FILES[ins_c] << "\t";
    }
    else  std::cerr << "number of tasks error!\n";
    return read_ins;
}

void FTP_trans_closure_warshall()
{
    memcpy(transMatr, adjMatr, sizeof(adjMatr));
    int i, j, delta, k;

    for (delta = 2; delta < numTasks; delta++)
    {
        for (i = 1; i <= numTasks - delta; i++)
        {
            j = i + delta;
            if (transMatr[i][j]) continue;

            for (k = i + 1; k < j; k++)
            {
                if (transMatr[i][k] && transMatr[k][j])
                {
                    transMatr[i][j] = true;
                    break;
                }
            }
        }
    }
}

void FTP_matrix_to_graph_vec()
{
    //put all direct and indirect successors of each job into the allSucs structure
    for (int i = 1; i <= numTasks; i++)
    {
        for (int j = 1; j < i; j++)
        {
            if (transMatr[j][i])
            {
                allPreds[i][0]++;
                allPreds[i][allPreds[i][0]] = j;
                if (adjMatr[j][i])
                {
                    directPreds[i][0]++;
                    directPreds[i][directPreds[i][0]] = j;
                }
            }
            else 
            {
                gammaMatr[i][j] = true;
                allGamma[i][0]++;
                allGamma[i][allGamma[i][0]] = j;
            }
        }
        for (int j = i + 1; j <= numTasks; j++)
        {
            if (transMatr[i][j])
            {
                allSucs[i][0]++;
                allSucs[i][allSucs[i][0]] = j;
                if (adjMatr[i][j])
                {
                    directSucs[i][0]++;
                    directSucs[i][directSucs[i][0]] = j;
                }
            }
            else
            {
                gammaMatr[i][j] = true;
                allGamma[i][0]++;
                allGamma[i][allGamma[i][0]] = j;
            }
        }
        if (directSucs[i][0] > 127) std::cerr << "out of range!\n";
    }
    
    // transpose
    for (int i = 1; i <= numTasks; i++) 
    {
        for (int k = 1; k <= numConfig; k++) 
        {
            configMatrTranspose[i][k] = configMatr[k][i];
        }
    }
}

void FTP_compute_C() 
{
    int shortest_path[NUMTASK];		// longest path from 0 to i
    memset(shortest_path, 0, sizeof(shortest_path));
    // shortest path
    for (int i = 1; i <= numTasks; i++)
    {
        for (int num = 1; num <= directPreds[i][0]; num++)
        {
            int j = directPreds[i][num];
            if (shortest_path[j] < shortest_path[i]) continue;
            shortest_path[i] = shortest_path[j] + 1;
        }
    }
    // compute positional weight
    for (int i = 1; i <= numTasks; i++)
    {
        int sum = taskTime[i];
        for (int j = i + 1; j <= numTasks; j++)
        {
            if (transMatr[i][j])
            {
                sum = sum + taskTime[j];
            }
        }
        positionalWeight[i] = sum;
    }
    for (int i = 1; i <= numTasks; i++)
    {
        for (int k = 1; k <= numConfig; k++)
        {
            if (configMatr[k][i])
            {
                compatibleSet[i][0]++;
                compatibleSet[i][compatibleSet[i][0]] = k;
            }
        }
    }
    // first Ck, prop 3.1
    CkBar = std::vector<int>(numConfig + 1);
    for (int k = 1; k <= numConfig; k++)
    {
        int sum_Ik_t = 0;
        int numTasks_k = 0;
        int L = 0;
        for (int i = 1; i <= numTasks; i++)
        {
            if (shortest_path[i] > L && configMatr[k][i])
            {
                L = shortest_path[i];
            }
        }
        for (int i = 1; i <= numTasks; i++)
        {
            if (configMatr[k][i])
            {
                sum_Ik_t += taskTime[i];
                numTasks_k++;
            }
        }
        CkBar[k] = L + 1 + (int)(ceil(2 * (double) sum_Ik_t / timeCap - intTolerance));
        CkBar[k] = CkBar[k] > numTasks_k ? numTasks_k : CkBar[k];
    }
    Ck = CkBar;
    //CkLabel = 1;
    CkSum = std::vector<int>(numConfig + 1, 0);
    for (int k = 1; k <= numConfig; k++)
    {
        for (int kk = 1; kk <= k; kk++)
        {
            CkSum[k] += Ck[kk];
        }
    }
}

// Duration augmentation rule
bool DAR()
{
    bool rebuild = true;
    while (rebuild) 
    {
        rebuild = false;
        for (int i = 1; i <= numTasks; i++)
        {
            if (taskTime[i] < timeCap)
            {
                bool flag = true;
                for (int j = 1; j < i && flag; j++)
                {
                    if (!transMatr[j][i] && taskTime[i] + taskTime[j] <= timeCap)
                    {
                        for (int k = 1; k <= numConfig; k++) 
                        {
                            if (configMatr[k][i] && configMatr[k][j]) 
                            {
                                flag = false;
                                break;
                            }
                        }
                    }
                }
                for (int j = i + 1; j <= numTasks && flag; j++)
                {
                    if (!transMatr[i][j] && taskTime[i] + taskTime[j] <= timeCap) 
                    {
                        for (int k = 1; k <= numConfig; k++)
                        {
                            if (configMatr[k][i] && configMatr[k][j])
                            {
                                flag = false;
                                break;
                            }
                        }
                    }
                }
                if (flag)
                {
                    rebuild = true;
                    taskTime[i] = timeCap;
                }
            }
        }
    }
    for (int i = 1; i <= numTasks; i++)taskTimeInv[i] = 1 / (double)taskTime[i];
    return rebuild;
}

int main(void)
{
    numTasks = -6;
    try
    {
        if (numTasks > 0) 
        {
            std::vector<int> ins_dd;
            for (int i = 143; i <= 150; i++) ins_dd.push_back(i);
            outName = ".//result-BP-" + std::to_string(numTasks) + "-add.txt";
            writeOutHeader();
            instanceType = true;   // New benchmark
            CkLabel = 1;
            for (int instanceId = 0; instanceId < ins_dd.size(); instanceId++)
            {
                numConfig = 2;
                while (numConfig <= 4)
                {
                    // initialize
                    bool read_ins = FTP_initialize(ins_dd, instanceId);
                    if (read_ins)
                    {
                        // read instance
                        std::string filename = "E:\\0.ฬีบบวล\\6.Studies\\Benchmark\\02 FTSP dataset\\FTP\\S_" + std::to_string(numTasks) + "_" + std::to_string(numConfig) + "_" + std::to_string(1) + ".txt";
                        configurationReader(filename);
                        // preprocessing
                        FTP_trans_closure_warshall();
                        FTP_matrix_to_graph_vec();
                        FTP_compute_C();
                        DAR();

                        BPCInitialSolution(); // obtaining a high-quality initial solution
                        totalTime += (initTime + LBTime);
                        check();// to be deleted

                        if (instanceFeasibility != 0 && initUB > rootLB) branchPriceAndCut();
                        else globalUpperbound = initUB;
                        writeOutLog();
                    }
                    else
                    {

                        writeLogFile("");
                        writeLogFileByEntry("fail!");
                    }
                    numConfig++;
                }
            }
        }
        else if (numTasks == 0) 
        {
            std::vector<int> ins_dd;
            for (int i = 1; i <= 450; i++) ins_dd.push_back(i);
            outName = ".//result-oldBenchmark.txt";
            writeOutHeader();
            numConfig = 1;
            instanceType = false;   // Old benchmark
            std::vector<std::vector<int>> TcapData = {
            {3786,3985,4206,4454,4732,5048,5408,5824,5853,6309,6842,6883,7571,8412,8898,10816},
            {5755,5785,6016,6267,6540,6837,7162,7520,7916,8356,8847,9400,10027,10743,11378,11570,17067},
            {84,85,87,89,91,93,95,97,99,101,104,106,109,112,115,118,121,125,129,133,137,142,146,152,157,163,170},
            {403,434,470,513,564,626,705,805},
            {20},
            {27,30,33,36,41,47,54},
            {41,44,49,54,61,69,81},
            {2004,2338,2806,3507,4676},
            {138,205,216,256,324,342},
            {7,9,10,13,14,21},
            {6,7,8,10,18},
            {56,57,62,69,79,92,110,111,138,184 },
            {1414,1572,1768,2020,2357,2828},
            {11,12,13,14,15,16,17,18,19,20,21},
            {75,79,83,87,92,97,103,110,118,127,137,150},
            {48,62,94},
            {6,7,8,10,15,18},
            {14,15,21,26,35,39},
            {176,183,192,201,211,222,234,248,263,281,301,324,351 },
            {14,16,18,21,25,32},
            {25,27,30,33,36,41,47,54,75},
            {1394,1422,1452,1483,1515,1548,1584,1620,1659,1699,1742,1787,1834,1883,1935,1991,2049,2111,2177,2247,2322,2402,2488,2580,2680,2787},
            {160,168,176,185,195,207,220,234,251,270,293,320,364,410,468,527},
            {54,56,58,60,62,65,68,71,74,78,82,86,92,97,104,111},
            {28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,45,46,47,49,50,52,54,56}};
            
            for (int instanceId = 0; instanceId < 25; instanceId++)
            {
                for (int t = 0; t < TcapData[instanceId].size(); t++) 
                {
                    numTasks = 0;
                    
                    bool read_ins = FTP_initialize(ins_dd, instanceId);
                    memset(configMatr, true, sizeof(configMatr));
                    if (read_ins) 
                    {
                        timeCap = TcapData[instanceId][t];
                        std::cout << timeCap << std::endl;

                        // preprocessing
                        FTP_trans_closure_warshall();
                        FTP_matrix_to_graph_vec();
                        FTP_compute_C();
                        DAR();

                        BPCInitialSolution(); // obtaining a high-quality initial solution
                        totalTime += (initTime + LBTime);

                        if (instanceFeasibility != 0 && initUB > rootLB) branchPriceAndCut();
                        writeOutLog();
                    }
                    else
                    {

                        writeLogFile("");
                        writeLogFileByEntry("fail!");
                    }
                }
                
            }
        }
        else if (numTasks == -1) 
        {
            numTasks = 100;
            outName = ".//sensitive-analysis-1-5.txt";
            writeOutHeader();
            instanceType = true;   // New benchmark
            CkLabel = 1;
            std::vector<int> ins_dd;
            for (int i = 301; i <= 375; i++) ins_dd.push_back(i);
            // sensitivity analysis
            numConfig = 3;
            for (int p = 1; p <= 5; p++)
            {
                for (int instanceId = 0; instanceId < ins_dd.size(); instanceId++)
                {
                    bool read_ins = FTP_initialize(ins_dd, instanceId);
                    if (read_ins) 
                    {
                        std::string filename = "E:\\0.ฬีบบวล\\6.Studies\\Benchmark\\02 FTSP dataset\\Sensitive analysis\\S_" + std::to_string(numTasks) + "_" + std::to_string(numConfig) + "_" + std::to_string(p) + ".txt";
                        configurationReader(filename);
                        // preprocessing
                        FTP_trans_closure_warshall();
                        FTP_matrix_to_graph_vec();
                        FTP_compute_C();
                        DAR();

                        BPCInitialSolution(); // obtaining a high-quality initial solution
                        totalTime += (initTime + LBTime);

                        if (instanceFeasibility != 0 && initUB > rootLB) branchPriceAndCut();
                        else globalUpperbound = initUB;
                        writeOutLog();
                    }
                }
            }
        }
        else if (numTasks == -2) 
        {
            std::vector<int> ins_dd;
            for (int i = 1; i <= 75; i++) ins_dd.push_back(i);
            instanceType = true;   // New benchmark
            CkLabel = 1;
            numTasks = 160;
            numConfig = 3;
            outName = ".//sensitive-analysis-" + std::to_string(numTasks) + ".txt";
            writeOutHeader();
            for (int instanceId = 0; instanceId < ins_dd.size(); instanceId++)
            {
                bool read_ins = FTP_initialize(ins_dd, instanceId);
                if (read_ins)
                {
                    // read instance
                    std::string filename = "E:\\0.ฬีบบวล\\6.Studies\\Benchmark\\02 FTSP dataset\\FTP\\S_" + std::to_string(numTasks) + "_" + std::to_string(numConfig) + "_" + std::to_string(1) + ".txt";
                    configurationReader(filename);
                    // preprocessing
                    FTP_trans_closure_warshall();
                    FTP_matrix_to_graph_vec();
                    FTP_compute_C();
                    DAR();

                    BPCInitialSolution(); // obtaining a high-quality initial solution
                    totalTime += (initTime + LBTime);

                    if (instanceFeasibility != 0 && initUB > rootLB) branchPriceAndCut();
                    else globalUpperbound = initUB;
                    writeOutLog();
                }
                else
                {
                    writeLogFile("");
                    writeLogFileByEntry("fail!");
                }
            }
        }
        else if (numTasks <= -3 && numTasks >= -6) 
        {
            CkLabel = -1 - numTasks;        // 2, 3, 4, 5
            numTasks = 100;
            outName = ".//sensitive-analysis-Ck" + std::to_string(CkLabel) + ".txt";
            writeOutHeader();
            instanceType = true;   // New benchmark
            std::vector<int> ins_dd;
            for (int i = 301; i <= 375; i++) ins_dd.push_back(i);
            // sensitivity analysis
            numConfig = 3;
            instanceType = true;   // New benchmark
            for (int instanceId = 0; instanceId < ins_dd.size(); instanceId++) 
            {
                // initialize
                bool read_ins = FTP_initialize(ins_dd, instanceId);
                if (read_ins)
                {
                    // read instance
                    std::string filename = "E:\\0.ฬีบบวล\\6.Studies\\Benchmark\\02 FTSP dataset\\FTP\\S_" + std::to_string(numTasks) + "_" + std::to_string(numConfig) + "_" + std::to_string(1) + ".txt";
                    configurationReader(filename);
                    // preprocessing
                    FTP_trans_closure_warshall();
                    FTP_matrix_to_graph_vec();
                    FTP_compute_C();
                    DAR();

                    BPCInitialSolution(); // obtaining a high-quality initial solution
                    totalTime += (initTime + LBTime);
                    check();// to be deleted

                    if (instanceFeasibility != 0 && initUB > rootLB) branchPriceAndCut();
                    else globalUpperbound = initUB;
                    writeOutLog();
                }
                else
                {

                    writeLogFile("");
                    writeLogFileByEntry("fail!");
                }
            }
        }
    }
    catch (...)
    {
        std::cout << "Unknown exception caught" << std::endl;
        system("pause");
    }
    return 2026;
}
