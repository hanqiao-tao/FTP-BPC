// The branch-price-and-cut algorithm.
// First, we try to generate a initial solution and compute lower bounds to prove optimality. These operations are limited in 1 minutes.
// Second, go to the B&B tree, and perform the column & row generation procedure
// Finally, record the solution status (optimal, feasible, infeasible or unknown), and clear the memory
#include "FTP.h"

static std::vector<std::vector<std::array<bool, NUMTASK + 14>>> FTPColumn;
static std::vector<boost::unordered_flat_map<std::array<bool, NUMTASK + 14>, int>> FTPColumnPool;
static boost::unordered_flat_map<std::array<bool, NUMTASK + 14>, int> ::iterator itCol;
Node* root = new Node();
int configurationSubset[16][5] = { 0 };
int configurationSubsetC[16][5] = { 0 };
int configurationSubsetNumber = 0;
int precCapList[NUMTASK];
int sucsCapList[NUMTASK];
int forbiddenSetC[NUMTASK * 4];
int forbiddenSetCid[NUMTASK * 4];

double xSol[NUMTASK][NUMTASK];
double ySol[NUMTASK][5];
double lambSol[NUMTASK][MAXCOL];
int lambSize[NUMTASK];
int lambIdList[NUMTASK][MAXCOL];
double dualCol[NUMTASK + 14];

static int* cut_2;
static int* cut_3;
static boost::unordered_flat_map<CutValue2, std::pair<int, int>, DataHashCut2>::iterator itBPC2;
static boost::unordered_flat_map<CutValue3, std::pair<int, int>, DataHashCut3>::iterator itBPC3;
int* minDist;

static double** mu = NULL;
static double* pi = NULL;
static double** theta = NULL;
static double* newColX;
static double* newColCut;

static int* Bipartite[NUMTASK];         // adjacent table for the bipartite graph
static int* match;					    // match[i] stores which point in V2 is matched with i in V1; -1, otherwise
static bool* vis;					    // vis[i] stores whether i in V2 is visited or not in DFS
static bool feasible_config[5][NUMTASK];

static bool dfs(int u)
{
    int i;
    for (i = 1; i <= Bipartite[u][0]; i++) {
        int v = Bipartite[u][i];
        if (!vis[v]) {
            vis[v] = true;
            if (match[v] == -1 || dfs(match[v])) {
                match[v] = u;// store the edge
                return true;
            }
        }
    }
    return false;
}

// Hungarian algorithm
static inline bool hungarian(int* taskPosition, int depth)
{
    int res = 0;
    // construct the bipartite graph
    for (int i = 0; i <= numTasks; i++)
    {
        MALLOC(Bipartite[i], CkSum[numConfig] + 1, int);
        Bipartite[i][0] = 0;
    }
    memset(feasible_config, 1, sizeof(feasible_config));
    for (int k = 1; k <= numConfig; k++)
    {
        for (int i = 1; i <= numTasks; i++)
        {
            if (!configMatr[k][i])
            {
                feasible_config[k][taskPosition[i]] = 0;
            }
        }
    }
    for (int k = 1; k <= numConfig; k++)
    {
        for (int u = 1; u <= depth; u++)
        {
            if (feasible_config[k][u] == 1)
            {
                for (int r = 1; r <= Ck[k]; r++)
                {
                    Bipartite[u][0]++;
                    Bipartite[u][Bipartite[u][0]] = CkSum[k - 1] + r;
                }
            }
        }
    }
    // DFS
    MALLOC(match, CkSum[numConfig] + 1, int);
    MALLOC(vis, CkSum[numConfig] + 1, bool);
    memset(match, -1, (CkSum[numConfig] + 1) * sizeof(int));
    for (int u = 1; u <= depth; u++)
    {
        memset(vis, false, (CkSum[numConfig] + 1) * sizeof(bool));
        if (dfs(u)) res++;
    }
    for (int i = 0; i <= numTasks; i++)
    {
        free(Bipartite[i]);
        Bipartite[i] = NULL;
    }

    free(vis);
    vis = NULL;
    if (res == depth) return true;
    return false;
}

void BPCInitialSolution()
{
    computeMachineLB();   // compute machine scheduling-based lower bound

    switch (CkLabel) 
    {
    case 2:
        for (int k = 1; k <= numConfig; k++)
        {
            Ck[k] = (int)floor(0.75 * (double)Ck[k] + 0.25 * (double)rootLB / (double)numConfig + intTolerance);
        }
        CkLabel = 0;
        break;
    case 3:
        for (int k = 1; k <= numConfig; k++)
        {
            Ck[k] = (int)floor(0.5 * (double)Ck[k] + 0.5 * (double)rootLB / (double)numConfig + intTolerance);
        }
        CkLabel = 0;
        break;
    case 4:
        for (int k = 1; k <= numConfig; k++)
        {
            Ck[k] = (int)floor(0.25 * (double)Ck[k] + 0.75 * (double)rootLB / (double)numConfig + intTolerance);
        }
        CkLabel = 0;
        break;
    case 5:
        for (int k = 1; k <= numConfig; k++)
        {
            Ck[k] = (int)ceil((double)rootLB / (double)numConfig - intTolerance);
        }
        CkLabel = 0;
        break;
    default:
        CkLabel = 1;
    }
    CkSum = std::vector<int>(numConfig + 1, 0);
    for (int k = 1; k <= numConfig; k++)
    {
        for (int kk = 1; kk <= k; kk++)
        {
            CkSum[k] += Ck[kk];
        }
    }
    if (rootLB == numTasks) // trivial case
    {
        initFeasiblity = 1;
        instanceFeasibility = 1;
        incumbentSol.push_back(std::vector<int>(numTasks + 1));
        incumbentSol[0][0] = numTasks;
        for (int i = 1; i <= numTasks; i++) incumbentSol[0][i] = i;
        return;
    }
    bdp(1);
    initUB = incumbentSol[0][0];
    if (initFeasiblity)
    {
        if (incumbentSol[0][0] == rootLB) return;
        computeDWLB();
        if (incumbentSol[0][0] == rootLB) return;
        ILS();
        initUB = incumbentSol[0][0];
        if (incumbentSol[0][0] == rootLB) return;
        bdp(0); 
        initUB = incumbentSol[0][0];
        if (incumbentSol[0][0] == rootLB) return;
        cyclicBestFirstSearch();
        initUB = incumbentSol[0][0];
        if (incumbentSol[0][0] == rootLB) return;
    }
    else // BPC fails to obtain a feasible initial solution 
    {
        incumbentSol.push_back(std::vector<int>(numTasks + 1, 0));
        for (int k = 1; k <= numConfig; k++) incumbentSol[0][0] += Ck[k];
        incumbentSol.push_back(std::vector<int>(incumbentSol[0][0] + 1));
        for (int i = 1; i <= numTasks; i++) L[i] = incumbentSol[0][0] - (int)floor(tailsLB[i] + intTolerance);
    }
}

static void genForbiddenSetLoad(int pos, int remainingT, int* forbiddenSet, bool* configFeasible)
{
    if (forbiddenSet[0] >= numConfig) return;
    if (remainingT < taskTime[pos]) return;
    int begin = forbiddenSetCid[forbiddenSetCid[0]] + 1;
    int end = begin + forbiddenSet[0];
    if (end >= NUMTASK * 4) return;      // avoid array out of bounds

    int count = 0;
    for (int k = 1; k <= numConfig; k++)
    {
        if (configFeasible[k] && configMatrTranspose[pos][k]) count++;
    }
    if (count == 0)
    {
        // we find a forbidden set satisfying capacity constraints
        // assign
        forbiddenSet[0]++;
        forbiddenSet[forbiddenSet[0]] = pos;
        // store
        forbiddenSetCid[0]++;
        forbiddenSetCid[forbiddenSetCid[0]] = end;
        memcpy(&forbiddenSetC[begin], &forbiddenSet[1], forbiddenSet[0] * sizeof(int));
        //disassign
        forbiddenSet[forbiddenSet[0]] = 0;
        forbiddenSet[0]--;
        return;
    }
    else
    {
        // assign
        remainingT -= taskTime[pos];
        bool configFeasible_old[5];
        memcpy(configFeasible_old, configFeasible, 5);
        for (int k = 1; k <= numConfig; k++) configFeasible[k] = configFeasible[k] && configMatrTranspose[pos][k];
        forbiddenSet[0]++;
        forbiddenSet[forbiddenSet[0]] = pos;
        for (int i = pos + 1; i <= numTasks; i++) genForbiddenSetLoad(i, remainingT, forbiddenSet, configFeasible);
        //disassign
        forbiddenSet[forbiddenSet[0]] = 0;
        forbiddenSet[0]--;
        memcpy(configFeasible, configFeasible_old, 5);
        remainingT += taskTime[pos];
    }
}

static void BPCCutsPreparation()
{
    // for non-robust cut
    clock_t start = clock();
    if (numConfig > 1 && addNonrobustCut)
    {
        memset(configurationSubset, 0, sizeof(configurationSubset));
        memset(configurationSubsetC, 0, sizeof(configurationSubsetC));
        configurationSubsetNumber = int(pow(2, numConfig)) - 2; // remove empty set and universe
        int tmp, tag = 0;
        for (int i = 0; i <= configurationSubsetNumber; i++)
        {
            tmp = tag;
            tag++;
            for (int j = 1; j <= numConfig; j++)
            {
                if (tmp & 0x1)
                {
                    configurationSubset[i][j] = 1;
                }
                tmp >>= 1;
            }
        }
        for (int i = 1; i <= configurationSubsetNumber; i++)
        {
            for (int j = 1; j <= numConfig; j++)
            {
                if (configurationSubset[i][j] == 0)
                {
                    configurationSubsetC[i][0]++;
                    configurationSubsetC[i][configurationSubsetC[i][0]] = j;
                }
            }
        }
    }
    else configurationSubsetNumber = 0;
    totalTime += double(clock() - start) / CLKTCK;
    // for pricing problem
    start = clock();
    int poisitionInit = 0;
    int taskCount, kCount, tmpSize, tmpSize2, ii, change = 0;
    register double ac, ac_2, ej, lj;
    int tmpChar;
    int tmp[NUMTASK] = { 0 };
    int tmp2[NUMTASK] = { 0 };
    int listPricing[NUMTASK];
    register double* ptr1, *ptr2;
    register int* tmpData, *tmpData2;
    std::pair<int, int> res;
    change = 1;
    for (int i = 1; i <= numTasks; i++) listPricing[i] = i;
    while (change >= 0)
    {
        change = -1;
        for (int i = 1; i < numTasks; i++)
        {
            if (apply[listPricing[i]] < apply[listPricing[i + 1]])
            {
                change = listPricing[i];
                listPricing[i] = listPricing[i + 1];
                listPricing[i + 1] = change;
            }
        }
    }
    for (int i = 1; i <= numTasks; i++) 
    {
        if (apply[listPricing[i]] == 0) 
        {
            change = i;
            break;
        }
    }
    change = change > 20 ? 20 : change;
    for (int taskCount = 1; taskCount <= change; taskCount++) listPricing[taskCount] = listPricing[taskCount] * NUMTASK;

    cutMap2.reserve(4950);
    CutValue2 val2;
    for (int j1 = 1; j1 <= numTasks; j1++)
    {
        val2.taskSet[0] = j1;
        for (int j2 = j1 + 1; j2 <= numTasks; j2++)
        {
            if (transMatr[j1][j2]) continue;
            tmp[0] = 0;
            tmp2[0] = 0;
            for (int j = 1; j <= numTasks; j++)
            {
                if (transMatr[j][j1] || transMatr[j][j2])
                {
                    tmp2[0]++;
                    tmp2[tmp2[0]] = j;
                }
                else if (transMatr[j1][j] || transMatr[j2][j])
                {
                    tmp[0]++;
                    tmp[tmp[0]] = j;
                }
            }
            if (tmp[0] == 0 && tmp2[0] == 0) continue;
            ptr1 = dataLB;
            tmpSize = tmp[0];
            lj = 0.0;
            tmpSize2 = tmp2[0];
            ej = 0.0;
            res = std::make_pair(0, 0);
            tmpData = tmp;
            tmpData2 = tmp2;
            // dual feasible function
            for (kCount = 0; kCount < kMax; kCount++, ptr1 += NUMTASKSQUARE)
            {
                ac = ptr1[j1] + ptr1[j2];
                ac_2 = ac;
                for (ii = 1, tmpData = &tmp[1]; ii <= tmpSize; ii++, tmpData++) ac += ptr1[*tmpData];
                lj = lj < ac ? ac : lj;

                for (ii = 1, tmpData2 = &tmp2[1]; ii <= tmpSize2; ii++, tmpData2++) ac_2 += ptr1[*tmpData2];
                ej = ej < ac_2 ? ac_2 : ej;
                for (taskCount = 1; taskCount < change; taskCount++)
                {
                    ptr2 = ptr1 + listPricing[taskCount];
                    ac = ptr2[j1] + ptr2[j2];
                    ac_2 = ac;
                    for (ii = 1, tmpData = &tmp[1]; ii <= tmpSize; ii++, tmpData++) ac += ptr2[*tmpData];
                    lj = lj < ac ? ac : lj;

                    for (ii = 1, tmpData2 = &tmp2[1]; ii <= tmpSize2; ii++, tmpData2++) ac_2 += ptr2[*tmpData2];
                    ej = ej < ac_2 ? ac_2 : ej;
                }
            }
            res.first = char(int(ceil(lj - intTolerance)));
            res.second = char(int(ceil(ej - intTolerance)));
            if (res.first == 0 && res.second == 0) continue;
            val2.taskSet[1] = j2;
            cutMap2.emplace(make_pair(val2, res));
        }
    }
    cut_2 = new int[cutMap2.size() * 4 + 1];
    cut_2[0] = cutMap2.size() * 4;
    ii = 1;
    for (itBPC2 = cutMap2.begin(); itBPC2 != cutMap2.end(); itBPC2++)
    {
        cut_2[ii] = itBPC2->first.taskSet[0];
        cut_2[ii + 1] = itBPC2->first.taskSet[1];
        cut_2[ii + 2] = itBPC2->second.first;
        cut_2[ii + 3] = itBPC2->second.second;
        ii += 4;
    }

    cutMap3.reserve(150000);
    CutValue3 val3;
    for (int j1 = 1; j1 <= numTasks; j1++)
    {
        val3.taskSet[0] = j1;
        for (int j2 = j1 + 1; j2 <= numTasks; j2++)
        {
            if (transMatr[j1][j2]) continue;
            val3.taskSet[1] = j2;
            for (int j3 = j2 + 1; j3 <= numTasks; j3++)
            {
                if (transMatr[j1][j3] || transMatr[j2][j3]) continue;
                tmp[0] = 0;
                tmp2[0] = 0;
                for (int j = 1; j <= numTasks; j++)
                {
                    if (transMatr[j][j1] || transMatr[j][j2] || transMatr[j][j3])
                    {
                        tmp2[0]++;
                        tmp2[tmp2[0]] = j;
                    }
                    else if (transMatr[j1][j] || transMatr[j2][j] || transMatr[j3][j])
                    {
                        tmp[0]++;
                        tmp[tmp[0]] = j;
                    }
                }
                if (tmp[0] == 0 && tmp2[0] == 0) continue;
                ptr1 = dataLB;
                tmpSize = tmp[0];
                lj = 0.0;
                tmpSize2 = tmp2[0];
                ej = 0.0;
                res = std::make_pair(0, 0);
                
                if (tmpSize == 0)
                {
                    for (int kCount = 0; kCount < kMax; kCount++, ptr1 += NUMTASKSQUARE)
                    {
                        ac_2 = ptr1[j1] + ptr1[j2] + ptr1[j3];
                        for (ii = 1, tmpData2 = &tmp2[1]; ii <= tmpSize2; ii++, tmpData2++) ac_2 += ptr1[*tmpData2];
                        ej = ej < ac_2 ? ac_2 : ej;
                        for (int taskCount = 1; taskCount < change; taskCount++)
                        {
                            ptr2 = ptr1 + listPricing[taskCount];
                            ac_2 = ptr2[j1] + ptr2[j2] + ptr2[j3];
                            for (ii = 1, tmpData2 = &tmp2[1]; ii <= tmpSize2; ii++, tmpData2++) ac_2 += ptr2[*tmpData2];
                            ej = ej < ac_2 ? ac_2 : ej;
                        }
                    }
                    tmpChar = char(int(ceil(ej - intTolerance)));
                    res.second = tmpChar;
                }
                else if (tmpSize2 == 0)
                {
                    for (int kCount = 0; kCount < kMax; kCount++, ptr1 += NUMTASKSQUARE)
                    {
                        ac = ptr1[j1] + ptr1[j2] + ptr1[j3];
                        for (ii = 1, tmpData = &tmp[1]; ii <= tmpSize; ii++, tmpData++) ac += ptr1[*tmpData];
                        lj = lj < ac ? ac : lj;
                        for (int taskCount = 1; taskCount < change; taskCount++)
                        {
                            ptr2 = ptr1 + listPricing[taskCount];
                            ac = ptr2[j1] + ptr2[j2] + ptr2[j3];
                            for (ii = 1, tmpData = &tmp[1]; ii <= tmpSize; ii++, tmpData++) ac += ptr2[*tmpData];
                            lj = lj < ac ? ac : lj;
                        }
                    }
                    tmpChar = char(int(ceil(lj - intTolerance)));
                    res.first = tmpChar;
                }
                else
                {
                    // dual feasible function
                    for (int kCount = 0; kCount < kMax; kCount++, ptr1 += NUMTASKSQUARE)
                    {
                        ac = ptr1[j1] + ptr1[j2] + ptr1[j3];
                        ac_2 = ac;
                        for (ii = 1, tmpData = &tmp[1]; ii <= tmpSize; ii++, tmpData++) ac += ptr1[*tmpData];
                        lj = lj < ac ? ac : lj;

                        for (ii = 1, tmpData2 = &tmp2[1]; ii <= tmpSize2; ii++, tmpData2++) ac_2 += ptr1[*tmpData2];
                        ej = ej < ac_2 ? ac_2 : ej;
                        for (int taskCount = 1; taskCount < change; taskCount++)
                        {
                            ptr2 = ptr1 + listPricing[taskCount];
                            ac = ptr2[j1] + ptr2[j2] + ptr2[j3];
                            ac_2 = ac;
                            for (ii = 1, tmpData = &tmp[1]; ii <= tmpSize; ii++, tmpData++) ac += ptr2[*tmpData];
                            lj = lj < ac ? ac : lj;

                            for (ii = 1, tmpData2 = &tmp2[1]; ii <= tmpSize2; ii++, tmpData2++) ac_2 += ptr2[*tmpData2];
                            ej = ej < ac_2 ? ac_2 : ej;
                        }
                    }
                    res.first = char(int(ceil(lj - intTolerance)));
                    res.second = char(int(ceil(ej - intTolerance)));
                }
                if (res.first == 0 && res.second == 0) continue;
                val3.taskSet[2] = j3;
                
                cutMap3.emplace(make_pair(val3, res));
            }
        }
    }
    cut_3 = new int [cutMap3.size() * 5 + 1];
    cut_3[0] = cutMap3.size() * 5;
    ii = 1;
    for (itBPC3 = cutMap3.begin(); itBPC3 != cutMap3.end(); itBPC3++)
    {
        cut_3[ii] = itBPC3->first.taskSet[0];
        cut_3[ii + 1] = itBPC3->first.taskSet[1];
        cut_3[ii + 2] = itBPC3->first.taskSet[2];
        cut_3[ii + 3] = itBPC3->second.first;
        cut_3[ii + 4] = itBPC3->second.second;
        ii += 5;
    }
    totalTime += double(clock() - start) / CLKTCK;

    // compute forbidden set but satisying capacity constraints
    start = clock();
    bool config_fea[5];
    memset(config_fea, true, sizeof(config_fea));
    int forbidden_set[5];
    memset(forbidden_set, 0, sizeof(forbidden_set));
    memset(forbiddenSetC, 0, sizeof(forbiddenSetC));
    memset(forbiddenSetCid, 0, sizeof(forbiddenSetCid));
    for (int i = 1; i <= numTasks; i++) genForbiddenSetLoad(i, timeCap, forbidden_set, config_fea);

    // pre-compute data for separation problem
    for (int i = 1; i <= numTasks; i++) 
    {
        precCapList[i] = -1 - timeCap;
        sucsCapList[i] = -1 - timeCap;
        for (int j = 1; j <= directPreds[i][0]; j++) precCapList[i] += taskTime[directPreds[i][j]];
        for (int j = 1; j <= directSucs[i][0]; j++) sucsCapList[i] += taskTime[directSucs[i][j]];
        for (int j = 1; j <= allGamma[i][0]; j++)
        {
            precCapList[i] += taskTime[allGamma[i][j]];
            sucsCapList[i] += taskTime[allGamma[i][j]];
        }
    }

    // reDo
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
    int len = precdenceRelation.size() * (precdenceRelation.size() + 1);
    minDist = new int[int(len * 1.5) + 1];     // caution: this number is theoretically large enough
    minDist[0] = 0;
    for (int j1 = 1; j1 <= numTasks; j1++)
    {
        if (2 * minDist[0] >= len) break;
        for (int jId = 1; jId <= allSucs[j1][0]; jId++)
        {
            if (2 * minDist[0] >= len) break;
            int j2 = allSucs[j1][jId];
            if (adjMatr[j1][j2]) continue;
            tmp[0] = 0;
            for (int jj = 1; jj < jId; jj++)
            {
                int j = allSucs[j1][jj];
                if (!transMatr[j][j2]) continue;
                tmp[0]++;
                tmp[tmp[0]] = j;
            }
            double differ = 0;
            if (tmp[0] == 1) differ = 1;
            else if (tmp[0] == 2)
            {
                if (taskTime[tmp[1]] + taskTime[tmp[2]] <= timeCap) differ = 1;
                else differ = 2;
            }
            else 
            {
                // dual feasible function
                ptr1 = dataLB;
                tmpSize = tmp[0];
                tmpData = tmp;
                // dual feasible function
                for (kCount = 0; kCount < kMax; kCount++, ptr1 += NUMTASKSQUARE)
                {
                    ac = 0;
                    for (ii = 1, tmpData = &tmp[1]; ii <= tmpSize; ii++, tmpData++) ac += ptr1[*tmpData];
                    differ = differ < ac ? ac : differ;
                    for (taskCount = 1; taskCount < change; taskCount++)
                    {
                        ptr2 = ptr1 + listPricing[taskCount];
                        ac = 0;
                        for (ii = 1, tmpData = &tmp[1]; ii <= tmpSize; ii++, tmpData++) ac += ptr2[*tmpData];
                        differ = differ < ac ? ac : differ;
                    }
                }
                differ = ceil(differ - intTolerance) + 1;
            }
            if ((int)differ + shortest_path[j1] <= shortest_path[j2]) continue;
            minDist[3 * minDist[0] + 1] = j1;
            minDist[3 * minDist[0] + 2] = j2;
            minDist[0]++;
            minDist[3 * minDist[0]] = (int)differ;
        }
    }
    totalTime += double(clock() - start) / CLKTCK;
}

static void BPCInit() 
{
    clock_t start = clock();
    //initialize the incumbent solution
    globalUpperbound = incumbentSol[0][0];
    for (int i = 1; i <= numTasks; i++) L[i] = (int)globalUpperbound - (int)(tailsLB[i]);
    stackInit();
    listInit();
    // reserve space based on the init UB and the estimated column number 
    for (int i = 0; i < FTPColumn.size(); i++) std::vector<std::array<bool, NUMTASK + 14>>().swap(FTPColumn[i]);
    for (int i = 0; i < FTPColumnPool.size(); i++) FTPColumnPool[i] = boost::unordered_flat_map<std::array<bool, NUMTASK + 14>, int>();
    FTPColumn.clear();
    FTPColumnPool.clear();
    FTPColumn.shrink_to_fit();
    FTPColumnPool.shrink_to_fit();
    FTPColumn.resize((int)globalUpperbound + 1);
    FTPColumnPool.resize((int)globalUpperbound + 1);
    // memory
    for (int i = 0; i <= globalUpperbound; i++)
    {
        FTPColumn[i].reserve(numTasks);
        FTPColumnPool[i].reserve(numTasks);
    }
    pi = new double[(int)globalUpperbound + 1];
    mu = new double* [(int)globalUpperbound + 1];
    for (int i = 0; i <= globalUpperbound; i++) mu[i] = new double[numTasks + 1];
    theta = new double* [(int)globalUpperbound + 1];
    for (int i = 0; i <= globalUpperbound; i++) theta[i] = new double[configurationSubsetNumber];
    newColX = new double[numTasks + 1];
    newColCut = new double[configurationSubsetNumber];
    //overtime indicator;
    overTime = false;
    overStack = false;
    //solve the root node 
    root = listTake();
    //for the root station, create vector nontake (jobs cannot be taken)
    root->nontakeMatr.resize((int)globalUpperbound + 1); //nontake[i] includes all jobs that cannot be taken in station i; 
    for (int i = 1; i <= globalUpperbound; i++)
    {
        root->nontakeMatr[i].resize(numTasks + 1);
        for (int j = 1; j <= numTasks; j++)
        {
            if (i<E[j] || i>L[j]) root->nontakeMatr[i][j] = true;
            else root->nontakeMatr[i][j] = false;
        }
    }
    if (initFeasiblity)
    {
        //add initial columns to column struct and to the model
        std::vector<std::array<bool, NUMTASK + 14>> initColumn((int)globalUpperbound + 1);
        for (int j = 1; j <= numTasks; j++) initColumn[incumbentSol[0][j]][j] = true;
        for (int i = 1; i <= globalUpperbound; i++)
        {
            for (int config_set = 1; config_set <= configurationSubsetNumber; config_set++)
            {
                int coeff = 1;
                for (int k = 1; k <= configurationSubsetC[config_set][0]; k++)
                {
                    int coeff_k = 0;
                    int config_notin = configurationSubsetC[config_set][k];
                    for (int j = 1; j <= numTasks; j++)
                    {
                        if (incumbentSol[0][j] == i && !configMatr[config_notin][j])
                        {
                            coeff_k = 1;
                            break;
                        }
                    }
                    if (coeff_k == 0)
                    {
                        coeff = 0;
                        break;
                    }
                }
                initColumn[i][NUMTASK - 1 + config_set] = coeff;
            }
            FTPColumn[i].push_back(initColumn[i]);
            FTPColumnPool[i].insert(std::make_pair(initColumn[i], 0));
            root->valid[i].push_back(0);
        }
        root->upperbound = globalUpperbound;
        root->lowerbound = rootLB;
    }
    totalTime += double(clock() - start) / CLKTCK;
}

static void BPCFree() 
{
    clock_t start = clock();
    if (stackTop == bottom && !overStack && !overTime)
    {
        if (incumbentSol[0][1] <= 0 || incumbentSol[0][1] > incumbentSol[0][0]) instanceFeasibility = 0; // the instances is proven to be infeaible!
        else 
        {
            rootLB = incumbentSol[0][0];
            instanceFeasibility = 1; // we find an optimal solution (also feasible)
        }
    }
    else 
    {
        int min_depth = MAXNODE;
        double LB_BPC = 0;
        while (stackTop != bottom)
        {
            Node* node = stackPop();
            if (min_depth > node->treeNodeDepth)
            {
                min_depth = node->treeNodeDepth;
                LB_BPC = node->lowerbound;
            }
            else if (min_depth == node->treeNodeDepth)
            {
                LB_BPC = LB_BPC > node->lowerbound ? node->lowerbound : LB_BPC;
            }
            listAdd(node);
        }
        rootLB = rootLB > LB_BPC ? rootLB : LB_BPC;
        rootLB = ceil(rootLB - intTolerance);
    }
    //count the total number of columns generated
    for (int i = 1; i < FTPColumn.size(); i++) totalColNum += (int)FTPColumn[i].size();
    // free memory
    for (int i = 0; i < FTPColumn.size(); i++)
    {
        std::vector<std::array<bool, NUMTASK + 14>>().swap(FTPColumn[i]);
        FTPColumnPool[i] = boost::unordered_flat_map<std::array<bool, NUMTASK + 14>, int>();
    }
    delete[] cut_2;
    cut_2 = nullptr;
    delete[] cut_3;
    cut_3 = nullptr;
    delete[] pi;
    pi = nullptr;
    for (int i = 0; i <= initUB; i++) 
    {
        delete[] mu[i];
        mu[i] = nullptr;
        delete[] theta[i];
        theta[i] = nullptr;
    }
    delete[] mu;
    mu = nullptr;
    delete[] theta;
    theta = nullptr;
    delete[] newColX;
    newColCut = nullptr;
    delete[] newColCut;
    newColCut = nullptr;
    delete[] minDist;
    minDist = nullptr;
    totalTime += double(clock() - start) / CLKTCK;
}

static void BPCPrepareChild(Node* parentnode, Node* childnode, int leftOrRight)//prepare the child Node for branch-and-price, remove invalid columns, impose column-conditions 
{
    childnode->parent = parentnode;
    childnode->branchChoice = parentnode->branchChoice;
    childnode->nontakeMatr = parentnode->nontakeMatr;
    for (int j = 1; j <= numTasks; j++)
    {
        for (int i = L[j] + 1; i <= globalUpperbound; i++)
        {
            childnode->nontakeMatr[i][j] = true;
        }
    }
    childnode->valid = parentnode->valid;
    childnode->upperbound = parentnode->upperbound;
    childnode->lowerbound = parentnode->lowerbound;
    childnode->treeNodeDepth = parentnode->treeNodeDepth + 1;
    if (childnode->treeNodeDepth > maxBBTreeDepth) maxBBTreeDepth = childnode->treeNodeDepth; //update the max tree depth
    //check 
    if (leftOrRight == 1)// left child, branching job and its successors cannot be executed at stations from 1 to branching station
    {
        // indicate the relation
        parentnode->lchild = childnode;
        // update the values for the child node based on the info from the parent and the choice made
        childnode->branchChoice[childnode->branchChoice.size() - 1][0] = leftOrRight;//choice value is 1, j can not be executed before i (i included);
        // check all the valid columns from the parents, see if j or the successors of j is processed by stations before i (i included); update the nontakeMatr meanwhile 
        int branchJ = childnode->branchChoice[childnode->branchChoice.size() - 1][1];
        int branchI = childnode->branchChoice[childnode->branchChoice.size() - 1][2];
        for (int i = 1; i <= branchI; i++) //check from station 1 to i, if j and any successor of j is executed there
        {
            // prepare the removed structure for the child node, then remove the column number from the valid structure
            std::vector<int> removed;
            for (int validColId = 0; validColId < parentnode->valid[i].size(); validColId++)
            {
                bool ifRemoved = false;
                if (FTPColumn[i][parentnode->valid[i][validColId]][branchJ])// see if the current valid column of the parent node has job branchJ
                {
                    ifRemoved = true;
                }
                else// check all successors of job branchJ, see if they are executed by columns of station i
                {
                    for (int sucId = 1; sucId <= allSucs[branchJ][0]; sucId++)
                    {
                        if (FTPColumn[i][parentnode->valid[i][validColId]][allSucs[branchJ][sucId]])// see if the current valid column (of the parent has job in it)
                        {
                            ifRemoved = true;
                            break;
                        }
                    }
                }
                // if the current culomn is to be removed, put it in the removed 
                if (ifRemoved)
                {
                    removed.push_back(parentnode->valid[i][validColId]);//put the column index into removed[i]
                    //remove the invalid column from the valid structure
                    childnode->valid[i].erase(remove(childnode->valid[i].begin(), childnode->valid[i].end(), removed[removed.size() - 1]), childnode->valid[i].end());
                }
            }

            //prepare the nontake matrix for the child node, to be used for pricing
            childnode->nontakeMatr[i][branchJ] = true;
            for (int sucId = 1; sucId <= allSucs[branchJ][0]; sucId++)
            {
                childnode->nontakeMatr[i][allSucs[branchJ][sucId]] = true;
            }
        }

        // pre check the feasibility of the child
        int count_invalid_sta = 0;
        for (int i = 1; i <= initUB; i++)// first check the branching job j
        {
            if (childnode->nontakeMatr[i][branchJ]) count_invalid_sta++;
        }
        if (count_invalid_sta == initUB) { childnode->ifDelete = true; return; }
        for (int sucId = 1; sucId <= allSucs[branchJ][0]; sucId++)// then check all successors of the branching job j, see if they are feasible or not
        {
            count_invalid_sta = 0;
            for (int i = 1; i <= initUB; i++)
            {
                if (childnode->nontakeMatr[i][allSucs[branchJ][sucId]]) count_invalid_sta++;
            }
            if (count_invalid_sta == initUB) { childnode->ifDelete = true; return; }
        }
    }
    else // right child, branching job and its predecessors cannot be executed at stations from branching station + 1 to the last station 
    {
        // indicate the relation
        parentnode->rchild = childnode;

        // update the values for the child node based on the info from the parent and the choice made
        childnode->branchChoice[childnode->branchChoice.size() - 1][0] = leftOrRight;//choice value is 2, j can not be executed before i (i included);
        // check all the valid columns from the parents, see if j or the successors of j is processed by stations before i (i included); update the nontakeMatr meanwhile 
        int branchJ = childnode->branchChoice[childnode->branchChoice.size() - 1][1];
        int branchI = childnode->branchChoice[childnode->branchChoice.size() - 1][2];
        for (int i = branchI + 1; i <= initUB; i++) //check from station branchI+1 to last station, if j and any predecessor of j is executed there
        {
            // prepare the removed structure for the child node, then remove the column number from the valid structure
            std::vector<int> removed;
            for (int validColId = 0; validColId < parentnode->valid[i].size(); validColId++)
            {
                bool ifRemoved = false;
                if (FTPColumn[i][parentnode->valid[i][validColId]][branchJ])// see if the current valid column of the parent node has job branchJ
                {
                    ifRemoved = true;
                }
                else// check all predecessors of job branchJ, see if they are executed by columns of station i
                {
                    for (int predId = 1; predId <= allPreds[branchJ][0]; predId++)
                    {
                        if (FTPColumn[i][parentnode->valid[i][validColId]][allPreds[branchJ][predId]])// see if the current valid column (of the parent has job in it)
                        {
                            ifRemoved = true;
                            break;
                        }
                    }
                }
                // if the current culomn is to be removed, put it in the removed 
                if (ifRemoved)
                {
                    removed.push_back(parentnode->valid[i][validColId]);//put the column index into removed[i]
                    //remove the invalid column from the valid structure
                    childnode->valid[i].erase(remove(childnode->valid[i].begin(), childnode->valid[i].end(), removed[removed.size() - 1]), childnode->valid[i].end());
                }
            }

            //prepare the nontake matrix for the child node, to be used for pricing
            childnode->nontakeMatr[i][branchJ] = true;
            for (int predId = 1; predId <= allPreds[branchJ][0]; predId++)
            {
                childnode->nontakeMatr[i][allPreds[branchJ][predId]] = true;
            }
        }

        // pre check the feasibility of the child
        int count_invalid_sta = 0;
        for (int i = 1; i <= initUB; i++)// first check the branching job j
        {
            if (childnode->nontakeMatr[i][branchJ]) count_invalid_sta++;
        }
        if (count_invalid_sta == initUB) { childnode->ifDelete = true; return; }
        for (int predId = 1; predId <= allPreds[branchJ][0]; predId++)// then check all successors of the branching job j, see if they are feasible or not
        {
            count_invalid_sta = 0;
            for (int i = 1; i <= initUB; i++)
            {
                if(childnode->nontakeMatr[i][allPreds[branchJ][predId]]) count_invalid_sta ++;
            }
            if (count_invalid_sta == initUB) { childnode->ifDelete = true; return; }
        }
    }
}

static void findBranchingChoice(Node* current)
{
    std::array<int, 3> bestBranchingChoice = { { 0 } };
    ////calculate the total processing time
    //int totalT = 0;
    //for (int j = 1; j <= numTasks; j++) totalT += taskTime[j];

    ////set the coefficient of other parts of the criterion
    //double coefPredSuc = 0.2;
    //if (current->parent == NULL) coefPredSuc = 0.2;
    //else
    //{
    //    if (0.2 - ((current->parent->treeNodeDepth / 6) * 0.05) > 0.05) coefPredSuc = 0.2 - ((current->parent->treeNodeDepth / 6) * 0.05);
    //    else coefPredSuc = 0.1;
    //}
    double bestCriterion = 0; // the larger the better
    for (int j = numTasks; j >= 1; j--)
    {
        double currentCriterion = 0;
        ////calculate the total processing time of the preds and sucs
        //int totalPredSucTime = 0;
        //int totalPredSucNum = 0;
        ////calculate the total number of preds and sucs
        //totalPredSucNum = allPreds[j][0] + allSucs[j][0];

        ////calculate the totalPredSucTime
        //for (int predId = 1; predId <= allPreds[j][0]; predId++) totalPredSucTime += taskTime[allPreds[j][predId]];
        //for (int sucId = 1; sucId <= allSucs[j][0]; sucId++) totalPredSucTime += taskTime[allSucs[j][sucId]];
        //totalPredSucTime += taskTime[j];

        //the other parts of the criterion
        //currentCriterion = coefPredSuc * double(totalPredSucTime) / double(totalT) - 0.001 * totalPredSucNum;
        //check each station, find the position closest to 0.5
        double closestMiddleVal = 100000;
        int closestFlight = 100000;
        double sumX = 0;
        for (int i = 1; i <= globalUpperbound; i++)
        {
            sumX += xSol[i][j];
            if (xSol[i][j] == 0) continue;
            else
            {
                if (abs(sumX - 0.5) < closestMiddleVal)
                {
                    closestMiddleVal = abs(sumX - 0.5);
                    closestFlight = i;
                }
                if (sumX >= 1) break;
            }
        }
        currentCriterion += (0.5 - closestMiddleVal);
        //if (current->parent == NULL) coefPredSuc = currentCriterion + (0.5 - closestMiddleVal);
        //else currentCriterion = currentCriterion + (0.5 - closestMiddleVal);
        if (currentCriterion > bestCriterion)
        {
            bestCriterion = currentCriterion;
            bestBranchingChoice[1] = j;
            bestBranchingChoice[2] = closestFlight;
        }
    }
    current->branchChoice.push_back(bestBranchingChoice);
    current->criterion = bestCriterion;
}

static void DFSrecursion(int* taskPosition, int* degrees, int depth)
{
    if (depth == incumbentSol[0][0]) return;
    // check if we obtain a complete solution
    bool flag = true;
    for (int i = 1; i <= numTasks; i++)
    {
        if (degrees[i] > 0) continue;
        flag = false;
        break;
    }
    if (flag)
    {
        if (hungarian(taskPosition, depth)) 
        {
            // we find a better solution!
            std::cout << depth << std::endl;
            incumbentSol[0][0] = depth;
            for (int i = 1; i <= numTasks; i++)incumbentSol[0][i] = taskPosition[i];
            for (int i = 1; i <= CkSum[numConfig]; i++)
            {
                if (match[i] != -1)
                {
                    for (int k = 0; k < numConfig; k++)
                    {
                        if (i > CkSum[k] && i <= CkSum[k + 1])
                        {
                            incumbentSol[1][match[i]] = k + 1;
                            break;
                        }
                    }
                }
            }
        }
        return;
    }
    for (int id = 0; id < lambSize[depth]; id++)
    {
        int colId = lambIdList[depth][id];
        bool flag = true;
        // check whether the current column is feasible!
        for (int i = 1; i <= numTasks && flag; i++)
        {
            if (FTPColumn[depth][colId][i] == 0) continue;
            // whether this task is exucuted twice
            if (degrees[i] == 1)
            {
                flag = false;
                break;
            }
            // whether this executed task has a predecessor that is not executed
            for (int ii = 1; ii <= allPreds[i][0] && flag; ii++)
            {
                if (degrees[i] == 0)
                {
                    flag = false;
                    break;
                }
            }
        }
        if (flag)
        {
            // we find a feasible column, then assign
            for (int i = 1; i <= numTasks; i++)
            {
                if (FTPColumn[depth][colId][i] == 1)
                {
                    degrees[i] = 1;
                    taskPosition[i] = depth;
                }
            }
            // DFS recursion
            DFSrecursion(taskPosition, degrees, depth + 1);
            // disassign
            for (int i = 1; i <= numTasks; i++)
            {
                if (FTPColumn[depth][colId][i] == 1)
                {
                    degrees[i] = 0;
                    taskPosition[i] = 0;
                }
            }
        }
    }
}

static void BPCDivingHeuristic()
{
    //Begin explore, DFS search
    int taskPosition[NUMTASK];
    memset(taskPosition, 0, sizeof(taskPosition));
    int degrees[NUMTASK];
    memset(degrees, 0, sizeof(degrees));
    DFSrecursion(taskPosition, degrees, 1);
}

static void BPCNodeFarkas(Node* current)
{
    double remainingTime = runTimeLimit - totalTime;
    clock_t start = clock();
    try
    {
        EnvrConfig config;
        config.Set("nobanner", "1");
        Envr ENV(config);
        Model masterModel = ENV.CreateModel("masterModel");

        std::vector<VarArray> y((int)globalUpperbound + 1);
        // position holder
        y[0] = masterModel.AddVars(1, 0, 0, 0, 'C');
        for (int i = 1; i <= (int)globalUpperbound; i++)
        {
            y[i] = masterModel.AddVars(numConfig + 1, 0, 1, 1, 'C');
            y[i][0].Set("UB", 0);
        }

        std::vector<VarArray> x((int)globalUpperbound + 1);
        // position holder
        x[0] = masterModel.AddVars(1, 0, 0, 0, 'C');
        for (int i = 1; i <= (int)globalUpperbound; i++)
        {
            x[i] = masterModel.AddVars(numTasks + 1, 0, 1, 0, 'C');
            x[i][0].Set("UB", 0);
        }

        Expr cons, cons2;
        // column variables
        std::vector<VarArray> lamb((int)globalUpperbound + 1);
        // x with column
        std::vector<ConstrArray> xToLamb((int)globalUpperbound + 1);
        for (int i = 1; i <= (int)globalUpperbound; i++)
        {
            xToLamb[i].Reserve(numTasks + 1);
            // position holder
            xToLamb[i].PushBack(masterModel.AddConstr(cons >= 0));
            for (int j = 1; j <= numTasks; j++) xToLamb[i].PushBack(masterModel.AddConstr(-x[i][j] == 0));
        }

        // y with column
        ConstrArray yToLamb;
        yToLamb.Reserve(1 + (int)globalUpperbound * numConfig);
        // position holder
        yToLamb.PushBack(masterModel.AddConstr(cons >= 0));
        for (int i = 1; i <= (int)globalUpperbound; i++)
        {
            for (int k = 1; k <= numConfig; k++) cons -= y[i][k];
            yToLamb.PushBack(masterModel.AddConstr(cons == 0));
            if (i > 1) masterModel.AddConstr(cons - cons2 <= 0);
            cons2 = cons;
            cons.Clear();
        }
        cons2.Clear();

        //y cuts with columns
        std::vector<ConstrArray> yCutsToLamb((int)globalUpperbound + 1);
        for (int i = 1; i <= globalUpperbound; i++)
        {
            yCutsToLamb[i].Reserve(configurationSubsetNumber);
            for (int configSetId = 1; configSetId <= configurationSubsetNumber; configSetId++)
            {
                for (int k = 1; k <= numConfig; k++) cons -= (configurationSubset[configSetId][k] * y[i][k]);
                yCutsToLamb[i].PushBack(masterModel.AddConstr(cons <= 0));
                cons.Clear();
            }
        }

        // Objective
        masterModel.SetObjSense(1);      // 1: min; -1: max
        for (int i = 1; i <= (int)globalUpperbound; i++)
        {
            for (int k = 1; k <= numConfig; k++) cons += y[i][k];
        }
        if (current->treeNodeDepth > 0) masterModel.AddConstr(cons >= current->parent->lowerbound);
        cons.Clear();

        // Constraints
        for (int j = 1; j <= numTasks; j++)
        {
            for (int i = 1; i <= (int)globalUpperbound; i++) cons += x[i][j];
            masterModel.AddConstr(cons == 1);
            cons.Clear();
        }
        for (int i = 1; i <= (int)globalUpperbound; i++)
        {
            for (int k = 1; k <= numConfig; k++) cons += y[i][k];
            masterModel.AddConstr(cons <= 1);
            cons.Clear();
        }

        // precedence constraints
        for (int pre = 0; pre < precdenceRelation.size(); pre++)
        {
            int j1 = precdenceRelation[pre].first;
            int j2 = precdenceRelation[pre].second;
            for (int i = E[j1]; i < E[j2] - 1; i++) cons += x[i][j1];
            
            for (int i = E[j2] - 1; i < L[j1]; i++)
            {
                cons += (x[i][j1] - x[i + 1][j2]);
                masterModel.AddConstr(cons >= 0);
            }
            cons.Clear();
        }

        // configuration constraints
        if (numConfig > 1 && !addNonrobustCut)
        {
            for (int i = 1; i <= (int)globalUpperbound; i++)
            {
                for (int j = 1; j <= numTasks; j++)
                {
                    cons += x[i][j];
                    for (int k = 1; k <= numConfig; k++)
                    {
                        if (configMatr[k][j]) cons -= y[i][k];
                    }
                    masterModel.AddConstr(cons <= 0);
                    cons.Clear();
                }
            }
        }

        // flight constraints
        for (int k = 1; k <= numConfig; k++)
        {
            for (int i = 1; i <= (int)globalUpperbound; i++) cons += y[i][k];
            masterModel.AddConstr(cons <= Ck[k]);
            cons.Clear();
        }

        //add initial valid columns for the current node
        for (int i = 1; i <= (int)globalUpperbound; i++)
        {
            lambSize[i] = current->valid[i].size();
            for (int currentValidColId = 0; currentValidColId < current->valid[i].size(); currentValidColId++)
            {
                lambIdList[i][currentValidColId] = current->valid[i][currentValidColId];
                memset(newColX, 0, (numTasks + 1) * sizeof(double));
                memset(newColCut, 0, configurationSubsetNumber * sizeof(double));
                for (int j = 1; j <= numTasks; j++) newColX[j] = FTPColumn[i][current->valid[i][currentValidColId]][j];
                for (int j = NUMTASK; j < NUMTASK + configurationSubsetNumber; j++) newColCut[j - NUMTASK] = FTPColumn[i][current->valid[i][currentValidColId]][j];
                Column col;
                col.AddTerms(xToLamb[i], newColX, numTasks + 1);
                col.AddTerm(yToLamb[i], 1);
                if (numConfig > 1 && !addNonrobustCut) col.AddTerms(yCutsToLamb[i], newColCut, configurationSubsetNumber);
                lamb[i].PushBack(masterModel.AddVar(0, 1, 0, 'C', col));
            }
        }

        //prefixing of variables
        for (int i = 1; i <= (int)globalUpperbound; i++)
        {
            for (int j = 1; j <= numTasks; j++)
            {
                if (current->nontakeMatr[i][j]) x[i][j].Set("UB", 0);
            }
        }

        // Solve
        masterModel.SetIntParam("Logging", 0);
        masterModel.SetIntParam("Threads", 1);
        masterModel.SetDblParam(COPT_DBLPARAM_TIMELIMIT, remainingTime);
        masterModel.SetIntParam("LpMethod", 1);
        masterModel.SetIntParam("Presolve", 0);
        masterModel.SetIntParam("ReqFarkasRay", 1);
        masterModel.Solve();
        bool newColGen = true;
        bool newRowGen = true;
    colAndRowGeneration:
        if (masterModel.GetIntAttr("LpStatus") == 2)        // infeasible
        {
            //-----------------------------------------------------
            //Farkas pricing to check feasiblity/initialize columns
            //-----------------------------------------------------
            bool needLPFeasible = true;
            while (needLPFeasible)
            {
                //take the farkas prices
                for (int i = 1; i <= (int)globalUpperbound; i++)
                {
                    masterModel.Get("DualFarkas", xToLamb[i], mu[i]);
                    if (numConfig > 1 && addNonrobustCut) masterModel.Get("DualFarkas", yCutsToLamb[i], theta[i]);
                }
                masterModel.Get("DualFarkas", yToLamb, pi);
                newColGen = false;
                for (int i = 1; i <= (int)globalUpperbound; i++)
                {
                    //put the corresponding farkas prices to the dual values
                    dualCol[0] = pi[i];
                    memcpy(&dualCol[1], &mu[i][1], numTasks * sizeof(double));
                    if (numConfig > 1 && addNonrobustCut) memcpy(&dualCol[NUMTASK], theta[i], configurationSubsetNumber * sizeof(double));
                    for (int j = 1; j <= numTasks; j++)
                    {
                        if (current->nontakeMatr[i][j]) dualCol[j] = -1;
                    }
                    //solve the pricing problem
                    bbPricing(i);
                    //check if new column for station i needs to be added
                    //std::cout << "Dual Farkas: " << bestPrice << std::endl;
                    if (bestPrice > intTolerance)
                    {
                        if(lambSize[i] >= MAXCOL) 
                        {
                            current->optimized = false;
                            overStack = true;
                            goto nodeFarkasEnd;
                        }
                        //add new column to the column pool and the LP model
                        std::array<bool, NUMTASK + 14> arr = { { 0 } };
                        memset(newColX, 0, (numTasks + 1) * sizeof(double));
                        if (numConfig > 1 && addNonrobustCut) memset(newColCut, 0, configurationSubsetNumber * sizeof(double));
                        for (int j_ind = 1; j_ind <= bestSol[0]; j_ind++)
                        {
                            arr[bestSol[j_ind]] = 1;
                            newColX[bestSol[j_ind]] = 1;
                        }
                        for (int j_ind = NUMTASK; j_ind < NUMTASK + configurationSubsetNumber; j_ind++)
                        {
                            arr[j_ind] = bestSol[j_ind];
                            newColCut[j_ind - NUMTASK] = bestSol[j_ind];
                        }
                        itCol = FTPColumnPool[i].find(arr);
                        if (itCol == FTPColumnPool[i].end())
                        {
                            // a new column
                            lambIdList[i][lambSize[i]] = (int)FTPColumn[i].size();
                            FTPColumnPool[i].insert(make_pair(arr, (int)FTPColumn[i].size()));
                            lambSize[i]++;
                            FTPColumn[i].push_back(arr);
                        }
                        else
                        {
                            // an old column
                            lambIdList[i][lambSize[i]] = itCol->second;
                            lambSize[i]++;
                        }
                        Column col;
                        col.AddTerms(xToLamb[i], newColX, numTasks + 1);
                        col.AddTerm(yToLamb[i], 1);
                        if (numConfig > 1 && addNonrobustCut) col.AddTerms(yCutsToLamb[i], newColCut, configurationSubsetNumber);
                        lamb[i].PushBack(masterModel.AddVar(0, 1, 0, 'C', col));
                        newColGen = true;
                    }
                }
                
                // solve the master again
                if (newColGen) masterModel.Solve();  // Add time limit here!! In some extreme case, solve this LP is very time consuming!!
                if (clock() > start + remainingTime * CLKTCK)
                {
                    current->optimized = false;
                    goto nodeFarkasEnd;
                }
                if (masterModel.GetIntAttr("LpStatus") == 1)//go on to reduce cost pricing
                {
                    needLPFeasible = false;
                }
                else if (masterModel.GetIntAttr("LpStatus") == 2 && newColGen) //need more farkas pricing
                {
                    needLPFeasible = true;
                }
                else if (masterModel.GetIntAttr("LpStatus") == 2 && !newColGen) //current node infeasible
                {
                    current->infeasible = true;
                    goto nodeFarkasEnd;
                }
            }
        }
        double nodeDualBound = 0;
        //CRG iterations, update column pool	
        while (newColGen || newRowGen)
        {
            newRowGen = false;
            double dualBound;
            //---------------------
            //--column generation--
            //---------------------
            while (newColGen)
            {
                dualBound = masterModel.GetDblAttr("LpObjval");
                // get the current solution and prepare the dual values 
                masterModel.Get("Dual", yToLamb, pi);
                for (int i = 1; i <= (int)globalUpperbound; i++)
                {
                    masterModel.Get("Dual", xToLamb[i], mu[i]);
                    if (numConfig > 1 && addNonrobustCut) masterModel.Get("Dual", yCutsToLamb[i], theta[i]);
                }
                newColGen = false;
                int addColNum = 0;
                for (int i = 1; i <= (int)globalUpperbound; i++)
                {
                    dualCol[0] = pi[i];
                    memcpy(&dualCol[1], &mu[i][1], numTasks * sizeof(double));
                    if (numConfig > 1 && addNonrobustCut) memcpy(&dualCol[NUMTASK], theta[i], configurationSubsetNumber * sizeof(double));
                    for (int j = 1; j <= numTasks; j++)
                    {
                        if (current->nontakeMatr[i][j]) dualCol[j] = -1;
                    }
                    //solve the pricing problem
                    bbPricing(i);
                    //check if new column for station i needs to be added
                    
                    if (bestPrice > intTolerance)
                    {
                        if (lambSize[i] >= MAXCOL)
                        {
                            current->optimized = false;
                            overStack = true;
                            goto nodeFarkasEnd;
                        }
                        dualBound -= bestPrice;
                        addColNum++;
                        //add new column to the column pool and the LP model
                        std::array<bool, NUMTASK + 14> arr = { { 0 } };
                        memset(newColX, 0, (numTasks + 1) * sizeof(double));
                        if (numConfig > 1 && addNonrobustCut) memset(newColCut, 0, configurationSubsetNumber * sizeof(double));
                        for (int j_ind = 1; j_ind <= bestSol[0]; j_ind++)
                        {
                            arr[bestSol[j_ind]] = 1;
                            newColX[bestSol[j_ind]] = 1;
                        }
                        for (int j_ind = NUMTASK; j_ind < NUMTASK + configurationSubsetNumber; j_ind++)
                        {
                            arr[j_ind] = bestSol[j_ind];
                            newColCut[j_ind - NUMTASK] = bestSol[j_ind];
                        }
                        itCol = FTPColumnPool[i].find(arr);
                        if (itCol == FTPColumnPool[i].end())
                        {
                            // a new column
                            lambIdList[i][lambSize[i]] = (int)FTPColumn[i].size();
                            FTPColumnPool[i].insert(make_pair(arr, (int)FTPColumn[i].size()));
                            lambSize[i]++;
                            FTPColumn[i].push_back(arr);
                        }
                        else
                        {
                            // an old column
                            lambIdList[i][lambSize[i]] = itCol->second;
                            lambSize[i]++;
                        }
                        Column col;
                        col.AddTerms(xToLamb[i], newColX, numTasks + 1);
                        col.AddTerm(yToLamb[i], 1);
                        if (numConfig > 1 && addNonrobustCut) col.AddTerms(yCutsToLamb[i], newColCut, configurationSubsetNumber);
                        lamb[i].PushBack(masterModel.AddVar(0, 1, 0, 'C', col));
                        newColGen = true;
                    }
                }
                if (newColGen)
                {
                    if (dualBound > nodeDualBound) nodeDualBound = dualBound;
                    if (globalUpperbound + intTolerance < 1 + nodeDualBound) // prune this node
                    {
                        current->optimized = true;
                        current->lowerbound = nodeDualBound;
                        goto nodeFarkasEnd;
                    }
                    newRowGen = true;
                    masterModel.Solve();
                    if (clock() > start + remainingTime * CLKTCK)
                    {
                        current->optimized = false;
                        goto nodeFarkasEnd;
                    }
                }
            }
            //--------------------
            //---row generation---
            //--------------------
            int currentLB = (int)ceil(masterModel.GetDblAttr("LpObjval") - intTolerance);
            for (int i = 1; i <= (int)globalUpperbound; i++)
            {
                masterModel.Get("Value", x[i], xSol[i]);
                masterModel.Get("Value", y[i], ySol[i]);
            }
            if (globalUpperbound + intTolerance < 1 + currentLB) break;
            if (!newRowGen) break;
            newRowGen = false;
            clock_t startSeparate;
            int direction, i, j, jj, j1, j2, j3, k, id, flight;
            double rhs;
            double* ptr_d = nullptr;
            cons.Clear();
            cons2.Clear();
            if (addCPcuts)
            {
                startSeparate = clock();
                for (i = 1; i <= numTasks; i++)
                {
                    if (directPreds[i][0] < 2) continue;
                    for (j = E[i]; j < L[i]; j++)
                    {
                        direction = separation(i, j);
                        if (direction == 0) continue;
                        if ((current->treeNodeDepth <= 5) && ifExtensionLifting)
                        {
                            // add strengthened CP cuts
                            extensionLifting(direction, i, j);
                            for (id = 1; id <= cover[0]; id++) cons += beta[id] * x[j][cover[id]];
                            if(beta[cover[0] + 1] > 0) cons += beta[cover[0] + 1] * x[j][i];
                        }
                        else
                        {
                            // add original CP cuts
                            for (id = 1; id <= cover[0]; id++) cons += x[j][cover[id]];
                        }
                        if (direction == 1) for (jj = j + 1; jj <= L[i]; jj++) cons2 += x[jj][i];
                        else for (jj = E[i]; jj < j; jj++) cons2 += x[jj][i];
                        for (k = 1; k <= numConfig; k++) cons -= omega[k] * y[j][k];
                        cons -= (cover[numTasks + 1] - 1) * cons2;
                        masterModel.AddConstr(cons <= 0);
                        CPcutNum++;
                        newRowGen = true;
                        cons.Clear();
                        cons2.Clear();
                    }
                }
                separateCPTime += clock() - startSeparate;
            }
            if (addTCcuts) 
            {
                startSeparate = clock();
                //check 2-cut
                for (id = 1; id <= cut_2[0]; id++)
                {
                    j1 = cut_2[id++];
                    j2 = cut_2[id++];
                    if (cut_2[id] > 0)
                    {
                        flight = (int)globalUpperbound + 1 - cut_2[id];
                        rhs = 0.0;
                        for (ptr_d = xSol[(int)globalUpperbound]; ptr_d > xSol[flight] && rhs < 1 + intTolerance; ptr_d -= NUMTASK) rhs += ptr_d[j1] + ptr_d[j2];
                        if (rhs > 1 + intTolerance)
                        {
                            for (i = (int)globalUpperbound; i > flight; i--) cons += (x[i][j1] + x[i][j2]);
                            newRowGen = true;
                            masterModel.AddConstr(cons <= 1);
                            TCcutNum++;
                            cons.Clear();
                        }
                    }
                    id++;
                    if (cut_2[id] > 0)
                    {
                        flight = cut_2[id];
                        rhs = 0.0;
                        for (ptr_d = xSol[1]; ptr_d < xSol[flight] && rhs < 1 + intTolerance; ptr_d += NUMTASK) rhs += ptr_d[j1] + ptr_d[j2];
                        if (rhs > 1 + intTolerance)
                        {
                            for (i = 1; i < flight; i++) cons += (x[i][j1] + x[i][j2]);
                            newRowGen = true;
                            masterModel.AddConstr(cons <= 1);
                            TCcutNum++;
                            cons.Clear();
                        }
                    }
                }
                //check 3-cut
                for (id = 1; id <= cut_3[0]; id++)
                {
                    j1 = cut_3[id++];
                    j2 = cut_3[id++];
                    j3 = cut_3[id++];
                    if (cut_3[id] > 0)
                    {
                        flight = (int)globalUpperbound - cut_3[id] + 1;
                        rhs = 0.0;
                        for (ptr_d = xSol[(int)globalUpperbound]; ptr_d > xSol[flight] && rhs < 2 + intTolerance; ptr_d -= NUMTASK) rhs += ptr_d[j1] + ptr_d[j2] + ptr_d[j3];
                        if (rhs > 2 + intTolerance)
                        {
                            for (i = (int)globalUpperbound; i > flight; i--) cons += (x[i][j1] + x[i][j2] + x[i][j3]);
                            newRowGen = true;
                            masterModel.AddConstr(cons <= 2);
                            TCcutNum++;
                            cons.Clear();
                        }
                    }
                    id++;
                    if (cut_3[id] > 0)
                    {
                        flight = cut_3[id];
                        rhs = 0.0;
                        for (ptr_d = xSol[1]; ptr_d < xSol[flight] && rhs < 2 + intTolerance; ptr_d += NUMTASK) rhs += ptr_d[j1] + ptr_d[j2] + ptr_d[j3];
                        if (rhs > 2 + intTolerance)
                        {
                            for (i = 1; i < flight; i++) cons += (x[i][j1] + x[i][j2] + x[i][j3]);
                            newRowGen = true;
                            masterModel.AddConstr(cons <= 2);
                            TCcutNum++;
                            cons.Clear();
                        }
                    }
                }
                separateTCTime += clock() - startSeparate;
            }   
            if (newRowGen)
            {
                // We add some cuts
                newColGen = true;
                masterModel.Solve();
                if (clock() > start + remainingTime * CLKTCK)
                {
                    current->optimized = false;
                    goto nodeFarkasEnd;
                }
                else goto colAndRowGeneration;
            }
            else break;
        }
        // get the current solution 
        for (int i = 1; i <= (int)globalUpperbound; i++) masterModel.Get("Value", x[i], xSol[i]);
        current->lowerbound = masterModel.GetDblAttr("LpObjval");
        current->integral = true;
        // check if all x_val are all integers/within tolerance
        for (int i = 1; i <= (int)globalUpperbound; i++)
        {
            for (int j = 1; j <= numTasks; j++)
            {
                if ((abs(1 - xSol[i][j]) > intTolerance) && abs(xSol[i][j]) > intTolerance)
                {
                    current->integral = false;
                    break;
                }
            }
            if (!current->integral) break;
        }
        // if results are integers, reset the values to integers
        if (current->integral)
        {
            for (int i = 1; i <= (int)globalUpperbound; i++)
            {
                for (int j = 1; j <= numTasks; j++)
                {
                    if (abs(1 - xSol[i][j]) <= intTolerance) xSol[i][j] = 1;
                    else
                    {
                        if (abs(xSol[i][j]) <= intTolerance) xSol[i][j] = 0;
                        else
                        {
                            std::cerr << "\nERROR! Integrality check error!\n";
                            throw 1;
                            goto nodeFarkasEnd;
                        }
                    }
                }
            }
            current->upperbound = current->lowerbound;
            if (current->upperbound < globalUpperbound)
            {
                // we find a better solution!
                globalUpperbound = ceil(current->upperbound - intTolerance);
                current->upperbound = globalUpperbound;
                current->lowerbound = globalUpperbound;
                for (int i = 1; i <= numTasks; i++) L[i] = (int)globalUpperbound - (int)(tailsLB[i]);
                incumbentSol[0][0] = (int)globalUpperbound;
                for (int j = 1; j <= numTasks; j++)
                {
                    for (int i = 1; i <= (int)globalUpperbound; i++)
                    {
                        if (xSol[i][j] == 1)
                        {
                            incumbentSol[0][j] = i;
                            break;
                        }
                    }
                }
            }
        }
        else 
        {
            for (int i = 1; i <= (int)globalUpperbound; i++) 
            {
                if (lambSize[i] > 0) masterModel.Get("Value", lamb[i], lambSol[i]);      // a bug from COPT....
                else memset(lambSol[i], 0, sizeof(lambSol[i]));
            }
            BPCDivingHeuristic();
            if (globalUpperbound != incumbentSol[0][0])
            {
                // diving heuristic find a better solution
                globalUpperbound = incumbentSol[0][0];
                for (int i = 1; i <= numTasks; i++) L[i] = (int)globalUpperbound - (int)(tailsLB[i]);
            }
            if (current->treeNodeDepth < 15) 
            {
                std::array<std::vector<int>, NUMTASK>().swap(current->valid);
                for (int i = 1; i <= (int)globalUpperbound; i++)
                {
                    int count = 0;
                    for (int currentValidColId = 0; currentValidColId < lambSize[i]; currentValidColId++)
                    {
                        if (lambSol[i][currentValidColId] > intTolerance) current->valid[i].push_back(lambIdList[i][currentValidColId]);
                        else
                        {
                            if (5 * count < lambSize[i])
                            {
                                count++;
                                current->valid[i].push_back(lambIdList[i][currentValidColId]);
                            }
                        }
                    }
                }
            }
            else 
            {
                std::array<std::vector<int>, NUMTASK>().swap(current->valid);
                for (int i = 1; i <= (int)globalUpperbound; i++)
                {
                    for (int currentValidColId = 0; currentValidColId < lambSize[i]; currentValidColId++) current->valid[i].push_back(lambIdList[i][currentValidColId]);
                }
            }
            
            current->optimized = true;
            findBranchingChoice(current);
        }
    }
    catch (const CoptException& e)
    {
        std::cout << "Error code = " << e.GetCode() << std::endl;
        std::cout << e.what() << std::endl;
    }
    catch (...)
    {
        std::cout << "Unknown exception caught\n";
    }
nodeFarkasEnd:
    numNodeExplored++;
    if ((globalUpperbound + intTolerance < 1 + ceil(current->lowerbound - intTolerance)) || current->integral || current->infeasible) current->ifDelete = true;
    totalTime += ((double)clock() - start) / CLKTCK;
    return;
}

void branchPriceAndCut()
{
    BPCCutsPreparation();
    BPCInit();
    BPCNodeFarkas(root);
    //std::cout << "root: " << root->lowerbound << std::endl;
    if (!root->optimized) numNodeExplored = -1;
    if (totalTime >= runTimeLimit) overTime = true;
    clock_t start = clock();
    if (!overTime && !root->integral && globalUpperbound + intTolerance >= root->lowerbound + 1 && !root->infeasible) // if not integrally optimal and initUB-LB>=1, put it in the stack to branch 
    {
        stackPush(root);
        root->treeNodeDepth++;
    }
    else
    {
        if (root->infeasible) instanceFeasibility = 0;
        listAdd(root);
    }
    bool UB_update;
    int dep_stack = 0;                              //counter of the depth of stack
    totalTime += double(clock() - start) / CLKTCK;
    //stack is not empty, do this loop
    while (stackTop != bottom && !overTime && !overStack && instanceFeasibility != 0)
    {
        start = clock();                            //start the timer
        Node* par = stackPop();                     //pop the first Node in tha stack
        UB_update = false;                          //initial indicators for children
        Node* lcurrent = listTake();                //generate the left child for the first node in stack
        Node* rcurrent = listTake();                //generate the right child for the first Node in stack
        BPCPrepareChild(par, lcurrent, 1);          //prepare the left child
        BPCPrepareChild(par, rcurrent, 2);          //prepare the right child
        totalTime += double(clock() - start) / CLKTCK;
        if (!lcurrent->ifDelete) BPCNodeFarkas(lcurrent);  //explore the left child
        if (totalTime >= runTimeLimit) overTime = true;
        if (!rcurrent->ifDelete) BPCNodeFarkas(rcurrent);  //explore the right child
        if (totalTime >= runTimeLimit) overTime = true;
        start = clock();
        listAdd(par);                              //recycle the parent Node
        //update indicators and recycle the children
        if ((lcurrent->upperbound == globalUpperbound && lcurrent->integral) || (rcurrent->upperbound == globalUpperbound && rcurrent->integral)) UB_update = true;
        //based on different situations, update stack
        if (!lcurrent->ifDelete && !rcurrent->ifDelete) 
        {
            //according to the lowerbound, push the larger one first, pop the smaller first 
            if (rcurrent->lowerbound < lcurrent->lowerbound || rcurrent->criterion < lcurrent->criterion)
            {
                stackPush(lcurrent);
                stackPush(rcurrent);
            }
            else
            {
                stackPush(rcurrent);
                stackPush(lcurrent);
            }
            //std::cout << lcurrent->treeNodeDepth << "  " << lcurrent->lowerbound << ", " << rcurrent->treeNodeDepth << "  " << rcurrent->lowerbound << std::endl;
        }
        else if (lcurrent->ifDelete && !rcurrent->ifDelete)
        {
            listAdd(lcurrent);
            stackPush(rcurrent);
            //std::cout << "Ldel, " << rcurrent->treeNodeDepth << "  " << rcurrent->lowerbound << std::endl;
        }
        else if (!lcurrent->ifDelete && rcurrent->ifDelete) 
        {
            listAdd(rcurrent);
            stackPush(lcurrent);
            //std::cout << lcurrent->treeNodeDepth << "  " << lcurrent->lowerbound << ", Rdel" << std::endl;
        }
        else 
        {
            listAdd(lcurrent);
            listAdd(rcurrent);
            //std::cout << "Ldel, Rdel" << std::endl;
        }
        //when UB updated, prune the stack
        if (UB_update) stackPrune();
        //update the stack depth
        if (stackDepth() > dep_stack)
        {
            dep_stack = stackDepth();
            if (dep_stack + 1> MAXNODE) overStack = true; //stack overflow 
        }
        totalTime += (double)(clock() - start) / CLKTCK;  //count timer
        if (totalTime >= runTimeLimit) overTime = true;   //over time
    }
    BPCFree();
}