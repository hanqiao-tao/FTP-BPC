// The bounded dynamic programming heuristic for finding an initial solution.
// Please read the article "Tao et al. Flight test scheduling: A generic model, lower bounds, and iterated local search, EJOR, 2025." for more details
#include "FTP.h"
struct Data
{
    double weight;
    char degrees[NUMTASK];
    char taskPosition[NUMTASK];
    short int numDo;
    bool operator==(const Data& cmp) const
    {
        return (memcmp(degrees, cmp.degrees, numTasks + 1) == 0);
    }
};

struct DataHash
{
    size_t operator()(const Data& d) const
    {
        return XXH3_64bits(d.degrees, numTasks + 1);
    }
};

struct compare_pq
{
    bool operator()(const Data& l, const Data& r)  const
    {
        return l.weight < r.weight;
    }
};

static int optimalBDP;
static int UB_BDP;
static int flightConfiguration[NUMTASK];
static int eligible[NUMTASK];
static int tasks[NUMTASK];
static int listDo[NUMTASK];                    //memory to keep a listing of items
static int maxLoads;
static int numFullLoad;
static int windowsWidth;         //parameters for dynamic programming heuristic
static int maxTransit;
static int flight;

static Data elements;      
static std::priority_queue<Data, std::vector<Data>, compare_pq > heapOld;
static std::priority_queue<Data, std::vector<Data>, compare_pq > heapEnumera;
static std::priority_queue<Data, std::vector<Data>, compare_pq > heapNew;
static boost::unordered_flat_set<Data, DataHash> State;
static boost::unordered_flat_map<Data, int, DataHash> States;
static boost::unordered_flat_map<Data, int, DataHash>::iterator it;
static Data el;

static int* Bipartite[NUMTASK];         // adjacent table for the bipartite graph
static int* match;					    // match[i] stores which point in V2 is matched with i in V1; -1, otherwise
static bool* vis;					    // vis[i] stores whether i in V2 is visited or not in DFS

static bool configFeasible[5] = { true };
static bool* ptr_bool;
static double ac[kMax];
static int tFeasible;
static int gap;

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
static inline bool hungarian()
{
    int res = 0;
    // construct the bipartite graph
    for (int i = 0; i <= numTasks; i++)
    {
        MALLOC(Bipartite[i], CkSum[numConfig] + 1, int);
        Bipartite[i][0] = 0;
    }
    std::vector<std::vector<int>> feasible_config(flight + 1, std::vector<int>(numConfig + 1, 1));
    for (int i = 1; i <= numTasks; i++)
    {
        for (int k = 1; k <= numConfig; k++)
        {
            if (!configMatr[k][i])
            {
                feasible_config[elements.taskPosition[i]][k] = 0;
            }
        }
    }
    for (int u = 1; u <= flight; u++)
    {
        for (int k = 1; k <= numConfig; k++)
        {
            if (feasible_config[u][k] == 1)
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
    for (int u = 1; u <= flight; u++)
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
    if (res == flight) return true;
    return false;
}

static void BDPInit(int version)
{
    optimalBDP = 1;
    if (version) UB_BDP = numTasks;
    else UB_BDP = incumbentSol[0][0];
    gap = UB_BDP - (int) rootLB;

    memset(eligible, 0, sizeof(eligible));
    memset(tasks, 0, sizeof(tasks));
    for (int i = 0; i <= numTasks; i++) listDo[i] = i;
    int delta = 1;
    while (delta > 0)
    {
        delta = 0;
        for (int i = 1; i <= numTasks - 1; i++)
        {
            if (tailsLB[listDo[i]] < tailsLB[listDo[i + 1]])
            {
                delta = listDo[i];
                listDo[i] = listDo[i + 1];
                listDo[i + 1] = delta;
            }
        }
    }
    windowsWidth = 1000;
    maxTransit = 250;
    maxLoads = 100;
    memset(elements.degrees, 0, sizeof(elements.degrees));
    memset(elements.taskPosition, 0, sizeof(elements.taskPosition));
    for (int i = 1; i <= numTasks; i++) elements.degrees[i] = directPreds[i][0];
    elements.weight = 0.0;
    elements.numDo = 0;
}

static void BDPFree() 
{
    heapNew = std::priority_queue<Data, std::vector<Data>, compare_pq >();
    heapOld = std::priority_queue<Data, std::vector<Data>, compare_pq >();
    heapEnumera = std::priority_queue<Data, std::vector<Data>, compare_pq >();

    boost::unordered_flat_set<Data, DataHash>().swap(State);
    boost::unordered_flat_map<Data, int, DataHash>().swap(States);
    if (optimalBDP == 1 && initFeasiblity) rootLB = incumbentSol[0][0];
    else if (optimalBDP == 1 && !initFeasiblity) instanceFeasibility = 0;
}

static inline bool saveBestSolution()
{
    memset(flightConfiguration, -1, sizeof(flightConfiguration));
    bool flag = hungarian();
    if (flag)
    {
        instanceFeasibility = 1;
        initFeasiblity = 1;
        for (int i = 1; i <= numTasks; i++)
        {
            L[i] = flight - (int)(floor(tailsLB[i] + intTolerance));
        }
        std::vector<std::vector<int>>().swap(incumbentSol);
        incumbentSol.push_back(std::vector<int>(numTasks + 1));
        incumbentSol.push_back(std::vector<int>(flight + 1));
        incumbentSol[0][0] = flight;
        for (int i = 1; i <= numTasks; i++) incumbentSol[0][i] = elements.taskPosition[i];
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
        heapNew = std::priority_queue<Data, std::vector<Data>, compare_pq >();
        heapOld = std::priority_queue<Data, std::vector<Data>, compare_pq >();
        heapEnumera = std::priority_queue<Data, std::vector<Data>, compare_pq >();
    }
    free(match);
    match = NULL;
    return flag;
}

// pre-compute Jackson's rule
static void computePotentiallyDominate()
{
    int superset1, superset2;
    for (int i = 1; i <= numTasks; i++)
    {
        for (int j = 1; j <= numTasks; j++)
        {
            if ((i != j) && (taskTime[i] >= taskTime[j]) && (!transMatr[i][j]) && (!transMatr[j][i]))
            {
                superset1 = 0;
                superset2 = 0;
                bool flag = true;
                for (int k = 1; k <= numConfig; k++)
                {
                    if (configMatr[k][i] > configMatr[k][j])
                    {
                        //no dominance
                        superset2 = (-1);
                        break;
                    }
                    else if (configMatr[k][i] < configMatr[k][j]) superset2 = 1;
                }
                if (superset1 > -1)
                {
                    for (int kk = 1; kk <= numTasks; kk++)
                    {
                        if (transMatr[i][kk] < transMatr[j][kk])
                        {
                            //no dominance
                            superset1 = (-1);
                            break;
                        }
                        else if (transMatr[i][kk] > transMatr[j][kk]) superset1 = 1;
                    }
                }
                if (superset1 == -1 || superset2 == -1) flag = false;
                else if (superset1 == 0 && superset2 == 0 && taskTime[i] == taskTime[j] && i < j) flag = false;

                if (flag) potentiallyDominate[i][j] = true;
            }
        }
    }
}

static void determineDominance(int position, int task, int num_task, std::vector<int> listIsomorphism, std::vector<int> listOrigin, int& conIsomorphism) //todo
{
    if (conIsomorphism == 1) return;
    if (position == num_task)
    {
        conIsomorphism = 1;
        return;
    }
    position++;
    int j;
    for (int candidata = 1; candidata <= numTasks; candidata++) 		//The following candidates need to verify
    {
        //1. The duration is the same as that of the equivalent task (list origin[position]]).
        if (taskTime[candidata] != taskTime[listOrigin[position]]) continue;
        //2. Having the same or more successors as the same task.
        if (allSucs[listOrigin[position]][0] > allSucs[candidata][0]) continue;
        //3. Unassigned
        for (j = 1; j < position; j++)
        {
            if (listIsomorphism[j] == candidata) j = 1000;
        }
        if (j >= 1000) continue;
        //4. Meet precedence *** Remember that the precedence matrix is the highest ***
        for (j = 1; j < position; j++)
        {
            if (transMatr[listOrigin[j]][listOrigin[position]] != transMatr[listIsomorphism[j]][candidata])
            {
                j = 1000;
                break;
            }
            if (transMatr[listOrigin[position]][listOrigin[j]] != transMatr[candidata][listIsomorphism[j]])
            {
                j = 1000;
                break;
            }
            if (adjMatr[listOrigin[j]][listOrigin[position]] != adjMatr[listIsomorphism[j]][candidata])
            {
                j = 1000;
                break;
            }
            if (adjMatr[listOrigin[position]][listOrigin[j]] != adjMatr[candidata][listIsomorphism[j]])
            {
                j = 1000;
                break;
            }
        }
        if (j >= 1000) continue;

        determineDominance(position, candidata, num_task, listIsomorphism, listOrigin, conIsomorphism);
    }
    return;
}

// Basic isomorphism detection, not much efficient
static void dectectDominanceIsomorphism()
{
    std::vector<int> listIsomorphism(numTasks + 1);
    std::vector<int> listOrigin(numTasks + 1);
    int num_task;
    int conIsomorphism;
    for (int j1 = 1; j1 <= numTasks; j1++)
    {
        num_task = 1;
        listOrigin[num_task] = j1;
        for (int i = 1; i <= numTasks; i++)
        {
            if (transMatr[j1][i])
            {
                num_task++;
                listOrigin[num_task] = i;
            }
        }
        for (int j2 = 1; j2 <= numTasks; j2++)
        {
            if ((j1 != j2) && (taskTime[j2] >= taskTime[j1]) && (!potentiallyDominate[j1][j2]) && (!potentiallyDominate[j2][j1]) && (!transMatr[j1][j2]) && (!transMatr[j2][j1]))
            {
                // Test successor theme (the total number of successors must be equal to or greater than)
                if (allSucs[j2][0] >= allSucs[j1][0])
                {
                    conIsomorphism = 0;
                    determineDominance(1, j2, num_task, listIsomorphism, listOrigin, conIsomorphism);
                    if (conIsomorphism == 1)
                    {
                        int superset1 = 0;
                        for (int k = 1; k <= numConfig; k++)
                        {
                            if (configMatr[k][j2] > configMatr[k][j1])
                            {
                                //no dominance
                                superset1 = (-1);
                                break;
                            }
                            else if (configMatr[k][j2] < configMatr[k][j1]) superset1 = 1;
                        }
                        if (taskTime[j2] >= taskTime[j1] && superset1 >= 0)
                        {
                            if (superset1 == 1 || taskTime[j2] > taskTime[j1]) potentiallyDominate[j2][j1] = true;
                            else if (j2 < j1) potentiallyDominate[j2][j1] = true;
                        }
                    }
                }
            }
        }
    }
}

// Solitary task test and creation of bin
static inline int taskSolitary(int numEligible, int version)
{
    int result, i, j, ii, jj, k, task, taskTimeVal;

    for (i = 1; i <= numEligible; i++)
    {
        result = 1; // YES
        task = eligible[i];
        taskTimeVal = taskTime[task];

        for (j = 1; (j <= numTasks) && (result == 1); j++)
        {
            if (elements.degrees[j] >= 0 && (task != j) && !transMatr[task][j] && !transMatr[j][task] && taskTimeVal + taskTime[j] <= timeCap)
            {
                for (k = 1; k <= compatibleSet[task][0]; k++)
                {
                    if (configMatrTranspose[j][k])
                    {
                        result = 0; //NO
                        break;
                    }
                }

            }
        }
        if (result == 1)
        {
            // We can assign a single task(consider it as an element in the heap)
            elements.numDo++;
            elements.degrees[task] = -1;
            elements.taskPosition[task] = flight;
            for (jj = 1; jj <= directSucs[task][0]; jj++)
            {
                elements.degrees[directSucs[task][jj]]--;
            }
            if (elements.numDo == numTasks)
            {
                if (saveBestSolution()) return 1;
            }
            if (!version) 
            {
                // Jackson rule
                for (jj = 1; jj <= numEligible; jj++)
                {
                    ii = eligible[jj];
                    if (elements.degrees[ii] == 0 && potentiallyDominate[ii][task]) return 1; //eligible[jj] dominate a tasks[j]
                }
            }
            // compute lower bound
            double bestBound = 0.0;
            memset(ac, 0, sizeof(ac));
            int position;
            double tails;
            for (int id = 1; id <= numTasks; id++)
            {
                ii = listDo[id];
                tails = tailsLB[ii];
                if (elements.degrees[ii] >= 0)
                {
                    position = ii;
                    for (j = 0; j < 10; j++, position += NUMTASKSQUARE)
                    {
                        ac[j] += dataLB[position];
                        if (ac[j] + tails > bestBound) bestBound = ac[j] + tails;
                    }
                }
            }
            if (ceil(bestBound - intTolerance) + flight >= UB_BDP) return 1;
            elements.weight = timeCap - (taskTime[task] + 0.001 * positionalWeight[task] + 0.05 * directSucs[task][0]);
            elements.weight += bestBound * (double)timeCap;
            // all rules passed
            if (!version && States.find(elements) == States.end()) States.insert(std::make_pair(elements, flight));
            heapEnumera.emplace(elements);
            return 1;
        }
    }
    return (0);
}

static void genLoadBDP(int depth, int remainingTime, int start, int numEligible, int version)
{
    int fullLoad = 1;
    int numSubEligible, i, ii, j, jj, k, ifConfigCompatible = 1;
    bool configFeasibleOld[5];
    int task;
    for (ii = start; ii <= numEligible; ii++)
    {
        task = eligible[ii];
        if (taskTime[task] <= remainingTime)
        {
            if (numConfig > 1)
            {
                memcpy(&configFeasibleOld[1], &configFeasible[1], numConfig);
                ifConfigCompatible = 0;
                for (k = 1; k <= numConfig; k++)
                {
                    if (configMatr[k][task] && configFeasible[k]) ifConfigCompatible++;
                    else configFeasible[k] = false;
                }
            }
            if (ifConfigCompatible > 0)
            {
                tasks[depth] = task;
                elements.numDo++;
                elements.degrees[task] = -1;
                elements.taskPosition[task] = flight;
                tFeasible -= taskTime[task];
                numSubEligible = numEligible;
                fullLoad = 0;
                for (jj = 1; jj <= directSucs[task][0]; jj++) elements.degrees[directSucs[task][jj]]--;
                
                genLoadBDP(depth + 1, remainingTime - taskTime[task], ii + 1, numSubEligible, version);
                if (numFullLoad >= maxLoads && version)
                {
                    optimalBDP = 0;
                    return;
                }
                tFeasible += taskTime[task];
                tasks[depth] = -1;
                elements.numDo--;
                elements.degrees[task] = 0;
                elements.taskPosition[task] = 0;
                if (numConfig > 1) memcpy(&configFeasible[1], &configFeasibleOld[1], numConfig);
                // Increment the degree of every successor of i.
                for (jj = 1; jj <= directSucs[task][0]; jj++) elements.degrees[directSucs[task][jj]]++;
            }
        }
    }
    // check if we attain a full load (maximum load rule)
    for (ii = 1; ii <= numEligible && fullLoad == 1; ii++) 
    {
        task = eligible[ii];
        if (elements.degrees[task] != 0) continue;
        if (remainingTime < taskTime[task]) continue;
        if (numConfig == 1)
        {
            fullLoad = 0;
            break;
        }
        ptr_bool = configMatrTranspose[task];
        for (k = 1; (k <= numConfig) && (fullLoad == 1); k++)
        {
            if (configFeasible[k] && ptr_bool[k])
            {
                fullLoad = 0;
                break;
            }
        }
    }
    // we find a full load
    if (fullLoad == 1)
    {
        // If there are no tasks assigned to this flight, then return.
        if (depth == 1) return;
        numFullLoad++;
        if (elements.numDo == numTasks)  // check whether we find a task-flight assignment
        {
            if (saveBestSolution()) return;
        }
        // lower bound
        double bestBound = 0.0;
        memset(ac, 0, sizeof(ac));
        int position;
        double tails;
        elements.weight = 0.0;
        for (ii = 1; ii <= numTasks; ii++)
        {
            task = listDo[ii];
            tails = tailsLB[task];
            if (elements.degrees[task] >= 0)
            {
                position = task;
                for (j = 0; j < 10; j++, position += NUMTASKSQUARE)
                {
                    ac[j] += dataLB[position];
                    if (ac[j] + tails > bestBound) bestBound = ac[j] + tails;
                }
            }
        }
        if (ceil(bestBound - intTolerance) + flight >= UB_BDP) return;
        elements.weight = timeCap;
        for (int i = 1; i < depth; i++)
        {
            elements.weight -= (taskTime[tasks[i]] + 0.001 * positionalWeight[tasks[i]] + 0.05 * directSucs[tasks[i]][0]);
        }
        elements.weight += bestBound * (double)timeCap;
        if (heapEnumera.size() >= maxTransit && elements.weight + intTolerance > heapEnumera.top().weight) return;    // a worse state

        if (numConfig == 1)
        {
            // modified SPR rule (used in the BBR-CBFS, 2012)
            ii = 0;
            for (i = 1; i < depth && ii == 0; i++)
            {
                if (directSucs[tasks[i]][0] > 0)  ii = 1;
            }
            if (ii == 0)
            {
                for (i = 1; i <= numTasks; i++)
                {
                    if (elements.degrees[i] >= 0 && directSucs[i][0] > 0) return;
                }
            }
        }
        if (!version)
        {
            // Jackson rule
            for (j = 1; j < depth; j++)
            {
                i = tasks[j];
                for (jj = 1; jj <= numEligible; jj++)
                {
                    ii = eligible[jj];
                    if (elements.degrees[ii] == 0 && potentiallyDominate[ii][i] && remainingTime + taskTime[i] >= taskTime[ii])
                    {
                        return; //eligible[jj] dominate a tasks[j]
                    }
                }
            }
            // Next verify memory-based rule:
            // (1) If there is a superset of the current partial solution in memory. If such a partial solution with a smaller flight exists, stop the exploration of current vertex
            // (2) If there is a dominating (according to Jackson's rule) partial solution in memory
            for (i = 1; i <= numTasks; i++)
            {
                if (elements.degrees[i] != 0) continue;
                if (taskTime[i] <= tFeasible)
                {
                    // verify if there is a superset of the current partial solution in memory (generalized max load rule)
                    memcpy(el.degrees, elements.degrees, numTasks + 1);
                    el.degrees[i]--;
                    for (jj = 1; jj <= directSucs[i][0]; jj++) el.degrees[directSucs[i][jj]]--;
                    if (States.find(el) != States.end()) return;

                    // pass the generalized max load rule, verify (generalized) item dominance rule
                    // there is no need to copy el.degrees again
                    if (CkLabel == 1)
                    {
                        for (ii = 1; ii <= numTasks; ii++)
                        {
                            if ((potentiallyDominate[i][ii]) && (elements.degrees[ii] < 0) && (tFeasible + taskTime[ii] >= taskTime[i]))
                            {
                                el.degrees[ii]++;
                                for (jj = 1; jj <= directSucs[ii][0]; jj++) el.degrees[directSucs[ii][jj]]++;
                                // we update values of el
                                if (States.find(el) != States.end()) return;
                                // reset
                                el.degrees[ii]--;
                                for (jj = 1; jj <= directSucs[ii][0]; jj++) el.degrees[directSucs[ii][jj]]--;
                            }
                        }
                    }
                    else
                    {
                        bool flag;
                        for (j = 1; j < depth; j++)
                        {
                            ii = tasks[j];
                            if (potentiallyDominate[i][ii])
                            {
                                flag = true;
                                for (k = 1; k <= numConfig; k++)
                                {
                                    if (configFeasible[k] && !configMatrTranspose[i][k])  // a novel trick to meet condition 4
                                    {
                                        flag = false;
                                        break;
                                    }
                                }
                                if (flag)
                                {
                                    el.degrees[ii]++;
                                    for (jj = 1; jj <= directSucs[ii][0]; jj++) el.degrees[directSucs[ii][jj]]++;
                                    if (States.find(el) != States.end()) return;
                                    // reset
                                    el.degrees[ii]--;
                                    for (jj = 1; jj <= directSucs[ii][0]; jj++) el.degrees[directSucs[ii][jj]]--;
                                }
                            }
                        }
                    }
                }
                else
                {
                    // do not need to verify generalized max load rule, and directly verify (generalized) item dominance rule
                    if (CkLabel == 1)
                    {
                        memcpy(el.degrees, elements.degrees, numTasks + 1);
                        el.degrees[i]--;
                        for (jj = 1; jj <= directSucs[i][0]; jj++) el.degrees[directSucs[i][jj]]--;
                        for (ii = 1; ii <= numTasks; ii++)
                        {
                            if ((potentiallyDominate[i][ii]) && (elements.degrees[ii] < 0) && (tFeasible + taskTime[ii] >= taskTime[i]))
                            {
                                el.degrees[ii]++;
                                for (jj = 1; jj <= directSucs[ii][0]; jj++) el.degrees[directSucs[ii][jj]]++;
                                if (States.find(el) != States.end()) return;
                                el.degrees[ii]--;
                                for (jj = 1; jj <= directSucs[ii][0]; jj++) el.degrees[directSucs[ii][jj]]--;
                            }
                        }
                    }
                    else
                    {
                        bool flag;
                        for (j = 1; j < depth; j++)
                        {
                            ii = tasks[j];
                            if (potentiallyDominate[i][ii] && (elements.degrees[ii] < 0) && (tFeasible + taskTime[ii] >= taskTime[i]))
                            {
                                flag = true;
                                for (k = 1; k <= numConfig; k++)
                                {
                                    if (configFeasible[k] && !configMatrTranspose[i][k])  // a novel trick to meet condition 4
                                    {
                                        flag = false;
                                        break;
                                    }
                                }
                                if (flag)
                                {
                                    memcpy(el.degrees, elements.degrees, numTasks + 1);
                                    el.degrees[i]--;
                                    for (jj = 1; jj <= directSucs[i][0]; jj++) el.degrees[directSucs[i][jj]]--;
                                    el.degrees[ii]++;
                                    for (jj = 1; jj <= directSucs[ii][0]; jj++) el.degrees[directSucs[ii][jj]]++;
                                    if (States.find(el) != States.end()) return;
                                }
                            }
                        }
                    }
                }
            }
            // all rules passed
            States.insert(std::make_pair(elements, flight));
        }

        if (heapEnumera.size() < maxTransit) heapEnumera.emplace(elements);
        else
        {
            optimalBDP = 0;
            heapEnumera.pop();
            heapEnumera.emplace(elements);
        }
    }
}

void bdp(int version)
{
    clock_t start = clock();
    if (!version) 
    {
        computePotentiallyDominate();
        dectectDominanceIsomorphism();
    }
    BDPInit(version);
    int i, step, numEligible, pass;
    heapNew.emplace(elements);
    if (!version) States.insert(std::make_pair(elements, 0));
    for (step = 1; step <= UB_BDP; step++)
    {
        //cout << "step " << step << " number of states: " << heapNew.size() <<"\t" << States.size() << endl;
        if (clock() >= start + 30 * CLKTCK) break;
        flight = step;
        if (heapNew.empty()) break;
        swap(heapNew, heapOld);
        while (!heapOld.empty())
        {
            if (clock() >= start + 30 * CLKTCK) break;
            elements = heapOld.top();
            heapOld.pop();
            pass = 1;
            if (!version)
            {
                it = States.find(elements);
                if (it == States.end()) continue;
                if (it->second < 0) pass = 0;
                else it->second = 0 - it->second;
            }
            if (pass == 1)
            {
                numEligible = 0;
                numFullLoad = 0;
                tFeasible = flight * timeCap;
                for (i = 1; i <= numTasks; i++)
                {
                    if (elements.degrees[i] == 0) eligible[++numEligible] = i;
                    else if (elements.degrees[i] < 0) tFeasible -= taskTime[i];
                }
                if (taskSolitary(numEligible, version) == 0)
                {
                    memset(configFeasible, true, 5);
                    genLoadBDP(1, timeCap, 1, numEligible, version);
                }
                while (!heapEnumera.empty())
                {
                    elements = heapEnumera.top();
                    heapEnumera.pop();
                    if (State.find(elements) == State.end())
                    {
                        if (heapNew.size() < windowsWidth)
                        {
                            State.insert(elements);
                            heapNew.emplace(elements);
                        }
                        else
                        {
                            optimalBDP = 0;
                            if (heapNew.top().weight > elements.weight)
                            {
                                State.insert(elements);
                                heapNew.pop();
                                heapNew.emplace(elements);
                            }
                        }
                    }
                }
            }
        }
        boost::unordered_flat_set<Data, DataHash>().swap(State);
        if (!version) 
        {
            it = States.begin();
            while (it != States.end())
            {
                int tmp = it->second;
                if (tmp > 0)
                {
                    if (tmp + gap < flight) it = States.erase(it);
                    else it++;
                }
                else
                {
                    if (flight + tmp > gap) it = States.erase(it);
                    else it++;
                }
            }
        }
    }
    BDPFree();
    initTime += double(clock() - start) / CLKTCK;
}