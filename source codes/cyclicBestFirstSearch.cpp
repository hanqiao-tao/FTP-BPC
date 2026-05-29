// cyclic best first search, called after the second BDP.
// for proving optimality or find better soluton.
#include "FTP.h"

struct DataCBFS
{
	double weight;
	char degrees[NUMTASK];
    char taskPosition[NUMTASK];
    short int numDo;
	bool operator==(const DataCBFS& cmp) const
	{
		return (memcmp(degrees, cmp.degrees, numTasks + 1) == 0);
	}
    DataCBFS &operator=(const DataCBFS& other)
    {
        weight = other.weight;
        memcpy(degrees, other.degrees, numTasks + 1);
        memcpy(taskPosition, other.taskPosition, numTasks + 1);
        numDo = other.numDo;
        return *this;
    }
};

struct compareCBFS_inv
{
	bool operator()(const DataCBFS& l, const DataCBFS& r) const
	{
		return l.weight > r.weight;
	}
};

struct DataCBFSHash
{
	size_t operator()(const DataCBFS& d) const
	{
		return XXH3_64bits(d.degrees, numTasks + 1);
	}
};

static int optimalCBFS;
static int* eligible;
static int* tasks;
static int* listDo;
static int* flightConfiguration;
static DataCBFS elements;
static DataCBFS el;

static std::priority_queue<DataCBFS, std::vector<DataCBFS>, compareCBFS_inv> Heaps[NUMTASK];
static boost::unordered_flat_map<DataCBFS, char, DataCBFSHash> States[NUMTASK];
static boost::unordered_flat_map<DataCBFS, char, DataCBFSHash>::iterator it;

static int flight;
static bool configFeasible[5] = { true };
static int numFullLoad;
static double ac[kMax];
static int tFeasible;
static bool* ptrBool;

static int* Bipartite[NUMTASK];         // adjacent table for the bipartite graph
static int* match;					    // match[i] stores which point in V2 is matched with i in V1; -1, otherwise
static bool* vis;					    // vis[i] stores whether i in V2 is visited or not in DFS
static bool feasible_config[5][NUMTASK];

static void initializeCBFS() 
{
    initUB = incumbentSol[0][0];
    optimalCBFS = 1;
    eligible = new int[numTasks + 1];
    memset(eligible, 0, (numTasks + 1) * sizeof(int));

    tasks = new int[numTasks + 1];
    memset(tasks, 0, (numTasks + 1) * sizeof(int));

    listDo = new int[numTasks + 1];
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

    flightConfiguration = new int[numTasks + 1];

    elements.weight = 0.0;
    elements.degrees[0] = 0;
    for (int i = 1; i <= numTasks; i++) elements.degrees[i] = directPreds[i][0];
    memset(elements.taskPosition, 0, sizeof(elements.taskPosition));
    elements.numDo = 0;
    el = elements;
    
    Heaps[0].push(elements);
    //for (int i = 0; i < initUB; i++) States[i].reserve(100003);  // 1000003?
    States[0].insert(std::make_pair(elements, 0));
}

static void freeCBFS() 
{
    delete[] eligible;
    delete[] tasks;
    delete[] listDo;
    delete[] flightConfiguration;

    for (int i = 0; i < NUMTASK; i++) boost::unordered_flat_map<DataCBFS, char, DataCBFSHash>().swap(States[i]);
    for (int i = 0; i < NUMTASK; i++) std::priority_queue<DataCBFS, std::vector<DataCBFS>, compareCBFS_inv>().swap(Heaps[i]);

    // we have obtained an optimal instance
    if (optimalCBFS == 1 && initFeasiblity == 1) rootLB = incumbentSol[0][0];
    else if (optimalCBFS == 1 && initFeasiblity == 0) instanceFeasibility = 0;
}

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
    memset(feasible_config, 1, sizeof(feasible_config));
    for (int k = 1; k <= numConfig; k++) 
    {
        for (int i = 1; i <= numTasks; i++) 
        {
            if (!configMatr[k][i]) 
            {
                feasible_config[k][elements.taskPosition[i]] = 0;
            }
        }
    }
    for (int k = 1; k <= numConfig; k++) 
    {
        for (int u = 1; u <= flight; u++) 
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

static inline bool saveBestSolutionCBFS()
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
        initUB = incumbentSol[0][0];
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
    }
    else optimalCBFS = 0;
    free(match);
    match = NULL;
    return flag;
}

static inline int taskSolitaryCBFS(int numEligible) 
{
    int result, ii, j, jj, task_time, i, k;
    for (i = 1; i <= numEligible; i++)
    {
        result = 1; // YES
        int task = eligible[i];
        task_time = taskTime[task];
        for (j = 1; (j <= numTasks) && (result == 1); j++)
        {
            if (elements.degrees[j] >= 0 && (task != j) && !transMatr[task][j] && !transMatr[j][task] && task_time + taskTime[j] <= timeCap)
            {
                for (k = 1; k <= compatibleSet[task][0]; k++)
                {
                    if (configMatrTranspose[j][compatibleSet[task][k]])
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
            tFeasible -= task_time;
            if (elements.numDo == numTasks)
            {
                // we try to find a better solution
                if(saveBestSolutionCBFS()) return 1;
            }

            // Jackson rule
            for (jj = 1; jj <= numEligible; jj++)
            {
                ii = eligible[jj];
                if (elements.degrees[ii] == 0 && potentiallyDominate[ii][task])
                {
                    return 1;//eligible[jj] dominate a tasks[j]
                }
            }

            // compute lower bound
            double bestbound = 0.0;
            int position;
            double tails;
            memset(ac, 0, sizeof(ac));
            for (int id = 1; id <= numTasks; id++)
            {
                ii = listDo[id];
                tails = tailsLB[ii];
                if (elements.degrees[ii] >= 0)
                {
                    position = ii;
                    for (int j = 0; j < 10; j++, position += NUMTASKSQUARE)
                    {
                        ac[j] += dataLB[position];
                        if (ac[j] + tails > bestbound) bestbound = ac[j] + tails;
                    }
                }
            }
            if (ceil(bestbound - intTolerance) + flight >= initUB) return 1;
            elements.weight = timeCap - (taskTime[task]);
            elements.weight += bestbound * (double)timeCap;

            // all rules passed
            int ok;
            for (ok = flight; ok < initUB; ok++)
            {
                it = States[ok].find(elements);
                if (it != States[ok].end())
                {
                    if (ok > flight)
                    {
                        States[ok].erase(it);
                        States[flight].insert(std::make_pair(elements, flight));
                        Heaps[flight].push(elements);
                    }
                    break;
                }
            }
            if (ok == initUB)
            {
                // we find a new element
                States[flight].insert(std::make_pair(elements, flight));
                Heaps[flight].push(elements);
            }
            return 1;
        }
    }
    return 0;
}

static void genLoadsCBFS(int depth, int remainingTime, int start, int numEligible) 
{  
    int fullLoad = 1;
    int numSubEligible, ii, j, jj, k, ifConfigCompatible = 1;
    
    bool configFeasibleOld[5] = { true, true, true, true, true };
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
                    if (configMatrTranspose[task][k] && configFeasible[k]) ifConfigCompatible++;
                    else configFeasible[k] = false;
                }
            }
            if (ifConfigCompatible == 0) continue;

            tasks[depth] = task;
            elements.degrees[task] = -1;
            elements.taskPosition[task] = flight;
            elements.numDo++;
            tFeasible -= taskTime[task];
            numSubEligible = numEligible;
            fullLoad = 0;
            for (jj = 1; jj <= directSucs[task][0]; jj++)
            {
                elements.degrees[directSucs[task][jj]]--;
            }
            genLoadsCBFS(depth + 1, remainingTime - taskTime[task], ii + 1, numSubEligible);
            if (numFullLoad >= 10000) 
            {
                optimalCBFS = 0;
                return;
            }
            tFeasible += taskTime[task];
            tasks[depth] = -1;
            elements.degrees[task] = 0;
            elements.taskPosition[task] = 0;
            elements.numDo--;
            if (numConfig > 1) memcpy(&configFeasible[1], &configFeasibleOld[1], numConfig);
            // Increment the degree of every successor of i.
            for (jj = 1; jj <= directSucs[task][0]; jj++)
            {
                elements.degrees[directSucs[task][jj]]++;
            }
        }
    }
    for (ii = 1; (ii <= numEligible) && (fullLoad == 1); ii++)
    {
        task = eligible[ii];
        if (remainingTime < taskTime[task]) continue;
        if (elements.degrees[task] != 0) continue;
        if (numConfig == 1)
        {
            fullLoad = 0;
            break;
        }
        else 
        {
            ptrBool = configMatrTranspose[task];
            for (k = 1; (k <= numConfig) && (fullLoad == 1); k++)
            {
                if (configFeasible[k] && ptrBool[k])
                {
                    fullLoad = 0;
                    break;
                }
            }
        }
    }
    if (fullLoad == 1) 
    {
        // If there are no tasks assigned to this flight, then return.
        if (depth == 1) return;
        if (elements.numDo == numTasks)
        {
            // we try to find a better solution
            if (saveBestSolutionCBFS()) return;
        }
        // Jackson rule
        int i;
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
        numFullLoad++;
        // compute lower bound
        double bestbound = 0.0;
        memset(ac, 0, sizeof(ac));
        int position;
        double tails;
        int idle_time = 0;
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
                    if (ac[j] + tails > bestbound) bestbound = ac[j] + tails;
                }
            }
            else idle_time += taskTime[task];
        }
        if (ceil(bestbound - intTolerance) + flight >= initUB) return;
        elements.weight = remainingTime;
        for (int i = 1; i < depth; i++)
        {
            //elements.weight -= (0.001 * positionalWeight[tasks[i]] + 0.05 * directSucs[tasks[i]][0]);
        }
        elements.weight += bestbound * (double)timeCap;

        // Next verify memory-based rule:
        // (1) If there is a superset of the current partial solution in memory. If such a partial solution with a smaller flight exists, stop the exploration of current vertex
        // (2) If there is a dominating (according to Jackson's rule) partial solution in memory
        for (i = 1; i <= numTasks; i++)
        {
            if (elements.degrees[i] != 0) continue;
            if (taskTime[i] <= tFeasible)
            {
                // verify if there is a superset of the current partial solution in memory (generalized max load rule)
                el = elements;
                el.degrees[i]--;
                for (jj = 1; jj <= directSucs[i][0]; jj++)
                {
                    el.degrees[directSucs[i][jj]]--;
                }
                int ok = flight;
                for (ok = flight; ok >= 0; ok--)
                {
                    it = States[ok].find(el);
                    if (it != States[ok].end()) return;
                }

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
                            for (ok = flight; ok >= 0; ok--)
                            {
                                it = States[ok].find(el);
                                if (it != States[ok].end()) return;
                            }

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
                                if (configFeasible[k] && !configMatr[k][i])  // a novel trick to meet condition 4
                                {
                                    flag = false;
                                    break;
                                }
                            }
                            if (flag)
                            {
                                el.degrees[ii]++;
                                for (jj = 1; jj <= directSucs[ii][0]; jj++) el.degrees[directSucs[ii][jj]]++;
                                for (ok = flight; ok >= 0; ok--)
                                {
                                    it = States[ok].find(el);
                                    if (it != States[ok].end()) return;
                                }
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
                // cannot verify generalized max load rule, and directly verify (generalized) item dominance rule
                if (CkLabel == 1) 
                {
                    for (ii = 1; ii <= numTasks; ii++)
                    {
                        if ((potentiallyDominate[i][ii]) && (elements.degrees[ii] < 0) && (tFeasible + taskTime[ii] >= taskTime[i]))
                        {
                            el = elements;
                            el.degrees[i]--;
                            for (jj = 1; jj <= directSucs[i][0]; jj++) el.degrees[directSucs[i][jj]]--;
                            el.degrees[ii]++;
                            for (jj = 1; jj <= directSucs[ii][0]; jj++) el.degrees[directSucs[ii][jj]]++;
                            // we update values of el
                            for (int ok = flight; ok >= 0; ok--)
                            {
                                it = States[ok].find(el);
                                if (it != States[ok].end()) return;
                            }
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
                                if (configFeasible[k] && !configMatr[k][i])  // a novel trick to meet condition 4
                                {
                                    flag = false;
                                    break;
                                }
                            }
                            if (flag)
                            {
                                el = elements;
                                el.degrees[i]--;
                                for (jj = 1; jj <= directSucs[i][0]; jj++) el.degrees[directSucs[i][jj]]--;
                                el.degrees[ii]++;
                                for (jj = 1; jj <= directSucs[ii][0]; jj++) el.degrees[directSucs[ii][jj]]++;
                                for (int ok = flight; ok >= 0; ok--)
                                {
                                    it = States[ok].find(el);
                                    if (it != States[ok].end()) return;
                                }
                            }
                        }
                    }
                }
            }
        }

        // all rules passed
        int ok;
        for (ok = flight; ok < initUB; ok++)
        {
            it = States[ok].find(elements);
            if (it != States[ok].end())
            {
                if (ok > flight)
                {
                    States[ok].erase(it);
                    States[flight].insert(std::make_pair(elements, flight));
                    Heaps[flight].push(elements);
                }
                break;
            }
        }
        if (ok == initUB)
        {
            // we find a new element
            States[flight].insert(std::make_pair(elements, flight));
            Heaps[flight].push(elements);
        }
    }
}

void cyclicBestFirstSearch() 
{
    double startCBFS = clock();
    initializeCBFS();
    double end_cbfs = startCBFS + (initTimeLimit - LBTime - initTime) * CLKTCK;
    int cFlights, change = 1, numEligible, currentNonemtpyFDepth = 0;
    double current_time;
    while (change > 0)
    {
        change = 0;
        current_time = clock();
        if (current_time >= end_cbfs)
        {
            optimalCBFS = 0; // CBFS fails !
            freeCBFS();
            initTime += (clock() - startCBFS) / CLKTCK;
            return;
        }

        // CBFS
        for (cFlights = currentNonemtpyFDepth; cFlights < initUB; cFlights++)
        {
            flight = -1;
        searchForAnother_CBFS:
            if (!Heaps[cFlights].empty())
            {
                elements = Heaps[cFlights].top();
                Heaps[cFlights].pop();
                if (incumbentSol[0][0] == rootLB) goto searchForAnother_CBFS;
                int ok;
                for (ok = cFlights; ok >= 0; ok--)
                {
                    it = States[ok].find(elements);
                    if (it != States[ok].end()) break;
                }
                if (it->second < 0)
                {
                    if (cFlights + it->second < 0) it->second = -cFlights;
                    else goto searchForAnother_CBFS;
                }
                else if (it->second > 0)
                {
                    if (cFlights < it->second) it->second = -cFlights;
                    else if (cFlights > it->second) goto searchForAnother_CBFS;
                }
                // explore this node
                change++;
                flight = cFlights;
            }
            else if (cFlights == currentNonemtpyFDepth)         // update states, queue_record, and explored_solution
            {
                //cout << "Station\tHeap size\tStates size\n";
                //for (cFlights = 1; cFlights < initUB; cFlights++) cout << "(" << cFlights << ")\t" << Heaps[cFlights].size() << "\t\t" << States[cFlights].size() << endl;
                //boost::unordered_flat_map<DataCBFS, char, DataCBFSHash>().swap(States[currentNonemtpyFDepth]);
                currentNonemtpyFDepth++;
                if (initUB == currentNonemtpyFDepth) break;
                cFlights = currentNonemtpyFDepth;
                goto searchForAnother_CBFS;
            }

            if (flight >= 0)
            {
                numEligible = 0;
                flight++;
                tFeasible = flight * timeCap;
                for (int i = 1; i <= numTasks; i++)
                {
                    if (elements.degrees[i] == 0) eligible[++numEligible] = i;
                    else if (elements.degrees[i] < 0) tFeasible -= taskTime[i];
                }
                if (!taskSolitaryCBFS(numEligible))
                {
                    memset(configFeasible, true, 5);
                    numFullLoad = 0;
                    genLoadsCBFS(1, timeCap, 1, numEligible);
                }
            }
        }
    }
    // free memory
    freeCBFS();
    initTime += (clock() - startCBFS) / CLKTCK;
}