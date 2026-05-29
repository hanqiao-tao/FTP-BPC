// Lower bounds for the FTP. 
// 1. machine scheduling-based lower bound.
// 2. Dantzig-Wolfe decomposition-based lower bound.
// Please read the article "Tao et al. Flight test scheduling: A generic model, lower bounds, and iterated local search, EJOR, 2025." for more details
#include "FTP.h"

double p[NUMTASK];
bool apply[NUMTASK];
int order[NUMTASK];
double dataLB[NUMTASKSQUARE * kMax];
double headsLB[NUMTASKSQUARE * kMax];
double tailsLB[NUMTASKSQUARE * kMax];
static int machineLB;
static double flightFreeCap[NUMTASK];
static double price;
static double bestPrice;
static double* bestPrice_sol;
int price_sol[NUMTASK];
static double* pi;
static int remainingT;					    // remaining time for the current partial solution
static int listPricing[NUMTASK];		    // task list sorted by benefitPerUnit
static double benefitPerUnit[NUMTASK];    // pricing[i]/ job_time[i]
static bool configFeasible[5];

// machineLB
static void initMemoryLB4()
{
    machineLB = 0;
    memset(p, 0, sizeof(p));
    memset(apply, 0, sizeof(apply));
    memset(order, 0, sizeof(order));
    memset(dataLB, 0, sizeof(dataLB));
    memset(headsLB, 0, sizeof(headsLB));
    memset(tailsLB, 0, sizeof(tailsLB));
    double tmp = 1.0 / (double) timeCap;
    for (int i = 1; i <= numTasks; i++) p[i] = (double)(taskTime[i]) * tmp;  // timeCap
}

inline void Sort(int list[], double* pesos, int beg, int end, int posicionInicial)
{
    int tmp;
    int l, r;

    // Tail-recursive optimized quicksort implementation
    // Switch to insertion sort for small partitions (more efficient for small arrays)
    while (end - beg > 16)  
    {
        // Median-of-three pivot selection to avoid worst-case O(n^2) performance
        int mid = beg + ((end - beg) >> 1);

        // Find median of three values and place it in the middle
        if (pesos[posicionInicial + list[mid]] > pesos[posicionInicial + list[beg]]) {
            tmp = list[beg]; list[beg] = list[mid]; list[mid] = tmp;
        }
        if (pesos[posicionInicial + list[end]] > pesos[posicionInicial + list[beg]]) {
            tmp = list[beg]; list[beg] = list[end]; list[end] = tmp;
        }
        if (pesos[posicionInicial + list[end]] > pesos[posicionInicial + list[mid]]) {
            tmp = list[mid]; list[mid] = list[end]; list[end] = tmp;
        }

        // Place median at position end-1 to serve as pivot
        tmp = list[mid]; list[mid] = list[end - 1]; list[end - 1] = tmp;

        int piv = list[end - 1];
        double pivot_peso = pesos[posicionInicial + piv];

        l = beg;
        r = end - 1;

        // Partitioning phase: rearrange elements so that all elements
        // less than pivot come before it and all greater elements after it
        while (1)
        {
            // Pre-compute pivot weight to avoid repeated array access
            while (l < r && pivot_peso < pesos[posicionInicial + list[++l]]);
            while (l < r && pivot_peso > pesos[posicionInicial + list[--r]]);

            if (l >= r) break;

            tmp = list[l]; list[l] = list[r]; list[r] = tmp;
        }

        // Restore pivot to its final position
        tmp = list[l]; list[l] = list[end - 1]; list[end - 1] = tmp;

        // Tail recursion optimization: always process smaller partition first
        // This ensures recursion depth is limited to O(log n)
        if (l - beg < end - l)
        {
            Sort(list, pesos, beg, l - 1, posicionInicial);
            beg = l + 1;
        }
        else
        {
            Sort(list, pesos, l + 1, end, posicionInicial);
            end = l - 1;
        }
    }

    // Insertion sort for small partitions (more cache-friendly and efficient for small n)
    if (end > beg)
    {
        for (int i = beg + 1; i <= end; i++)
        {
            int key = list[i];
            double key_peso = pesos[posicionInicial + key];
            int j = i - 1;

            while (j >= beg && key_peso > pesos[posicionInicial + list[j]])
            {
                list[j + 1] = list[j];
                j--;
            }
            list[j + 1] = key;
        }
    }
}

static void computeDataLB4()
{
    int poisitionInit, poisitionInit2;
    double vCut0, vCutMax, f;
    // check if there exist two jobs with same duration to avoid extra computation
    for (int i = 0; i <= numTasks; i++)
    {
        apply[i] = 1;
    }
    for (int j = 2; j <= numTasks; j++)
    {
        for (int i = 1; (i < j) && (apply[j] == 1); i++)
        {
            if (taskTime[i] == taskTime[j])
            {
                apply[j] = 0;
            }
        }
    }
    // compute data with dual feasible function
    poisitionInit = 0;
    dataLB[poisitionInit] = 0.0;
    // trivial LB1
    for (int i = 1; i <= numTasks; i++)
    {
        dataLB[++poisitionInit] = p[i];
    }
    // DFF with parameter k = 0
    for (int epsPosition = 1, poisitionInit2Copy = NUMTASK; epsPosition <= numTasks; epsPosition++, poisitionInit2Copy += NUMTASK)
    {
        poisitionInit = 0;
        poisitionInit2 = poisitionInit2Copy;
        if (fabs(dataLB[poisitionInit + epsPosition] - 0.5) < intTolerance)
        {
            vCut0 = 0.5;
            vCutMax = 0.5;
        }
        else
        {
            if (dataLB[poisitionInit + epsPosition] < 0.5)
            {
                vCut0 = dataLB[poisitionInit + epsPosition];
                vCutMax = 1.0 - dataLB[poisitionInit + epsPosition];
            }
            else
            {
                vCut0 = 1.0 - dataLB[poisitionInit + epsPosition];
                vCutMax = dataLB[poisitionInit + epsPosition];
            }
        }
        for (int i = 1; i <= numTasks; i++)
        {
            poisitionInit++;
            poisitionInit2++;
            if (dataLB[poisitionInit] < (vCut0 - intTolerance))
            {
                dataLB[poisitionInit2] = 0.0;
            }
            else
            {
                if (dataLB[poisitionInit] > (vCutMax + intTolerance))
                {
                    dataLB[poisitionInit2] = 1.0;
                }
                else
                {
                    dataLB[poisitionInit2] = dataLB[poisitionInit];
                }
            }
        }
    }
    // DFF with parameter k = 1,2,...,kMax
    for (int k = 1, poisitionInitCopy = NUMTASKSQUARE; k < kMax; k++, poisitionInitCopy += NUMTASKSQUARE)
    {
        poisitionInit = poisitionInitCopy;
        dataLB[poisitionInit] = 0.0;
        for (int i = 1; i <= numTasks; i++)
        {
            f = p[i] * (double)(k + 1);
            if (fabs(f - round(f)) < intTolerance)
            {
                dataLB[++poisitionInit] = p[i];
            }
            else
            {
                dataLB[++poisitionInit] = floor(f + intTolerance) / (double)(k);
            }
        }
        for (int epsPosition = 1, poisitionInit2Copy = poisitionInitCopy + NUMTASK; epsPosition <= numTasks; epsPosition++, poisitionInit2Copy += NUMTASK)
        {
            poisitionInit = poisitionInitCopy;
            poisitionInit2 = poisitionInit2Copy;
            if (fabs(dataLB[poisitionInit + epsPosition] - 0.5) < intTolerance)
            {
                vCut0 = 0.5;
                vCutMax = 0.5;
            }
            else
            {
                if (dataLB[poisitionInit + epsPosition] < 0.5)
                {
                    vCut0 = dataLB[poisitionInit + epsPosition];
                    vCutMax = 1.0 - dataLB[poisitionInit + epsPosition];
                }
                else
                {
                    vCut0 = 1.0 - dataLB[poisitionInit + epsPosition];
                    vCutMax = dataLB[poisitionInit + epsPosition];
                }
            }
            for (int i = 1; i <= numTasks; i++)
            {
                poisitionInit++;
                poisitionInit2++;
                if (dataLB[poisitionInit] < (vCut0 - intTolerance))
                {
                    dataLB[poisitionInit2] = 0.0;
                }
                else
                {
                    if (dataLB[poisitionInit] > (vCutMax + intTolerance))
                    {
                        dataLB[poisitionInit2] = 1.0;
                    }
                    else
                    {
                        dataLB[poisitionInit2] = dataLB[poisitionInit];
                    }
                }
            }
        }
    }
}

static int computeHead(int task)
{
    int positionOrder;
    if (task == 0) // all tasks are predecessors
    {
        positionOrder = numTasks;
        for (int i = 1; i <= numTasks; i++)
        {
            order[i - 1] = numTasks + 1 - i;
        }
    }
    else //determine task's predecessors
    {
        positionOrder = 0;
        for (int i = 1; i <= numTasks; i++)
        {
            if (transMatr[i][task])
            {
                order[positionOrder] = i;
                positionOrder++;
            }
        }
    }
    int maxRound = 0;
    int poisitionInit;
    for (int kCount = 0, positionInitCopy = 0; kCount < kMax; kCount++, positionInitCopy += NUMTASKSQUARE)
    {
        for (int taskCount = 0; taskCount <= numTasks; taskCount++)
        {
            if (apply[taskCount] == 1)
            {
                poisitionInit = positionInitCopy + taskCount * NUMTASK;
                if (positionOrder > 1)
                {
                    Sort(order, headsLB, 0, positionOrder - 1, poisitionInit);
                }
                double ac = 0.0;
                for (int i = 0; i < positionOrder; i++)
                {
                    ac += dataLB[poisitionInit + order[i]];
                    double tmp = ac + headsLB[poisitionInit + order[i]];
                    if (headsLB[poisitionInit + task] < tmp)
                    {
                        headsLB[poisitionInit + task] = tmp;
                    }
                }
                headsLB[poisitionInit + task] = ceil(headsLB[poisitionInit + task] - intTolerance);
                // maxRound always save the maximum headsLB[.] among all tasks
                if (headsLB[poisitionInit + task] > maxRound)
                {
                    maxRound = (int)headsLB[poisitionInit + task];
                }
            }
        }
    }
    poisitionInit = task;
    for (int kCount = 0, positionInitCopy = task; kCount < kMax; kCount++, positionInitCopy += NUMTASKSQUARE)
    {
        poisitionInit = positionInitCopy;
        for (int eps_pos = 0; eps_pos <= numTasks; eps_pos++)
        {
            if ((headsLB[poisitionInit] < maxRound) && (dataLB[poisitionInit] > intTolerance))
            {
                headsLB[poisitionInit] = maxRound;
            }
            poisitionInit += NUMTASK;
        }
    }
    return (0);
}

static int computeTail(int task)
{
    int positionOrder;
    if (task == 0) // all tasks are successors
    {
        positionOrder = numTasks;
        for (int i = 1; i <= numTasks; i++)
        {
            order[i - 1] = i;
        }
    }
    else //determine task's successors
    {
        positionOrder = 0;
        for (int i = 1; i <= numTasks; i++)
        {
            if (transMatr[task][i])
            {
                order[positionOrder] = i;
                positionOrder++;
            }
        }
    }
    int maxRound = 0;
    int positionInit;
    for (int kCount = 0, positionInitCopy = 0; kCount < kMax; kCount++, positionInitCopy += NUMTASKSQUARE)
    {
        for (int taskCount = 0; taskCount <= numTasks; taskCount++)
        {
            if (apply[taskCount] == 1)
            {
                positionInit = positionInitCopy + taskCount * NUMTASK;
                if (positionOrder > 1)
                {
                    Sort(order, tailsLB, 0, positionOrder - 1, positionInit);
                }
                double ac = 0.0;
                for (int i = 0; i < positionOrder; i++)
                {
                    ac += dataLB[positionInit + order[i]];
                    double tmp = ac + tailsLB[positionInit + order[i]];
                    if (tailsLB[positionInit + task] < tmp)
                    {
                        tailsLB[positionInit + task] = tmp;
                    }
                }
                tailsLB[positionInit + task] = ceil(tailsLB[positionInit + task] - intTolerance);
                // maxRound always save the maximum headsLB[.] among all tasks
                if (tailsLB[positionInit + task] > maxRound)
                {
                    maxRound = (int)tailsLB[positionInit + task];
                }
            }
        }
    }
    positionInit = task;
    for (int kCount = 0, positionInitCopy = task; kCount < kMax; kCount++, positionInitCopy += NUMTASKSQUARE)
    {
        positionInit = positionInitCopy;
        for (int eps_pos = 0; eps_pos <= numTasks; eps_pos++)
        {
            if ((tailsLB[positionInit] < maxRound) && (dataLB[positionInit] > intTolerance))
            {
                tailsLB[positionInit] = maxRound;
            }
            positionInit += NUMTASK;
        }
    }
    return (0);
}

static void determineHeadsOrTails()
{
    int pendings[NUMTASK];
    int executionOrder[NUMTASK];

    //tails
    for (int i = 1; i <= numTasks; i++)
    {
        executionOrder[i] = numTasks + 1 - i;
    }
    for (int i = 1; i <= numTasks; i++)
    {
        pendings[i] = 0;
        for (int j = i + 1; j <= numTasks; j++)
        {
            if (transMatr[i][j])
            {
                pendings[i]++;
            }
        }
    }
    int Delta = 1;
    while (Delta != 0)
    {
        Delta = 0;
        for (int i = 1; i < numTasks; i++)
        {
            if (pendings[executionOrder[i]] > pendings[executionOrder[i + 1]])
            {
                Delta = executionOrder[i];
                executionOrder[i] = executionOrder[i + 1];
                executionOrder[i + 1] = Delta;
            }
        }
    }
    for (int i = 1; i <= numTasks; i++)
    {
        computeTail(executionOrder[i]);
    }
    computeTail(0);

    //heads
    for (int i = 1; i <= numTasks; i++)
    {
        executionOrder[i] = i;
    }
    for (int i = 1; i <= numTasks; i++)
    {
        pendings[i] = 0;
        for (int j = 1; j < i; j++)
        {
            if (transMatr[j][i])
            {
                pendings[i]++;
            }
        }
    }
    Delta = 1;
    while (Delta != 0)
    {
        Delta = 0;
        for (int i = 1; i < numTasks; i++)
        {
            if (pendings[executionOrder[i]] > pendings[executionOrder[i + 1]])
            {
                Delta = executionOrder[i];
                executionOrder[i] = executionOrder[i + 1];
                executionOrder[i + 1] = Delta;
            }
        }
    }
    for (int i = 1; i <= numTasks; i++)
    {
        computeHead(executionOrder[i]);
    }
    computeHead(0);
}

static bool flow(int positionInit, int LBTry)
{
    double remaining;
    int task;
    if (LBTry > numTasks)
    {
        return true;
    }
    for (int i = 1; i <= LBTry; i++)
    {
        flightFreeCap[i] = 1.0;
    }
    for (int i = 1; i <= numTasks; i++)
    {
        task = order[i];
        remaining = dataLB[positionInit + task];
        for (int j = E[task]; (j <= L[task]) && (remaining > intTolerance); j++)
        {
            if (remaining < flightFreeCap[j])
            {
                flightFreeCap[j] -= remaining;
                remaining = 0.0;
                break;
            }
            else
            {
                remaining -= flightFreeCap[j];
                flightFreeCap[j] = 0.0;
            }
        }
        if (remaining > intTolerance)
        {
            return false;
        }
    }
    return true;
}

static int determineFlow(int LB)
{
    int LBTry = LB;
    for (int i = 1; i <= numTasks; i++)
    {
        order[i] = i;
    }
    for (int i = 1; i <= numTasks; i++)
    {
        E[i] = 1 + (int)(headsLB[i]);
    }
repetir:
    for (int i = 1; i <= numTasks; i++)
    {
        L[i] = LBTry - (int)(tailsLB[i]);
    }
    int Delta = 1;
    while (Delta > 0)
    {
        Delta = 0;
        for (int i = 1; i < numTasks; i++)
        {
            if (L[order[i]] > L[order[i + 1]])
            {
                Delta = order[i];
                order[i] = order[i + 1];
                order[i + 1] = Delta;
            }
            else
            {
                if ((L[order[i]] == L[order[i + 1]]) && (E[order[i]] > E[order[i + 1]]))
                {
                    Delta = order[i];
                    order[i] = order[i + 1];
                    order[i + 1] = Delta;
                }
            }
        }
    }
    int position_initial = 0;
    for (int k_count = 0, position_initial_copy = 0; k_count < kMax; k_count++, position_initial_copy += NUMTASKSQUARE)
    {
        position_initial = position_initial_copy;
        for (int task_count = 0; task_count <= numTasks; task_count++, position_initial += NUMTASK)
        {
            //int position_initial = k_value * NUMTASKSQUARE + task_value * NUMTASK;
            if (flow(position_initial, LBTry) == false)
            {
                LBTry++;
                goto repetir;
            }
        }
    }
    return LBTry;
}

void computeMachineLB() // LB4
{
    clock_t start = clock();
    initMemoryLB4();
    computeDataLB4();
    determineHeadsOrTails();
    int LB_0 = (int)(tailsLB[0]);
    if (LB_0 < (int)(headsLB[0])) LB_0 = (int)(headsLB[0]);

    machineLB = determineFlow(LB_0);
    rootLB = machineLB;
    LBTime += double(clock() - start) / CLKTCK;
}

static inline double DWBoundPricing(int rest_time, int position) 
{
    int i, ii, k, task, flag;
    double ac = 0.0;
    for (i = position; i <= numTasks && pi[listPricing[i]] > intTolerance; i++)
    {
        task = listPricing[i];
        flag = 0;
        for (ii = 1; ii <= price_sol[0]; ii++)
        {
            if (task < price_sol[ii])
            {
                if (transMatr[task][price_sol[ii]])
                {
                    flag++;
                    break;
                }
            }
            else
            {
                if (transMatr[price_sol[ii]][task])
                {
                    flag++;
                    break;
                }
            }
        }
        if (flag > 0) continue;
        for (k = 1; k <= numConfig; k++)
        {
            if (configMatrTranspose[task][k] && configFeasible[k])
            {
                flag++; 
                break;
            }
        }
        if (flag == 0) continue;
        if (rest_time > taskTime[task])
        {
            rest_time -= taskTime[task];
            ac += pi[task];
        }
        else
        {
            ac += pi[task] * (double)(rest_time) * taskTimeInv[task];
            return ac;
        }
    }
    return ac;
}

static void DWKnapsackBranch(int position) 
{
    int task = listPricing[position];
    int i, k, config_set_val;
    // time capacity
    if (taskTime[task] > remainingT) return;
    // precedence
    for (i = 1; i <= price_sol[0]; i++)
    {
        if (transMatr[task][price_sol[i]]) return;
        if (transMatr[price_sol[i]][task]) return;
    }
    // configuration
    config_set_val = 0;
    for (k = 1; k <= numConfig; k++)
    {
        if (configMatrTranspose[task][k] && configFeasible[k]) config_set_val++;
    }
    if (config_set_val == 0) return;

    // earliest & latest
    int eMin = E[task];
    int lMax = L[task];
    for (i = 1; i <= price_sol[0]; i++) if (eMin < E[price_sol[i]]) eMin = E[price_sol[i]];
    for (i = 1; i <= price_sol[0]; i++) if (lMax > L[price_sol[i]]) lMax = L[price_sol[i]];
    if (eMin > lMax) return;

    // pricing bounds
    if (price + pi[task] + DWBoundPricing(remainingT - taskTime[task], position + 1) < bestPrice) return;
    
    // all condition satisfied, assign
    price_sol[0]++;
    price_sol[price_sol[0]] = task;
    remainingT -= taskTime[task];
    price += pi[task];
    bool configFeasible_old[5];
    memcpy(configFeasible_old, configFeasible, 5);
    for (k = 1; k <= numConfig; k++) configFeasible[k] &= configMatrTranspose[task][k];
    if (price > bestPrice)
    {
        // update best solution
        memset(bestPrice_sol, 0, sizeof(double) * (numTasks + 1));
        for (int i = 1; i <= price_sol[0]; i++) bestPrice_sol[price_sol[i]] = 1;
        bestPrice = price;
    }

    // branch
    for (i = position + 1; i <= numTasks; i++)
    {
        if (pi[listPricing[i]] > intTolerance)
        {
            DWKnapsackBranch(i);
        }
    }

    // disassign
    price -= pi[task];
    remainingT += taskTime[task];
    memcpy(configFeasible, configFeasible_old, 5);
    price_sol[price_sol[0]] = 0;
    price_sol[0]--;
}

static inline void DWPricing() 
{
    int i;
    int change = 1;
    price = 0.0;
    bestPrice = 0.0;
    for (i = 1; i <= numTasks; i++)
    {
        benefitPerUnit[i] = pi[i] * taskTimeInv[i];  // may be using * (taskTime[i]^{-1}) is faster
        listPricing[i] = i;
    }
    // sort benefitPerUnit descendently (bubble sort)
    while (change >= 0)
    {
        change = -1;
        for (int i = 1; i < numTasks; i++)
        {
            if (benefitPerUnit[listPricing[i]] < benefitPerUnit[listPricing[i + 1]])
            {
                change = listPricing[i];
                listPricing[i] = listPricing[i + 1];
                listPricing[i + 1] = change;
            }
        }
    }
    // initialize
    memset(price_sol, 0, sizeof(price_sol));
    memset(configFeasible, 1, 5);
    remainingT = timeCap;
    for (i = 1; i <= numTasks; i++)
    {
        if (pi[listPricing[i]] > intTolerance) DWKnapsackBranch(i);
    }
}

void computeDWLB()
{
    clock_t start = clock();
    int initUB = incumbentSol[0][0];
    try
    {
        EnvrConfig config;
        config.Set("nobanner", "1");
        Envr ENV(config);
        Model master_model = ENV.CreateModel("Master_Model");
        VarArray z_q;
        ConstrArray z_to_lamb;
        Expr cons;
        // position holder
        z_to_lamb.PushBack(master_model.AddConstr(cons >= 0));
        cons -= 1;
        for (int i = 1; i <= numTasks; i++) z_to_lamb.PushBack(master_model.AddConstr(cons == 0));
        // add initial columns
        double* new_col = new double[numTasks + 1];
        new_col[0] = 0;
        for (int j = 1; j <= initUB; j++)
        {
            Column col;
            for (int i = 1; i <= numTasks; i++) 
            {
                if (incumbentSol[0][i] == j) new_col[i] = 1;
                else new_col[i] = 0;
            }
            col.AddTerms(z_to_lamb, new_col, numTasks + 1);
            z_q.PushBack(master_model.AddVar(0, 1, 1, 'C', col));
        }
        delete[] new_col;
        master_model.SetObjSense(1);

        // Solve
        master_model.SetIntParam(COPT_INTPARAM_LOGGING, 0);
        master_model.SetIntParam(COPT_INTPARAM_THREADS, 1);
        master_model.SetIntParam(COPT_INTPARAM_LPMETHOD, 1);
        master_model.Solve();

        // Column generation
        bool new_col_gen = true;
        pi = new double[numTasks + 1];
        bestPrice_sol = new double[numTasks + 1];
        bestPrice_sol[0] = 0;
        while (new_col_gen) 
        {
            new_col_gen = false;
            master_model.Get(COPT_DBLINFO_DUAL, z_to_lamb, pi);
            //solve the pricing problem
            DWPricing();
            //cout << bestPrice << endl;
            if (bestPrice > 1 + intTolerance) 
            {
                new_col_gen = true;
                // add new columns
                Column col;
                col.AddTerms(z_to_lamb, bestPrice_sol, numTasks + 1);
                z_q.PushBack(master_model.AddVar(0, 1, 1, 'C', col));
                master_model.Solve();
            }
        }
        int LB_DW = (int)(ceil(master_model.GetDblAttr("LpObjval") - intTolerance));
        rootLB = LB_DW > rootLB ? LB_DW : rootLB;
        delete[] pi;
        delete[] bestPrice_sol;
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
}