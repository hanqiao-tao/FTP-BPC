// The branch-and-bound algorithm for solving pricing problems
#include "FTP.h"

double bestPrice;				            // best value for the pricing problem
int bestSol[NUMTASK + 14];				    // best solution for the pricing problem

static double price;					    // value for the pricing problem
static int sol[NUMTASK + 14];				// solution for the pricing problem
static int change;                          // for bubble sort
static int remainingT;					    // remaining time for the current partial solution
static int iTask, jTask, kTask;
static int numPositive;
static double pricingBound;
static int listPricing[NUMTASK];		    // task list sorted by benefitPerUnit
static double benefitPerUnit[NUMTASK];    // pricing[i]/ job_time[i]
static int* ptrSol = NULL;
static double* ptrDual = NULL;
static bool* ptrBool = NULL;
static bool configFeasible[5] = { true };
static CutValue2 pricingCutVal2;
static CutValue3 pricingCutVal3;
static boost::unordered_flat_map<CutValue2, std::pair<int, int>, DataHashCut2>::iterator it2;
static boost::unordered_flat_map<CutValue3, std::pair<int, int>, DataHashCut3>::iterator it3;

static inline void compare3(int task)
{
    // a complete branching to achieve sort task, iTask, jTask increasingly.
    if (task < iTask)
    {
        if (jTask > iTask)
        {
            pricingCutVal3.taskSet[0] = task;
            pricingCutVal3.taskSet[1] = iTask;
            pricingCutVal3.taskSet[2] = jTask;
        }
        else
        {
            if (jTask > task)
            {
                pricingCutVal3.taskSet[0] = task;
                pricingCutVal3.taskSet[1] = jTask;
                pricingCutVal3.taskSet[2] = iTask;
            }
            else
            {
                pricingCutVal3.taskSet[0] = jTask;
                pricingCutVal3.taskSet[1] = task;
                pricingCutVal3.taskSet[2] = iTask;
            }
        }
    }
    else
    {
        if (jTask > task)
        {
            pricingCutVal3.taskSet[0] = iTask;
            pricingCutVal3.taskSet[1] = task;
            pricingCutVal3.taskSet[2] = jTask;
        }
        else
        {
            if (jTask > iTask)
            {
                pricingCutVal3.taskSet[0] = iTask;
                pricingCutVal3.taskSet[1] = jTask;
                pricingCutVal3.taskSet[2] = task;
            }
            else
            {
                pricingCutVal3.taskSet[0] = jTask;
                pricingCutVal3.taskSet[1] = iTask;
                pricingCutVal3.taskSet[2] = task;
            }
        }
    }
}

// a simple upper bound based on the KP (Dantizig's rule)
static inline double bound(int restTime, int position)
{
    int i, ii, task, k;
    double ac = 0.0;
    int flag;
    for (i = position; i <= numPositive; i++)
    {
        task = listPricing[i];
        flag = 0;
        for (ii = 1; ii <= sol[0]; ii++)
        {
            if (task < sol[ii])
            {
                if (transMatr[task][sol[ii]])
                {
                    flag++;
                    break;
                }
            }
            else
            {
                if (transMatr[sol[ii]][task]) 
                {
                    flag++;
                    break;
                }
            }
        }
        if (flag > 0) continue;
        ptrBool = configMatrTranspose[task];
        for (k = 1; k <= numConfig; k++)
        {
            if (ptrBool[k] && configFeasible[k]) flag++;
        }
        if (flag == 0) continue;

        if (restTime >= taskTime[task])
        {
            restTime -= taskTime[task];
            ac += dualCol[task];
        }
        else
        {
            ac += dualCol[task] * (double)(restTime) * taskTimeInv[task];
            return ac;
        }
    }
    return ac;
}

// for solving pricing problem in BPC
static void knapsackBranchPricing(int position, int flightId)
{
    int task = listPricing[position];
    int i, j, k, config_notin, config_set_val, tmp;
    bool flag;
    // time capacity
    if (taskTime[task] > remainingT) return;
    // precedence
    for (i = 1; i <= sol[0]; i++)
    {
        if (task < sol[i]) 
        {
            if (transMatr[task][sol[i]]) return;
        }
        else 
        {
            if (transMatr[sol[i]][task]) return;
        }
    }
    // pricing bounds
    pricingBound = price + dualCol[task] + bound(remainingT - taskTime[task], position + 1);
    if (pricingBound <= bestPrice || pricingBound < intTolerance) return;
    // configuration 
    config_set_val = 0;
    ptrBool = configMatrTranspose[task];
    for (k = 1; k <= numConfig; k++)
    {
        if (ptrBool[k] && configFeasible[k]) config_set_val++;
    }
    if (config_set_val == 0) return;
    //robust cut
    for (i = 1; i <= sol[0]; i++)
    {
        iTask = sol[i];
        if (iTask > task)
        {
            pricingCutVal2.taskSet[0] = task;
            pricingCutVal2.taskSet[1] = iTask;
        }
        else
        {
            pricingCutVal2.taskSet[0] = iTask;
            pricingCutVal2.taskSet[1] = task;
        }
        it2 = cutMap2.find(pricingCutVal2);
        if (it2 != cutMap2.end())
        {
            if (it2->second.second > flightId) return;
            tmp = it2->second.first;
            if (tmp > 0 && flightId + tmp > initUB + 1) return;
        }
    }

    for (i = 1; i <= sol[0]; i++)
    {
        iTask = sol[i];
        for (j = i + 1; j <= sol[0]; j++)
        {
            jTask = sol[j];
            compare3(task);
            it3 = cutMap3.find(pricingCutVal3);
            if (it3 != cutMap3.end())
            {
                if (it3->second.second > flightId) return;
                tmp = it3->second.first;
                if (tmp > 0 && flightId + it3->second.first > initUB + 1) return;
            }
        }
    }
    // all condition satisfied, assign
    double old_price = price;
    remainingT -= taskTime[task];
    price += dualCol[task];
    sol[0]++;
    sol[sol[0]] = task;
    bool configFeasible_old[5] = { true };
    memcpy(configFeasible_old, configFeasible, sizeof(configFeasible_old));
    for (k = 1; k <= numConfig; k++) configFeasible[k] &= ptrBool[k];
    int old_copy[14] = { 0 };
    memcpy(old_copy, &sol[NUMTASK], 14 * sizeof(int));
    ptrSol = &sol[NUMTASK];
    ptrDual = &dualCol[NUMTASK];
    for (j = 1; j <= configurationSubsetNumber; j++, ptrSol++, ptrDual++)
    {
        if (*ptrSol == 0)
        {
            config_set_val = 1;
            for (k = 1; k <= configurationSubsetC[j][0]; k++)
            {
                flag = false;
                config_notin = configurationSubsetC[j][k];
                for (i = 1; i <= sol[0]; i++)
                {
                    if (!configMatr[config_notin][sol[i]])
                    {
                        flag = true;
                        break;
                    }
                }
                if (!flag)
                {
                    config_set_val = 0;
                    break;
                }
            }
            *ptrSol = config_set_val;
            if (config_set_val == 1) price += *ptrDual;
        }
    }
    if (price > bestPrice + intTolerance)
    {
        // update best solution
        memcpy(bestSol, sol, sizeof(sol));
        bestPrice = price;
    }
    // branch
    for (i = position + 1; i <= numPositive; i++)
    {
        if (E[listPricing[i]] <= flightId && flightId <= L[listPricing[i]]) knapsackBranchPricing(i, flightId);
    }

    // disassign
    sol[sol[0]] = 0;
    sol[0]--;
    price = old_price;
    remainingT += taskTime[task];
    memcpy(configFeasible, configFeasible_old, sizeof(configFeasible_old));
    memcpy(&sol[NUMTASK], old_copy, 14 * sizeof(int));
    return;
}

void bbPricing(int flightId)
{
    // initialize
    clock_t start = clock();
    int i, j, k, ii, tmp, task, configSetVal;
    bool flag;
    change = 1;
    price = dualCol[0];
    bestPrice = dualCol[0];
    memset(bestSol, 0, sizeof(bestSol));
    memset(sol, 0, sizeof(sol));
    memset(configFeasible, true, sizeof(configFeasible));
    remainingT = timeCap;
    int id1 = 1, id2 = numTasks;
    for (i = 1; i <= numTasks; i++)
    {
        if (dualCol[i] > intTolerance)
        {
            benefitPerUnit[i] = dualCol[i] * taskTimeInv[i];
            listPricing[id1] = i;
            id1++;
        }
        else
        {
            benefitPerUnit[i] = -1;
            listPricing[id2] = i;
            id2--;
        }
    }
    numPositive = id1 - 1;
    // sort benefitPerUnit descendently
    Sort(listPricing, benefitPerUnit, 1, numPositive, 0);
    
    // to speed up the branch-and-bound procedure, we first obtain an solution by a greedy heuristic
    for (ii = 1; ii <= numPositive; ii++)
    {
        task = listPricing[ii];
        flag = true;
        // capacity
        if (remainingT < taskTime[task]) flag = false;
        // precedence
        if (flag)
        {
            for (i = 1; i <= bestSol[0]; i++)
            {
                if (transMatr[task][bestSol[i]] || transMatr[bestSol[i]][task])
                {
                    flag = false;
                    break;
                }
            }
        }
        //configuration && robust cut
        if (flag && numConfig > 1) 
        {
            configSetVal = 0;
            ptrBool = configMatrTranspose[task];
            for (k = 1; k <= numConfig; k++)
            {
                if (ptrBool[k] && configFeasible[k]) configSetVal++;
            }
            if (configSetVal == 0) flag = false;
        }
        for (i = 1; i <= bestSol[0] && flag; i++)
        {
            iTask = bestSol[i];
            if (task < iTask)
            {
                pricingCutVal2.taskSet[0] = task;
                pricingCutVal2.taskSet[0] = iTask;
            }
            else 
            {
                pricingCutVal2.taskSet[0] = iTask;
                pricingCutVal2.taskSet[0] = task;
            }
            it2 = cutMap2.find(pricingCutVal2);
            if (it2 != cutMap2.end())
            {
                if (it2->second.second > flightId) flag = false;
                else
                {
                    tmp = it2->second.first;
                    if (flag && tmp > 0) if (flightId + tmp > initUB + 1) flag = false;
                }
            }
            
        }
        for (i = 1; i <= bestSol[0] && flag; i++)
        {
            iTask = bestSol[i];
            for (j = i + 1; j <= bestSol[0] && flag; j++)
            {
                jTask = bestSol[j];
                compare3(task);
                it3 = cutMap3.find(pricingCutVal3);
                if (it3 != cutMap3.end())
                {
                    if (it3->second.second > flightId) flag = false;
                    else
                    {
                        tmp = it3->second.first;
                        if (tmp > 0) if (flightId + tmp > initUB + 1) flag = false;
                    }
                }
            }
        }
        
        if (flag)
        {
            remainingT -= taskTime[task];
            bestSol[0]++;
            bestSol[bestSol[0]] = task;
            bestPrice += dualCol[task];
            if (numConfig > 1)
            {
                for (k = 1; k <= numConfig; k++) configFeasible[k] &= ptrBool[k];
            }
        }
    }
    int config_notin;
    for (j = 1; j <= configurationSubsetNumber; j++) 
    {
        configSetVal = 1;
        for (k = 1; k <= configurationSubsetC[j][0]; k++) 
        {
            flag = false;
            config_notin = configurationSubsetC[j][k];
            for (i = 1; i <= bestSol[0]; i++) 
            {
                if (!configMatr[config_notin][bestSol[i]]) 
                {
                    flag = true;
                    break;
                }
            }
            if (!flag) 
            {
                configSetVal = 0;
                break;
            }
        }
        bestSol[NUMTASK - 1 + j] = configSetVal;
        if (configSetVal == 1) bestPrice += dualCol[NUMTASK - 1 + j];
    }
    
    // reset
    remainingT = timeCap;
    memset(configFeasible, true, sizeof(configFeasible));
    if (bestPrice < intTolerance) 
    {
        bestPrice = 0.0;
        memset(bestSol, 0, sizeof(bestSol));
    }
    if (bestSol[0] == numPositive)
    {
        pricingTime += double((clock() - start));
        return;
    }
    // branch-and-bound
    for (j = 1; j <= numPositive; j++)
    {
        if (E[listPricing[j]] <= flightId && flightId <= L[listPricing[j]])
        {
            knapsackBranchPricing(j, flightId);
        }
    }
    pricingTime += double((clock() - start));
    return;
}
