// The iterated local search heuristic for further improving the quality of the solution.
// Please read the article "Tao et al. Flight test scheduling: A generic model, lower bounds, and iterated local search, EJOR, 2025." for more details

#include "FTP.h"

static int solutionVND[2][NUMTASK];
static bool* ptrBool1 = NULL;
static bool* ptrBool2 = NULL;
static int* ptrInt1 = NULL;
static int* ptrInt2 = NULL;
static int* ptrInt3 = NULL;
static int* ptrInt4 = NULL;
static int flightCap[NUMTASK];
static int emptyFlight[NUMTASK];
static int testScheduling[NUMTASK][NUMTASK];
static int workload[5];

static void backwardVND()
{
    bool improve = true;
    memset(flightCap, 0, sizeof(flightCap));
    for (int j = 1; j <= numTasks; j++)
    {
        flightCap[solutionVND[0][j]] += taskTime[j];
    }
    int loop = 1;
    int count = 1;
    while (improve)
    {
        improve = false;
        // Relocate 
        if (!improve)
        {
            ptrInt1 = directSucs[numTasks];
            ptrInt2 = directPreds[numTasks];
            for (int j = numTasks; j >= 1; j--, ptrInt1 -= NUMTASK, ptrInt2 -= NUMTASK)
            {
                for (int flight2 = solutionVND[0][0]; flight2 >= 1; flight2--)
                {
                    int flight1 = solutionVND[0][j];
                    if (flight1 == flight2) continue;
                    int a = flightCap[flight1];
                    int b = flightCap[flight2];
                    int b_plus = b + taskTime[j];
                    if ((timeCap < b_plus) || (b_plus <= a)) continue;     
                    // capacity constraints satisfy
                    bool flag = configMatr[solutionVND[1][flight2]][j];
                    if (!flag) continue;
                    // check precedence constraints
                    if (flight1 < flight2)
                    {
                        for (int lId = 1; lId <= ptrInt1[0] && flag; lId++)
                        {
                            if (solutionVND[0][ptrInt1[lId]] < flight2 + 1)
                            {
                                flag = false;
                                break;
                            }
                        }
                    }
                    else
                    {
                        for (int lId = 1; lId <= ptrInt2[0] && flag; lId++)
                        {
                            if (flight2 < solutionVND[0][ptrInt2[lId]] + 1) 
                            {
                                flag = false;
                                break;
                            }
                        }
                    }
                    if (!flag) continue;                                                        
                    // all constraints satisfied
                    solutionVND[0][j] = flight2;
                    flightCap[flight2] = b_plus;
                    flightCap[flight1] -= taskTime[j];
                    improve = true;
                }
            }
        }

        // Swap(1, 1) neighborhood: accept worse solution
        if (!improve)
        {
            ptrInt1 = directSucs[numTasks];
            ptrInt2 = directPreds[numTasks];
            for (int task1 = numTasks; task1 >= 1; task1--, ptrInt1 -= NUMTASK, ptrInt2 -= NUMTASK)
            {
                ptrInt3 = ptrInt1 - NUMTASK;
                ptrInt4 = ptrInt2 - NUMTASK;
                for (int task2 = task1 - 1; task2 >= 1; task2--, ptrInt3 -= NUMTASK, ptrInt4 -= NUMTASK)
                {
                    int flight1 = solutionVND[0][task1];
                    int flight2 = solutionVND[0][task2];
                    if (flight1 != flight2)
                    {
                        int a = flightCap[flight1];
                        int b = flightCap[flight2];
                        int delta = taskTime[task1] - taskTime[task2];
                        if ((timeCap + delta < a) || (timeCap < b + delta)) continue;
                        // accept and respect capacity constraints
                        bool flag = configMatr[solutionVND[1][flight2]][task1] && configMatr[solutionVND[1][flight1]][task2];
                        if (!flag) continue;
                        // check precedence constraints
                        if (flight1 < flight2)
                        {
                            //check task1's successors
                            for (int lId = 1; (lId <= ptrInt1[0]) && (flag); lId++)
                            {
                                if (solutionVND[0][ptrInt1[lId]] < flight2 + 1) flag = false;
                            }
                            //check task2's precedessors
                            for (int lId = 1; (lId <= ptrInt4[0]) && (flag); lId++)
                            {
                                if (flight1 < solutionVND[0][ptrInt4[lId]] + 1) flag = false;
                            }
                        }
                        else
                        {
                            //check task2's successors
                            for (int lId = 1; (lId <= ptrInt3[0]) && (flag); lId++)
                            {
                                if (solutionVND[0][ptrInt3[lId]] < flight1 + 1) flag = false;
                            }
                            //check task1's precedessors
                            for (int lId = 1; (lId <= ptrInt2[0]) && (flag); lId++)
                            {
                                if (flight2 < solutionVND[0][ptrInt2[lId]] + 1) flag = false;
                            }
                        }
                        if (!flag) continue;
                        // all constraints satisfied
                        solutionVND[0][task1] = flight2;
                        solutionVND[0][task2] = flight1;
                        flightCap[flight1] -= delta;
                        flightCap[flight2] += delta;
                        improve = true;
                    }
                }
            }

        }

        // Clear empty
        emptyFlight[0] = 1;
        for (int i = 1; i <= solutionVND[0][0]; i++)
        {
            if (flightCap[i] == 0)
            {
                emptyFlight[emptyFlight[0]] = i;
                emptyFlight[0]++;
            }
        }
        emptyFlight[0]--;
        count++;
        if (emptyFlight[0] > 0)
        {
            // for test
            int tmp = solutionVND[0][0];
            solutionVND[0][0] -= emptyFlight[0];
            for (int j = 1; j <= numTasks; j++)
            {
                for (int id = 1; id <= emptyFlight[0]; id++)
                {
                    if (id < emptyFlight[0] && emptyFlight[id] <= solutionVND[0][j] && emptyFlight[id + 1] > solutionVND[0][j])
                    {
                        solutionVND[0][j] -= id;
                    }
                    if (id == emptyFlight[0] && emptyFlight[id] <= solutionVND[0][j])
                    {
                        solutionVND[0][j] -= id;
                    }
                }
            }
            count = 0;
            memset(flightCap, 0, sizeof(flightCap));
            for (int j = 1; j <= numTasks; j++)
            {
                flightCap[solutionVND[0][j]] += taskTime[j];
            }
            // for configuration
            for (int emp = 1; emp <= emptyFlight[0]; emp++) 
            {
                for (int i = emptyFlight[emp] - emp + 1; i < tmp; i++) solutionVND[1][i] = solutionVND[1][i + 1];
                solutionVND[1][tmp] = 0;
                tmp--;
                //solutionVND[1].erase(solutionVND[1].begin() + emptyFlight[emp] - emp + 1);
            }
        }
        if (loop > 9999 || count > 1000) break;
        loop++;
    }
}

static void forwardVND()
{
    bool improve = true; 
    memset(flightCap, 0, sizeof(flightCap));
    for (int j = 1; j <= numTasks; j++)
    {
        flightCap[solutionVND[0][j]] += taskTime[j];
    }
    int loop = 1;
    int count = 1;
    while (improve)
    {
        // Relocate 
        improve = false;
        if (!improve)
        {
            ptrInt1 = directSucs[1];
            ptrInt2 = directPreds[1];
            for (int j = 1; j <= numTasks; j++, ptrInt1 += NUMTASK, ptrInt2 += NUMTASK)
            {
                for (int flight2 = 1; flight2 <= solutionVND[0][0]; flight2++)
                {
                    int flight1 = solutionVND[0][j];
                    if (flight1 == flight2) continue;
                    int a = flightCap[flight1];
                    int b = flightCap[flight2];
                    int b_plus = b + taskTime[j];
                    if (timeCap < b_plus || b_plus <= a) continue;
                    // capacity constraints satisfy
                    bool flag = configMatr[solutionVND[1][flight2]][j];          
                    if (!flag) continue;
                    // check precedence constraints
                    if (flight1 < flight2)
                    {
                        for (int lId = 1; lId <= ptrInt1[0] && flag; lId++)
                        {
                            if (solutionVND[0][ptrInt1[lId]] < flight2 + 1) flag = false;
                        }
                    }
                    else
                    {
                        for (int lId = 1; lId <= ptrInt2[0] && flag; lId++)
                        {
                            if (flight2 < solutionVND[0][ptrInt2[lId]] + 1) flag = false;
                        }
                    }
                    if (!flag) continue;
                    // all constraints satisfied
                    solutionVND[0][j] = flight2;
                    flightCap[flight2] = b_plus;
                    flightCap[flight1] -= taskTime[j];
                    improve = true;
                }
            }
        }
        // Swap(1, 1) neighborhood: accept worse solution
        if (!improve)
        {
            ptrInt1 = directSucs[1];
            ptrInt2 = directPreds[1];
            for (int task1 = 1; task1 <= numTasks; task1++, ptrInt1 += NUMTASK, ptrInt2 += NUMTASK)
            {
                ptrInt3 = ptrInt1 + NUMTASK;
                ptrInt4 = ptrInt2 + NUMTASK;
                for (int task2 = task1 + 1; task2 <= numTasks; task2++, ptrInt3 += NUMTASK, ptrInt4 += NUMTASK)
                {
                    int flight1 = solutionVND[0][task1];
                    int flight2 = solutionVND[0][task2];
                    if (flight1 == flight2) continue;
                    int a = flightCap[flight1];
                    int b = flightCap[flight2];
                    int delta = taskTime[task1] - taskTime[task2];
                    if ((timeCap + delta < a) || (timeCap < b + delta)) continue;
                    // accept and respect capacity constraints
                    bool flag = configMatr[solutionVND[1][flight2]][task1] && configMatr[solutionVND[1][flight1]][task2];
                    if (!flag) continue;
                    // check precedence constraints

                    if (flight1 < flight2)
                    {
                        //check task1's successors
                        for (int lId = 1; (lId <= ptrInt1[0]) && (flag); lId++)
                        {
                            if (solutionVND[0][ptrInt1[lId]] < flight2 + 1) flag = false;
                        }
                        //check task2's precedessors
                        for (int lId = 1; (lId <= ptrInt4[0]) && (flag); lId++)
                        {
                            if (flight1 < solutionVND[0][ptrInt4[lId]] + 1) flag = false;
                        }
                    }
                    else
                    {
                        //check task2's successors
                        for (int lId = 1; (lId <= ptrInt3[0]) && (flag); lId++)
                        {
                            if (solutionVND[0][ptrInt3[lId]] < flight1 + 1) flag = false;
                        }
                        //check task1's precedessors
                        for (int lId = 1; (lId <= ptrInt2[0]) && (flag); lId++)
                        {
                            if (flight2 < solutionVND[0][ptrInt2[lId]] + 1) flag = false;
                        }
                    }
                    if (!flag) continue;
                    // all constraints satisfied
                    solutionVND[0][task1] = flight2;
                    solutionVND[0][task2] = flight1;
                    flightCap[flight1] -= delta;
                    flightCap[flight2] += delta;
                    improve = true;
                }
            }

        }

        // Clear empty
        emptyFlight[0] = 1;
        for (int i = 1; i <= solutionVND[0][0]; i++)
        {
            if (flightCap[i] == 0)
            {
                emptyFlight[emptyFlight[0]] = i;
                emptyFlight[0]++;
            }
        }
        emptyFlight[0]--;
        count++;
        if (emptyFlight[0] > 0)
        {
            // for test
            int tmp = solutionVND[0][0];
            solutionVND[0][0] -= emptyFlight[0];
            for (int j = 1; j <= numTasks; j++)
            {
                for (int id = 1; id <= emptyFlight[0]; id++)
                {
                    if (id < emptyFlight[0] && emptyFlight[id] <= solutionVND[0][j] && emptyFlight[id + 1] > solutionVND[0][j])
                    {
                        solutionVND[0][j] -= id;
                    }
                    if (id == emptyFlight[0] && emptyFlight[id] <= solutionVND[0][j])
                    {
                        solutionVND[0][j] -= id;
                    }
                }
            }
            count = 0;
            memset(flightCap, 0, sizeof(flightCap));
            for (int j = 1; j <= numTasks; j++)
            {
                flightCap[solutionVND[0][j]] += taskTime[j];
            }
            // for configuration
            for (int emp = 1; emp <= emptyFlight[0]; emp++) 
            {
                for (int i = emptyFlight[emp] - emp + 1; i < tmp; i++) solutionVND[1][i] = solutionVND[1][i + 1];
                solutionVND[1][tmp] = 0;
                tmp--;
                //solutionVND[1].erase(solutionVND[1].begin() + emptyFlight[emp] - emp + 1);
            }
        }

        if (loop > 9999 || count > 1000) break;
        loop++;
    }
}

static void flightVND()
{
    // compute test scheduling in each flight
    for (int i = 1; i <= solutionVND[0][0]; i++) memset(testScheduling[i], 0, sizeof(int) * NUMTASK);

    for (int i = 1; i <= numTasks; i++)
    {
        int j = solutionVND[0][i];
        testScheduling[j][0]++;
        testScheduling[j][testScheduling[j][0]] = i;
    }
    // compute the workload of each configuration
    memset(workload, 0, sizeof(workload));
    for (int j = 1; j <= solutionVND[0][0]; j++)
    {
        workload[solutionVND[1][j]]++;
    }
    bool ifMove = false;

    // Swap 2 flights' configuration
    if (!ifMove)
    {
        for (int j1 = 1; j1 <= solutionVND[0][0]; j1++)
        {
            for (int j2 = j1 + 1; j2 <= solutionVND[0][0]; j2++)
            {
                int config1 = solutionVND[1][j1];
                int config2 = solutionVND[1][j2];
                ptrBool1 = &configMatr[config1][0];
                ptrBool2 = &configMatr[config2][0];
                bool flagConfig = true;
                for (int i = 1; (i <= testScheduling[j1][0]) && flagConfig; i++)
                {
                    flagConfig = flagConfig && ptrBool2[testScheduling[j1][i]];
                }
                for (int i = 1; (i <= testScheduling[j2][0]) && flagConfig; i++)
                {
                    flagConfig = flagConfig && ptrBool1[testScheduling[j2][i]];
                }
                if (flagConfig)
                {
                    int tmp = solutionVND[1][j1];
                    solutionVND[1][j1] = solutionVND[1][j2];
                    solutionVND[1][j2] = tmp;
                }

            }
        }
    }
}

// perturbation
static void Perturbation()
{
    srand(922);
    bool change = false;
    int maxDeleted = 8 > int(numTasks / 15) ? 8 : int(numTasks / 15);
    int rho = maxDeleted;

    std::vector<int> XCopy(numTasks + 1, 0);
    memcpy(XCopy.data(), solutionVND[0], sizeof(int) * XCopy.size());
    std::vector<int> YCopy(solutionVND[0][0] + 1, 0);
    memcpy(YCopy.data(), solutionVND[1], sizeof(int) * YCopy.size());
    std::vector<int> workload(numConfig + 1);
    for (int j = 1; j <= XCopy[0]; j++) workload[YCopy[j]]++;
    int count = 0;
    while (change == false && count < 5)
    {
        change = true;
        // random choice
        std::vector<int> removedList;
        for (int i = 0; i < rho;)
        {
            bool flag = true;
            int r = 1 + rand() % numTasks;
            for (int j = 0; j < removedList.size(); j++)
            {
                if (r == removedList[j])
                {
                    flag = false;
                    break;
                }
            }
            if (flag == true)
            {
                removedList.push_back(r);
                i++;
            }
        }
        // remove task
        for (int i = 0; i < removedList.size(); i++)
        {
            XCopy[removedList[i]] = 0;
        }
        // delete empty flight
        std::vector<int> emptyFlight(XCopy[0] + 1);
        emptyFlight.resize(XCopy[0] + 1);
        for (int i = 1; i <= numTasks; i++)
        {
            emptyFlight[XCopy[i]] = 1;
        }
        std::vector<int> emptyFlight2 = { 0 };
        for (int j = 1; j <= XCopy[0]; j++)
        {
            if (emptyFlight[j] == 0)
            {
                workload[YCopy[j]]--;
                emptyFlight2.push_back(j);
                emptyFlight2[0]++;
            }
        }
        XCopy[0] -= emptyFlight2[0];
        for (int j = 1; j <= numTasks; j++)
        {
            for (int id = 1; id <= emptyFlight2[0]; id++)
            {
                if (id < emptyFlight2[0] && emptyFlight2[id] <= XCopy[j] && emptyFlight2[id + 1] > XCopy[j])
                {
                    XCopy[j] -= id;
                }
                if (id == emptyFlight2[0] && emptyFlight2[id] <= XCopy[j])
                {
                    XCopy[j] -= id;
                }
            }
        }

        for (int emp = 1; emp <= emptyFlight2[0]; emp++)
        {
            int pos = emptyFlight2[emp] - emp + 1;
            YCopy.erase(YCopy.begin() + pos);  // a bug of VS, i cannot directly write: YCopy.begin()+ emptyFlight2[emp] - emp + 1;
        }

        // Repair
        std::vector<int> taskSumList(XCopy[0] + 1);
        for (int i = 1; i <= numTasks; i++)
        {
            if (XCopy[i] > 0)
            {
                taskSumList[XCopy[i]] += taskTime[i];
            }
        }
        std::vector<int> XCopy2(XCopy);
        std::vector<int> YCopy2(YCopy);
        for (int i = 0; i < removedList.size(); i++)
        {
            int item = removedList[i];
            bool flag = false;
            for (int bins = 1; bins <= XCopy2[0]; bins++)
            {
                bool flagCap = false;
                bool flagPrec = true;
                bool flagConfig = false;
                // check capacity canstraint
                if (taskSumList[bins] + taskTime[item] <= timeCap)
                {
                    flagCap = true;
                    // check precdence constraint
                    for (int j = 1; j <= directPreds[item][0]; j++)
                    {
                        if (bins - XCopy2[directPreds[item][j]] < 1)
                        {
                            flagPrec = false;
                            break;
                        }
                    }
                    for (int j = 1; (j <= directSucs[item][0]) && (flagPrec); j++)
                    {
                        if (XCopy2[directSucs[item][j]] - bins < 1) flagPrec = false;
                    }
                    //check configuration constraint
                    if (flagPrec)
                    {
                        flagConfig = configMatr[YCopy2[bins]][item];

                        if (!flagConfig)
                        {
                            // try to change the sort of bins
                            for (int k = 1; k <= numConfig; k++)
                            {
                                if (configMatr[k][item] && workload[k] < Ck[k])
                                {
                                    bool flag_adj = true;
                                    for (int j = 1; (j <= numTasks) && flag_adj; j++)
                                    {
                                        if (XCopy2[j] == bins) flag_adj = flag_adj && configMatr[k][j];
                                    }
                                    if (flag_adj == true) // change
                                    {
                                        flagConfig = true;
                                        workload[YCopy2[bins]]--;
                                        YCopy2[bins] = k;
                                        workload[k]++;
                                        break;
                                    }
                                }
                            }
                        }
                    }
                }
                if (flagCap && flagPrec && flagConfig)
                {
                    // the current item can be packed in bins, and consider the next item
                    XCopy2[item] = bins;
                    taskSumList[bins] += taskTime[item];
                    flag = true;
                    break;
                }
            }
            if (flag == false)
            {
                // none of the current bin can pack bin, try to open a new bin
                // only need to check precedence constraint, then find the sort of the new bin and left capacity
                for (int location = 1; location <= XCopy2[0] + 1; location++)
                {
                    flag = true;
                    for (int j = 1; j <= directPreds[item][0]; j++)
                    {
                        if (location <= XCopy2[directPreds[item][j]])
                        {
                            flag = false;
                            break;
                        }
                    }
                    for (int j = 1; (j <= directSucs[item][0]) && (flag); j++)
                    {
                        if (location > XCopy2[directSucs[item][j]])
                        {
                            flag = false;
                            break;
                        }
                    }
                    if (flag)
                    {
                        // try to find feasible location
                        for (int k = 1; k <= numConfig; k++)
                        {
                            flag = false;
                            if (configMatr[k][item] && workload[k] < Ck[k])
                            {
                                flag = true;
                                YCopy2.insert(YCopy2.begin() + location, k);
                                workload[k]++;
                                taskSumList.insert(taskSumList.begin() + location, taskTime[item]);
                                for (int i = 1; i <= numTasks; i++)
                                {
                                    if (XCopy2[i] >= location) XCopy2[i]++;
                                }
                                XCopy2[item] = location;
                                XCopy2[0]++;
                                break;
                            }
                        }
                        break;
                    }
                }
            }
            change = change && flag;
            if (flag)
            {
                XCopy = XCopy2;
                YCopy = YCopy2;
            }
            else break;
        }
        if (change == false)
        {
            memcpy(XCopy.data(), solutionVND[0], sizeof(int)* (numTasks + 1));
            YCopy.resize(solutionVND[0][0] + 1);
            memcpy(YCopy.data(), solutionVND[1], sizeof(int)* (solutionVND[0][0] + 1));
            rho--;
            if (rho == 1)
            {
                rho = maxDeleted;
                count++;
            }
        }
        else
        {
            memcpy(solutionVND[0], XCopy.data(), sizeof(int)* XCopy.size());
            memcpy(solutionVND[1], YCopy.data(), sizeof(int)* YCopy.size());
        }
    }
}

void ILS()
{
    clock_t start = clock();
    int UB_pre = incumbentSol[0][0];
    memcpy(solutionVND[0], incumbentSol[0].data(), (numTasks + 1) * sizeof(int));
    memcpy(solutionVND[1], incumbentSol[1].data(), (incumbentSol[0][0] + 1) * sizeof(int));
    //solutionVND = incumbentSol;
    int count1 = 0;
    while (incumbentSol[0][0] > rootLB && count1 < 5)
    {
        int count2 = 0;
        while (count2 < 10)
        {
            backwardVND();
            forwardVND();
            if(numConfig > 1) flightVND();
            count2++;
        }
        if (incumbentSol[0][0] > solutionVND[0][0])
        {
            memcpy(incumbentSol[0].data(), solutionVND[0], (numTasks + 1) * sizeof(int));
            incumbentSol[1].resize(solutionVND[0][0] + 1);
            memcpy(incumbentSol[1].data(), solutionVND[1], (solutionVND[0][0] + 1) * sizeof(int));
        }
        Perturbation();
        count1++;
    }

    for (int i = 1; i <= numTasks; i++)
    {
        L[i] += incumbentSol[0][0] - UB_pre;
    }
    initTime += double(clock() - start) / CLKTCK;
}