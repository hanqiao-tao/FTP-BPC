#include "FTP.h"

bool instanceReader(std::string filename) //pre_matr size numTasks+1 / numTasks+1
{
    std::ifstream fin;
    fin.open(filename);
    if (fin.is_open() == true)
    {
        std::string line_str;
        std::getline(fin, line_str);
        assert(line_str == "<number of tasks>");
        std::getline(fin, line_str);
        //numTasks = std::stoi(line_str);

        std::getline(fin, line_str);//emptyline
        std::getline(fin, line_str);
        assert(line_str == "<cycle time>");
        std::getline(fin, line_str);
        timeCap = std::stoi(line_str);

        std::getline(fin, line_str);//emptyline
        std::getline(fin, line_str);
        assert(line_str == "<order strength>");
        std::getline(fin, line_str);

        std::getline(fin, line_str);//emptyline
        if (numTasks <= 100 || numTasks == 1000) std::getline(fin, line_str);//emptyline, delete this line when n = 300!!!
        std::getline(fin, line_str);
        assert(line_str == "<task times>");

        //read in processing times
        taskTime[0] = 0;
        for (int j = 1; j <= numTasks; j++)
        {
            std::string no_j, dur_j;
            getline(fin, line_str);
            std::stringstream ss(line_str);
            std::getline(ss, no_j, ' ');
            int cur_j = std::stoi(no_j);
            assert(cur_j == j);

            std::getline(ss, dur_j, ' ');
            taskTime[j] = std::stoi(dur_j);
        }

        //read in precedence relations into the matrix
        std::getline(fin, line_str);//emptyline
        std::getline(fin, line_str);
        precdenceRelation.reserve(numTasks * numTasks / 2);
        assert(line_str == "<precedence relations>");
        while (getline(fin, line_str) && line_str.empty() == false)
        {
            std::string pre_s, suc_s;
            std::stringstream ss(line_str);
            std::getline(ss, pre_s, ',');
            int pre = std::stoi(pre_s);
            std::getline(ss, suc_s, ',');
            int suc = std::stoi(suc_s);
            assert(pre < suc);
            adjMatr[pre][suc] = true;
            precdenceRelation.push_back(std::make_pair(pre, suc));
        }
        std::getline(fin, line_str);
        assert(line_str == "<end>");
        fin.close();
        return true;
    }
    else
    {
        std::cerr << "Instance reading Error!!!\n";
        return false;
    }
}

bool instanceReaderOld(std::string filename)
{
    std::ifstream fin;
    fin.open(filename);
    if (fin.is_open() == true) 
    {
        std::string line_str;
        std::getline(fin, line_str);
        numTasks = std::stoi(line_str);
        for (int i = 1; i <= numTasks; i++) 
        {
            std::getline(fin, line_str);
            taskTime[i] = std::stoi(line_str);
        }
        precdenceRelation.reserve(numTasks * numTasks / 2);
        while (getline(fin, line_str) && line_str.empty() == false)
        {
            std::string pre_s, suc_s;
            std::stringstream ss(line_str);
            std::getline(ss, pre_s, ',');
            int pre = std::stoi(pre_s);
            std::getline(ss, suc_s, ',');
            int suc = std::stoi(suc_s);
            if (pre == -1 && suc == -1) 
                break;
            adjMatr[pre][suc] = true;
            precdenceRelation.push_back(std::make_pair(pre, suc));
        }
        fin.close();
        return true;
    }
    else
    {
        std::cerr << "Instance reading Error!!!\n";
        return false;
    }
}

bool configurationReader(std::string filename)
{
    std::ifstream fin;
    fin.open(filename);
    if (fin.is_open() == true)
    {
        std::string line_str;
        int k_id = 1;
        while (std::getline(fin, line_str) && line_str.empty() == false)
        {
            std::stringstream ss(line_str);
            std::string s;
            std::getline(ss, s, '\040');
            int i_id = 1;
            while (s.empty() == false)
            {
                configMatr[k_id][i_id] = stoi(s);
                std::getline(ss, s, '\040');
                std::getline(ss, s, '\040');
                i_id++;
            }
            k_id++;
        }
        fin.close();
        return true;
    }
    else
    {
        std::cerr << "Configuration reading Error!!!\n";
        return false;
    }
}

// check solution if feasible
bool check()
{
    bool flag = 1;
    std::vector<int> bin_sum(1 + incumbentSol[0][0], 0);
    for (int i = 1; i <= numTasks; i++)
    {
        if (incumbentSol[0][i] == 0)
        {
            flag = false;
            std::cout << "unassigned: " << i << std::endl;
        }
        if (incumbentSol[0][i] > incumbentSol[0][0])
        {
            flag = false;
            std::cout << "error" << i << std::endl;
        }
        bin_sum[incumbentSol[0][i]] += taskTime[i];
    }
    for (int j = 1; j <= numTasks; j++) 
    {
        if (E[j] > incumbentSol[0][j]) std::cout << "efalse: " << j << std::endl;
        if (L[j] < incumbentSol[0][j]) std::cout << "lfalse: " << j << std::endl;
    }
    for (int j = 1; (flag == 1) && (j <= incumbentSol[0][0]); j++)
    {
        if (bin_sum[j] > timeCap)
        {
            flag = false;
            std::cout << "capacity: " << j << std::endl;
        }
        if (bin_sum[j] == 0) std::cout << "empty bin: " << j << "\n";
    }
    //precedence constraints
    for (int k = 0; k < precdenceRelation.size(); k++)
    {
        int i2 = precdenceRelation[k].second;
        int i1 = precdenceRelation[k].first;
        if (adjMatr[i1][i2] && incumbentSol[0][i2] - incumbentSol[0][i1] < 1)
        {
            std::cout << "precedence: " << i1 << "  " << i2 << std::endl;
            flag = false;
        }
    }
    // configuration and flight constraints
    if (numConfig > 1) 
    {
        std::vector<int> config_use(1 + incumbentSol[0][0], 0);
        for (int i = 1; i <= incumbentSol[0][0]; i++)
        {
            config_use[incumbentSol[1][i]]++;
            if (config_use[incumbentSol[1][i]] > Ck[incumbentSol[1][i]])
            {
                std::cout << "flight: " << i << "  " << incumbentSol[1][i] << std::endl;
                flag = false;
            }
            int config = incumbentSol[1][i];
            for (int j = 1; j <= numTasks; j++)
            {
                if (incumbentSol[0][j] == i)
                {
                    if (configMatr[config][j] == false)
                    {
                        std::cout << "config: " << config << " " << j << std::endl;
                        flag = false;
                    }
                }
            }
        }
    }
    return flag;
}

void writeLogFile(const std::string& szString)
{
    std::ofstream fout;
    fout.open(outName, std::ios_base::app);
    fout << szString << std::endl;
    fout.close();
}

void writeLogFileByEntry(const std::string& szString)
{
    std::ofstream fout;
    fout.open(outName, std::ios_base::app);
    fout << szString << '\t';
    fout.close();
}

void writeOutHeader()
{
    if (logOrNot == true)
    {
        writeLogFileByEntry("UB");
        writeLogFileByEntry("LB");
        writeLogFileByEntry("totalTime");
        writeLogFileByEntry("LBTime");
        writeLogFileByEntry("initTime");
        if (numTasks <= 300)
        {
            writeLogFileByEntry("pricingTime");
            writeLogFileByEntry("separateCPTime");
            writeLogFileByEntry("separateTCTime");
            writeLogFileByEntry("totalColNum");
            writeLogFileByEntry("CPcutNum");
            writeLogFileByEntry("TCcutNum");
            writeLogFileByEntry("maxBBTreeDepth");
            writeLogFileByEntry("numNodeExplored");
            writeLogFileByEntry("instance feasibility");
        }
    }
}

void writeOutLog()
{
    pricingTime = pricingTime / CLKTCK;
    separateCPTime = separateCPTime / CLKTCK;
    separateTCTime = separateTCTime / CLKTCK;
    if (logOrNot)
    {
        writeLogFile("");
        writeLogFileByEntry(std::to_string(int(globalUpperbound)));         //write optimal solution 
        if (overTime == false && overStack == false) writeLogFileByEntry(std::to_string(int(globalUpperbound)));//optimal
        else writeLogFileByEntry(std::to_string(int(rootLB)));              //root lower bound 
        writeLogFileByEntry(std::to_string(totalTime));                     //write time
        writeLogFileByEntry(std::to_string(LBTime));                        //write LB time
        writeLogFileByEntry(std::to_string(initTime));                      //write initial solution time
        writeLogFileByEntry(std::to_string(pricingTime));                   //write pricing time
        writeLogFileByEntry(std::to_string(separateCPTime));                //write separation time for CP cut
        writeLogFileByEntry(std::to_string(separateTCTime));                //write separation time for TC cut
        writeLogFileByEntry(std::to_string(totalColNum));                   //number of columns
        writeLogFileByEntry(std::to_string(CPcutNum));                      //number of CP cuts
        writeLogFileByEntry(std::to_string(TCcutNum));                      //number of TC cuts
        writeLogFileByEntry(std::to_string(maxBBTreeDepth));                //largest depth
        writeLogFileByEntry(std::to_string(numNodeExplored));               //number of nodes
        writeLogFileByEntry(std::to_string(instanceFeasibility));           //feasibility
    }
    std::cout << "----------BPC algorithm solved results----------\n";
    if (instanceFeasibility == 0) std::cout << "infeasible instance!!\n";
    else if (instanceFeasibility == -1) std::cout << "unknown instance feasibility!!\n";
    else if (instanceFeasibility == 1 && !overTime && !overStack)//problem solved
    {
        //output the import information
        std::cout << "The optimal solution is: " << int(globalUpperbound) << std::endl;
        std::cout << "Time used to solve the problem is: " << totalTime << "s" << std::endl;
        std::cout << "Number of the nodes examined is: " << numNodeExplored << std::endl;
        std::cout << "Number of columns generated is: " << totalColNum << ", time used to solve pricing problems is: " << pricingTime << "s" << std::endl;
        std::cout << "Number of CP cuts generated is:" << CPcutNum << ", time used to separate CP cut is: " << separateCPTime << "s" << std::endl;
    }
    else if (instanceFeasibility == 1 && overTime)//time out
    {
        //output the import information
        std::cout << "Running out of time! Failed to solve instance to optimality in " << runTimeLimit << "s!" << std::endl;
        std::cout << "The solution is: " << int(globalUpperbound) << std::endl;
        std::cout << "The lower bound is: " << int(rootLB) << std::endl;
        std::cout << "Time used to solve the problem is: " << totalTime << std::endl;
        std::cout << "Number of the nodes examined is: " << numNodeExplored << std::endl;
        std::cout << "Number of columns generated is: " << totalColNum << ", time used to solve pricing problems is: " << pricingTime << std::endl;
        std::cout << "Number of CP cuts generated is:" << CPcutNum << ", time used to separate CP cut is: " << separateCPTime << std::endl;
    }
    else if (instanceFeasibility == 1 && overStack)//stack overflow
    {
        //output the import information
        std::cout << "Running out of the nodes in stack! Failed to solve instance to optimality!" << std::endl;
        std::cout << "The solution is: " << int(globalUpperbound) << std::endl;
        std::cout << "The lower bound is: " << int(rootLB) << std::endl;
        std::cout << "Time used to solve the problem is: " << totalTime << std::endl;
        std::cout << "Number of the nodes examined is: " << numNodeExplored << std::endl;
        std::cout << "Number of columns generated is: " << totalColNum << ", time used to solve pricing problems is: " << pricingTime << std::endl;
        std::cout << "Number of CP cuts generated is:" << CPcutNum << ", time used to separate CP cut is: " << separateCPTime << std::endl;
    }
    std::cout << std::endl << std::endl;
}