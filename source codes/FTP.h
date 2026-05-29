#define _CRT_SECURE_NO_WARNINGS
#pragma warning(disable:4267)

#include <iostream>
#include <cstdio>
#include <fstream>
#include <sstream>
#include <vector>
#include <queue>
#include <array>
#include <ctime>
#include <malloc.h>
#include "coptcpp_pch.h"
#include <boost/unordered_set.hpp>
#include <boost/unordered_map.hpp>
#include <boost/unordered/unordered_flat_set.hpp>
#include <boost/unordered/unordered_flat_map.hpp>
#include "xxhash.h"

#ifndef CLKTCK
#define CLKTCK	CLOCKS_PER_SEC
#endif

#define  MALLOC(x,n,type) do									   \
{																   \
	if ((x = (type *) malloc( (n) * sizeof(type))) == NULL)		   \
	{															   \
	    fprintf(stderr,"out of memory\n");                         \
        fprintf(stderr,"x %d type\n",n);                           \
	    exit(1);                                                   \
	}															   \
} while (0)

//using namespace std;

#define NUMTASK 300  
#define NUMTASKSQUARE  90000 
#define kMax 21

#define MAXNODE 500           //static assigned number of potentially occupied nodes
#define UPPERBOUND 99999      //Initializing upperbound for nodes
#define MAXCOL 20000		  //limit of the number of columns for a flight in one node
#define intTolerance 1e-6	  //numerical tolerance

// control parameters
extern double runTimeLimit;
extern double initTimeLimit;
extern bool logOrNot;
extern bool addCPcuts;
extern bool addTCcuts;
extern bool addNonrobustCut;
extern bool ifExtensionLifting;
extern bool instanceType;

// statstics
extern double globalUpperbound;
extern double rootLB;
extern int initUB;

extern int numNodeExplored;
extern int maxBBTreeDepth;
extern int totalColNum;
extern int CPcutNum;
extern int TCcutNum;

extern double totalTime;
extern double LBTime;
extern double initTime;
extern double pricingTime;
extern double separateCPTime;
extern double separateTCTime;

extern bool overTime;
extern bool overStack;

extern bool initFeasiblity;
extern int instanceFeasibility;

// instance
extern std::string instanceName;
extern std::string outName;
extern int numTasks;
extern int timeCap;
extern int taskTime[NUMTASK];
extern double taskTimeInv[NUMTASK];
extern std::vector<std::pair<int, int>> precdenceRelation;
extern int E[NUMTASK];
extern int L[NUMTASK];
extern int numConfig;
extern std::vector<int> Ck;								  // workload limit for each configuration
extern std::vector<int> CkBar;							  
extern std::vector<int> CkSum;							  // CkSum[config + 1] = Ck[1] + ... + Ck[config], for Hungarian algorithm
extern int CkLabel;

extern bool adjMatr[NUMTASK][NUMTASK];
extern int directSucs[NUMTASK][NUMTASK];
extern int directPreds[NUMTASK][NUMTASK];

extern bool transMatr[NUMTASK][NUMTASK];
extern int allSucs[NUMTASK][NUMTASK];
extern int allPreds[NUMTASK][NUMTASK];

extern bool gammaMatr[NUMTASK][NUMTASK];
extern int allGamma[NUMTASK][NUMTASK];

extern bool configMatr[5][NUMTASK];
extern bool configMatrTranspose[NUMTASK][5];
extern char compatibleSet[NUMTASK][5];

// others
extern std::string fileName;
extern std::string fileSolName;
extern std::vector<std::vector<int>> incumbentSol;

// lowerBounds.cpp
extern double p[NUMTASK];
extern bool apply[NUMTASK];
extern int order[NUMTASK];
extern double dataLB[NUMTASKSQUARE * kMax];
extern double headsLB[NUMTASKSQUARE * kMax];
extern double tailsLB[NUMTASKSQUARE * kMax];

// boundedDynamicProgramming.cpp
extern int positionalWeight[NUMTASK];
extern bool potentiallyDominate[NUMTASK][NUMTASK];

struct CutValue2
{
	int taskSet[2];
	bool operator==(const CutValue2& cmp) const
	{
		return (memcmp(taskSet, cmp.taskSet, 8) == 0);
	}
};

struct DataHashCut2
{
	size_t operator()(const CutValue2& val) const
	{
		return XXH3_64bits(val.taskSet, 8);
	}
};

struct CutValue3
{
	int taskSet[3];
	bool operator==(const CutValue3& cmp) const
	{
		return (memcmp(taskSet, cmp.taskSet, 12) == 0);
	}
};

struct DataHashCut3
{
	size_t operator()(const CutValue3& val) const
	{
		return XXH3_64bits(val.taskSet, 12);
	}
};


extern boost::unordered_flat_map<CutValue2, std::pair<int, int>, DataHashCut2> cutMap2;		// ->second.first--> l_j(cut_b); second.second--> e_j(cut_f)
extern boost::unordered_flat_map<CutValue3, std::pair<int, int>, DataHashCut3> cutMap3;

// pricingProblem.cpp
extern int bestSol[NUMTASK + 14];
extern double bestPrice;

//separation.cpp
extern int cover[NUMTASK];
extern int omega[5];
extern int beta[NUMTASK];

// branchPriceAndCut.cpp
extern int configurationSubset[16][5];
extern int configurationSubsetC[16][5];
extern int configurationSubsetNumber;
extern int forbiddenSetC[NUMTASK * 4];
extern int forbiddenSetCid[NUMTASK * 4];
extern int precCapList[NUMTASK];  // \sum_{i \in P_{i_0} \cup \Gamma_{i_0}} l_i - L - 1
extern int sucsCapList[NUMTASK];  // \sum_{i \in F_{i_0} \cup \Gamma_{i_0}} l_i - L - 1

extern double dualCol[NUMTASK + 14];
extern double xSol[NUMTASK][NUMTASK];
extern double ySol[NUMTASK][5];  
//define the branch-and-bound tree node
struct Node 
{
	double upperbound;												//the upperbound of current node
	double lowerbound;												//the lowerbound of current node
	Node* parent;
	Node* lchild;
	Node* rchild;
	Node* next;														//linked list next available position
	Node* SlistNext;												//point to Slist linked list next node

	bool optimized;													//whether the current node is optimized with column-generation or not
	bool integral;													//whether the solution of the node is integral, if it is upperbound=lowerbound check with global upperbound, and the node can be add the available list
	bool infeasible;												//whether the current node is feasible
	bool ifDelete;													//whether the current node is deleted from the B&B tree
	int treeNodeDepth;												//depth in the B&B tree
	double criterion;

	std::array<std::vector<int>, NUMTASK> valid;					//indices of valid columns for this node, should be parent node's valid columns removing infeasible columns and adding generated columns
	std::vector<std::array<int, 3>> branchChoice;					//branching choices made, NOTE: [0/1/2][j][i] add the new job j and station i of the current node after optimization, first element:: 0 not indicated, 1 as left, 2 as right  
	std::vector<std::vector<bool>> nontakeMatr;						//branching choices recorded by a matrix, nontakeMatr[i][j]=1 meaning job j cannot be put in station i, NOTE:should be initialized for the root node
	//contructor for new nodes             
	Node() :															      
		parent(nullptr),
		lchild(nullptr),
		rchild(nullptr),
		next(nullptr),
		SlistNext(nullptr),

		treeNodeDepth(0),
		upperbound(UPPERBOUND),
		lowerbound(0),
		criterion(0),

		optimized(false),
		integral(false),
		infeasible(false),
		ifDelete(false)
	{
		std::vector<std::vector<bool>>().swap(nontakeMatr);
		std::vector<std::array<int, 3>>().swap(branchChoice);
	};
};
extern Node* root;
extern Node nodeArray[];						//nodes array in the initial linked list
extern Node head;
extern Node s_head;
extern Node stackBottom;
extern Node listEnd;
extern Node* listHead;
extern Node* L_end;								//linked list for the available nodes
extern Node* SlistHead;						    //Slist linked list
extern Node* bottom;
extern Node* stackTop;							//stack, LIFO, at beginning the top pointer points to the bottom

/*Functions in io.cpp*/
bool instanceReader(std::string filename);
bool instanceReaderOld(std::string filename);
bool configurationReader(std::string filename);
void writeOutHeader();
void writeOutLog();
bool check();
void writeLogFile(const std::string& szString);
void writeLogFileByEntry(const std::string& szString);

/*Functions in lowerBound.cpp*/
inline void Sort(int list[], double* pesos, int beg, int end, int posicionInicial);
void computeMachineLB();
void computeDWLB();

/*Functions in boundedDynamicProgramming.cpp*/
void bdp(int version);

/*Functions in cyclicBestFirstSearch.cpp*/
void cyclicBestFirstSearch();

/*Functions in iteratedLocalSearch.cpp*/
void ILS();

/*Functions in branchPriceAndCut.cpp*/
void BPCInitialSolution();
void branchPriceAndCut();

/*Functions in pricingProblem.cpp*/
void bbPricing(int stationPrice);

/*Functions in separation.cpp*/
int separation(int i0, int j0);
void extensionLifting(int direction, int i0, int j0);

/*Functions in branchingTree.cpp*/
void listInit();
void listAdd(Node* n);
Node* listTake();
int stackDepth();
void stackPush(Node* n);
Node* stackPop();
void stackPrune();
void stackInit();
