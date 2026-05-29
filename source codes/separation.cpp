// This cpp file consists of two steps:
// 1. try to separate a violated minimal cover. this is equivalent to solve a knapsack problem by combo algorithm
// 2. try to extend and lift the obtained cover
#include "FTP.h"
#include "combo.h"

int zeta[NUMTASK];
int weight[NUMTASK];
int knapsackSol[NUMTASK];
double zetaOrigin[NUMTASK];
static double rhsVal1;		// sum_{j > j_0} x(i0, j)
static double rhsVal2;		// sum_k y(j0, k)
static bool ifSeparate;
int cover[NUMTASK];		
int omega[5];
int beta[NUMTASK];
static int omegaKnap[5];
static double maxDiffer;
static bool candidates[NUMTASK];
static int EFSol[NUMTASK];
//static int EFBestSol[NUMTASK];
static int valEF, bestValEF, tFeasibleEF, configEF, flagEF;

// compute the coefficients of differ in the separation problem
static inline void coeffForward(int i0, int j0)
{
	int cardP = directPreds[i0][0];
	int cardGamma = allGamma[i0][0];
	ifSeparate = true;
	int task;
	// compute original coefficients
	for (int i = 1; i <= cardP; i++)
	{
		task = directPreds[i0][i];
		zetaOrigin[i - 1] = rhsVal1 - xSol[j0][task];
		weight[i - 1] = taskTime[task];
	}
	for (int i = 0; i < cardGamma; i++)
	{
		task = allGamma[i0][i + 1];
		zetaOrigin[i + cardP] = rhsVal2 - xSol[j0][task];
		weight[i + cardP] = taskTime[task];
	}
}

// enumerate the forbidden sets satisfying capacity constraints, and find min f(C)
static inline void enumerateForbiddenSetForward(int i0, int j0)
{
	if (forbiddenSetCid[0] <= 0) return;
	int delta = 0; // see whether this set has two direct predecessors of task i0
	int task;
	double differ;
	int maxId = 0, maxDelta = 0;
	int omega_forbidden[5];
	memset(omega_forbidden, 0, sizeof(omega_forbidden));
	memset(omega, 0, sizeof(omega));
	for (int i = 1; i <= forbiddenSetCid[1]; i++)
	{
		task = forbiddenSetC[i];
		if(task == i0 || transMatr[i0][task])
		{
			delta = 0;
			break;
		}
		else if (transMatr[task][i0])
		{
			if (adjMatr[task][i0]) delta++;
			else 
			{
				delta = 0;
				break;
			}
		}
		else 
		{
			for (int k = 1; k <= numConfig; k++)
			{
				if (configMatrTranspose[task][k]) omega_forbidden[k]++;
			}
		}
	}
	if (delta >= 2)
	{
		differ = 0;
		// compute omega
		for (int k = 1; k <= numConfig; k++)
		{
			int a = 1, b = 1;
			for (int i = 1; i <= forbiddenSetCid[1]; i++)
			{
				task = forbiddenSetC[i];
				differ -= xSol[j0][task];
				if (configMatr[k][task]) continue;
				if (gammaMatr[task][i0]) a = 0;
				else b = 0;
			}
			if (a == 0 && b == 1) omega_forbidden[k] += 1;
		}
		// compute the difference: rhs - lhs
		differ += (delta - 1) * rhsVal1;
		for (int k = 1; k <= numConfig; k++) differ += omega_forbidden[k] * ySol[j0][k];
		if (differ + intTolerance < maxDiffer)
		{
			maxDiffer = differ;
			maxId = 1;
			maxDelta = delta;
			memcpy(omega, omega_forbidden, sizeof(omega_forbidden));
		}
	}
	memset(omega_forbidden, 0, sizeof(omega_forbidden));

	for (int id = 2; id <= forbiddenSetCid[0]; id++) 
	{
		delta = 0;
		for (int i = forbiddenSetCid[id - 1] + 1; i <= forbiddenSetCid[id]; i++) 
		{
			task = forbiddenSetC[i];
			if (task == i0 || transMatr[i0][task])
			{
				delta = 0;
				break;
			}
			else if (transMatr[task][i0])
			{
				if (adjMatr[task][i0]) delta++;
				else
				{
					delta = 0;
					break;
				}
			}
			else
			{
				for (int k = 1; k <= numConfig; k++)
				{
					if (configMatrTranspose[task][k]) omega_forbidden[k]++;
				}
			}
		}
		if (delta >= 2) 
		{
			differ = 0;
			// compute omega
			for (int k = 1; k <= numConfig; k++)
			{
				int a = 1, b = 1;
				for (int i = forbiddenSetCid[id - 1] + 1; i <= forbiddenSetCid[id]; i++)
				{
					task = forbiddenSetC[i];
					differ -= xSol[j0][task];
					if (configMatr[k][task]) continue;
					if (gammaMatr[task][i0]) a = 0;
					else b = 0;
				}
				if (a == 0 && b == 1) omega_forbidden[k] += 1;
			}
			// compute the difference: rhs - lhs
			differ += (delta - 1) * rhsVal1;
			for (int k = 1; k <= numConfig; k++) differ += omega_forbidden[k] * ySol[j0][k];
			if (differ + intTolerance < maxDiffer)
			{
				maxDiffer = differ;
				maxId = id;
				maxDelta = delta;
				memcpy(omega, omega_forbidden, sizeof(omega_forbidden));
			}
		}
		memset(omega_forbidden, 0, sizeof(omega_forbidden));
	}
	if (maxDiffer + intTolerance < 0)
	{
		// we find a violated cut!
		if (maxId == 1)
		{
			cover[0] = forbiddenSetCid[1];
			memcpy(&cover[1], &forbiddenSetC[1], sizeof(int) * cover[0]);
			cover[numTasks + 1] = maxDelta;
		}
		else 
		{
			cover[0] = forbiddenSetCid[maxId] - forbiddenSetCid[maxId - 1];
			memcpy(&cover[1], &forbiddenSetC[forbiddenSetCid[maxId - 1] + 1], sizeof(int) * cover[0]);
			cover[numTasks + 1] = maxDelta;
		}
	}
	else memset(omega, 0, sizeof(omega));
}

// solve knapsack problem
static inline void weakSeparationForward(int i0, int j0)
{
	int length = directPreds[i0][0] + allGamma[i0][0];
	// turn to integer
	double maxVal = 0;
	for (int i = 0; i < length; i++) maxVal = maxVal > zetaOrigin[i] ? maxVal : zetaOrigin[i];
	int factor = (int)floor(std::min(50000.0, 1e08 / maxVal) + intTolerance);
	for (int i = 0; i < length; i++) zeta[i] = (zetaOrigin[i] < 0 ? -1 : (int)floor(round(zetaOrigin[i] * factor) + intTolerance));
	combo_separation(length, zeta, weight, knapsackSol, precCapList[i0]);
	// compute the difference: rhs - lhs
	int coverKnap[NUMTASK] = { 0 };
	double differKnap = 0.0;
	int task;
	for (int i = 0; i < directPreds[i0][0]; i++)
	{
		if (knapsackSol[i] == 0) 
		{
			task = directPreds[i0][i + 1];
			coverKnap[0]++;
			coverKnap[coverKnap[0]] = task;
			differKnap -= xSol[j0][task];
		}
	}
	if (coverKnap[0] < 2) return;		// delta < 2, illegal cover
	coverKnap[numTasks + 1] = coverKnap[0];
	memset(omegaKnap, 0, sizeof(omegaKnap));
	for (int i = directPreds[i0][0]; i < length; i++)
	{
		if (knapsackSol[i] == 0)
		{
			task = allGamma[i0][i + 1 - directPreds[i0][0]];
			coverKnap[0]++;
			coverKnap[coverKnap[0]] = task;
			differKnap -= xSol[j0][task];
			for (int k = 1; k <= numConfig; k++)
			{
				if (configMatrTranspose[task][k]) omegaKnap[k]++;
			}
		}
	}
	for (int k = 1; k <= numConfig; k++)
	{
		int a = 1, b = 1;
		for (int i = 1; i <= coverKnap[numTasks + 1]; i++)
		{
			task = coverKnap[i];
			if (!configMatr[k][task])
			{
				b = 0;
				break;
			}
		}
		if (b != 1) continue;
		for (int i = coverKnap[numTasks + 1] + 1; i <= coverKnap[0]; i++)
		{
			task = coverKnap[i];
			if (!configMatr[k][task])
			{
				omegaKnap[k] += 1;
				break;
			}
		}
	}
	differKnap += (coverKnap[numTasks + 1] - 1) * rhsVal1;
	for (int k = 1; k <= numConfig; k++) differKnap += omegaKnap[k] * ySol[j0][k];

	if (differKnap + intTolerance < maxDiffer) 
	{
		maxDiffer = differKnap;
		memcpy(cover, coverKnap, sizeof(cover));
		memcpy(omega, omegaKnap, sizeof(omega));
	}
}

// extension & lifting
static inline void extendLiftForward(int i0, int j0) {}

static inline void coeffBackward(int i0, int j0) 
{
	int cardF = directSucs[i0][0];
	int cardGamma = allGamma[i0][0];
	ifSeparate = true;
	int task;
	// compute original coefficients
	for (int i = 1; i <= cardF; i++)
	{
		task = directSucs[i0][i];
		zetaOrigin[i - 1] = rhsVal1 - xSol[j0][task];
		weight[i - 1] = taskTime[task];
	}
	for (int i = 0; i < cardGamma; i++)
	{
		task = allGamma[i0][i + 1];
		zetaOrigin[i + cardF] = rhsVal2 - xSol[j0][task];
		weight[i + cardF] = taskTime[task];
	}
}

static inline void enumerateForbiddenSetBackward(int i0, int j0) 
{
	if (forbiddenSetCid[0] <= 0) return;
	int delta = 0; // see whether this set has two direct predecessors of task i0
	int task;
	double differ;
	int maxId = 0, maxDelta = 0;
	int omega_forbidden[5];
	memset(omega_forbidden, 0, sizeof(omega_forbidden));
	memset(omega, 0, sizeof(omega));
	for (int i = 1; i <= forbiddenSetCid[1]; i++)
	{
		task = forbiddenSetC[i];
		if (task == i0 || transMatr[task][i0])
		{
			delta = 0;
			break;
		}
		else if (transMatr[i0][task])
		{
			if (adjMatr[i0][task]) delta++;
			else
			{
				delta = 0;
				break;
			}
		}
		else
		{
			for (int k = 1; k <= numConfig; k++)
			{
				if (configMatrTranspose[task][k]) omega_forbidden[k]++;
			}
		}
	}
	if (delta >= 2)
	{
		differ = 0;
		// compute omega
		for (int k = 1; k <= numConfig; k++)
		{
			int a = 1, b = 1;
			for (int i = 1; i <= forbiddenSetCid[1]; i++)
			{
				task = forbiddenSetC[i];
				differ -= xSol[j0][task];
				if (configMatr[k][task]) continue;
				if (gammaMatr[task][i0]) a = 0;
				else b = 0;
			}
			if (a == 0 && b == 1) omega_forbidden[k] += 1;
		}
		// compute the difference: rhs - lhs
		differ += (delta - 1) * rhsVal1;
		for (int k = 1; k <= numConfig; k++) differ += omega_forbidden[k] * ySol[j0][k];
		if (differ + intTolerance < maxDiffer)
		{
			maxDiffer = differ;
			maxId = 1;
			maxDelta = delta;
			memcpy(omega, omega_forbidden, sizeof(omega_forbidden));
		}
	}
	memset(omega_forbidden, 0, sizeof(omega_forbidden));

	for (int id = 2; id <= forbiddenSetCid[0]; id++)
	{
		delta = 0;
		for (int i = forbiddenSetCid[id - 1] + 1; i <= forbiddenSetCid[id]; i++)
		{
			task = forbiddenSetC[i];
			if (task == i0 || transMatr[task][i0])
			{
				delta = 0;
				break;
			}
			else if (transMatr[i0][task])
			{
				if (adjMatr[i0][task]) delta++;
				else
				{
					delta = 0;
					break;
				}
			}
			else
			{
				for (int k = 1; k <= numConfig; k++)
				{
					if (configMatrTranspose[task][k]) omega_forbidden[k]++;
				}
			}
		}
		if (delta >= 2)
		{
			differ = 0;
			// compute omega
			for (int k = 1; k <= numConfig; k++)
			{
				int a = 1, b = 1;
				for (int i = forbiddenSetCid[id - 1] + 1; i <= forbiddenSetCid[id]; i++)
				{
					task = forbiddenSetC[i];
					differ -= xSol[j0][task];
					if (configMatr[k][task]) continue;
					if (gammaMatr[task][i0]) a = 0;
					else b = 0;
				}
				if (a == 0 && b == 1) omega_forbidden[k] += 1;
			}
			// compute the difference: rhs - lhs
			differ += (delta - 1) * rhsVal1;
			for (int k = 1; k <= numConfig; k++) differ += omega_forbidden[k] * ySol[j0][k];
			if (differ + intTolerance < maxDiffer)
			{
				maxDiffer = differ;
				maxId = id;
				maxDelta = delta;
				memcpy(omega, omega_forbidden, sizeof(omega_forbidden));
			}
		}
		memset(omega_forbidden, 0, sizeof(omega_forbidden));
	}
	if (maxDiffer + intTolerance < 0)
	{
		// we find a violated cut!
		if (maxId == 1)
		{
			cover[0] = forbiddenSetCid[1];
			memcpy(&cover[1], &forbiddenSetC[1], sizeof(int) * cover[0]);
			cover[numTasks + 1] = maxDelta;
		}
		else
		{
			cover[0] = forbiddenSetCid[maxId] - forbiddenSetCid[maxId - 1];
			memcpy(&cover[1], &forbiddenSetC[forbiddenSetCid[maxId - 1] + 1], sizeof(int) * cover[0]);
			cover[numTasks + 1] = maxDelta;
		}
	}
	else memset(omega, 0, sizeof(omega));
}

static inline void weakSeparationBackward(int i0, int j0) 
{
	int length = directSucs[i0][0] + allGamma[i0][0];
	// turn to integer
	double maxVal = 0;
	for (int i = 0; i < length; i++) maxVal = maxVal > zetaOrigin[i] ? maxVal : zetaOrigin[i];
	int factor = (int)floor(std::min(50000.0, 1e08 / maxVal) + intTolerance);
	for (int i = 0; i < length; i++) zeta[i] = (zetaOrigin[i] < 0 ? -1 : (int)floor(round(zetaOrigin[i] * factor) + intTolerance));
	combo_separation(length, zeta, weight, knapsackSol, sucsCapList[i0]);
	// compute the difference: rhs - lhs
	int coverKnap[NUMTASK] = { 0 };
	double differKnap = 0.0;
	int task;
	for (int i = 0; i < directSucs[i0][0]; i++)
	{
		if (knapsackSol[i] == 0)
		{
			task = directSucs[i0][i + 1];
			coverKnap[0]++;
			coverKnap[coverKnap[0]] = task;
			differKnap -= xSol[j0][task];
		}
	}
	if (coverKnap[0] < 2) return;		// delta < 2, illegal cover
	coverKnap[numTasks + 1] = coverKnap[0];
	memset(omegaKnap, 0, sizeof(omegaKnap));
	for (int i = directSucs[i0][0]; i < length; i++)
	{
		if (knapsackSol[i] == 0)
		{
			task = allGamma[i0][i + 1 - directSucs[i0][0]];
			coverKnap[0]++;
			coverKnap[coverKnap[0]] = task;
			differKnap -= xSol[j0][task];
			for (int k = 1; k <= numConfig; k++)
			{
				if (configMatrTranspose[task][k]) omegaKnap[k]++;
			}
		}
	}
	for (int k = 1; k <= numConfig; k++)
	{
		int a = 1, b = 1;
		for (int i = 1; i <= coverKnap[numTasks + 1]; i++)
		{
			task = coverKnap[i];
			if (!configMatr[k][task])
			{
				b = 0;
				break;
			}
		}
		if (b != 1) continue;
		for (int i = coverKnap[numTasks + 1] + 1; i <= coverKnap[0]; i++)
		{
			task = coverKnap[i];
			if (!configMatr[k][task])
			{
				omegaKnap[k] += 1;
				break;
			}
		}
	}
	differKnap += (coverKnap[numTasks + 1] - 1) * rhsVal1;
	for (int k = 1; k <= numConfig; k++) differKnap += omegaKnap[k] * ySol[j0][k];

	if (differKnap + intTolerance < maxDiffer)
	{
		maxDiffer = differKnap;
		memcpy(cover, coverKnap, sizeof(cover));
		memcpy(omega, omegaKnap, sizeof(omega));
	}
}

// separation procedure
int separation(int i0, int j0)
{
	// return 0: no violated cut found; 1: violated forward CP cut found; 2: violated backward CP cut found
	// check whether we need to separate cuts in forward direction
	rhsVal2 = 0;
	for (int k = 1; k <= numConfig; k++) rhsVal2 += ySol[j0][k];
	if(j0 == L[i0]) goto separateBack;
	rhsVal1 = 0;
	for (int j = j0 + 1; j <= L[i0]; j++) rhsVal1 += xSol[j][i0];
	if (rhsVal1 + intTolerance >= rhsVal2) goto separateBack;
	// compute zeta[i]
	coeffForward(i0, j0);
	// enumerate forbidden set
	maxDiffer = 0;
	memset(cover, 0, sizeof(cover));
	enumerateForbiddenSetForward(i0, j0);
	// knapsack separation
	weakSeparationForward(i0, j0);
	if (maxDiffer + intTolerance <= 0) return 1;
separateBack:
	if (j0 == E[i0]) return 0;
	// check whether we need to separate cuts in backward direction
	rhsVal1 = 0;
	for (int j = E[i0]; j < j0; j++) rhsVal1 += xSol[j][i0];
	if (rhsVal1 + intTolerance >= rhsVal2) return 0;
	// compute zeta[i]
	coeffBackward(i0, j0);
	// enumerate forbidden set
	maxDiffer = 0;
	memset(cover, 0, sizeof(cover));
	enumerateForbiddenSetBackward(i0, j0);
	// knapsack separation
	weakSeparationBackward(i0, j0);
	if (maxDiffer + intTolerance <= 0) return 2;
	return 0;
}

static void branchingEFProb(int position)
{
	int task = cover[position];
	if (taskTime[task] > tFeasibleEF) return;
	if (!configMatr[configEF][task]) return;
	if (flagEF == 1) { if (transMatr[EFSol[1]][task]) return; }
	else { if (transMatr[task][EFSol[1]]) return; }
	for (int i = 2; i <= EFSol[0]; i++) 
	{
		if (EFSol[i] < task) { if (transMatr[EFSol[i]][task]) return; }
		else { if (transMatr[task][EFSol[i]]) return; }
	}
	// do not use Dantzig bound here.
	// all constraints passed, assign.
	EFSol[0]++;
	EFSol[EFSol[0]] = task;
	tFeasibleEF -= taskTime[task];
	valEF += beta[position];
	if (bestValEF < valEF) 
	{
		bestValEF = valEF;
		//memcpy(EFBestSol, EFSol, sizeof(EFSol));
	}
	//bestValEF = valEF > bestValEF ? valEF : bestValEF;
	// branching
	for (int id = position + 1; id < cover[0]; id++) branchingEFProb(id);
	// disassign
	tFeasibleEF += taskTime[task];
	valEF -= beta[position];
	EFSol[EFSol[0]] = 0;
	EFSol[0]--;
}

static inline void bbEFProb()
{
	bestValEF = 0;
	valEF = 0;
	tFeasibleEF = timeCap - taskTime[EFSol[1]];
	//memset(EFBestSol, 0, sizeof(EFBestSol));
	// branch and bound for the KPC
	for (int id = 1; id < cover[0]; id++) branchingEFProb(id);
	bestValEF = omega[configEF] - bestValEF;
}

void extensionLifting(int direction, int i0, int j0) 
{
	//int maxEFtask = 100;
	memset(beta, 0, sizeof(beta));
	for (int i = 1; i <= cover[0]; i++) beta[cover[i]] = 1;
	memset(candidates, true, sizeof(candidates));
	for (int id = 1; id <= cover[0]; id++) candidates[cover[id]] = false;
	candidates[i0] = false;
	for (int i = 1; i <= numTasks; i++) 
	{
		if (E[i] > j0 || L[i] < j0) candidates[i] = false;
	}
	//int count = 0;
	int betaVal;
	if (direction == 1) // forward
	{
		for (int i = 1; i <= numTasks; i++) 
		{
			if (!candidates[i]) continue;
			//if (count >= maxEFtask) break;
			betaVal = NUMTASK;
			// pre-assign
			cover[0]++;
			cover[cover[0]] = i;
			configEF = 1;
			if (transMatr[i][i0]) 
			{
				while (configEF <= numConfig)
				{
					if (!configMatr[configEF][i]) { configEF++; continue; }
					memset(EFSol, 0, sizeof(EFSol));
					EFSol[0] = 2;
					EFSol[1] = i0;
					EFSol[2] = i;
					flagEF = 1;
					bbEFProb();
					bestValEF += (cover[numTasks + 1] - 1);
					if (betaVal > bestValEF) betaVal = bestValEF;
					if (betaVal == 0) break;
					configEF++;
				}
			}
			else if (transMatr[i0][i]) 
			{
				while (configEF <= numConfig)
				{
					if (!configMatr[configEF][i]) { configEF++; continue; }
					memset(EFSol, 0, sizeof(EFSol));
					EFSol[0] = 2;
					EFSol[1] = i0;
					EFSol[2] = i;
					flagEF = 2;
					bbEFProb();
					if (betaVal > bestValEF) betaVal = bestValEF;
					if (betaVal == 0) break;
					configEF++;
				}
			}
			else 
			{
				while (configEF <= numConfig)
				{
					if (!configMatr[configEF][i]) { configEF++; continue; }
					memset(EFSol, 0, sizeof(EFSol));
					EFSol[0] = 2;
					EFSol[1] = i0;
					EFSol[2] = i;
					flagEF = 1;
					bbEFProb();
					bestValEF += (cover[numTasks + 1] - 1);
					if (betaVal > bestValEF) betaVal = bestValEF;
					if (betaVal == 0) break;
					memset(EFSol, 0, sizeof(EFSol));
					EFSol[0] = 2;
					EFSol[1] = i0;
					EFSol[2] = i;
					flagEF = 2;
					bbEFProb();
					if (betaVal > bestValEF) betaVal = bestValEF;
					if (betaVal == 0) break;
					configEF++;
				}
			}
			if (betaVal == 0)
			{
				cover[cover[0]] = 0;
				cover[0]--;
			}
			else
			{
				beta[cover[0]] = betaVal;
				//count++;
			}
		}
	}
	else // backward 
	{
		for (int i = 1; i <= numTasks; i++)
		{
			if (!candidates[i]) continue;
			//if (count >= maxEFtask) break;
			betaVal = NUMTASK;
			cover[0]++;
			cover[cover[0]] = i;
			configEF = 1;
			if (transMatr[i][i0])
			{
				while (configEF <= numConfig)
				{
					if (!configMatr[configEF][i]) { configEF++; continue; }
					memset(EFSol, 0, sizeof(EFSol));
					EFSol[0] = 2;
					EFSol[1] = i0;
					EFSol[2] = i;
					flagEF = 1;
					bbEFProb();
					if (betaVal > bestValEF) betaVal = bestValEF;
					if (betaVal == 0) break;
					configEF++;
				}
			}
			else if (transMatr[i0][i])
			{
				while (configEF <= numConfig)
				{
					if (!configMatr[configEF][i]) { configEF++; continue; }
					memset(EFSol, 0, sizeof(EFSol));
					EFSol[0] = 2;
					EFSol[1] = i0;
					EFSol[2] = i;
					flagEF = 2;
					bbEFProb();
					bestValEF += (cover[numTasks + 1] - 1);
					if (betaVal > bestValEF) betaVal = bestValEF;
					if (betaVal == 0) break;
					configEF++;
				}
			}
			else
			{
				while (configEF <= numConfig)
				{
					if (!configMatr[configEF][i]) { configEF++; continue; }
					memset(EFSol, 0, sizeof(EFSol));
					EFSol[0] = 2;
					EFSol[1] = i0;
					EFSol[2] = i;
					flagEF = 1;
					bbEFProb();
					if (betaVal > bestValEF) betaVal = bestValEF;
					if (betaVal == 0) break;
					memset(EFSol, 0, sizeof(EFSol));
					EFSol[0] = 2;
					EFSol[1] = i0;
					EFSol[2] = i;
					flagEF = 2;
					bbEFProb();
					bestValEF += (cover[numTasks + 1] - 1);
					if (betaVal > bestValEF) betaVal = bestValEF;
					if (betaVal == 0) break;
					configEF++;
				}
			}
			if (betaVal == 0)
			{
				cover[cover[0]] = 0;
				cover[0]--;
			}
			else
			{
				beta[cover[0]] = betaVal;
				//count++;
			}
		}
	}
	betaVal = NUMTASK;
	while (configEF <= numConfig)
	{
		if (!configMatr[configEF][i0]) { configEF++; continue; }
		EFSol[0] = 2;
		EFSol[1] = i0;
		EFSol[2] = i0;
		flagEF = 1;
		bbEFProb();
		if (betaVal > bestValEF) betaVal = bestValEF;
		if (betaVal == 0) break;
		configEF++;
	}
	if (betaVal > 0) beta[cover[0] + 1] = betaVal;
}