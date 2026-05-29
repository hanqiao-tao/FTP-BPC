#define _CRT_SECURE_NO_WARNINGS
#pragma warning(disable:4101)
#pragma warning(disable:4244)
/* ======================================================================
			 combo.h,    S.Martello, D.Pisinger, P.Toth     feb 1997
   ====================================================================== */

   /* This is the header file of the COMBO algorithm described in
	* S.Martello, D.Pisinger, P.Toth: "Dynamic Programming and Strong
	* Bounds for the 0-1 Knapsack Problem".
	*/

	/* ======================================================================
					 type declarations
	   ====================================================================== */

typedef int           boolean; /* logical variable         */
typedef int           ntype;   /* number of states/items   */
typedef long          itype;   /* item profits and weights */
typedef long          stype;   /* sum of profit or weight  */

/* item record */
typedef struct {
	itype   p;              /* profit                  */
	itype   w;              /* weight                  */
	boolean x;              /* solution variable       */
} item;

/* ======================================================================
				  forward declarations
   ====================================================================== */
#ifdef __cplusplus
extern "C" {
#endif
	int combo_separation(int n, int* p, int* w, int* x, int c);
	// n : number of tasks
	// *p: the array of coefficients
	// *w: Job_time
	// *x: solution vector for the knapsack problem
	// c : due_date, i.e., capacity 
	// return knpsack obj val
#ifdef __cplusplus
}
#endif
