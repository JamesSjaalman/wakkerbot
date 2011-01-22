
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include <math.h>

#undef NDEBUG
#include <assert.h>

#include "crosstab.h"

#define COUNTOF(a) (sizeof(a) / sizeof(a)[0])
#define FRAC_LIMIT 0.1

#define SHOW_CALLS 0
#define SHOW_FUZZ 0
#define SHOW_ITER 0
#define SHOW_GEHANNUS 0
#define SHOW_PERMUTE 0
#define SHOW_INDEXES 0
struct label {
	size_t size;
	size_t used;
	char ** tabl ;
	} *labels;


static void cross_wipe_slot(struct crosstab *ptr,unsigned int slot);
static void cross_fuzz_slot(struct crosstab *ptr,unsigned int slot);
static unsigned int cross_find_slot(struct crosstab *ptr,unsigned int num);
static unsigned int cross_alloc_slot(struct crosstab *ptr);
static unsigned int *crosstab_hnd(struct crosstab *ptr, unsigned int key);
static double crosstab_value(struct crosstab *ptr,unsigned slot);
static void crosstab_bin_dump(struct crosstab *ptr);

static void row_format_slots(struct crossrow *tab, unsigned int cnt);
static void crosstab_reclaim(struct crosstab * ptr, unsigned int newsize);
static void crosstab_reorder(struct crosstab * ptr);
static void crosstab_recalc(struct crosstab * ptr);
double iterding(double *vec, unsigned int *mx, unsigned int cnt);
static void index_doubles( unsigned *index, double *values, unsigned cnt);
static int cmp_ranked_double(const void *l, const void *r);
static void index2_2d( unsigned *target, unsigned *index, unsigned cnt);
static unsigned permute_doubles( double *values, unsigned *index, unsigned cnt);
static unsigned permute_unsigned( unsigned *values, unsigned *index, unsigned cnt);
static unsigned permute_rows( struct crossrow *rows, unsigned *index, unsigned cnt);
static unsigned get_label (char *dst, unsigned num);

extern unsigned urnd(unsigned lim);


static unsigned int xy2zz(unsigned int x, unsigned int y) { 
if (x > y) 
	return y+(x*(x+1))/2; 
else	return x+(y*(y+1))/2; 
}
	/* The index of a cell in our LU matrix, given its X,Y coordinates */
#define XY2ZZ(x,y) xy2zz((x),(y))
	/* the amount of cells we need for an LU matrix */
#define LUSIZE(s) (((s)*((s)+1))/2)

unsigned crosstab_get(struct crosstab *ptr,unsigned idx)
{
unsigned slot;
slot = ptr->index[idx];
return ptr->table[slot].hash.key;
}

double crosstab_ask(struct crosstab *ptr,unsigned sym)
{
double this;
unsigned int *up;

	/* search hashtable to find element */
up = crosstab_hnd(ptr, sym);
this = crosstab_value(ptr, *up);
return this;
}

static double crosstab_value(struct crosstab *ptr,unsigned slot)
{
double this;

if (slot >= ptr->msize) this = 0; // ptr->total.sum ? 0.1/ptr->total.sum : 0.0;
else this = ptr->score * ptr->scores[slot] ;
/* else this =  ptr->scores[slot] * ptr->total.sum * (double) ptr->table[slot].payload.uniq ; */

/* return log(1/(1- this)) ; */
return this;
}

	/* find the slot corresponding to num.
	** if num is not found in the hashtable: allocate a new slot
	** , initialise it, and put num into it.
	*/
static unsigned int cross_find_slot(struct crosstab *ptr,unsigned int num)
{
unsigned int slot, *up;

	/* search hashtable to find element */
up = crosstab_hnd(ptr, num);
slot = *up;
if (slot != IDX_NIL) return slot;

slot = cross_alloc_slot(ptr);
#if SHOW_CALLS
fprintf(stderr, "Find_slot(%u) alloced %u\n", num, slot);
#endif
ptr->table[slot].hash.key = num;
	/* REsearch hashtable because array has been realloced */
up = crosstab_hnd(ptr, num);
*up = slot;
return slot;
}

static unsigned int cross_alloc_slot(struct crosstab *ptr)
{
unsigned int slot = IDX_NIL;

for (slot = ptr->freelist ; slot == IDX_NIL; slot = ptr->freelist) {
	crosstab_reduce( ptr, ptr->msize - sqrt(ptr->msize) );
	}

if (slot != IDX_NIL) {
	ptr->freelist = ptr->table[slot].hash.link;
	ptr->table[slot].hash.link = IDX_NIL;
	}
return slot;
}

	/* remove one "slot" from the crosstable.
	** substract all it's values from the row/columns totals
	** from the grand total, 
	** set it's cell and row/column totals to zero.
	** Dont touch the key or linked list yet; only the payload!
	*/
static void cross_wipe_slot(struct crosstab *ptr,unsigned int slot)
{
unsigned int xy,zzz;

#if SHOW_CALLS
fprintf(stderr, "wipe_slot(%u->%u)\n", slot, ptr->table[slot].hash.key );
#endif
if (ptr->table[slot].hash.key == IDX_NIL ) return;
	/* grand total */
ptr->total.sum -= ptr->table[slot].payload.sum;
	/* the row/columns totals for all indices (including ourself) */
for (xy=0; xy < ptr->msize; xy++ ) {
	if (ptr->table[xy].hash.key == IDX_NIL ) continue;
	zzz = XY2ZZ(slot,xy);
	if (ptr->matrix[zzz] > 0) {
		ptr->table[xy].payload.sum -= ptr->matrix[zzz];
		ptr->matrix[zzz] = 0;
		ptr->total.uniq -= 1;
		ptr->table[xy].payload.uniq -= 1;
		}
	}

	/* our row/col total */
ptr->table[slot].payload.sum = 0;
ptr->table[slot].payload.uniq = 0;
return ;
}

static void cross_fuzz_slot(struct crosstab *ptr,unsigned int slot)
{
unsigned int xy,zzz;
unsigned pay;

#if (SHOW_CALLS || SHOW_FUZZ )
fprintf(stderr, "fuzz_slot(%u->%u)\n", slot, ptr->table[slot].hash.key );
#endif
if (ptr->table[slot].hash.key == IDX_NIL ) return;

	/* the row/columns totals for all indices (including ourself) */
for (xy=0; xy < ptr->msize; xy++ ) {
	if (ptr->table[xy].hash.key == IDX_NIL ) continue;
	zzz = XY2ZZ(slot,xy);
	if (ptr->matrix[zzz] > 0) {
		// pay = 1+sqrt( ptr->matrix[zzz] );
		pay = urnd( 1+ptr->matrix[zzz] );
#if (SHOW_FUZZ > 1 )
		fprintf(stderr, "[%u,%u] %u - %u\n", slot, xy, ptr->matrix[zzz], pay);
#endif
		if (!pay) continue;
		ptr->total.sum -= pay;
		ptr->table[xy].payload.sum -= pay;
		if (xy != slot) ptr->table[slot].payload.sum -= pay;
		ptr->matrix[zzz] -= pay;
		if (ptr->matrix[zzz] != 0) continue;
		ptr->total.uniq -= 1;
		ptr->table[xy].payload.uniq -= 1;
		if (xy != slot) ptr->table[slot].payload.uniq -= 1;
		}
	}

return ;
}

void crosstab_add_pair(struct crosstab *ptr,unsigned int one, unsigned int two, unsigned int val)
{
unsigned int zzz,xxx,yyy;

#if SHOW_CALLS
fprintf(stderr, "add_pair(%p,%u,%u,%u)\n", (void*) ptr, one, two, val );
#endif
xxx = cross_find_slot(ptr,one); 
yyy = cross_find_slot(ptr,two); 

if (xxx > yyy) { zzz = xxx; xxx = yyy; yyy = zzz; }

zzz = XY2ZZ(xxx,yyy);
#if SHOW_CALLS
fprintf(stderr, "xy2zz(%u,%u) := %u\n", xxx, yyy, zzz);
#endif
if (ptr->matrix[zzz] == 0) {
	ptr->total.uniq += 1;
	ptr->table[xxx].payload.uniq += 1;
	if (xxx != yyy) ptr->table[yyy].payload.uniq += 1;
	}

ptr->matrix[zzz] += val;
ptr->table[xxx].payload.sum += val;
ptr->total.sum += val;
if (yyy != xxx) { ptr->table[yyy].payload.sum += val; }

return;
}

struct crosstab *crosstab_init(unsigned int newsize)
{
struct crosstab *ptr;

#if SHOW_CALLS
fprintf(stderr, "crosstab_init(%u)\n", newsize);
#endif

ptr = malloc (sizeof *ptr);
if (!ptr) return NULL;
ptr->msize = 0;
ptr->freelist = IDX_NIL;

ptr->total.uniq = 0;
ptr->total.sum = 0;
ptr->score = 0.0;
ptr->table = NULL;
ptr->table = NULL;
ptr->index = NULL;
ptr->scores = NULL;
ptr->matrix = NULL;

crosstab_resize (ptr, newsize);
return ptr;
}

void crosstab_free(struct crosstab *ptr)
{
if (!ptr) return;
free (ptr->table);
free (ptr->table);
free (ptr->index);
free (ptr->scores);
free (ptr->matrix);
free (ptr);
}

void crosstab_resize(struct crosstab * ptr, unsigned int newsize)
{
unsigned int slot,oldsize, cpysize;
unsigned int *up;
struct crossrow *oldrow;

#if SHOW_CALLS
fprintf(stderr, "crosstab_init(%u) lusize=%u\n", newsize, LUSIZE(newsize));
#endif

oldsize = ptr->msize;
cpysize = oldsize < newsize ? oldsize : newsize;

oldrow = ptr->table;
ptr->table = malloc (newsize * sizeof *ptr->table);
	/* we must set the correct size, because crosstab_hnd() relies on it */
ptr->msize = newsize;

memcpy (ptr->table, oldrow, cpysize * sizeof *oldrow);
row_format_slots( ptr->table , newsize );
for (slot =0 ; slot < cpysize; slot++) {
	if ( oldrow[slot].hash.key == IDX_NIL) continue;
	ptr->table[slot].hash.key = oldrow[slot].hash.key ;
	up = crosstab_hnd(ptr, oldrow[slot].hash.key );
	*up = slot;
	}
for ( ; slot < newsize; slot++) {
	ptr->table[slot].hash.key = IDX_NIL;
	}
free (oldrow);

	/* find end of freelist */
for (up = &ptr->freelist; *up != IDX_NIL; up = &ptr->table[*up].hash.link) {;}
	/* append new slots to freelist */
for (slot = oldsize; slot < newsize; slot++) {
	*up = slot;
	up = &ptr->table[slot].hash.link;
	}
*up = IDX_NIL;

ptr->table = realloc (ptr->table, newsize * sizeof *ptr->table);
ptr->index = realloc (ptr->index, newsize * sizeof *ptr->index);
ptr->scores = realloc (ptr->scores, newsize * sizeof *ptr->scores);
ptr->matrix = realloc (ptr->matrix, LUSIZE(newsize) * sizeof *ptr->matrix);

	/* initialise the new slots */
for (slot=oldsize; slot < newsize; slot++ ) {
	ptr->index[slot] = slot;
	ptr->scores[slot] = 0.0;
	ptr->table[slot].payload.sum = 0;
	ptr->table[slot].payload.uniq = 0;
	}
for (slot=LUSIZE(oldsize); slot < LUSIZE(newsize); slot++ ) {
	ptr->matrix[slot] = 0;
	}
return ;
}

	/* perform power-iteration and keep the result vector in ->scores.
	** the eigenvalue is put in ptr->score.
	 */
static void crosstab_recalc(struct crosstab * ptr)
{
unsigned slot,iter;
double oldval,frac,limit;

if (!ptr || !ptr->msize) return;

limit = FRAC_LIMIT / (1+sqrt(ptr->total.uniq));
#if SHOW_ITER
	fprintf(stderr, "Cnt=%2u Uniq=%u limit = %6.5f\n" , ptr->total.sum, ptr->total.uniq, limit);
#endif
for (slot=0; slot < ptr->msize; slot++ ) {
	ptr->scores[slot] = (double) 0.5 * ptr->table[slot].payload.sum / ptr->total.sum;
	}
for (iter =0; iter < 100; iter++) {
	oldval = ptr->score;
	ptr->score = iterding (ptr->scores , ptr->matrix, ptr->msize );
	frac = (ptr->score-oldval)/ ptr->score;
#if SHOW_ITER
	fprintf(stderr, "Iter=%2u val=%6.4f %6.5f\n" , iter, ptr->score, frac);
#endif
	if (fabs(frac) <= limit) break;
	}
return;
}

	/* find the weakest elements and put them on the freelist */
void crosstab_reduce(struct crosstab * ptr, unsigned int newsize)
{
unsigned idx,slot;

if (!ptr || newsize >= ptr->msize) return;

	/* Pick a victim: a random slot from idx[0] ... idx[newsize] and eat some of it's meat.
	** we don't bother about the elements at newsize and beyond, because they are almost dead anyway.
	 */
idx = urnd(newsize);
slot = ptr->index[idx] ;
cross_fuzz_slot(ptr,slot);

	/* recalculate the power-iteration */
crosstab_recalc(ptr);

	/* reshuffle the index, such that index[0] ... idx[newsize-1] contain the indexes of the best/worst items */
index_doubles(ptr->index, ptr->scores, ptr->msize);

#if ( SHOW_ITER >= 2)
fprintf(stderr, "NewIdx " );
for (slot=0; slot < ptr->msize; slot++ ) {
	fprintf(stderr, " | %5u ", ptr->index[slot] );
	}
fprintf(stderr, "\nTheVect" );
for (slot=0; slot < ptr->msize; slot++ ) {
	idx = ptr->index[slot];
	fprintf(stderr, " | %6.4f", ptr->scores[idx] );
	}
fprintf(stderr, " | %6.4f\n", ptr->score);
#endif

	/* put everything from idx[newsize] and up on the freelist */
crosstab_reclaim(ptr, newsize);
}

	/* reshuffle the matrix is such a way that the 'best' elements are at the lowest indexes */
void crosstab_repack(struct crosstab * ptr)
{
unsigned int *index_2d;

if (!ptr) return;
	/* do poswer-iteration and reshuffle index */
crosstab_recalc(ptr);
index_doubles(ptr->index, ptr->scores, ptr->msize);

#if (SHOW_ITER >= 2)
{unsigned idx,slot;
fprintf(stderr, "NewIdx " );
for (idx=0; idx < ptr->msize; idx++ ) {
	fprintf(stderr, " | %5u ", ptr->index[idx] );
	}
fprintf(stderr, "\nTheVect" );
for (idx=0; idx < ptr->msize; idx++ ) {
	slot = ptr->index[idx];
	fprintf(stderr, " | %6.4f", ptr->scores[slot] );
	}
fprintf(stderr, " | %6.4f\n", ptr->score);
}
#endif

	/* we need not only permute the 1d elements (ptr->scores, ptr->table)
	** , but also the 2d matrix.
	** The 2d permutation array can be constructed from the 1d version.
	*/
index_2d = malloc (LUSIZE(ptr->msize) * sizeof *index_2d);
index2_2d( index_2d, ptr->index, ptr->msize);

#if (SHOW_PERMUTE >= 2)
fprintf(stderr, "\n2d=%3u ", LUSIZE(ptr->msize) );
for (slot=0; slot < LUSIZE(ptr->msize); slot++ ) {
	fprintf(stderr, " | %5u ", index_2d[slot] );
	}
fprintf(stderr, "\n..\n" );
#endif

permute_unsigned(ptr->matrix, index_2d, LUSIZE(ptr->msize) );

	/* Hack: reuse index2d as a copy of ptr->index.
	** this is needed because permute_doubles() also alters the ptr->index array
	** NOTE: this relies on (LUSIZE > size)
	*/
assert (LUSIZE(ptr->msize)  >= ptr->msize);
memcpy (index_2d, ptr->index, ptr->msize * sizeof *index_2d);
permute_doubles(ptr->scores, index_2d, ptr->msize );

free(index_2d);
permute_rows(ptr->table, ptr->index, ptr->msize );

crosstab_reorder(ptr);
}

static void crosstab_reorder(struct crosstab * ptr)
{
unsigned int idx,slot;
unsigned int *up, *fp;

#if SHOW_CALLS
fprintf(stderr, "Crosstab_reorder(%u)\n", ptr->msize);
#endif


row_format_slots( ptr->table , ptr->msize );
for (idx=slot =0 ; slot < ptr->msize; slot++) {
	if ( ptr->table[slot].hash.key == IDX_NIL) {
#if SHOW_GEHANNUS
		fprintf(stderr, "[isFree %u]", slot);
#endif
		}
	else	{
#if SHOW_GEHANNUS
		fprintf(stderr, "[Keep %u <<-- %u]", idx, slot);
#endif
		up = crosstab_hnd(ptr, ptr->table[slot].hash.key );
		if ( idx != slot) ptr->table[idx].payload = ptr->table[slot].payload;
		*up = idx++;
		}
	}

	/* reset freelist */
ptr->freelist = IDX_NIL;
fp = &ptr->freelist;
	/* append to freelist */
for ( slot = idx ; slot < ptr->msize; slot++) {
#if SHOW_GEHANNUS
	fprintf(stderr, "[AbsAddFree %u]", slot);
#endif
	*fp = slot;
	fp = &ptr->table[slot].hash.link;
	}
/* *fp = IDX_NIL; */

for (slot=0; slot < ptr->msize; slot++) {
	ptr->index[slot] = slot;
	}

return ;
}

static void crosstab_reclaim(struct crosstab * ptr, unsigned int newsize)
{
unsigned int idx,slot,totsize;
unsigned int *up, *fp;

totsize = ptr->msize;
#if SHOW_CALLS
fprintf(stderr, "Crosstab_reclaim(%u) Totsize=%u\n", newsize, totsize);
#endif

	/* find end of freelist */
for(fp = &ptr->freelist; *fp != IDX_NIL; fp = &ptr->table[*fp].hash.link) {
	fprintf(stderr, "{%u}", *fp);
	}

for (idx=newsize; idx < totsize; idx++) {
	slot = ptr->index[idx] ;
	if ( ptr->table[slot].hash.key == IDX_NIL) continue;
#if SHOW_GEHANNUS
	fprintf(stderr, "[WipeFree %u->%u]", idx, slot);
#endif
	up = crosstab_hnd(ptr, ptr->table[slot].hash.key );
	cross_wipe_slot(ptr, slot);
	*up = ptr->table[slot].hash.link;
	ptr->table[slot].hash.link = IDX_NIL;
	ptr->table[slot].hash.key = IDX_NIL;
#if SHOW_GEHANNUS
	fprintf(stderr, "[AddFree %u]", slot);
#endif
	/* add to freelist */
	*fp = slot;
	fp = &ptr->table[slot].hash.link;
	}

return ;
}

static unsigned int *crosstab_hnd(struct crosstab *ptr, unsigned int key)
{
unsigned int *up;

for (up = &ptr->table[key % ptr->msize].hash.head ; *up != IDX_NIL; up = &ptr->table[*up].hash.link) {
	if (ptr->table[*up].hash.key == key) break;
	}
return up;
}

static void row_format_slots(struct crossrow *tab, unsigned int cnt)
{
unsigned int idx;

for (idx=0; idx < cnt; idx++) {
	tab[idx].hash.head = IDX_NIL;
	tab[idx].hash.link = IDX_NIL;
	}
}

void crosstab_print(FILE *fp,struct crosstab *ptr)
{
crosstab_pretty_print(fp, ptr, NULL);
}

void crosstab_pretty_print(FILE *fp, struct crosstab *ptr, size_t (*cnv)(char *buff, unsigned sym) )
{
unsigned int xslot,yslot,xxx,yyy,zzz;
char buff [500];

fprintf(fp, "\nSlot    " );
for (xslot=0; xslot < ptr->msize; xslot++ ) {
	fprintf(fp, "+--[%2u]--", xslot );
	}
fprintf(fp, "\nIndex   " );
for (xslot=0; xslot < ptr->msize; xslot++ ) {
	xxx = ptr->index[xslot];
	fprintf(fp, "+--[%2u]--", xxx );
	}
fprintf(fp, "\nHead    " );
for (xslot=0; xslot < ptr->msize; xslot++ ) {
	xxx = ptr->index[xslot];
	if (ptr->table[xxx].hash.head == IDX_NIL) fprintf(fp, "+--[##]--" );
	else fprintf(fp, "+--[%2u]--", ptr->table[xxx].hash.head );
	}
fprintf(fp, "\nLink=%02u ", ptr->freelist%100 );
for (xslot=0; xslot < ptr->msize; xslot++ ) {
	xxx = ptr->index[xslot];
	if (ptr->table[xxx].hash.link == IDX_NIL) fprintf(fp, "+--[__]--" );
	else fprintf(fp, "+--[%2u]--", ptr->table[xxx].hash.link );
	}
fprintf(fp, "\nIndex   " );
for (xslot=0; xslot < ptr->msize; xslot++ ) {
	xxx = ptr->index[xslot];
	fprintf(fp, "+--[%2u]--", xxx );
	}
fprintf(fp, "\n" );
for (yslot=0; yslot < ptr->msize; yslot++ ) {
	yyy = ptr->index[yslot];
	if (ptr->table[yyy].hash.key == IDX_NIL) fprintf(fp, " *free* |" );
	else fprintf(fp, " %6u |", ptr->table[yyy].hash.key );
	for (xslot=0; xslot <= yslot; xslot++ ) {
		xxx = ptr->index[xslot];
		zzz = XY2ZZ(xxx,yyy);
		fprintf(fp, "%7u |", ptr->matrix[zzz]);
		}
	if (cnv) cnv(buff, ptr->table[yyy].hash.key );
	else buff[0] = 0;
	fprintf(fp, "--------+ %s\n", buff );
	}
fprintf(fp, "--------" ); for (xslot=0; xslot < ptr->msize; xslot++ ) { fprintf(fp, "+--------" ); } fprintf(fp, "\n");

fprintf(fp, "Key     " );
for (xslot=0; xslot < ptr->msize; xslot++ ) {
	xxx = ptr->index[xslot];
	if (ptr->table[xxx].hash.key == IDX_NIL) fprintf(fp, "| *free* " );
	else fprintf(fp, "| %6u ", ptr->table[xxx].hash.key );
	}
fprintf(fp, "|\n--------" ); for (xslot=0; xslot < ptr->msize; xslot++ ) { fprintf(fp, "+--------" ); } fprintf(fp, "+\n");

fprintf(fp, "Cnt    " );
for (xslot=0; xslot < ptr->msize; xslot++ ) {
	xxx = ptr->index[xslot];
	fprintf(fp, " |%7u", ptr->table[xxx].payload.sum );
	}
fprintf(fp, " |%7u\n", ptr->total.sum );

fprintf(fp, "Uniq   " );
for (xslot=0; xslot < ptr->msize; xslot++ ) {
	xxx = ptr->index[xslot];
	fprintf(fp, " |%7u", ptr->table[xxx].payload.uniq );
	}
fprintf(fp, " |%7u\n", ptr->total.uniq );
fprintf(fp, "--------" ); for (xslot=0; xslot < ptr->msize; xslot++ ) { fprintf(fp, "+--------" ); } fprintf(fp, "+\n");
fprintf(fp, " Orig  " );
for (xslot=0; xslot < ptr->msize; xslot++ ) {
	xxx = ptr->index[xslot];
	ptr->scores[xxx] = (double) 0.5 * ptr->table[xxx].payload.sum / ptr->total.sum;
	fprintf(fp, " | %6.4f", ptr->scores[xxx] );
	}
fprintf(fp, " | %6.4f\n", ptr->score);
#if 1
	{
unsigned int iter;

for (iter =0; iter < 10; iter++) {
	ptr->score = iterding (ptr->scores , ptr->matrix, ptr->msize );
	fprintf(fp, "Iter=%2u", iter );
		for (xslot=0; xslot < ptr->msize; xslot++ ) {
			xxx = ptr->index[xslot];
			fprintf(fp, " | %6.4f", ptr->scores[xxx] );
		}
	fprintf(fp, " | %6.4f\n", ptr->score);
	}
index_doubles(ptr->index, ptr->scores, ptr->msize);
fprintf(fp, " Index " );
for (xslot=0; xslot < ptr->msize; xslot++ ) {
	fprintf(fp, " | %5u ", ptr->index[xslot] );
	}
fprintf(fp, "\n" );
}
#endif

}

void crosstab_show(FILE *fp, struct crosstab *ptr, size_t (*cnv)(char *buff, unsigned sym) )
{
unsigned int slot,idx;
double value;
char buff [500];

	/* do poswer-iteration and reshuffle index */
crosstab_recalc(ptr);
index_doubles(ptr->index, ptr->scores, ptr->msize);

fprintf(fp, "\n[%4u]:        |%6u/%3u| %6.3f | weight |\n"
	, ptr->freelist!=IDX_NIL? ptr->freelist:9999, ptr->total.sum,ptr->total.uniq,  ptr->score );
fprintf(fp, "------|--------+----------+---------+--------+\n" );
for (idx=0; idx < ptr->msize; idx++ ) {
	slot = ptr->index[idx];
	value = crosstab_value(ptr,slot);
	fprintf(fp, "%2u  %2u|", idx, slot );
	if (ptr->table[slot].hash.key == IDX_NIL) fprintf(fp, " <free> |" );
	else fprintf(fp, " %6u |", ptr->table[slot].hash.key );
	fprintf(fp, "%6u/%2u | %6.5f | %6.4f |"
		, ptr->table[slot].payload.sum, ptr->table[slot].payload.uniq
		, (double) ptr->scores[slot], (double) value );

	if (ptr->table[slot].hash.key != IDX_NIL) {
		if (cnv) cnv(buff, ptr->table[slot].hash.key );
		else get_label(buff, ptr->table[slot].hash.key );
		}
	else buff[0] = 0;
	fprintf(fp, "%s\n", buff );
	}
crosstab_bin_dump(ptr);
}

double iterding(double *vec, unsigned int *mx, unsigned int cnt)
{
unsigned int i,j,zz;
double *tmp, sum;

tmp = malloc (cnt * sizeof *tmp);

for (i=0; i < cnt; i++) {
	tmp[i] = 0;
	}
sum = 0;
for (i=0; i < cnt; i++) {
	for (j=0; j < cnt; j++) {
		zz = XY2ZZ(i, j) ;
		tmp [ i ] += vec [ j ] * mx [ zz ];
		}
	sum += tmp [ i ];
	}
for (i=0; i < cnt; i++) {
	vec [ i ] = tmp[ i ] / sum;
	}
free (tmp);
return sum;
}

static double * anchor_double=NULL;
static int cmp_ranked_double(const void *l, const void *r)
{
unsigned const *ul = l;
unsigned const *ur = r;

if (anchor_double[*ul] > anchor_double[*ur] ) return -3;
else if (anchor_double[*ul] < anchor_double[*ur] ) return 3;
else if (*ul > *ur ) return 2;
else if (*ul < *ur ) return -2;
// else if (ul > ur ) return 1;
// else if (ul < ur ) return -1;
else return 0;
}

static void index_doubles( unsigned *index, double *values, unsigned cnt)
{
/* unsigned idx;
for (idx = 0; idx < cnt; idx++) { index[idx] = idx; } */

anchor_double= values;
qsort (index, cnt, sizeof index[0], cmp_ranked_double);
}

/* Eof */
static void index2_2d( unsigned *target, unsigned *index, unsigned cnt)
{
unsigned x_dst,y_dst,x_src,y_src,z_dst,z_src;

for (y_dst = 0; y_dst < cnt; y_dst++) {
	for (x_dst = 0; x_dst <= y_dst; x_dst++) {
		x_src= index[x_dst];
		y_src= index[y_dst];
		z_dst = XY2ZZ(x_dst,y_dst);
		z_src = XY2ZZ(x_src,y_src);
#if SHOW_INDEXES
		fprintf(stderr, "[dst=(%u,%u) src=(%u,%u), [%u] <<-- %u]\n", x_dst, y_dst, x_src, y_src, z_dst, z_src);
#endif
		target [z_dst] = z_src;
		}
	}
}

static unsigned permute_unsigned( unsigned *values, unsigned *index, unsigned cnt)
{
unsigned start, dst, src, count;
unsigned save;

for (count=start = 0 ; start < cnt; start++) {
	if ( index[start] == start) { 
#if SHOW_PERMUTE
		fprintf(stderr, "[Skip %u]", start); 
#endif
		continue; }
	save = values[start];
#if SHOW_PERMUTE
	fprintf(stderr, "\n[UnsignedAnchor %u]", start);
#endif
	for (dst = start;  ; dst = src) {
		count++;
		src = index[ dst ] ;
		if (src == start) break;
		if (src == dst) break; /* Huh ? */
#if SHOW_PERMUTE
		fprintf(stderr, "%u <<-- %u\n", dst, src);
#endif
		values[dst] = values[src] ;
		index[dst] = dst;
		}
#if SHOW_PERMUTE
	fprintf(stderr, "## Final %u <<-- start=%u; src=%u\n", dst, start, src);
#endif
	values [ dst ] = save;
	index [ dst ] = dst;
	}
return count;
}

static unsigned permute_doubles( double *values, unsigned *index, unsigned cnt)
{
unsigned start, dst, src, count;
double save;

for (count=start = 0 ; start < cnt; start++) {
	if ( index[start] == start) {
#if SHOW_PERMUTE
		 fprintf(stderr, "[Skip %u]", start); 
#endif
		continue; }
	save = values[start];
#if SHOW_PERMUTE
	fprintf(stderr, "\n[DoubleAnchor %u]", start);
#endif
	for (dst = start;  ; dst = src) {
		count++;
		src = index[ dst ] ;
		if (src == start) break;
		if (src == dst) break; /* Huh ? */
#if SHOW_PERMUTE
		fprintf(stderr, "%u <<-- %u\n", dst, src);
#endif
		values[dst] = values[src] ;
		index[dst] = dst;
		}
#if SHOW_PERMUTE
	fprintf(stderr, "## Final %u <<-- start=%u; src=%u\n", dst, start, src);
#endif
	values [ dst ] = save;
	index [ dst ] = dst;
	}
return count;
}

static unsigned permute_rows( struct crossrow *rows, unsigned *index, unsigned cnt)
{
unsigned start, dst, src, count;
struct crossrow save;

for (start = 0 ; start < cnt; start++) {
	if ( index[start] == start) continue;
	save = rows[start];
#if SHOW_PERMUTE
	fprintf(stderr, "\n[RowAnchor %u]", start);
#endif
	for (dst = start;  ; dst = src) {
		count++;
		src = index[ dst ] ;
		if (src == start) break;
		if (src == dst) break; /* Huh ? */
#if SHOW_PERMUTE
		fprintf(stderr, "%u <<-- %u\n", dst, src);
#endif
		rows[dst] = rows[src] ;
		index[dst] = dst;
		}
#if SHOW_PERMUTE
	fprintf(stderr, "## Final %u <<-- %u\n", dst, start);
#endif
	rows [ dst ] = save;
	index [ dst ] = dst;
	}
return count;
}

static void crosstab_bin_dump(struct crosstab *ptr)
{
FILE *fp;
unsigned int idx0,idx1,zzz,cnt;
struct dmprec {
	unsigned key0;
	unsigned key1;
	unsigned uniq;
	unsigned sum;
	} record;

fp = fopen("crosstab.dmp", "a+" );
/* crosstab_recalc(ptr); */
record.key0= IDX_NIL;
record.key1= IDX_NIL;
record.uniq = ptr->total.uniq;
record.sum = ptr->total.sum;
fwrite(&record, sizeof record, 1, fp);

for (idx0=0; idx0 < ptr->msize; idx0++ ) {
	if (ptr->table[idx0].hash.key == IDX_NIL) continue;
	record.key0 = ptr->table[idx0].hash.key;
	record.key1 = IDX_NIL;
	record.uniq = ptr->table[idx0].payload.uniq ;
	record.sum = ptr->table[idx0].payload.sum ;
	fwrite(&record, sizeof record, 1, fp);
	for (cnt=0,idx1=idx0; idx1 < ptr->msize; idx1++ ) {
		if (ptr->table[idx1].hash.key == IDX_NIL) continue;
		record.key1 = ptr->table[idx1].hash.key;
		zzz = XY2ZZ(idx0,idx1);
		if (ptr->matrix[zzz] ==0) continue;
		record.sum = ptr->matrix[zzz];
		record.uniq = cnt++;
		fwrite(&record, sizeof record, 1, fp);
		}
	}
fclose (fp);
}

unsigned crosstab_bin_load(struct crosstab *ptr, char *name)
{
FILE *fp;
unsigned int cnt,sum;
struct dmprec {
	unsigned key0;
	unsigned key1;
	unsigned uniq;
	unsigned sum;
	} master,detail;

fp = fopen(name, "rb" );
/* crosstab_recalc(ptr); */
fprintf(stderr,"Load(%s) :=%p\n", name, (void*) fp);

fread(&master, sizeof master, 1, fp);

for (sum=cnt=0; ;  ) {
	fread(&detail, sizeof detail, 1, fp);
	if (fread(&detail, sizeof detail, 1, fp) <1) break;
	if (detail.key0 == IDX_NIL) continue;
	if (detail.key1 == IDX_NIL) continue;
	if (detail.sum == 0) continue;
	/* if (cnt >= ptr->msize-2) crosstab_resize (ptr, ptr->msize? 2*ptr->msize: 16 ); */
	crosstab_add_pair(ptr, detail.key0,  detail.key1, detail.sum);
	sum += detail.sum;
	cnt += 1;
	}
fclose (fp);
fprintf(stderr,"Master=%u/%u; Sum=%u Cnt=%u\n"
	, master.sum, master.uniq, sum, cnt);
return cnt;
}

unsigned crosstab_labels_load(struct crosstab *dummy, char *name)
{
FILE *fp;
char buff[512];
size_t beg,len;

fp = fopen(name, "r" );
fprintf(stderr,"Names_Load(%s) :=%p\n", name, (void*) fp);

if (labels) while (labels->used) {
	free (labels->tabl[ --labels->used ] );
	}
if (!labels) { labels = malloc (sizeof *labels); labels->size = labels->used = 0; labels->tabl = NULL; }

while (fgets(buff, sizeof buff, fp)) {
	beg = strcspn(buff, "'" );
	if (!beg) continue;
	len = strcspn(buff, "#" );
	if (len && len < beg) continue;
	beg++;
	len = strcspn(buff+beg, "'" );
	buff[beg+len] = 0;
	if (labels->used >= labels->size) {
		size_t new_size = labels->size ? 2 * labels->size : 16;
		labels->tabl = realloc (labels->tabl, new_size * sizeof *labels->tabl);
		labels->size = new_size;
		}
	labels->tabl[ labels->used ] = malloc (1+len);
	memcpy (labels->tabl[ labels->used ] , buff+beg, 1+len);
	labels->used += 1;
	}
fclose (fp);
fprintf(stderr,"Names=%u/%u;\n"
	, (unsigned int) labels->used, (unsigned int) labels->size);
return labels->used;
}

static unsigned get_label (char *dst, unsigned num)
{
if (num >= labels->used) return sprintf(dst, "<%u>", num);
else return sprintf (dst, "'%s'", labels->tabl[ num] );
}

/* Eof */
