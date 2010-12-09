
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include <math.h>

#include "crosstab.h"

#define COUNTOF(a) (sizeof(a) / sizeof(a)[0])

static void cross_wipe_num(struct crosstab *ptr,unsigned int slot);
static unsigned int cross_find_slot(struct crosstab *ptr,unsigned int num);
static unsigned int cross_alloc_slot(struct crosstab *ptr);
static unsigned int cross_find_victim(struct crosstab *ptr);
static unsigned int *crosstab_hnd(struct crosstab *ptr, unsigned int key);
static void row_format_slots(struct crossrow *tab, unsigned int cnt);
static void crosstab_rebuild(struct crosstab * ptr, unsigned int newsize);
/* static struct crosstab glob_crosstab; */
static double calcterm(double total, double this);
double iterding(double *vec, unsigned int *mx, unsigned int cnt);
static void index_doubles( unsigned *index, double *values, unsigned cnt);
static int cmp_ranked_double(const void *l, const void *r);
static void index2_2d( unsigned *target, unsigned *index, unsigned cnt);
static unsigned permute_doubles( double *values, unsigned *index, unsigned cnt);
static unsigned permute_unsigned( unsigned *values, unsigned *index, unsigned cnt);
static unsigned permute_rows( struct crossrow *rows, unsigned *index, unsigned cnt);


static unsigned int xy2zz(unsigned int x, unsigned int y) { 
if (x > y) 
	return y+(x*(x+1))/2; 
else	return x+(y*(y+1))/2; 
}
	/* The index of a cell in our LU matrix, given its X,Y coordinates */
#define XY2ZZ(x,y) xy2zz((x),(y))
	/* the amount of cells we need for an LU matrix */
#define LUSIZE(s) (((s)*((s)+1))/2)

static unsigned int cross_find_slot(struct crosstab *ptr,unsigned int num)
{
unsigned int idx, *up;

	/* search hashtable to find element */
up = crosstab_hnd(ptr, num);
if (*up != IDX_NIL) return *up;

idx = cross_alloc_slot(ptr);
fprintf(stderr, "Find_slot(%u) alloced %u\n", num, idx);
ptr->table[idx].hash.key = num;
	/* REsearch hashtable because array has been realloced */
up = crosstab_hnd(ptr, num);
*up = idx;
return idx;
}

static unsigned int cross_alloc_slot(struct crosstab *ptr)
{
unsigned int idx = IDX_NIL;

again:
idx = ptr->freelist ;
if (idx != IDX_NIL) {
	ptr->freelist = ptr->table[idx].hash.link;
	ptr->table[idx].hash.link = IDX_NIL;
	}
#if WANT_RESIZE
if (idx == IDX_NIL) {
	crosstab_resize( ptr, ptr->msize *2);
	goto again;
	}
#endif
if (idx == IDX_NIL) {
	idx = cross_find_victim(ptr);
	}
return idx;
}

static unsigned int cross_find_victim(struct crosstab *ptr)
{
unsigned int victim,idx, *up;
double val = 1.;

for (idx=victim=0; idx < ptr->msize; idx++ ) {
	unsigned int zzz;
	if (ptr->table[idx].hash.key == IDX_NIL ) { victim = idx; break; }
	if (idx == victim) continue;
		/* fixme: some health indicator needed here */
	zzz = XY2ZZ(idx,idx);
	if (ptr->total.sum == 0 || (double)ptr->table[idx].stats.sum / ptr->total.sum < val ) {
		val = (ptr->total.sum == 0) ? 0 
		: (double)ptr->table[idx].stats.sum / ptr->matrix[zzz] ;
		victim = idx;
		}
	}
if (ptr->table[victim].hash.key != IDX_NIL) cross_wipe_num(ptr, victim);
up = crosstab_hnd(ptr, ptr->table[victim].hash.key );
*up = IDX_NIL;

return victim;
}

/* remove one "slot" from the crosstable.
** substract all it's values from the row/columns totals
** from the grand total, 
** set it's cell and row/column totals to zero.
*/
static void cross_wipe_num(struct crosstab *ptr,unsigned int slot)
{
unsigned int xy,zzz;


fprintf(stderr, "wipenum(%u->%u)\n", slot, ptr->table[slot].hash.key );
	/* grand total */
if (ptr->table[slot].stats.sum) {
	ptr->total.uniq -= 1;
	ptr->total.sum -= ptr->table[slot].stats.sum;
	}
	/* the row/columns totals for other indices (including ourself) */
for (xy=0; xy < ptr->msize; xy++ ) {
	if (ptr->table[xy].hash.key == IDX_NIL ) continue;
	zzz = XY2ZZ(slot,xy);
	if (ptr->matrix[zzz] > 0) {
		if (xy != slot); ptr->table[xy].stats.uniq -= 1;
		ptr->table[xy].stats.sum -= ptr->matrix[zzz];
		}
	}

	/* reset all the cells that use idx as a row or column */
for (xy=0; xy < ptr->msize; xy++ ) {
	if (ptr->table[xy].hash.key == IDX_NIL ) continue;
	zzz = XY2ZZ(slot,xy);
	ptr->matrix[zzz] = 0;
	}

	/* our row/col total */
ptr->table[slot].stats.sum = 0;
ptr->table[slot].stats.uniq = 0;
ptr->table[slot].hash.key = IDX_NIL;
return ;
}

void crosstab_add_pair(struct crosstab *ptr,unsigned int one, unsigned int two)
{
unsigned int zzz,xxx,yyy;

xxx = cross_find_slot(ptr,one); 
yyy = cross_find_slot(ptr,two); 

if (xxx > yyy) { zzz = xxx; xxx = yyy; yyy = zzz; }

zzz = XY2ZZ(xxx,yyy);
fprintf(stderr, "xy2zz(%u,%u) := %u\n", xxx, yyy, zzz);
if (ptr->matrix[zzz] == 0) {
	ptr->total.uniq += 1;
	ptr->table[xxx].stats.uniq += 1;
	if (xxx != yyy) {
		ptr->table[yyy].stats.uniq += 1;
		}
	}

ptr->matrix[zzz] += 1;
ptr->table[xxx].stats.sum += 1;
ptr->total.sum += 1;

if (yyy != xxx) {
	ptr->table[yyy].stats.sum += 1;
	}

return;
}

struct crosstab *crosstab_init(unsigned int newsize)
{
struct crosstab *ptr;

fprintf(stderr, "cronsstab_init(%u)\n", newsize);

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
unsigned int idx,oldsize, cpysize;
unsigned int *up;
struct crossrow *oldrow;

fprintf(stderr, "cronsstab_init(%u) lusize=%u\n", newsize, LUSIZE(newsize));

oldsize = ptr->msize;
cpysize = oldsize < newsize ? oldsize : newsize;

oldrow = ptr->table;
ptr->table = malloc (newsize * sizeof *ptr->table);
	/* we must set the correct size, because crosstab_hnd() relies on it */
ptr->msize = newsize;

memcpy (ptr->table, oldrow, cpysize * sizeof *oldrow);
row_format_slots( ptr->table , newsize );
for (idx =0 ; idx < cpysize; idx++) {
	if ( oldrow[idx].hash.key == IDX_NIL) continue;
	ptr->table[idx].hash.key = oldrow[idx].hash.key ;
	up = crosstab_hnd(ptr, oldrow[idx].hash.key );
	*up = idx;
	}
for ( ; idx < newsize; idx++) {
	ptr->table[idx].hash.key = IDX_NIL;
	}
free (oldrow);

	/* find end of freelist */
for (up = &ptr->freelist; *up != IDX_NIL; up = &ptr->table[*up].hash.link) {;}
	/* append to freelist */
for (idx = oldsize; idx < newsize; idx++) {
	*up = idx;
	up = &ptr->table[idx].hash.link;
	}
*up = IDX_NIL;

ptr->table = realloc (ptr->table, newsize * sizeof *ptr->table);
ptr->index = realloc (ptr->index, newsize * sizeof *ptr->index);
ptr->scores = realloc (ptr->scores, newsize * sizeof *ptr->scores);
ptr->matrix = realloc (ptr->matrix, LUSIZE(newsize) * sizeof *ptr->matrix);

for (idx=oldsize; idx < newsize; idx++ ) {
	ptr->index[idx] = idx;
	ptr->scores[idx] = 0.0;
	ptr->table[idx].stats.sum = 0;
	ptr->table[idx].stats.uniq = 0;
	/* ptr->table[idx].term = 0.0; */
	}
for (idx=LUSIZE(oldsize); idx < LUSIZE(newsize); idx++ ) {
	ptr->matrix[idx] = 0;
	}
return ;
}

void crosstab_reduce(struct crosstab * ptr, unsigned int newsize)
{
unsigned idx, iter;
unsigned int *index_2d;
double oldval,frac;

if (!ptr || newsize >= ptr->msize) return;

for (idx=0; idx < ptr->msize; idx++ ) {
	ptr->scores[idx] = (double) 0.5 * ptr->table[idx].stats.sum / ptr->total.sum;
	}
for (iter =0; iter < 100; iter++) {
	oldval = ptr->score;
	ptr->score = iterding (ptr->scores , ptr->matrix, ptr->msize );
	frac = (ptr->score-oldval)/ ptr->score;
	fprintf(stderr, "Iter=%2u val=%6.4f (%6.5f)\n"
		, iter, ptr->score, frac
		);
	if (fabs(frac) <= 0.001) break;
	}

index_doubles(ptr->index, ptr->scores, ptr->msize);
fprintf(stderr, "NewIdx " );
for (idx=0; idx < ptr->msize; idx++ ) {
	fprintf(stderr, " | %5u ", ptr->index[idx] );
	}
fprintf(stderr, "\nTheVect" );
for (idx=0; idx < ptr->msize; idx++ ) {
	iter = ptr->index[idx];
	fprintf(stderr, " | %6.4f", ptr->scores[iter] );
	}
fprintf(stderr, " | %6.4f\n", ptr->score);

#if 0
index_2d = malloc (LUSIZE(ptr->msize) * sizeof *index_2d);
index2_2d( index_2d, ptr->index, ptr->msize);

fprintf(stderr, "\n2d=%3u ", LUSIZE(ptr->msize) );
for (idx=0; idx < LUSIZE(ptr->msize); idx++ ) {
	fprintf(stderr, " | %5u ", index_2d[idx] );
	}
fprintf(stderr, "\n..\n" );
permute_unsigned(ptr->matrix, index_2d, LUSIZE(ptr->msize) );
free(index_2d);
iter = permute_rows(ptr->table, ptr->index, ptr->msize );
#endif
crosstab_rebuild(ptr, newsize);

}

static void crosstab_rebuild(struct crosstab * ptr, unsigned int newsize)
{
unsigned int idx,slot,totsize;
unsigned int *up, *fp;

totsize = ptr->msize;
fprintf(stderr, "Crosstab_rehash(%u) Totsize=%u\n", newsize, totsize);

	/* reset freelist */
#if 0
ptr->freelist = IDX_NIL;
fp = &ptr->freelist;

row_format_slots( ptr->table , totsize );
for (slot =0 ; slot < totsize; slot++) {
	if ( ptr->table[slot].hash.key == IDX_NIL) {
		fprintf(stderr, "[isFree %u]", slot);
		*fp = slot;
		fp = &ptr->table[slot].hash.link;
		}
	else	{
		fprintf(stderr, "[Keep %u]", slot);
		up = crosstab_hnd(ptr, ptr->table[slot].hash.key );
		*up = slot;
		}
	}

	/* append to freelist */
for (slot=newsize; slot < totsize; slot++) {
	if ( ptr->table[slot].hash.key == IDX_NIL) continue;
	fprintf(stderr, "[DontWipeFree %u]", slot);
	up = crosstab_hnd(ptr, ptr->table[slot].hash.key );
	cross_wipe_num(ptr, slot);
	*up = ptr->table[slot].hash.link;
	fprintf(stderr, "[AddFree %u]", slot);
	*fp = slot;
	fp = &ptr->table[slot].hash.link;
	}
/* *fp = IDX_NIL; */

for (slot=0; slot < totsize; slot++) {
	ptr->index[slot] = slot;
	}
#else

	/* add to freelist */
for(fp = &ptr->freelist; *fp != IDX_NIL; fp = &ptr->table[slot].hash.link) {;}

for (slot=newsize; slot < totsize; slot++) {
	idx = ptr->index[slot] ;
	if ( ptr->table[idx].hash.key == IDX_NIL) continue;
	fprintf(stderr, "[WipeFree %u->%u]", slot, idx);
	up = crosstab_hnd(ptr, ptr->table[idx].hash.key );
	cross_wipe_num(ptr, idx);
	*up = ptr->table[idx].hash.link;
	fprintf(stderr, "[AddFree %u]", idx);
	ptr->table[idx].hash.link = IDX_NIL;
	*fp = idx;
	fp = &ptr->table[idx].hash.link;
	}
#endif

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
unsigned int xslot,yslot,xxx,yyy,zzz;


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
	fprintf(fp, "--------+\n" );
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
	fprintf(fp, " |%7u", ptr->table[xxx].stats.sum );
	}
fprintf(fp, " |%7u\n", ptr->total.sum );

fprintf(fp, "Uniq   " );
for (xslot=0; xslot < ptr->msize; xslot++ ) {
	xxx = ptr->index[xslot];
	fprintf(fp, " |%7u", ptr->table[xxx].stats.uniq );
	}
fprintf(fp, " |%7u\n", ptr->total.uniq );
fprintf(fp, "--------" ); for (xslot=0; xslot < ptr->msize; xslot++ ) { fprintf(fp, "+--------" ); } fprintf(fp, "+\n");
fprintf(fp, " Orig  " );
for (xslot=0; xslot < ptr->msize; xslot++ ) {
	xxx = ptr->index[xslot];
	ptr->scores[xxx] = (double) 0.5 * ptr->table[xxx].stats.sum / ptr->total.sum;
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
		fprintf(stderr, "[dst=(%u,%u) src=(%u,%u), [%u] <<-- %u]\n"
		, x_dst, y_dst, x_src, y_src
		, z_dst, z_src);
		target [z_dst] = z_src;
		}
	}
}

static unsigned permute_unsigned( unsigned *values, unsigned *index, unsigned cnt)
{
unsigned start, dst, src, count;
unsigned save;

for (count=start = 0 ; start < cnt; start++) {
	if ( index[start] == start) { fprintf(stderr, "[Skip %u]", start); continue; }
	save = values[start];
	fprintf(stderr, "\n[UnsignedAnchor %u]", start);
	for (dst = start;  ; dst = src) {
		count++;
		src = index[ dst ] ;
		if (src == start) break;
		if (src == dst) break; /* Huh ? */
		fprintf(stderr, "%u <<-- %u\n", dst, src);
		values[dst] = values[src] ;
		index[dst] = dst;
		}
	fprintf(stderr, "## Final %u <<-- start=%u; src=%u\n", dst, start, src);
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
	if ( index[start] == start) { fprintf(stderr, "[Skip %u]", start); continue; }
	save = values[start];
	fprintf(stderr, "\n[DoubleAnchor %u]", start);
	for (dst = start;  ; dst = src) {
		count++;
		src = index[ dst ] ;
		if (src == start) break;
		if (src == dst) break; /* Huh ? */
		fprintf(stderr, "%u <<-- %u\n", dst, src);
		values[dst] = values[src] ;
		index[dst] = dst;
		}
	fprintf(stderr, "## Final %u <<-- start=%u; src=%u\n", dst, start, src);
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
	fprintf(stderr, "\n[RowAnchor %u]", start);
	for (dst = start;  ; dst = src) {
		count++;
		src = index[ dst ] ;
		if (src == start) break;
		if (src == dst) break; /* Huh ? */
		fprintf(stderr, "%u <<-- %u\n", dst, src);
		rows[dst] = rows[src] ;
		index[dst] = dst;
		}
	fprintf(stderr, "## Final %u <<-- %u\n", dst, start);
	rows [ dst ] = save;
	index [ dst ] = dst;
	}
return count;
}
/* Eof */
#if 0
	{
unsigned int *index;
unsigned int *index_2d;
index = malloc (ptr->msize * sizeof *index);
index_2d = malloc (LUSIZE(ptr->msize) * sizeof *index);

index2_2d( index_2d, index, ptr->msize);

#if 1
fprintf(fp, " Index " );
for (xxx=0; xxx < ptr->msize; xxx++ ) {
	fprintf(fp, " | %5u ", index[xxx] );
	}
fprintf(fp, "\n" );

// xxx = permute_doubles(ptr->scores, index, ptr->msize );
xxx = permute_rows(ptr->table, index, ptr->msize );
if (xxx) crosstab_rebuild(ptr, ptr->msize);

fprintf(fp, "Swap=%2u", xxx );
for (xxx=0; xxx < ptr->msize; xxx++ ) {
	fprintf(fp, " | %6.4f", ptr->scores[xxx] );
	}
fprintf(fp, "|%6.4f\n", ptr->score);

fprintf(fp, " NewIdx" );
for (xxx=0; xxx < ptr->msize; xxx++ ) {
	fprintf(fp, " | %5u ", index[xxx] );
	}
fprintf(fp, "\n" );
#endif

#if 0
permute_doubles(ptr->matrix, index_2d, LUSIZE(ptr->msize) );
index_doubles(index, ptr->scores, ptr->msize);
fprintf(fp, " Idx_2d" );
permute_doubles(ptr->scores, index, ptr->msize);

fprintf(fp, "Swapped" );
	for (xxx=0; xxx < ptr->msize; xxx++ ) {
		fprintf(fp, " | %6.4f", ptr->scores[xxx] );
	}
fprintf(fp, "|%6.4f\n", ptr->score);
fprintf(fp, " Idx_2d" );
for (xxx=0; xxx < LUSIZE(ptr->msize); xxx++ ) {
	fprintf(fp, " | %5u ", index_2d[xxx] );
	}
fprintf(fp, "\n" );

fprintf(fp, " Idx_2d" );
for (xxx=0; xxx < LUSIZE(ptr->msize); xxx++ ) {
	fprintf(fp, " | %5u ", index_2d[xxx] );
	}
fprintf(fp, "\n" );
#endif


free (index);
free (index_2d);
	
	}
#endif
static double calcterm(double total, double this)
{
double frac;

if (this == 0.0) return 0.0;
if (total+this == 0.0) return 0.0;
frac = this / (total+this);
return -frac /** 1/M_LN2 */ * log(frac);
}

