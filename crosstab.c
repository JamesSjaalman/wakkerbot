
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>

#include "crosstab.h"

#define COUNTOF(a) (sizeof(a) / sizeof(a)[0])

static void cross_wipe_num(struct crosstab *ptr,unsigned xxx);
static unsigned cross_find_index(struct crosstab *ptr,unsigned num);
static unsigned cross_alloc(struct crosstab *ptr,unsigned num);
static unsigned cross_find_victim(struct crosstab *ptr,unsigned num);
static unsigned *crosstab_hnd(struct crosstab *ptr, unsigned key);
static void crosshash_format_slots(struct crosshash *tab, unsigned cnt);
/* static struct crosstab glob_crosstab; */


static unsigned xy2zz(unsigned x, unsigned y) { return x+((y*(y+1))/2); }
static unsigned sxy2zz(unsigned siz,unsigned x, unsigned y) { return x+((y*(y+1))/2); }


#define zzzzzXY2ZZ(x,y) ((x)+(y)*COUNTOF(glob_crosstab.domain))
#define XY2ZZ(x,y) xy2zz(x,y)
#define LUSIZE(s) ((s*(s+1))/2)

static unsigned cross_find_index(struct crosstab *ptr,unsigned num)
{
unsigned idx, *up;

	/* search hashtable to find element */
up = crosstab_hnd(ptr, num );
if (*up != IDX_NIL) return *up;

idx = cross_alloc(ptr,num);
fprintf(stderr, "Find_index(%u) alloced %u\n", num, idx);
ptr->table[idx].key = num;
*up = idx;
return idx;
}

static unsigned cross_alloc(struct crosstab *ptr,unsigned num)
{
unsigned idx;

if (ptr->freelist != IDX_NIL) {
	idx = ptr->freelist ;
	ptr->freelist = ptr->table[idx].link;
	ptr->table[idx].link = IDX_NIL;
	}
else idx = cross_find_victim(ptr, num);
return idx;
}

static unsigned cross_find_victim(struct crosstab *ptr,unsigned num)
{
unsigned victim,idx;
double val = 1.;

for (idx=victim=0; idx < ptr->msize; idx++ ) {
	unsigned zzz;
	if (ptr->table[idx].key == IDX_NIL ) { victim = idx; break; }
	if (idx == victim) continue;
		/* fixme: some heath indicator needed here */
	zzz = XY2ZZ(idx,idx);
	if (ptr->total.sum == 0 || (double)ptr->edge[idx].sum / ptr->total.sum < val ) {
		val = (ptr->total.sum == 0) ? 0 
		: (double)ptr->edge[idx].sum / ptr->cells[zzz].sum ;
		victim = idx;
		}
	}
if (ptr->table[victim].key != IDX_NIL) cross_wipe_num(ptr, victim);
return victim;
}

/* remove one "index" from the crosstable.
** substract all it's values from the row/columns totals
** from the grand total, 
** set it's cell and row/column totals to zero.
*/
static void cross_wipe_num(struct crosstab *ptr,unsigned num)
{
unsigned yyy,zzz;


fprintf(stderr, "wipenum(%u)\n", num);
	/* grand total */
if (ptr->edge[num].sum) {
	ptr->total.uniq -= 1;
	}
ptr->total.sum -= ptr->edge[num].sum;
	/* the row/columns totals for other indices (including ourself) */
for (yyy=0; yyy < ptr->msize; yyy++ ) {
	if (ptr->table[yyy].key == IDX_NIL ) continue;
	zzz = XY2ZZ(num,yyy);
	if (ptr->cells[zzz].sum > 0) ptr->edge[yyy].uniq -= 1;
	ptr->edge[yyy].sum -= ptr->cells[zzz].sum;
	}

for (yyy=0; yyy < ptr->msize; yyy++ ) {
	if (ptr->table[yyy].key == IDX_NIL ) continue;
	if (yyy == num) continue;
	zzz = XY2ZZ(yyy,num);
	if (ptr->cells[zzz].sum > 0) ptr->edge[yyy].uniq -= 1;
	ptr->edge[yyy].sum -= ptr->cells[zzz].sum;
	}

	/* reset all the cells that use num as a row or column */
for (yyy=0; yyy < ptr->msize; yyy++ ) {
	if (ptr->table[yyy].key == IDX_NIL ) continue;
	zzz = XY2ZZ(num,yyy);
	ptr->cells[zzz].sum = 0;
	}
for (yyy=0; yyy < ptr->msize; yyy++ ) {
	if (ptr->table[yyy].key == IDX_NIL ) continue;
	zzz = XY2ZZ(yyy,num);
	ptr->cells[zzz].sum = 0;
	}

	/* our row/col total */
ptr->edge[num].sum = 0;
ptr->edge[num].uniq = 0;
ptr->table[num].key = IDX_NIL;
return ;
}

void crosstab_add_pair(struct crosstab *ptr,unsigned one, unsigned two)
{
unsigned zzz,xxx,yyy;

xxx = cross_find_index(ptr,one); 
yyy = cross_find_index(ptr,two); 

if (xxx > yyy) { zzz = xxx; xxx = yyy; yyy = zzz; }

zzz = XY2ZZ(xxx,yyy);
fprintf(stderr, "xy2zz(%u,%u) := %u\n", xxx, yyy, zzz);
if (ptr->cells[zzz].sum == 0) {
	ptr->total.uniq += 1;
	ptr->edge[xxx].uniq += 1;
	if (xxx != yyy) ptr->edge[yyy].uniq += 1;
	}
ptr->cells[zzz].sum += 1;
ptr->edge[xxx].sum += 1;
if (xxx != yyy) ptr->edge[yyy].sum += 1;
ptr->total.sum += 1;

return;
}

struct crosstab *crosstab_init(struct crosstab * ptr, unsigned newsize)
{
unsigned idx,oldsize;
unsigned *up;
struct crosshash *sav;

fprintf(stderr, "cronsstab_init(%u) lusize=%u\n", newsize, LUSIZE(newsize));

if (!ptr) {
	ptr = malloc (sizeof *ptr);
	ptr->msize = 0;

	ptr->freelist = IDX_NIL;
	ptr->total.uniq = 0;
	ptr->total.sum = 0;
	ptr->table = NULL;
	ptr->edge = NULL;
	ptr->cells = NULL;
	}
oldsize = ptr->msize;
ptr->msize = newsize;

sav = ptr->table;
ptr->table = malloc (newsize * sizeof *ptr->table);
memcpy (ptr->table, sav, oldsize * sizeof *sav);
crosshash_format_slots( ptr->table , newsize );
if (sav) for (idx =0 ; idx < oldsize; idx++) {
	if ( sav[idx].key== IDX_NIL) continue;
	up = crosstab_hnd(ptr, sav[idx].key );
	*up = idx;
	}
free (sav);
	/* append to freelist */
for (up = &ptr->freelist; *up != IDX_NIL; up = &ptr->table[*up].link) {;}

for (idx = oldsize; idx < newsize; idx++) {
	*up = idx;
	up = &ptr->table[idx].link;
	}
*up = IDX_NIL;

ptr->edge = realloc (ptr->edge, newsize * sizeof *ptr->edge);
ptr->cells = realloc (ptr->cells, LUSIZE(newsize) * sizeof *ptr->cells);

for (idx=oldsize; idx < newsize; idx++ ) {
	ptr->edge[idx].uniq = 0;
	ptr->edge[idx].sum = 0;
	}
for (idx=LUSIZE(oldsize); idx < LUSIZE(newsize); idx++ ) {
	ptr->cells[idx].sum = 0;
	}
return ptr;
}

static unsigned *crosstab_hnd(struct crosstab *ptr, unsigned key)
{
unsigned *up;

for (up = &ptr->table[key % ptr->msize].head ; *up != IDX_NIL; up = &ptr->table[*up].link) {
	if (ptr->table[*up].key == key) break;
	}
return up;
}

static void crosshash_format_slots(struct crosshash *tab, unsigned cnt)
{
unsigned idx;

for (idx=0; idx < cnt; idx++) {
	tab[idx].head = IDX_NIL;
	tab[idx].link = IDX_NIL;
	tab[idx].key = IDX_NIL;
	}
}


void crosstab_print(FILE *fp,struct crosstab *ptr)
{
unsigned xxx,yyy,zzz;


fprintf(fp, "\n        " );
for (xxx=0; xxx < ptr->msize; xxx++ ) {
	if (ptr->table[xxx].key == IDX_NIL) fprintf(fp, "+--[  ]--" );
	else fprintf(fp, "+--[%2u]--", ptr->table[xxx].key );
	}
fprintf(fp, "\n" );
for (yyy=0; yyy < ptr->msize; yyy++ ) {
	if (ptr->table[yyy].key == IDX_NIL) fprintf(fp, "[  ]    |" );
	else fprintf(fp, "[%2u]    |", ptr->table[yyy].key );
	for (xxx=0; xxx < ptr->msize; xxx++ ) {
		if (xxx > yyy) {fprintf(fp, "--------+" ); break; }
		zzz = XY2ZZ(xxx,yyy);
		fprintf(fp, "%7u |", ptr->cells[zzz].sum);
		}
	fprintf(fp, "\n");
	}
fprintf(fp, "-------" );
for (xxx=0; xxx < ptr->msize; xxx++ ) {
	fprintf(fp, " +-------" );
	}
fprintf(fp, "\n");
fprintf(fp, "%3u/%3u" , ptr->total.sum , ptr->total.uniq );
for (xxx=0; xxx < ptr->msize; xxx++ ) {
	fprintf(fp, " |%3u/%3u", ptr->edge[xxx].sum, ptr->edge[xxx].uniq );
	}
fprintf(fp, "\n");
}

/* Eof */
