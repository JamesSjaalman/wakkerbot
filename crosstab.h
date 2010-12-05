

#define CROSS_DICT_SIZE 6
#define IDX_NIL ((unsigned)-1)

struct crosscell {
	unsigned sum;
	};

struct crossrow {
	unsigned uniq;
	unsigned sum;
	};
struct crosshash {
	unsigned head;
	unsigned link;
	unsigned key;
	};
struct crosstab {
	unsigned msize;
	unsigned freelist;
	struct	crossrow total;
	struct crosshash *table;
	struct crossrow *edge;
	struct crosscell *cells;
	};

void crosstab_show(FILE *fp, struct crosstab *ptr );
struct crosstab *crosstab_init(struct crosstab *old,  unsigned newsize);
void crosstab_add_pair(struct crosstab *ptr,  unsigned one, unsigned two);
void crosstab_print(FILE *fp, struct crosstab *ptr );

