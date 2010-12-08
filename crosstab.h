

#define IDX_NIL ((unsigned int)-1)
#define WANT_LRU 0
#define WANT_RESIZE 1

struct rowstats {
	unsigned int uniq;
	unsigned int sum;
	};
struct rowhash {
	unsigned int head;
	unsigned int link;
	unsigned int key;
	};
struct rowlru {
	unsigned int older;
	unsigned int newer;
	};

struct crossrow {
	struct rowhash hash;
#if WANT_LRU
	struct rowlru lru;
#endif
	struct rowstats stats;
	};

struct crosstab {
	unsigned int msize;
	unsigned int freelist;
#if WANT_LRU
	struct	{
		unsigned int oldest;
		unsigned int newest;
		} lru;
#endif
	struct rowstats total;
	double score;
	unsigned int *index;
	double *scores;
	struct crossrow *table;
	unsigned int *matrix;
	};

void crosstab_show(FILE *fp, struct crosstab *ptr );
struct crosstab *crosstab_init(unsigned int newsize);
void crosstab_resize(struct crosstab * ptr, unsigned int newsize);
void crosstab_free(struct crosstab *ptr);
void crosstab_add_pair(struct crosstab *ptr,  unsigned int one, unsigned int two);
void crosstab_print(FILE *fp, struct crosstab *ptr );
