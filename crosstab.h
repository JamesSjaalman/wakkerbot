
#define IDX_NIL ((unsigned int)-1)
#define WANT_LRU 0

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
	struct rowstats payload;
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
	char meuk[22];
	unsigned int *index;
	double *scores;
	struct crossrow *table;
	unsigned int *matrix;
	};

struct crosstab *crosstab_init(unsigned int newsize);
/* i */ void crosstab_resize(struct crosstab * ptr, unsigned int newsize);
/* z */ void crosstab_reduce(struct crosstab * ptr, unsigned int newsize);
/* s */ void crosstab_repack(struct crosstab * ptr);
void crosstab_free(struct crosstab *ptr);
/* x y */ void crosstab_add_pair(struct crosstab *ptr,  unsigned int one, unsigned int two, unsigned val);
/* p */ void crosstab_print(FILE *fp, struct crosstab *ptr );
/* P */ void crosstab_pretty_print(FILE *fp, struct crosstab *ptr, size_t (*cnv)(char *buff, unsigned sym) );
/* . */ void crosstab_show(FILE *fp, struct crosstab *ptr, size_t (*cnv)(char *buff, unsigned sym) );
/* ? */ double crosstab_ask(struct crosstab * ptr, unsigned sym);
/* g */ unsigned crosstab_get(struct crosstab * ptr, unsigned idx);
/* l */ unsigned crosstab_bin_load(struct crosstab *ptr, char *name);

