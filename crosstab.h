#ifndef CROSSTAB_H
#define CROSSTAB_H 1

#define IDX_NIL ((unsigned int)-1)

struct rowstats {
	unsigned int uniq;
	unsigned int sum;
	};
	/* hashtable, combined with array of head pointers */
struct rowhash {
	unsigned int head;
	unsigned int link;
	unsigned int key;
	};

struct crossrow {
	struct rowhash hash;
	struct rowstats payload;
	};

	/*
	** Since the vicinity matrix is symmetric, we need only store N*(N+1)/2 elements
	*/
struct crosstab {
#if WANT_FIX
	unsigned nfixed;
#else
#define nfixed 0
#endif
	unsigned int msize;
	unsigned int freelist;	/* points to LL of free cells (in table[] */
	struct rowstats total;	/* the main score (counts) */
	double score;		/* The main score (eigenvalue) */
	/* char meuk[22]; */
	unsigned int *index;	/* the numerical offsets into table[] , in descending order */
	double *scores;		/* The resulting scores of the words */
	struct crossrow *table;	/* hashtable+payload[msize] */
	unsigned int *matrix;	/* msize*(msize+1)/2 crosstable */
	};

struct crosstab *crosstab_init(unsigned int newsize);
void crosstab_free(struct crosstab *ptr);

/* V---- the command-letter for cross-driv */
/* i */ void crosstab_resize(struct crosstab * ptr, unsigned int newsize);

        /* find the weakest elements and put them on the freelist */
/* z */ void crosstab_reduce(struct crosstab * ptr, unsigned int newsize);
/* s */ void crosstab_repack(struct crosstab * ptr);
/* x y */ void crosstab_add_pair(struct crosstab *ptr,  unsigned int one, unsigned int two, unsigned val);

	/* ------------------------- */
/* p */ void crosstab_print(FILE *fp, struct crosstab *ptr );
	/* Uses callback functions to format the character content+weight of the token given its numeric value */
/* P */ void crosstab_pretty_print(FILE *fp, struct crosstab *ptr , size_t (*cnv)(char *buff, unsigned sym) );
/* . */ void crosstab_show(FILE *fp, struct crosstab *ptr
	, size_t (*cnv)(char *buff, unsigned sym)
	, double (*symval)(unsigned sym) );
	/* get token -->> value */
/* ? */ double crosstab_ask(struct crosstab * ptr, unsigned sym);
	/* get index -->> value (for iteraterators */
/* g */ unsigned crosstab_get(struct crosstab * ptr, unsigned idx);

/* l */ unsigned crosstab_bin_load(struct crosstab *ptr, char *name);
/* n */ unsigned crosstab_labels_load(struct crosstab *dummy, char *name);

#endif /* CROSSTAB_H */
