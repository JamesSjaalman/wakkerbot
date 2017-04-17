
/*===========================================================================*/
/*
 *  Copyright (C) 1998 Jason Hutchens
 *
 *  This program is free software; you can redistribute it and/or modify it
 *  under the terms of the GNU General Public License as published by the Free
 *  Software Foundation; either version 2 of the license or (at your option)
 *  any later version.
 *
 *  This program is distributed in the hope that it will be useful, but
 *  WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 *  or FITNESS FOR A PARTICULAR PURPOSE.  See the Gnu Public License for more
 *  details.
 *
 *  You should have received a copy of the GNU General Public License along
 *  with this program; if not, write to the Free Software Foundation, Inc.,
 *  675 Mass Ave, Cambridge, MA 02139, USA.
 */

/*===========================================================================*/

/*
 *		$Id: megahal.c,v 1.10 2004/02/23 11:12:29 lfousse Exp $
 *
 *		File:			megahal.c
 *
 *		Program:		MegaHAL
 *
 *		Purpose:		To simulate a natural language conversation with a psychotic
 *						computer.  This is achieved by learning from the user's
 *						input using a third-order Markov model on the word level.
 *						Words are considered to be sequences of characters separated
 *						by whitespace and punctuation.  Replies are generated
 *						randomly based on a keyword, and they are scored using
 *						measures of surprise.
 *
 *		Author:		Mr. Jason L. Hutchens (http://www.amristar.com.au/~hutch/)
 *
 *		WWW:		http://megahal.sourceforge.net
 *
 *		Compilation Notes
 *		=================
 *
 *		When compiling, be sure to link with the maths library so that the
 *		log() function can be found.
 *
 *		On the Macintosh, add the library SpeechLib to your project.  It is
 *		very important that you set the attributes to Import Weak.  You can
 *		do this by selecting the lib and then use Project Inspector from the
 *		Window menu.
 *
 *		CREDITS
 *		=======
 *
 *		Amiga (AmigaOS)
 *		---------------
 *		Dag Agren (dagren@ra.abo.fi)
 *
 *		DEC (OSF)
 *		---------
 *		Jason Hutchens (hutch@ciips.ee.uwa.edu.au)
 *
 *		Macintosh
 *		---------
 *		Paul Baxter (pbaxter@assistivetech.com)
 *		Doug Turner (dturner@best.com)
 *
 *		PC (Linux)
 *		----------
 *		Jason Hutchens (hutch@ciips.ee.uwa.edu.au)
 *
 *		PC (OS/2)
 *		---------
 *		Bjorn Karlowsky (?)
 *
 *		PC (Windows 3.11)
 *		-----------------
 *		Jim Crawford (pfister_@hotmail.com)
 *
 *		PC (Windows '95)
 *		----------------
 *		Jason Hutchens (hutch@ciips.ee.uwa.edu.au)
 *
 *		PPC (Linux)
 *		-----------
 *		Lucas Vergnettes (Lucasv@sdf.lonestar.org)
 *
 *		SGI (Irix)
 *		----------
 *		Jason Hutchens (hutch@ciips.ee.uwa.edu.au)
 *
 *		Sun (SunOS)
 *		-----------
 *		Jason Hutchens (hutch@ciips.ee.uwa.edu.au)
 */

/*===========================================================================*/

/* Wakkerbot, based on megahal (c) 2010-2013, WP 
**					http://www.sourceforge.net/wakkerbot
**	Modifications/ additions:
**	-	specialised tokeniser
**	-	careful handling of Initcaps and bastard strings(such as acronyms and numerics)
**	-	Hashtables for dictionary and markov-nodes
**	-	Almost-sorted tables inside the nodes for faster weighted sampling.
**	-	random generator based on hardware CPU clock
**	-	keyword extraction based on word<->word neighborship and power-iteration
**	-	Excessive parametrisation and tuning. Penalties for sentences without Initcaps or a final period.
**	-	Alzheimer Algorithm for LRU and fast forgetting of infrequent words
**	-	cruft removal (multi-brain/personality, speech)
**	
*/

/*
 *		$Log: megahal.c,v $
 *		Revision 1.10  2004/02/23 11:12:29  lfousse
 *		Changed default working directory and added options to change it.
 *		
 *		Revision 1.9  2004/01/13 10:59:20  lfousse
 *		* Applied code cleaning already shipped with the debian package.
 *		* Removed pure debian stuff.
 *		* Added lacking setup.py file for python module.
 *		
 *		Revision 1.8  2003/08/26 12:49:16  lfousse
 *		* Added the perl interface
 *		* cleaned up the python interface a bit (but this
 *		  still need some work by a python "expert")
 *		* Added a learn_no_reply function.
 *		
 *		Revision 1.7  2003/08/18 21:45:23  lfousse
 *		Added megahal_learn_no_reply function for quick learning, and
 *		corresponding python interface.
 *		
 *		Revision 1.6  2002/10/16 04:32:53  davidw
 *		* megahal.c (change_personality): [ 541667 ] Added patch from Andrew
 *		  Burke to rework logic in change_personality.
 *		
 *		* megahal.c: Trailing white space cleanup.
 *		
 *		* python-interface.c: [ 546397 ] Change python include path to a more
 *		  recent version.  This should really be fixed by using some of
 *		  Python's build automation tools.
 *		
 *		Revision 1.5  2000/11/08 11:07:11  davidw
 *		Moved README to docs directory.
 *
 *		Changes to debian files.
 *
 *		Revision 1.4  2000/09/07 21:51:12  davidw
 *		Created some library functions that I think are workable, and moved
 *		everything else into megahal.c as static variables/functions.
 *
 *		Revision 1.3  2000/09/07 11:43:43  davidw
 *		Started hacking:
 *
 *		Reduced makefile targets, eliminating non-Linux OS's.  There should be
 *		a cleaner way to do this.
 *
 *		Added Tcl and Python C level interfaces.
 *
 *		Revision 1.23  1998/05/19 03:02:02  hutch
 *		Removed a small malloc() bug, and added a progress display for
 *		generate_reply().
 *
 *		Revision 1.22  1998/04/24 03:47:03  hutch
 *		Quick bug fix to get sunos version to work.
 *
 *		Revision 1.21  1998/04/24 03:39:51  hutch
 *		Added the BRAIN command, to allow user to change MegaHAL personalities
 *		on the fly.
 *
 *		Revision 1.20  1998/04/22 07:12:37  hutch
 *		A few small changes to get the DOS version to compile.
 *
 *		Revision 1.19  1998/04/21 10:10:56  hutch
 *		Fixed a few little errors.
 *
 *		Revision 1.18  1998/04/06 08:02:01  hutch
 *		Added debugging stuff, courtesy of Paul Baxter.
 *
 *		Revision 1.17  1998/04/02 01:34:20  hutch
 *		Added the help function and fixed a few errors.
 *
 *		Revision 1.16  1998/04/01 05:42:57  hutch
 *		Incorporated Mac code, including speech synthesis, and attempted
 *		to tidy up the code for multi-platform support.
 *
 *		Revision 1.15  1998/03/27 03:43:15  hutch
 *		Added AMIGA specific changes, thanks to Dag Agren.
 *
 *		Revision 1.14  1998/02/20 06:40:13  hutch
 *		Tidied up transcript file format.
 *
 *		Revision 1.13  1998/02/20 06:26:19  hutch
 *		Fixed random number generator and Seed() function (thanks to Mark
 *		Tarrabain), removed redundant code left over from the Loebner entry,
 *		prettied things up a little and destroyed several causes of memory
 *		leakage (although probably not all).
 *
 *		Revision 1.12  1998/02/04 02:55:11  hutch
 *		Fixed up memory allocation error which caused SunOS versions to crash.
 *
 *		Revision 1.11  1998/01/22 03:16:30  hutch
 *		Fixed several memory leaks, and the frustrating bug in the
 *		Write_Input routine.
 *
 *		Revision 1.10  1998/01/19 06:44:36  hutch
 *		Fixed MegaHAL to compile under Linux with a small patch credited
 *		to Joey Hess (joey@kitenet.net).  MegaHAL may now be included as
 *		part of the Debian Linux distribution.
 *
 *		Revision 1.9  1998/01/19 06:37:32  hutch
 *		Fixed a minor bug with end-of-sentence punctuation.
 *
 *		Revision 1.8  1997/12/24 03:17:01  hutch
 *		More bug fixes, and hopefully the final contest version!
 *
 *		Revision 1.7  1997/12/22  13:18:09  hutch
 *		A few more bug fixes, and non-repeating implemented.
 *
 *		Revision 1.6  1997/12/22 04:27:04  hutch
 *		A few minor bug fixes.
 *
 *		Revision 1.5  1997/12/15 04:35:59  hutch
 *		Final Loebner version!
 *
 *		Revision 1.4  1997/12/11 05:45:29  hutch
 *		The almost finished version.
 *
 *		Revision 1.3  1997/12/10 09:08:09  hutch
 *		Now Loebner complient (tm).
 *
 *		Revision 1.2  1997/12/08 06:22:32  hutch
 *		Tidied up.
 *
 *		Revision 1.1  1997/12/05  07:11:44  hutch
 *		Initial revision (lots of files were merged into one, RCS re-started)
 *
 *		Revision 1.7  1997/12/04 07:07:13  hutch
 *		Added load and save functions, and tidied up some code.
 *
 *		Revision 1.6  1997/12/02 08:34:47  hutch
 *		Added the ban, aux and swp functions.
 *
 *		Revision 1.5  1997/12/02 06:03:04  hutch
 *		Updated to use a special terminating symbol, and to store only
 *		branches of maximum depth, as they are the only ones used in
 *		the reply.
 *
 *		Revision 1.4  1997/10/28 09:23:12  hutch
 *		MegaHAL is babbling nicely, but without keywords.
 *
 *		Revision 1.3  1997/10/15  09:04:03  hutch
 *		MegaHAL can parrot back whatever the user says.
 *
 *		Revision 1.2  1997/07/21 04:03:28  hutch
 *		Fully working.
 *
 *		Revision 1.1  1997/07/15 01:55:25  hutch
 *		Initial revision.
 */

/*===========================================================================*/

#include <stdio.h>
#include <stdlib.h>
#include <stdarg.h>

#pragma define _BSD_SOURCE 1
#pragma define _XOPEN_SOURCE 1
#define __USE_MISC
#include <unistd.h>    // lockf()
#undef __USE_MISC

#include <getopt.h>

#include <ctype.h> /* isspace() */
#include <string.h>
#include <strings.h> /* strncasecmp */
extern char *strdup(const char *);

#include <errno.h>
#include <signal.h>

#include <float.h> /* DBL_EPSILON */
#include <math.h>
#include <time.h>

#include <sys/types.h>

#include "megahal.h"

#if defined(DEBUG)
#include "debug.h"
#endif


#define MIN(a,b) ((a)<(b))?(a):(b)

/* Changed Cookie and restarted version numbering, because the sizes have changed */
#define COOKIE "Wakker0.0"
#define DEFAULT_TIMEOUT 10
#define DEFAULT_DIR "."
#define MY_NAME "MegaHAL"
#define MY_NAME "PlasBot"

#define STATIC /* EMPTY:: For profiling, to avoid inlining of STATIC functions. */
#define STATIC static

#define COUNTOF(a) (sizeof(a) / sizeof(a)[0])
#define MYOFFSETOF(p,m) ((size_t)( ((char*)(&((p)->(m)))) - ((char*)(p) )))
#define WAKKER_INF (1E+40)

	/* define to outcomment old stuff */
#define DONT_WANT_THIS 0

	/* store precomputed hash values in Dict entries.
	** This will cost 32 bit / entry and wont save a lot of CPU
	** (The maximal AVG estimated chainlength is 1.5)
	** The final stringcompare is needed anyway
	** , and strings tend to be different (except for the last one ;-).
	*/
#define WANT_STORE_HASH 0

	/* some develop/debug switches. 0 to disable */
#define WANT_DUMP_REHASH_TREE 0
#define WANT_DUMP_DELETE_DICT 0

	/* bitmask (0-3)
	** 1 := dump Xtab weight details
	** 2 := symbol_weight() prim/alt details
	** */
#define WANT_DUMP_KEYWORD_WEIGHTS 0

#define WANT_DUMP_ALZHEIMER_PROGRESS 1 /* 0...4 */

	/* Show replies every time evaluate_reply() finds a better candidate 
	** (default=1) for building debugging
	*/
#define WANT_DUMP_ALL_REPLIES 1

	/* dump tree as ascii when program exits (This will cost a LOT of disk space)
	** 1 := only dump forward tree
	** 2 := only dump backward tree
	** 3 := dump both.
	 */
#define WANT_DUMP_MODEL 0

/*
** Real SWITCHES. Note: these are not independent. Some combinations might be impossible
*/
	/* Use keyword weights when evaluating the replies */
#define WANT_KEYWORD_WEIGHTS 1
	/* The order of the Markov model.
	** NOTE: if you change this, the (binary) .brn file will be rewritten
	** using the new value of ORDER_WANTED. Be carefull.
	*/
#define ORDER_WANTED 5

	/* improved random generator, using noise from the CPU clock (only works on intel/gcc) */
#define WANT_RDTSC_RANDOM 1

#include "megahal.cnf"

	/* add some copy cat detection */
#ifndef WANT_PARROT_CHECK
#define USE_QSORT 0
#define WANT_PARROT_CHECK 11
#endif
	/* Flags for converting strings to/from latin/utf8
	** Best is to keep the corpus in utf8.
	** In this case:
	**	if the input happens to be latin, specify SCRUTINIZE_INPUT=SCRUTINIZE_L2U
	**	if you want the output to be latin, specify SCRUTINIZE_OUTPUT SCRUTINIZE_U2L
	*/
#define SCRUTINIZE_U2L 1
#define SCRUTINIZE_L2U 2
#define SCRUTINIZE_INPUT 0
#define SCRUTINIZE_OUTPUT SCRUTINIZE_U2L
#define SCRUTINIZE_OUTPUT 0

#if WANT_PARROT_CHECK
#define PARROT_ADD(x) do { \
	parrot_hash[ (x) % COUNTOF(parrot_hash)] += 1; \
	parrot_hash2[ (x) % COUNTOF(parrot_hash2)] += 1; \
	} while(0)

#define PARROT_RESURRECT(dum) do { \
	memset (parrot_hash, 0, sizeof parrot_hash); \
	memset (parrot_hash2, 0, sizeof parrot_hash2); \
	} while(0)

#endif /* WANT_PARROT_CHECK */

#define SEP "/"

typedef unsigned char StrLen;
typedef unsigned char StrType;
typedef unsigned char StrFlag;
typedef unsigned int WordNum;
typedef unsigned int ChildIndex;
typedef unsigned int DictSize;
typedef unsigned int Count;
typedef unsigned int UsageCnt;
typedef unsigned int HashVal;
typedef unsigned int Stamp;
typedef unsigned long long BigThing;
typedef unsigned long long UsageSum;
BigThing rdtsc_rand(void);

#define STRLEN_MAX ((StrLen)-1)
#define WORD_NIL ((WordNum)-1)
#define WORD_ERR ((WordNum)0)
#define WORD_FIN ((WordNum)1)
#define CHILD_NIL ((ChildIndex)-1)
#define STAMP_MAX ((Stamp)-1)

typedef struct {
    StrLen length;
    StrType ztype;	/* type is not stored in the brainfile but recomputed on loading */
    StrFlag zflag;	/* flag not stored in the brainfile recomputed on loading */
    char *word;
} STRING;

struct	dictslot {
	WordNum tabl;
	WordNum link;
#if WANT_STORE_HASH
	HashVal whash;
#endif /* WANT_STORE_HASH */
	struct wordstat {
		UsageCnt nnode;
		UsageCnt valuesum;
		} stats;
	STRING string;
	};

typedef struct {
    DictSize size;
    DictSize msize;
    struct dictstat	{
		UsageSum nnode;
		UsageSum valuesum;
		DictSize nonzero;
		} stats;
    struct dictslot *entry;
} DICT;

#define WANT_OLD_NODES 1
#if WANT_OLD_NODES
struct treeslot {
    ChildIndex tabl;
    ChildIndex link;
    struct treenode *ptr;
	};

typedef struct treenode {
    UsageCnt childsum; /* sum of children's count */
    UsageCnt thevalue; /* my count */
    WordNum symbol;
    Stamp stamp;
    ChildIndex msize;
    ChildIndex branch;
    struct treeslot *children;
} TREE;
#else
typedef unsigned NodeNum, NodeIdx;
#define NODE_NUM_NIL ((NodeNum) -1)
#define NODE_IDX_NIL ((NodeIdx) -1)
struct nnode {
	struct hnode {
		NodeIdx head,link;
		} num,partok, par;
	NodeNum num,pnum; /* persistant number + parent number */
	WordNum tok;
	Stamp stamp;
	UsageCnt childsum;
	UsageCnt thevalue;
	UsageCnt maxvalue;
	};
#endif

#if WANT_OLD_NODES
typedef struct {
    Count order;
    TREE *forward;
    TREE *backward;
    TREE **context;
    DICT *dict;
} MODEL;
#else
typedef struct {
    Count order;
    NodeNum fwd,rev;
    NodeNum context[10];
    DICT *dict;
} MODEL;
#endif

struct memstat {
	unsigned word_cnt;
	unsigned node_cnt;
	unsigned alloc;
	unsigned free;
	unsigned alzheimer;
	unsigned symdel;
	unsigned treedel;
        unsigned long long tokens_read;
	} volatile memstats = {0,0,0,0,0,0,0,0} ;

/*===========================================================================*/
static char *errorfilename = "megahal.log";
static char *statusfilename = "megahal.txt";
static int glob_width = 45;
static int glob_order = ORDER_WANTED;
static int glob_timeout = DEFAULT_TIMEOUT;
static int glob_dirt = 0;

static int noprompt = 0;
static int noprogress = 0;
static int nowrap = 0;
static int nobanner = 0;
static int quiet = 0;
static FILE *errorfp;
static FILE *statusfp;

#if WANT_PARROT_CHECK
unsigned parrot_hash[WANT_PARROT_CHECK] = {0,};
unsigned parrot_hash2[WANT_PARROT_CHECK+1] = {0,};
#endif /* WANT_PARROT_CHECK */

static MODEL *glob_model = NULL;
	/* Refers to a dup'd fd for the brainfile, used for locking */
static int glob_fd = -1;

#if 1||CROSS_DICT_SIZE
#include "crosstab.h"
unsigned int cross_dict_size=0;
struct crosstab *glob_crosstab = NULL;

#endif

static char *glob_directory = NULL;
static char *last_directory = NULL;

static Stamp stamp_min = 0, stamp_max=0;

volatile sig_atomic_t signal_caught = 0;

#ifndef ALZHEIMER_NODE_COUNT
#define ALZHEIMER_NODE_COUNT (16*1024*1024)
#endif
#define NODE_COUNT (ALZHEIMER_NODE_COUNT+(2*1024*1024))
struct treenode nodes[NODE_COUNT];

STATIC int resize_tree(TREE *tree, unsigned newsize);

STATIC TREE *add_symbol(TREE *, WordNum);
STATIC WordNum add_word_dodup(DICT *dict, STRING word);
STATIC size_t word_format(char *buff, STRING string);

STATIC size_t tokenize(char *string, int *sp);

STATIC void error(char *, char *, ...);
STATIC void exithal(void);
void sig_lethal(int signum);
void sig_ignore(int);
void show_config(FILE *fp);
STATIC void initialize_error(char *);
STATIC void initialize_status(char *);

STATIC TREE *find_symbol(TREE *node, WordNum symbol);
STATIC TREE *find_symbol_add(TREE *, WordNum);

STATIC WordNum find_word(DICT *, STRING);
STATIC DICT *new_dict(void);

STATIC char *read_input(char * prompt);
STATIC void save_model(char *, MODEL *);
STATIC void log_input(char *);
STATIC void log_output(char *);

STATIC char *format_output(char *);
STATIC void empty_dict(DICT *dict);
STATIC void free_model(MODEL *);
STATIC void free_tree(TREE *);
STATIC void free_string(STRING word);

STATIC void initialize_context(MODEL *);
STATIC void initialize_dict(DICT *);
STATIC DICT *read_dict(char *filename);
STATIC void load_dict(FILE *, DICT *);
STATIC int load_model(char *path, MODEL *mp);
STATIC void load_personality(MODEL **);
STATIC TREE * load_tree(FILE *);
STATIC void load_word(FILE *, DICT *);
STATIC MODEL *new_model(int);
STATIC TREE *node_new(unsigned nchild);
STATIC STRING new_string(char *str, size_t len);
STATIC void print_header(FILE *);
STATIC void save_dict(FILE *, DICT *);
STATIC unsigned save_tree(FILE *, TREE *);
STATIC void save_word(FILE *, STRING);
STATIC WordNum seed(MODEL *);

STATIC void show_dict(DICT *);
STATIC void status(char *, ...);
STATIC void train(MODEL *, char *);
STATIC void update_context(MODEL *, WordNum symbol);
STATIC void update_model(MODEL *model, WordNum symbol);
STATIC void warn(char *, char *, ...);
STATIC int wordcmp(STRING one, STRING two);
unsigned int urnd(unsigned int range);

STATIC HashVal hash_mem(void *dat, size_t len);
STATIC WordNum * dict_hnd(DICT *dict, STRING word);
STATIC HashVal hash_word(STRING word);
STATIC int grow_dict(DICT *dict);
STATIC int resize_dict(DICT *dict, unsigned newsize);
STATIC void format_dictslots(struct dictslot * slots, unsigned size);
STATIC unsigned long set_dict_count(MODEL *model);
STATIC unsigned long dict_inc_ref_recurse(DICT *dict, TREE *node);
STATIC unsigned long dict_inc_ref(DICT *dict, WordNum symbol, unsigned nnode, unsigned valuesum);
STATIC unsigned long dict_dec_ref(DICT *dict, WordNum symbol, unsigned nnode, unsigned valuesum);

/* these exist to allow utf8 in strings */
STATIC int myisalpha(int ch);
STATIC int myisupper(int ch);
STATIC int myislower(int ch);
STATIC int myisalnum(int ch);
STATIC int myisalnum_extra(int ch);
STATIC int myiswhite(int ch);
STATIC int buffer_is_usable(char *buf, unsigned len);
STATIC int dont_need_white_l(STRING string);
STATIC int dont_need_white_r(STRING string);
STATIC int word_is_allcaps(STRING string);
STATIC int word_has_highbit(STRING string);
STATIC int word_classify(STRING org);
#define TOKEN_LOWER 1
#define TOKEN_UPPER 2
#define TOKEN_INITCAPS 3
#define TOKEN_CAMEL 4
#define TOKEN_AFKO 5
#define TOKEN_NUMBER 6
#define TOKEN_PUNCT 7
#define TOKEN_ATAAP 8
#define TOKEN_HEKHASH 9
#define TOKEN_MISC 10

STATIC void del_symbol_do_free(TREE *tree, WordNum symbol);
void free_tree_recursively(TREE *tree);
STATIC unsigned model_alzheimer(MODEL * model, unsigned maxnodecount);
STATIC unsigned symbol_alzheimer_recurse(TREE *tree, unsigned lev, unsigned lim);
STATIC int check_interval(Stamp min, Stamp max, Stamp this);
#define STAMP_INSIDE 0
#define STAMP_BELOW -1
#define STAMP_ABOVE 1

void read_dict_from_ascii(DICT *dict, char *name);
static DICT *alz_dict = NULL;

STATIC void dump_model(MODEL * model, char *path, int flags);
STATIC void dump_model_recursive(FILE *fp, TREE *tree, DICT *dict, int indent);

STATIC ChildIndex *node_hnd(TREE *node, WordNum symbol);
STATIC void format_treeslots(struct treeslot *slots , unsigned size);
STATIC void show_memstat(char *msg);
STATIC void treeslots_sort(struct treeslot  *slots , unsigned count);
STATIC int treeslots_cmp(const void *vl, const void *vr);

STATIC STRING word_dup_lowercase(STRING org);
STATIC STRING word_dup_initcaps(STRING org);
STATIC STRING word_dup_othercase(STRING org);
	/* The weight we want we want to associate with a word.
	** if want_other is nonzero, we are also interested in
	** other capitalisations of the word.
	*/
STATIC double word_weight(DICT *dict, STRING word, int want_other);
STATIC double symbol_weight(DICT *dict, WordNum symbol, int want_other);
	/* Callback functions for crosstab */
STATIC double symbol_weight_callback(WordNum sym);
STATIC size_t symbol_format_callback(char *buff, WordNum sym);
	/* The aftermath for the output-sentence.
	** Sentences that don't start with a Capitalised Word
	** or don't end with a period get penalised.
	** [the ugly globals are only used in debug printf()s]
	*/
double init_val_fwd= 1.0;
double init_val_rev= 1.0;
int init_typ_fwd= 0;
double start_penalty(MODEL *model, STRING word);
double end_penalty(MODEL *model, STRING word);

STATIC void dump_word(FILE *fp, STRING word);
STATIC char * scrutinize_string(char * src, int mode);
STATIC char * utf2latin(char * src, size_t len);
STATIC char * latin2utf(char * src, size_t len);
STATIC size_t cp_utf2latin(char *dst, char * src, size_t len);

STATIC int eat_utf8(unsigned char *str, unsigned len, unsigned *target);
STATIC unsigned cha_latin2utf8(unsigned char *dst, unsigned val);
STATIC size_t hexdump_string(char *buff, STRING string);
STATIC size_t decode_word(char * buff, STRING src, int type );

struct sentence {
	unsigned mused;
	unsigned msize;
	unsigned kwhit;
	struct	{
		STRING string;
		} *entry;
	} ;
struct sentence *glob_input = NULL;
// struct sentence *glob_greets = NULL;
STATIC void make_words(char * str, struct sentence * dst);
STATIC void add_word_to_sentence(struct sentence *dst, STRING word);
STATIC void learn_from_input(MODEL * mp, struct sentence *src);
STATIC char *generate_reply(MODEL *mp, struct sentence *src);
STATIC double evaluate_reply(MODEL *model, struct sentence *sentence);
STATIC struct sentence * sentence_new(void);
STATIC int sentence_grow(struct sentence *ptr);
STATIC int sentence_resize(struct sentence *ptr, unsigned newsize);
STATIC void sentence_reverse(struct sentence *ptr);
STATIC struct sentence *one_reply(MODEL *);
STATIC void change_personality(struct sentence *, unsigned int, MODEL **);
STATIC void make_keywords(MODEL *mp, struct sentence *src);
STATIC WordNum babble(MODEL *model, struct sentence *words);
STATIC char *make_output(struct sentence *src);

	/* The lean statistics department.
	*/
#if WANT_PARROT_CHECK
STATIC double penalize_two_parrots(unsigned arr1[], unsigned arr2[], unsigned siz1);
STATIC double penalize_one_parrot(unsigned arr[], unsigned siz);
STATIC double penalize_both_parrots(unsigned arr1[], unsigned arr2[], unsigned siz1);
STATIC unsigned long long dragon_denominator2(unsigned long nslot, unsigned long nitem);
#endif

void megahal_setquiet(void)
{
    quiet = 1;
}

void megahal_setnoprompt(void)
{
    noprompt = 1;
}

void megahal_setnoprogress(void)
{
    noprogress = 1;
}

void megahal_setnowrap (void)
{
    nowrap = 1;
}
void megahal_setnobanner (void)
{
    nobanner = 1;
}

void megahal_seterrorfile(char *filename)
{
    errorfilename = filename;
}

void megahal_setstatusfile(char *filename)
{
    statusfilename = filename;
}

void megahal_setdirectory (char *dir)
{
    glob_directory = dir;
}


void megahal_settimeout (char *string)
{
    sscanf(string, "%d", &glob_timeout);
    if (glob_timeout) {
      alarm(2+glob_timeout);
      signal(SIGALRM, sig_lethal);
    }
}

/*
   megahal_initialize --

   Initialize various brains and files.

   Results:

   None.
*/

void megahal_initialize(void)
{
    unsigned bogus;
    bogus = urnd(100);
    errorfp = stderr;
    statusfp = stdout;

    initialize_error(errorfilename);
    initialize_status(statusfilename);
    sig_ignore(0);


    glob_input = sentence_new();
    // glob_greets = sentence_new();
    change_personality(NULL, 0, &glob_model);
    while (bogus--) urnd(42);
}

/*
   megahal_do_reply --

   Take string as input, and return allocated string as output.  The
   caller is responsible for freeing this memory.

  */

char *megahal_do_reply(char *input, int want_log)
{
    char *output = NULL;

    if (want_log) log_input(input);

    make_words(input, glob_input);
    if (glob_input->mused < 3) return NULL;
    if (glob_timeout <= 0 ) learn_from_input(glob_model, glob_input);
    else {
        show_config(stderr);
	output = generate_reply(glob_model, glob_input);
	}
    return output;
}

/*
   megahal_learn_no_reply --

   Take string as input, update model but don't generate reply.

  */

void megahal_learn_no_reply(char *input, int want_log)
{
    if (want_log) log_input(input);

    make_words(input, glob_input);

    learn_from_input(glob_model, glob_input);
}

/*
   megahal_output --
   This function pretty prints output.
   Wrapper function to have things in the right namespace.
*/

void megahal_output(char *output)
{
    if (!quiet) log_output(output);
    printf( "%s", output );
}

/*
   megahal_input --

   Get a string from stdin, using a prompt.

  */

char *megahal_input(char *prompt)
{
    if (noprompt)
	return read_input(NULL);
    else
	return read_input(prompt);
}

void megahal_dumptree(char *path, int flags)
{
dump_model(glob_model, path, flags);
}


/*
   megahal_cleanup --

   Clean up everything. Prepare for exit.

  */

void megahal_cleanup(void)
{
    save_model("megahal.brn", glob_model);
    show_memstat("Cleanup" );
    exithal();
}



/*---------------------------------------------------------------------------*/

/*
 *		Function:	ExitHAL
 *
 *		Purpose:		Terminate the program.
 */
STATIC void exithal(void)
{
#if (WANT_DUMP_MODEL & 1)
    dump_model(glob_model, "tree.fwd", 1);
#endif
#if (WANT_DUMP_MODEL & 2)
    dump_model(glob_model, "tree.rev", 2);
#endif
    show_memstat("Exit(0)" );
    exit(0);
}

/*---------------------------------------------------------------------------*/

/*
 *		Function:	Read_Input
 *
 *		Purpose:		Read an input string from the user.
 *		NOTE: this function returns a static malloc()d string, which is
 *		reused on every invocation, so the caller should *not* free() it.
 *		Also, because the contents of the string change, the caller should not
 *		keep any pointers into the returned string.
 */
STATIC char *read_input(char *prompt)
{
    static char *input = NULL;
    static size_t msize=0;
    unsigned seen_eol;
    size_t length;
    int ch;

    seen_eol = 0;
    length = 0;

    /*
     *		Display the prompt to the user.
     */
    if (prompt) {
	fprintf(stdout, "%s", prompt);
	fflush(stdout);
	}

    /*
     *		Loop forever, reading characters and putting them into the input
     *		string.
     */
    while(1) {
	ch = getc(stdin);

	/*
	 *		If the character is a line-feed, then bump the seen_eol variable
	 *		If it already was nonzero, then this is a double line-feed,
	 *		in which case we should exit.  After a line-feed, display the
	 *		prompt again, and set the character to the space character, as
	 *		we don't permit linefeeds to appear in the input.
	 */
	if (ch == EOF) { if (seen_eol) break; else return NULL; }
	if (ch == '\r') continue;
	if (ch == '\n') {
	    if (seen_eol) break;
	    if (prompt) { fprintf(stdout, "%s", prompt); fflush(stdout); }
	    seen_eol += 1;
	    ch = ' ';
	} else {
	    seen_eol = 0;
	}

	/* This will end execution on two consecutive empty lines*/
	/* if (seen_eol && !length) return NULL;*/

	if (length +2 >= msize) {
		input = realloc(input, msize? 2*msize: 256);
		if (input) msize = msize ? 2 * msize : 256;
		}
	if (!input) {
	    error("read_input", "Unable to re-allocate the input string");
	    return NULL;
	}

	input[length++] = ch;
	// input[length] ='\0';
    }

    while(length > 0 && isspace(input[length-1])) length--;
    input[length] = '\0';

	/* scrutinize_string may or may not reallocate the output string, but we don't care */
    input = scrutinize_string (input, SCRUTINIZE_INPUT);
    return input;
}

/*---------------------------------------------------------------------------*/

/*
 *		Function:	Initialize_Error
 *
 *		Purpose:		Close the current error file pointer, and open a new one.
 */
STATIC void initialize_error(char *filename)
{
    if (errorfp != stderr) fclose(errorfp);

    if (!filename) return ;

    errorfp = fopen(filename, "a");
    if (!errorfp) {
	errorfp = stderr;
	return ;
    }
    print_header(errorfp);
    return ;
}

/*---------------------------------------------------------------------------*/

/*
 *		Function:	Error
 *
 *		Purpose:		Print the specified message to the error file.
 */
STATIC void error(char *title, char *fmt, ...)
{
    va_list argp;

    fprintf(errorfp, "%s: ", title);
    va_start(argp, fmt);
    vfprintf(errorfp, fmt, argp);
    va_end(argp);
    fprintf(errorfp, ".\n");
    fflush(errorfp);

    fprintf(stderr, MY_NAME " died for some reason; check the error log.\n");

    show_memstat("Exit(1)" );
    exit(1);
}

/*---------------------------------------------------------------------------*/

STATIC void warn(char *title, char *fmt, ...)
{
    va_list argp;

    fprintf(errorfp, "%s: ", title);
    va_start(argp, fmt);
    vfprintf(errorfp, fmt, argp);
    va_end(argp);
    fprintf(errorfp, ".\n");
    fflush(errorfp);

    fprintf(stderr, MY_NAME " emitted a warning; check the error log.\n");

    return ;
}

STATIC void show_memstat(char *msg)
{
if (!msg) msg = "..." ;

status( "[ stamp Min=%u Max=%u ]\n", (unsigned) stamp_min, (unsigned) stamp_max);
status ("Memstat %s: {wordcnt=%u nodecnt=%u alloc=%u free=%u alzheimer=%u symdel=%u treedel=%u} tokens_read=%llu\n"
	, msg
	, memstats.word_cnt , memstats.node_cnt
	, memstats.alloc , memstats.free
	, memstats.alzheimer , memstats.symdel , memstats.treedel
	, memstats.tokens_read
	);
}
/*---------------------------------------------------------------------------*/

/*
 *		Function:	Initialize_Status
 *
 *		Purpose:		Close the current status file pointer, and open a new one.
 */
STATIC void initialize_status(char *filename)
{
    if (statusfp != stdout) fclose(statusfp);
    if (!filename) return ;
    statusfp = fopen(filename, "a");
    if (!statusfp) {
	statusfp = stdout;
	return ;
    }
    print_header(statusfp);
    return ;
}

/*---------------------------------------------------------------------------*/

/*
 */
STATIC void status(char *fmt, ...)
{
    va_list argp;

    va_start(argp, fmt);
    vfprintf(statusfp, fmt, argp);
    va_end(argp);
    fflush(statusfp);

    return ;
}

/*---------------------------------------------------------------------------*/

/*
 *		Function:	Print_Header
 *
 *		Purpose:		Display a copyright message and timestamp.
 */
STATIC void print_header(FILE *fp)
{
    time_t clock;
    char timestamp[1024];
    struct tm *local;

    clock = time(NULL);
    local = localtime(&clock);
    strftime(timestamp, 1024, "Start at: [%Y/%m/%d %H:%M:%S]\n", local);

    fprintf(fp, "MegaHALv8\n");
    fprintf(fp, "Copyright (C) 1998 Jason Hutchens\n"
		"Compiled Wakkerbot %s %s\n%s"
	, __DATE__ , __TIME__, timestamp);
    fflush(fp);

}

/*---------------------------------------------------------------------------*/

STATIC void log_output(char *output)
{
    char *formatted;
    char *bit;

    formatted = format_output(output);

    bit = strtok(formatted, "\n");
    if (!bit) status(MY_NAME ": %s\n", formatted);
    for( ;bit; bit = strtok(NULL, "\n")) {
	status(MY_NAME ": %s\n", bit);
    }
}

/*---------------------------------------------------------------------------*/

STATIC void log_input(char *input)
{
    char *formatted;
    char *bit;

    glob_width = 64;
    formatted = format_output(input);

    bit = strtok(formatted, "\n");
    if (!bit) status("User:    %s\n", formatted);
    for(	;bit; bit = strtok(NULL, "\n")) {
	status("User:    %s\n", bit);
    }
}

/*---------------------------------------------------------------------------*/

STATIC char *format_output(char *output)
{
    static char *formatted = NULL;
    size_t len, l,i,j,c;

    len = strlen(output);
    formatted = realloc(formatted, len+2);
    if (!formatted) {
	error("format_output", "Unable to re-allocate formatted");
	return "ERROR";
    }

    l = 0;
    j = 0;
    for(i = 0; i < len ; i++) {
	if (l == 0 && isspace(output[i])) continue;
	formatted[j++] = output[i];
	l++;
	if (nowrap) continue;
	if (l < glob_width) continue;
	for(c = j-1; c > 0; c--)
	    if (formatted[c] == ' ') {
		formatted[c] = '\n';
		l = j-c-1;
		break;
	    }
    }
    if (j > 0 && formatted[j-1] != '\n') {
	formatted[j] = '\n';
	j++;
    }
    formatted[j] = '\0';

    return formatted;
}

/*---------------------------------------------------------------------------*/

STATIC void add_word_to_sentence(struct sentence *dst, STRING word)
{

if (!dst) return ;

if (dst->mused >= dst->msize && sentence_grow(dst)) return ;

dst->entry[dst->mused++].string = word;

return ;

}
/*---------------------------------------------------------------------------*/

STATIC WordNum add_word_dodup(DICT *dict, STRING word)
{
WordNum *np;

if (!word.length) return 0; /* WP: should be WORD_NIL */

np = dict_hnd(dict, word);
if (!np) return 0; /* WP: should be WORD_NIL */

if (*np == WORD_NIL) {
	STRING this;
	*np = dict->size++;
	this = new_string(word.word, word.length);
	dict->entry[*np].string = this;
#if WANT_STORE_HASH
	dict->entry[*np].whash = hash_word(this);
#endif /* WANT_STORE_HASH */
	}
return *np;

}

#if NEVER
STATIC void del_word_dofree(DICT *dict, STRING word);
/* FIXME: this is (semantically) wrong:
** if we shift down the words, their symbols (indexes)
** will change (decremented) as well.
** Which is ok if we use the dict ONLY for
** EXISTS() testing, but we should not assume
** the symbols to be stable after a deletion.
** --> the symbols (WordNums) should NOT be considered stable.
*/
STATIC void del_word_dofree(DICT *dict, STRING word)
{
WordNum *np,this,top;

np = dict_hnd(dict, word);
if (!np) return;
if (*np == WORD_NIL) {
	warn( "del_word_dofree", "could not find '%*.*s'\n"
	,  (int) word.length,  (int) word.length,  word.word );
	return;
	}

this = *np ;
if (this == dict->entry[this].link) {
	warn( "del_word_dofree", "Cyclic linked list detected at %u: '%*.*s'\n"
	,  this, (int) word.length,  (int) word.length,  word.word );
	dict->entry[this].link = WORD_NIL;
	}
*np = dict->entry[this].link;
dict->entry[this].link = WORD_NIL;

if ( dict->entry[this].stats.nnode ) dict->stats.nonzero -= 1;
dict->stats.nnode -= dict->entry[this].stats.nnode;
dict->stats.valuesum -= dict->entry[this].stats.valuesum;
free (dict->entry[this].string.word );
dict->entry[this].string.word = NULL;
dict->entry[this].string.length = 0;

	/* done deleting. now locate the top element */
top = --dict->size;
if (!top || top == this) return ; /* last man standing */

np = dict_hnd(dict, dict->entry[top].string);
if (!np || *np == WORD_NIL) {
	warn( "del_word_dofree", "deleting at %u could not find top element at %u\n", this, top);
	return ;
	}

	/* move the top element to the vacant slot */
*np = this;
dict->entry[this].string = dict->entry[top].string;

#if WANT_STORE_HASH
dict->entry[this].whash = dict->entry[top].whash;
#endif /* WANT_STORE_HASH */

dict->entry[this].stats = dict->entry[top].stats;
	/* dont forget top's offspring */
dict->entry[this].link = dict->entry[top].link;
dict->entry[top].link = WORD_NIL;
dict->entry[top].stats.nnode = 0;
dict->entry[top].stats.valuesum = 0;
dict->entry[top].string.word = NULL;
dict->entry[top].string.length = 0;

#if WANT_STORE_HASH
dict->entry[top].whash = 0;
#endif /* WANT_STORE_HASH */

if (!dict->size || dict->size <= dict->msize - DICT_SIZE_SHRINK) {

#if (WANT_DUMP_DELETE_DICT >= 1)
    status("dict(%llu:%llu/%llu) will be shrunk: %u/%u\n"
	, dict->stats.valuesum, dict->stats.nnode, dict->stats.nonzero, dict->branch, dict->msize);
#endif
    resize_dict(dict, dict->size);
    }
return ;
}
#endif /* Never */
/*---------------------------------------------------------------------------*/

STATIC WordNum find_word(DICT *dict, STRING string)
{
WordNum *np;

if (!dict) return WORD_NIL; /* WP: Changed sentinel to WORD_NIL */
np = dict_hnd(dict, string);

if (!np || *np == WORD_NIL) return WORD_NIL; /* WP: Changed sentinel to WORD_NIL */
return *np;
}

STATIC STRING new_string(char *str, size_t len)
{
STRING this = {0,0,0,NULL};

if (str) {
     if (!len) len = strlen(str);
     if (len) { this.word = malloc(len); memcpy(this.word, str, len); }
     else { this.word = malloc(1); memset(this.word, 0, 1); }
     this.length = len;
     this.ztype = word_classify(this);
     }
else	{
     // this.word = NULL;
     }
return this;
}

/*---------------------------------------------------------------------------*/

/*
 *		Function:	Wordcmp
 *
 *		Purpose:		Compare two STRINGS, and return an integer indicating whether
 *						the first word is less than, equal to or greater than the
 *						second word.
 */
STATIC int wordcmp(STRING one, STRING two)
{
    int rc;
    size_t siz;

    siz = MIN(one.length,two.length);

    /* rc = strncasecmp(one.word, two.word, siz);*/
    rc = memcmp(one.word, two.word, siz);
    if (rc) return rc;

    if (one.length < two.length) return -1;
    if (one.length > two.length) return 1;

    return 0;
}

/*---------------------------------------------------------------------------*/

/*
 *		Function:	Free_Dictionary
 *
 *		Purpose:		Release the memory consumed by the dictionary.
 */
STATIC void empty_dict(DICT *dict)
{
    if (!dict) return;
    dict->stats.valuesum = 0;
    dict->stats.nnode = 0;
    dict->stats.nonzero = 0;
    dict->size = 0;
    resize_dict(dict, DICT_SIZE_INITIAL);
}

/*---------------------------------------------------------------------------*/

STATIC void free_model(MODEL *model)
{
    if (!model) return;
    free_tree(model->forward);
    free_tree(model->backward);
    free(model->context);
    empty_dict(model->dict);
    free(model->dict);

    free(model);
}

/*---------------------------------------------------------------------------*/

STATIC void free_tree(TREE *tree)
{
    static int level = 0;
    unsigned int ikid;

    if (!tree) return;

    if (tree->children != NULL) {
	// if (level == 0) progress("Freeing tree", 0, 1);
	for(ikid = 0; ikid < tree->branch; ikid++) {
	    level++;
	    free_tree(tree->children[ikid].ptr);
	    level--;
	    // if (level == 0) progress(NULL, ikid, tree->branch);
	}
	// if (level == 0) progress(NULL, 1, 1);
	free(tree->children);
    }
    free(tree);
    memstats.node_cnt -= 1;
    memstats.free += 1;
}

/*---------------------------------------------------------------------------*/

/*
 *		Function:	Initialize_Dictionary
 *
 *		Purpose:		Add dummy words to the dictionary.
 */
STATIC void initialize_dict(DICT *dict)
{
/* NOTE: The constants 0 AND 1 refering to thes two array elements
** are hardcoded at a few places in the source..
*/
    static STRING word = {7,0,0, "<ERROR>" };
    static STRING end = {5,0,0, "<FIN>" };

    dict->stats.valuesum = 0;
    dict->stats.nnode = 0;
    dict->stats.nonzero = 0;
    add_word_dodup(dict, word);
    add_word_dodup(dict, end);
}

STATIC unsigned long set_dict_count(MODEL *model)
{
unsigned ret=0;

if (!model) return 0;
       /* all words are born unrefd */
if (model->dict) model->dict->stats.nonzero = 0;
ret += dict_inc_ref_recurse(model->dict, model->forward);
ret += dict_inc_ref_recurse(model->dict, model->backward);

return ret;
}

STATIC unsigned long dict_inc_ref_recurse(DICT *dict, TREE *node)
{
WordNum symbol;
unsigned uu,ret=0;

if (!node) return 0;
symbol = node->symbol;

ret = dict_inc_ref(dict, symbol, 1, node->thevalue);
for (uu=0; uu < node->branch; uu++) {
	ret += dict_inc_ref_recurse(dict, node->children[uu].ptr);
	}
return ret;
}

STATIC unsigned long dict_inc_ref_node(DICT *dict, TREE *node, WordNum symbol)
{

if (!dict || !node || symbol >= dict->size ) return 0;

if (node->thevalue <= 1) return dict_inc_ref(dict, symbol, 1, 1);
else return dict_inc_ref(dict, symbol, 0, node->thevalue);

}

STATIC unsigned long dict_inc_ref(DICT *dict, WordNum symbol, unsigned nnode, unsigned valuesum)
{

if (!dict || symbol >= dict->size ) return 0;

if (dict->entry[ symbol ].stats.nnode == 0 ) dict->stats.nonzero += 1;
dict->entry[ symbol ].stats.nnode += nnode;
dict->entry[ symbol ].stats.valuesum += valuesum;
dict->stats.nnode += nnode;
dict->stats.valuesum += valuesum;

return dict->entry[ symbol ].stats.valuesum;
}

STATIC unsigned long dict_dec_ref(DICT *dict, WordNum symbol, unsigned nnode, unsigned valuesum)
{

if (!dict || symbol >= dict->size ) return 0;

dict->entry[ symbol ].stats.nnode -= nnode;
if (dict->entry[ symbol ].stats.nnode == 0 ) dict->stats.nonzero -= 1;
dict->entry[ symbol ].stats.valuesum -= valuesum;
dict->stats.nnode -= nnode;
dict->stats.valuesum -= valuesum;

return dict->entry[ symbol ].stats.valuesum;
}
/*---------------------------------------------------------------------------*/

/*
 *		Function:	New_Dictionary
 *
 *		Purpose:		Allocate room for a new dictionary.
 */

STATIC DICT *new_dict(void)
{
    DICT *dict = NULL;

    dict = malloc(sizeof *dict);
    if (!dict) {
	error("new_dict", "Unable to allocate dictionary.");
	return NULL;
    }

    dict->entry = malloc (DICT_SIZE_INITIAL * sizeof *dict->entry);
    if (!dict->entry) {
	error("new_dict", "Unable to allocate dict->slots.");
	free(dict);
	return NULL;
	}
    dict->msize = DICT_SIZE_INITIAL;
    format_dictslots(dict->entry, dict->msize);
    dict->size = 0;
    dict->stats.nnode = 0;
    dict->stats.valuesum = 0;

    return dict;
}

STATIC void format_dictslots(struct dictslot * slots, unsigned size)
{
    unsigned idx;

    for (idx = 0; idx < size; idx++) {
	slots[idx].tabl = WORD_NIL;
	slots[idx].link = WORD_NIL;
#if WANT_STORE_HASH
	slots[idx].whash = 0xe;
#endif /* WANT_STORE_HASH */
	slots[idx].stats.nnode = 0;
	slots[idx].stats.valuesum = 0;
	slots[idx].string.length = 0;
	slots[idx].string.word = NULL;
	}

}
/*---------------------------------------------------------------------------*/

/*
 *		Function:	Save_Dictionary
 *
 *		Purpose:		Save a dictionary to the specified file.
 */
STATIC void save_dict(FILE *fp, DICT *dict)
{
    unsigned int iwrd;

    fwrite(&dict->size, sizeof dict->size, 1, fp);
    // progress("Saving dictionary", 0, 1);
    for(iwrd = 0; iwrd < dict->size; iwrd++) {
	save_word(fp, dict->entry[iwrd].string );
	// progress(NULL, iwrd, dict->size);
    }
    // progress(NULL, 1, 1);
    memstats.word_cnt = iwrd;
}

/*---------------------------------------------------------------------------*/

/*
 *		Function:	Load_Dictionary
 *
 *		Purpose:		Load a dictionary from the specified file.
 */
STATIC void load_dict(FILE *fp, DICT *dict)
{
    unsigned int iwrd;
    unsigned int size;
    size_t kuttje; /* to silence gcc */

	/* Avoid a lot of resizing by pre-allocating size+INITSIZE items. */
    kuttje = fread(&size, sizeof size, 1, fp);
    resize_dict(dict, dict->msize+size + kuttje + sqrt(size)); // 20150222
    /* resize_dict(dict, dict->msize+size ); */
    status("Load_dictSize=%u Initial_dictSize=%u\n", size, dict->msize);
    // progress("Loading dictionary", 0, 1);
    for(iwrd = 0; iwrd < size; iwrd++) {
	load_word(fp, dict);
	// progress(NULL, iwrd, size);
    }
    // progress(NULL, 1, 1);
    memstats.word_cnt = size;
}

/*---------------------------------------------------------------------------*/

/*
 *		Function:	Save_Word
 *
 *		Purpose:		Save a dictionary word to a file.
 */
STATIC void save_word(FILE *fp, STRING word)
{

    fwrite(&word.length, sizeof word.length, 1, fp);
    fwrite(&word.word[0], word.length, 1, fp);
}

/*---------------------------------------------------------------------------*/

/*
 *		Function:	Load_Word
 *
 *		Purpose:		Load a dictionary word from a file.
 */
STATIC void load_word(FILE *fp, DICT *dict)
{
    static char zzz[1+STRLEN_MAX];
    static STRING word = {0,0,0,zzz};
    size_t kuttje;

    kuttje = fread(&word.length, sizeof word.length, 1, fp);
    // word.word = malloc(word.length);
    if (!kuttje) {
	error("load_word", "Unable to allocate kuttje");
	return;
    }
    kuttje = fread(&word.word[0], word.length, 1, fp);
    if (kuttje) add_word_dodup(dict, word);
    // free(word.word);
}

/*---------------------------------------------------------------------------*/

/*
 *		Function:	New_Node
 *
 *		Purpose:		Allocate a new node for the n-gram tree, and initialise
 *						its contents to sensible values.
 */
STATIC TREE *node_new(unsigned nchild)
{
    TREE *node = NULL;

    node = malloc(sizeof *node);
    if (!node) {
	error("node_new", "Unable to allocate the node.");
	return NULL;
    }

    node->symbol = WORD_ERR;
    node->childsum = 0;
    node->thevalue = 0;
    node->stamp = stamp_max;
    node->msize = 0;
    node->branch = 0;
    if (!nchild) node->children = NULL;
    else {
        node->children =  malloc (nchild * sizeof *node->children);
        node->msize = nchild;
        if (node->children) format_treeslots(node->children,  node->msize);
	}
    memstats.node_cnt += 1;
    memstats.alloc += 1;
    return node;

}

/*---------------------------------------------------------------------------*/

/*
 *		Function:	New_Model
 *
 *		Purpose:		Create and initialise a new ngram model.
 */
STATIC MODEL *new_model(int order)
{
    MODEL *model = NULL;

    model = malloc(sizeof *model);
    if (!model) {
	error("new_model", "Unable to allocate model.");
        return NULL;
    }

    model->order = order;
    model->forward = node_new(0);
    model->backward = node_new(0);
    model->context = malloc( (2+order) *sizeof *model->context);
    if (!model->context) {
	error("new_model", "Unable to allocate context array.");
        return NULL;
    }
    initialize_context(model);
    model->dict = new_dict();
    initialize_dict(model->dict);

    return model;
}

/*---------------------------------------------------------------------------*/

/*
 *		Function:	Update_Model
 *
 *		Purpose:		Update the model with the specified symbol.
 */
STATIC void update_model(MODEL *model, WordNum symbol)
{
    unsigned int iord;
	/* this is a bit defensive; these symbols should never occur */
    if (symbol == WORD_NIL) return;
    if (symbol == WORD_ERR) return;
    /*
     *	Update all of the models in the current context with the specified
     *	symbol.
     */
    for(iord = model->order+1; iord > 0; iord--) {
	if ( !model->context[iord-1] ) continue;
	model->context[iord] = add_symbol(model->context[iord-1], symbol);
	dict_inc_ref_node(model->dict, model->context[iord], symbol);
	}

    return;
}

/*---------------------------------------------------------------------------*/

/*
 *		Function:	Update_Context
 *
 *		Purpose:		Update the context of the model without adding the symbol.
 */
STATIC void update_context(MODEL *model, WordNum symbol)
{
    unsigned int iord;

    for(iord = model->order+1; iord > 0; iord--) {
	if ( !model->context[iord-1] ) continue;
	model->context[iord] = find_symbol(model->context[iord-1], symbol);
	}
}

/*---------------------------------------------------------------------------*/

/*
 *	Update the statistics of the specified tree with the
 *	specified symbol, which may mean growing the tree if the
 *	symbol hasn't been seen in this context before.
 */
STATIC TREE *add_symbol(TREE *tree, WordNum symbol)
{
    TREE *node = NULL;

    node = find_symbol_add(tree, symbol);
    if (!node) return NULL;

    /*
     *		Increment the symbol counts
     *		Stop incrementing when wraparound detected.
     */
    /* fprintf(stderr, "Add_symbol(%u: Parent=%u->%u Child=%u->%u)\n"
	, symbol, tree->symbol, tree->childsum, node->symbol, node->thevalue);
	 */
    node->stamp = stamp_max; tree->stamp = stamp_max;
    node->thevalue += 1; tree->childsum += 1;
    if (!node->thevalue) {
	warn("add_symbol", "Count wants to wrap");
	node->thevalue -= 1;
    }
    if (!tree->childsum) {
	warn("add_symbol", "Usage wants to wrap");
	tree->childsum -= 1;
    }

    glob_dirt += 1;
    return node;
}

STATIC void dump_model(MODEL * model, char *path, int flags)
{
FILE *fp;

fp = fopen (path , "w" );
if (!fp) return;

fprintf(fp, "[ stamp Min=%u Max=%u ]\n", (unsigned)stamp_min, (unsigned)stamp_max);

if (flags & 1) {
	fprintf(fp, "->forward Order=%u\n", (unsigned) model->order);
	dump_model_recursive(fp, model->forward, model->dict, 0);
	}

if (flags & 2) {
	fprintf(fp, "->backward Order=%u\n", (unsigned) model->order);
	dump_model_recursive(fp, model->backward, model->dict, 0);
	}
fprintf(fp, "->Eof\n" );
fclose (fp);
}

STATIC void dump_model_recursive(FILE *fp, TREE *tree, DICT *dict, int indent)
{
unsigned slot;
WordNum sym;
static STRING null = {0,0,0,""};
unsigned nnode=0,valuesum=0;
STRING str;
if (!tree) return;

sym = tree->symbol;
if (sym < dict->size){
	str = dict->entry[sym].string ;
	nnode = dict->entry[sym].stats.nnode;
	valuesum = dict->entry[sym].stats.valuesum;
	}
else	{
	str = null;
	}

for (slot = 0; slot < indent; slot++) {
	fputc(' ', fp);
	}

fprintf(fp, "Va=%u Su=%u St=%u Br=%u/%u Sym=%u [%u,%u] '%*.*s'\n"
	, tree->thevalue
	, tree->childsum
	, tree->stamp
	, tree->branch, tree->msize , tree->symbol
	, valuesum, nnode
	, (int) str.length , (int) str.length , str.word
	);

if (! tree->branch) return;
for (slot = 0; slot < tree->branch; slot++) {
	dump_model_recursive(fp, tree->children[slot].ptr , dict, indent+1);
	}

return;
}

/* Delete a symbol from a node.
** The node's statistics are updated (but NOT it's parent's summary statistics!!)
** The node is compacted by shifting the highest element into the vacated slot.
** The node's children-array is NOT (yet) reallocated.
*/
STATIC void del_symbol_do_free(TREE *tree, WordNum symbol)
{
    ChildIndex *ip, this,top;
    TREE *child = NULL;

    /*
     *		Search for the symbol in the subtree of the tree node.
     */
    ip = node_hnd(tree, symbol);
    if (!ip || *ip == CHILD_NIL) {
	warn("Del_symbol_do_free", "Symbol %u not found\n", symbol);
	return ;
	}
	/* cut the node out of the hash chain; save the child. */
    this = *ip;
    *ip = tree->children[this].link;
    tree->children[this].link = CHILD_NIL;
    child = tree->children[this].ptr ;

    /*
     *		Decrement the symbol counts
     *		Avoid wrapping.
     */
    if (!tree->childsum) {
	warn("del_symbol_do_free", "Usage already zero\n");
    }
    if (tree->childsum < child->thevalue) {
	warn("del_symbol_do_free", "Usage (%u -= %u) would drop below zero\n", tree->childsum, child->thevalue );
	child->thevalue = tree->childsum;
    }
    tree->childsum -= child->thevalue;

    /* FIXME: we should also decrement the refcounts for the corresponding dict-entry.
    ** (but that would require access to the model->dict, and we should avoid the risk
    ** of creating stale pointers in model->context[order]
    */
    if (!tree->branch) {
	warn("del_symbol_do_free", "Branching already zero");
	goto kill;
    }
    top = --tree->branch;
    memstats.symdel += 1;
    if ( !top || top == this) {;}
    else {
	/* unlink top */
	ip = node_hnd(tree, tree->children[top].ptr->symbol);
	*ip = tree->children[top].link;
	tree->children[top].link = CHILD_NIL;
	/* now swap this and top */
	tree->children[this].ptr = tree->children[top].ptr;
	tree->children[top].ptr = NULL;
	
	/* relink into the hash chain */
	ip = node_hnd(tree, tree->children[this].ptr->symbol);
	*ip = this;
	}

	/* now this child needs to be abolished ... */
kill:
    free_tree_recursively(child);
    memstats.treedel += 1;
    /* fprintf(stderr, "Freed_tree() node_count now=%u treedel = %u\n",  memstats.node_cnt, memstats.treedel ); */
    if (!tree->branch || tree->msize - tree->branch >= sqrt( tree->branch)) {
#if (WANT_DUMP_ALZHEIMER_PROGRESS >= 2)
	status("Tree(%u/%u) will be shrunk: %u/%u\n"
		, tree->thevalue, tree->childsum, tree->branch, tree->msize);
#endif
		resize_tree(tree, tree->branch);
		}
}

void free_tree_recursively(TREE *tree)
{
unsigned index;

if (!tree) return;

    for (index= tree->branch; index--;	) {
        free_tree_recursively( tree->children[index].ptr );
        }
    free(tree->children);
    (void) dict_dec_ref(alz_dict, tree->symbol, 1, tree->thevalue);
    free(tree);
    memstats.node_cnt -= 1;
    memstats.free += 1;
}

/*---------------------------------------------------------------------------*/

STATIC TREE *find_symbol(TREE *node, WordNum symbol)
{
ChildIndex *ip;

ip = node_hnd(node, symbol);
if (!ip || *ip == CHILD_NIL) return NULL;

return node->children[*ip].ptr ;
}

/*---------------------------------------------------------------------------*/

STATIC TREE *find_symbol_add(TREE *node, WordNum symbol)
{
ChildIndex *ip;

ip = node_hnd(node, symbol);
if ( !ip || *ip == CHILD_NIL) { /* not found: create one */
    if (node->branch >= node->msize) {
        unsigned newsize ;
        newsize = node->branch+sqrt(1+node->branch);
        if (resize_tree(node, newsize)) {
                warn("Find_symbol_add", "resize failed; old=%u new=%u symbol=%u"
		, node->msize, newsize, symbol );
		return NULL;
		}
        /* after realloc ip might be stale: need to obtain a new one */
        ip = node_hnd(node, symbol);
        if ( !ip) {
            warn("Find_symbol_add", "Ip was NULL after resize, symbol=%u", symbol );
            return NULL;
            }
        if (*ip != CHILD_NIL) {
            warn("Find_symbol_add", "*Ip was not CHILD_NIL after resize, symbol=%u, *ip=%u", symbol, (unsigned) *ip );
            return NULL;
            }
	}
    *ip = node->branch++;
    node->children[ *ip ].ptr = node_new(0);
    node->children[ *ip ].ptr->symbol = symbol;
    }

    return node->children[ *ip ].ptr ;
}

STATIC int resize_tree(TREE *tree, unsigned newsize)
{
    ChildIndex item,slot;
    unsigned oldsize;
    struct treeslot *old;

    if (!tree) return -1;
/* fprintf(stderr, "resize_tree(%u/%u) %u\n", tree->branch,  tree->msize, newsize);*/
    old = tree->children;

    if (newsize) {
        tree->children = malloc(newsize * sizeof *tree->children );
        if (!tree->children) {
	    error("Resize_tree", "Unable to reallocate subtree.");
            tree->children = old;
	    return -1;
        }
    }
    else tree->children = NULL; /* old is freed anyway */
    oldsize = tree->msize ;
    tree->msize = newsize;
    if (tree->children && tree->msize) format_treeslots(tree->children, tree->msize);

#if WANT_DUMP_REHASH_TREE
	fprintf(stderr, "Old=%p:%u New=%p:%u Tree_resize(%u/%u)\n"
	, (void*) old, oldsize
	, (void*) tree->children, newsize
	, tree->branch,  tree->msize);
#endif /* WANT_DUMP_REHASH_TREE */

/* Now rebuild the hash table.
 * The hash-chain pointers have already been initialized to NIL,
 * we only have to copy the children's "payload" verbatim,
 * find the place where to append it in the hash-chain, and put it there.
 *
 * Since we need to rebuild the hash chains anyway, this is a good place to
 * sort the items (in descending order) to make life easier for babble() .
 * We only sort when the node is growing (newsize>oldsize), assuming ordering is more or less
 * fixed for aged nodes. FIXME
 */
    if (old) {
	    if (newsize > oldsize && tree->branch > 1) {
#if ( WANT_DUMP_ALZHEIMER_PROGRESS >= 2 || WANT_DUMP_REHASH_TREE)
		fprintf(stderr, "Resize:sort(Symbol=%u Cnt=%u) Old=%u New=%u Value=%u Childsum=%u\n"
		, tree->symbol, tree->branch
		, oldsize, newsize
		, tree->thevalue, tree->childsum);
#endif
		treeslots_sort(old, tree->branch );
		}

        for (item =0 ; item < tree->branch; item++) {
	ChildIndex *ip;
	slot = old[item].ptr->symbol % tree->msize;
	for( ip = &tree->children[slot].tabl; *ip != CHILD_NIL; ip = &tree->children[*ip].link ) {

#if (WANT_DUMP_REHASH_TREE >= 2)
		fprintf(stderr, "%u,", (unsigned) *ip);
#endif
		}
#if (WANT_DUMP_REHASH_TREE >= 2)
		fprintf(stderr, "Placing Item=%u Hash=%5u(%8x) Slot=%4u TargetSlot=%u (previous %u)\n"
		, (unsigned) item , (unsigned) old[item].ptr->symbol, (unsigned) old[item].ptr->symbol, (unsigned) slot
		, (unsigned) ((char*) ip - (char*) &tree->children[0].tabl) / sizeof tree->children[0]
		, (unsigned) *ip );
#endif
	*ip = item;
	tree->children[item].ptr = old[item].ptr;
	}
    free (old);
    }
    return 0; /* success */
}

STATIC void format_treeslots(struct treeslot *slots , unsigned size)
{
    unsigned idx;

    for (idx = 0; idx < size; idx++) {
	slots[idx].tabl = CHILD_NIL;
	slots[idx].link = CHILD_NIL;
	slots[idx].ptr = NULL;
	}
}


STATIC int treeslots_cmp(const void *vl, const void *vr)
{
const struct treeslot  *sl=vl;
const struct treeslot  *sr=vr;

if ( !sl->ptr && !sr->ptr) return 0;
if ( !sl->ptr ) return 1;
if ( !sr->ptr ) return -1;

if ( sl->ptr->thevalue < sr->ptr->thevalue ) return 1;
if ( sl->ptr->thevalue > sr->ptr->thevalue ) return -1;

if ( sl->ptr->symbol < sr->ptr->symbol ) return -1;
if ( sl->ptr->symbol > sr->ptr->symbol ) return 1;
return 0;
}

/* NOTE: quicksort is a bad choice here, since the childnodes are "almost sorted",
 * The sorting does not consume enough CPU to justify a mergesort or insertion sort variant.
 * (when training, qsort ate 10% CPU, most of it in the compare function)
 *
 * This is a "one pass bubblesort":
 * It will /eventually/ get the array sorted.
 * Having the array sorted is not that important: babble() may need only a few steps
 * extra on an almost sorted array.
 * treeslots_cmp(left,right) returns positive if left < right (which is the intended order)
 *
 * NOTE 2013-10-14 we start at the top of the array, since that is
 * where the new entries emerge and the old ones fade away.
 */

#if 0
STATIC void treeslots_sort(struct treeslot  *slots , unsigned count)
{
	qsort(slots, count, sizeof *slots, treeslots_cmp);
}
#else

STATIC void treeslots_sort(struct treeslot  *slots , unsigned count)
{
unsigned idx;
#if SORT_UP_WOULD_BE_OPTIMAL
for (idx = 1; idx < count; idx++) {
#else
for (idx = count; --idx > 0; ) {
#endif
	struct treeslot tmp;
	if (treeslots_cmp( &slots[idx-1], &slots[idx]) <= 0) continue;
	tmp = slots[idx];
	slots[idx] = slots[idx-1];
	slots[idx-1] = tmp;
	}
}

#endif

/*
** Find the place where the index to 'symbol' lives. (or should live)
**
** Profiling shows that node_hnd() is the biggest CPU consumer
** (unless Alzheimer kicks in ;-)
** I don't see a way to speed this thing up, apart from making it static.
*/
STATIC ChildIndex *node_hnd(TREE *node, WordNum symbol)
{
ChildIndex *ip;
unsigned slot;

if (!node->msize) return NULL;

	/* Symbol-numbers are considered uniform "random" enough
	** , so don't need hashing */
slot = symbol % node->msize;
for (ip = &node->children[ slot ].tabl; *ip != CHILD_NIL; ip = &node->children[ *ip ].link ) {
#if WANT_MAXIMAL_PARANOIA
	slot = *ip;
	if (!node->children[ *ip ].ptr) {
		warn ( "Node_hnd", "empty child looking for %u\n", symbol);
		continue;
		}
#endif
	if (symbol == node->children[ *ip ].ptr->symbol) return ip;
	}
return ip;
}
/*---------------------------------------------------------------------------*/

/*
 *		Function:	Initialize_Context
 *
 *		Purpose:		Set the context of the model to a default value.
 */
void initialize_context(MODEL *model)
{
    unsigned int iord;

    for (iord = 0; iord < 2+model->order; iord++) model->context[iord] = NULL;
    if (model->forward) model->forward->stamp = stamp_max;
    if (model->backward) model->backward->stamp = stamp_max;
}

STATIC double word_weight(DICT *dict, STRING word, int want_other)
{
WordNum *np, symbol;

np = dict_hnd(dict, word);

if (!np || *np == WORD_NIL) return 0.0;
symbol = *np;

return symbol_weight(dict, symbol, want_other);
}

STATIC double symbol_weight(DICT *dict, WordNum symbol, int want_other)
{
STRING alt;
WordNum *np, altsym;

if (!dict || symbol >= dict->size) return 0.0;

if (want_other) {
	alt = word_dup_othercase(dict->entry[symbol].string);
	np = dict_hnd(dict, alt);
	altsym = (np) ? *np : WORD_NIL;
	}
else altsym = WORD_NIL;

#if (WANT_DUMP_KEYWORD_WEIGHTS & 2)
fprintf(stderr, "Symbol %u/%u:%u ('%*.*s') %u/%llu\n"
        , symbol, (unsigned)dict->size, (unsigned)dict->stats.nonzero
	, (int)dict->entry[symbol].string.length, (int)dict->entry[symbol].string.length, (int)dict->entry[symbol].string.word
	, (unsigned)dict->entry[symbol].stats.valuesum
	, (unsigned long long)dict->stats.valuesum
	);
if (altsym != WORD_NIL) fprintf(stderr, "AltSym %u/%u:%u ('%*.*s') %u/%llu\n"
        , symbol, (unsigned)dict->size, (unsigned)dict->stats.nonzero
	, (int)dict->entry[altsym].string.length, (int)dict->entry[altsym].string.length, (int)dict->entry[altsym].string.word
	, (unsigned)dict->entry[altsym].stats.valuesum
	, (unsigned long long)dict->stats.valuesum
	);
#endif

	/* This is to catch and ignore typos.
	** Typos have an initial score of 2*(1+glob_order) 
	** will never get any hits, (and will decay soon)
	*/
#define TRESHOLD (2*(1+glob_order))
if (altsym==WORD_NIL) {
	if (dict->entry[symbol].stats.valuesum < TRESHOLD) return 0.00099;
	if (dict->entry[symbol].stats.nnode < TRESHOLD) return 0.00088;
	// 20150324
	if (dict->entry[symbol].string.ztype == TOKEN_ATAAP) return 0.00077;
	if (dict->entry[symbol].string.ztype == TOKEN_HEKHASH) return 0.00066;
	// 20120224
	// if (dict->entry[symbol].stats.valuesum == dict->entry[symbol].stats.nnode) return 0.00777;
#undef TRESHOLD
        return ((double)dict->stats.valuesum / dict->stats.nonzero)
		/ (0.5 + dict->entry[symbol].stats.valuesum)
		;
} else {
	return ((double)dict->stats.valuesum * 2 / dict->stats.nonzero)
		/ (0.5 + dict->entry[symbol].stats.valuesum + dict->entry[altsym].stats.valuesum)
		;
	}
}

STATIC STRING word_dup_othercase(STRING org)
{
static char zzz[1+STRLEN_MAX];
STRING new = {0,0,0,zzz};
unsigned ii,chg;

if (!org.ztype) org.ztype =  word_classify(org);
switch (org.ztype) {
case TOKEN_INITCAPS: return word_dup_lowercase(org);
case TOKEN_CAMEL: return word_dup_lowercase(org);
case TOKEN_UPPER: return word_dup_lowercase(org);
case TOKEN_LOWER: return word_dup_initcaps(org);
default: break;
	}

new.length = org.length;
for (chg=ii = 0; ii < org.length; ii++) { /* Attempt Initcaps */
	if (myislower( org.word[ii] ) && ii==0) { chg++; new.word[ii] = org.word[ii] - ('a' - 'A'); }
	else if (ii && chg) new.word[ii] = org.word[ii] + ('a' - 'A');
	else new.word[ii] = org.word[ii] ;
	}
if (!chg) for (chg=ii = 0; ii < org.length; ii++) { /* attempt all lowercase */
	if (myisupper( org.word[ii] )) { chg++; new.word[ii] = org.word[ii] + ('a' - 'A'); }
	else new.word[ii] = org.word[ii] ;
	}
if (!chg) for (chg=ii = 0; ii < org.length; ii++) { /* attempt all UPPERCASE */
	if (myislower( org.word[ii] )) { chg++; new.word[ii] = org.word[ii] - ('a' - 'A'); }
	else new.word[ii] = org.word[ii] ;
	}
return new;
}

STATIC STRING word_dup_lowercase(STRING org)
{
static char zzz[1+STRLEN_MAX];
STRING new = {0,0,0,zzz};
unsigned ii;

new.length = org.length;
new.ztype = TOKEN_LOWER;

for (ii = 0; ii < org.length; ii++) {
	if (myisupper( org.word[ii] )) new.word[ii] = org.word[ii] + ('a' - 'A');
	else new.word[ii] = org.word[ii] ;
	}
return new;
}

STATIC STRING word_dup_initcaps(STRING org)
{
static char zzz[1+STRLEN_MAX];
STRING new = {0,0,0,zzz};
unsigned ii;

new.length = org.length;
new.ztype = TOKEN_INITCAPS;

if (myislower( org.word[0] )) new.word[0] = org.word[0] - ('a' - 'A');
for (ii = 1; ii < org.length; ii++) {
	if (myisupper( org.word[ii] )) new.word[ii] = org.word[ii] + ('a' - 'A');
	else new.word[ii] = org.word[ii] ;
	}
return new;
}

STATIC int word_classify(STRING org)
{
unsigned ii;
unsigned upper=0, lower=0,number=0,high=0,other=0, initcaps=0, initaap=0, inithash=0;

if (!org.length) return 0; /* ajuus */
for (ii = 0; ii < org.length; ii++) {
	if (org.word[ii] >= 'A' && org.word[ii] <= 'Z' ) { if (ii) upper++; else initcaps++; }
	else if (org.word[ii] >= 'a' && org.word[ii] <= 'z' ) lower++;
	else if (org.word[ii] >= '0' && org.word[ii] <= '9' ) number++;
	else if (org.word[ii] & 0x80 ) high++;
	else if (org.word[ii] == '@' ) { if (ii) other++; else initaap++; }
	else if (org.word[ii] == '#' ) { if (ii) other++; else inithash++; }
	else other++;
	}
if (lower == ii) return TOKEN_LOWER; /* pvda */
if (upper+initcaps == ii) return TOKEN_UPPER; /* PVDA */
if (lower+initcaps == ii) return TOKEN_INITCAPS; /* Pvda */
if (lower+upper+initcaps == ii) return TOKEN_CAMEL; /* PvdA */
if (lower+upper+number+initaap == ii) return TOKEN_ATAAP; /* @PvdA */
if (lower+upper+number+inithash == ii) return TOKEN_HEKHASH; /* #PvdA */
if (other == ii) return TOKEN_PUNCT; /* ... */
if (lower+upper+initcaps+other == ii) return TOKEN_AFKO; /* P.v.d.A */
if (lower+upper+other+initcaps+number == ii) return TOKEN_NUMBER; /* P.v.d.6 */
return TOKEN_MISC;
}

/*
 *		Function:	Learn
 *
 *		Purpose:		Learn from the user's input.
 */
STATIC void learn_from_input(MODEL *model, struct sentence *words)
{
    unsigned widx;
    WordNum symbol;

    /*
     *		We only learn from inputs which are long enough
     *		We need N+1 words to feed a N-ary model.
     */
    if (words->mused <= model->order) return;
    stamp_max++;

#if ALZHEIMER_FACTOR
    { unsigned val;
    val = urnd(10*ALZHEIMER_FACTOR);
    if (val == ALZHEIMER_FACTOR/2) {
        initialize_context(model);
        model_alzheimer(model, ALZHEIMER_NODE_COUNT);
	}
    }
#endif
    /*
     *		Train the model in the forwards direction.  Start by initializing
     *		the context of the model.
     */
    initialize_context(model);
    model->context[0] = model->forward;
    for(widx = 0; widx < words->mused; widx++) {
	/*
	 *		Add the symbol to the model's dictionary if necessary, and then
	 *		update the forward model accordingly.
	 */
	symbol = add_word_dodup(model->dict, words->entry[widx].string );
	update_model(model, symbol);
        /* if (symbol <= 1 || !myisalnum(words->entry[widx].string.word[0])) stamp_max++; */
        if (widx % 64 == 63)  stamp_max++;
    }
    /*
     *		Add the sentence-terminating symbol.
     */
    update_model(model, WORD_FIN);

    /*
     *		Train the model in the backwards direction.  Start by initializing
     *		the context of the model.
     */
    initialize_context(model);
    model->context[0] = model->backward;
    for(widx = words->mused; widx-- > 0; ) {
	/*
	 *		Find the symbol in the model's dictionary, and then update
	 *		the backward model accordingly.
	 */
	symbol = find_word(model->dict, words->entry[widx].string );
	update_model(model, symbol);
    }
    /*
     *		Add the sentence-terminating symbol. (for the beginning of the sentence)
     */
    update_model(model, WORD_FIN);

    return;
}

/*---------------------------------------------------------------------------*/

/*
 *		Function:	Train
 *
 *		Purpose:		Infer a MegaHAL brain from the contents of a text file.
 */
STATIC void train(MODEL *model, char *filename)
{
    FILE *fp;
    static struct sentence *exercise = NULL;
    char buffer[4*1024];

    if (!filename) return;

    fp = fopen(filename, "r");
    if (!fp) {
	fprintf(stderr, "Unable to find the personality %s\n", filename);
	return;
    }

    if (!exercise) exercise = sentence_new();
    else exercise->mused = 0;
    

    while( fgets(buffer, sizeof buffer, fp) ) {
	if (buffer[0] == '#') continue;

	buffer[strlen(buffer)-1] ='\0';

	make_words(buffer, exercise);
	learn_from_input(model, exercise);


    }

    fclose(fp);
}

/*---------------------------------------------------------------------------*/

/*
 *		Function:	Show_Dictionary
 *
 *		Purpose:		Display the dictionary for training purposes.
 */
void show_dict(DICT *dict)
{
    unsigned int iwrd;
    FILE *fp;
    size_t hexlen;
    char hexdump[1024];
    char formatted[512];

    fp = fopen("megahal.dic", "w");
    if (!fp) {
	warn("show_dict", "Unable to open file: %s", "megahal.dic");
	return;
    }

fprintf(fp, "#Nnode\tnValue\tR(Nfrac/Vfrac)\tWord\t");
fprintf(fp, "# TotStats= %llu %llu Words= %lu/%lu Nonzero=%lu\n"
	, (unsigned long long) dict->stats.nnode, (unsigned long long) dict->stats.valuesum
	, (unsigned long) dict->size, (unsigned long) dict->msize, (unsigned long) dict->stats.nonzero );
    for(iwrd = 0; iwrd < dict->size; iwrd++) {
	    fprintf(fp, "%lu\t%lu\t(%6.4e / %6.4e)\t'%*.*s'"
		, (unsigned long) dict->entry[iwrd].stats.nnode, (unsigned long) dict->entry[iwrd].stats.valuesum
		, (double ) dict->entry[iwrd].stats.nnode * dict->stats.nonzero / dict->stats.nnode
		, (double ) dict->entry[iwrd].stats.valuesum * dict->stats.nonzero / dict->stats.valuesum
		, (int) dict->entry[iwrd].string.length, (int) dict->entry[iwrd].string.length, dict->entry[iwrd].string.word
		);
        if ( word_has_highbit(dict->entry[iwrd].string)) {
		hexlen = hexdump_string(hexdump, dict->entry[iwrd].string);
                decode_word(formatted, dict->entry[iwrd].string, (int) hexdump[hexlen+2] - '0');
		}
        else formatted[0] = hexdump[hexlen=0] = 0;
        fprintf(fp, " '%s' %s\n"
            , formatted
            , hexdump
		);
    }

    fclose(fp);
}

void read_dict_from_ascii(DICT *dict, char *name)
{
    FILE *fp;
    char buff[300];
    unsigned long int nnode,valuesum;
    int pos;
    size_t len;
    STRING word = {0,0,0,NULL};


    if (!dict) return;

    fp = fopen( name, "r");
    if (!fp) {
	warn("read_dict_from_ascii", "Unable to open file `%s'", name);
	return;
    }

while (fgets(buff, sizeof buff, fp)) {
	if (buff[0] == '#') continue;
	sscanf(buff, "%lu %lu\t%n",  &nnode, &valuesum,  &pos);
	pos += strcspn(buff+pos, "\t" );
	pos += 1;
        len = strcspn(buff+pos, "\n" );
        if (!len) continue;
        word.word= buff+pos;
        word.length = len;
        word.ztype = word_classify(word);
        add_word_dodup(dict, word);
    }
memstats.word_cnt = dict->size;

    fclose(fp);
}

/*---------------------------------------------------------------------------*/

/*
 *		Function:	Save_Model
 *
 *		Purpose:		Save the current state to a MegaHAL brain file.
 */
STATIC void save_model(char *modelname, MODEL *model)
{
    FILE *fp;
    static char *filename = NULL;
    unsigned forw,back;

    if (!glob_dirt ) {
	status ("Not dirty; not written" );
        goto skip;
        }
    filename = realloc(filename, strlen(glob_directory)+strlen(SEP)+12);
    if (!filename) error("save_model","Unable to allocate filename");

    show_dict(model->dict);
    if (!filename) return;

    alarm(0);
    sprintf(filename, "%s%smegahal.brn", glob_directory, SEP);
    fp = fopen(filename, "wb");
    if (!fp) {
	warn("save_model", "Unable to open file `%s'", filename);
	return;
    }

    memstats.node_cnt = 0;
    memstats.word_cnt = 0;
    fwrite(COOKIE, sizeof(char), strlen(COOKIE), fp);
    fwrite(&model->order, sizeof model->order, 1, fp);
    forw = save_tree(fp, model->forward);
    back = save_tree(fp, model->backward);
    save_dict(fp, model->dict);
    status("Glob_dirt=%d: Saved %lu(%lu+%lu) nodes, %u words.\n"
      , glob_dirt
      , memstats.node_cnt, forw, back
      , memstats.word_cnt);
    fclose(fp);
    
skip:
    close(glob_fd); glob_fd = -1;
}

/*---------------------------------------------------------------------------*/

/*
 *		Function:	Save_Tree
 *
 *		Purpose:		Save a tree structure to the specified file.
 */
STATIC unsigned save_tree(FILE *fp, TREE *node)
{
    static int level = 0;
    unsigned int ikid;
    unsigned count = 1;

    fwrite(&node->symbol, sizeof node->symbol, 1, fp);
    fwrite(&node->childsum, sizeof node->childsum, 1, fp);
    fwrite(&node->thevalue, sizeof node->thevalue, 1, fp);
    fwrite(&node->stamp, sizeof node->stamp, 1, fp);
    fwrite(&node->branch, sizeof node->branch, 1, fp);
    memstats.node_cnt++;
    for(ikid = 0; ikid < node->branch; ikid++) {
	level++;
	count += save_tree(fp, node->children[ikid].ptr );
	level--;
    }
    return count;
}

/*---------------------------------------------------------------------------*/

/*
 *		Function:	Load_Tree
 *
 *		Purpose:		Load a tree structure from the specified file.
 */
STATIC TREE * load_tree(FILE *fp)
{
    static int level = 0;
    unsigned int cidx;
    unsigned int symbol;
    unsigned long long int childsum;
    ChildIndex *ip;
    size_t kuttje;
    TREE this, *ptr;

    kuttje = fread(&this.symbol, sizeof this.symbol, 1, fp);
    if (level==0 && this.symbol==0) this.symbol=1;
    kuttje += fread(&this.childsum, sizeof this.childsum, 1, fp);
    kuttje += fread(&this.thevalue, sizeof this.thevalue, 1, fp);
    kuttje += fread(&this.stamp, sizeof this.stamp, 1, fp);
#if 0
    if ( this.stamp > stamp_max) stamp_max = this.stamp;
    else if ( this.stamp < stamp_min) stamp_min = this.stamp;
#else
	/* We allow the timestamp to fold around at 0xffffffff
	** -->> 0x00000001 will be *above* 0xffffffff ...
	** Current timestamp is 2386300 (2012-01-31) so this will probably never happen.
	*/
    if (stamp_min == stamp_max) { stamp_min = this.stamp; stamp_max = 1+ this.stamp;}
    else { int rc;
    rc = check_interval (stamp_min, stamp_max, this.stamp);
    switch (rc) {
        case STAMP_BELOW: stamp_min = this.stamp; break;
        case STAMP_ABOVE: stamp_max = this.stamp; break;
	case STAMP_INSIDE: break;
	default: error("load_tree", "Weird timestamp(%u,%u) +%u :%d", stamp_min, stamp_max, this.stamp, rc);
	}
    }
#endif
    kuttje += fread(&this.branch, sizeof this.branch, 1, fp);
    // if (this.branch == 0) return NULL;
    if (kuttje < 5) return NULL;

    ptr = node_new( this.branch );
    if (!ptr) {
	error("load_tree", "Unable to allocate subtree");
	return ptr;
    }
    ptr->symbol = this.symbol;
    ptr->childsum = this.childsum;
    ptr->thevalue = this.thevalue;
    ptr->stamp = this.stamp;
    ptr->branch = this.branch;
    /* ptr->children  and ptr->msize are set by node_new() */

    childsum = 0;
    for(cidx = 0; cidx < ptr->branch; cidx++) {
	level++;
	ptr->children[cidx].ptr = load_tree(fp);
	level--;

	if (ptr->children[cidx].ptr ) childsum += ptr->children[cidx].ptr->thevalue;
	symbol = ptr->children[cidx].ptr ? ptr->children[cidx].ptr->symbol: cidx;
	ip = node_hnd(ptr, symbol );
	if (ip) *ip = cidx;
    }
    if (childsum != ptr->childsum) {
		fprintf(stderr, "Oldvalue = %llu <- Newvalue= %llu\n"
		, (unsigned long long) ptr->childsum , (unsigned long long) childsum);
		ptr->childsum = childsum;
		}
return ptr;
}

/*---------------------------------------------------------------------------*/

/*
 *		Function:	Load_Model
 *
 *		Purpose:		Load a model into memory.
 */
STATIC int load_model(char *filename, MODEL *model)
{
    FILE *fp;
    char cookie[16];
    unsigned refcount;
    size_t kuttje;


    if (!filename) return -1;

    // fp = fopen(filename, "rb");
    fp = fopen(filename, "rb+"); //lockf needs write permission

    if (!fp) {
	warn("load_model", "Unable to open file `%s'", filename);
	return -1;
    }
    while (1) {
	int rc;
	if (glob_fd < 0) { rc = dup( fileno(fp) ); glob_fd = rc; }
	else rc = dup2( fileno(fp), glob_fd  );
	if (rc == -1) {
		rc = errno;
		warn("load_model", "Unable to dup2 file `%s' err=%d(%s) ", filename, rc, strerror(rc) );
		fclose (fp);
		return -1;
		}
		/* F_TLOCK locks, but returns -1 on failure */
	rc = lockf( glob_fd, F_TLOCK, sizeof cookie );
	if (!rc) break;
	rc = errno;
	warn("Load_model", "Unable to lock file `%s' err=%d(%s) ", filename, rc, strerror(rc) );
	sleep (5);
	}


    kuttje = fread(cookie, sizeof(char), strlen(COOKIE), fp);
    if (kuttje != strlen(COOKIE) ) {
	warn("Load_model", "Read %u/%u from '%s' : %d (%s)\n"
		, (unsigned) kuttje, (unsigned) strlen(COOKIE), filename
		, errno, strerror(errno)
		);
	exit(1);
	}
    if (memcmp(cookie, COOKIE, strlen(COOKIE)) ) {
	warn("Load_model", "File `%s' is not a Wakkerbot brain: coockie='%s' (expected '%s')"
		, filename , cookie,COOKIE);
	goto fail;
    }
    memstats.node_cnt = 0;
    memstats.word_cnt = 0;
    kuttje = fread(&model->order, sizeof model->order, 1, fp);
    status("Loading %s Order= %u\n", filename, (unsigned)model->order);
    if (model->order != glob_order) {
        model->order = glob_order;
        model->context = realloc(  model->context, (2+model->order) *sizeof *model->context);
        status("Set Order to %u\n", (unsigned)model->order);
	}
    status("Forward\n");
    model->forward = load_tree(fp);
    status("Backward\n");
    model->backward = load_tree(fp);
    status("Dict\n");
#if 1
    load_dict(fp, model->dict);
#else
    read_dict_from_ascii(model->dict, "megahal.dic" );
#endif
    refcount = set_dict_count(model);
    status("Loaded %lu Nodes, %u Words. Total Refcount= %u Maxnodes=%lu\n"
	, memstats.node_cnt,memstats.word_cnt, refcount, (unsigned long)ALZHEIMER_NODE_COUNT);
    status( "Stamp Min=%u Max=%u.\n", (unsigned long)stamp_min, (unsigned long)stamp_max);

    fclose(fp);
    lseek (glob_fd, 0, SEEK_SET );

    show_dict(model->dict);

#if ALZHEIMER_FACTOR
    while ( memstats.node_cnt > ALZHEIMER_NODE_COUNT) {
        model_alzheimer(model, ALZHEIMER_NODE_COUNT);
        }
#endif

    return 0;

fail:
    fclose(fp);
    return -1;
}

/*---------------------------------------------------------------------------*/

/*
 *    Function:   Make_Words
 *
 *    Purpose:    Break a string into an array of words,
 *	and put them into a dict, sequentially.
 *	NOTE No memory for the STRINGS is allocated: the DICT points to the input string.
 */
STATIC void make_words(char * src, struct sentence * target)
{
    size_t len, pos, chunk;
    STRING word ={0,0,0,NULL};
    static STRING period = {1,0,0, "." }  ;
    int state = 0; /* FIXME: this could be made static to allow for multi-line strings */

    target->mused = 0;
    len = strlen(src);
    if (!len) return;

    for(pos=0; pos < len ; pos += chunk) {

	chunk = tokenize(src+pos, &state);
        if (!chunk) { /* maybe we should reset state here ... */ pos++; continue; }
        if (chunk > STRLEN_MAX) {
            if (!buffer_is_usable(src+pos,chunk)) { continue; } /* ignore large stretches of WS */
            warn( "Make_words", "Truncated too long string(%u) at %s\n"
		, (unsigned) chunk, src+pos);
            chunk = STRLEN_MAX;
            }
        if (buffer_is_usable(src+pos,chunk)) {
            word.word = src+pos;
            word.length = chunk;
	    add_word_to_sentence(target, word);
	    }

        // if (pos+chunk >= len) break;
    }
    memstats.tokens_read += target->mused;

    /*
     *		If the last word isn't punctuation, then add a full-stop character.
     */
    if (target->mused && myisalnum(target->entry[target->mused-1].string.word[0])) {
		add_word_to_sentence(target, period);
    }
    else if (target->mused
		&& target->entry[target->mused-1].string.length
		 && !strchr(".!?", target->entry[target->mused-1].string.word[ target->entry[target->mused-1].string.length-1] )) {
	target->entry[target->mused-1].string = period;
    }

    return;
}
/*---------------------------------------------------------------------------*/
/*
 *		Function:	Tokenize
 *
 *		Purpose:		Find the length of the token started @ string
 * This tokeniser attempts to respect abbreviations such as R.W.A or R.w.a.
 * Also, numeric literals, such as 200.50 are left alone (almost the same for 200,50 or 200.000,00)
 * Maybe 10e-0.6 should also be recognised.
 * Multiple stretches of .,!? are kept intact, multiple stretches of
 * other non alphanumerc tokens (@#$%^&*) as well.
 * Brackets and braces are always chopped up to 1-character tokens.
 * Quoted strings are not respected, but broken up into separate tokens.
 * The quotes are treated as separate tokens too.
 */
#define T_INIT 0
#define T_ANY 1
#define T_WORD 2
#define T_WORDDOT 3
#define T_WORDDOTLET 4
#define T_AFKODOT 5
#define T_AFKO 6
#define T_NUM 7
#define T_NUMDOT 8
#define T_NUMDOTLET 9
#define T_MEUK 10
#define T_PUNCT 11
#define T_ATHASH 12
STATIC size_t tokenize(char *str, int *sp)
{
    size_t pos ;

    for(pos=0; str[pos]; ) {
    switch(*sp) {
    case T_INIT: /* initial */
#if 0
	/* if (str[pos] == '\'' ) { *sp |= 16; return pos; }*/
	/* if (str[posi] == '"' ) { *sp |= 32; return pos; }*/
#endif
	if (myisalpha(str[pos])) {*sp = T_WORD; pos++; continue; }
	if (myisalnum(str[pos])) {*sp = T_NUM; pos++; continue; }
	if (strspn(str+pos, "#@")) { *sp = T_ATHASH; pos++; continue; }
	/* if (strspn(str+pos, "-+")) { *sp = T_NUM; pos++; continue; }*/
	*sp = T_ANY; continue;
	break;
    case T_ANY: /* either whitespace or meuk: eat it */
	pos += strspn(str+pos, " \t\n\r\f\b" );
	if (pos) {*sp = T_INIT; return pos; }
        *sp = T_MEUK; continue;
        break;
    case T_WORD: /* inside word */
	while ( myisalnum(str[pos]) ) pos++;
	if (str[pos] == '\0' ) { *sp = T_INIT;return pos; }
	if (str[pos] == '.' ) { *sp = T_WORDDOT; pos++; continue; }
	*sp = T_INIT; return pos;
        break;
    case T_WORDDOT: /* word. */
	if (myisalpha(str[pos]) ) { *sp = T_WORDDOTLET; pos++; continue; }
	*sp = T_INIT; return pos-1;
        break;
    case T_WORDDOTLET: /* word.A */
	if (str[pos] == '.') { *sp = T_AFKODOT; pos++; continue; }
	if (myisalpha(str[pos]) ) { *sp = T_INIT; return pos-2; }
	if (myisalnum(str[pos]) ) { *sp = T_NUM; continue; }
	*sp = T_INIT; return pos-2;
        break;
    case T_AFKODOT: /* A.B. */
        if (myisalpha(str[pos]) ) { *sp = T_AFKO; pos++; continue; }
        *sp = T_INIT; return pos >= 3 ? pos : pos -2;
        break;
    case T_AFKO: /* word.A.B */
	if (str[pos] == '.') { *sp = T_AFKODOT; pos++; continue; }
	if (myisalpha(str[pos]) ) { *sp = T_INIT; return pos - 2; }
	*sp = T_INIT; return pos-1;
        break;
    case T_NUM: /* number */
	if ( myisalnum(str[pos]) ) { pos++; continue; }
	if (strspn(str+pos, ".,")) { *sp = T_NUMDOT; pos++; continue; }
	*sp = T_INIT; return pos;
        break;
    case T_NUMDOT: /* number[.,] */
	if (myisalpha(str[pos])) { *sp = T_NUMDOTLET; pos++; continue; }
	if (myisalnum(str[pos])) { *sp = T_NUM; pos++; continue; }
	if (strspn(str+pos, "-+")) { *sp = T_NUM; pos++; continue; }
	*sp = T_INIT; return pos-1;
        break;
    case T_NUMDOTLET: /* number[.,][a-z] */
	if (myisalpha(str[pos])) { *sp = T_INIT; return pos-2; }
	if (myisalnum(str[pos])) { *sp = T_NUM; pos++; continue; }
	*sp = T_INIT; return pos-2;
        break;
    case T_MEUK: /* inside meuk */
	if (myisalnum(str[pos])) {*sp = T_INIT; return pos; }
	if (myiswhite(str[pos])) {*sp = T_INIT; return pos; }
	if (strspn(str+pos, ".,?!" )) { if (!pos) *sp = T_PUNCT; else { *sp = T_INIT; return pos; }}
	if (strspn(str+pos, "@'\"" )) { *sp = T_INIT; return pos ? pos : 1; }
	if (strspn(str+pos, ":;" )) { *sp = T_INIT; return pos ? pos : 1; }
	if (strspn(str+pos, "('\"){}[]" )) { *sp = T_INIT; return pos ? pos : 1; }
	pos++; continue; /* collect all garbage */
        break;
    case T_PUNCT: /* punctuation */
	if (strspn(str+pos, "@#" )) { *sp = T_MEUK; pos++; continue; }
	pos += strspn(str+pos, ".,?!" ) ;
        *sp = T_INIT; return pos ? pos : 1;
        break;
    case T_ATHASH: /* @ or # should be followed by an "identifier"  */
	while ( myisalpha(str[pos]) ) pos++;
	if (pos  < 2)  { *sp = T_MEUK; continue; }
        while ( myisalnum_extra(str[pos]) ) {pos++; }
	*sp = T_INIT;
	return pos ;
        }
    }
    /* This is ugly. Depending on the state,
    ** we need to know how many lookahead chars we consumed */
    switch (*sp) {
    case T_INIT: break;
    case T_ANY: break;
    case T_WORD: break;
    case T_WORDDOT: pos -= 1; break;
    case T_WORDDOTLET: pos -= 2; break;
    case T_AFKODOT: if (pos < 3) pos -= 2; break;
    case T_AFKO: break;
    case T_NUM: break;
    case T_NUMDOT: pos-= 1; break;
    case T_NUMDOTLET: pos -= 2; break;
    case T_MEUK: break;
    case T_PUNCT: break;
    case T_ATHASH: break;
    default: break;
    }
    *sp = T_INIT; return pos;
}

STATIC int myisupper(int ch)
{
if (ch >= 'A' && ch <= 'Z') return 1;
else return 0;
}

STATIC int myislower(int ch)
{
if (ch >= 'a' && ch <= 'z') return 1;
else return 0;
}

STATIC int myisalnum(int ch)
{
int ret = myisalpha(ch);
if (ret) return ret;
if (ch >= '0' && ch <= '9') return 1;
return 0;
}

STATIC int myisalnum_extra(int ch)
{
int ret = myisalnum(ch);
if (ret) return ret;
if (ch == '_' || ch == '$') return 1;
return 0;
}

STATIC int myisalpha(int ch)
{
if (myislower(ch) || myisupper(ch)) return 1;
	/* don't parse, just assume valid utf8*/
if (ch & 0x80) return 1;
return 0;
}

STATIC int myiswhite(int ch)
{
if (ch == ' ') return 1;
if (ch == '\t') return 1;
if (ch == '\n') return 1;
if (ch == '\r') return 1;
if (ch == '\f') return 1;
return 0;
}

STATIC int word_is_allcaps(STRING string)
{
unsigned idx, nupp=0, nlow=0, noth=0;

for(idx = 0; idx < string.length; idx++) {
	if (myisupper(string.word[idx])) nupp++;
	else if (myislower(string.word[idx])) nlow++;
	else noth++;
	}
if (nlow || noth) return 0;
else return 1;
}

STATIC int buffer_is_usable(char *buf, unsigned len)
{
unsigned idx;

if (len < 1) return 1;

for(idx = 0; idx < len; idx++) switch( buf[idx] ) {
	case ' ':
	case '\t':
	case '\n':
	case '\r':
	case '\0': continue;
	default: return 1;
	}
return 0;
}

STATIC int word_has_highbit(STRING string)
{
unsigned idx;

if (string.length < 1) return 0;

for(idx = 0; idx < string.length; idx++) {
	if ( string.word[idx] & 0x80) return 1;
	}
return 0;
}

/*
** These functions should more or less match with the tokeniser.
** The most important shared logic is that - " '
** should always be separate (single character) tokens
** ; except when used in decimal numerics.
** Also, "()[]{}" should be kept separate 1char tokens.
*/
STATIC int dont_need_white_l(STRING string)
{
unsigned idx;

for(idx = 0; idx < string.length; idx++) switch( string.word[idx] ) {
	case '.':
	case ',':
		if (idx) continue; /* this is because dot and comma can occur in decimal numerics */
	case ':':
	case ';':
	case '?':
	case '!':
	case ']':
	case ')':
	case '}':
	case '&':
	case '*':
	case '/':
	case '%':
		return 1;
	default: continue;
	}
return 0;
}

STATIC int dont_need_white_r(STRING string)
{
unsigned idx;

for(idx = 0; idx < string.length; idx++) switch( string.word[idx] ) {
	case '[':
	case '(':
	case '{':
	case '&':
	case '-':
	case '+':
	case '*':
	case '/':
		return 1;
	default: continue;
	}
return 0;
}
void show_config(FILE *fp)
{
    fprintf(fp, "[Pid=%d]Compiled-in constant settings:\n", getpid() );
    fprintf(fp, "NODE_COUNT=%d\n", NODE_COUNT);
    fprintf(fp, "ALZHEIMER_NODE_COUNT=%d\n", ALZHEIMER_NODE_COUNT);
    fprintf(fp, "MIN_REPLY_SIZE=%d\n", MIN_REPLY_SIZE);
    fprintf(fp, "INTENDED_REPLY_SIZE=%d\n", INTENDED_REPLY_SIZE);
    fprintf(fp, "MAX_REPLY_CHARS=%d\n", MAX_REPLY_CHARS);
    fprintf(fp, "STOP_WORD_TRESHOLD=%f\n", STOP_WORD_TRESHOLD);
    fprintf(fp, "WANT_KEYWORD_WEIGHTS=%d\n", WANT_KEYWORD_WEIGHTS);
    fprintf(fp, "CROSS_TAB_FRAC=%f\n", CROSS_TAB_FRAC);
    fprintf(fp, "CROSS_DICT_SIZE_MIN=%d\n", CROSS_DICT_SIZE_MIN);
    fprintf(fp, "CROSS_DICT_SIZE_MAX=%d\n", CROSS_DICT_SIZE_MAX);
    fprintf(fp, "CROSS_DICT_WORD_DISTANCE=%d\n", CROSS_DICT_WORD_DISTANCE);
    fprintf(fp, "WANT_TWO_PARROTS=yes\n");
    fprintf(fp, "WANT_PARROT_CHECK=%d\n", WANT_PARROT_CHECK);
    fprintf(fp, "PARROT_POWER=%f\n", PARROT_POWER);
    fprintf(fp, "OVERSIZE_PENALTY_POWER=%f\n", OVERSIZE_PENALTY_POWER);
    fprintf(fp, "UNDERSIZE_PENALTY_POWER=%f\n", UNDERSIZE_PENALTY_POWER);
}
/*---------------------------------------------------------------------------*/
/*
 *    Function:   Generate_Reply
 *
 *    Purpose:    Take a string of user input and return a string of output
 *                which may vaguely be construed as containing a reply to
 *                whatever is in the input string.
 */
void check_entropy(void)
{
double quality5, quality10;
unsigned five[] = {1,1,1,1,1};
unsigned six[] = {1,1,1,1,1,1};
unsigned ten[] = {1,1,1,1,1,1,1,1,1,1};
unsigned eleven[] = {1,1,1,1,1,1,1,1,1,1,1};

quality5 = penalize_both_parrots(five, six, 5 );
quality10 = penalize_both_parrots(ten, eleven, 10 );

fprintf(stderr, "*** quality5=%f quality10=%f\n", quality5, quality10 );
}

STATIC char *generate_reply(MODEL *model, struct sentence *src)
{
    static char *output_none = "Geert! doe er wat aan!" ;
	/* "I don't know enough to answer you yet!"; */
    struct sentence *zeresult;
    double rawsurprise, surprise, max_surprise;
    char *output;
    unsigned count;
    int basetime;
    double penalty, quality;

    // check_entropy();
    /* show_config(stderr); */

#if ALZHEIMER_FACTOR
    count = urnd(ALZHEIMER_FACTOR);
    if (count == ALZHEIMER_FACTOR/2) {
        initialize_context(model);
        model_alzheimer(model, ALZHEIMER_NODE_COUNT);
	}
#endif
    initialize_context(model);
    /*
     *		Create an array of keywords from the words in the user's input
     */
    make_keywords(model, src);
    output = output_none;

    max_surprise = -100.0;
    quality = penalty = 0.0;
    count = 0;
    basetime = time(NULL);
    do {
	zeresult = one_reply(model);
	rawsurprise = evaluate_reply(model, zeresult);
	count++;
#if WANT_PARROT_CHECK
	/* I'm not dead yet ... */
#if 0
	penalty = penalize_two_parrots(parrot_hash, parrot_hash2, COUNTOF(parrot_hash) );
        surprise = rawsurprise / penalty ;
#else
	
	// quality = penalize_one_parrot(parrot_hash, COUNTOF(parrot_hash) );
	quality = penalize_both_parrots(parrot_hash, parrot_hash2, COUNTOF(parrot_hash) );
	if (penalty/quality > 1.1) continue; /* too nuch decrease */
        surprise = rawsurprise * quality ;
#endif
        if ( (surprise - max_surprise) <= (10*DBL_EPSILON) ) continue;

#endif /* WANT_PARROT_CHECK */

#if WANT_PARROT_CHECK
{
    unsigned pidx;
    fprintf(stderr, "\nParrot1={" );
    for (pidx=0; pidx < COUNTOF(parrot_hash); pidx++) { fprintf(stderr, " %u", parrot_hash[ pidx] ); }
    fprintf(stderr, "} quality=%f\n", quality );

    fprintf(stderr, "Parrot2={" );
    for (pidx=0; pidx < COUNTOF(parrot_hash2); pidx++) { fprintf(stderr, " %u", parrot_hash2[ pidx] ); }
    fprintf(stderr, "}\n" );

    fprintf(stderr, "Penal= %f Raw=%f, Max=%f, Surp=%f"
    , penalty, rawsurprise, max_surprise, surprise);

}
#endif /* WANT_PARROT_CHECK */
	penalty = quality;
	max_surprise = surprise;
	output = make_output(zeresult);
#if WANT_DUMP_ALL_REPLIES
{
	fprintf(stderr, "\n%u %f N=%u:%u/%u (Typ=%d Fwd=%f Rev=%f):\n\t%s\n"
	, count, surprise
	, (unsigned) zeresult->mused, (unsigned int) strlen(output), zeresult->kwhit
	, init_typ_fwd, init_val_fwd, init_val_rev
	, output);
}
#endif
    if (signal_caught) {
		fprintf(stderr, "\n*** Timer eleapsed signal=%d\n", signal_caught);
		break;
		}
    } while(time(NULL)-basetime < glob_timeout);

    alarm(0);

#if WANT_DUMP_ALL_REPLIES
	fprintf(stderr, "ReplyProbed=%u cross_dict_size=%u\n"
	, count, cross_dict_size );
#endif

    /*
     *		Return the best answer we generated
     */
    return output;
}

/*---------------------------------------------------------------------------*/

STATIC void make_keywords(MODEL *model, struct sentence *src)
{
    unsigned int iwrd;
    WordNum symbol;

    STRING canonword;
    WordNum canonsym;
    /* array for retaining the sliding WINDOW[distance] with previous words. */
    WordNum echobox[CROSS_DICT_WORD_DISTANCE] = {0,};
    unsigned rotor,echocount;
    unsigned oldsize, other;

    if (!src->mused) return;
    oldsize = cross_dict_size ;
    cross_dict_size = sqrt(src->mused);
    if (cross_dict_size < CROSS_DICT_SIZE_MIN) cross_dict_size = CROSS_DICT_SIZE_MIN ;
    if (cross_dict_size > CROSS_DICT_SIZE_MAX) cross_dict_size = CROSS_DICT_SIZE_MAX ;

    fprintf(stderr, "Make_keywords: Old xdict=%u, src->mused =%u Newsize=%u\n", oldsize, src->mused, cross_dict_size);

#if 1 /* FIXME resize instead of free+alloc*/
    if (glob_crosstab) crosstab_resize(glob_crosstab,cross_dict_size);
    else glob_crosstab = crosstab_init(cross_dict_size);
#else
    if (glob_crosstab) crosstab_free(glob_crosstab);
    glob_crosstab = crosstab_init(cross_dict_size);
#endif
    rotor = echocount = 0;

    for(iwrd = 0; iwrd < src->mused; iwrd++) {
	/*
	 *		Find the symbol ID of the word.  If it doesn't exist in
	 *		the model, or if it begins with a non-alphanumeric
	 *		character, or if it is in the exclusion array, then
	 *		skip over it.
	 */
	if (!myisalnum(src->entry[iwrd].string.word[0] )) continue;
	/* if (word_is_allcaps(words->entry[iwrd].string)) continue;*/
        symbol = find_word(model->dict, src->entry[iwrd].string );
        if (symbol == WORD_NIL) continue;
        // if (symbol == WORD_ERR) continue;
        // if (symbol == WORD_FIN) continue;
        if (symbol >= model->dict->size) continue;

		/* we may or may not like frequent words */
	/* 20120119:i We use the wordweight of the canonical form */
	canonword = word_dup_lowercase(model->dict->entry[symbol].string);
	canonsym = find_word( model->dict, canonword);
        if (canonsym >= model->dict->size) canonsym = symbol;
	if (symbol_weight(model->dict, canonsym, 0) < STOP_WORD_TRESHOLD) continue;

	for (other = 0; other < echocount; other++ ) {
		unsigned dist;
		dist = other > rotor ? (other - rotor) : (other+CROSS_DICT_WORD_DISTANCE -rotor);

		crosstab_add_pair( glob_crosstab, echobox[other] , canonsym, 1+CROSS_DICT_WORD_DISTANCE-dist );
		}
	if (echocount < COUNTOF(echobox)) echocount++;
	echobox[rotor] = canonsym;
	if (++rotor >= COUNTOF(echobox)) rotor =0;
	}

#if CROSS_DICT_SIZE
	crosstab_show(stderr, glob_crosstab, symbol_format_callback, symbol_weight_callback);
        /* NOTE: the callbacks set .zflag */
#endif
}

/*---------------------------------------------------------------------------*/

STATIC struct sentence *one_reply(MODEL *model)
{
    static struct sentence *zereply = NULL; /* NOTE: static variable */
    unsigned int widx;
    WordNum symbol;

    if (!zereply) zereply = sentence_new();
    else zereply->mused = 0;

    /*
     *		Start off by making sure that the model's context is empty.
     */
    initialize_context(model);
    model->context[0] = model->forward;

    /*
     *		Generate the reply in the forward direction.
     */
    for (symbol = seed(model); symbol > WORD_FIN ; symbol = babble(model, zereply) ) {
	/*
	 *		Append the symbol to the reply sentence.
	 */
	add_word_to_sentence(zereply, model->dict->entry[symbol].string );
	/*
	 *		Extend the current context of the model with the current symbol.
	 */
	update_context(model, symbol);
    }

    /*
     *		Start off by making sure that the model's context is empty.
     */
    initialize_context(model);
    model->context[0] = model->backward;

    /*
     *		Re-create the context of the model from the current reply
     *		sentence so that we can generate backwards to reach the
     *		beginning of the string.
     */
    for(widx = MIN(zereply->mused, 1+model->order); widx-- > 0; ) {
	symbol = find_word(model->dict, zereply->entry[ widx ].string );
	update_context(model, symbol);
    }

    /*
     *		Generate the reply in the backward direction.
     */
    sentence_reverse(zereply);
    while(1) {
	symbol = babble(model, zereply);
	if (symbol <= WORD_FIN) break;

	add_word_to_sentence(zereply, model->dict->entry[symbol].string );

	update_context(model, symbol);
    }
    sentence_reverse(zereply);

    return zereply;
}

/*---------------------------------------------------------------------------*/

/*
 *		Function:	Evaluate_Reply
 *
 *		Purpose:		Measure the average surprise of keywords relative to the
 *						language model.
 */
STATIC double evaluate_reply(MODEL *model, struct sentence *de_zin)
{
    unsigned int widx, iord, count, totcount, kwhit;
    WordNum symbol, canonsym;
    double gfrac, kfrac, weight,term,probability, entropy;
    TREE *node=NULL;
    STRING canonword;
    unsigned tweetsize=0;

    if (de_zin->mused == 0) return -100000.0;

    initialize_context(model);
    model->context[0] = model->forward;

#if WANT_PARROT_CHECK
	PARROT_RESURRECT(0);
#endif /* WANT_PARROT_CHECK */

    kwhit = totcount = 0, entropy = 0.0;
    for (widx = 0; widx < de_zin->mused; widx++) {
	tweetsize += 1+de_zin->entry[widx].string.length;

	symbol = find_word(model->dict, de_zin->entry[widx].string );
	if (symbol >= model->dict->msize) continue;
	/* Only crosstab-keywords contribute to the scoring
	*/
	canonword = word_dup_lowercase(model->dict->entry[symbol].string);
	canonsym = find_word( model->dict, canonword);
        if (canonsym >= model->dict->size) canonsym = symbol;
#if 1
	kfrac = crosstab_ask(glob_crosstab, canonsym);
	// if (kfrac < CROSS_TAB_FRAC / (cross_dict_size) ) goto update1;
	// if (kfrac < CROSS_TAB_FRAC ) goto update1;
	if (kfrac < CROSS_TAB_FRAC / sqrt(cross_dict_size) ) goto update1;
	if (model->dict->entry[symbol].string.zflag ) kwhit++;
	// else goto update1;
	else kfrac = 1.0 / de_zin->mused;
#else
#endif
	probability = 0.0;
        count = 0;
        totcount++;
        for(iord = 0; iord <= model->order; iord++) {
            if ( !model->context[iord] ) continue;
            node = find_symbol(model->context[iord], symbol);
            if (!node) continue;
            // if (!count++) kwhit++;
            count++;
		/* too unique: don't count them */
            /* if (node->thevalue < 2) continue; 20131207 */
            if (node->thevalue < 1) continue; 
            probability += (0.1+node->thevalue) / (0.1 + model->context[iord]->childsum);
            }
        if (!count) goto update1;
        if (!(probability > 0.0)) goto update1;

        term = (double) probability / count;
#if WANT_KEYWORD_WEIGHTS
        gfrac = symbol_weight(model->dict, symbol, 0);
        weight = kfrac * log(1.0+gfrac);
        entropy -= weight * log(term);
#else
        gfrac = weight = 1.0;
        entropy -= log(term);
#endif

#if (WANT_DUMP_KEYWORD_WEIGHTS & 1)
fprintf(stderr, "#### '%*.*s'\n"
"Valsum=%9lu/%9llu Nnode=%9lu/%9llu\n"
"Gfrac=%6.4e Kfrac=%6.4e W=%6.4e\n"
"Prob=%6.4e/Cnt=%u/%u:=Term=%6.4e w*log(Term)=%6.4e Entr=%6.4e\n"
        , (int) de_zin->entry[widx].string.length
        , (int) de_zin->entry[widx].string.length
        , de_zin->entry[widx].string.word
        , (unsigned long) model->dict->entry[symbol].stats.valuesum
        , (unsigned long long) model->dict->stats.valuesum
        , (unsigned long) model->dict->entry[symbol].stats.nnode
        , (unsigned long long) model->dict->stats.nnode
        , gfrac, kfrac, weight
        , probability , count, kwhit
        , (double) term
        , (double) weight * log( term )
        , (double) entropy
        );
#endif
update1:
        update_context(model, symbol);
#if WANT_PARROT_CHECK
        for(iord = model->order+2; iord-- > 0; ) {
	   node = model->context[iord] ;
           if (node) break;
           }
	if (node) { PARROT_ADD(node->stamp); }
#endif /* WANT_PARROT_CHECK */
	} /* For-loop */

#if (WANT_DUMP_KEYWORD_WEIGHTS & 1)
fprintf(stderr, "####[%u] =%6.4f\n", widx,(double) entropy
	);
#endif

    initialize_context(model);
    model->context[0] = model->backward;

    for(widx = de_zin->mused; widx-- > 0; ) {
	symbol = find_word(model->dict, de_zin->entry[widx].string );
	if (symbol >= model->dict->msize) continue;
	canonword = word_dup_lowercase(model->dict->entry[symbol].string);
	canonsym = find_word( model->dict, canonword);
        if (canonsym >= model->dict->size) canonsym = symbol;
#if 1
	kfrac = crosstab_ask(glob_crosstab, canonsym);
	// if (kfrac < CROSS_TAB_FRAC / (cross_dict_size) ) goto update2;
	// if (kfrac < CROSS_TAB_FRAC ) goto update2;
	if (kfrac < CROSS_TAB_FRAC / sqrt(cross_dict_size) ) goto update2;
	if (model->dict->entry[symbol].string.zflag ) kwhit++;
	else kfrac = 1.0 / de_zin->mused;
	// else goto update2;
#else
	kfrac = model->dict->entry[symbol].string.zflag ? 0.1 : 0.01;
#endif
        probability = 0.0;
        count = 0;
        totcount++;
        for(iord = 0; iord <= model->order; iord++) {
            if ( !model->context[iord] ) continue;
            node = find_symbol(model->context[iord], symbol);
            if (!node) continue;
            // if (!count++) kwhit++;
            count++;
            /* if (node->thevalue < 2) continue; Too unique */
            if (node->thevalue < 1) continue; /* Too unique */
            probability += (0.1+node->thevalue) / (0.1 + model->context[iord]->childsum);
        }

        if ( !count ) goto update2;
        if (!(probability > 0.0)) goto update2;

        term = (double) probability / count;
#if WANT_KEYWORD_WEIGHTS
        gfrac = symbol_weight(model->dict, symbol, 0);
        weight = kfrac * log(1.0+gfrac);
        entropy -= weight * log(term);
#else
        gfrac = weight = 1.0;
        entropy -= log(term);
#endif

#if (WANT_DUMP_KEYWORD_WEIGHTS & 1)
fprintf(stderr, "#### Rev '%*.*s'\n"
"Valsum=%9lu/%9llu Nnode=%9lu/%9llu\n"
"Gfrac=%6.4e Kfrac=%6.4e W=%6.4e\n"
"Prob=%6.4e/Cnt=%u/%u:=Term=%6.4e w*log(Term)=%6.4e Entr=%6.4e\n"
        , (int) de_zin->entry[widx].string.length
        , (int) de_zin->entry[widx].string.length
        , de_zin->entry[widx].string.word
        , (unsigned long) model->dict->entry[symbol].stats.valuesum
        , (unsigned long long) model->dict->stats.valuesum
        , (unsigned long) model->dict->entry[symbol].stats.nnode
        , (unsigned long long) model->dict->stats.nnode
        , gfrac, kfrac, weight
        , probability , count, kwhit
        , (double) term
        , (double) weight * log( term )
        , (double) entropy
        );
#endif
update2:
        update_context(model, symbol);
#if WANT_PARROT_CHECK
        for(iord = model->order+2; iord-- > 0; ) {
	    node = model->context[iord] ;
           if (node) break;
           }
	if (node) PARROT_ADD(node->stamp);
#endif /* WANT_PARROT_CHECK */
    }
#if (WANT_DUMP_KEYWORD_WEIGHTS & 1)
fprintf(stderr, "####[both] =%6.4f\n", (double) entropy
	);
#endif

    /* if (totcount >= 8) entropy /= sqrt(totcount-1); */
    /* if (totcount >= 16) entropy /= totcount;*/
    if (totcount >= (MIN_REPLY_SIZE/4)) entropy /= sqrt(totcount);
    if (totcount >= (MIN_REPLY_SIZE/2)) entropy /= totcount;


	/* extra penalty for sentences that are too long */
	/* extra penalty for sentences that don't start at <END> or don't stop at <END> */
	/* extra penalty for sentences that don't start with a capitalized letter */
	/* extra penalty for incomplete sentences */
    widx = de_zin->mused;
    if (widx && widx != INTENDED_REPLY_SIZE) {
#if 1
	if (widx > INTENDED_REPLY_SIZE) {
		entropy /= pow((1.0* widx) / INTENDED_REPLY_SIZE, OVERSIZE_PENALTY_POWER);
		}
	else	{
		entropy /= pow ((0.0+INTENDED_REPLY_SIZE) / widx , UNDERSIZE_PENALTY_POWER);
		}
#endif
        if (tweetsize >= MAX_REPLY_CHARS) entropy /= 10;
	init_val_fwd = start_penalty(model, de_zin->entry[0].string);
	init_val_rev = end_penalty(model, de_zin->entry[widx-1].string );
        entropy -= sqrt(init_val_fwd);
        entropy -= sqrt(init_val_rev);
	entropy *= sqrt(1+kwhit);
	}
#if (WANT_DUMP_KEYWORD_WEIGHTS & 1)
fprintf(stderr, "####[Corrected] =%6.4f\n", (double) entropy
	);
#endif
    de_zin->kwhit = kwhit;
    return entropy;
}

/*---------------------------------------------------------------------------*/

STATIC char *make_output(struct sentence *src)
{
    static char *output = NULL;
    unsigned int widx;
    size_t length;
    char *output_none = "I am utterly speechless!";
    char *tags;
    unsigned int sqcnt=0, dqcnt=0, hycnt=0;
    int begin;


    if (src->mused == 0) { return output_none; }
	/* calculate the space we'll need.
	** We assume one space between adjacent wordst plus a NUL at the end.
	*/
    length = 1;
    for(widx = 0; widx < src->mused; widx++) length += 1+ src->entry[widx].string.length;
    output = realloc(output, length);
    if (!output) {
	error("make_output", "Unable to reallocate output.");
	return output_none;
    }

    tags = malloc(2+src->mused);
    if (tags) memset(tags, 0, src->mused);
#define NO_SPACE_L 1
#define NO_SPACE_R 2
#define IS_SINGLE 4
#define IS_DOUBLE 8
#define IS_HYPHEN 16

	/* do we want a white before or after the token at [widx] ? */
    for(widx = 0; widx < src->mused; widx++) {
	if (!widx		|| dont_need_white_l(src->entry[widx].string)) tags[widx] |= NO_SPACE_L;
	if (widx == src->mused-1	|| dont_need_white_r(src->entry[widx].string)) tags[widx] |= NO_SPACE_R;
	if (src->entry[widx].string.length <= 1 && src->entry[widx].string.word[0] == '\'' ) { sqcnt++; tags[widx] |= IS_SINGLE; }
	if (src->entry[widx].string.length <= 1 && src->entry[widx].string.word[0] == '"' ) { dqcnt++; tags[widx] |= IS_DOUBLE; }
	if (src->entry[widx].string.length <= 1 && src->entry[widx].string.word[0] == '-' ) { hycnt++; tags[widx] |= IS_HYPHEN; }
	}

	/* First detect o'Hara and don't */
    if (sqcnt >0) for(widx = 0; widx < src->mused; widx++) {
	if ( !(tags[widx] & IS_SINGLE)) continue;
#if 0
	 fprintf(stderr, "Single:"); dump_word(stderr, src->entry[widx].string);
	if (widx) { fprintf(stderr, "left:"); dump_word(stderr, src->entry[widx-1].string); fputc('\n', stderr); }
	if (widx <src->mused-1) { fprintf(stderr, "Right:"); dump_word(stderr, src->entry[widx+1].string); fputc('\n', stderr); }
#endif
	/* if the word to the left is absent or 1char we dont want a white inbetween */
	if (!widx || src->entry[widx-1].string.length <2) {
		tags[widx] |= NO_SPACE_L;
		tags[widx] |= NO_SPACE_R;
		tags[widx] &= ~IS_SINGLE;
		sqcnt--;
		}
	/* if the word to the right is absent or 1char we dont want a white inbetween */
	if (widx == src->mused-1 || src->entry[widx+1].string.length <2) {
		tags[widx] |= NO_SPACE_L;
		tags[widx] |= NO_SPACE_R;
		tags[widx] &= ~IS_SINGLE;
		}
	}

	/* Try to match pairs of single quotes. This is rude: we don't care about nesting. */
    if (sqcnt >1) for(begin= -1,widx = 0; widx < src->mused; widx++) {
		if (!(tags[widx] & IS_SINGLE)) continue;
		if (begin < 0) {begin = widx; continue; }
		tags[begin] |= NO_SPACE_R; tags[begin] &= ~NO_SPACE_L; if (begin) tags[begin-1] &= ~NO_SPACE_R;
		tags[widx] |= NO_SPACE_L; tags[widx] &= ~NO_SPACE_R; if (begin < src->mused-1) tags[begin+1] &= ~NO_SPACE_L;
		tags[begin] &= ~IS_SINGLE;
		tags[widx] &= ~IS_SINGLE;
		begin = -1;
		sqcnt -= 2;
		}

	/* idem: double quotes */
    if (dqcnt >1) for(begin= -1,widx = 0; widx < src->mused; widx++) {
		if (!(tags[widx] & IS_DOUBLE)) continue;
		if (begin < 0) {begin = widx; continue; }
		tags[begin] |= NO_SPACE_R;
		tags[widx] |= NO_SPACE_L;
		tags[begin] &= ~IS_DOUBLE;
		tags[widx] &= ~IS_DOUBLE;
		begin = -1;
		dqcnt -= 2;
		}
	/* Idem: hyphens  */
    if (hycnt >1) for(begin= -1,widx = 0; widx < src->mused; widx++) {
		if (!(tags[widx] & IS_HYPHEN)) continue;
		if (begin < 0) {begin = widx; continue; }
		tags[begin] |= NO_SPACE_R;
		tags[widx] |= NO_SPACE_L;
		tags[begin] &= ~IS_HYPHEN;
		tags[widx] &= ~IS_HYPHEN;
		begin = -1;
		hycnt -= 2;
		}
	/* Final pass: cleanup.
	** if there are any unmached quotes or hyphens left,
	**  they don't want whitespace around them. Rude, again.
	*/
    if (sqcnt+dqcnt+hycnt) for(widx = 0; widx < src->mused; widx++) {
		if (!(tags[widx] & (IS_SINGLE | IS_DOUBLE | IS_HYPHEN))) continue;
		tags[widx] |= NO_SPACE_L;
		tags[widx] |= NO_SPACE_R;
		}

    length = 0;
    for(widx = 0; widx < src->mused; widx++) {
	if (!widx) {;}
	else if (tags[widx] & NO_SPACE_L ) {;}
	else if (tags[widx-1] & NO_SPACE_R) {;}
	else output[length++] = ' ';
	memcpy(output+length, src->entry[widx].string.word, src->entry[widx].string.length);
	length += src->entry[widx].string.length;
	}

    output[length] = '\0';

    free(tags);
#undef NO_SPACE_L
#undef NO_SPACE_R
#undef IS_SINGLE
#undef IS_DOUBLE
#undef IS_HYPHEN
	/* scrutinize_string may or may not reallocate the output string, but we don't care */
    output = scrutinize_string (output, SCRUTINIZE_OUTPUT);
    return output;
}

/*---------------------------------------------------------------------------*/

/*
 *	Function:	Babble
 *
 *	Purpose:		Return a random symbol from the current context, or a
 *				zero symbol identifier if we've reached either the
 *				start or end of the sentence.  Select the symbol based
 *				on probabilities. (ie weighted by ptr->thevalue)
 *				In all cases, use the longest available context to choose the symbol.
 */
STATIC WordNum babble(MODEL *model, struct sentence *src)
{
    TREE *node;
    unsigned int oidx,cidx=0;
    unsigned credit;
    WordNum symbol = WORD_ERR;


    /*
     *		Select the longest available context.
     */
    node = NULL;
    for(oidx = 0; oidx <= model->order; oidx++) {
	if (!model->context[oidx] ) continue;
	node = model->context[oidx];
	}

    if (!node ) goto done;
    if (node->branch == 0) goto done;
    // if (node->branch == 1) { symbol = node->children[0].ptr->symbol; goto done; }
    /*
     *		Choose a symbol at random from this context.
     *		weighted by ->thevalue
     */
#if 1
    credit = urnd( node->childsum );
#if 0
    credit += urnd( node->childsum -credit ); /* 201501314 */
    fprintf(stderr, "{%u/%u}", credit, node->childsum);
#endif
    for (cidx = 0; 1; cidx = (cidx+1) % node->branch ) {
	if (credit < node->children[cidx].ptr->thevalue) break; /* found it */
        /* 20120203 if (node->children[cidx].ptr->thevalue == 0) credit--; */
	credit -= node->children[cidx].ptr->thevalue;
    }
#else
    cidx = urnd( node->branch );
#endif
    symbol = node->children[cidx].ptr->symbol;

done:
#if 0
    fprintf(stderr, "[%u/%u]", cidx, node->branch);
    fprintf(stderr, "=%u", symbol );
#endif
    return symbol;
}

/*---------------------------------------------------------------------------*/

/*
 *		Function:	Seed
 *
 *		Purpose:		Seed the reply by guaranteeing that it contains a
 *						keyword, if one exists.
 */
STATIC WordNum seed(MODEL *model)
{

    WordNum symbol;
	symbol = crosstab_get(glob_crosstab, urnd (cross_dict_size) );
	if (symbol >= model->dict->size) symbol = crosstab_get(glob_crosstab, urnd( (cross_dict_size/2)) );
	if (symbol >= model->dict->size) symbol = crosstab_get(glob_crosstab, urnd( (cross_dict_size/4)) );
	if (symbol >= model->dict->size) symbol = crosstab_get(glob_crosstab, urnd( (cross_dict_size/8)) );
	if (symbol >= model->dict->size) symbol = crosstab_get(glob_crosstab, urnd( (cross_dict_size/16)) );
	if (symbol >= model->dict->size) symbol
		 = (model->context[0]->branch) 
		? model->context[0]->children[ urnd(model->context[0]->branch) ].ptr->symbol
		: WORD_NIL;
	if (symbol >= model->dict->size) symbol = urnd(model->dict->size);
#if 0
	else {
		STRING altword;
		WordNum altsym;
		altword = word_dup_initcaps (model->dict->entry[symbol].string);
		altsym = find_word(model->dict, altword);
		if (altsym != WORD_NIL) symbol = altsym;
		}
#endif
    // fprintf(stderr, "{*%u}", symbol );
    return symbol;
}

/*---------------------------------------------------------------------------*/
double start_penalty(MODEL *model, STRING word)
{
WordNum symbol, altsym;
STRING other;
TREE *node=NULL, *altnode=NULL;
double penalty =999;

if (!model || !model->forward || !model->dict) return penalty;

symbol = find_word(model->dict, word);
init_typ_fwd = word.ztype;
if (/* symbol <= WORD_ERR || */ symbol == WORD_NIL) return penalty;
init_typ_fwd = model->dict->entry[symbol].string.ztype;
node = find_symbol(model->forward, symbol);
if (!node) return 100.0;

switch (init_typ_fwd) {
case TOKEN_INITCAPS:
	other = word_dup_lowercase(model->dict->entry[symbol].string);
	altsym = find_word(model->dict, other);
	if (altsym == WORD_NIL) { penalty = 0.0; break; } /* there is no other: This might be a capitalised Name */
	else if (altsym==symbol) { penalty = 0.0; break; }
	altnode = find_symbol(model->forward, altsym);
	if (!altnode) penalty = /* the other is not present at this level */
			(model->dict->entry[altsym].stats.valuesum < model->dict->entry[symbol].stats.valuesum) /* assume Capitalised Name */
			? 0.1
			/* most common case: this is just a Begincaps */
			: ((1.0+model->dict->entry[symbol].stats.valuesum)
			/ (1.0+model->dict->entry[altsym].stats.valuesum)
			);
	// else if (node->thevalue > altnode->thevalue) penalty = 0.1; /* Initcaps is more frequent at the start of a sentence */
	else penalty = (0.0+node->thevalue) / (1.0+altnode->thevalue) ;
	break;
case TOKEN_LOWER:
	/* The altsym refers tot the Initcaps version, which @linebegin should always be better than the original 'symbol' */
	other = word_dup_initcaps(model->dict->entry[symbol].string);
	altsym = find_word(model->dict, other);
	if (altsym == WORD_NIL) { penalty = 1.0; break; } /* there is no other: still deprecated as a starting word */
	altnode = find_symbol(model->forward, altsym);
	if (!altnode)  penalty =
			(model->dict->entry[altsym].stats.valuesum > model->dict->entry[symbol].stats.valuesum) /* Capitalised Name  ???*/
			? 1.8
			/* Altsymbol is less frequent: this should have been Initcapsed */
			: ((1.0+model->dict->entry[symbol].stats.valuesum)
			/ (1.0+model->dict->entry[altsym].stats.valuesum)
			);
	else if (altnode->thevalue <= node->thevalue) penalty = 1.6; /* Initcaps should be more frequent @ start of sentence */
	else penalty = (1.0+altnode->thevalue) / (1.0+node->thevalue) ;
	break;
case TOKEN_UPPER: /* SHOUTING! */
case TOKEN_AFKO:
	penalty = 3;
	other = word_dup_initcaps(model->dict->entry[symbol].string);
	goto misc;
case TOKEN_CAMEL: /* mostly typos */
	penalty = 4;
	other = word_dup_initcaps(model->dict->entry[symbol].string);
	goto misc;
case TOKEN_MISC:	/* Anything, including high ascii */
	penalty = 3;
	other = word_dup_initcaps(model->dict->entry[symbol].string);
misc:	/* The altsym refers tot the Initcaps version 
	** which should always be better than symbol */
	altsym = find_word(model->dict, other);
	if (altsym == WORD_NIL) { penalty /= 2.0; break; } /* there is no other: still deprecated as a starting word */
	else if (altsym == symbol) { penalty /= 8; break; }
	// altnode = find_symbol(model->forward, altsym);
	// if (altnode) penalty = ((1.0+altnode->thevalue) / (1.0+node->thevalue));
	break;
case TOKEN_PUNCT:
	penalty = 3.0;
	break;
case TOKEN_ATAAP:
case TOKEN_HEKHASH:
	penalty = 7.0; break;
case TOKEN_NUMBER:
default:
	penalty = 2.0; break;
	}
return (penalty);
}
/*---------------------------------------------------------------------------*/

double end_penalty(MODEL *model, STRING word)
{
WordNum symbol;
TREE *node=NULL;
int type =0;
double penalty =999;

if (!model || !model->backward || !model->dict) return -11.11;

symbol = find_word(model->dict, word);
if (/* symbol <= WORD_ERR || */ symbol == WORD_NIL) return 111;
type = model->dict->entry[symbol].string.ztype;
node = find_symbol(model->backward, symbol);


switch (type) {
case TOKEN_INITCAPS:
case TOKEN_LOWER:
case TOKEN_UPPER:
case TOKEN_MISC:	/* Anything, including high ascii */
case TOKEN_ATAAP: /* mentions */
case TOKEN_HEKHASH: /* hashtag */
case TOKEN_CAMEL: /* mostly typos */
default:
	penalty = 4;
	break;
case TOKEN_AFKO:
case TOKEN_NUMBER:
	penalty = 1.7;
	break;
case TOKEN_PUNCT:
	if ( strchr(".!?", word.word[ word.length-1] )) penalty = 0.0;
	else if (node) penalty = 2.0;
	else penalty = 2.3;
	break;
	}
return (penalty);
}
/*---------------------------------------------------------------------------*/

/*
 *		Purpose:		Read a dictionary from a file.
 */
STATIC DICT *read_dict(char *filename)
{
    DICT *this;
    FILE *fp = NULL;
    static char buffer[1024];
    static STRING word ={0,0,0,buffer};

    this = new_dict();

    if (!filename) return this;

    fp = fopen(filename, "r");
    if ( !fp ) return this;

    while( fgets(buffer, sizeof buffer, fp) ) {
        size_t len;
	if (buffer[0] == '#') continue;
        word.length = len = strcspn (buffer, "\t \n#" );
        if (!len) continue;
	add_word_dodup(this, word);
    }

    fclose(fp);
    return this;
}
/*---------------------------------------------------------------------------*/

/*
 *		Function:	Ignore
 *
 *		Purpose:		Log the occurrence of a signal, but ignore it.
 * WP: using printf() and friends from within a signal handler is not a good idea.
 */
void sig_ignore(int sig)
{
    if (sig != 0) warn("ignore", MY_NAME " received signal %d", sig);

    /* signal(SIGINT, saveandexit);*/
    /* signal(SIGILL, die);*/
    /*    signal(SIGSEGV, die);*/
    /*    signal(SIGFPE, die);*/

    signal(SIGINT, sig_lethal);
    signal(SIGILL, sig_lethal);
    signal(SIGFPE, sig_lethal);
}

void sig_lethal(int signum)
{
signal_caught = signum;
// abort();
}


/*---------------------------------------------------------------------------*/

/*
 *		Function:	Die
 *
 *		Purpose:		Log the occurrence of a signal, and exit.
 */
void die(int sig)
{
    error("die", MY_NAME " received signal %d", sig);
    exithal();
}

/*---------------------------------------------------------------------------*/

/*
 *		Function:	Rnd
 *
 *		Purpose:		Return a random integer between 0 and range-1.
 */
unsigned int urnd(unsigned int range)
{
    static int flag = 0;

    if (!flag) {
	srand48(time(NULL));
    flag = 1;
    }

if (range <= 1) return 0;

while(1)	{
    BigThing val, box;
#if WANT_RDTSC_RANDOM
    val = rdtsc_rand();
#else
    val =  lrand48();
#endif
/* we need this to avoid oversampling of the lower values.
 * Oversampling the lower values becomes more of a problem if (UNSIGNED_MAX/range) gets smaller
 * */
    box = val / range;
    if ((1+box) *range < range) continue;
    return val % range;
	}
}

/*---------------------------------------------------------------------------*/
/* random number generator uses 'entropy' from CPU-ticker */
#define rdtscll(name) \
          __asm__ __volatile__("rdtsc" : "=A" (name))

BigThing rdtsc_rand(void)
{
static BigThing val=0x0000111100001111ULL;

#if WANT_RDTSC_RANDOM
// static BigThing old;
BigThing new;

rdtscll(new);
val ^= (val >> 15) ^ (val << 14) ^ (new << 13); /* PT approved */
// old = new;
#else
val ^= (val >> 15) ^ (val << 14) ^ 9 ;
#endif

return val;
}
/*---------------------------------------------------------------------------*/

void load_personality(MODEL **model)
{
    FILE *fp;
    static char *filename = NULL;

    /*
     *		Allocate memory for the filename
     */
    filename = realloc(filename, strlen(glob_directory)+strlen(SEP)+12);
    if ( !filename) error("load_personality","Unable to allocate filename");

    /*
     *		Check to see if the brain exists
     */

    if (strcmp(glob_directory, last_directory)) {
	sprintf(filename, "%s%smegahal.brn", glob_directory, SEP);
	fp = fopen(filename, "r");
	if ( !fp ) {
	    sprintf(filename, "%s%smegahal.trn", glob_directory, SEP);
	    fp = fopen(filename, "r");
	    if ( !fp ) {
		fprintf(stdout, "Unable to change MegaHAL personality to \"%s\".\n"
			"Reverting to MegaHAL personality \"%s\".\n", glob_directory, last_directory);
		free(glob_directory);
		glob_directory = strdup(last_directory);
		return;
	    }
	}
	fclose(fp);
	fprintf(stdout, "Changing to MegaHAL personality \"%s\".\n", glob_directory);
    }

    /*
     *		Free the current personality
     */
    free_model(*model);

    /*
     *		Create a language model.
     */
    *model = new_model(glob_order);

    /*
     *		Train the model on a text if one exists
     */

    close( glob_fd  ); glob_fd = -1;
    sprintf(filename, "%s%smegahal.brn", glob_directory, SEP);
    if ( load_model(filename, *model) ) {
	sprintf(filename, "%s%smegahal.trn", glob_directory, SEP);
	train(*model, filename);
    }

}

/*---------------------------------------------------------------------------*/

void change_personality(struct sentence *command, unsigned int position, MODEL **model)
{

    if ( !glob_directory ) {
	glob_directory = malloc(strlen(DEFAULT_DIR)+1);
	if ( !glob_directory ) {
	    error("change_personality", "Unable to allocate directory");
	} else {
	    strcpy(glob_directory, DEFAULT_DIR);
	}
    }

    if ( !last_directory ) {
	last_directory = strdup(glob_directory);
    }

    if ( !command || position+2 >= command->mused ) {
	/* no dir set, so we leave it to whatever was set above */
    } else {
        glob_directory = realloc(glob_directory, command->entry[position+2].string.length+1);
        if ( !glob_directory )
            error("change_personality", "Unable to allocate directory");
        memcpy(glob_directory, command->entry[position+2].string.word,
                command->entry[position+2].string.length);
        glob_directory[command->entry[position+2].string.length] ='\0';
    }

    load_personality(model);
}

/*---------------------------------------------------------------------------*/

STATIC void free_string(STRING word)
{
    free(word.word);
    word.word = NULL;
    word.length = 0;
    word.ztype = 0;
    word.zflag = 0;
}

STATIC HashVal hash_word(STRING string)
{
return hash_mem(string.word, (size_t) string.length);
}

STATIC HashVal hash_mem(void *dat, size_t len)
{
unsigned char *str = (unsigned char*) dat;
HashVal val=0;
size_t idx;

for(idx=0; idx < len; idx++ )	{
	val ^= (val >> 2) ^ (val << 5) ^ (val << 13) ^ str[idx] ^ 0x80001801;
	}
return val;
}

STATIC WordNum * dict_hnd (DICT *dict, STRING word)
{
WordNum *np;
unsigned hash,slot;

/* We always assume that the next operation will be an insert, so there needs to be at least
 * one free spot.
 * If the seeked element is not present, *np will point
 * to the place where it is to be inserted. (the slot after the last used item.)
 */
if (dict->size >= dict->msize && grow_dict(dict)) return NULL;

hash = hash_word(word);
slot = hash % dict->msize;

for (np = &dict->entry[slot].tabl ; *np != WORD_NIL ; np = &dict->entry[*np].link ) {
#if WANT_STORE_HASH
	if ( dict->entry[*np].whash != hash) continue;
#endif /* WANT_STORE_HASH */
	if ( wordcmp(dict->entry[*np].string , word)) continue;
	break;
	}
return np;
}

STATIC int grow_dict(DICT *dict)
{
    unsigned newsize;

    newsize = dict->size ? dict->size + sqrt(1+dict->size) : DICT_SIZE_INITIAL;
    return resize_dict(dict, newsize);
}


STATIC int resize_dict(DICT *dict, unsigned newsize)
{
    struct dictslot *old;
    WordNum item,slot;

    old = dict->entry ;
    while (newsize < dict->size) newsize += 2;
    dict->entry = malloc (newsize * sizeof *dict->entry);
    if (!dict->entry) {
	error("resize_dict", "Unable to allocate dict->slots.");
	dict->entry = old;
	return -1;
	}
    dict->msize = newsize;
    format_dictslots(dict->entry, dict->msize);

	/* When we get here, dict->entry contains the new slots (with empty hashtable)
	** and *old* contains the old entries (including hashtable)
	** dict->msize contains the new size, and dict->size the number of valid elements.
	** item is the *index* in both the old and new table.
	*/
    for (item =0 ; item < dict->size; item++) {
		WordNum *np;
#if WANT_STORE_HASH
		slot = old[item].whash % dict->msize;
#else
		unsigned hash;
		hash = hash_word(old[item].string);
		slot = hash % dict->msize;
#endif /* WANT_STORE_HASH */

			/* Find insertion point */
		for( np = &dict->entry[slot].tabl; np; np = &dict->entry[*np].link ) {
			if (*np == WORD_NIL) break;
			if (dict->entry[*np].stats.valuesum <= old[item].stats.valuesum) break; /* 20131011 : keep LL sorted */
			}

		dict->entry[item].link = *np;	/* 20131011 */
		*np = item;

#if WANT_STORE_HASH
		dict->entry[item].whash = old[item].whash;
#endif /* WANT_STORE_HASH */
		dict->entry[item].stats.nnode = old[item].stats.nnode;
		dict->entry[item].stats.valuesum = old[item].stats.valuesum;
		dict->entry[item].string = old[item].string;
		}
    free (old);
    return 0; /* success */
}

STATIC struct sentence * sentence_new(void)
{
struct sentence *new;
new = malloc (sizeof *new);
new->mused = new->msize = 0;
new->kwhit = 0;
new->entry= NULL;
return new;
}
STATIC int sentence_grow(struct sentence *ptr)
{
    unsigned newsize;

    newsize = ptr->mused ? ptr->mused + (1+ptr->mused)/2 : 64;
    return sentence_resize(ptr, newsize);
}


STATIC int sentence_resize(struct sentence *ptr, unsigned newsize)
{
    void * old;
    old = ptr->entry ;
    ptr->entry = realloc (ptr->entry, newsize * sizeof *ptr->entry);
    if (!ptr->entry) {
	error("sentence_resize", "Unable to allocate entries:oldsize =%u newsize=%u"
	, ptr->msize, newsize );
	ptr->entry = old;
	return -1;
	}
    ptr->msize = newsize;

    return 0; /* success */
}

STATIC void sentence_reverse(struct sentence *ptr)
{
    unsigned bot,top;
    for (bot = 0, top = ptr->mused? ptr->mused-1: 0; bot < top; bot++, top--) {
	STRING tmp ;
	tmp = ptr->entry[bot].string;
	ptr->entry[bot].string = ptr->entry[top].string;
	ptr->entry[top].string  = tmp;
	}
}

/*********************************************************************************************/

static TREE * alz_stack[10] = {NULL,};
static FILE *alz_file = NULL;

STATIC unsigned model_alzheimer(MODEL * model, unsigned maxnodecount)
{
Stamp limit;
unsigned step, width;
unsigned count=0, totcount=0;
static double density = 0.0;
static unsigned direction = 0;
int rc;

if (!model || !maxnodecount) return 0;
if (memstats.node_cnt <= ALZHEIMER_NODE_COUNT) return 0;

alz_dict = model->dict;

alz_file = fopen ("alzheimer.dmp", "a" );


	/* density is an estimate of the amount of nodes we expect to reap per timestamp
	** step is our estimate for the number of steps we need to add to stamp_min to harvest
	** the intended amount of nodes. (= bring down memstats.node_cnt to maxnodecount)
	*/
if (density == 0.0) {
	width = (unsigned)(stamp_max-stamp_min);
	if (width < 2) return 0;
	density = (double)memstats.node_cnt / width ;
	direction = urnd(stamp_max);
	}

for(  totcount = 0; memstats.node_cnt > maxnodecount;	) {
    width = stamp_max-stamp_min;
    step = (memstats.node_cnt - maxnodecount) / density;
    if (!step) step = width / 100;
    while (step && step > width/10) step /= 2;
    if (!step) step = 1;
    limit = stamp_min + step;

#if (WANT_DUMP_ALZHEIMER_PROGRESS >= 2)
    fprintf(stderr, "Model_alzheimer(%u:%s) NodeCount=%u/%u Stamp_min=%u Stamp_max=%u Width=%u Dens=%6.4f Step=%u Limit=%u\n"
	, direction, (direction%2) ? "Backward" : "Forward"
	    , (unsigned)memstats.node_cnt, (unsigned)maxnodecount
	    , (unsigned)stamp_min, (unsigned)stamp_max
            , (unsigned)width, density, step, (unsigned)limit);
#endif

    fprintf(alz_file, "Model_alzheimer(%u:%s) NodeCount=%u/%u Stamp_min=%u Stamp_max=%u Width=%u Dens=%6.4f Step=%u Limit=%u\n"
	, direction, (direction%2) ? "Backward" : "Forward"
	    , (unsigned)memstats.node_cnt, (unsigned)maxnodecount
	    , (unsigned)stamp_min, (unsigned)stamp_max
            , (unsigned)width, density, step, (unsigned)limit);

    rc = check_interval(stamp_min, stamp_max, limit);
    if (rc) { /* outside interval */
#if (WANT_DUMP_ALZHEIMER_PROGRESS >=0)
	    fprintf(stderr, "Model_alzheimer(%u:%s) outside interval Rc=%d Ajuus!\n"
		, direction, (direction%2) ? "Backward" : "Forward", rc);
#endif
	    fprintf(alz_file, "Model_alzheimer(%u:%s) outside interval Rc=%d Ajuus!\n"
		, direction, (direction%2) ? "Backward" : "Forward", rc);
            direction++;
	    if (width < 2) goto ajuus;
	    density = (double)memstats.node_cnt / width;
            continue;
	    }

    switch(direction % 2) {
    case 0:
        count = symbol_alzheimer_recurse(model->forward, 0, limit);
        break;
    case 1:
        count = symbol_alzheimer_recurse(model->backward, 0, limit);
        break;
	}

    totcount += count;

	/*
	** adjust running average of density.
	**  If nothing is harvested, increase the stepsize by lowering the density estimate.
	**  0.8 might overshoot.  maybe 0.9...0.95 is better, but that may take too many iterations.
	*/
    if (count) { density = (1* density + (1.0 * count / step)) / 2; }
    else density *= 0.8;

    stamp_min = limit;

#if WANT_DUMP_ALZHEIMER_PROGRESS
    fprintf(stderr, "Model_alzheimer(%u:%s) Count=%6u %u/%u Stamp=[%u,%u] Width=%u Step=%u Dens=%6.4f\n"
	, direction, (direction%2) ? "Backward" : "Forward" , count
	, (unsigned)memstats.node_cnt, (unsigned)maxnodecount
	, (unsigned)stamp_min, (unsigned)stamp_max,(unsigned)(stamp_max-stamp_min)
	,step, density);
    show_memstat("Alzheimer" );
#endif

    fprintf(alz_file,  "Model_alzheimer(%u:%s) Count=%6u %u/%u Stamp=[%u,%u] Width=%u Step=%u Dens=%6.4f\n"
	, direction, (direction%2) ? "Backward" : "Forward" , count
	    , (unsigned)memstats.node_cnt, (unsigned)ALZHEIMER_NODE_COUNT
	    , (unsigned)stamp_min, (unsigned)stamp_max, (unsigned)(stamp_max-stamp_min)
	,step, density);
	/* Avoid the next iteration to overshoot (we expect to harvest 'count' items) */
    direction++;
    if (memstats.node_cnt <= maxnodecount+count/2) break;
    }

ajuus:
fclose (alz_file);
return totcount;
}

STATIC unsigned symbol_alzheimer_recurse(TREE *tree, unsigned lev, Stamp lim)
{
unsigned slot,count;
WordNum symbol;
int rc;

if (!tree) return 0;
alz_stack[lev++] = tree;

rc = check_interval(lim, stamp_max, tree->stamp);
if (rc) { /* Too old: outside interval */
#if (WANT_DUMP_ALZHEIMER_PROGRESS >= 3)
	for (slot=0; slot< lev; slot++) fputc(' ', alz_file);
	for (slot=0; slot< lev; slot++) fprintf(alz_file, "[%u:%u]", alz_stack[slot]->symbol, alz_stack[slot]->stamp );
	fprintf(alz_file, "symbol_alzheimer_recurse(rc=%d) Node considered too old (stamp=%u symbol=%u childsum=%u count=%u)\n"
	, rc, tree->stamp, tree->symbol, tree->childsum, tree->thevalue);
#endif
#if (WANT_DUMP_ALZHEIMER_PROGRESS >= 4)
	dump_model_recursive(alz_file, tree, alz_dict, lev);
#endif
	}

/* We should work from top to bottom, because it would require less shuffling */
count = 0;
for (slot = tree->branch; slot--> 0;	) {
	TREE *child;

#if (WANT_DUMP_ALZHEIMER_PROGRESS >= 3)
    fprintf(alz_file, "symbol_alzheimer_recurse(lev=%u lim=%u) Stamp=%u enter this slot=%u\n"
	, lev, lim, tree->stamp, slot);
#endif
	if (slot >= tree->branch) continue;
	child =  tree->children[slot].ptr;
	if (!child) continue;
	rc = check_interval(lim, stamp_max, child->stamp);
	if (!rc) { /* inside interval */
		count += symbol_alzheimer_recurse(child, lev, lim);
		continue;
		}
	else	{	/* slot is stale: remove it */
		symbol = child->symbol ;
		memstats.alzheimer += 1;
		del_symbol_do_free(tree, symbol) ;
		count++;
		}
	}
return count;
}

/* Check of this inside or above/below interval {min,max}
** min and max may have been wrapped around zero (--> min > max)
** return
**	0 := this inside interval
**	1 := this below interval
**	-1 := this above interval (but wrapped)
** The two impossible cases return -2.
*/
STATIC int check_interval(Stamp min, Stamp max, Stamp this)
{
switch (4 *(max >= min)
	+2 *(this >= min)
	+1 *(this > max)
	) {
	case 0: return STAMP_INSIDE;	/* inside (wrapped) */
	case 1:				/* outside (wrapped) */
		return ((Stamp)(min - this) < (Stamp)(this - max)) ? STAMP_BELOW : STAMP_ABOVE;
	case 2: return -2;
	case 3: return STAMP_INSIDE;	/* inside (wrapped) */
	case 4:				/* all below */
		return ((Stamp)(min - this) < (Stamp)(this - max)) ? STAMP_BELOW : STAMP_ABOVE;
	case 5: return -2;	/* impossible */
	case 6: return STAMP_INSIDE;	/* inside normal case */
	case 7:		/* all above) */
		return ((Stamp)(min - this) < (Stamp)(this - max)) ? STAMP_BELOW : STAMP_ABOVE;
	}
return -2;
}

STATIC void dump_word(FILE *fp, STRING word)
{

fprintf(fp,"'%*.*s'"
	,  (int) word.length,  (int) word.length,  word.word );
}

#if CROSS_DICT_SIZE
STATIC size_t word_format(char *buff, STRING word)
{

return sprintf(buff,"'%*.*s'"
	,  (int) word.length,  (int) word.length,  word.word );
}

STATIC size_t symbol_format_callback(char *buff, WordNum sym)
{
DICT *this_dict = glob_model->dict;
if ( !this_dict ) return sprintf(buff, "<NoDict>" );
else if (sym >= this_dict->size) return sprintf(buff, "<%u>", sym );
this_dict->entry[sym].string.zflag = 1;
return word_format(buff, this_dict->entry[sym].string );
}

STATIC double symbol_weight_callback(WordNum sym)
{
DICT *this_dict = glob_model->dict;
if ( !this_dict ) return 0.0;
else if (sym >= this_dict->size) return -1.0;
else return symbol_weight(this_dict, sym, 0 );
}
#endif

STATIC char * scrutinize_string(char * src, int mode)
{
switch (mode) {
case SCRUTINIZE_U2L : return utf2latin(src, 0);
case SCRUTINIZE_L2U : return latin2utf(src, 0);
default:
case 0: return src;
	}
}

STATIC char * utf2latin(char * str, size_t len)
{
unsigned idx,pos;
int ret;

if (!len) len = strlen (str);

	/* the string can only shrink, so we can perform this in place */
for (idx=pos=0; idx < len ; idx += ret) {
	unsigned val=0;
	ret = eat_utf8 ((unsigned char*) str+idx, len-pos, &val);
	if (ret == 0) break;
	else if (ret < 0) { ret=1; str[pos++] = str[idx]; } /* does not fit, this should never happen */
	/* else if (ret==1)  { str[pos++] = val; } normal character */
	else	{ str[pos++] = val; } /* we consumed ret characters, but only produced one */
	}
str[pos] = 0;
return str;
}

STATIC size_t cp_utf2latin(char *dst, char * src, size_t len)
{
unsigned idx,pos;
int ret;

if (!len) len = strlen (src);

for (idx=pos=0; idx < len ; idx += ret) {
	unsigned val=0;
	ret = eat_utf8 ((unsigned char*) src+idx, len-pos, &val);
	if (ret == 0) break;
	else if (ret < 0) { ret=1; dst[pos++] = src[idx]; } /* does not fit, this should never happen */
	else	{ dst[pos++] = val; } /* we consumed ret characters, but only produced one */
	}
dst[pos] = 0;
return pos;
}

STATIC char * latin2utf(char * src, size_t len)
{
unsigned idx,pos;

int ret;
unsigned char *dst;

if (!len) len = strlen (src);
	/* the string can expand; we are pessimistic and allocate twice the original size */
dst = malloc (2*len+1);

for (idx=pos=0; src[idx] ;idx++ ) {
	ret = cha_latin2utf8(dst+pos, ((unsigned char*)src)[idx] );
	pos += ret;
	}
dst[pos] = 0;
free (src);
return (char*) dst;
}

STATIC unsigned cha_latin2utf8(unsigned char *dst, unsigned val)
{
if (val <  0x80)  { *dst = val; return 1; }
else	{
	/* all 11 bit codepoints (0x0 -- 0x7ff)
	** fit within a 2byte utf8 char
	** firstbyte = 110 +xxxxx := 0xc0 + (char>>6) MSB
	** second    = 10 +xxxxxx := 0x80 + (char& 63) LSB
	*/
	*dst++ = 0xc0 | ((val >>6) & 0x1f); /* 3+5 bits */
	*dst++ = 0x80 | ((val) & 0x3f); /* 2+6 bits */
	}
return 2;
}

STATIC int eat_utf8(unsigned char *str, unsigned len, unsigned *target)
{
unsigned val = 0;
unsigned todo;

if (!len) return 0;

val = str[0];
if ((val & 0x80) == 0x00) { *target = val; return 1; }
else if ((val & 0xe0) == 0xc0) { val &= 0x1f; todo = 1; }
else if ((val & 0xf0) == 0xe0) { val &= 0x0f; todo = 2; }
else if ((val & 0xf8) == 0xf0) { val &= 0x07; todo = 3; }
else if ((val & 0xfc) == 0xf8) { val &= 0x03; todo = 4; }
else if ((val & 0xfe) == 0xfc) { val &= 0x01; todo = 5; }
else {*target = val; return 1; } /* Default (Not in the spec) */

/* fprintf(stderr, "[val=%x, todo=%d]", val, todo); */

len--;str++;
if (todo > len) { return -todo; }

for(len=todo;todo--;) {
	val <<= 6;
	val |= *str++ & 0x3f;
	}

*target = val;
return  1+ len;
}

STATIC size_t hexdump_string(char *buff, STRING string)
{
unsigned idx;
int type = 0;
int state = 0;
for (idx = 0; idx <  string.length; idx++) {
	unsigned val=0, cha;
	cha = 0xff & string.word[idx] ;
	sprintf(buff+3*idx, " %02x", 0xff & cha );
	switch(state) {
	case 0:
		if (!(cha & 0x80)) continue;
		else if ((cha & 0xe0) == 0xc0) { state = 1; val = cha & 0x1f ; continue; }
		else if ((cha & 0xf0) == 0xe0) { state = 2; val = cha & 0x0f ; continue; }
		else if ((cha & 0xf8) == 0xf0) { state = 3; val = cha & 0x07 ; continue; }
		else if ((cha & 0xfc) == 0xf8) { state = 4; val = cha & 0x03 ; continue; }
		else if ((cha & 0xfe) == 0xfc) { state = 5; val = cha & 0x01 ; continue; }
		else { type |= 1; continue; }
	case 1:
		if ((cha & 0xc0) != 0x80) type |= 1;
		else {
			type |= 2;
			val <<= 6; val |= cha&0x3f; state--;
			if (val >=256) type |= 1;
			}
		break;
	case 2:
	case 3:
	case 4:
	case 5:
		if ((cha & 0xc0) != 0x80 ) type |= 1;
		val <<= 6; val |= cha&0x3f; state--;
		break;
		}

	}
sprintf (buff+3*idx, " =%d", type);
return 3*idx;
}

STATIC size_t decode_word(char * buff, STRING str, int type )
{
size_t ret;

switch (type) {
case 0: memcpy( buff, str.word, ret = str.length); break;
case 1: memcpy( buff, str.word, ret = str.length);break;
case 2: ret = cp_utf2latin(buff, str.word, str.length); break;
case 3: memcpy( buff, str.word, ret = str.length); break;
default: ret = sprintf( buff, "SomeType=%d", type); break;
	}
buff[ ret] = 0;
return ret;
}

#if WANT_PARROT_CHECK
#if USE_QSORT
int cmp_unsigned_desc(const void *vl, const void *vr)
{
unsigned *ul = (unsigned*) vl;
unsigned *ur = (unsigned*) vr;
if (*ul < *ur) return 1;
if (*ul > *ur) return -1;
return 0;
}

#else
STATIC inline void meuksort(unsigned arr[], unsigned siz);
STATIC inline void meuksort(unsigned arr[], unsigned siz)
{
unsigned bot,idx, best,max;

	/* remove zeros by putting them beyond the end */
for (bot=0; bot < siz; ) {
	if( !arr[bot]) { arr[bot] = arr[--siz]; arr[siz] = 0; }
	else bot++;
	}

	/* Selection sort: find elements better than [bot] */
for (bot=0; bot < siz; bot++) {
	max = arr[best=bot];
	for (idx=bot+1; idx < siz; idx++ ) {
		if (arr[idx] <= max) continue;
		max = arr[best=idx];
		}
	if (best == bot) continue;
	arr[best] = arr[bot];
	arr[bot] = max;
	}
}
#endif /* USE_QSORT */

/* siz1 is the size of the first array; the second one has 1 item extra */
STATIC double penalize_two_parrots(unsigned arr1[], unsigned arr2[], unsigned siz1)
{
unsigned idx;
unsigned ssq,sum;
double penalty;
unsigned long long red_dragon;

#if USE_QSORT
qsort ( arr1, siz1, sizeof arr1[0], cmp_unsigned_desc);
qsort ( arr2, siz1+1, sizeof arr2[0], cmp_unsigned_desc);
#else
meuksort ( arr1, siz1);
meuksort ( arr2, siz1+1);
#endif

sum=ssq=0;
for (idx=0; idx < siz1 ; idx++) { 
    // if ( !arr1[idx] || !arr2[idx] ) break;
    sum += arr1[idx] + arr2[idx] ;
    ssq += arr1[idx] * arr2[idx] ;
    }
sum += arr2[idx] ;
sum /= 2;
if (sum <= 2) return 0.0;


/* Formula from hashtable-site www.strchr.com/hash_functions/
**     SUM ( chainlen * (chainlen+1)) / 2    ## Chainlen := number of items/slot
**     ------------------------------
**          (n/2m)* (n+2m -1)
**
** N= nitem; m=nslot
** for ease of computation, 2*nominator and 2*denominator are used here.
** The result is a ratio that should be ~1 for perfect hashing/spread.
** I penalize higher ratios by raising to a higher power (around 1.5)
*/

red_dragon = dragon_denominator2( siz1, sum);

penalty = pow ( (double)ssq/red_dragon, PARROT_POWER );

/* fprintf(stderr, "Parrot2: Sum=%u Siz=%u Ssq= %lu/%llu := %f\n" , sum, siz1, ssq, red_dragon, penalty ); */

if (penalty != penalty) penalty = WAKKER_INF; /* Check for NaN */
if (penalty >= WAKKER_INF) penalty = WAKKER_INF; /* Check for Inf */

return penalty;
}

/* expected value for ssq when dividing nitems over nslots */
STATIC unsigned long long dragon_denominator2(unsigned long nslot, unsigned long nitem)
{

unsigned long long result;
result = ((unsigned long long)nitem * (nitem+2*nslot-1)) / (nslot) ;
/* fprintf (stderr, "Denominator (%lu,%lu) := %llu\n" , nslot, nitem, result); */
return result;
}
#endif

STATIC double penalize_both_parrots(unsigned arr1[], unsigned arr2[], unsigned siz1)
{
unsigned idx;
unsigned sum;
double pn,entropy,penalty;

if (siz1 < 1) return 0.0;
sum=0;
for (idx=0; idx < siz1 ; idx++) { 
    sum += arr1[idx] ;
    sum += arr2[idx] ;
    }
sum += arr2[idx] ;
if (sum < 3) return 0.0;

entropy = 0.0;
for (idx=0; idx < siz1 ; idx++) { 
    if (arr1[idx] ) {
    	if (arr1[idx] == sum) { entropy = 0.0; break; }
    	pn = (0.0+arr1[idx]) / sum;
    	entropy += pn * log(pn);
	}
    if (arr2[idx] ) {
    	if (arr2[idx] == sum) { entropy = 0.0; break; }
    	pn = (0.0+arr2[idx]) / sum;
    	entropy += pn * log(pn);
	}
    }
if (arr2[idx] && arr2[idx] != sum) {
    pn = (0.0+arr2[idx]) / sum;
    entropy += pn * log(pn);
    }

penalty =  exp( -entropy);
/***
fprintf(stderr, "sum=%u entropy=%lf, penalty=%lf\n"
	 , sum , entropy, penalty);
***/
// penalty =  ( 1.0/ -penalty);

// if (penalty != penalty) penalty = WAKKER_INF; /* Check for NaN */
// if (penalty >= WAKKER_INF) penalty = 0; /* Check for Inf */

return penalty/ (2*siz1+1);
}

STATIC double penalize_one_parrot(unsigned arr[], unsigned siz)
{
unsigned idx;
unsigned sum;
double pn,entropy,penalty;

if (siz < 1) return 0.0;
sum=0;
for (idx=0; idx < siz ; idx++) { 
    sum += arr[idx] ;
    }
if (sum < 2) return 0.0;

entropy = 0.0;
for (idx=0; idx < siz ; idx++) { 
    if (arr[idx] < 1) continue;
    if (arr[idx] == sum) { entropy = 0.0; break; }
    pn = (0.0+arr[idx]) / sum;
    entropy += pn * log(pn);
    }

penalty =  exp( -entropy);
/***
fprintf(stderr, "sum=%u entropy=%lf, penalty=%lf\n"
	 , sum , entropy, penalty);
***/
// penalty =  ( 1.0/ -penalty);

if (penalty != penalty) penalty = WAKKER_INF; /* Check for NaN */
if (penalty >= WAKKER_INF) penalty = WAKKER_INF; /* Check for Inf */
	/* inverse entropy ? */
return penalty;
}


int do_check_interval(Stamp min, Stamp max, Stamp this)
{
return check_interval(min, max, this);
}

#if 0 /* !WANT_DOUBLE_PARROT */
#define WANT_DOUBLE_PARROT 1
STATIC double penalize_parrot(unsigned arr[], unsigned siz);
STATIC double fact2 (unsigned expected, unsigned seen);

STATIC double penalize_parrot(unsigned arr[], unsigned siz)
{
unsigned idx;
unsigned ssq,sum;
double calc,penalty;
unsigned long long red_dragon;

sum=ssq=0;
for (idx=0; idx < siz ; idx++) { 
    sum += arr[idx] ;
    ssq += arr[idx] * (1+arr[idx]) ;
    }
if (sum <= 1) return 0.0;


/* Formula from hashtable-site www.strchr.com/hash_functions/
**     Sum ( chainlen * (chainlen+1)) / 2    ## Chainlen := number of items/slot
**     ------------------------------
**          (n/2m)* (n+2m -1)
**
** N= nitem; m=nslot
** for ease of computation, 2*nominator and 2*denominator are used here.
** The result is a ratio that should be ~1 for perfect hashing/spread.
** I penalize higher ratios by raising to a higher power (around 1.5)
*/

red_dragon = dragon_denominator2( siz, sum);

penalty = pow ( (double)ssq/red_dragon, PARROT_POWER );

/* fprintf(stderr, "Sum=%u Siz=%u Ssq= %lu/%llu := %f\n" , sum, siz, ssq, red_dragon, penalty ); */

if (penalty != penalty) penalty = WAKKER_INF; /* Check for NaN */
if (penalty >= WAKKER_INF) penalty = WAKKER_INF; /* Check for Inf */


return penalty;
}
STATIC double fact2 (unsigned expected,unsigned seen) 
{
unsigned val;
if (seen < expected) return fact2(seen, expected);
if (seen < 2 || expected < 2) { seen += 2; expected += 2; }

for (val =1; seen > expected; seen--) {
	if (val * seen < val) return val* pow( (seen+expected)/2,(seen-expected));
	val *= seen;
	}
/* if (expected) val/= expected; */
return val;
}
#endif
/* Eof */


#if DONT_WANT_THIS
#define P_THINK 40
#define D_KEY 100000
#define V_KEY 50000
#define D_THINK 500000
#define V_THINK 250000

#undef FALSE
#undef TRUE

/* typedef enum { FALSE, TRUE } bool; */
static bool speech = FALSE;
static bool typing_delay = FALSE;

typedef enum { UNKNOWN, QUIT, EXIT, SAVE, DELAY, HELP, SPEECH, VOICELIST, VOICE, BRAIN, QUIET} COMMAND_WORDS;

typedef struct {
    STRING word;
    char *helpstring;
    COMMAND_WORDS command;
} COMMAND;

STATIC COMMAND_WORDS execute_command(struct sentence *, unsigned int *position);
STATIC void make_greeting(struct sentence *dst);
STATIC void do_help(void);
STATIC void changevoice(struct sentence *, unsigned int);
STATIC void typein(char);

STATIC void listvoices(void);
STATIC void delay(char *);
STATIC void die(int);
STATIC void free_words(DICT *words);
/*
   megahal_command --
   Check to see if input is a megahal command, and if so, act upon it.
   Returns 1 if it is a command, 0 if it is not.
  */

int megahal_command(char *input)
{
    unsigned int position = 0;
    char *output;

    make_words(input,glob_input);
    switch(execute_command(glob_input, &position)) {
    case EXIT:
	exithal();
	return 1;
	break;
    case QUIT:
	save_model("megahal.brn", glob_model);
	exithal();
	return 2;
	break;
    case SAVE:
	save_model("megahal.brn", glob_model);
	break;
    case DELAY:
	typing_delay = !typing_delay;
	printf(MY_NAME " typing is now %s.\n", typing_delay?"on":"off");
	return 1;
    case SPEECH:
	speech = !speech;
	printf(MY_NAME " speech is now %s.\n", speech?"on":"off");
	return 1;
    case HELP:
	do_help();
	return 1;
    case VOICELIST:
	listvoices();
	return 1;
    case VOICE:
	changevoice(glob_input, position);
	return 1;
    case BRAIN:
	change_personality(glob_input, position, &glob_model);
	make_greeting(glob_greets);
	output = generate_reply(glob_model, glob_greets);
	log_output(output);
	return 1;
    case QUIET:
	quiet = !quiet;
	return 1;
    default:
	return 0;
    }
    return 0;
}
/*
 *		Function:	Execute_Command
 *
 *		Purpose:		Detect whether the user has typed a command, and
 *						execute the corresponding function.
 */
STATIC COMMAND_WORDS execute_command(struct sentence *src, unsigned int *position)
{
    unsigned int iwrd;
    unsigned int j;

    /*
     *		If there is only one word, then it can't be a command.
     */
    *position = src->mused+1;
    if (src->mused <= 1) return UNKNOWN;

    /*
     *		Search through the word array.  If a command prefix is found,
     *		then try to match the following word with a command word.  If
     *		a match is found, then return a command identifier.  If the
     *		Following word is a number, then change the judge.  Otherwise,
     *		continue the search.
     */
    for(iwrd = 0; iwrd < src->mused-1; iwrd++) {
	/*
	 *		The command prefix was found.
	 */
	if (src->entry[iwrd].string.word[src->entry[iwrd].string.length - 1] != '#') continue;
	    /*
	     *		Look for a command word.
	     */
	for(j = 0; j < COUNTOF(commands); j++)
	if (!strncasecmp(commands[j].word.word, src->entry[iwrd + 1].string.word, src->entry[iwrd + 1].string.length) ) {
	    *position = iwrd + 1;
	    return commands[j].command;
		}
	}

    return UNKNOWN;
}
static COMMAND commands[] = {
    { { 4,0, "QUIT" }, "quits the program and saves MegaHAL's brain", QUIT },
    { { 4,0, "EXIT" }, "exits the program *without* saving MegaHAL's brain", EXIT },
    { { 4,0, "SAVE" }, "saves the current MegaHAL brain", SAVE },
    { { 5,0, "DELAY" }, "toggles MegaHAL's typing delay (off by default)", DELAY },
    { { 6,0, "SPEECH" }, "toggles MegaHAL's speech (off by default)", SPEECH },
    { { 6,0, "VOICES" }, "list available voices for speech", VOICELIST },
    { { 5,0, "VOICE" }, "switches to voice specified", VOICE },
    { { 5,0, "BRAIN" }, "change to another MegaHAL personality", BRAIN },
    { { 4,0, "HELP" }, "displays this message", HELP },
    { { 5,0, "QUIET" }, "toggles MegaHAL's responses (on by default)",QUIET},
    /*
      { { 5,0, "STATS" }, "Display stats", STATS},
      { { 5,0, "STATS-SESSION" }, "Display stats for this session only",STATS_SESSION},
      { { 5,0, "STATS-ALL" },"Display stats for the whole lifetime",STATS-ALL},
	*/
};
void do_help(void)
{
    unsigned int j;

    for(j = 0; j < COUNTOF(commands); j++) {
	printf("#%-7s: %s\n", commands[j].word.word, commands[j].helpstring);
    }
    show_config(stdout);
}

char *megahal_initial_greeting(void)
{
    char *output;

    make_greeting(glob_greets);
    output = generate_reply(glob_model, glob_greets);
    return output;
}
/*---------------------------------------------------------------------------*/
/*
 *		Function:	Make_Greeting
 *		Purpose:		Put some special words into the dictionary so that the
 *						program will respond as if to a new judge.
 */
STATIC void make_greeting(struct sentence *target)
{
    // unsigned int iwrd;
    // for(iwrd = 0; iwrd < target->mused; iwrd++) free(target->entry[iwrd].string.word);
    target->mused = 0;
    // if (glob_grt->mused > 0) add_word_dodup(target, glob_grt->entry[ urnd(glob_grt->mused) ].string );
}


/*
 *		Function:	changevoice
 *		Purpose:		change voice of speech output.
 */
void changevoice(struct sentence* src, unsigned int position)
{
}
/*---------------------------------------------------------------------------*/
/*
 *		Function:	Delay
 *		Purpose:		Display the string to stdout as if it was typed by a human.
 */
void delay(char *string)
{
    size_t idx,len;

    if (typing_delay == FALSE)	{
	fprintf(stdout, "%s", string);
	return;
    }

    /*
     *		Display the entire string, one character at a time
     */
    len = strlen(string);
    for(idx = 0; idx < len-1; idx++) typein(string[idx]);
    usleep((D_THINK+urnd(V_THINK)-urnd(V_THINK))/2);
    typein(string[idx]);
}

/*---------------------------------------------------------------------------*/

STATIC void free_words(DICT *words)
{
    unsigned int iwrd;

    if ( !words ) return;

    if (words->entry != NULL)
	for(iwrd = 0; iwrd < words->size; iwrd++) free_string(words->entry[iwrd].string);
}


/*
 *		Function:	Typein
 *		Purpose:		Display a character to stdout as if it was typed by a human.
 */
void typein(char c)
{
    /*
     *		Standard keyboard delay
     */
    usleep(D_KEY+urnd(V_KEY)-urnd(V_KEY));
    fprintf(stdout, "%c", c);
    fflush(stdout);

    /*
     *		A random thinking delay
     */
    if ( !myisalnum(c) &&  urnd(100) < P_THINK)
	usleep(D_THINK+urnd(V_THINK)-urnd(V_THINK));
}

/*
 *		Function:	listvoices
 *		Purpose:		Display the names of voices for speech output.
 */
void listvoices(void)
{
}

/*---------------------------------------------------------------------------*/

/*
 *		Function:	Progress
 *		Purpose:		Display a progress indicator as a percentage.
 */
void progress(char *message, unsigned long done, unsigned long todo);
void progress(char *message, unsigned long done, unsigned long todo)
{
    static int last = 0;
    static int first = 0;

    if (noprogress) return ;
    /*
     *    We have already hit 100%, and a newline has been printed, so nothing
     *    needs to be done.
     *    WP: we could avoid div/zero.
     */
    if (!todo) todo = done?done:1;
    if (done*100/todo == 100 && !first ) return ;

    /*
     *    Nothing has changed since the last time this function was called,
     *    so do nothing, unless it's the first time!
     */
    if (done*100/todo == last) {
	if (done == 0 && !first ) {
	    fprintf(stderr, "%s: %3lu%%", message, done*100/todo);
	    first = 1;
	}
	return ;
    }

    /*
     *    Erase what we printed last time, and print the new percentage.
     */
    last = done*100/todo;

    if (done > 0) fprintf(stderr, "\b\b\b\b");
    fprintf(stderr, "%3lu%%", done*100/todo);

    /*
     *    We have hit 100%, so reset static variables and print a newline.
     */
    if (last == 100) {
	first = 0;
	last = 0;
	fprintf(stderr, "\n");
    }

    return ;
}

#endif /* DONT_WANT_THIS */

