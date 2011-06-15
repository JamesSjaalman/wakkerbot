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
#include <unistd.h>
#include <getopt.h>

#if !defined(AMIGA) && !defined(__mac_os)
#include <malloc.h>
#endif

#include <string.h>
#include <strings.h> /* strncasecmp */
#include <errno.h>
#include <signal.h>

#include <float.h> /* DBL_EPSILON */
#include <math.h>
#include <time.h>
#include <ctype.h>

#if defined(__mac_os)
#include <types.h>
#include <Speech.h>
#else
#include <sys/types.h>
#endif

#include "megahal.h"

#if defined(DEBUG)
#include "debug.h"
#endif


#define P_THINK 40
#define D_KEY 100000
#define V_KEY 50000
#define D_THINK 500000
#define V_THINK 250000

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

	/* define to outcomment old stuff */
#define DONT_WANT_THIS 0

	/* this is an ugly hack to cast a string pointer named 'str' to an unsigned char
	** This is absolutely necessary for the isXXXX() functions which
	** expect an int in the range 0...255 OR -a (for EOF)
	** Using a signed char would sign-extend the argument to -128...127,
	** which causes the ctype[] array to be indexed out of bounds
	*/
#define UCPstr ((unsigned char *)str)

	/* some develop/debug switches. 0 to disable */
#define WANT_DUMP_REHASH_TREE 0
#define WANT_DUMP_DELETE_DICT 0

	/* bitmask (0-3)
	** 1 := dump Xtab weight details
	** 2 := symbol_weight() prim/alt details
	** */
#define WANT_DUMP_KEYWORD_WEIGHTS 0

#define WANT_DUMP_ALZHEIMER_PROGRESS 1 /* 0...4 */
	/* show replies, every time evaluate_reply() finds a better candidate */
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
	/* The crossdict is a cross-table containing a keyword-keyword adjacency matrix.
	** this matrix is evaluated by a power-iteration algoritm, which basically
	** yields the first eigenvector and -value.
	** The matrix is fed with pairs of "n-adjacent" words, plus a distance.
	** The matrix has a fixed size; if a new insertion would make it bigger than
	** (CROSS_DICT_SIZE) the weakest keywords are removed.
	**
	** Only "rare" words (with "less than average" frequency of occurence) are considered.
	** Only pairs of words with a (distance <= CROSS_DICT_WORD_DISTANCE) are entered.
	** specifying a CROSS_DICT_WORD_DISTANCE of 3 will cause word[x] downto word[x-3] to
	** be entered into the matrix.
	*/
#define CROSS_DICT_SIZE 71
#define CROSS_DICT_WORD_DISTANCE 1

	/* Use keyword weights when evaluating the replies */
#define WANT_KEYWORD_WEIGHTS 1

	/* suppress whitespace; only store REAL words.
	** NOTE: changing this setting will require a complete rebuild of megahal's brain.
	** Without whitespace suppression, stretches of whitespace are just like ordinary
	** symbols *and references to them are stored in the nodes*.
	** With suppression of whitespace only "real tokens" (words and punctuation) are
	** used and stored in the nodes. This allows us to actually create a 5th order
	** MC (and not a word+white_word_white+word, which effectively is a 3d order).
	** The downside of this is that we'll have to re-insert the whitespace when
	** generating the output text.
	** Highly recommended.
	*/
#define WANT_SUPPRESS_WHITESPACE 1

	/*
	** ALZHEIMER_NODE_COUNT is the number of nodes we intend to maintain.
	** if the actual number of nodes exceeds this limit, the Alzheimer-functions might be triggered,
	** and the oldest nodes will be pruned. The timestamp is used as a poor man's LRU.
	** NOTE: this is the *intended* number. The actual number will fluctuate, and will
	** sometimes exceed this limit.
	**
	** (1/ALZHEIMER_FACTOR) is the chance of Alzheimer hitting the tree, once per reply or lerning step.
	** Zero to disable.
	** Alzheimer periodically does a complete treewalk (twice) to find and eliminate nodes
	** it considers too old.  This is expensive.
	** ALZHEIMER_FACTOR should be chosen such that Alzheimer hits us once every few minutes.
	** 100 could be a start.
	** (with a glob_timeout=DEFAULT_TIMEOUT=10 this would result in avg (1000s/2) between sweeps)
	** YMMV
	*/
#define ALZHEIMER_NODE_COUNT ( 35 * 1000 * 1000)
#define ALZHEIMER_FACTOR 100

	/* improved random generator, using noise from the CPU clock (only works on intel/gcc) */
#define WANT_RDTSC_RANDOM 1

	/* For TREEs, we use SQRT(n) as the value to increment/decrement with.
	** NOTE dicts will hardly ever be shrunk; only emptied.
	*/
#define DICT_SIZE_INITIAL 4
#define DICT_SIZE_SHRINK 16

	/* we don't want results smaller than this amount of tokens.
	** Note: both words and puntuation count as tokens.
	** whitespace does not count (if WANT_SUPPRESS_WHITESPACE is enabled)
 	*/
#define MIN_REPLY_SIZE 14
#define WANT_PARROT_CHECK (MIN_REPLY_SIZE)
#define PARROT_ADD(x) parrot_hash[ (x) % COUNTOF(parrot_hash)] += 1,parrot_hash2[ (x) % COUNTOF(parrot_hash2)] += 1

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

#ifdef __mac_os
#define bool Boolean
#endif

#ifdef DOS
#define SEP "\\"
#else
#define SEP "/"
#endif

#ifdef AMIGA
#undef toupper
#define toupper(x) ToUpper(x)
#undef tolower
#define tolower(x) ToLower(x)
#undef isalpha
#define isalpha(x) IsAlpha(_AmigaLocale,x)
#undef isalnum
#define isalnum(x) IsAlNum(_AmigaLocale,x)
#undef isdigit
#define isdigit(x) IsDigit(_AmigaLocale,x)
#undef isspace
#define isspace(x) IsSpace(_AmigaLocale,x)
#endif

#ifndef __mac_os
#undef FALSE
#undef TRUE
typedef enum { FALSE, TRUE } bool;
#endif

typedef unsigned char StrLen;
typedef unsigned char StrType;
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

typedef struct {
    StrLen length;
    StrType type;	/* type is not stored in the brainfile but recomputed on loading */
    char *word;
} STRING;

struct	dictslot {
	WordNum tabl;
	WordNum link;
	HashVal hash;
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

typedef struct {
    Count size;
    struct {
    	STRING from;
    	STRING to;
	} *pairs;
} SWAP;

struct treeslot {
    ChildIndex tabl;
    ChildIndex link;
    struct node *ptr;
	};

typedef struct node {
    UsageCnt childsum; /* sum of children's count */
    UsageCnt thevalue; /* my count */
    WordNum symbol;
    Stamp stamp;
    ChildIndex msize;
    ChildIndex branch;
    struct treeslot *children;
} TREE;

typedef struct {
    Count order;
    TREE *forward;
    TREE *backward;
    TREE **context;
    DICT *dict;
} MODEL;

struct memstat {
	unsigned word_cnt;
	unsigned node_cnt;
	unsigned alloc;
	unsigned free;
	unsigned alzheimer;
	unsigned symdel;
	unsigned treedel;
	} volatile memstats = {0,0,0,0,0,0,0} ;

typedef enum { UNKNOWN, QUIT, EXIT, SAVE, DELAY, HELP, SPEECH, VOICELIST, VOICE, BRAIN, QUIET} COMMAND_WORDS;

typedef struct {
    STRING word;
    char *helpstring;
    COMMAND_WORDS command;
} COMMAND;

/*===========================================================================*/

static char *errorfilename = "megahal.log";
static char *statusfilename = "megahal.txt";
static int glob_width = 45;
static int glob_order = 5;
static int glob_timeout = DEFAULT_TIMEOUT;

static bool typing_delay = FALSE;
static bool noprompt = FALSE;
static bool noprogres = FALSE;
static bool speech = FALSE;
static bool nowrap = FALSE;
static bool nobanner = FALSE;
static bool quiet = FALSE;
static FILE *errorfp;
static FILE *statusfp;

#if WANT_PARROT_CHECK
unsigned parrot_hash[WANT_PARROT_CHECK] = {0,};
unsigned parrot_hash2[WANT_PARROT_CHECK+1] = {0,};
#endif /* WANT_PARROT_CHECK */
#if DONT_WANT_THIS
static bool used_key;
#endif
static MODEL *glob_model = NULL;
	/* Refers to a dup'd fd for the brainfile, used for locking */
static int glob_fd = -1;
#if 1||CROSS_DICT_SIZE
#include "crosstab.h"
struct crosstab *glob_crosstab = NULL;
	/* this is ugly: a copy of model->dict is needed just for formatting the symbols
	** in the callback for the print-crosstab function
	*/
static DICT *glob_dict = NULL;
#endif

static DICT *glob_ban = NULL;
static DICT *glob_aux = NULL;
static DICT *glob_grt = NULL;
static SWAP *glob_swp = NULL;

static char *glob_directory = NULL;
static char *last_directory = NULL;

static Stamp stamp_min = 0xffffffff, stamp_max=0;

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

#ifdef AMIGA
struct Locale *_AmigaLocale;
#endif

#ifdef __mac_os
Boolean gSpeechExists = false;
SpeechChannel gSpeechChannel = nil;
#endif

STATIC int resize_tree(TREE *tree, unsigned newsize);

STATIC void add_swap(SWAP *list, char *from, char *to);
STATIC TREE *add_symbol(TREE *, WordNum);
STATIC WordNum add_word_dodup(DICT *dict, STRING word);
STATIC size_t word_format(char *buff, STRING string);
STATIC size_t symbol_format(char *buff, WordNum sym);

STATIC size_t tokenize(char *string, int *sp);

STATIC void delay(char *);
STATIC void die(int);
STATIC void error(char *, char *, ...);
STATIC void exithal(void);
STATIC TREE *find_symbol(TREE *node, WordNum symbol);
STATIC TREE *find_symbol_add(TREE *, WordNum);

STATIC WordNum find_word(DICT *, STRING);
STATIC void help(void);
STATIC void ignore(int);
STATIC bool initialize_error(char *);
#ifdef __mac_os
STATIC bool initialize_speech(void);
#endif
STATIC bool initialize_status(char *);
STATIC void listvoices(void);
STATIC DICT *new_dict(void);

STATIC char *read_input(char * prompt);
STATIC void save_model(char *, MODEL *);
#ifdef __mac_os
STATIC char *strdup(const char *);
#endif
STATIC void log_input(char *);
STATIC void log_output(char *);
#if defined(DOS) || defined(__mac_os)
STATIC void usleep(int);
#endif

STATIC char *format_output(char *);
STATIC void empty_dict(DICT *dict);
STATIC void free_model(MODEL *);
STATIC void free_tree(TREE *);
STATIC void free_string(STRING word);
STATIC void free_words(DICT *words);

STATIC void initialize_context(MODEL *);
STATIC void initialize_dict(DICT *);
STATIC DICT *read_dict(char *filename);
STATIC SWAP *initialize_swap(char *);
STATIC void load_dict(FILE *, DICT *);
STATIC bool load_model(char *path, MODEL *mp);
STATIC void load_personality(MODEL **);
STATIC TREE * load_tree(FILE *);
STATIC void load_word(FILE *, DICT *);
STATIC MODEL *new_model(int);
STATIC TREE *node_new(unsigned nchild);
STATIC SWAP *new_swap(void);
STATIC STRING new_string(char *str, size_t len);
STATIC bool print_header(FILE *);
bool progress(char *message, unsigned long done, unsigned long todo);
STATIC void save_dict(FILE *, DICT *);
STATIC unsigned save_tree(FILE *, TREE *);
STATIC void save_word(FILE *, STRING);
STATIC WordNum seed(MODEL *);

STATIC void show_dict(DICT *);
STATIC void speak(char *);
STATIC bool status(char *, ...);
STATIC void train(MODEL *, char *);
STATIC void typein(char);
STATIC void update_context(MODEL *, WordNum symbol);
STATIC void update_model(MODEL *model, WordNum symbol);
STATIC bool warn(char *, char *, ...);
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
STATIC int myiswhite(int ch);
STATIC int word_is_usable(STRING word);
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
#define TOKEN_MISC 8

STATIC void del_symbol_do_free(TREE *tree, WordNum symbol);
STATIC void del_word_dofree(DICT *dict, STRING word);
void free_tree_recursively(TREE *tree);
STATIC unsigned model_alzheimer(MODEL * model, unsigned maxnodecount);
STATIC unsigned symbol_alzheimer_recurse(TREE *tree, unsigned lev, unsigned lim);
static int check_interval(unsigned min, unsigned max, unsigned this);
void read_dict_from_ascii(DICT *dict, char *name);
static DICT *alz_dict = NULL;

STATIC void dump_model(MODEL * model, char *path, int flags);
STATIC void dump_model_recursive(FILE *fp, TREE *tree, DICT *dict, int indent);

STATIC ChildIndex *node_hnd(TREE *node, WordNum symbol);
STATIC void format_treeslots(struct treeslot *slots , unsigned size);
STATIC void show_memstat(char *msg);
STATIC int treeslots_cmp(const void *vl, const void *vr);
STATIC void treeslots_sort(struct treeslot  *slots , unsigned count);

STATIC STRING word_dup_lowercase(STRING org);
STATIC STRING word_dup_initcaps(STRING org);
STATIC STRING word_dup_othercase(STRING org);
	/* The weight we want we want to associate with a word.
	** if want_other is nonzero, we are also interested in
	** other capitalisations of the word.
	*/
STATIC double word_weight(DICT *dict, STRING word, int want_other);
STATIC double symbol_weight(DICT *dict, WordNum symbol, int want_other);
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
	unsigned size;
	unsigned msize;
	struct	{
		STRING string;
		} *entry;
	} ;
struct sentence *glob_input = NULL;
struct sentence *glob_greets = NULL;
STATIC void make_words(char * str, struct sentence * dst);
STATIC void add_word_to_sentence(struct sentence *dst, STRING word);
STATIC void learn_from_input(MODEL * mp, struct sentence *src);
STATIC char *generate_reply(MODEL *mp, struct sentence *src);
STATIC double evaluate_reply(MODEL *model, struct sentence *sentence);
STATIC void make_greeting(struct sentence *dst);
STATIC struct sentence * sentence_new(void);
STATIC int sentence_grow(struct sentence *ptr);
STATIC int sentence_resize(struct sentence *ptr, unsigned newsize);
STATIC void sentence_reverse(struct sentence *ptr);
STATIC struct sentence *one_reply(MODEL *);
STATIC COMMAND_WORDS execute_command(struct sentence *, unsigned int *position);
STATIC void changevoice(struct sentence *, unsigned int);
STATIC void change_personality(struct sentence *, unsigned int, MODEL **);
STATIC void make_keywords(MODEL *mp, struct sentence *src);
STATIC bool dissimilar(struct sentence *one, struct sentence *two);
STATIC WordNum babble(MODEL *model, struct sentence *words);
STATIC char *make_output(struct sentence *src);

void megahal_setquiet(void)
{
    quiet = TRUE;
}

void megahal_setnoprompt(void)
{
    noprompt = TRUE;
}

void megahal_setnoprogres(void)
{
    noprogres = TRUE;
}

void megahal_setnowrap (void)
{
    nowrap = TRUE;
}
void megahal_setnobanner (void)
{
    nobanner = TRUE;
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
    ignore(0);

#ifdef AMIGA
    _AmigaLocale = OpenLocale(NULL);
#endif
#ifdef __mac_os
    gSpeechExists = initialize_speech();
#endif
    if (!nobanner)
	fprintf(stdout,
		"+------------------------------------------------------------------------+\n"
		"|                                                                        |\n"
		"|  #    #  ######   ####     ##    #    #    ##    #                     |\n"
		"|  ##  ##  #       #    #   #  #   #    #   #  #   #               ###   |\n"
		"|  # ## #  #####   #       #    #  ######  #    #  #              #   #  |\n"
		"|  #    #  #       #  ###  ######  #    #  ######  #       #   #   ###   |\n"
		"|  #    #  #       #    #  #    #  #    #  #    #  #        # #   #   #  |\n"
		"|  #    #  ######   ####   #    #  #    #  #    #  ######    #     ###r6 |\n"
		"|                                                                        |\n"
		"|                    Copyright(C) 1998 Jason Hutchens                    |\n"
		"+------------------------------------------------------------------------+\n"
		);

    glob_input = sentence_new();
    glob_greets = sentence_new();
    change_personality(NULL, 0, &glob_model);
    while (bogus--) urnd(42);
}

/*
   megahal_do_reply --

   Take string as input, and return allocated string as output.  The
   user is responsible for freeing this memory.

  */

char *megahal_do_reply(char *input, int log)
{
    char *output = NULL;

    if (log != 0)
	log_input(input);  /* log input if so desired */

    make_words(input, glob_input);
    if (!glob_timeout) learn_from_input(glob_model, glob_input);
    else output = generate_reply(glob_model, glob_input);
    return output;
}

/*
   megahal_learn_no_reply --

   Take string as input, update model but don't generate reply.

  */

void megahal_learn_no_reply(char *input, int log)
{
    if (log != 0)
	log_input(input);  /* log input if so desired */

    make_words(input, glob_input);

    learn_from_input(glob_model, glob_input);
}

/*
   megahal_initial_greeting --

   This function returns an initial greeting.  It can be used to start
   Megahal conversations, but it isn't necessary.

  */

char *megahal_initial_greeting(void)
{
    char *output;

    make_greeting(glob_greets);
    output = generate_reply(glob_model, glob_greets);
    return output;
}

/*
   megahal_output --

   This function pretty prints output.

   Wrapper function to have things in the right namespace.

*/

void megahal_output(char *output)
{
    if (!quiet)
	log_output(output);
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
	help();
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
   megahal_cleanup --

   Clean up everything. Prepare for exit.

  */

void megahal_cleanup(void)
{
    save_model("megahal.brn", glob_model);

#ifdef AMIGA
    CloseLocale(_AmigaLocale);
#endif
    show_memstat("Cleanup" );
}


/*---------------------------------------------------------------------------*/

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
    *position = src->size+1;
    if (src->size <= 1) return UNKNOWN;

    /*
     *		Search through the word array.  If a command prefix is found,
     *		then try to match the following word with a command word.  If
     *		a match is found, then return a command identifier.  If the
     *		Following word is a number, then change the judge.  Otherwise,
     *		continue the search.
     */
    for(iwrd = 0; iwrd < src->size-1; iwrd++) {
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

/*---------------------------------------------------------------------------*/

/*
 *		Function:	ExitHAL
 *
 *		Purpose:		Terminate the program.
 */
STATIC void exithal(void)
{
#ifdef __mac_os
    /*
     *		Must be called because it does use some system memory
     */
    if (gSpeechChannel) {
	StopSpeech(gSpeechChannel);
	DisposeSpeechChannel(gSpeechChannel);
	gSpeechChannel = nil;
    }
#endif

#if WANT_DUMP_MODEL
    dump_model(glob_model, "megahal.dmp", WANT_DUMP_MODEL);
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
 *		keep any pointers into the reterned string.
 */
STATIC char *read_input(char *prompt)
{
    static char *input = NULL;
    static size_t msize=0;
    bool seen_eol;
    size_t length;
    int c;

    /*
     *		Perform some initializations.  The seen_eol boolean variable is used
     *		to detect a double line-feed, while length contains the number of
     *		characters in the input string.
     */
    seen_eol = FALSE;
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

	/*
	 *		Read a single character from stdin.
	 */
	c = getc(stdin);

	/*
	 *		If the character is a line-feed, then set the seen_eol variable
	 *		to TRUE.  If it already is TRUE, then this is a double line-feed,
	 *		in which case we should exit.  After a line-feed, display the
	 *		prompt again, and set the character to the space character, as
	 *		we don't permit linefeeds to appear in the input.
	 */
	if (c == -1 ) {
	    if (seen_eol == TRUE) break; else return NULL;
		}
	if (c == -1 || c == '\n') {
	    if (seen_eol == TRUE) break;
	    if (prompt) { fprintf(stdout, "%s", prompt); fflush(stdout); }
	    seen_eol = TRUE;
	    c = ' ';
	} else {
	    seen_eol = FALSE;
	}

	/*
	 *		Re-allocate the input string so that it can hold one more
	 *		character.
	 */
	/* This will end execution on two consecutive empty lines*/
	/* if (seen_eol && !length) return NULL;*/

	if (length +2 >= msize) {
		input = realloc(input, msize? 2*msize: 16);
		if (input) msize = msize ? 2 * msize : 16;
		}
	if (!input) {
	    error("read_input", "Unable to re-allocate the input string");
	    return NULL;
	}

	/*
	 *		Add the character just read to the input string.
	 */
	input[length++] = c;
	input[length] ='\0';
    }

    while(length > 0 && isspace(input[length-1])) length--;
    input[length] = '\0';

    /*
     *		We have finished, so return the input string.
     */
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
STATIC bool initialize_error(char *filename)
{
    if (errorfp != stderr) fclose(errorfp);

    if (!filename) return TRUE;

    errorfp = fopen(filename, "a");
    if (!errorfp) {
	errorfp = stderr;
	return FALSE;
    }
    return print_header(errorfp);
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

STATIC bool warn(char *title, char *fmt, ...)
{
    va_list argp;

    fprintf(errorfp, "%s: ", title);
    va_start(argp, fmt);
    vfprintf(errorfp, fmt, argp);
    va_end(argp);
    fprintf(errorfp, ".\n");
    fflush(errorfp);

    fprintf(stderr, MY_NAME " emitted a warning; check the error log.\n");

    return TRUE;
}

STATIC void show_memstat(char *msg)
{
if (!msg) msg = "..." ;

status( "[ stamp Min=%u Max=%u ]\n", (unsigned) stamp_min, (unsigned) stamp_max);
status ("Memstat %s: {wordcnt=%u nodecnt=%u alloc=%u free=%u alzheimer=%u symdel=%u treedel=%u}\n"
	, msg
	, memstats.word_cnt , memstats.node_cnt
	, memstats.alloc , memstats.free
	, memstats.alzheimer , memstats.symdel , memstats.treedel
	);
}
/*---------------------------------------------------------------------------*/

/*
 *		Function:	Initialize_Status
 *
 *		Purpose:		Close the current status file pointer, and open a new one.
 */
STATIC bool initialize_status(char *filename)
{
    if (statusfp != stdout) fclose(statusfp);
    if (!filename) return FALSE;
    statusfp = fopen(filename, "a");
    if (!statusfp) {
	statusfp = stdout;
	return FALSE;
    }
    return print_header(statusfp);
}

/*---------------------------------------------------------------------------*/

/*
 *		Function:	Status
 *
 *		Purpose:		Print the specified message to the status file.
 */
STATIC bool status(char *fmt, ...)
{
    va_list argp;

    va_start(argp, fmt);
    vfprintf(statusfp, fmt, argp);
    va_end(argp);
    fflush(statusfp);

    return TRUE;
}

/*---------------------------------------------------------------------------*/

/*
 *		Function:	Print_Header
 *
 *		Purpose:		Display a copyright message and timestamp.
 */
STATIC bool print_header(FILE *fp)
{
    time_t clock;
    char timestamp[1024];
    struct tm *local;

    clock = time(NULL);
    local = localtime(&clock);
    strftime(timestamp, 1024, "Start at: [%Y/%m/%d %H:%M:%S]\n", local);

    fprintf(fp, "MegaHALv8\n");
    fprintf(fp, "Copyright (C) 1998 Jason Hutchens\nCompiled Wakkerbot %s %s\n%s"
	, __DATE__ , __TIME__, timestamp);
    fflush(fp);

    return TRUE;
}

/*---------------------------------------------------------------------------*/

/*
 *    Function:   Write_Output
 *
 *    Purpose:    Display the output string.
 */
STATIC void log_output(char *output)
{
    char *formatted;
    char *bit;

    speak(output);

    // glob_width = 75;
    // formatted = format_output(output);
    // delay(formatted);
    // glob_width = 64;
    formatted = format_output(output);

    bit = strtok(formatted, "\n");
    if (!bit) (void)status(MY_NAME ": %s\n", formatted);
    while(bit) {
	(void)status(MY_NAME ": %s\n", bit);
	bit = strtok(NULL, "\n");
    }
}

/*---------------------------------------------------------------------------*/

/*
 *    Function:   Write_Input
 *
 *    Purpose:    Log the user's input
 */
STATIC void log_input(char *input)
{
    char *formatted;
    char *bit;

    glob_width = 64;
    formatted = format_output(input);

    bit = strtok(formatted, "\n");
    if (!bit) (void)status("User:    %s\n", formatted);
    while(bit) {
	(void)status("User:    %s\n", bit);
	bit = strtok(NULL, "\n");
    }
}

/*---------------------------------------------------------------------------*/

/*
 *    Function:   Format_Output
 *
 *    Purpose:    Format a string to display nicely on a terminal of a given
 *                width.
 */
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

/*
 *		Function:	Add_Word_Nofuzz
 *
 *		Purpose:		Append a word to a dictionary, and return the identifier assigned to the word.
 *						The index is not searched or updated, and the new word is not dupped, only referenced.
 */
STATIC void add_word_to_sentence(struct sentence *dst, STRING word)
{

if (!dst) return ;

if (dst->size >= dst->msize && sentence_grow(dst)) return ;


dst->entry[dst->size++].string = word;

return ;

}
/*---------------------------------------------------------------------------*/

/*
 *		Function:	Add_Word
 *
 *		Purpose:		Add a word to a dictionary, and return the identifier
 *						assigned to the word.  If the word already exists in
 *						the dictionary, then return its current identifier
 *						without adding it again.
 */
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
	dict->entry[*np].hash = hash_word(this);
	}
return *np;

}

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
dict->entry[this].hash = dict->entry[top].hash;
dict->entry[this].stats = dict->entry[top].stats;
	/* dont forget top's offspring */
dict->entry[this].link = dict->entry[top].link;
dict->entry[top].link = WORD_NIL;
dict->entry[top].stats.nnode = 0;
dict->entry[top].stats.valuesum = 0;
dict->entry[top].string.word = NULL;
dict->entry[top].string.length = 0;
dict->entry[top].hash = 0;

if (!dict->size || dict->size <= dict->msize - DICT_SIZE_SHRINK) {

#if (WANT_DUMP_DELETE_DICT >= 1)
    status("dict(%llu:%llu/%llu) will be shrunk: %u/%u\n"
 	, dict->stats.valuesum, dict->stats.nnode, dict->stats.nonzero, dict->branch, dict->msize);
#endif
    resize_dict(dict, dict->size);
    }
return ;
}

/*---------------------------------------------------------------------------*/

/*
 *		Function:	Find_Word
 *
 *		Purpose:		Return the symbol corresponding to the word specified.
 *						We assume that the word with index zero is equal to a
 *						NULL word, indicating an error condition.
 */
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
STRING this;

if (str) {
     if (!len) len = strlen(str);
     if (len) { this.word = malloc(len); memcpy(this.word, str, len); }
     else { this.word = malloc(1); memset(this.word, 0, 1); }
     this.length = len;
     this.type = word_classify(this);
     }
else	{
     this.word = NULL;
     this.length = 0;
     this.type = 0;
     }
return this;
}

/*---------------------------------------------------------------------------*/

/*
 *		Function:	Wordcmp
 *
 *		Purpose:		Compare two words, and return an integer indicating whether
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
	if (level == 0) progress("Freeing tree", 0, 1);
	for(ikid = 0; ikid < tree->branch; ikid++) {
	    level++;
	    free_tree(tree->children[ikid].ptr);
	    level--;
	    if (level == 0) progress(NULL, ikid, tree->branch);
	}
	if (level == 0) progress(NULL, 1, 1);
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
    static STRING word = {7,0, "<ERROR>" };
    static STRING end = {5,0, "<FIN>" };

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
dict->stats.nnode += nnode;
dict->entry[ symbol ].stats.valuesum += valuesum;
dict->stats.valuesum += valuesum;

return dict->entry[ symbol ].stats.valuesum;
}

STATIC unsigned long dict_dec_ref(DICT *dict, WordNum symbol, unsigned nnode, unsigned valuesum)
{

if (!dict || symbol >= dict->size ) return 0;

dict->entry[ symbol ].stats.nnode -= nnode;
if (dict->entry[ symbol ].stats.nnode == 0 ) dict->stats.nonzero -= 1;
dict->stats.nnode -= nnode;
dict->entry[ symbol ].stats.valuesum -= valuesum;
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
	slots[idx].hash = 0xe;
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
    progress("Saving dictionary", 0, 1);
    for(iwrd = 0; iwrd < dict->size; iwrd++) {
	save_word(fp, dict->entry[iwrd].string );
	progress(NULL, iwrd, dict->size);
    }
    progress(NULL, 1, 1);
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
    resize_dict(dict, dict->msize+size);
    status("Load_dictSize=%u Initial_dictSize=%u\n", size, dict->msize);
    progress("Loading dictionary", 0, 1);
    for(iwrd = 0; iwrd < size; iwrd++) {
	load_word(fp, dict);
	progress(NULL, iwrd, size);
    }
    progress(NULL, 1, 1);
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
    static STRING word = {0,0,zzz};
    size_t kuttje;

    kuttje = fread(&word.length, sizeof word.length, 1, fp);
    // word.word = malloc(word.length);
    if (!word.word) {
	error("load_word", "Unable to allocate word");
	return;
    }
    kuttje = fread(&word.word[0], word.length, 1, fp);
    add_word_dodup(dict, word);
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

    /*
     *		Allocate memory for the new node
     */
    node = malloc(sizeof *node);
    if (!node) {
	error("node_new", "Unable to allocate the node.");
	return NULL;
    }

    /*
     *		Initialise the contents of the node
     */
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
	goto fail;
    }

    model->order = order;
    model->forward = node_new(0);
    model->backward = node_new(0);
    model->context = malloc( (2+order) *sizeof *model->context);
    if (!model->context) {
	error("new_model", "Unable to allocate context array.");
	goto fail;
    }
    initialize_context(model);
    model->dict = new_dict();
    initialize_dict(model->dict);

    return model;

fail:
    return NULL;
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
     *		Update all of the models in the current context with the specified
     *		symbol.
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
 *		Function:	Add_Symbol
 *
 *		Purpose:		Update the statistics of the specified tree with the
 *						specified symbol, which may mean growing the tree if the
 *						symbol hasn't been seen in this context before.
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
    node->thevalue += 1; tree->childsum += 1;
    node->stamp = stamp_max; tree->stamp = stamp_max;
    if (!node->thevalue) {
	warn("add_symbol", "Count wants to wrap");
	node->thevalue -= 1;
    }
    if (!tree->childsum) {
	warn("add_symbol", "Usage wants to wrap");
	tree->childsum -= 1;
    }

    return node;
}

STATIC void dump_model(MODEL * model, char *path, int flags)
{
FILE *fp;

fp = fopen (path , "w" );
if (!fp) return;

fprintf(fp, "[ stamp Min=%u Max=%u ]\n", (unsigned)stamp_min, (unsigned)stamp_max);

if (flags & 1) {
	fprintf(fp, "->forward order=%u\n", (unsigned) model->order);
	dump_model_recursive(fp, model->forward, model->dict, 0);
	}

if (flags & 2) {
	fprintf(fp, "->backward order=%u\n", (unsigned) model->order);
	dump_model_recursive(fp, model->backward, model->dict, 0);
	}
fprintf(fp, "->Eof\n" );
fclose (fp);
}

STATIC void dump_model_recursive(FILE *fp, TREE *tree, DICT *dict, int indent)
{
unsigned slot;
WordNum sym;
static STRING null = {0,0,""};
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
    if (!top || top == this) {;}
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

/*
 *		Function:	Find_Symbol
 *
 *		Purpose:		Search the node. If one of its direct children
 *						refers to 'symbol' return a pointer to that child.
 */
STATIC TREE *find_symbol(TREE *node, WordNum symbol)
{
ChildIndex *ip;

ip = node_hnd(node, symbol);
if (!ip || *ip == CHILD_NIL) return NULL;

return node->children[*ip].ptr ;
}

/*---------------------------------------------------------------------------*/

/*
 *		Function:	Find_Symbol_Add
 *
 *		Purpose:		This function is conceptually similar to find_symbol,
 *						apart from the fact that if the symbol is not found,
 *						a new node for this symbol is allocated and added under the
 *						tree.
 */
STATIC TREE *find_symbol_add(TREE *node, WordNum symbol)
{
ChildIndex *ip;

ip = node_hnd(node, symbol);

/* if (!ip) return NULL; */
if (!ip || *ip == CHILD_NIL) { /* not found: create one */
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
        if (!ip) {
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
	fprintf(stderr, "Old=%p:%u New=%p:%u Tree_resize(%u/%u) %u\n"
	, (void*) old, (void*) tree->children, newsize, tree->branch,  tree->msize);
#endif /* WANT_DUMP_REHASH_TREE */

/* Now rebuild the hash table.
 * The hash-chain pointers have already been initialized to NIL,
 * we only have to copy the children's "payload" verbatim,
 * find the place where to append it in the hash-chain, and put it there.
 *
 * Since we need to rebuild the hachchains anyway, this is a good place to
 * sort the items (in descending order) to make life easier for babble() .
 * We only sort when the node is growing (newsize>oldsize), assuming ordering is more or less
 * fixed for older nodes. FIXME
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

STATIC void format_treeslots(struct treeslot  *slots , unsigned size)
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

if (!sl->ptr && ! sr->ptr) return 0;
if (!sl->ptr ) return 1;
if (!sr->ptr ) return -1;

if (sl->ptr->thevalue < sr->ptr->thevalue ) return 1;
if (sl->ptr->thevalue > sr->ptr->thevalue ) return -1;

if (sl->ptr->symbol < sr->ptr->symbol ) return -1;
if (sl->ptr->symbol > sr->ptr->symbol ) return 1;
return 0;

}

STATIC void treeslots_sort(struct treeslot  *slots , unsigned count)
{
#if 1
/* NOTE: quicksort is probably a bad choice here, since the childnodes are "almost ordered",
 * The sorting does not consume enough CPU to justify a mergesort or insertion sort variant.
 * (qsort ate 10% when training, most of it in the compare function)
 * This is a "one pass bubblesort"; it will _eventually_ get the array sorted.
 * Having the array sorted is not important: babble() may need some more steps
 * on an unsorted array.
 */
unsigned idx;
for (idx = 1; idx < count; idx++) {
	struct treeslot tmp;
	if (treeslots_cmp( &slots[idx-1], &slots[idx]) <= 0) continue;
	tmp = slots[idx-1];
	slots[idx-1] = slots[idx];
	slots[idx] = tmp;
	}
#else
qsort(slots, count, sizeof *slots, treeslots_cmp);
#endif
}
/* Profiling shows that node_hnd() is the biggest CPU consumer
** (unless Alzheimer kicks in ;-)
** I don't see a way to speed this thing up, apart from maybe making is static.
*/
STATIC ChildIndex *node_hnd(TREE *node, WordNum symbol)
{
ChildIndex *ip;
unsigned slot;

if (!node->msize) return NULL;
slot = symbol % node->msize;
for (ip = &node->children[ slot ].tabl; *ip != CHILD_NIL; ip = &node->children[ *ip ].link ) {
#if WANT_MAXIMAL_PARANOIA
	if (!node->children[ *ip ].ptr) {
		warn ( "Node_hnd", "empty child looking for %u\n", symbol);
		continue;
		}
#endif
	if (symbol == node->children[ *ip ].ptr->symbol) break;
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

    for(iord = 0; iord < 2+model->order; iord++) model->context[iord] = NULL;
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
/*		, (double ) dict->entry[i].stats.nnode * dict->size / dict->stats.node */

if (altsym==WORD_NIL) {
	/* this is to catch typos, which have an initial score of 2*(1+order) */
	if (dict->entry[symbol].stats.valuesum <= 12) return 0.00099;
	if (dict->entry[symbol].stats.nnode <= 12) return 0.00088;
	if (dict->entry[symbol].stats.valuesum == dict->entry[symbol].stats.nnode) return 0.00777;
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
STRING new = {0,0,zzz};
unsigned ii,chg;

if (!org.type) org.type =  word_classify(org);
switch (org.type) {
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
STRING new = {0,0,zzz};
unsigned ii;

new.length = org.length;
new.type = TOKEN_LOWER;

for (ii = 0; ii < org.length; ii++) {
	if (myisupper( org.word[ii] )) new.word[ii] = org.word[ii] + ('a' - 'A');
	else new.word[ii] = org.word[ii] ;
	}
return new;
}

STATIC STRING word_dup_initcaps(STRING org)
{
static char zzz[1+STRLEN_MAX];
STRING new = {0,0,zzz};
unsigned ii;

new.length = org.length;
new.type = TOKEN_INITCAPS;

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
unsigned upper=0, lower=0,number=0,high=0,other=0, initcaps=0;

if (!org.length) return 0; /* ajuus */
for (ii = 0; ii < org.length; ii++) {
	if (org.word[ii] >= 'A' && org.word[ii] <= 'Z' ) { if (ii) upper++; else initcaps++; }
	else if (org.word[ii] >= 'a' && org.word[ii] <= 'z' ) lower++;
	else if (org.word[ii] >= '0' && org.word[ii] <= '9' ) number++;
	else if (org.word[ii] & 0x80 ) high++;
	else other++;
	}
if (lower == ii) return TOKEN_LOWER; /* pvda */
if (upper+initcaps == ii) return TOKEN_UPPER; /* PVDA */
if (lower+initcaps == ii) return TOKEN_INITCAPS; /* Pvda */
if (lower+upper+initcaps == ii) return TOKEN_CAMEL; /* PvdA */
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
     */
    if (words->size <= model->order) return;
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
    for(widx = 0; widx < words->size; widx++) {
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
    for(widx = words->size; widx-- > 0; ) {
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
 *		Purpose:	 	Infer a MegaHAL brain from the contents of a text file.
 */
STATIC void train(MODEL *model, char *filename)
{
    FILE *fp;
    static struct sentence *exercise = NULL;
    int length;
    char buffer[4*1024];

    if (!filename) return;

    fp = fopen(filename, "r");
    if (!fp) {
	printf("Unable to find the personality %s\n", filename);
	return;
    }

    fseek(fp, 0, 2);
    length = ftell(fp);
    rewind(fp);

    if (!exercise) exercise = sentence_new();
    else exercise->size = 0;
    

    progress("Training from file", 0, 1);
    while( fgets(buffer, sizeof buffer, fp) ) {
	if (buffer[0] == '#') continue;

	buffer[strlen(buffer)-1] ='\0';

	make_words(buffer, exercise);
	learn_from_input(model, exercise);

	progress(NULL, ftell(fp), length);

    }
    progress(NULL, 1, 1);

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
	warn("show_dict", "Unable to open file");
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
    STRING word = {0,0,NULL};


    if (!dict) return;

    fp = fopen( name, "r");
    if (!fp) {
	warn("read_dict", "Unable to open file");
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
        word.type = word_classify(word);
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

    filename = realloc(filename, strlen(glob_directory)+strlen(SEP)+12);
    if (!filename) error("save_model","Unable to allocate filename");

    show_dict(model->dict);
    if (!filename) return;

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
    status("Saved %lu(%lu+%lu) nodes, %u words.\n"
	, memstats.node_cnt, forw, back
	,memstats.word_cnt);
    fclose(fp);
    close( glob_fd  ); glob_fd = -1;
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
    if (level == 0) progress("Saving tree", 0, 1);
    for(ikid = 0; ikid < node->branch; ikid++) {
	level++;
	count += save_tree(fp, node->children[ikid].ptr );
	level--;
	if (level == 0) progress(NULL, ikid, node->branch);
    }
    if (level == 0) progress(NULL, 1, 1);
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
    kuttje = fread(&this.childsum, sizeof this.childsum, 1, fp);
    kuttje = fread(&this.thevalue, sizeof this.thevalue, 1, fp);
    kuttje = fread(&this.stamp, sizeof this.stamp, 1, fp);
    if ( this.stamp > stamp_max) stamp_max = this.stamp;
    else if ( this.stamp < stamp_min) stamp_min = this.stamp;
    kuttje = fread(&this.branch, sizeof this.branch, 1, fp);
    // if (this.branch == 0) return NULL;

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

    if (level == 0) progress("Loading tree", 0, 1);
    childsum = 0;
    for(cidx = 0; cidx < ptr->branch; cidx++) {
	// node->children[cidx].ptr = node_new(0);
	level++;
	// load_tree(fp, node->children[cidx].ptr);
	ptr->children[cidx].ptr = load_tree(fp);
	level--;

	if (ptr->children[cidx].ptr ) childsum += ptr->children[cidx].ptr->thevalue;
	symbol = ptr->children[cidx].ptr ? ptr->children[cidx].ptr->symbol: cidx;
	ip = node_hnd(ptr, symbol );
	if (ip) *ip = cidx;
	if (level == 0) progress(NULL, cidx, ptr->branch);
    }
    if (childsum != ptr->childsum) {
		fprintf(stderr, "Oldvalue = %llu <- Newvalue= %llu\n"
		, (unsigned long long) ptr->childsum , (unsigned long long) childsum);
		ptr->childsum = childsum;
		}
    if (level == 0) progress(NULL, 1, 1);
return ptr;
}

/*---------------------------------------------------------------------------*/

/*
 *		Function:	Load_Model
 *
 *		Purpose:		Load a model into memory.
 */
STATIC bool load_model(char *filename, MODEL *model)
{
    FILE *fp;
    char cookie[16];
    unsigned refcount;
    size_t kuttje;


    if (!filename) return FALSE;

    // fp = fopen(filename, "rb");
    fp = fopen(filename, "rb+"); //lockf needs write permission

    if (!fp) {
	warn("load_model", "Unable to open file `%s'", filename);
	return FALSE;
    }
    while (1) {
	int rc;
	if (glob_fd < 0) rc = dup( fileno(fp) );
	else rc = dup2( fileno(fp), glob_fd  );
	if (rc == -1) {
		rc = errno;
		warn("load_model", "Unable to dup2 file `%s' err=%d(%s) ", filename, rc, strerror(rc) );
		fclose (fp);
		return FALSE;
		}
	glob_fd = rc;
	rc = lockf( glob_fd, F_TLOCK, sizeof cookie );
	if (!rc) break;
	rc = errno;
	warn("load_model", "Unable to lock file `%s' err=%d(%s) ", filename, rc, strerror(rc) );
	sleep (5);
	}


    kuttje = fread(cookie, sizeof(char), strlen(COOKIE), fp);
    if (kuttje != strlen(COOKIE) ) {
	warn("load_model", "Read %u/%u from '%s' : %d (%s)\n"
		, (unsigned) kuttje, (unsigned) strlen(COOKIE), filename
		, errno, strerror(errno)
		);
	exit(1);
	}
    if (memcmp(cookie, COOKIE, strlen(COOKIE)) ) {
	warn("load_model", "File `%s' is not a MegaHAL brain: coockie='%s' (expected '%s')"
		, filename , cookie,COOKIE);
	goto fail;
    }
    memstats.node_cnt = 0;
    memstats.word_cnt = 0;
    kuttje = fread(&model->order, sizeof model->order, 1, fp);
    status("Loading %s order= %u\n", filename, (unsigned)model->order);
    if (model->order != glob_order) {
        model->order = glob_order;
        model->context = realloc(  model->context, (2+model->order) *sizeof *model->context);
        status("Set Order to %u order= %u\n", (unsigned)model->order);
	}
    status("Forward\n");
    // load_tree(fp, model->forward);
    model->forward = load_tree(fp);
    status("Backward\n");
    // load_tree(fp, model->backward);
    model->backward = load_tree(fp);
    status("Dict\n");
#if 1
    load_dict(fp, model->dict);
#else
    read_dict_from_ascii(model->dict, "megahal.dic" );
#endif
    refcount = set_dict_count(model);
    status("Loaded %lu nodes, %u words. Total refcount= %u maxnodes=%lu\n"
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

    return TRUE;
fail:
    fclose(fp);

    return FALSE;
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
    STRING word ;
    static STRING period = {1,0, "." }  ;
    int state = 0; /* FIXME: this could be made static to allow for multi-line strings */

    target->size = 0;

    len = strlen(src);
    if (!len) return;

    for(pos=0; pos < len ; ) {

	chunk = tokenize(src+pos, &state);
        if (!chunk) { /* maybe we should reset state here ... */ pos++; }
        if (chunk > STRLEN_MAX) {
            warn( "Make_words", "Truncated too long string(%u) at %s\n", (unsigned) chunk, src+pos);
            chunk = STRLEN_MAX;
            }
        word.length = chunk;
        word.word = src+pos;
#if WANT_SUPPRESS_WHITESPACE
        if (word_is_usable(word)) add_word_to_sentence(target, word);
#else
        add_word_to_sentence(target, word);
#endif

        if (pos+chunk >= len) break;
        pos += chunk;
    }

    /*
     *		If the last word isn't punctuation, then replace it with a
     *		full-stop character.
     */
    if (target->size && myisalnum(target->entry[target->size-1].string.word[0])) {
		add_word_to_sentence(target, period);
    }
    else if (target->size
		&& target->entry[target->size-1].string.length
		 && !strchr(".!?", target->entry[target->size-1].string.word[ target->entry[target->size-1].string.length-1] )) {
	target->entry[target->size-1].string = period;
    }

    return;
}
/*---------------------------------------------------------------------------*/
/*
 *		Function:	Tokenize
 *
 *		Purpose:		Find the length of the token started @ string
 * This tokeniser attempts to respect abbreviations such as R.W.A or R.w.a.
 * Also numeric literals, such as 200.50 are left alone (almost the same for 200,50 or 200.000,00)
 * Maybe 10e-0.6 should also be recognised.
 * multiple stretches of .,!? are kept intact, multiple stretches of
 * other non alphanumerc tokens (@#$%^&*) as well.
 * brackets and braces are always chopped up to 1-character tokens.
 * quoted strings are not respected, but broken up into seperate tokens.
 * The quotes are treated as seperate tokens too.
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
STATIC size_t tokenize(char *str, int *sp)
{
    /* unsigned char *ucp = (unsigned char *) str;*/
    size_t pos ;

    for(pos=0; str[pos]; ) {
    switch(*sp) {
    case T_INIT: /* initial */
#if 0
	/* if (UCPstr[pos] == '\'' ) { *sp |= 16; return pos; }*/
	/* if (UCPstr[posi] == '"' ) { *sp |= 32; return pos; }*/
#endif
    	if (myisalpha(UCPstr[pos])) {*sp = T_WORD; pos++; continue; }
    	if (myisalnum(UCPstr[pos])) {*sp = T_NUM; pos++; continue; }
	/* if (strspn(str+pos, "-+")) { *sp = T_NUM; pos++; continue; }*/
	*sp = T_ANY; continue;
	break;
    case T_ANY: /* either whitespace or meuk: eat it */
    	pos += strspn(str+pos, " \t\n\r\f\b" );
	if (pos) {*sp = T_INIT; return pos; }
        *sp = T_MEUK; continue;
        break;
    case T_WORD: /* inside word */
	while ( myisalnum(UCPstr[pos]) ) pos++;
    	if (UCPstr[pos] == '\0' ) { *sp = T_INIT;return pos; }
	if (UCPstr[pos] == '.' ) { *sp = T_WORDDOT; pos++; continue; }
	*sp = T_INIT; return pos;
        break;
    case T_WORDDOT: /* word. */
	if (myisalpha(UCPstr[pos]) ) { *sp = T_WORDDOTLET; pos++; continue; }
	*sp = T_INIT; return pos-1;
        break;
    case T_WORDDOTLET: /* word.A */
	if (UCPstr[pos] == '.') { *sp = T_AFKODOT; pos++; continue; }
	if (myisalpha(UCPstr[pos]) ) { *sp = T_INIT; return pos-2; }
	if (myisalnum(UCPstr[pos]) ) { *sp = T_NUM; continue; }
	*sp = T_INIT; return pos-2;
        break;
    case T_AFKODOT: /* A.B. */
        if (myisalpha(UCPstr[pos]) ) { *sp = T_AFKO; pos++; continue; }
        *sp = T_INIT; return pos >=3? pos: pos -2;
        break;
    case T_AFKO: /* word.A.B */
	if (UCPstr[pos] == '.') { *sp = T_AFKODOT; pos++; continue; }
	/* if (myisalpha(UCPstr[pos]) ) { pos++; continue; }*/
	if (myisalpha(UCPstr[pos]) ) { *sp = T_INIT; return pos - 2; }
	*sp = T_INIT; return pos-1;
        break;
    case T_NUM: /* number */
	if ( myisalnum(UCPstr[pos]) ) { pos++; continue; }
	if (strspn(str+pos, ".,")) { *sp = T_NUMDOT; pos++; continue; }
	*sp = T_INIT; return pos;
        break;
    case T_NUMDOT: /* number[.,] */
	if (myisalpha(UCPstr[pos])) { *sp = T_NUMDOTLET; pos++; continue; }
	if (myisalnum(UCPstr[pos])) { *sp = T_NUM; pos++; continue; }
	if (strspn(str+pos, "-+")) { *sp = T_NUM; pos++; continue; }
	*sp = T_INIT; return pos-1;
        break;
    case T_NUMDOTLET: /* number[.,][a-z] */
	if (myisalpha(UCPstr[pos])) { *sp = T_INIT; return pos-2; }
	if (myisalnum(UCPstr[pos])) { *sp = T_NUM; pos++; continue; }
	*sp = T_INIT; return pos-2;
        break;
    case T_MEUK: /* inside meuk */
	if (myisalnum(UCPstr[pos])) {*sp = T_INIT; return pos; }
	if (myiswhite(UCPstr[pos])) {*sp = T_INIT; return pos; }
	if (strspn(str+pos, ".,?!" )) { if (!pos) *sp = T_PUNCT; else { *sp = T_INIT; return pos; }}
	if (strspn(str+pos, "@'\"" )) { *sp = T_INIT; return pos ? pos : 1; }
	if (strspn(str+pos, ":;" )) { *sp = T_INIT; return pos ? pos : 1; }
	if (strspn(str+pos, "('\"){}[]" )) { *sp = T_INIT; return pos ? pos : 1; }
	pos++; continue; /* collect all garbage */
        break;
    case T_PUNCT: /* punctuation */
	pos += strspn(str+pos, ".,?!" ) ;
        *sp = T_INIT; return pos ? pos : 1;
        break;
        }
    }
    /* This is ugly. Depending on the state,
    ** we need to know how many lookahead chars we took */
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

STATIC int myisalpha(int ch)
{
int ret = isalpha(ch);
if (ret) return ret;
	/* don't parse, just assume valid utf8*/
if (ch == -1) return 0;
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

STATIC int word_is_usable(STRING string)
{
unsigned idx;

if (string.length < 1) return 1;

for(idx = 0; idx < string.length; idx++) switch( string.word[idx] ) {
	case '\0':
	case '\n':
	case '\r':
	case '\t':
	case ' ': continue;
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
/*---------------------------------------------------------------------------*/
/*
 *		Function:	Make_Greeting
 *
 *		Purpose:		Put some special words into the dictionary so that the
 *						program will respond as if to a new judge.
 */
STATIC void make_greeting(struct sentence *target)
{
    // unsigned int iwrd;
    // for(iwrd = 0; iwrd < target->size; iwrd++) free(target->entry[iwrd].string.word);
    target->size = 0;
    // if (glob_grt->size > 0) add_word_dodup(target, glob_grt->entry[ urnd(glob_grt->size) ].string );
}

/*---------------------------------------------------------------------------*/
/*
 *    Function:   Generate_Reply
 *
 *    Purpose:    Take a string of user input and return a string of output
 *                which may vaguely be construed as containing a reply to
 *                whatever is in the input string.
 */
STATIC char *generate_reply(MODEL *model, struct sentence *src)
{
    static char *output_none = "Geert! doe er wat aan!" ;
	/* "I don't know enough to answer you yet!"; */
    struct sentence *zeresult;
    double rawsurprise, surprise, max_surprise;
    char *output;
    unsigned count;
    int basetime;
    double penalty;
#if WANT_PARROT_CHECK
    unsigned pidx,ssq1,sum1;
    double calc1;
    unsigned ssq2,sum2;
    double calc2,penalty1,penalty2;
#endif

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

    /*
    zeresult = one_reply(model);
     *		Loop for the specified waiting period, generating and evaluating
     *		replies
     */
    max_surprise = -100.0;
    penalty = 0.0;
    count = 0;
    basetime = time(NULL);
    progress("Generating reply", 0, 1);
    do {
	zeresult = one_reply(model);
	// if (zeresult->size < MIN_REPLY_SIZE) continue;
	rawsurprise = evaluate_reply(model, zeresult);
        /* if (rawsurprise >= -1000000 && rawsurprise <= 1000000) {;} 
	else continue; */
	count++;
#if WANT_PARROT_CHECK
	sum1=ssq1=0;
	for (pidx=0; pidx < COUNTOF(parrot_hash); pidx++) { 
	    sum1 += parrot_hash[pidx] ;
	    ssq1 += parrot_hash[pidx] * parrot_hash[pidx] ;
	    }
	if (sum1 <= 1) continue;
	calc1 = (sum1 * sum1) / (COUNTOF(parrot_hash)); /* estimated sum of squares */
	penalty1 = ((double)ssq1/calc1) ;

	sum2=ssq2=0;
	for (pidx=0; pidx < COUNTOF(parrot_hash2); pidx++) { 
	    sum2 += parrot_hash2[pidx] ;
	    ssq2 += parrot_hash2[pidx] * parrot_hash2[pidx] ;
	    }
	calc2 = (sum2 * sum2) / (COUNTOF(parrot_hash2)); /* estimated sum of squares */
	penalty2 = ((double)ssq2/calc2) ;
#if 1
	/* we use min(p1,p2) * p1 * p2; because (one of) p1,p2 might by inflated by
	** hash collisions */
        penalty = penalty1<penalty2 ?penalty1:penalty2 ;
        penalty = sqrt(penalty*penalty1*penalty2) ;
#else
	penalty = (penalty1*penalty2) / (penalty1+penalty2);
	penalty *= penalty;
#endif
        surprise = rawsurprise / penalty ;
        if ( (surprise - max_surprise) <= (5*DBL_EPSILON) ) continue;
#else
	if (surprise <= max_surprise || !dissimilar(src, zeresult) ) continue;
#endif /* WANT_PARROT_CHECK */

#if WANT_PARROT_CHECK
fprintf(stderr, "\nParrot1={" );
for (pidx=0; pidx < COUNTOF(parrot_hash); pidx++) { fprintf(stderr, " %u", parrot_hash[ pidx] ); }
fprintf(stderr, "} Sum=%u Ssq=%u Exp=%f Rat=%f\n"
, sum1, ssq1, calc1, penalty1 );

fprintf(stderr, "Parrot2={" );
for (pidx=0; pidx < COUNTOF(parrot_hash2); pidx++) { fprintf(stderr, " %u", parrot_hash2[ pidx] ); }
fprintf(stderr, "} Sum=%u Ssq=%u Exp=%f Rat=%f\n"
, sum2, ssq2, calc2, penalty2);
fprintf(stderr, "Penal=%f Raw=%f, Max=%f, Surp=%f"
 , penalty, rawsurprise, max_surprise, surprise);

#endif /* WANT_PARROT_CHECK */

	max_surprise = surprise;
	output = make_output(zeresult);
#if WANT_DUMP_ALL_REPLIES
fprintf(stderr, "\n%u %f N=%u (Typ=%d Fwd=%f Rev=%f):\n\t%s\n"
, count, surprise, (unsigned) zeresult->size
, init_typ_fwd, init_val_fwd, init_val_rev
, output);
#endif
 	progress(NULL, (time(NULL)-basetime),glob_timeout);
    } while(time(NULL)-basetime < glob_timeout);
    progress(NULL, 1, 1);
#if WANT_DUMP_ALL_REPLIES
	fprintf(stderr, "ReplyProbed=%u\n", count );
#endif

    /*
     *		Return the best answer we generated
     */
    return output;
}

/*---------------------------------------------------------------------------*/

/*
 *		Function:	Dissimilar
 *
 *		Purpose:		Return TRUE or FALSE depending on whether the dictionaries
 *						are the same or not.
 */
STATIC bool dissimilar(struct sentence *one, struct sentence *two)
{
    unsigned int iwrd;

    if (one->size != two->size) return TRUE;
    for(iwrd = 0; iwrd < one->size; iwrd++)
	if (wordcmp(one->entry[iwrd].string , two->entry[iwrd].string ) ) return TRUE;
    return FALSE;
}

/*---------------------------------------------------------------------------*/

/*
 *		Function:	Make_Keywords
 *
 *		Purpose:		Put all the interesting words from the user's input into
 *						a keywords dictionary, which will be used when generating
 *						a reply.
 */
STATIC void make_keywords(MODEL *model, struct sentence *src)
{
    unsigned int iwrd;
    WordNum symbol;

#if CROSS_DICT_SIZE
    STRING canonword;
    WordNum canonsym;
    WordNum echobox[CROSS_DICT_WORD_DISTANCE];
    unsigned rotor,echocount;
    unsigned other;

    if (!glob_crosstab ) {
	glob_crosstab = crosstab_init(CROSS_DICT_SIZE);
	}
    rotor = echocount = 0;
#else
    unsigned int ikey;
#endif


    for(iwrd = 0; iwrd < src->size; iwrd++) {
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
        // if (model->dict->entry[symbol].stats.nnode > model->dict->stats.nnode / model->dict->stats.nonzero ) continue;
        // if (model->dict->entry[symbol].stats.valuesum > model->dict->stats.valuesum / model->dict->stats.nonzero ) continue;
	if (symbol_weight(model->dict, symbol, 0) < 1.0) continue;
	canonword = word_dup_lowercase(model->dict->entry[symbol].string);
	canonsym = find_word( model->dict, canonword);
        if (canonsym >= model->dict->size) canonsym = symbol;

#if CROSS_DICT_SIZE
	for (other = 0; other < echocount; other++ ) {
		unsigned dist;
		dist = other > rotor ? (other - rotor) : (other+CROSS_DICT_WORD_DISTANCE -rotor);

		crosstab_add_pair( glob_crosstab, echobox[other] , canonsym, 1+CROSS_DICT_WORD_DISTANCE-dist );
		}
	if (echocount < COUNTOF(echobox)) echocount++;
	echobox[rotor] = canonsym;
	if (++rotor >= COUNTOF(echobox)) rotor =0;
#endif
	}

#if CROSS_DICT_SIZE
	crosstab_show(stderr, glob_crosstab, symbol_format);
#endif
}

/*---------------------------------------------------------------------------*/

/*
 *		Function:	Reply
 *
 *		Purpose:		Generate a dictionary of reply words appropriate to the
 *						given dictionary of keywords.
 */
STATIC struct sentence *one_reply(MODEL *model)
{
    static struct sentence *zereply = NULL;
    unsigned int widx;
    WordNum symbol;

    if (!zereply) zereply = sentence_new();
    else zereply->size = 0;

    /*
     *		Start off by making sure that the model's context is empty.
     */
    initialize_context(model);
    model->context[0] = model->forward;
#if DONT_WANT_THIS
    used_key = FALSE;
#endif

    /*
     *		Generate the reply in the forward direction.
     */
    for (symbol = seed(model); symbol > WORD_FIN ; symbol = babble(model, zereply) ) {
	/*
	 *		Append the symbol to the reply dictionary.
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
     *		dictionary so that we can generate backwards to reach the
     *		beginning of the string.
     */
    for(widx = MIN(zereply->size, 1+model->order); widx-- > 0; ) {
	symbol = find_word(model->dict, zereply->entry[ widx ].string );
	update_context(model, symbol);
    }

    /*
     *		Generate the reply in the backward direction.
     */
    sentence_reverse(zereply);
    while(1) {
	/*
	 *		Get a random symbol from the current context.
	 */
	symbol = babble(model, zereply);
	if (symbol <= WORD_FIN) break;

	add_word_to_sentence(zereply, model->dict->entry[symbol].string );

	/*
	 *		Extend the current context of the model with the current symbol.
	 */
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
STATIC double evaluate_reply(MODEL *model, struct sentence *sentence)
{
    unsigned int widx, iord, count, totcount ;
    WordNum symbol, canonsym;
    double gfrac, kfrac, weight,term,probability, entropy;
    TREE *node;
    STRING canonword;

    if (sentence->size == 0) return -100000.0;

    initialize_context(model);
    model->context[0] = model->forward;

#if WANT_PARROT_CHECK
    memset (parrot_hash, 0, sizeof parrot_hash);
    memset (parrot_hash2, 0, sizeof parrot_hash2);
#endif /* WANT_PARROT_CHECK */

    totcount = 0, entropy = 0.0;
    for (widx = 0; widx < sentence->size; widx++) {
	symbol = find_word(model->dict, sentence->entry[widx].string );

	/* Only crosstab-keywords contribute to the scoring
	*/
	canonword = word_dup_lowercase(model->dict->entry[symbol].string);
	canonsym = find_word( model->dict, canonword);
        if (canonsym >= model->dict->size) canonsym = symbol;
	kfrac = crosstab_ask(glob_crosstab, canonsym);
	if (kfrac < 1.0 / (CROSS_DICT_SIZE) ) goto update1;
	probability = 0.0;
        count = 0;
        totcount++;
        for(iord = 0; iord < model->order; iord++) {
            if ( !model->context[iord] ) continue;
            node = find_symbol(model->context[iord], symbol);
            if (!node) continue;
            count++;
		/* too unique: don't count them */
            if (node->thevalue < 2) continue; 
            probability += (0.1+node->thevalue) / (0.1 + model->context[iord]->childsum);
            }
        if (!count) goto update1;
        if (!(probability > 0.0)) goto update1;

        term = (double) probability / count;
        gfrac = symbol_weight(model->dict, symbol, 0);
        weight = kfrac * log(1.0+gfrac);
#if WANT_KEYWORD_WEIGHTS
        entropy -= weight * log(term);
#else
        entropy -= log(term);
#endif

#if (WANT_DUMP_KEYWORD_WEIGHTS & 1)
fprintf(stderr, "#### '%*.*s'\n"
"Valsum=%9lu/%9llu Nnode=%9lu/%9llu\n"
"Gfrac=%6.4e Kfrac=%6.4e W=%6.4e\n"
"Prob=%6.4e/Cnt=%u:=Term=%6.4e w*log(Term)=%6.4e Entr=%6.4e\n"
        , (int) sentence->entry[widx].string.length
        , (int) sentence->entry[widx].string.length
        , sentence->entry[widx].string.word
        , (unsigned long) model->dict->entry[symbol].stats.valuesum
        , (unsigned long long) model->dict->stats.valuesum
        , (unsigned long) model->dict->entry[symbol].stats.nnode
        , (unsigned long long) model->dict->stats.nnode
        , gfrac, kfrac, weight
        , probability , (unsigned) count
        , (double) term
        , (double) weight * log( term )
        , (double) entropy
        );
#endif
update1:
        update_context(model, symbol);
#if WANT_PARROT_CHECK
        for(iord = model->order+1; iord-- > 0; ) {
	   node = model->context[iord] ;
           if (node) break;
           }
	if (node) { PARROT_ADD(node->stamp); }
#endif /* WANT_PARROT_CHECK */
    }
#if (WANT_DUMP_KEYWORD_WEIGHTS & 1)
fprintf(stderr, "####[%u] =%6.4f\n", widx,(double) entropy
	);
#endif

    initialize_context(model);
    model->context[0] = model->backward;

    for(widx = sentence->size; widx-- > 0; ) {
	symbol = find_word(model->dict, sentence->entry[widx].string );

	canonword = word_dup_lowercase(model->dict->entry[symbol].string);
	canonsym = find_word( model->dict, canonword);
        if (canonsym >= model->dict->size) canonsym = symbol;
	kfrac = crosstab_ask(glob_crosstab, canonsym);
	if (kfrac < 1.0 / (CROSS_DICT_SIZE) ) goto update2;
        probability = 0.0;
        count = 0;
        totcount++;
        for(iord = 0; iord < model->order; iord++) {
            if ( !model->context[iord] ) continue;
            node = find_symbol(model->context[iord], symbol);
            if (!node) continue;
            count++;
            if (node->thevalue < 2) continue; /* Too unique */
            probability += (0.1+node->thevalue) / (0.1 + model->context[iord]->childsum);
        }

        if ( !count ) goto update2;
        if (!(probability > 0.0)) goto update2;

        term = (double) probability / count;
        gfrac = symbol_weight(model->dict, symbol, 0);
        weight = kfrac * log(1.0+gfrac);
#if WANT_KEYWORD_WEIGHTS
        entropy -= weight * log(term);
#else
        entropy -= log(term);
#endif

#if (WANT_DUMP_KEYWORD_WEIGHTS & 1)
fprintf(stderr, "#### Rev '%*.*s'\n"
"Valsum=%9lu/%9llu Nnode=%9lu/%9llu\n"
"Gfrac=%6.4e Kfrac=%6.4e W=%6.4e\n"
"Prob=%6.4e/Cnt=%u:=Term=%6.4e w*log(Term)=%6.4e Entr=%6.4e\n"
        , (int) sentence->entry[widx].string.length
        , (int) sentence->entry[widx].string.length
        , sentence->entry[widx].string.word
        , (unsigned long) model->dict->entry[symbol].stats.valuesum
        , (unsigned long long) model->dict->stats.valuesum
        , (unsigned long) model->dict->entry[symbol].stats.nnode
        , (unsigned long long) model->dict->stats.nnode
        , gfrac, kfrac, weight
        , probability , (unsigned) count
        , (double) term
        , (double) weight * log( term )
        , (double) entropy
        );
#endif
update2:
        update_context(model, symbol);
#if WANT_PARROT_CHECK
        for(iord = model->order+1; iord-- > 0; ) {
	    node = model->context[iord] ;
           if (node) break;
           }
	if (node) { PARROT_ADD(node->stamp); }
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
    widx = sentence->size;
    if (widx && widx != MIN_REPLY_SIZE) {
#if 1
	if (widx > MIN_REPLY_SIZE) {
		entropy /= pow((1.0* widx) / MIN_REPLY_SIZE, 1.6);
		}
	else	{
		entropy /= pow ((0.0+MIN_REPLY_SIZE) / widx , 1.4);
		}
#endif
	init_val_fwd = start_penalty(model, sentence->entry[0].string);
	init_val_rev = end_penalty(model, sentence->entry[widx-1].string );
        entropy -= sqrt(init_val_fwd);
        entropy -= sqrt(init_val_rev);
	}
#if (WANT_DUMP_KEYWORD_WEIGHTS & 1)
fprintf(stderr, "####[Corrected] =%6.4f\n", (double) entropy
	);
#endif

    return entropy;
}

/*---------------------------------------------------------------------------*/

/*
 *		Function:	Make_Output
 *
 *		Purpose:		Generate a string from the dictionary of reply words.
 */
STATIC char *make_output(struct sentence *src)
{
    static char *output = NULL;
    unsigned int widx;
    size_t length;
    char *output_none = "I am utterly speechless!";
#if WANT_SUPPRESS_WHITESPACE
    char *tags;
    unsigned int sqcnt=0, dqcnt=0, hycnt=0;
    int begin;
#endif


    if (src->size == 0) { return output_none; }
	/* calculate the space we'll need.
	** We assume one space between adjacent wordst plus a NUL at the end.
	*/
    length = 1;
#if WANT_SUPPRESS_WHITESPACE
    for(widx = 0; widx < src->size; widx++) length += 1+ src->entry[widx].string.length;
#else
    for(widx = 0; widx < src->size; widx++) length += src->entry[widx].string.length;
#endif
    output = realloc(output, length);
    if (!output) {
	error("make_output", "Unable to reallocate output.");
	return output_none;
    }

#if WANT_SUPPRESS_WHITESPACE
    tags = malloc(2+src->size);
    if (tags) memset(tags, 0, src->size);
#define NO_SPACE_L 1
#define NO_SPACE_R 2
#define IS_SINGLE 4
#define IS_DOUBLE 8
#define IS_HYPHEN 16

	/* do we want a white before or after the token at [widx] ? */
    for(widx = 0; widx < src->size; widx++) {
	if (!widx			|| dont_need_white_l(src->entry[widx].string)) tags[widx] |= NO_SPACE_L;
	if (widx == src->size-1	|| dont_need_white_r(src->entry[widx].string)) tags[widx] |= NO_SPACE_R;
	if (src->entry[widx].string.length <= 1 && src->entry[widx].string.word[0] == '\'' ) { sqcnt++; tags[widx] |= IS_SINGLE; }
	if (src->entry[widx].string.length <= 1 && src->entry[widx].string.word[0] == '"' ) { dqcnt++; tags[widx] |= IS_DOUBLE; }
	if (src->entry[widx].string.length <= 1 && src->entry[widx].string.word[0] == '-' ) { hycnt++; tags[widx] |= IS_HYPHEN; }
	}

	/* First detect o'Hara and don't */
    if (sqcnt >0) for(widx = 0; widx < src->size; widx++) {
	if ( !(tags[widx] & IS_SINGLE)) continue;
#if 0
	 fprintf(stderr, "Single:"); dump_word(stderr, src->entry[widx].string);
	if (widx) { fprintf(stderr, "left:"); dump_word(stderr, src->entry[widx-1].string); fputc('\n', stderr); }
	if (widx <src->size-1) { fprintf(stderr, "Right:"); dump_word(stderr, src->entry[widx+1].string); fputc('\n', stderr); }
#endif
	/* if the word to the left is absent or 1char we dont want a white inbetween */
	if (!widx || src->entry[widx-1].string.length <2) {
		tags[widx] |= NO_SPACE_L;
		tags[widx] |= NO_SPACE_R;
		tags[widx] &= ~IS_SINGLE;
		sqcnt--;
		}
	/* if the word to the right is absent or 1char we dont want a white inbetween */
	if (widx == src->size-1 || src->entry[widx+1].string.length <2) {
		tags[widx] |= NO_SPACE_L;
		tags[widx] |= NO_SPACE_R;
		tags[widx] &= ~IS_SINGLE;
		}
	}

	/* Try to match pairs of single quotes. This is rude: we don't care about nesting. */
    if (sqcnt >1) for(begin= -1,widx = 0; widx < src->size; widx++) {
		if (!(tags[widx] & IS_SINGLE)) continue;
		if (begin < 0) {begin = widx; continue; }
		tags[begin] |= NO_SPACE_R; tags[begin] &= ~NO_SPACE_L; if (begin) tags[begin-1] &= ~NO_SPACE_R;
		tags[widx] |= NO_SPACE_L; tags[widx] &= ~NO_SPACE_R; if (begin < src->size-1) tags[begin+1] &= ~NO_SPACE_L;
		tags[begin] &= ~IS_SINGLE;
		tags[widx] &= ~IS_SINGLE;
		begin = -1;
		sqcnt -= 2;
		}

	/* idem: double quotes */
    if (dqcnt >1) for(begin= -1,widx = 0; widx < src->size; widx++) {
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
    if (hycnt >1) for(begin= -1,widx = 0; widx < src->size; widx++) {
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
    if (sqcnt+dqcnt+hycnt) for(widx = 0; widx < src->size; widx++) {
		if (!(tags[widx] & (IS_SINGLE | IS_DOUBLE | IS_HYPHEN))) continue;
		tags[widx] |= NO_SPACE_L;
		tags[widx] |= NO_SPACE_R;
		}
#endif

    length = 0;
    for(widx = 0; widx < src->size; widx++) {
#if WANT_SUPPRESS_WHITESPACE
	if (!widx) {;}
	else if (tags[widx] & NO_SPACE_L ) {;}
	else if (tags[widx-1] & NO_SPACE_R) {;}
	else output[length++] = ' ';
#endif
	memcpy(output+length, src->entry[widx].string.word, src->entry[widx].string.length);
	length += src->entry[widx].string.length;
	}

    output[length] = '\0';

#if WANT_SUPPRESS_WHITESPACE
    free(tags);
#undef NO_SPACE_L
#undef NO_SPACE_R
#undef IS_SINGLE
#undef IS_DOUBLE
#undef IS_HYPHEN
#endif
	/* scrutinize_string may or may not reallocate the output string, but we don't care */
    output = scrutinize_string (output, SCRUTINIZE_OUTPUT);
    return output;
}

/*---------------------------------------------------------------------------*/

/*
 *		Function:	Babble
 *
 *		Purpose:		Return a random symbol from the current context, or a
 *						zero symbol identifier if we've reached either the
 *						start or end of the sentence.  Select the symbol based
 *						on probabilities, favouring keywords.  In all cases,
 *						use the longest available context to choose the symbol.
 */
STATIC WordNum babble(MODEL *model, struct sentence *src)
{
    TREE *node;
    unsigned int oidx,cidx;
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

    /*
     *		Choose a symbol at random from this context.
     *		weighted by ->thevalue
     */
    // cidx = urnd(node->branch);
    // credit = urnd( (1+node->childsum)/2);
    cidx = 0;
    credit = urnd( node->childsum );
    while(1) {
	/*
	 *		If the symbol occurs as a keyword, then use it.  Only use an
	 *		auxilliary keyword if a normal keyword has already been used.
	 */
	symbol = node->children[cidx].ptr->symbol;
	if (credit < node->children[cidx].ptr->thevalue) break;
        if (node->children[cidx].ptr->thevalue == 0) credit--;
	else credit -= node->children[cidx].ptr->thevalue;
	cidx = (cidx+1) % node->branch;
    }
done:
    // fprintf(stderr, "{+%u}", symbol );
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
	symbol = crosstab_get(glob_crosstab, urnd (CROSS_DICT_SIZE) );
	if (symbol >= model->dict->size) symbol = crosstab_get(glob_crosstab, urnd( (CROSS_DICT_SIZE/2)) );
	if (symbol >= model->dict->size) symbol = crosstab_get(glob_crosstab, urnd( (CROSS_DICT_SIZE/4)) );
	if (symbol >= model->dict->size) symbol = crosstab_get(glob_crosstab, urnd( (CROSS_DICT_SIZE/8)) );
	if (symbol >= model->dict->size) symbol = crosstab_get(glob_crosstab, urnd( (CROSS_DICT_SIZE/16)) );
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
init_typ_fwd = word.type;
if (/* symbol <= WORD_ERR || */ symbol == WORD_NIL) return penalty;
init_typ_fwd = model->dict->entry[symbol].string.type;
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
type = model->dict->entry[symbol].string.type;
node = find_symbol(model->backward, symbol);


switch (type) {
case TOKEN_INITCAPS:
case TOKEN_LOWER:
case TOKEN_UPPER:
case TOKEN_MISC:	/* Anything, including high ascii */
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
#if 0
/*
 *		Function:	New_Swap
 *
 *		Purpose:		Allocate a new swap structure.
 */
SWAP *new_swap(void)
{
    SWAP *swp;

    swp = malloc(sizeof *swp);
    if (!swp) {
	error("new_swap", "Unable to allocate swap");
	return NULL;
    }
    swp->size = 0;
    swp->pairs = NULL;

    return swp;
}

/*---------------------------------------------------------------------------*/

/*
 *		Function:	Add_Swap
 *
 *		Purpose:		Add a new entry to the swap structure.
 */
STATIC void add_swap(SWAP *list, char *from, char *to)
{
    list->size += 1;

    list->pairs = realloc(list->pairs, list->size *sizeof *list->pairs);
    if (!list->pairs) {
	error("add_swap", "Unable to reallocate pairs");
	return;
    }

    list->pairs[list->size-1].from = new_string(from, 0);
    list->pairs[list->size-1].to = new_string(to, 0);
}

/*---------------------------------------------------------------------------*/

/*
 *		Function:	Initialize_Swap
 *
 *		Purpose:		Read a swap structure from a file.
 */
STATIC SWAP *initialize_swap(char *filename)
{
    SWAP *list;
    FILE *fp = NULL;
    char buffer[1024];
    char *from;
    char *to;

    list = new_swap();

    if (!filename) return list;

    fp = fopen(filename, "r");
    if (!fp) return list;

    while (fgets(buffer, sizeof buffer, fp) ) {
	if (buffer[0] == '#') continue;
	from = strtok(buffer, "\t ");
	to = strtok(NULL, "\t \n#");

	add_swap(list, from, to);
    }

    fclose(fp);
    return list;
}

/*---------------------------------------------------------------------------*/

STATIC void free_swap(SWAP *swap)
{
    unsigned int idx;

    if (!swap) return;

    for(idx = 0; idx < swap->size; idx++) {
	free_string(swap->pairs[idx].from);
	free_string(swap->pairs[idx].to);
    }
    free(swap->pairs);
    free(swap);
}
#endif
/*---------------------------------------------------------------------------*/

/*
 *		Function:	Initialize_List
 *
 *		Purpose:		Read a dictionary from a file.
 */
STATIC DICT *read_dict(char *filename)
{
    DICT *this;
    FILE *fp = NULL;
    static char buffer[1024];
    static STRING word ={0,0,buffer};

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
 *		Function:	Delay
 *
 *		Purpose:		Display the string to stdout as if it was typed by a human.
 */
void delay(char *string)
{
    size_t idx,len;

    /*
     *		Don't simulate typing if the feature is turned off
     */
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

/*
 *		Function:	Typein
 *
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

/*---------------------------------------------------------------------------*/

/*
 *		Function:	Ignore
 *
 *		Purpose:		Log the occurrence of a signal, but ignore it.
 */
void ignore(int sig)
{
    if (sig != 0) warn("ignore", MY_NAME " received signal %d", sig);

#if !defined(DOS)
    /* signal(SIGINT, saveandexit);*/
    /* signal(SIGILL, die);*/
    /*    signal(SIGSEGV, die);*/
#endif
    /*    signal(SIGFPE, die);*/
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
    static bool flag = FALSE;

    if (flag == FALSE) {
#if defined(__mac_os) || defined(DOS)
	srand(time(NULL));
#else
	srand48(time(NULL));
#endif
    }
    flag = TRUE;
#if defined(__mac_os) || defined(DOS)
    return rand()%range;
#else
if (range <= 1) return 0;
while(1)	{
    unsigned val, box;
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
#endif
}

/*---------------------------------------------------------------------------*/
/* random number generator uses 'entropy' from CPU-ticker */
#define rdtscll(name) \
          __asm__ __volatile__("rdtsc" : "=A" (name))

BigThing rdtsc_rand(void)
{
static BigThing val=0x0000111100001111ULL;

#if WANT_RDTSC_RANDOM
static BigThing old;
BigThing new;

rdtscll(new);
val ^= (val >> 15) ^ (val << 14) ^ (new << 13); /* PT approved */
old = new;
#else
val ^= (val >> 15) ^ (val << 14) ^ 9 ;
#endif

return val;
}

/*---------------------------------------------------------------------------*/

/*
 *		Function:	Usleep
 *
 *		Purpose:		Simulate the Un*x function usleep.  Necessary because
 *						Microsoft provide no similar function.  Performed via
 *						a busy loop, which unnecessarily chews up the CPU.
 *						But Windows '95 isn't properly multitasking anyway, so
 *						no-one will notice.  Modified from a real Microsoft
 *						example, believe it or not!
 */
#if defined(DOS) || defined(__mac_os)
void usleep(int period)
{
    clock_t goal;

    goal =(clock_t)(period*CLOCKS_PER_SEC)/(clock_t)1000000+clock();
    while(goal > clock());
}
#endif

/*---------------------------------------------------------------------------*/

/*
 *		Function:	Strdup
 *
 *		Purpose:		Provide the strdup() function for Macintosh.
 */
#ifdef __mac_os
char *strdup(const char *str)
{
    char *rval = malloc(strlen(str)+1);

    if (rval != NULL) strcpy(rval, str);

    return rval;
}
#endif

/*---------------------------------------------------------------------------*/

/*
 *		Function:	Initialize_Speech
 *
 *		Purpose:		Initialize speech output.
 */
#ifdef __mac_os
bool initialize_speech(void)
{
    bool speechExists = false;
    long response;
    OSErr err;

    err = Gestalt(gestaltSpeechAttr, &response);

    if (!err) {
	if (response & (1L << gestaltSpeechMgrPresent)) {
	    speechExists = true;
	}
    }
    return speechExists;
}
#endif

/*---------------------------------------------------------------------------*/

/*
 *		Function:	changevoice
 *
 *		Purpose:		change voice of speech output.
 */
void changevoice(struct sentence* src, unsigned int position)
{
#ifdef __mac_os
    int i, index;
    STRING word ={ 1,0, "#" };
    char buffer[80];
    VoiceSpec voiceSpec;
    VoiceDescription info;
    short count, voiceCount;
    unsigned char* temp;
    OSErr err;
    /*
     *		If there is less than 4 words, no voice specified.
     */
    if (src->size <= 4) return;

    for(i = 0; i < src->size-4; i++)
	if (!wordcmp(word, src->entry[i].string ) ) {

	    err = CountVoices(&voiceCount);
	    if (!err && voiceCount) {
		for (count = 1; count <= voiceCount; count++) {
		    err = GetIndVoice(count, &voiceSpec);
		    if (err) continue;
		    err = GetVoiceDescription(&voiceSpec, &info,
					      sizeof(VoiceDescription));
		    if (err) continue;


		    for (temp =  info.name; *temp; temp++) {
			if (*temp == ' ')
			    *temp = '_';
		    }

		    /*
		     *		skip command and get voice name
		     */
		    index = i + 3;
		    memcpy(buffer, src->entry[index].string.word, sizeof buffer);
		    buffer[(sizeof buffer) -1] = 0;
		    c2pstr(buffer);
		    /* compare ignoring case*/
		    if (EqualString((StringPtr)buffer, info.name, false, false)) {
			if (gSpeechChannel) {
			    StopSpeech(gSpeechChannel);
			    DisposeSpeechChannel(gSpeechChannel);
			    gSpeechChannel = nil;
			}
			err = NewSpeechChannel(&voiceSpec, &gSpeechChannel);
			if (!err) {
			    p2cstr((StringPtr)buffer);
			    printf("Now using %s voice\n", buffer);
			    c2pstr(buffer);
			    err = SpeakText(gSpeechChannel, &buffer[1], buffer[0]);
			}
		    }
		}
	    }
	}
#endif
}

/*---------------------------------------------------------------------------*/

/*
 *		Function:	listvoices
 *
 *		Purpose:		Display the names of voices for speech output.
 */
void listvoices(void)
{
#ifdef __mac_os
    VoiceSpec voiceSpec;
    VoiceDescription info;
    short count, voiceCount;
    unsigned char* temp;
    OSErr err;

    if (gSpeechExists) {
	err = CountVoices(&voiceCount);
	if (!err && voiceCount) {
	    for (count = 1; count <= voiceCount; count++) {
		err = GetIndVoice(count, &voiceSpec);
		if (err) continue;

		err = GetVoiceDescription(&voiceSpec, &info,
					  sizeof(VoiceDescription));
		if (err) continue;

		p2cstr(info.name);
		for (temp =  info.name; *temp; temp++)
		    if (*temp == ' ')
			*temp = '_';
		printf("%s\n",info.name);
	    }
	}
    }
#endif
}

/*---------------------------------------------------------------------------*/

/*
 *		Function:	Speak
 */
void speak(char *output)
{
    if (speech == FALSE) return;
#ifdef __mac_os
    if (gSpeechExists) {
	OSErr err;

	if (gSpeechChannel)
	    err = SpeakText(gSpeechChannel, output, strlen(output));
	else {
	    c2pstr(output);
	    SpeakString((StringPtr)output);
	    p2cstr((StringPtr)output);
	}
    }
#endif
}

/*---------------------------------------------------------------------------*/

/*
 *		Function:	Progress
 *
 *		Purpose:		Display a progress indicator as a percentage.
 */
bool progress(char *message, unsigned long done, unsigned long todo)
{
    static int last = 0;
    static bool first = FALSE;

    if (noprogres) return FALSE;
    /*
     *    We have already hit 100%, and a newline has been printed, so nothing
     *    needs to be done.
     *    WP: avoid div/zero.
     */
    if (!todo) todo = done?done:1;
    if (done*100/todo == 100 && first == FALSE) return TRUE;

    /*
     *    Nothing has changed since the last time this function was called,
     *    so do nothing, unless it's the first time!
     */
    if (done*100/todo == last) {
	if (done == 0 &&first == FALSE) {
	    fprintf(stderr, "%s: %3lu%%", message, done*100/todo);
	    first = TRUE;
	}
	return TRUE;
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
	first = FALSE;
	last = 0;
	fprintf(stderr, "\n");
    }

    return TRUE;
}

/*---------------------------------------------------------------------------*/

void help(void)
{
    unsigned int j;

    for(j = 0; j <COUNTOF(commands); j++) {
	printf("#%-7s: %s\n", commands[j].word.word, commands[j].helpstring);
    }
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
    free_words(glob_ban);
    empty_dict(glob_ban);
    free_words(glob_aux);
    empty_dict(glob_aux);
    free_words(glob_grt);
    empty_dict(glob_grt);
    /* free_swap(glob_swp); */

    /*
     *		Create a language model.
     */
    *model = new_model(glob_order);

    /*
     *		Train the model on a text if one exists
     */

    close( glob_fd  ); glob_fd = -1;
    sprintf(filename, "%s%smegahal.brn", glob_directory, SEP);
    if (load_model(filename, *model) == FALSE) {
	sprintf(filename, "%s%smegahal.trn", glob_directory, SEP);
	train(*model, filename);
    }

    /*
     *		Read a dictionary containing banned keywords, auxiliary keywords,
     *		greeting keywords and swap keywords
     */
    sprintf(filename, "%s%smegahal.ban", glob_directory, SEP);
    glob_ban = read_dict(filename);
    sprintf(filename, "%s%smegahal.aux", glob_directory, SEP);
    glob_aux = read_dict(filename);
    sprintf(filename, "%s%smegahal.grt", glob_directory, SEP);
    glob_grt = read_dict(filename);
    /* sprintf(filename, "%s%smegahal.swp", glob_directory, SEP);
    glob_swp = initialize_swap(filename);
	*/
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

    if ( !command || position+2 >= command->size ) {
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

STATIC void free_words(DICT *words)
{
    unsigned int iwrd;

    if ( !words ) return;

    if (words->entry != NULL)
	for(iwrd = 0; iwrd < words->size; iwrd++) free_string(words->entry[iwrd].string);
}

/*---------------------------------------------------------------------------*/

STATIC void free_string(STRING word)
{
    free(word.word);
    word.word = NULL;
    word.length = 0;
}



STATIC HashVal hash_word(STRING string)
{
return hash_mem(string.word, (size_t) string.length);
}

STATIC HashVal hash_mem(void *dat, size_t len)
{
unsigned char *str = (unsigned char*) dat;
unsigned val=0;
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
	if ( dict->entry[*np].hash != hash) continue;
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

    for (item =0 ; item < dict->size; item++) {
		WordNum *np;
		slot = old[item].hash % dict->msize;
		for( np = &dict->entry[slot].tabl; np; np = &dict->entry[*np].link ) {
			if (*np == WORD_NIL) break;
			}
		*np = item;
		dict->entry[item].hash = old[item].hash;
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
new->size = new->msize = 0;
new->entry= NULL;
return new;
}
STATIC int sentence_grow(struct sentence *ptr)
{
    unsigned newsize;

    newsize = ptr->size ? ptr->size + (1+ptr->size)/2 : 64;
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
    for (bot = 0, top = ptr->size? ptr->size-1: 0; bot < top; bot++, top--) {
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
unsigned count, totcount;
static double density = 0.0;
static unsigned direction = 0;
int rc;

if (!model || ! maxnodecount) return 0;
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
** main and max may have been wrapped around zero (--> min > max)
** return
**	0 := this inside interval
**	1 := this below interval
**	-1 := this above interval (but wrapped)
** The two impossible cases return -2.
*/
static int check_interval(Stamp min, Stamp max, Stamp this)
{
switch (4 *(max >= min)
	+2 *(this >= min)
	+1 *(this > max)
	) {
	case 0: return 0;
	case 1: return 1;
	case 2: return -2;
	case 3: return 0;
	case 4: return 1;
	case 5: return -2;
	case 6: return 0;
	case 7: return -1;
	}
return 0;
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

STATIC size_t symbol_format(char *buff, WordNum sym)
{
if (! (glob_dict = glob_model->dict)) return sprintf(buff, "<NoDict>" );
else if (sym >= glob_dict->size) return sprintf(buff, "<%u>", sym );
else return word_format(buff, glob_dict->entry[sym].string );
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
unsigned val;

if (!len) len = strlen (str);

	/* the string can only shrink, so we can perform this in place */
for (idx=pos=0; idx < len ; idx += ret) {
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
unsigned val;

if (!len) len = strlen (src);

for (idx=pos=0; idx < len ; idx += ret) {
	ret = eat_utf8 ((unsigned char*) src+idx, len-pos, &val);
	if (ret == 0) break;
	else if (ret < 0) { ret=1; dst[pos++] = src[idx]; } /* does not fit, this should never happen */
	/* else if (ret==1)  { dst[pos++] = val; } normal character */
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
	unsigned val, cha;
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
/* Eof */
