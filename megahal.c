
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
#include <signal.h>
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

#define STATIC static
#define STATIC /* EMPTY:: For profiling, to avoid inlining of STATIC functions. */
#define COUNTOF(a) (sizeof(a) / sizeof(a)[0])
	/* this is an ugly hack to cast a string str to an unsigned char
	** This is absolutely necessary for the isXXXX() functions which
	** expect an int in the range 0...255 OR -a (for EOF)
	** Using a signed char would sign-extend the argument to -128...127,
	** which causes the ctype[] array to be indexed out of bounds
	*/
#define UCP ((unsigned char *)str)

	/* some develop/debug switches. 0 to disable */
#define WANT_DUMP_REHASH_TREE 0
#define WANT_DUMP_DELETE_DICT 1

	/* bitmask (0-31)
	** 1:= summary
	** 2:= full table after make_keywords()
	** 4:= weight details in evaluate_reply()
	** 8:= prim/alt details 
	** */
#define WANT_DUMP_KEYWORD_WEIGHTS 0 

#define WANT_DUMP_ALZHEIMER_PROGRESS 1 /* 0...4 */
#define WANT_DUMP_ALL_REPLIES 1
	/* dump tree as ascii (This will cost a LOT of disk space)
	** 1 := only dump forward tree
	** 2 := only dump backward tree
	** 3 := dump both.
	 */
#define WANT_DUMP_MODEL 0

/*
** Real SWITCHES. Note: these are not independent. Some combinations might be impossible
** (cleanup needed)
*/
	/* The crossdict is a cross-table containing a keyword-keyword adjacency matrix.
	** this matrix is evaluated by a power-iteration algoritm, which basically
	** yields the first eigenvector and -value.
	** the matrix is fed with pairs of words. 
	** Only words with "less than average" frequency of occurence are considered.
	** Only pairs of words with a (distance < CROSS_DICT_WORD_DISTANCE) are entered.
	** To avoid unbounded growth, random rows of the matrix have their values decremented
	** randomly, on a periodic basis.
	*/
#define CROSS_DICT_SIZE 31
#define CROSS_DICT_WORD_DISTANCE 10

	/* Maintain and use weights on the keywords */
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
	*/
#define WANT_SUPPRESS_WHITESPACE 1

	/* Keep a timestamp in the nodes, to facilitate Alzheimer */
#define WANT_TIMESTAMPED_NODES 1

	/* The number of keywords that will be kept between replies.  Zero to disable.
	** This is a very hard parameter to tune.
	** Setting it too low (10) will force 'good' keywords out.
	** Setting it too high (100) will cause a lot of stale words to be kept.
	** The 'selection-pressure' depends on the number of (new) keywords that want
	** to enter the keyword-dict per input-text.
	** KEYWORD_DICT_SIZE should be approximately equal to the number of (unique) symbols in the input text.
	** If the size of the input texts varies, the larger inputs will effectively flush the keyword-dict.
	** for me, 20...30 is the best setting
	** YMMV
	*/
#define KEYWORD_DICT_SIZE 23

	/* Alternative tokeniser. Attempts to keep dotted acronyms and (floating point) numbers intact. */
#define WANT_NEW_TOKENIZER 1

	/*
	** ALZHEIMER_NODE_COUNT is the number of nodes we intend to maintain.
	** if the actual number of nodes exceeds this limit, Alzheimer might be triggered,
	** and the oldest nodes will be pruned. The timestamp is used as a poor man's LRU.
	** NOTE: this is the *intended* number. The actual number will fluctuate, and will
	** sometimes exceed this limit.
	**
	** (1/ALZHEIMER_FACTOR) is the chance of Alzheimer hitting the tree, once per reply.
	** Zero to disable.
	** Alzheimer periodically does a complete treewalk (twice) to find and eliminate nodes
	** it considers too old.  This is expensive.
	** ALZHEIMER_FACTOR should be chosen such that Alzheimer hits us once every few minutes.
	** 100 could be a start. 
	** (with a glob_timeout=DEFAULT_TIMEOUT=10 this would result in avg (1000s/2) between sweeps)
	** YMMV
	*/
#define ALZHEIMER_NODE_COUNT ( 1600 * 1000 )
#define ALZHEIMER_NODE_COUNT ( 35 * 1000 * 1000)
#define ALZHEIMER_FACTOR 50
#define ALZHEIMER_FACTOR 300

	/* improved random generator, using noise from the CPU clock (only works on intel/gcc) */
#define WANT_RDTSC_RANDOM 1

	/* Resizing the tree is a space/time tradeoff:
	** resizing it on every insert/delete results in O(N*N) behavior.
	** Doing it less often will cost less CPU, but will consume more memory.
	** (formally, it still is O(N*N), but with a smaller O ;-)
	** setting NODE_SIZE_SHRINK to zero will only shrink by halving.
	** NOTE dicts will hardly ever be shrunk; only emptied.
	*/
#define DICT_SIZE_INITIAL 4
#define DICT_SIZE_SHRINK 16
#define NODE_SIZE_INITIAL 2
#define NODE_SIZE_SHRINK 16

	/* we don't want results smaller than this amount of tokens.
	** Note: words and puntuation count as tokens. whitespace does not
	** (if WANT_SUPPRESS_WHITESPACE is enabled)
 	*/
#define MIN_REPLY_SIZE 14

	/* Dont maintain a hashtable for the lineair dict used to store the reply */
#define WANT_FLAT_NOFUSS 0

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

#define WORD_NIL ((WordNum)-1)
#define WORD_ERR ((WordNum)0)
#define WORD_FIN ((WordNum)1)
#define CHILD_NIL ((ChildIndex)-1)

typedef struct {
    StrLen length;
    char *word;
} STRING;

struct	dictslot {
	WordNum tabl;
	WordNum link;
	HashVal hash;
	struct wordstat {
		UsageCnt nhits;
		UsageCnt whits;
		} stats;
	STRING string;
	};

typedef struct {
    DictSize size;
    DictSize msize;
    struct dictstat	{
		UsageSum nhits;
		UsageSum whits;
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
    UsageCnt usage; /* sum of children's count */
    UsageCnt count; /* my count */
    WordNum symbol;
#if WANT_TIMESTAMPED_NODES 
    Stamp stamp; 
#endif
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
static int glob_width = 75;
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

static bool used_key;
static DICT *glob_keys = NULL;
static DICT *glob_input = NULL;
static DICT *glob_greets = NULL;
static MODEL *glob_model = NULL;
#if 1||CROSS_DICT_SIZE
#include "crosstab.h"
struct crosstab *glob_crosstab = NULL;
static DICT *glob_dict = NULL;
#endif

static DICT *glob_ban = NULL;
static DICT *glob_aux = NULL;
static DICT *glob_grt = NULL;
static SWAP *glob_swp = NULL;

static char *glob_directory = NULL;
static char *last_directory = NULL;

#if WANT_TIMESTAMPED_NODES 
static Stamp stamp_min = 0xffffffff, stamp_max=0;
#endif

static COMMAND commands[] = {
    { { 4, "QUIT" }, "quits the program and saves MegaHAL's brain", QUIT },
    { { 4, "EXIT" }, "exits the program *without* saving MegaHAL's brain", EXIT },
    { { 4, "SAVE" }, "saves the current MegaHAL brain", SAVE },
    { { 5, "DELAY" }, "toggles MegaHAL's typing delay (off by default)", DELAY },
    { { 6, "SPEECH" }, "toggles MegaHAL's speech (off by default)", SPEECH },
    { { 6, "VOICES" }, "list available voices for speech", VOICELIST },
    { { 5, "VOICE" }, "switches to voice specified", VOICE },
    { { 5, "BRAIN" }, "change to another MegaHAL personality", BRAIN },
    { { 4, "HELP" }, "displays this message", HELP },
    { { 5, "QUIET" }, "toggles MegaHAL's responses (on by default)",QUIET},
    /*
      { { 5, "STATS" }, "Display stats", STATS},
      { { 5, "STATS-SESSION" }, "Display stats for this session only",STATS_SESSION},
      { { 5, "STATS-ALL" },"Display stats for the whole lifetime",STATS-ALL},
	*/
};

#ifdef AMIGA
struct Locale *_AmigaLocale;
#endif

#ifdef __mac_os
Boolean gSpeechExists = false;
SpeechChannel gSpeechChannel = nil;
#endif

STATIC void add_aux(MODEL *model, DICT *keywords, STRING word);
STATIC void add_key(MODEL *model, DICT *keywords, STRING word);
STATIC int resize_tree(TREE *tree, unsigned newsize);

STATIC void add_swap(SWAP *list, char *from, char *to);
STATIC TREE *add_symbol(TREE *, WordNum);
STATIC WordNum add_word_dodup(DICT *dict, STRING word);
STATIC WordNum add_word_nofuss(DICT *dict, STRING word);
STATIC WordNum babble(MODEL *model, DICT *keywords, DICT *words);
STATIC size_t word_format(char *buff, STRING string);
STATIC size_t symbol_format(char *buff, WordNum sym);

#if WANT_NEW_TOKENIZER
STATIC void make_words(char *, DICT *);
STATIC size_t tokenize(char *string, int *sp);
#else /* WANT_NEW_TOKENIZER */
STATIC void make_words(char *, DICT *);
STATIC size_t boundary(char *string, int *state);
#endif

STATIC void capitalize(char *);
STATIC void changevoice(DICT *, unsigned int);
STATIC void change_personality(DICT *, unsigned int, MODEL **);
STATIC void delay(char *);
STATIC void die(int);
STATIC bool dissimilar(DICT *, DICT *);
STATIC void error(char *, char *, ...);
STATIC double evaluate_reply(MODEL *model, DICT *keywords, DICT *sentence);
STATIC COMMAND_WORDS execute_command(DICT *, unsigned int *position);
STATIC void exithal(void);
STATIC TREE *find_symbol(TREE *node, WordNum symbol);
STATIC TREE *find_symbol_add(TREE *, WordNum);

STATIC WordNum find_word(DICT *, STRING);
STATIC char *generate_reply(MODEL *, DICT *);
STATIC void help(void);
STATIC void ignore(int);
STATIC bool initialize_error(char *);
#ifdef __mac_os
STATIC bool initialize_speech(void);
#endif
STATIC bool initialize_status(char *);
STATIC void learn_from_input(MODEL *, DICT *);
STATIC void listvoices(void);
STATIC void make_greeting(DICT *);
STATIC DICT *new_dict(void);

STATIC char *read_input(char * prompt);
STATIC void save_model(char *, MODEL *);
#ifdef __mac_os
STATIC char *strdup(const char *);
#endif
STATIC void upper(char *);
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
STATIC void load_tree(FILE *, TREE *);
STATIC void load_word(FILE *, DICT *);
STATIC DICT *make_keywords(MODEL *, DICT *);
STATIC char *make_output(DICT *);
STATIC MODEL *new_model(int);
STATIC TREE *new_node(void);
STATIC SWAP *new_swap(void);
STATIC STRING new_string(char *str, size_t len);
STATIC bool print_header(FILE *);
bool progress(char *message, unsigned long done, unsigned long todo);
STATIC DICT *one_reply(MODEL *, DICT *);
STATIC void save_dict(FILE *, DICT *);
STATIC void save_tree(FILE *, TREE *);
STATIC void save_word(FILE *, STRING);
STATIC WordNum seed(MODEL *, DICT *);

STATIC void show_dict(DICT *);
STATIC void speak(char *);
STATIC bool status(char *, ...);
STATIC void train(MODEL *, char *);
STATIC void typein(char);
STATIC void update_context(MODEL *, WordNum symbol);
STATIC void update_model(MODEL *model, WordNum symbol);
STATIC bool warn(char *, char *, ...);
STATIC int wordcmp(STRING one, STRING two);
STATIC bool word_exists(DICT *, STRING);
STATIC unsigned int urnd(unsigned int range);

STATIC HashVal hash_mem(void *dat, size_t len);
STATIC WordNum * dict_hnd(DICT *dict, STRING word);
STATIC WordNum * dict_hnd_tail (DICT *dict, STRING word);
STATIC HashVal hash_word(STRING word);
STATIC int grow_dict(DICT *dict);
STATIC int resize_dict(DICT *dict, unsigned newsize);
STATIC void format_dictslots(struct dictslot * slots, unsigned size);
STATIC unsigned long set_dict_count(MODEL *model);
STATIC unsigned long dict_inc_refa_node(DICT *dict, TREE *node, WordNum symbol);
STATIC unsigned long dict_inc_ref_recurse(DICT *dict, TREE *node);
STATIC unsigned long dict_inc_ref(DICT *dict, WordNum symbol, unsigned nhits, unsigned whits);
STATIC unsigned long dict_dec_ref(DICT *dict, WordNum symbol, unsigned nhits, unsigned whits);

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
size_t hexdump_string(char *buff, STRING string);

STATIC void del_symbol_do_free(TREE *tree, WordNum symbol);
STATIC void del_word_dofree(DICT *dict, STRING word);
void free_tree_recursively(TREE *tree);
STATIC unsigned model_alzheimer(MODEL * model, unsigned maxnodecount);
STATIC unsigned symbol_alzheimer_recurse(TREE *tree, unsigned lev, unsigned lim);
static int check_interval(unsigned min, unsigned max, unsigned this);
void read_dict_from_ascii(DICT *dict, char *name);
static DICT *alz_dict = NULL;

STATIC void dump_model(MODEL *model);
STATIC void dump_model_recursive(FILE *fp, TREE *tree, DICT *dict, int indent);

STATIC ChildIndex *node_hnd(TREE *node, WordNum symbol);
STATIC void format_treeslots(struct treeslot *slots , unsigned size);
STATIC void show_memstat(char *msg);

STATIC STRING word_dup_othercase(STRING org);
double word_weight(DICT *dict, STRING word);
double symbol_weight(DICT *dict, WordNum symbol);
STATIC void dump_word(FILE *fp, STRING word);
STATIC void schrink_keywords(DICT *words, unsigned newsize);
/* Function: setnoprompt

   Purpose: Set noprompt variable.

 */
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

    glob_input = new_dict();
    glob_greets = new_dict();
    change_personality(NULL, 0, &glob_model);
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

    /* upper(input);*/

    make_words(input, glob_input);

    learn_from_input(glob_model, glob_input);
    output = generate_reply(glob_model, glob_input);
    /* capitalize(output);*/
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

    /* upper(input);*/

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
STATIC COMMAND_WORDS execute_command(DICT *words, unsigned int *position)
{
    unsigned int iwrd;
    unsigned int j;

    /*
     *		If there is only one word, then it can't be a command.
     */
    *position = words->size+1;
    if (words->size <= 1) return UNKNOWN;

    /*
     *		Search through the word array.  If a command prefix is found,
     *		then try to match the following word with a command word.  If
     *		a match is found, then return a command identifier.  If the
     *		Following word is a number, then change the judge.  Otherwise,
     *		continue the search.
     */
    for(iwrd = 0; iwrd < words->size-1; iwrd++) {
	/*
	 *		The command prefix was found.
	 */
	if (words->entry[iwrd].string.word[words->entry[iwrd].string.length - 1] != '#') continue;
	    /*
	     *		Look for a command word.
	     */
	for(j = 0; j < COUNTOF(commands); j++)
	if (!strncasecmp(commands[j].word.word, words->entry[iwrd + 1].string.word, words->entry[iwrd + 1].string.length) ) {
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
    dump_model(glob_model);
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
    static size_t size=0;
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
	if (length +2 >= size) {
		input = realloc(input, size? 2*size: 16);
		if (input) size = size ? 2 * size : 16;
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
    fprintf(fp, "Copyright (C) 1998 Jason Hutchens\n%s", timestamp);
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

    /* capitalize(output);*/
    speak(output);

    glob_width = 75;
    formatted = format_output(output);
    delay(formatted);
    glob_width = 64;
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
 *		Function:	Capitalize
 *
 *		Purpose:		Convert a string to look nice.
 */
STATIC void capitalize(char *str)
{
    size_t len, idx;
    /* unsigned char *ucp = (unsigned char *) str;*/
    bool start = TRUE;

    len = strlen(str);
    for(idx = 0; idx < len; idx++) {
	if (myisalpha(UCP[idx])) {
	    if (start == TRUE) UCP[idx] = toupper(UCP[idx]);
	    else UCP[idx] = tolower(UCP[idx]);
	    start = FALSE;
	}
	if (idx > 2 && strchr("!.?", UCP[idx-1]) != NULL && isspace(UCP[idx]))
	    start = TRUE;
    }
}

/*---------------------------------------------------------------------------*/

/*
 *		Function:	Upper
 *
 *		Purpose:		Convert a string to its uppercase representation.
 */
STATIC void upper(char *str)
{
    size_t len, idx;
    /* unsigned char *ucp = (unsigned char *) str;*/

    len = strlen(str);
    for(idx = 0; idx < len; idx++) UCP[idx] = toupper(UCP[idx]);
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
#if WANT_FLAT_NOFUSS
STATIC WordNum add_word_nofuss(DICT *dict, STRING word)
{
WordNum *np;

if (!dict) return 0; /* WP: should be WORD_NIL */
/* WP20101022: allow empty token at the end of a sentence*/
/* if (!word.length) return 0; // sentinel should be WORD_NIL */

if (dict->size >= dict->msize && grow_dict(dict)) return WORD_NIL;
np = &dict->entry[ dict->size].tabl ;

*np = dict->size++;
dict->entry[*np].link = WORD_NIL;
dict->entry[*np].string = word;
/* fake the hash value.
 * setting it to the identity transform will cause X to be put into slot X.
 * Degenerate chains, but consistent, even on doubling.
 */
dict->entry[*np].hash = *np;

return *np;

}
#else
STATIC WordNum add_word_nofuss(DICT *dict, STRING word)
{
WordNum symbol,*np;

if (!dict) return WORD_NIL;

np = dict_hnd_tail(dict, word);
symbol = dict->size++;
*np = symbol;

dict->entry[symbol].link = WORD_NIL;
dict->entry[symbol].hash = hash_word(word);
dict->entry[symbol].string = word;

return *np;

}
#endif /* WANT_FLAT_NOFUSS */
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
** if we shift down the words, their symbols
** will be altered (decremented) as well.
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

if ( dict->entry[this].stats.nhits ) dict->stats.nonzero -= 1;
dict->stats.nhits -= dict->entry[this].stats.nhits;
dict->stats.whits -= dict->entry[this].stats.whits;
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
dict->entry[top].stats.nhits = 0;
dict->entry[top].stats.whits = 0;
dict->entry[top].string.word = NULL;
dict->entry[top].string.length = 0;
dict->entry[top].hash = 0;

if (!dict->size || dict->size <= dict->msize - DICT_SIZE_SHRINK) {

#if (WANT_DUMP_DELETE_DICT >= 2)
    status("dict(%llu:%llu/%llu) will be shrunk: %u/%u\n"
 	, dict->stats.whits, dict->stats.nhits, dict->stats.nonzero, dict->branch, dict->msize);
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
     }
else	{
     this.word = NULL;
     this.length = 0;
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
    dict->stats.whits = 0;
    dict->stats.nhits = 0;
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
    static STRING word = {7, "<ERROR>" };
    static STRING end = {5, "<FIN>" };

    dict->stats.whits = 0;
    dict->stats.nhits = 0;
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

ret = dict_inc_ref(dict, symbol, 1, node->count);
for (uu=0; uu < node->branch; uu++) {
	ret += dict_inc_ref_recurse(dict, node->children[uu].ptr);
	}
return ret;
}

STATIC unsigned long dict_inc_ref_node(DICT *dict, TREE *node, WordNum symbol)
{

if (!dict || !node || symbol >= dict->size ) return 0;

if (node->count <= 1) return dict_inc_ref(dict, symbol, 1, 1);
else return dict_inc_ref(dict, symbol, 0, node->count);

}

STATIC unsigned long dict_inc_ref(DICT *dict, WordNum symbol, unsigned nhits, unsigned whits)
{

if (!dict || symbol >= dict->size ) return 0;

if (dict->entry[ symbol ].stats.nhits == 0 ) dict->stats.nonzero += 1;
dict->entry[ symbol ].stats.nhits += nhits;
dict->stats.nhits += nhits;
dict->entry[ symbol ].stats.whits += whits;
dict->stats.whits += whits;

return dict->entry[ symbol ].stats.whits;
}

STATIC unsigned long dict_dec_ref(DICT *dict, WordNum symbol, unsigned nhits, unsigned whits)
{

if (!dict || symbol >= dict->size ) return 0;

dict->entry[ symbol ].stats.nhits -= nhits;
if (dict->entry[ symbol ].stats.nhits == 0 ) dict->stats.nonzero -= 1;
dict->stats.nhits -= nhits;
dict->entry[ symbol ].stats.whits -= whits;
dict->stats.whits -= whits;

return dict->entry[ symbol ].stats.whits;
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
    dict->stats.nhits = 0;
    dict->stats.whits = 0;

    return dict;
}

STATIC void format_dictslots(struct dictslot * slots, unsigned size)
{
    unsigned idx;

    for (idx = 0; idx < size; idx++) {
	slots[idx].tabl = WORD_NIL;
	slots[idx].link = WORD_NIL;
	slots[idx].hash = 0xe;
	slots[idx].stats.nhits = 0;
	slots[idx].stats.whits = 0;
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

    kuttje = fread(&size, sizeof size, 1, fp);
    status("Load_dictSize=%d\n", size);
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
    static char zzz[256];
    static STRING word = {0,zzz};
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
STATIC TREE *new_node(void)
{
    TREE *node = NULL;

    /*
     *		Allocate memory for the new node
     */
    node = malloc(sizeof *node);
    if (!node) {
	error("new_node", "Unable to allocate the node.");
	return NULL;
    }

    /*
     *		Initialise the contents of the node
     */
    node->symbol = 0;
    node->usage = 0;
    node->count = 0;
#if WANT_TIMESTAMPED_NODES 
    node->stamp = stamp_max;
#endif
    node->msize = 0;
    node->branch = 0;
    node->children = NULL;
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
    model->forward = new_node();
    model->backward = new_node();
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
    node->count += 1; tree->usage += 1;
#if WANT_TIMESTAMPED_NODES
    node->stamp = stamp_max; tree->stamp = stamp_max;
#endif
    if (!node->count) {
	warn("add_symbol", "Count wants to wrap");
	node->count -= 1;
    }
    if (!tree->usage) {
	warn("add_symbol", "Usage wants to wrap");
	tree->usage -= 1;
    }

    return node;
}

STATIC void dump_model(MODEL * model)
{
FILE *fp;

fp = fopen ("tree.dmp", "w" );
if (!fp) return;

#if WANT_TIMESTAMPED_NODES
fprintf(fp, "[ stamp Min=%u Max=%u ]\n", (unsigned)stamp_min, (unsigned)stamp_max);
#endif

#if (WANT_DUMP_MODEL & 1)
fprintf(fp, "->forward order=%u\n", (unsigned) model->order);
dump_model_recursive(fp, model->forward, model->dict, 0);
#endif

#if (WANT_DUMP_MODEL & 2)
fprintf(fp, "->backward order=%u\n", (unsigned) model->order);
dump_model_recursive(fp, model->backward, model->dict, 0);
#endif
fprintf(fp, "->Eof\n" );
fclose (fp);
}

STATIC void dump_model_recursive(FILE *fp, TREE *tree, DICT *dict, int indent)
{
unsigned slot;
WordNum sym;
static STRING null = {0,""};
unsigned nhits=0,whits=0;
STRING str;
if (!tree) return;

sym = tree->symbol;
if (sym < dict->size){
	str = dict->entry[sym].string ;
	nhits = dict->entry[sym].stats.nhits;
	whits = dict->entry[sym].stats.whits;
	}
else	{
	str = null;
	}

for (slot = 0; slot < indent; slot++) {
	fputc(' ', fp);
	}

fprintf(fp, "Us=%u Cnt=%u Stmp=%u Br=%u/%u Sym=%u [%u,%u] '%*.*s'\n"
	, tree->usage, tree->count
#if WANT_TIMESTAMPED_NODES 
	, tree->stamp
#else
	, (unsigned) 0
#endif
	, tree->branch, tree->msize , tree->symbol
	, whits, nhits
	, (int) str.length , (int) str.length , str.word
	);

if (! tree->branch) return;
for (slot = 0; slot < tree->branch; slot++) {
	dump_model_recursive(fp, tree->children[slot].ptr , dict, indent+1);
	}

return;
}

/* Delete a symbol from a node.
** The node's statistics are updated (but NOT it's parent's statistics!!)
** The node's is compacted by shifting the highest element into the vacated slot.
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
    if (!tree->usage) {
	warn("del_symbol_do_free", "Usage already zero\n");
    }
    if (tree->usage < child->count) {
	warn("del_symbol_do_free", "Usage (%u -= %u) would drop below zero\n", tree->usage, child->count );
	child->count = tree->usage;
    }
    tree->usage -= child->count;

    /* FIXME: we should decrement the refcounts for the corresponding dict-entry.
    ** (but that would require acces to the model->dict, and we should avoid the risk
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
    /* if (!tree->branch || tree->branch <= tree->msize - NODE_SIZE_SHRINK) {*/
    if (!tree->branch || tree->branch <= tree->msize / 2 
	|| (NODE_SIZE_SHRINK && tree->branch <= tree->msize - NODE_SIZE_SHRINK) ) {
#if (WANT_DUMP_ALZHEIMER_PROGRESS >= 2)
	status("Tree(%u/%u) will be shrunk: %u/%u\n"
		, tree->count, tree->usage, tree->branch, tree->msize);
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
    (void) dict_dec_ref(alz_dict, tree->symbol, 1, tree->count);
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

if (!ip || *ip == CHILD_NIL) { /* not found: create one */
    if (node->branch >= node->msize) {
        if (resize_tree(node, node->branch+2 )) return NULL;
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
    node->children[ *ip ].ptr = new_node();
    node->children[ *ip ].ptr->symbol = symbol;
    }

     return node->children[ *ip ].ptr ;
}

STATIC int resize_tree(TREE *tree, unsigned newsize)
{
    ChildIndex item,slot;
    struct treeslot *old;

    if (!tree) return -1;
/* fprintf(stderr, "resize_tree(%u/%u) %u\n", tree->branch,  tree->msize, newsize);*/
    old = tree->children;
    /* if (!newsize) newsize = NODE_SIZE_INITIAL;*/
    /* while (newsize < tree->branch) newsize += 2; */

    if (newsize) {
        tree->children = malloc(newsize * sizeof *tree->children );
        if (!tree->children) {
	    error("resize_tree", "Unable to reallocate subtree.");
            tree->children = old;
	    return -1;
        }
    }
    else tree->children = NULL; /* old is freed anyway */
    tree->msize = newsize;
    if (tree->children && tree->msize) format_treeslots(tree->children, tree->msize);

#if WANT_DUMP_REHASH_TREE
	fprintf(stderr, "Old=%p New=%p Tree_resize(%u/%u) %u\n", (void*) old, (void*) tree->children, tree->branch,  tree->msize, newsize);
#endif /* WANT_DUMP_REHASH_TREE */

/* Now rebuild the hash table.
 * The hash-chain pointers have already been initialized to NIL,
 * we only have to copy the children's "payload" verbatim,
 * find the place where to append it in the hash-chain, and put it there.
 */
    if (old) for (item =0 ; item < tree->branch; item++) {
	ChildIndex *ip;
	slot = old[item].ptr->symbol % tree->msize;
	for( ip = &tree->children[slot].tabl; *ip != CHILD_NIL; ip = &tree->children[*ip].link ) {

#if WANT_DUMP_REHASH_TREE
		fprintf(stderr, "%u,", (unsigned) *ip);
#endif
		}
#if WANT_DUMP_REHASH_TREE
		fprintf(stderr, "Placing Item=%u Hash=%5u(%8x) Slot=%4u TargetSlot=%u (previous %u)\n"
		, (unsigned) item , (unsigned) old[item].ptr->symbol, (unsigned) old[item].ptr->symbol, (unsigned) slot
		, (unsigned) ((char*) ip - (char*) &tree->children[0].tabl) / sizeof tree->children[0] 
		, (unsigned) *ip );
#endif
	*ip = item;
	tree->children[item].ptr = old[item].ptr;
	}
    free (old);
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

STATIC ChildIndex *node_hnd(TREE *node, WordNum symbol)
{
ChildIndex *ip;
unsigned slot;

if (!node->msize) return NULL;
slot = symbol % node->msize;
for (ip = &node->children[ slot ].tabl; *ip != CHILD_NIL; ip = &node->children[ *ip ].link ) {
	if (!node->children[ *ip ].ptr) {
		warn ( "Node_hnd", "empty child looking for %u\n", symbol);
		continue;
		}
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
#if WANT_TIMESTAMPED_NODES
    if (model->forward) model->forward->stamp = stamp_max;
    if (model->backward) model->backward->stamp = stamp_max;
#endif

}

double word_weight(DICT *dict, STRING word)
{
WordNum *np, symbol;

np = dict_hnd(dict, word);

if (!np || *np == WORD_NIL) return 0.0;
symbol = *np;

return symbol_weight(dict, symbol);
}

double symbol_weight(DICT *dict, WordNum symbol)
{
STRING alt;
WordNum *np, altsym;

if (!dict || !dict->size) return 0.0;

alt = word_dup_othercase(dict->entry[symbol].string);
np = dict_hnd(dict, alt);
if (!np || *np == WORD_NIL) altsym = symbol;
else altsym = *np;

#if (WANT_DUMP_KEYWORD_WEIGHTS & 8)
fprintf(stderr, "Symbol %u/%u:%u ('%*.*s') %u/%llu\n"
        , symbol, (unsigned)dict->size, (unsigned)dict->stats.nonzero
	, (int)dict->entry[symbol].string.length, (int)dict->entry[symbol].string.length, (int)dict->entry[symbol].string.word
	, (unsigned)dict->entry[symbol].stats.whits
	, (unsigned long long)dict->stats.whits
	);
if (altsym != symbol) fprintf(stderr, "AltSym %u/%u:%u ('%*.*s') %u/%llu\n"
        , symbol, (unsigned)dict->size, (unsigned)dict->stats.nonzero
	, (int)dict->entry[altsym].string.length, (int)dict->entry[altsym].string.length, (int)dict->entry[altsym].string.word
	, (unsigned)dict->entry[altsym].stats.whits
	, (unsigned long long)dict->stats.whits
	);
#endif
/*		, (double ) dict->entry[i].stats.nhits * dict->size / dict->stats.node */

if (altsym==symbol) {
        return ((double)dict->stats.whits / dict->stats.nonzero) /* used to be size */
		/ (0.5 + dict->entry[symbol].stats.whits)
		;
} else {
	return ((double)dict->stats.whits * 2 / dict->stats.nonzero) /* used to be size */
		/ (0.5 + dict->entry[symbol].stats.whits + dict->entry[altsym].stats.whits)
		;
	}
}

STATIC STRING word_dup_othercase(STRING org)
{
static char zzz[256];
STRING new = {0,zzz};
unsigned ii,chg;

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

/*
 *		Function:	Learn
 *
 *		Purpose:		Learn from the user's input.
 */
STATIC void learn_from_input(MODEL *model, DICT *words)
{
    unsigned widx;
    WordNum symbol;

    /*
     *		We only learn from inputs which are long enough
     */
    if (words->size <= model->order) return;
#if WANT_TIMESTAMPED_NODES
    stamp_max++;
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
    }
    /*
     *		Add the sentence-terminating symbol.
     */
    update_model(model, 1);

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
    update_model(model, 1);

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
    DICT *words = NULL;
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

    words = new_dict();

    progress("Training from file", 0, 1);
    while( fgets(buffer, sizeof buffer, fp) ) {
	if (buffer[0] == '#') continue;

	buffer[strlen(buffer)-1] ='\0';

	/* upper(buffer);*/
	make_words(buffer, words);
	learn_from_input(model, words);

	progress(NULL, ftell(fp), length);

    }
    progress(NULL, 1, 1);

    empty_dict(words);
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
    char hexdump[1024];
    size_t hexlen;

    fp = fopen("megahal.dic", "w");
    if (!fp) {
	warn("show_dict", "Unable to open file");
	return;
    }

fprintf(fp, "# TotStats= %llu %llu Words= %lu/%lu Nonzero=%lu\n"
	, (unsigned long long) dict->stats.nhits, (unsigned long long) dict->stats.whits
	, (unsigned long) dict->size, (unsigned long) dict->msize, (unsigned long) dict->stats.nonzero );
    for(iwrd = 0; iwrd < dict->size; iwrd++) {
		if ( word_has_highbit(dict->entry[iwrd].string)) hexdump_string(hexdump, dict->entry[iwrd].string);
		else hexdump[0] = 0;
	    fprintf(fp, "%lu\t%lu\t(%6.4e / %6.4e)\t%*.*s%s\n"
		, (unsigned long) dict->entry[iwrd].stats.nhits, (unsigned long) dict->entry[iwrd].stats.whits
		, (double ) dict->entry[iwrd].stats.nhits * dict->stats.nonzero / dict->stats.nhits
		, (double ) dict->entry[iwrd].stats.whits * dict->stats.nonzero / dict->stats.whits
		, (int) dict->entry[iwrd].string.length, (int) dict->entry[iwrd].string.length, dict->entry[iwrd].string.word 
		, hexdump
		);
    }

    fclose(fp);
}

void read_dict_from_ascii(DICT *dict, char *name)
{
    FILE *fp;
    char buff[300];
    unsigned long int nhits,whits;
    int pos;
    size_t len;
    STRING word;
    

    if (!dict) return;

    fp = fopen( name, "r");
    if (!fp) {
	warn("read_dict", "Unable to open file");
	return;
    }

while (fgets(buff, sizeof buff, fp)) {
	if (buff[0] == '#') continue;
	sscanf(buff, "%lu %lu\t%n",  &nhits, &whits,  &pos);
	pos += strcspn(buff+pos, "\t" );
	pos += 1;
        len = strcspn(buff+pos, "\n" );
        if (!len) continue;
        word.word= buff+pos;
        word.length = len;
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
    save_tree(fp, model->forward);
    save_tree(fp, model->backward);
    save_dict(fp, model->dict);
    status("Saved %lu nodes, %u words.\n", memstats.node_cnt,memstats.word_cnt);

    fclose(fp);
}

/*---------------------------------------------------------------------------*/

/*
 *		Function:	Save_Tree
 *
 *		Purpose:		Save a tree structure to the specified file.
 */
STATIC void save_tree(FILE *fp, TREE *node)
{
    static int level = 0;
    unsigned int ikid;

    fwrite(&node->symbol, sizeof node->symbol, 1, fp);
    fwrite(&node->usage, sizeof node->usage, 1, fp);
    fwrite(&node->count, sizeof node->count, 1, fp);
#if WANT_TIMESTAMPED_NODES
    fwrite(&node->stamp, sizeof node->stamp, 1, fp);
#endif
    fwrite(&node->branch, sizeof node->branch, 1, fp);
    memstats.node_cnt++;
    if (level == 0) progress("Saving tree", 0, 1);
    for(ikid = 0; ikid < node->branch; ikid++) {
	level++;
	save_tree(fp, node->children[ikid].ptr );
	level--;
	if (level == 0) progress(NULL, ikid, node->branch);
    }
    if (level == 0) progress(NULL, 1, 1);
}

/*---------------------------------------------------------------------------*/

/*
 *		Function:	Load_Tree
 *
 *		Purpose:		Load a tree structure from the specified file.
 */
STATIC void load_tree(FILE *fp, TREE *node)
{
    static int level = 0;
    unsigned int cidx;
    unsigned int symbol;
    ChildIndex *ip;
    size_t kuttje;

    kuttje = fread(&node->symbol, sizeof node->symbol, 1, fp);
    if (level==0 && node->symbol==0) node->symbol=1;
    kuttje = fread(&node->usage, sizeof node->usage, 1, fp);
    kuttje = fread(&node->count, sizeof node->count, 1, fp);
#if WANT_TIMESTAMPED_NODES
    kuttje = fread(&node->stamp, sizeof node->stamp, 1, fp);
    if ( node->stamp > stamp_max) stamp_max = node->stamp;
    else if ( node->stamp < stamp_min) stamp_min = node->stamp;
#endif
    kuttje = fread(&node->branch, sizeof node->branch, 1, fp);
    if (node->branch == 0) return;

    resize_tree(node , node->branch );
    if (!node->children) {
	error("load_tree", "Unable to allocate subtree");
	return;
    }

    if (level == 0) progress("Loading tree", 0, 1);
    for(cidx = 0; cidx < node->branch; cidx++) {
	node->children[cidx].ptr = new_node();
	level++;
	load_tree(fp, node->children[cidx].ptr);
	level--;

	symbol = node->children[cidx].ptr ? node->children[cidx].ptr->symbol: cidx;
	ip = node_hnd(node, symbol );
	if (ip) *ip = cidx;
	if (level == 0) progress(NULL, cidx, node->branch);
    }
    if (level == 0) progress(NULL, 1, 1);
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

    fp = fopen(filename, "rb");

    if (!fp) {
	warn("load_model", "Unable to open file `%s'", filename);
	return FALSE;
    }


    kuttje = fread(cookie, sizeof(char), strlen(COOKIE), fp);
    if (memcmp(cookie, COOKIE, strlen(COOKIE)) ) {
	warn("load_model", "File `%s' is not a MegaHAL brain", filename);
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
    load_tree(fp, model->forward);
    status("Backward\n");
    load_tree(fp, model->backward);
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
#if WANT_NEW_TOKENIZER
STATIC void make_words(char *input, DICT *words)
{
    size_t len, pos, chunk;
    STRING word ; 
    static STRING period = {1, "." }  ; 
    int state = 0; /* FIXME: this could be made static to allow for multi-line strings */

    empty_dict(words);

    len = strlen(input);
    if (!len) return;

    for(pos=0; pos < len ; ) {

	chunk = tokenize(input+pos, &state);
        if (!chunk) { /* maybe we should reset state here ... */ pos++; }
        if (chunk > 255) {
            warn( "Make_words", "Truncated too long  string(%u) at %s\n", (unsigned) chunk, input+pos);
            chunk = 255;
            }
        word.length = chunk;
        word.word = input+pos;
#if WANT_SUPPRESS_WHITESPACE
        if (word_is_usable(word)) add_word_nofuss(words, word);
#else
        add_word_nofuss(words, word);
#endif

        if (pos+chunk >= len) break;
        pos += chunk;
    }

    /*
     *		If the last word isn't punctuation, then replace it with a
     *		full-stop character.
     */
    if (words->size && myisalnum(words->entry[words->size-1].string.word[0])) {
		add_word_nofuss(words, period);
    }
    else if (words->size
		&& words->entry[words->size-1].string.length
		 && !strchr(".!?", words->entry[words->size-1].string.word[ words->entry[words->size-1].string.length-1] )) {
	words->entry[words->size-1].string = period;
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
 * multiple stretches of .,!? are kept intact. , multiple stretches of
 * other non alphanumerc tokens (@#$%^&*) as well.
 * brackets and brases are always chopped up to 1-character tokens.
 * quotes are not handled yet.
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
	/* if (UCP[pos] == '\'' ) { *sp |= 16; return pos; }*/
	/* if (UCP[posi] == '"' ) { *sp |= 32; return pos; }*/
#endif
    	if (myisalpha(UCP[pos])) {*sp = T_WORD; pos++; continue; }
    	if (myisalnum(UCP[pos])) {*sp = T_NUM; pos++; continue; }
	/* if (strspn(str+pos, "-+")) { *sp = T_NUM; pos++; continue; }*/
	*sp = T_ANY; continue;
	break;
    case T_ANY: /* either whitespace or meuk: eat it */
    	pos += strspn(str+pos, " \t\n\r\f\b" ); 
	if (pos) {*sp = T_INIT; return pos; }
        *sp = T_MEUK; continue;
        break;
    case T_WORD: /* inside word */
	while ( myisalnum(UCP[pos]) ) pos++;
    	if (UCP[pos] == '\0' ) { *sp = T_INIT;return pos; }
	if (UCP[pos] == '.' ) { *sp = T_WORDDOT; pos++; continue; }
	*sp = T_INIT; return pos;
        break;
    case T_WORDDOT: /* word. */
	if (myisalpha(UCP[pos]) ) { *sp = T_WORDDOTLET; pos++; continue; }
	*sp = T_INIT; return pos-1;
        break;
    case T_WORDDOTLET: /* word.A */
	if (UCP[pos] == '.') { *sp = T_AFKODOT; pos++; continue; }
	if (myisalpha(UCP[pos]) ) { *sp = T_INIT; return pos-2; }
	if (myisalnum(UCP[pos]) ) { *sp = T_NUM; continue; }
	*sp = T_INIT; return pos-2;
        break;
    case T_AFKODOT: /* A.B. */
        if (myisalpha(UCP[pos]) ) { *sp = T_AFKO; pos++; continue; }
        *sp = T_INIT; return pos >=3? pos: pos -2;
        break;
    case T_AFKO: /* word.A.B */
	if (UCP[pos] == '.') { *sp = T_AFKODOT; pos++; continue; }
	/* if (myisalpha(UCP[pos]) ) { pos++; continue; }*/
	if (myisalpha(UCP[pos]) ) { *sp = T_INIT; return pos - 2; }
	*sp = T_INIT; return pos-1;
        break;
    case T_NUM: /* number */
	if ( myisalnum(UCP[pos]) ) pos++;
	if (strspn(str+pos, ".,")) { *sp = T_NUMDOT; pos++; continue; }
	*sp = T_INIT; return pos;
        break;
    case T_NUMDOT: /* number[.,] */
	if (myisalpha(UCP[pos])) { *sp = T_NUMDOTLET; pos++; continue; }
	if (myisalnum(UCP[pos])) { *sp = T_NUM; pos++; continue; }
	if (strspn(str+pos, "-+")) { *sp = T_NUM; pos++; continue; }
	*sp = T_INIT; return pos-1;
        break;
    case T_NUMDOTLET: /* number[.,][a-z] */
	if (myisalpha(UCP[pos])) { *sp = T_INIT; return pos-2; }
	if (myisalnum(UCP[pos])) { *sp = T_NUM; pos++; continue; }
	*sp = T_INIT; return pos-2;
        break;
    case T_MEUK: /* inside meuk */
	if (myisalnum(UCP[pos])) {*sp = T_INIT; return pos; }
	if (myiswhite(UCP[pos])) {*sp = T_INIT; return pos; }
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

#else /*  WANT_NEW_TOKENIZER */
STATIC void make_words(char *input, DICT *words)
{
    size_t offset = 0;
    size_t len = strlen(input);
    STRING word ; 
    static STRING period = {1, "." }  ; 

    /*
     *		Clear the entries in the dictionary
     */
    empty_dict(words);

    /*
     *		If the string is empty then do nothing, for it contains no words.
     */
    if (len == 0) return;

    /*
     *		Loop forever.
     */
    while(1) {

	/*
	 *		If the current character is of the same type as the previous
	 *		character, then include it in the word.  Otherwise, terminate
	 *		the current word.
	 */
	if (boundary(input, offset)) {
		if (offset > 255) {
			warn( "Make_words", "String too long (%u) at %s\n", (unsigned) offset, input);
			offset = 255;
			}
		word.length = offset;
		word.word = input;
	    /*
	     *		Add the word to the dictionary
	     */
#if WANT_SUPPRESS_WHITESPACE
        if (word_is_usable(word)) add_word_nofuss(words, word);
#else
	add_word_nofuss(words, word);
#endif

	    if (offset == len) break;
	    input += offset;
	    len -= offset;
	    offset = 0;
	} else {
	    offset++;
	}
    }

    /*
     *		If the last word isn't punctuation, then replace it with a
     *		full-stop character.
     */
    if (words->size && myisalnum(words->entry[words->size-1].string.word[0])) {
		add_word_nofuss(words, period);
    }
    else if (words->size
		&& words->entry[words->size-1].string.length
		 && !strchr(".!?", words->entry[words->size-1].string.word[ words->entry[words->size-1].string.length-1] )) {
	words->entry[words->size-1].string = period;
    }

    return;
}

/*---------------------------------------------------------------------------*/
/*
 *		Function:	Boundary
 *
 *		Purpose:		Return whether or not a word boundary exists in a string
 *						at the specified location.
 */
STATIC bool boundary(char *str, size_t position)
{
    /* unsigned char *ucp = (unsigned char *) string;*/
    if (position == 0) return FALSE;

    if (UCP[position] == '\0' ) return TRUE;

    if (
	UCP[position] == '\''
	&& myisalpha(UCP[position-1])
	&& myisalpha(UCP[position+1])
	)
	return FALSE;

    if (
	position > 1
	&& UCP[position-1] == '\''
	&& myisalpha(UCP[position-2])
	&& myisalpha(UCP[position]) 
	)
	return FALSE;

    if (
	myisalpha(UCP[position])
	&& !myisalpha(UCP[position-1])
	)
	return TRUE;

    if (
	!myisalpha(UCP[position])
	&& myisalpha(UCP[position-1])
	)
	return TRUE;

    if (isdigit(UCP[position]) != isdigit(UCP[position-1]))
	return TRUE;

    return FALSE;
}

#endif /* WANT_NEW_TOKENIZER */

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

size_t hexdump_string(char *buff, STRING string)
{
unsigned idx;
for (idx = 0; idx <  string.length; idx++) {
	sprintf(buff+3*idx, " %02x", 0xff & string.word[idx] );
	}
return 3*idx;
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
STATIC void make_greeting(DICT *words)
{
    unsigned int iwrd;

    for(iwrd = 0; iwrd < words->size; iwrd++) free(words->entry[iwrd].string.word);
    empty_dict(words);
    if (glob_grt->size > 0) add_word_dodup(words, glob_grt->entry[ urnd(glob_grt->size) ].string );
}

/*---------------------------------------------------------------------------*/
/*
 *    Function:   Generate_Reply
 *
 *    Purpose:    Take a string of user input and return a string of output
 *                which may vaguely be construed as containing a reply to
 *                whatever is in the input string.
 */
STATIC char *generate_reply(MODEL *model, DICT *words)
{
    static char *output_none = "Geert! doe er wat aan!" ;
	/* "I don't know enough to answer you yet!"; */
    DICT *replywords;
    DICT *keywords;
    double surprise, max_surprise;
    char *output;
    unsigned count;
    int basetime;

#if ALZHEIMER_FACTOR
    count = urnd(ALZHEIMER_FACTOR);
    if (count == ALZHEIMER_FACTOR/2) {
        initialize_context(model);
        model_alzheimer(model, ALZHEIMER_NODE_COUNT);
	}
#else
    initialize_context(model);
#endif
    /*
     *		Create an array of keywords from the words in the user's input
     */
    keywords = make_keywords(model, words);

    output = output_none;

#if 0
    {
    static DICT *dummy = NULL;
    if (!dummy) dummy = new_dict();
    replywords = one_reply(model, dummy);
    if (dissimilar(words, replywords)) output = make_output(replywords);
    }
#else
    replywords = one_reply(model, keywords);
    /* output = make_output(replywords); */
#endif

    /*
     *		Loop for the specified waiting period, generating and evaluating
     *		replies
     */
    max_surprise = -1.0;
    count = 0;
    basetime = time(NULL);
    progress("Generating reply", 0, 1); 
    do {
	replywords = one_reply(model, keywords);
	if (replywords->size < MIN_REPLY_SIZE) continue;
	surprise = evaluate_reply(model, keywords, replywords);
	count++;
	if (surprise > max_surprise && dissimilar(words, replywords) ) {
	    output = make_output(replywords);
#if WANT_DUMP_ALL_REPLIES
		fprintf(stderr, "\n%u %lf/%lf:\n\t%s\n", count, surprise, max_surprise, output);
#endif
	    max_surprise = surprise;
	}
 	progress(NULL, (time(NULL)-basetime),glob_timeout);
    } while(time(NULL)-basetime < glob_timeout);
    progress(NULL, 1, 1);

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
STATIC bool dissimilar(DICT *dic1, DICT *dic2)
{
    unsigned int iwrd;

    if (dic1->size != dic2->size) return TRUE;
    for(iwrd = 0; iwrd < dic1->size; iwrd++)
	if (wordcmp(dic1->entry[iwrd].string , dic2->entry[iwrd].string ) ) return TRUE;
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
STATIC DICT *make_keywords(MODEL *model, DICT *words)
{
    /* static DICT *keys = NULL; */
    unsigned int ikey;
    unsigned int iwrd;
    WordNum symbol;

#if CROSS_DICT_SIZE
    WordNum echobox[CROSS_DICT_WORD_DISTANCE];
    unsigned rotor , echocount;

    if (!glob_crosstab ) {
	glob_crosstab = crosstab_init(CROSS_DICT_SIZE);
	}
    rotor = echocount = 0;
#endif

    if (!glob_keys) {
	glob_keys = new_dict();
	}


#if (KEYWORD_DICT_SIZE)
#else
    for(ikey = 0; ikey < glob_keys->size; ikey++) free(glob_keys->entry[ikey].string.word);
    /* glob_keys->size = 0;*/
    empty_dict(glob_keys);
#endif

    for(iwrd = 0; iwrd < words->size; iwrd++) {
	/*
	 *		Find the symbol ID of the word.  If it doesn't exist in
	 *		the model, or if it begins with a non-alphanumeric
	 *		character, or if it is in the exclusion array, then
	 *		skip over it.
	 */
	if (!myisalnum(words->entry[iwrd].string.word[0] )) continue;
	/* if (word_is_allcaps(words->entry[iwrd].string)) continue;*/
        symbol = find_word(model->dict, words->entry[iwrd].string );
        if (symbol == WORD_NIL) continue;
        if (symbol == WORD_ERR) continue;
        if (symbol == WORD_FIN) continue;
        if (symbol >= model->dict->size) continue;

		/* we may or may not like frequent words */
        if (model->dict->entry[symbol].stats.whits > model->dict->stats.whits / model->dict->stats.nonzero ) continue;
#if CROSS_DICT_SIZE
	{
	unsigned other;
	for (other = 0; other < echocount; other++ ) {
		if (symbol < 2 || symbol >= model->dict->size
		|| echobox[other] < 2 || echobox[other] >= model->dict->size ) fprintf(stderr, "[? %u, %u[%u/%u]]\n"
			, symbol,echobox[other], other, echocount);
		else crosstab_add_pair( glob_crosstab, echobox[other] , symbol );
		}
	if (echocount < COUNTOF(echobox)) echocount++;
	echobox[rotor++] = symbol;
	if (rotor >= COUNTOF(echobox)) rotor =0;
	/* fprintf(stderr, "[%u/%u %u]", rotor, echocount, other); */
	}
#endif

#if DONT_WANT_THIS
    {
    unsigned int iswp, swapped = 0;
	for(iswp = 0; iswp < glob_swp->size; iswp++)
	    if (!wordcmp(glob_swp->pairs[iswp].from , words->entry[iwrd].string ) ) {
		add_key(model, glob_keys, glob_swp->pairs[iswp].to );
		swapped++;
		break;
	    }
	if (!swapped) add_key(model, glob_keys, words->entry[iwrd].string );
    }
#else
	add_key(model, glob_keys, words->entry[iwrd].string );
#if (KEYWORD_DICT_SIZE)
        if (glob_keys->size > 2* KEYWORD_DICT_SIZE) schrink_keywords(glob_keys, KEYWORD_DICT_SIZE);
#endif
#endif
    }

#if (KEYWORD_DICT_SIZE)
    /* perform russian roulette on the keywords. */
    schrink_keywords(glob_keys, KEYWORD_DICT_SIZE);
#endif

#if DONT_WANT_THIS
    if (glob_keys->size > 0) for(iwrd = 0; iwrd < words->size; iwrd++) {

	if (!myisalnum(words->entry[iwrd].string.word[0] )) continue;
	swapped = 0;
	for(iswp = 0; iswp < glob_swp->size; iswp++)
	    if (!wordcmp(glob_swp->pairs[iswp].from, words->entry[iwrd].string )) {
		add_aux(model, glob_keys, glob_swp->pairs[iswp].to );
		swapped++;
		break;
	    }
	if (!swapped) add_aux(model, glob_keys, words->entry[iwrd].string );
    }
#endif

#if CROSS_DICT_SIZE
	crosstab_show(stderr, glob_crosstab, symbol_format);
#endif
#if (WANT_DUMP_KEYWORD_WEIGHTS & 2)
fprintf(stderr, "Total %u W=%llu N=%llu\n"
	, (unsigned) glob_keys->size
	, (unsigned long long)glob_keys->stats.whits
	, (unsigned long long)glob_keys->stats.nhits
	);
for (ikey=0; ikey < glob_keys->size; ikey++) {
	double gweight,kweight, eweight;
	symbol = find_word(model->dict, glob_keys->entry[ikey].string );
	gweight = word_weight (model->dict, glob_keys->entry[ikey].string);
	kweight = word_weight (glob_keys, glob_keys->entry[ikey].string);
	eweight = crosstab_ask(glob_crosstab, symbol);
	fprintf(stderr, "[%2u] w=%u n=%u := G=%6.4e K=%6.4e E=%6.4e %c '%*.*s'\n"
	, ikey
	, (unsigned)glob_keys->entry[ikey].stats.whits
	, (unsigned)glob_keys->entry[ikey].stats.nhits
	, gweight, kweight, eweight
	, (glob_keys->entry[ikey].stats.whits > glob_keys->size) ? '+' : '-'
	, (int)glob_keys->entry[ikey].string.length, (int)glob_keys->entry[ikey].string.length, glob_keys->entry[ikey].string.word
	);
	}
#endif

#if (WANT_DUMP_KEYWORD_WEIGHTS & 1)
fprintf(stderr, "Returned %u keywords\n", glob_keys->size );
#endif
    return glob_keys;
}

/*---------------------------------------------------------------------------*/
STATIC void schrink_keywords(DICT *words, unsigned newsize)
{
    unsigned int ikey;
    static UsageCnt whits=0,nhits=0;

    if (!words || !words->size ) return;

    if (!whits) whits = words->stats.whits / words->size;
    if (!nhits) nhits = words->stats.nhits / words->size;

    while ( words->size > newsize ) {
	ikey = urnd(words->size) ;
		/* This is ugly. There appears to be a "reference leak" somewhere in
		** the keyword dict, causing underflow in the totals.
		** This is an attempt to (at least) stabilize the totals by maintaining a floating average,
		** in such a way that the totals never underflow. The totals will be incorrect, but exact scaling is not needed.
		*/
	whits = ( 9* whits + 1* words->entry[ikey].stats.whits) / (10);
	nhits = ( 9* nhits + 1* words->entry[ikey].stats.nhits) / (10);
	if (words->entry[ikey].stats.whits > whits) {	words->entry[ikey].stats.whits -= sqrt(whits); continue; }
	if (words->entry[ikey].stats.nhits > nhits) {	words->entry[ikey].stats.nhits -= 1; continue; }
	
        words->stats.whits = (words->stats.whits + words->size * whits) / 2;
        words->stats.nhits = (words->stats.nhits + words->size * nhits) / 2;
	del_word_dofree(words, words->entry[ikey].string );
	}
return;
}
/*---------------------------------------------------------------------------*/

/*
 *		Function:	Add_Key
 *
 *		Purpose:		Add a word to the keyword dictionary.
 */
STATIC void add_key(MODEL *model, DICT *keywords, STRING word)
{
    WordNum ksymbol,oldtopsym;

    if (!myisalnum(word.word[0])) return;
#if DONT_WANT_THIS
    {
    WordNum symbol, xsymbol;
    symbol = find_word(model->dict, word);
    if (symbol == WORD_NIL) return;
    xsymbol = find_word(glob_ban, word);
    if (xsymbol != WORD_NIL) return;
    xsymbol = find_word(glob_aux, word);
    if (xsymbol == WORD_NIL) return;
    }
#endif

    oldtopsym = (keywords->size>0) ? keywords->size-1 : WORD_NIL;
    ksymbol = add_word_dodup(keywords, word);
    if (ksymbol == WORD_NIL) return;
	/* is this a freshly inserted symbol ? */
    if (ksymbol == keywords->size-1 && ksymbol != oldtopsym) {
	dict_inc_ref(keywords, ksymbol, 1, KEYWORD_DICT_SIZE);
	}
    else {
	dict_inc_ref(keywords, ksymbol, 0, KEYWORD_DICT_SIZE);
	}
}
/*---------------------------------------------------------------------------*/

/*
 *		Function:	Add_Aux
 *
 *		Purpose:		Add an auxilliary keyword to the keyword dictionary.
 */
STATIC void add_aux(MODEL *model, DICT *keywords, STRING word)
{
    WordNum symbol;

    if (!myisalnum(word.word[0]) ) return;
    symbol = find_word(model->dict, word);
    if (symbol == WORD_NIL) return;
    symbol = find_word(glob_aux, word);
    if (symbol == WORD_NIL) return;

    add_word_dodup(keywords, word);
}

/*---------------------------------------------------------------------------*/

/*
 *		Function:	Reply
 *
 *		Purpose:		Generate a dictionary of reply words appropriate to the
 *						given dictionary of keywords.
 */
STATIC DICT *one_reply(MODEL *model, DICT *keywords)
{
    static DICT *replies = NULL;
    unsigned int widx;
    WordNum symbol;
    bool start = TRUE;

    if (!replies) replies = new_dict();
    else empty_dict(replies);

    /*
     *		Start off by making sure that the model's context is empty.
     */
    initialize_context(model);
    model->context[0] = model->forward;
    used_key = FALSE;

    /*
     *		Generate the reply in the forward direction.
     */
    while(1) {
	/*
	 *		Get a random symbol from the current context.
	 */
	if (start == TRUE) symbol = seed(model, keywords);
	else symbol = babble(model, keywords, replies);
	if (symbol <= 1) break;
	start = FALSE;

	/*
	 *		Append the symbol to the reply dictionary.
	 */
	add_word_nofuss(replies, model->dict->entry[symbol].string );
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
    for(widx = MIN(replies->size, 1+model->order); widx-- > 0; ) {
	symbol = find_word(model->dict, replies->entry[ widx ].string );
	update_context(model, symbol);
    }

    /*
     *		Generate the reply in the backward direction.
     */
    while(1) {
	/*
	 *		Get a random symbol from the current context.
	 */
	symbol = babble(model, keywords, replies);
	if (symbol <= 1) break;

	/*
	 *		Prepend the symbol to the reply dictionary.
	 */
	replies->entry = realloc(replies->entry, (replies->size+1)*sizeof *replies->entry);
	if (!replies->entry) {
	    error("one_reply", "Unable to reallocate dictionary");
	    return NULL;
	}

	/*
	 *		Shuffle everything up for the prepend.
	 */
	for(widx = replies->size; widx > 0; widx--) {
	    replies->entry[widx].string = replies->entry[widx-1].string;
	}
	replies->size += 1;

	replies->entry[0].string = model->dict->entry[symbol].string;

	/*
	 *		Extend the current context of the model with the current symbol.
	 */
	update_context(model, symbol);
    }

    return replies;
}

/*---------------------------------------------------------------------------*/

/*
 *		Function:	Evaluate_Reply
 *
 *		Purpose:		Measure the average surprise of keywords relative to the
 *						language model.
 */
STATIC double evaluate_reply(MODEL *model, DICT *keywords, DICT *sentence)
{
    unsigned int widx, iord;
    WordNum symbol, ksymbol;
    double gfrac, kfrac,efrac, weight,probability, entropy = 0.0;
    unsigned count, totcount = 0;
    TREE *node;

    if (sentence->size == 0) return 0.0;
    initialize_context(model);
    model->context[0] = model->forward;
    for (widx = 0; widx < sentence->size; widx++) {
	symbol = find_word(model->dict, sentence->entry[widx].string );
	ksymbol = find_word(keywords, sentence->entry[widx].string );

	if (ksymbol == WORD_NIL) goto update1;
	probability = 0.0;
        count = 0;
        totcount++;
        for(iord = 0; iord < model->order; iord++) {
            if ( !model->context[iord] ) continue;

            node = find_symbol(model->context[iord], symbol);
            if (!node) continue;

            probability += (double)node->count / model->context[iord]->usage;
            count++;
            }

        if (!count ) goto update1;
        gfrac = symbol_weight(model->dict, symbol);
        kfrac = symbol_weight(keywords, ksymbol);
	efrac = crosstab_ask(glob_crosstab, symbol);
        /* weight = gfrac/kfrac; */
        weight = gfrac*efrac;

#if (WANT_DUMP_KEYWORD_WEIGHTS & 4)
        fprintf(stderr, "%*.*s: Keyw= %lu/%lu : %llu/%llu (%6.4e)  Glob=%u/%u (%6.4e)  Prob=%6.4e/Count=%u Weight=%6.4e Term=%6.4e %c\n"
        , (int) sentence->entry[widx].string.length
        , (int) sentence->entry[widx].string.length
        , sentence->entry[widx].string.word
        , (unsigned long) keywords->entry[ksymbol].stats.whits
        , (unsigned long) keywords->entry[ksymbol].stats.nhits
        , (unsigned long long) keywords->stats.whits
        , (unsigned long long) keywords->stats.nhits
        , kfrac
        , model->dict->entry[symbol].stats.whits
        , model->dict->entry[symbol].stats.nhits
        , gfrac
        , probability , (unsigned) count
        , weight
        , probability *weight / count
        , weight > 1.0 ? '*' : ' '
        );
#endif
#if WANT_KEYWORD_WEIGHTS
        probability *= weight;
#endif
        entropy -= log(probability / count);
update1:
        update_context(model, symbol);
    }

    initialize_context(model);
    model->context[0] = model->backward;
    for(widx = sentence->size; widx-- > 0; ) {
	symbol = find_word(model->dict, sentence->entry[widx].string );

	ksymbol = find_word(keywords, sentence->entry[widx].string );
	if ( ksymbol == WORD_NIL) goto update2;
        probability = 0.0;
        count = 0;
        totcount++;
        for(iord = 0; iord < model->order; iord++) {
            if ( !model->context[iord] ) continue;

            node = find_symbol(model->context[iord], symbol);
            if (!node) continue;
            probability += (double)node->count / model->context[iord]->usage;
            count++;

        }

        if ( !count ) goto update2;
        gfrac = symbol_weight(model->dict, symbol);
        kfrac = symbol_weight(keywords, ksymbol);
	efrac = crosstab_ask(glob_crosstab, symbol);
        /* weight = gfrac/kfrac; */
        weight = gfrac*efrac;
#if WANT_KEYWORD_WEIGHTS
        probability *= weight;
#endif
        entropy -= log(probability / count);
update2:
        update_context(model, symbol);
    }

    /* if (totcount >= 8) entropy /= sqrt(totcount-1); */
    /* if (totcount >= 16) entropy /= totcount;*/
    if (totcount >= 3) entropy /= sqrt(totcount-1); 
    if (totcount >= 7) entropy /= totcount;

	/* extra penalty for sentences that don't start with a capitalized letter */
    widx = sentence->size;
    if (widx && sentence->entry[0].string.length 
	&& ( myislower( sentence->entry[0].string.word[ 0 ] )
	 || ! myisalnum( sentence->entry[0].string.word[ 0 ] )) ) entropy /= 2;
	/* extra penalty for incomplete sentences */
    widx = sentence->size;
    if (widx-- && sentence->entry[widx].string.length 
	&& !strchr(".!?", sentence->entry[widx].string.word[ sentence->entry[widx].string.length-1] )) entropy /= 2;
    return entropy;
}

/*---------------------------------------------------------------------------*/

/*
 *		Function:	Make_Output
 *
 *		Purpose:		Generate a string from the dictionary of reply words.
 */
STATIC char *make_output(DICT *words)
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


    if (words->size == 0) { return output_none; }
	/* calculate the space we'll need.
	** We assume one space between adjacent wordst plus a NUL at the end.
	*/
    length = 1;
#if WANT_SUPPRESS_WHITESPACE
    for(widx = 0; widx < words->size; widx++) length += 1+ words->entry[widx].string.length;
#else
    for(widx = 0; widx < words->size; widx++) length += words->entry[widx].string.length;
#endif

    output = realloc(output, length);
    if (!output) {
	error("make_output", "Unable to reallocate output.");
	return output_none;
    }

#if WANT_SUPPRESS_WHITESPACE
    tags = malloc(2+words->size);
    if (tags) memset(tags, 0, words->size);
#define NO_SPACE_L 1
#define NO_SPACE_R 2
#define IS_SINGLE 4
#define IS_DOUBLE 8
#define IS_HYPHEN 16

	/* do we want a white before or after the token at [widx] ? */
    for(widx = 0; widx < words->size; widx++) {
	if (!widx			|| dont_need_white_l(words->entry[widx].string)) tags[widx] |= NO_SPACE_L;
	if (widx == words->size-1	|| dont_need_white_r(words->entry[widx].string)) tags[widx] |= NO_SPACE_R;
	if (words->entry[widx].string.length <= 1 && words->entry[widx].string.word[0] == '\'' ) { sqcnt++; tags[widx] |= IS_SINGLE; }
	if (words->entry[widx].string.length <= 1 && words->entry[widx].string.word[0] == '"' ) { dqcnt++; tags[widx] |= IS_DOUBLE; }
	if (words->entry[widx].string.length <= 1 && words->entry[widx].string.word[0] == '-' ) { hycnt++; tags[widx] |= IS_HYPHEN; }
	}

	/* First detect o'Hara and don't */
    if (sqcnt >0) for(widx = 0; widx < words->size; widx++) {
	if ( !(tags[widx] & IS_SINGLE)) continue;
#if 0
	 fprintf(stderr, "Single:"); dump_word(stderr, words->entry[widx].string);
	if (widx) { fprintf(stderr, "left:"); dump_word(stderr, words->entry[widx-1].string); fputc('\n', stderr); }
	if (widx <words->size-1) { fprintf(stderr, "Right:"); dump_word(stderr, words->entry[widx+1].string); fputc('\n', stderr); }
#endif
	/* if the word to the left is absent or 1char we dont want a white inbetween */
	if (!widx || words->entry[widx-1].string.length <2) {
		tags[widx] |= NO_SPACE_L;
		tags[widx] |= NO_SPACE_R;
		tags[widx] &= ~IS_SINGLE;
		sqcnt--;
		}
	/* if the word to the right is absent or 1char we dont want a white inbetween */
	if (widx == words->size-1 || words->entry[widx+1].string.length <2) {
		tags[widx] |= NO_SPACE_L;
		tags[widx] |= NO_SPACE_R;
		tags[widx] &= ~IS_SINGLE;
		}
	}

	/* Try to match pairs of single quotes. This is rude: we don't care about nesting. */
    if (sqcnt >1) for(begin= -1,widx = 0; widx < words->size; widx++) {
		if (!(tags[widx] & IS_SINGLE)) continue;
		if (begin < 0) {begin = widx; continue; }
		tags[begin] |= NO_SPACE_R; tags[begin] &= ~NO_SPACE_L; if (begin) tags[begin-1] &= ~NO_SPACE_R;
		tags[widx] |= NO_SPACE_L; tags[widx] &= ~NO_SPACE_R; if (begin < words->size-1) tags[begin+1] &= ~NO_SPACE_L;
		tags[begin] &= ~IS_SINGLE;
		tags[widx] &= ~IS_SINGLE;
		begin = -1;
		sqcnt -= 2;
		}

	/* idem: double quotes */
    if (dqcnt >1) for(begin= -1,widx = 0; widx < words->size; widx++) {
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
    if (hycnt >1) for(begin= -1,widx = 0; widx < words->size; widx++) {
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
	**  they don't want whitspace around them. Rude, again.
	*/
    if (sqcnt+dqcnt+hycnt) for(widx = 0; widx < words->size; widx++) {
		if (!(tags[widx] & (IS_SINGLE | IS_DOUBLE | IS_HYPHEN))) continue;
		tags[widx] |= NO_SPACE_L;
		tags[widx] |= NO_SPACE_R;
		}
#endif

    length = 0;
    for(widx = 0; widx < words->size; widx++) {
#if WANT_SUPPRESS_WHITESPACE
	if (!widx) {;}
	else if (tags[widx] & NO_SPACE_L ) {;}
	else if (tags[widx-1] & NO_SPACE_R) {;}
	else output[length++] = ' ';
#endif
	memcpy(output+length, words->entry[widx].string.word, words->entry[widx].string.length);
	length += words->entry[widx].string.length;
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
STATIC WordNum babble(MODEL *model, DICT *keywords, DICT *words)
{
    TREE *node;
    unsigned int oidx,cidx;
    unsigned count;
    WordNum symbol = 0;


    /*
     *		Select the longest available context.
     */
    node = NULL;
    for(oidx = 0; oidx <= model->order; oidx++) {
	if (!model->context[oidx] ) continue;
	    node = model->context[oidx];
	}

    if (!node || node->branch == 0) return 0;

    /*
     *		Choose a symbol at random from this context.
     */
    cidx = urnd(node->branch);
    count = urnd(node->usage);
    while(count > 0) {
	/*
	 *		If the symbol occurs as a keyword, then use it.  Only use an
	 *		auxilliary keyword if a normal keyword has already been used.
	 */
	symbol = node->children[cidx].ptr->symbol;
#if DONT_WANT_THIS
	if (find_word(keywords, model->dict->entry[symbol].string) == WORD_NIL ) goto next;
	if (used_key == FALSE && find_word(glob_aux, model->dict->entry[symbol].string) != WORD_NIL) goto next;
	if (word_exists(words, model->dict->entry[symbol].string) ) goto next;
	used_key = TRUE;
#endif
next:
	if (count > node->children[cidx].ptr->count) count -= node->children[cidx].ptr->count;
	else break; /*count = 0;*/
	cidx = (cidx+1) % node->branch;
    }

    return symbol;
}

/*---------------------------------------------------------------------------*/

/*
 *		Function:	Word_Exists
 *
 *		Purpose:		A silly brute-force searcher for the reply string.
 */
STATIC bool word_exists(DICT *dict, STRING word)
{
    unsigned int iwrd;

    for(iwrd = 0; iwrd < dict->size; iwrd++)
	if (!wordcmp(dict->entry[iwrd].string , word) )
	    return TRUE;
    return FALSE;
}

/*---------------------------------------------------------------------------*/

/*
 *		Function:	Seed
 *
 *		Purpose:		Seed the reply by guaranteeing that it contains a
 *						keyword, if one exists.
 */
STATIC WordNum seed(MODEL *model, DICT *keywords)
{
    unsigned int kidx;
    WordNum symbol, xsymbol;
    double weight,bestweight = 0.0;

    /*
     *		Fix, thanks to Mark Tarrabain
     */
#if 0
    if (model->context[0]->branch == 0) symbol = 0;
    else symbol = model->context[0]->children[ urnd(model->context[0]->branch) ].ptr->symbol;

    if (keywords && keywords->size > 0) {
        /* unsigned int stop;*/
	/* stop = kidx = urnd(keywords->size);*/
	/* for (kidx=(kidx+1)%keywords->size; kidx != stop; kidx = (kidx+1) % keywords->size) {*/
	for (kidx = urnd(keywords->size/4); kidx <  keywords->size;kidx += 1+urnd(keywords->size/4) ) {
	    /* if ( find_word(glob_aux, keywords->entry[kidx].string ) != WORD_NIL ) continue;*/
	    xsymbol = find_word(model->dict, keywords->entry[kidx].string );
	    if ( xsymbol < 2 || xsymbol == WORD_NIL) continue;
            weight = symbol_weight(model->dict, xsymbol) ;
            if (weight < bestweight) continue;
            bestweight = weight;
	    symbol = xsymbol;
	    }
	}
#else
	symbol = crosstab_get(glob_crosstab, urnd( sqrt(CROSS_DICT_SIZE*CROSS_DICT_SIZE/2)) );
	if (symbol > model->dict->size) symbol = 0;
#endif

    return symbol;
}

/*---------------------------------------------------------------------------*/

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
    static STRING word ={0,buffer};

    this = new_dict();

    if (!filename) return this;

    fp = fopen(filename, "r");
    if ( !fp ) return this;

    while( fgets(buffer, sizeof buffer, fp) ) {
	if (buffer[0] == '#') continue;
#if 0
        {
        char *string;
	string = strtok(buffer, "\t \n#");
	if ( !string || !*string) continue;

	word = new_string(buffer, 0);
        }
#else
        {
        size_t len;
        word.length = len = strcspn (buffer, "\t \n#" );
        if (!len) continue;
        }
#endif
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
STATIC unsigned int urnd(unsigned int range)
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
if (range <1) return 0;
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
void changevoice(DICT* words, unsigned int position)
{
#ifdef __mac_os
    int i, index;
    STRING word ={ 1, "#" };
    char buffer[80];
    VoiceSpec voiceSpec;
    VoiceDescription info;
    short count, voiceCount;
    unsigned char* temp;
    OSErr err;
    /*
     *		If there is less than 4 words, no voice specified.
     */
    if (words->size <= 4) return;

    for(i = 0; i < words->size-4; i++)
	if (!wordcmp(word, words->entry[i].string ) ) {

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
		    memcpy(buffer, words->entry[index].string.word, sizeof buffer);
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
    free_swap(glob_swp);

    /*
     *		Create a language model.
     */
    *model = new_model(glob_order);

    /*
     *		Train the model on a text if one exists
     */

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
    sprintf(filename, "%s%smegahal.swp", glob_directory, SEP);
    glob_swp = initialize_swap(filename);
}

/*---------------------------------------------------------------------------*/

void change_personality(DICT *command, unsigned int position, MODEL **model)
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

STATIC WordNum * dict_hnd_tail (DICT *dict, STRING word)
{
WordNum *np;

for (np = dict_hnd(dict,word); np ; np = &dict->entry[*np].link ) {
	if (*np == WORD_NIL) break;
	}
return np;
}

STATIC int grow_dict(DICT *dict)
{
    unsigned newsize;

    newsize = dict->size ? dict->size + dict->size/2 : DICT_SIZE_INITIAL;
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
		dict->entry[item].stats.nhits = old[item].stats.nhits;
		dict->entry[item].stats.whits = old[item].stats.whits;
		dict->entry[item].string = old[item].string;
		}
    free (old);
    return 0; /* success */
}

/*********************************************************************************************/

static TREE * alz_stack[10] = {NULL,};
static FILE *alz_file = NULL;

STATIC unsigned model_alzheimer(MODEL * model, unsigned maxnodecount)
{
Stamp limit;
unsigned step, width;
unsigned count, totcount;
static double dens = 0.0;
int rc;

if (!model || ! maxnodecount) return 0;
if (memstats.node_cnt <= ALZHEIMER_NODE_COUNT) return 0;

alz_dict = model->dict;


alz_file = fopen ("alzheimer.dmp", "a" );

	/* dens is an estimate of the amount of nodes we expect to reap per timestamp
	** step is our estimate for the number of steps we need to add to stamp_min to harvest
	** the intended amount of nodes. (= bring down memstats.node_cnt to maxnodecount)
	*/
if (dens == 0.0) {
	width = (unsigned)(stamp_max-stamp_min);
	if (width < 2) return 0;
	dens = (double)memstats.node_cnt / width ;
	}

for(  totcount = 0; memstats.node_cnt > maxnodecount;	) {
    width = stamp_max-stamp_min;
    step = (memstats.node_cnt - maxnodecount) / dens;
    if (!step) step = width / 100;
    while (step && step > width/10) step /= 2;
    if (!step) step = 2;
    limit = stamp_min + step;

#if WANT_DUMP_ALZHEIMER_PROGRESS
    fprintf(stderr, "Model_alzheimer() Count=%u/%u Stamp_min=%u Stamp_max=%u Width=%u Dens=%6.4f Step=%u Limit=%u\n"
	    , (unsigned)memstats.node_cnt, (unsigned)maxnodecount
	    , (unsigned)stamp_min, (unsigned)stamp_max
            , (unsigned)width, dens, step, (unsigned)limit);
#endif

    fprintf(alz_file, "Model_alzheimer() Count=%u/%u Stamp_min=%u Stamp_max=%u Width=%u Dens=%6.4f Step=%u Limit=%u\n"
	    , (unsigned)memstats.node_cnt, (unsigned)maxnodecount
	    , (unsigned)stamp_min, (unsigned)stamp_max
            , (unsigned)width, dens, step, (unsigned)limit);

    rc = check_interval(stamp_min, stamp_max, limit);
    if (rc) { /* outside interval */
#if WANT_DUMP_ALZHEIMER_PROGRESS
	    fprintf(stderr, "Model_alzheimer() outside interval Rc=%d Ajuus!\n", rc);
#endif
	    fprintf(alz_file, "Model_alzheimer() outside interval Rc=%d Ajuus!\n", rc);
	    if (width < 2) goto ajuus;
	    dens = (double)memstats.node_cnt / width;
            continue;
	    }

    count = symbol_alzheimer_recurse(model->forward, 0, limit);
#if WANT_DUMP_ALZHEIMER_PROGRESS
    fprintf(stderr, "symbol_alzheimer_recursed(forward) := %u\n", count);
#endif
    totcount += count;

    count = symbol_alzheimer_recurse(model->backward, 0, limit);
#if WANT_DUMP_ALZHEIMER_PROGRESS
    fprintf(stderr, "symbol_alzheimer_recursed(backward) := %u\n", count);
#endif
    totcount += count;

    stamp_min = limit;
	/*
	** adjust running average of density.
	**  If nothing is harvested, increase the stepsize by lowering the density estimate.
	**  0.8 might overshoot.  maybe 0.9...0.95 is better, but that may take too many iterations.
	** NOTE: we only use the count for the backward tree, and assume the same yield from the
	** forward tree.
	*/
    if (count) { dens += 2.0* count / step; dens /= 2; }
    else dens *= 0.8;

#if WANT_DUMP_ALZHEIMER_PROGRESS
    fprintf(stderr, "Model_alzheimer() Count=%u/%u Stamp_min=%u Stamp_max=%u Width=%u Dens=%6.4f\n"
	    , (unsigned)memstats.node_cnt, (unsigned)maxnodecount
	    , (unsigned)stamp_min, (unsigned)stamp_max,(unsigned)(stamp_max-stamp_min), dens);
#endif

    fprintf(alz_file, "Model_alzheimer() Count=%u/%u Stamp_min=%u Stamp_max=%u Width=%u Dens=%6.4f\n"
	    , (unsigned)memstats.node_cnt, (unsigned)ALZHEIMER_NODE_COUNT
	    , (unsigned)stamp_min, (unsigned)stamp_max, (unsigned)(stamp_max-stamp_min), dens);
	/* Avoid the next iteration to overshoot (we expect to harvest 2*count) */
    if (memstats.node_cnt <= maxnodecount+count) break;
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
#if (WANT_DUMP_ALZHEIMER_PROGRESS >= 2)
	for (slot=0; slot< lev; slot++) fputc(' ', alz_file);
	for (slot=0; slot< lev; slot++) fprintf(alz_file, "[%u:%u]", alz_stack[slot]->symbol, alz_stack[slot]->stamp );
	fprintf(alz_file, "symbol_alzheimer_recurse(rc=%d) Node considered too old (stamp=%u symbol=%u usage=%u count=%u)\n"
	, rc, tree->stamp, tree->symbol, tree->usage, tree->count);
#endif
#if (WANT_DUMP_ALZHEIMER_PROGRESS >= 4)
	dump_model_recursive(alz_file, tree, alz_dict, lev);
#endif
	}

/* We should work from top to bottom, because it would require less shuffling */
count = 0;
for (slot = tree->branch; slot--> 0;	) {
	TREE *child;

#if (WANT_DUMP_ALZHEIMER_PROGRESS >= 2)
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
/* Eof */
