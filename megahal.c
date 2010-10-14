
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

#define STATIC static
#define STATIC /* EMPTY:: For profiling, to avoid inlining of STATIC functions. */

#define WANT_DUMP_REHASH_TREE 1
#undef WANT_DUMP_REHASH_TREE

#define WANT_DUMP_KEYWORD_WEIGHTS 1
#undef WANT_DUMP_KEYWORD_WEIGHTS

#define WANT_DUMP_ALL_REPLIES 1
#undef WANT_DUMP_ALL_REPLIES

/* the number of keywords that is kept between replies.
 * Zero to disable */
#define KEYWORD_DICT_SIZE 0

/* (1/ALZHEIMER_FACTOR) is the chance 
** of alzheimer hitting the tree, once per reply.
** Zero to disable
** 10 is disastrous, 100 is still too big; 1000 might be good enough.
*/
#define ALZHEIMER_FACTOR 0

#undef WANT_DUMP_ALZHEIMER_PROGRESS
#define WANT_DUMP_ALZHEIMER_PROGRESS 1

/* improved random generator, using noise from the CPU clock (only works on intel/gcc) */
#undef WANT_RDTSC_RANDOM
#define WANT_RDTSC_RANDOM 1

#define DICT_SIZE_INITIAL 4
#define NODE_SIZE_INITIAL 2
#define MIN_PAREL_SIZE 30

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
typedef unsigned long long BigThing;
BigThing rdtsc_rand(void);

#define WORD_NIL ((WordNum)-1)
#define CHILD_NIL ((ChildIndex)-1)

typedef struct {
    StrLen length;
    char *word;
} STRING;

struct	dictslot {
	WordNum tabl;
	WordNum link;
	HashVal hash;
	struct dictstat {
		unsigned node;
		unsigned hits;
		} stats;
	STRING string;
	};
typedef struct {
    DictSize size;
    DictSize msize;
    struct dictslot *entry;
} DICTIONARY;

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
    // HashVal nhash;
    struct node *ptr;
	};
typedef struct node {
    UsageCnt usage; /* sum of children's count */
    UsageCnt count; /* my count */
    WordNum symbol;
    ChildIndex msize;
    ChildIndex branch;
    struct treeslot *children;
} TREE;

typedef struct {
    Count order;
    TREE *forward;
    TREE *backward;
    TREE **context;
    DICTIONARY *dictionary;
} MODEL;

struct memstat {
	unsigned alloc;
	unsigned free;
	unsigned alzheimer;
	unsigned symdel;
	unsigned treedel;
	} memstats = {0,0,0,0,0} ;

typedef enum { UNKNOWN, QUIT, EXIT, SAVE, DELAY, HELP, SPEECH, VOICELIST, VOICE, BRAIN, QUIET} COMMAND_WORDS;

typedef struct {
    STRING word;
    char *helpstring;
    COMMAND_WORDS command;
} COMMAND;

/*===========================================================================*/

#define MY_NAME "MegaHAL"
#define MY_NAME "PlasBot"
static int glob_width = 75;
static int glob_order = 7; // 5
static int glob_timeout = DEFAULT_TIMEOUT;

static bool typing_delay = FALSE;
static bool noprompt = FALSE;
static bool speech = FALSE;
static bool nowrap = FALSE;
static bool nobanner = FALSE;
static bool quiet = FALSE;

static char *errorfilename = "megahal.log";
static char *statusfilename = "megahal.txt";
static DICTIONARY *glob_words = NULL;
static DICTIONARY *glob_greets = NULL;
static MODEL *glob_model = NULL;

static FILE *errorfp;
static FILE *statusfp;

static DICTIONARY *glob_ban = NULL;
static DICTIONARY *glob_aux = NULL;
static DICTIONARY *glob_grt = NULL;
static SWAP *glob_swp = NULL;

static bool used_key;
static char *directory = NULL;
static char *last_directory = NULL;
static unsigned long node_count=0;
static unsigned long word_count=0;

static COMMAND command[] = {
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
#define COMMAND_SIZE (sizeof(command)/sizeof(command[0]))

#ifdef AMIGA
struct Locale *_AmigaLocale;
#endif

#ifdef __mac_os
Boolean gSpeechExists = false;
SpeechChannel gSpeechChannel = nil;
#endif

STATIC void add_aux(MODEL *model, DICTIONARY *keys, STRING word);
STATIC void add_key(MODEL *model, DICTIONARY *keys, STRING word);
STATIC int resize_tree(TREE *tree, unsigned newsize);

STATIC void add_swap(SWAP *list, char *from, char *to);
STATIC TREE *add_symbol(TREE *, WordNum);
STATIC WordNum add_word_dodup(DICTIONARY *dict, STRING word);
STATIC WordNum add_word_nofuss(DICTIONARY *dict, STRING word);
STATIC WordNum babble(MODEL *model, DICTIONARY *keys, DICTIONARY *words);
STATIC bool boundary(char *string, size_t position);

STATIC void capitalize(char *);
STATIC void changevoice(DICTIONARY *, unsigned int);
STATIC void change_personality(DICTIONARY *, unsigned int, MODEL **);
STATIC void delay(char *);
STATIC void die(int);
STATIC bool dissimilar(DICTIONARY *, DICTIONARY *);
STATIC void error(char *, char *, ...);
STATIC double evaluate_reply(MODEL *model, DICTIONARY *keys, DICTIONARY *sentence);
STATIC COMMAND_WORDS execute_command(DICTIONARY *, unsigned int *position);
STATIC void exithal(void);
STATIC TREE *find_symbol(TREE *node, WordNum symbol);
STATIC TREE *find_symbol_add(TREE *, WordNum);

STATIC WordNum find_word(DICTIONARY *, STRING);
STATIC char *generate_reply(MODEL *, DICTIONARY *);
STATIC void help(void);
STATIC void ignore(int);
STATIC bool initialize_error(char *);
#ifdef __mac_os
STATIC bool initialize_speech(void);
#endif
STATIC bool initialize_status(char *);
STATIC void learn_from_input(MODEL *, DICTIONARY *);
STATIC void listvoices(void);
STATIC void make_greeting(DICTIONARY *);
STATIC void make_words(char *, DICTIONARY *);
STATIC DICTIONARY *new_dictionary(void);

STATIC char *read_input(char * prompt);
STATIC void save_model(char *, MODEL *);
#ifdef __mac_os
STATIC char *strdup(const char *);
#endif
STATIC void upper(char *);
STATIC void write_input(char *);
STATIC void write_output(char *);
#if defined(DOS) || defined(__mac_os)
STATIC void usleep(int);
#endif

STATIC char *format_output(char *);
STATIC void free_dictionary(DICTIONARY *dict);
STATIC void free_model(MODEL *);
STATIC void free_tree(TREE *);
STATIC void free_word(STRING word);
STATIC void free_words(DICTIONARY *words);

STATIC void initialize_context(MODEL *);
STATIC void initialize_dictionary(DICTIONARY *);
STATIC DICTIONARY *read_dictionary(char *filename);
STATIC SWAP *initialize_swap(char *);
STATIC void load_dictionary(FILE *, DICTIONARY *);
STATIC bool load_model(char *, MODEL *);
STATIC void load_personality(MODEL **);
STATIC void load_tree(FILE *, TREE *);
STATIC void load_word(FILE *, DICTIONARY *);
STATIC DICTIONARY *make_keywords(MODEL *, DICTIONARY *);
STATIC char *make_output(DICTIONARY *);
STATIC MODEL *new_model(int);
STATIC TREE *new_node(void);
STATIC SWAP *new_swap(void);
STATIC STRING new_string(char *str, size_t len);
STATIC bool print_header(FILE *);
bool progress(char *message, unsigned long done, unsigned long todo);
STATIC DICTIONARY *one_reply(MODEL *, DICTIONARY *);
STATIC void save_dictionary(FILE *, DICTIONARY *);
STATIC void save_tree(FILE *, TREE *);
STATIC void save_word(FILE *, STRING);
STATIC WordNum seed(MODEL *, DICTIONARY *);

STATIC void show_dictionary(DICTIONARY *);
STATIC void speak(char *);
STATIC bool status(char *, ...);
STATIC void train(MODEL *, char *);
STATIC void typein(char);
STATIC void update_context(MODEL *, WordNum symbol);
STATIC void update_model(MODEL *model, WordNum symbol);
STATIC bool warn(char *, char *, ...);
STATIC int wordcmp(STRING one, STRING two);
STATIC bool word_exists(DICTIONARY *, STRING);
STATIC unsigned int urnd(unsigned int range);

STATIC HashVal hash_mem(void *dat, size_t len);
STATIC WordNum * dict_hnd(DICTIONARY *dict, STRING word);
STATIC WordNum * dict_hnd_tail (DICTIONARY *dict, STRING word);
STATIC HashVal hash_word(STRING word);
STATIC int double_dictionary(DICTIONARY *dict);
STATIC int resize_dictionary(DICTIONARY *dict, unsigned newsize);
STATIC void format_dictionary(struct dictslot * slots, unsigned size);
STATIC unsigned long set_dict_count(MODEL *model);
STATIC unsigned long dict_inc_refa_node(DICTIONARY *dict, TREE *node, WordNum symbol);
STATIC unsigned long dict_inc_ref_recurse(DICTIONARY *dict, TREE *node);
STATIC unsigned long dict_inc_ref(DICTIONARY *dict, WordNum symbol, unsigned nnode, unsigned nhits);

STATIC void del_symbol_do_free(TREE *tree, WordNum symbol);
STATIC void del_word_dofree(DICTIONARY *dict, STRING word);
void free_tree_recursively(TREE *tree);
STATIC void symbol_russian_alzheimer(TREE *tree);
STATIC void symbol_russian_alzheimer_recurse(TREE *tree, unsigned the_dice);

STATIC ChildIndex *node_hnd(TREE *node, WordNum symbol);
STATIC void format_treeslots(struct treeslot *slots , unsigned size);
STATIC void show_memstat(char *msg);

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
    directory = dir;
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

    glob_words = new_dictionary();
    glob_greets = new_dictionary();
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
	write_input(input);  /* log input if so desired */

    // upper(input);

    make_words(input, glob_words);

    learn_from_input(glob_model, glob_words);
    output = generate_reply(glob_model, glob_words);
    // capitalize(output);
    return output;
}

/*
   megahal_learn_no_reply --

   Take string as input, update model but don't generate reply.

  */

void megahal_learn_no_reply(char *input, int log)
{
    if (log != 0)
	write_input(input);  /* log input if so desired */

    // upper(input);

    make_words(input, glob_words);

    learn_from_input(glob_model, glob_words);
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
	write_output(output);
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

    make_words(input,glob_words);
    switch(execute_command(glob_words, &position)) {
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
	changevoice(glob_words, position);
	return 1;
    case BRAIN:
	change_personality(glob_words, position, &glob_model);
	make_greeting(glob_greets);
	output = generate_reply(glob_model, glob_greets);
	write_output(output);
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
STATIC COMMAND_WORDS execute_command(DICTIONARY *words, unsigned int *position)
{
    unsigned int i;
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
    for(i = 0; i < words->size-1; ++i) {
	/*
	 *		The command prefix was found.
	 */
	if (words->entry[i].string.word[words->entry[i].string.length - 1] != '#') continue;
	    /*
	     *		Look for a command word.
	     */
	for(j = 0; j < COMMAND_SIZE; ++j)
	if (!strncasecmp(command[j].word.word, words->entry[i + 1].string.word, words->entry[i + 1].string.length) ) {
	    *position = i + 1;
	    return command[j].command;
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
	// This will end execution on two consecutive empty lines
	// if (seen_eol && !length) return NULL;
	if (length +2 >= size) {
		input = realloc(input, size? 2*size: 16);
		if (input) size = size ? 2 * size : 16;
		}
	if (input == NULL) {
	    error("read_input", "Unable to re-allocate the input string");
	    return NULL;
	}

	/*
	 *		Add the character just read to the input string.
	 */
	input[length++] = c;
	input[length] ='\0';
    }

    while(length > 0 && isspace(input[length-1])) --length;
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

    if (filename == NULL) return TRUE;

    errorfp = fopen(filename, "a");
    if (errorfp == NULL) {
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
status ("Memstat %s: {alloc=%u free=%u alzheimer=%u symdel=%u treedel=%u}\n"
	, msg, memstats.alloc , memstats.free
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
    if (filename == NULL) return FALSE;
    statusfp = fopen(filename, "a");
    if (statusfp == NULL) {
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
STATIC bool print_header(FILE *file)
{
    time_t clock;
    char timestamp[1024];
    struct tm *local;

    clock = time(NULL);
    local = localtime(&clock);
    strftime(timestamp, 1024, "Start at: [%Y/%m/%d %H:%M:%S]\n", local);

    fprintf(file, "MegaHALv8\n");
    fprintf(file, "Copyright (C) 1998 Jason Hutchens\n%s", timestamp);
    fflush(file);

    return TRUE;
}

/*---------------------------------------------------------------------------*/

/*
 *    Function:   Write_Output
 *
 *    Purpose:    Display the output string.
 */
STATIC void write_output(char *output)
{
    char *formatted;
    char *bit;

    // capitalize(output);
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
STATIC void capitalize(char *string)
{
    size_t len, ii;
    unsigned char *ucp = (unsigned char *) string;
    bool start = TRUE;

    len = strlen(string);
    for(ii = 0; ii < len; ii++) {
	if (isalpha(ucp[ii])) {
	    if (start == TRUE) ucp[ii] = toupper(ucp[ii]);
	    else ucp[ii] = tolower(ucp[ii]);
	    start = FALSE;
	}
	if (ii > 2 && strchr("!.?", ucp[ii-1]) != NULL && isspace(ucp[ii]))
	    start = TRUE;
    }
}

/*---------------------------------------------------------------------------*/

/*
 *		Function:	Upper
 *
 *		Purpose:		Convert a string to its uppercase representation.
 */
STATIC void upper(char *string)
{
    size_t len, ii;
    unsigned char *ucp = (unsigned char *) string;

    len = strlen(string);
    for(ii = 0; ii < len; ii++) ucp[ii] = toupper(ucp[ii]);
}

/*---------------------------------------------------------------------------*/

/*
 *    Function:   Write_Input
 *
 *    Purpose:    Log the user's input
 */
STATIC void write_input(char *input)
{
    char *formatted;
    char *bit;

    glob_width = 64;
    formatted = format_output(input);

    bit = strtok(formatted, "\n");
    if (bit == NULL) (void)status("User:    %s\n", formatted);
    while(bit != NULL) {
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
    if (formatted == NULL) {
	error("format_output", "Unable to re-allocate formatted");
	return "ERROR";
    }

    l = 0;
    j = 0;
    for(i = 0; i < len ; ++i) {
	if (l == 0 && isspace(output[i])) continue;
	formatted[j++] = output[i];
	++l;
	if (nowrap) continue;
	if (l < glob_width) continue;
	for(c = j-1; c > 0; --c)
	    if (formatted[c] == ' ') {
		formatted[c] = '\n';
		l = j-c-1;
		break;
	    }
    }
    if (j > 0 && formatted[j-1] != '\n') {
	formatted[j] = '\n';
	++j;
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
STATIC WordNum add_word_nofuss(DICTIONARY *dict, STRING word)
{
WordNum *wp;

if (!dict) return 0; /* WP: should be WORD_NIL */
if (!word.length) return 0; /* WP: should be WORD_NIL */

if (dict->size >= dict->msize && double_dictionary(dict)) return WORD_NIL;
wp = &dict->entry[ dict->size].tabl ;

*wp = dict->size++;
dict->entry[*wp].link = WORD_NIL;
dict->entry[*wp].string = word;
/* fake the hash value.
 * setting it to the identity transform will cause X to be put into slot X.
 * Degenerate chains, but consistent, even on doubling.
 */
dict->entry[*wp].hash = *wp;

return *wp;

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
STATIC WordNum add_word_dodup(DICTIONARY *dict, STRING word)
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

STATIC void del_word_dofree(DICTIONARY *dict, STRING word)
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
dict->entry[top].string.word = NULL;
dict->entry[top].string.length = 0;
dict->entry[top].hash = 0;
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
STATIC WordNum find_word(DICTIONARY *dict, STRING string)
{
WordNum *np;

if (!dict) return 0; /* WP: should be WORD_NIL */
np = dict_hnd(dict, string);

if (!np || *np == WORD_NIL) return 0; /* WP: should be WORD_NIL */
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
    int i;
    size_t siz;

    siz = MIN(one.length,two.length);

    // i = strncasecmp(one.word, two.word, siz);
    i = memcmp(one.word, two.word, siz);
    if (i) return i;

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
STATIC void free_dictionary(DICTIONARY *dict)
{
    if (dict == NULL) return;
    dict->size = 0;
    resize_dictionary(dict, DICT_SIZE_INITIAL);
}

/*---------------------------------------------------------------------------*/

STATIC void free_model(MODEL *model)
{
    if (model == NULL) return;
    free_tree(model->forward);
    free_tree(model->backward);
    free(model->context);
    free_dictionary(model->dictionary);
    free(model->dictionary);

    free(model);
}

/*---------------------------------------------------------------------------*/

STATIC void free_tree(TREE *tree)
{
    static int level = 0;
    unsigned int i;

    if (tree == NULL) return;

    if (tree->children != NULL) {
	if (level == 0) progress("Freeing tree", 0, 1);
	for(i = 0; i < tree->branch; ++i) {
	    ++level;
	    free_tree(tree->children[i].ptr);
	    --level;
	    if (level == 0) progress(NULL, i, tree->branch);
	}
	if (level == 0) progress(NULL, 1, 1);
	free(tree->children);
    }
    free(tree);
    memstats.free += 1;
}

/*---------------------------------------------------------------------------*/

/*
 *		Function:	Initialize_Dictionary
 *
 *		Purpose:		Add dummy words to the dictionary.
 */
STATIC void initialize_dictionary(DICTIONARY *dict)
{
    STRING word ={ 7, "<ERROR>" };
    STRING end ={ 5, "<FIN>" };

    add_word_dodup(dict, word);
    add_word_dodup(dict, end);
}

STATIC unsigned long set_dict_count(MODEL *model)
{
unsigned ret=0;

if (!model) return 0;
ret += dict_inc_ref_recurse(model->dictionary, model->forward);
ret += dict_inc_ref_recurse(model->dictionary, model->backward);

return ret;
}

STATIC unsigned long dict_inc_ref_recurse(DICTIONARY *dict, TREE *node)
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

STATIC unsigned long dict_inc_ref_node(DICTIONARY *dict, TREE *node, WordNum symbol)
{

if (!dict || !node || symbol >= dict->size ) return 0;

if (node->count <= 1) return dict_inc_ref(dict, symbol, 1, 1);
else return dict_inc_ref(dict, symbol, 0, node->count);

}

STATIC unsigned long dict_inc_ref(DICTIONARY *dict, WordNum symbol, unsigned nnode, unsigned nhits)
{

if (!dict || symbol >= dict->size ) return 0;
dict->entry[ symbol ].stats.node += nnode;
dict->entry[ symbol ].stats.hits += nhits;

return dict->entry[ symbol ].stats.hits;
}
/*---------------------------------------------------------------------------*/

/*
 *		Function:	New_Dictionary
 *
 *		Purpose:		Allocate room for a new dictionary.
 */

STATIC DICTIONARY *new_dictionary(void)
{
    DICTIONARY *dict = NULL;

    dict = malloc(sizeof *dict);
    if (dict == NULL) {
	error("new_dictionary", "Unable to allocate dictionary.");
	return NULL;
    }

    dict->entry = malloc (DICT_SIZE_INITIAL * sizeof *dict->entry);
    if (!dict->entry) {
	error("new_dictionary", "Unable to allocate dictionary->slots.");
	return NULL;
	}
    dict->msize = DICT_SIZE_INITIAL;
    dict->size = 0;
    format_dictionary(dict->entry, dict->msize);

    return dict;
}

STATIC void format_dictionary(struct dictslot * slots, unsigned size)
{
    unsigned ii;

    for (ii = 0; ii < size; ii++) {
	slots[ii].tabl = WORD_NIL;
	slots[ii].link = WORD_NIL;
	slots[ii].hash = 0xe;
	slots[ii].stats.node = 0;
	slots[ii].stats.hits = 0;
	slots[ii].string.length = 0;
	slots[ii].string.word = NULL;
	}

}
/*---------------------------------------------------------------------------*/

/*
 *		Function:	Save_Dictionary
 *
 *		Purpose:		Save a dictionary to the specified file.
 */
STATIC void save_dictionary(FILE *file, DICTIONARY *dict)
{
    unsigned int i;

    fwrite(&dict->size, sizeof dict->size, 1, file);
    progress("Saving dictionary", 0, 1);
    for(i = 0; i < dict->size; ++i) {
	save_word(file, dict->entry[i].string );
	progress(NULL, i, dict->size);
    }
    progress(NULL, 1, 1);
    word_count = i;
}

/*---------------------------------------------------------------------------*/

/*
 *		Function:	Load_Dictionary
 *
 *		Purpose:		Load a dictionary from the specified file.
 */
STATIC void load_dictionary(FILE *file, DICTIONARY *dict)
{
    unsigned int i;
    unsigned int size;

    fread(&size, sizeof size, 1, file);
    fprintf(stderr, "Size=%d\n", size);
    progress("Loading dictionary", 0, 1);
    for(i = 0; i < size; ++i) {
	load_word(file, dict);
	progress(NULL, i, size);
    }
    progress(NULL, 1, 1);
    word_count = size;
}

/*---------------------------------------------------------------------------*/

/*
 *		Function:	Save_Word
 *
 *		Purpose:		Save a dictionary word to a file.
 */
STATIC void save_word(FILE *file, STRING word)
{

    fwrite(&word.length, sizeof word.length, 1, file);
    fwrite(&word.word[0], word.length, 1, file);
}

/*---------------------------------------------------------------------------*/

/*
 *		Function:	Load_Word
 *
 *		Purpose:		Load a dictionary word from a file.
 */
STATIC void load_word(FILE *file, DICTIONARY *dict)
{
    STRING word;

    fread(&word.length, sizeof word.length, 1, file);
    word.word = malloc(word.length);
    if (word.word == NULL) {
	error("load_word", "Unable to allocate word");
	return;
    }
    fread(&word.word[0], word.length, 1, file);
    add_word_dodup(dict, word);
    free(word.word);
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
    if (node == NULL) {
	error("new_node", "Unable to allocate the node.");
	return NULL;
    }

    /*
     *		Initialise the contents of the node
     */
    node->symbol = 0;
    node->usage = 0;
    node->count = 0;
    node->msize = 0;
    node->branch = 0;
    node->children = NULL;
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
    if (model == NULL) {
	error("new_model", "Unable to allocate model.");
	goto fail;
    }

    model->order = order;
    model->forward = new_node();
    model->backward = new_node();
    model->context = malloc( (order+2) *sizeof *model->context);
    if (model->context == NULL) {
	error("new_model", "Unable to allocate context array.");
	goto fail;
    }
    initialize_context(model);
    model->dictionary = new_dictionary();
    initialize_dictionary(model->dictionary);

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
    unsigned int i;

    /*
     *		Update all of the models in the current context with the specified
     *		symbol.
     */
    for(i = model->order+1; i > 0; --i) {
	if (model->context[i-1] == NULL) continue;
	model->context[i] = add_symbol(model->context[i-1], symbol);
	dict_inc_ref_node(model->dictionary, model->context[i], symbol);
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
    unsigned int i;

    for(i = model->order+1; i > 0; --i)
	if (model->context[i-1] != NULL)
	    model->context[i] = find_symbol(model->context[i-1], symbol);
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

    /*
     *		Search for the symbol in the subtree of the tree node.
     */
    node = find_symbol_add(tree, symbol);
    if (!node) return NULL;

    /*
     *		Increment the symbol counts
     *		Stop incrementing when wraparound detected.
     */
    node->count += 1; tree->usage += 1;
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

STATIC void symbol_russian_alzheimer(TREE *tree)
{
unsigned the_dice;

if (!tree) return;

the_dice = urnd(tree->usage);

#if WANT_DUMP_ALZHEIMER_PROGRESS
fprintf(stderr, "symbol_russian_alzheimer() dice=%u\n", the_dice);
#endif

symbol_russian_alzheimer_recurse(tree, the_dice);
}

STATIC void symbol_russian_alzheimer_recurse(TREE *tree, unsigned dice)
{
unsigned slot;
if (!tree) return;

if (! tree->branch) {
#if WANT_DUMP_ALZHEIMER_PROGRESS
	fprintf(stderr, "symbol_russian_alzheimer_recurse(dice=%u) Terminal node (symbol=%u usage=%u count=%u)\n"
	, dice, tree->symbol, tree->usage, tree->count);
#endif
	return;
	}

/* This is the same kind of sampling as used in babble()
 * Starting with a random slot is not strictly needed
 * , given a good random value for the_dice 
 */
slot = urnd(tree->branch);

#if WANT_DUMP_ALZHEIMER_PROGRESS
fprintf(stderr, "symbol_russian_alzheimer_recurse(dice=%u) slot=%u\n", dice, slot);
#endif

while (dice >= tree->children[slot].ptr->count) {
	dice -= tree->children[slot].ptr->count;
	slot = (slot+1) % tree->branch;
	}

if (!dice || (tree->children[slot].ptr && tree->children[slot].ptr->branch)) {
	unsigned symbol;
	symbol = tree->children[slot].ptr ? tree->children[slot].ptr->symbol : 0;

#if WANT_DUMP_ALZHEIMER_PROGRESS
	fprintf(stderr, "symbol_russian_alzheimer_recurse(%u) exact match or terminal child; slot=%u symbol=%u\n"
		, dice, slot, symbol);
#endif
	memstats.alzheimer += 1;
	del_symbol_do_free(tree, symbol) ;
	}
else	{
	symbol_russian_alzheimer_recurse(tree->children[slot].ptr, dice);
	}
return;
}

STATIC void del_symbol_do_free(TREE *tree, WordNum symbol)
{
    ChildIndex *ip, this,top;
    TREE *child = NULL;

    /*
     *		Search for the symbol in the subtree of the tree node.
     */
    ip = node_hnd(tree, symbol);
    if (!ip || *ip == CHILD_NIL) {
	warn("del_symbol_do_free", "Symbol %u not found\n", symbol);
	return ;
	}
	/* cut the node out of the hash chain; save the child. */
    this = *ip;
    *ip = tree->children[this].link;
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
	// tree->children[this].nhash = tree->children[top].nhash;
	
	tree->children[top].ptr = NULL;
	// tree->children[top].nhash = 0;
	/* relink into the hash chain */
    	ip = node_hnd(tree, tree->children[this].ptr->symbol);
	*ip = this;
	}

	/* now this child needs to be abolished ... */
kill:
    free_tree_recursively(child);
    if (tree->branch < tree->msize/2) {
	fprintf(stderr, "Tree(%u/%u) could be shrunk: %u/%u\n"
		, tree->count, tree->usage, tree->branch, tree->msize);
		}
}

void free_tree_recursively(TREE *tree)
{
unsigned index;

if (!tree) return;
for (index= tree->branch; index--;	) {
	free_tree_recursively( tree->children[index] .ptr );
	}
free(tree->children);
free(tree);
memstats.treedel += 1;
}

/*---------------------------------------------------------------------------*/

/*
 *		Function:	Find_Symbol
 *
 *		Purpose:		Return a pointer to the child node, if one exists, which
 *						contains the specified symbol.
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
 *						a new node for this symbol is allocated and added to the
 *						tree.
 */
STATIC TREE *find_symbol_add(TREE *node, WordNum symbol)
{
ChildIndex *ip;

ip = node_hnd(node, symbol);
if (!ip) return NULL;

if (*ip == CHILD_NIL) { /* not found: create one */
    *ip = node->branch++;
     // node->children[ *ip ].nhash = symbol;
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
// fprintf(stderr, "resize_tree(%u/%u) %u\n", tree->branch,  tree->msize, newsize);
    old = tree->children;
    if (!newsize) newsize = NODE_SIZE_INITIAL;
    while (newsize < tree->branch) newsize += 2;

    tree->children = malloc(newsize * sizeof *tree->children );
    if (tree->children == NULL) {
	error("resize_tree", "Unable to reallocate subtree.");
        tree->children = old;
	return -1;
    }

    tree->msize = newsize;
    format_treeslots(tree->children, tree->msize);

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
	// slot = old[item].nhash % tree->msize;
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
	// tree->children[item].nhash = old[item].nhash;
	tree->children[item].ptr = old[item].ptr;
	}
    free (old);
    return 0; /* success */
}

STATIC void format_treeslots(struct treeslot  *slots , unsigned size)
{
    unsigned ui;

    for (ui = 0; ui < size; ui++) {
	slots[ui].tabl = CHILD_NIL;
	slots[ui].link = CHILD_NIL;
	// slots[ui].nhash = ui;
	slots[ui].ptr = NULL;
	}
}


STATIC ChildIndex *node_hnd(TREE *node, WordNum symbol)
{
ChildIndex *ip;
unsigned slot;

if (node->branch >= node->msize && resize_tree(node, node->branch+node->branch/2 )) return NULL;

slot = symbol % node->msize;
for (ip = &node->children[ slot ].tabl; *ip != CHILD_NIL; ip = &node->children[ *ip ].link ) {
	// if (symbol != node->children[ *ip ].nhash) continue;
	if (! node->children[ *ip ].ptr) continue;
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
    unsigned int i;

    for(i = 0; i <= model->order; ++i) model->context[i] = NULL;

}

/*---------------------------------------------------------------------------*/

/*
 *		Function:	Learn
 *
 *		Purpose:		Learn from the user's input.
 */
STATIC void learn_from_input(MODEL *model, DICTIONARY *words)
{
    unsigned int i;
    int j;
    WordNum symbol;

    /*
     *		We only learn from inputs which are long enough
     */
    if (words->size <= model->order) return;

    /*
     *		Train the model in the forwards direction.  Start by initializing
     *		the context of the model.
     */
    initialize_context(model);
    model->context[0] = model->forward;
    for(i = 0; i < words->size; ++i) {
	/*
	 *		Add the symbol to the model's dictionary if necessary, and then
	 *		update the forward model accordingly.
	 */
	symbol = add_word_dodup(model->dictionary, words->entry[i].string );
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
    for(j = words->size; j-- > 0; ) {
	/*
	 *		Find the symbol in the model's dictionary, and then update
	 *		the backward model accordingly.
	 */
	symbol = find_word(model->dictionary, words->entry[j].string );
	update_model(model, symbol);
    }
    /*
     *		Add the sentence-terminating symbol.
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
    FILE *file;
    DICTIONARY *words = NULL;
    int length;
    char buffer[4*1024];

    if (filename == NULL) return;

    file = fopen(filename, "r");
    if (file == NULL) {
	printf("Unable to find the personality %s\n", filename);
	return;
    }

    fseek(file, 0, 2);
    length = ftell(file);
    rewind(file);

    words = new_dictionary();

    progress("Training from file", 0, 1);
    while( fgets(buffer, sizeof buffer, file) ) {
	if (buffer[0] == '#') continue;

	buffer[strlen(buffer)-1] ='\0';

	// upper(buffer);
	make_words(buffer, words);
	learn_from_input(model, words);

	progress(NULL, ftell(file), length);

    }
    progress(NULL, 1, 1);

    free_dictionary(words);
    fclose(file);
}

/*---------------------------------------------------------------------------*/

/*
 *		Function:	Show_Dictionary
 *
 *		Purpose:		Display the dictionary for training purposes.
 */
void show_dictionary(DICTIONARY *dict)
{
    unsigned int i;
    FILE *file;

    file = fopen("megahal.dic", "w");
    if (file == NULL) {
	warn("show_dictionary", "Unable to open file");
	return;
    }

    for(i = 0; i < dict->size; ++i) {
	    fprintf(file, "%lu %lu %*.*s\n"
		, (unsigned long) dict->entry[i].stats.node, (unsigned long) dict->entry[i].stats.hits
		, (int) dict->entry[i].string.length, (int) dict->entry[i].string.length, dict->entry[i].string.word );
    }

    fclose(file);
}

/*---------------------------------------------------------------------------*/

/*
 *		Function:	Save_Model
 *
 *		Purpose:		Save the current state to a MegaHAL brain file.
 */
STATIC void save_model(char *modelname, MODEL *model)
{
    FILE *file;
    static char *filename = NULL;

    filename = realloc(filename, strlen(directory)+strlen(SEP)+12);
    if (filename == NULL) error("save_model","Unable to allocate filename");

    show_dictionary(model->dictionary);
    if (filename == NULL) return;

    sprintf(filename, "%s%smegahal.brn", directory, SEP);
    file = fopen(filename, "wb");
    if (file == NULL) {
	warn("save_model", "Unable to open file `%s'", filename);
	return;
    }
    node_count = 0;
    word_count = 0;
    fwrite(COOKIE, sizeof(char), strlen(COOKIE), file);
    fwrite(&model->order, sizeof model->order, 1, file);
    save_tree(file, model->forward);
    save_tree(file, model->backward);
    save_dictionary(file, model->dictionary);
    status("Saved %lu nodes, %u words.\n", node_count,word_count);

    fclose(file);
}

/*---------------------------------------------------------------------------*/

/*
 *		Function:	Save_Tree
 *
 *		Purpose:		Save a tree structure to the specified file.
 */
STATIC void save_tree(FILE *file, TREE *node)
{
    static int level = 0;
    unsigned int i;

    fwrite(&node->symbol, sizeof node->symbol, 1, file);
    fwrite(&node->usage, sizeof node->usage, 1, file);
    fwrite(&node->count, sizeof node->count, 1, file);
    fwrite(&node->branch, sizeof node->branch, 1, file);
    node_count++;
    if (level == 0) progress("Saving tree", 0, 1);
    for(i = 0; i < node->branch; ++i) {
	++level;
	save_tree(file, node->children[i].ptr );
	--level;
	if (level == 0) progress(NULL, i, node->branch);
    }
    if (level == 0) progress(NULL, 1, 1);
}

/*---------------------------------------------------------------------------*/

/*
 *		Function:	Load_Tree
 *
 *		Purpose:		Load a tree structure from the specified file.
 */
STATIC void load_tree(FILE *file, TREE *node)
{
    static int level = 0;
    unsigned int ui;
    unsigned int symbol;
    ChildIndex *ip;

    fread(&node->symbol, sizeof node->symbol, 1, file);
    fread(&node->usage, sizeof node->usage, 1, file);
    fread(&node->count, sizeof node->count, 1, file);
    fread(&node->branch, sizeof node->branch, 1, file);
    node_count++;
    if (node->branch == 0) return;

    resize_tree(node , 1+ node->branch );
    if (node->children == NULL) {
	error("load_tree", "Unable to allocate subtree");
	return;
    }

    if (level == 0) progress("Loading tree", 0, 1);
    for(ui = 0; ui < node->branch; ++ui) {
	node->children[ui].ptr = new_node();
	++level;
	load_tree(file, node->children[ui].ptr);
	--level;

	symbol = node->children[ui].ptr ? node->children[ui].ptr->symbol: ui;
	ip = node_hnd(node, symbol );
	if (ip) *ip = ui;
	// node->children[ui].nhash = symbol;
	if (level == 0) progress(NULL, ui, node->branch);
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
    FILE *file;
    char cookie[16];
    unsigned refcount;


    if (filename == NULL) return FALSE;

    file = fopen(filename, "rb");

    if (file == NULL) {
	warn("load_model", "Unable to open file `%s'", filename);
	return FALSE;
    }


    fread(cookie, sizeof(char), strlen(COOKIE), file);
    if (memcmp(cookie, COOKIE, strlen(COOKIE)) ) {
	warn("load_model", "File `%s' is not a MegaHAL brain", filename);
	goto fail;
    }
    node_count = 0;
    word_count = 0;
    fread(&model->order, sizeof model->order, 1, file);
    load_tree(file, model->forward);
    load_tree(file, model->backward);
    load_dictionary(file, model->dictionary);
    refcount = set_dict_count(model);
    status("Loaded %lu nodes, %u words. Total refcount=%u\n", node_count,word_count, refcount);

    fclose(file);
    show_dictionary(model->dictionary);
    return TRUE;
fail:
    fclose(file);

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
STATIC void make_words(char *input, DICTIONARY *words)
{
    size_t offset = 0;
    size_t len = strlen(input);
    STRING word ; 
    static STRING period = {1, "." }  ; 

    /*
     *		Clear the entries in the dictionary
     */
    free_dictionary(words);

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
			warn( "String too long (%u) at %s\n", (unsigned) offset, input);
			offset = 255;
			}
		word.length = offset;
		word.word = input;
	    /*
	     *		Add the word to the dictionary
	     */
	add_word_nofuss(words, word);

	    if (offset == len) break;
	    input += offset;
	    len -= offset;
	    offset = 0;
	} else {
	    ++offset;
	}
    }

    /*
     *		If the last word isn't punctuation, then replace it with a
     *		full-stop character.
     */
    if (isalnum(words->entry[words->size-1].string.word[0])) {
		add_word_nofuss(words, period);
    }
    else if (!strchr("!.?", words->entry[words->size-1].string.word[ words->entry[words->size-1].string.length-1] )) {
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
STATIC bool boundary(char *string, size_t position)
{
    unsigned char *ucp = (unsigned char *) string;
    if (position == 0) return FALSE;

    if (ucp[position] == '\0' ) return TRUE;

    if (
	ucp[position] == '\''
	&& isalpha(ucp[position-1])
	&& isalpha(ucp[position+1])
	)
	return FALSE;

    if (
	position > 1
	&& ucp[position-1] == '\''
	&& isalpha(ucp[position-2])
	&& isalpha(ucp[position]) 
	)
	return FALSE;

    if (
	isalpha(ucp[position])
	&& !isalpha(ucp[position-1])
	)
	return TRUE;

    if (
	!isalpha(ucp[position])
	&& isalpha(ucp[position-1])
	)
	return TRUE;

    if (isdigit(ucp[position]) != isdigit(ucp[position-1]))
	return TRUE;

    return FALSE;
}

/*---------------------------------------------------------------------------*/
/*
 *		Function:	Make_Greeting
 *
 *		Purpose:		Put some special words into the dictionary so that the
 *						program will respond as if to a new judge.
 */
STATIC void make_greeting(DICTIONARY *words)
{
    unsigned int i;

    for(i = 0; i < words->size; ++i) free(words->entry[i].string.word);
    free_dictionary(words);
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
STATIC char *generate_reply(MODEL *model, DICTIONARY *words)
{
    static char *output_none = "Geert! doe er wat aan!" ;
    static DICTIONARY *dummy = NULL;
    DICTIONARY *replywords;
    DICTIONARY *keywords;
    double surprise, max_surprise;
    char *output;
    unsigned count;
    int basetime;

#if ALZHEIMER_FACTOR
    count = urnd(ALZHEIMER_FACTOR);
    if (count == ALZHEIMER_FACTOR/2) {
        initialize_context(model);
        symbol_russian_alzheimer(model->forward);
        symbol_russian_alzheimer(model->backward);
	}
#endif
    /*
     *		Create an array of keywords from the words in the user's input
     */
    keywords = make_keywords(model, words);

    /*
     *		Make sure some sort of reply exists
     */
    if (!output_none ) {
	output_none = malloc(40);
	// if (output_none) strcpy(output_none, "I don't know enough to answer you yet!");
    }
    output = output_none;
    if (dummy == NULL) dummy = new_dictionary();
    replywords = one_reply(model, dummy);
    if (dissimilar(words, replywords)) output = make_output(replywords);

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
	if (replywords->size < MIN_PAREL_SIZE) continue;
	surprise = evaluate_reply(model, keywords, replywords);
	++count;
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
STATIC bool dissimilar(DICTIONARY *dic1, DICTIONARY *dic2)
{
    unsigned int i;

    if (dic1->size != dic2->size) return TRUE;
    for(i = 0; i < dic1->size; ++i)
	if (wordcmp(dic1->entry[i].string , dic2->entry[i].string ) ) return TRUE;
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
STATIC DICTIONARY *make_keywords(MODEL *model, DICTIONARY *words)
{
    static DICTIONARY *keys = NULL;
    unsigned int i;
    unsigned int j;
    unsigned swapped;

    if (keys == NULL) keys = new_dictionary();
#if (!KEYWORD_DICT_SIZE )
    for(i = 0; i < keys->size; ++i) free(keys->entry[i].string.word);
    // keys->size = 0;
    free_dictionary(keys);
#elif 0
    for(i = 0; i < keys->size; ++i) {
	keys->entry[i].stats.node += 1;
	if (urnd(keys->size) >= KEYWORD_DICT_SIZE ) continue;
	/* if (!keys->entry[i].stats.hits) */
		del_word_dofree(keys, keys->entry[i].string );
	}
#else
    for (swapped = 0 ;keys->size > swapped+KEYWORD_DICT_SIZE; ) {
	i = urnd(keys->size);
	j = find_word(words, keys->entry[i].string );
	if ( j && j != WORD_NIL ) {
		keys->entry[i].stats.node++;
		swapped++;
		continue;
		}
	del_word_dofree(keys, keys->entry[i].string );
	}
#endif

    for(i = 0; i < words->size; ++i) {
	/*
	 *		Find the symbol ID of the word.  If it doesn't exist in
	 *		the model, or if it begins with a non-alphanumeric
	 *		character, or if it is in the exclusion array, then
	 *		skip over it.
	 */
	if (!isalnum(words->entry[i].string.word[0] )) continue;
	swapped = 0;
	for(j = 0; j < glob_swp->size; ++j)
	    if (!wordcmp(glob_swp->pairs[j].from , words->entry[i].string ) ) {
		add_key(model, keys, glob_swp->pairs[j].to );
		swapped++;
		break;
	    }
	if (!swapped) add_key(model, keys, words->entry[i].string );
    }

    if (keys->size > 0) for(i = 0; i < words->size; ++i) {

	if (!isalnum(words->entry[i].string.word[0] )) continue;
	swapped = 0;
	for(j = 0; j < glob_swp->size; ++j)
	    if (!wordcmp(glob_swp->pairs[j].from, words->entry[i].string )) {
		add_aux(model, keys, glob_swp->pairs[j].to );
		swapped++;
		break;
	    }
	if (!swapped) add_aux(model, keys, words->entry[i].string );
    }

    return keys;
}

/*---------------------------------------------------------------------------*/

/*
 *		Function:	Add_Key
 *
 *		Purpose:		Add a word to the keyword dictionary.
 */
STATIC void add_key(MODEL *model, DICTIONARY *keys, STRING word)
{
    int symbol, xsymbol, ksymbol;

    if (!isalnum(word.word[0])) return;
    symbol = find_word(model->dictionary, word);
    if (symbol == 0) return;
    xsymbol = find_word(glob_ban, word);
    if (xsymbol != 0) return;
    xsymbol = find_word(glob_aux, word);
    if (xsymbol != 0) return;

    ksymbol = add_word_dodup(keys, word);
    if (ksymbol < keys->size) {
	keys->entry[ksymbol].stats.hits += 1;
	}
    if (ksymbol == keys->size-1) {
	keys->entry[ksymbol].stats.node += 1;
	}
}
/*---------------------------------------------------------------------------*/

/*
 *		Function:	Add_Aux
 *
 *		Purpose:		Add an auxilliary keyword to the keyword dictionary.
 */
STATIC void add_aux(MODEL *model, DICTIONARY *keys, STRING word)
{
    int symbol;

    if (isalnum(word.word[0]) == 0) return;
    symbol = find_word(model->dictionary, word);
    if (symbol == 0) return;
    symbol = find_word(glob_aux, word);
    if (symbol == 0) return;

    add_word_dodup(keys, word);
}

/*---------------------------------------------------------------------------*/

/*
 *		Function:	Reply
 *
 *		Purpose:		Generate a dictionary of reply words appropriate to the
 *						given dictionary of keywords.
 */
STATIC DICTIONARY *one_reply(MODEL *model, DICTIONARY *keys)
{
    static DICTIONARY *replies = NULL;
    unsigned int ui;
    WordNum symbol;
    bool start = TRUE;

    if (replies == NULL) replies = new_dictionary();
    else free_dictionary(replies);

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
	if (start == TRUE) symbol = seed(model, keys);
	else symbol = babble(model, keys, replies);
	if (symbol == 0 || symbol == 1) break;
	start = FALSE;

	/*
	 *		Append the symbol to the reply dictionary.
	 */
	add_word_nofuss(replies, model->dictionary->entry[ symbol ].string );
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
    if (replies->size > 0) for(ui = MIN(replies->size, 1+model->order); ui-- > 0; ) {
	symbol = find_word(model->dictionary, replies->entry[ ui ].string );
	update_context(model, symbol);
    }

    /*
     *		Generate the reply in the backward direction.
     */
    while(1) {
	/*
	 *		Get a random symbol from the current context.
	 */
	symbol = babble(model, keys, replies);
	if (symbol == 0 || symbol == 1) break;

	/*
	 *		Prepend the symbol to the reply dictionary.
	 */
	replies->entry = realloc(replies->entry, (replies->size+1)*sizeof *replies->entry);
	if (replies->entry == NULL) {
	    error("one_reply", "Unable to reallocate dictionary");
	    return NULL;
	}

	/*
	 *		Shuffle everything up for the prepend.
	 */
	for(ui = replies->size; ui > 0; --ui) {
	    replies->entry[ui].string = replies->entry[ui-1].string;
	}

	replies->entry[0].string = model->dictionary->entry[symbol].string;
	replies->size += 1;

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
STATIC double evaluate_reply(MODEL *model, DICTIONARY *keys, DICTIONARY *sentence)
{
    unsigned int ui, uj;
    WordNum symbol, ksymbol;
    double gfrac, kfrac,weight,probability, entropy = 0.0;
    unsigned count, totcount = 0;
    TREE *node;

    if (sentence->size<= 0) return 0.0;
    initialize_context(model);
    model->context[0] = model->forward;
    for(ui = 0; ui < sentence->size; ++ui) {
	symbol = find_word(model->dictionary, sentence->entry[ui].string );

	ksymbol = find_word(keys, sentence->entry[ui].string );
	if (ksymbol != 0 && ksymbol != WORD_NIL) {
	    probability = 0.0;
	    count = 0;
	    ++totcount;
	    for(uj = 0; uj < model->order; ++uj) {
		if (model->context[uj] == NULL) continue;

		node = find_symbol(model->context[uj], symbol);
    		if (!node) continue;
		probability += (double)node->count / model->context[uj]->usage;
		++count;

	    }

	    if (count > 0) {
	    	kfrac = (double)(1+keys->entry[ksymbol].stats.hits) / (double)(1+keys->entry[ksymbol].stats.node);
	    	gfrac = (double)(1+model->dictionary->entry[symbol].stats.hits) / (double)(1+model->dictionary->entry[symbol].stats.node);
		weight = kfrac / gfrac;
#if WANT_DUMP_KEYWORD_WEIGHTS
		fprintf(stderr, "[%*.*s: Keyw=%u/%u (%e)  Glob=%u/%u (%e)  Weight=%e]\n"
		, (int) sentence->entry[ui].string.length
		, (int) sentence->entry[ui].string.length
		, sentence->entry[ui].string.word
		, keys->entry[ksymbol].stats.hits
		, keys->entry[ksymbol].stats.node
		, kfrac
		, model->dictionary->entry[symbol].stats.hits
		, model->dictionary->entry[symbol].stats.node
		, gfrac
		, weight
		);
#endif
	    	probability *= weight;
		entropy -= log(probability / count);
		}
	}

	update_context(model, symbol);
    }

    initialize_context(model);
    model->context[0] = model->backward;
    for(ui = sentence->size; ui-- > 0; ) {
	symbol = find_word(model->dictionary, sentence->entry[ui].string );

	ksymbol = find_word(keys, sentence->entry[ui].string );
	if (ksymbol != 0 && ksymbol != WORD_NIL) {
	    probability = 0.0;
	    count = 0;
	    ++totcount;
	    for(uj = 0; uj < model->order; ++uj) {
		if (model->context[uj] == NULL) continue;

		node = find_symbol(model->context[uj], symbol);
    		if (!node) continue;
		probability += (double)node->count / model->context[uj]->usage;
		++count;

	    }

	    if (count > 0) {
	    	//weight = (double)(1+keys->entry[ksymbol].stats.hits) / (1+model->dictionary->entry[symbol].stats.hits);
	    	// weight = (double)(1+keys->entry[ksymbol].stats.hits) / (1+keys->entry[ksymbol].stats.node) ; 
	    	kfrac = (double)(1+keys->entry[ksymbol].stats.hits) / (double)(1+keys->entry[ksymbol].stats.node);
	    	gfrac = (double)(1+model->dictionary->entry[symbol].stats.hits) / (double)(1+model->dictionary->entry[symbol].stats.node);
		weight = kfrac / gfrac;
		probability *= weight;
		entropy -= log(probability/count);
		}
	}

	update_context(model, symbol);
    }

    if (totcount >= 8) entropy /= sqrt(totcount-1); 
    if (totcount >= 16) entropy /= totcount;

    return entropy;
}

/*---------------------------------------------------------------------------*/

/*
 *		Function:	Make_Output
 *
 *		Purpose:		Generate a string from the dictionary of reply words.
 */
STATIC char *make_output(DICTIONARY *words)
{
    static char *output = NULL;
    unsigned int ui;
    size_t length;
    static char *output_none = NULL;

    if (output_none == NULL) output_none = malloc(40);

    if (words->size == 0) {
	if (output_none != NULL)
	    strcpy(output_none, "I am utterly speechless!");
	return output_none;
    }

    length = 1;
    for(ui = 0; ui < words->size; ++ui) length += words->entry[ui].string.length;

    output = realloc(output, length);
    if (output == NULL) {
	error("make_output", "Unable to reallocate output.");
	if (output_none != NULL)
	    strcpy(output_none, "I forgot what I was going to say!");
	return output_none;
    }

    length = 0;
    for(ui = 0; ui < words->size; ++ui)
	{
	memcpy(output+length, words->entry[ui].string.word, words->entry[ui].string.length);
	length += words->entry[ui].string.length;
	}

    output[length] = '\0';

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
STATIC WordNum babble(MODEL *model, DICTIONARY *keys, DICTIONARY *words)
{
    TREE *node;
    unsigned int ui;
    unsigned count;
    WordNum symbol = 0;

    node = NULL;

    /*
     *		Select the longest available context.
     */
    for(ui = 0; ui <= model->order; ui++) {
	if (!model->context[ui] ) continue;
	// if (!node || node->branch <  model->context[ui]->branch ) // DlD
	    node = model->context[ui];
	}

    if (!node || node->branch == 0) return 0;

    /*
     *		Choose a symbol at random from this context.
     */
    ui = urnd(node->branch);
    count = urnd(node->usage);
    while(count > 0) {
	/*
	 *		If the symbol occurs as a keyword, then use it.  Only use an
	 *		auxilliary keyword if a normal keyword has already been used.
	 */
	symbol = node->children[ui].ptr->symbol;

	if (!find_word(keys, model->dictionary->entry[symbol].string) ) goto next;
	if (used_key == FALSE && find_word(glob_aux, model->dictionary->entry[symbol].string) ) goto next;
	if (word_exists(words, model->dictionary->entry[symbol].string) ) goto next;
	used_key = TRUE;
next:
	if (count > node->children[ui].ptr->count) count -= node->children[ui].ptr->count;
	else break; //count = 0;
	ui = (ui+1) % node->branch;
    }

    return symbol;
}

/*---------------------------------------------------------------------------*/

/*
 *		Function:	Word_Exists
 *
 *		Purpose:		A silly brute-force searcher for the reply string.
 */
STATIC bool word_exists(DICTIONARY *dictionary, STRING word)
{
    register unsigned int i;

    for(i = 0; i < dictionary->size; ++i)
	if (!wordcmp(dictionary->entry[i].string , word) )
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
STATIC WordNum seed(MODEL *model, DICTIONARY *keys)
{
    unsigned int idx, stop;
    WordNum symbol;

    /*
     *		Fix, thanks to Mark Tarrabain
     */
    if (model->context[0]->branch == 0) symbol = 0;
    else symbol = model->context[0]->children[ urnd(model->context[0]->branch) ].ptr->symbol;

    if (keys && keys->size > 0) {
	stop = idx = urnd(keys->size);
	while(TRUE) {
	    if ( find_word(model->dictionary, keys->entry[idx].string )
		&& !find_word(glob_aux, keys->entry[idx].string )
		) {
		symbol = find_word(model->dictionary, keys->entry[idx].string );
		return symbol;
	    }
	    idx = (idx+1) % keys->size;
	    if (idx == stop) return symbol;
	}
    }

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
    if (swp == NULL) {
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

    // list->from = realloc(list->from, list->size *sizeof *list->from);
    // if (list->from == NULL) {
	// error("add_swap", "Unable to reallocate from");
	// return;
    // }

    list->pairs = realloc(list->pairs, list->size *sizeof *list->pairs);
    if (list->pairs == NULL) {
	error("add_swap", "Unable to reallocate pairs");
	return;
    }

    // list->pairs[list->size-1].from.length = strlen(from);
    // list->pairs[list->size-1].from.word = strdup(from);
    // list->pairs[list->size-1].to.length = strlen(to);
    // list->pairs[list->size-1].to.word = strdup(to);
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
    FILE *file = NULL;
    char buffer[1024];
    char *from;
    char *to;

    list = new_swap();

    if (filename == NULL) return list;

    file = fopen(filename, "r");
    if (file == NULL) return list;

    while (fgets(buffer, sizeof buffer, file) ) {
	if (buffer[0] == '#') continue;
	from = strtok(buffer, "\t ");
	to = strtok(NULL, "\t \n#");

	add_swap(list, from, to);
    }

    fclose(file);
    return list;
}

/*---------------------------------------------------------------------------*/

STATIC void free_swap(SWAP *swap)
{
    register unsigned int i;

    if (swap == NULL) return;

    for(i = 0; i < swap->size; ++i) {
	free_word(swap->pairs[i].from);
	free_word(swap->pairs[i].to);
    }
    free(swap->pairs);
    // free(swap->from);
    // free(swap->to);
    free(swap);
}

/*---------------------------------------------------------------------------*/

/*
 *		Function:	Initialize_List
 *
 *		Purpose:		Read a dictionary from a file.
 */
STATIC DICTIONARY *read_dictionary(char *filename)
{
    DICTIONARY *list;
    FILE *file = NULL;
    STRING word;
    char *string;
    char buffer[1024];

    list = new_dictionary();

    if (filename == NULL) return list;

    file = fopen(filename, "r");
    if (file == NULL) return list;

    while( fgets(buffer, sizeof buffer, file) ) {
	if (buffer[0] == '#') continue;
	string = strtok(buffer, "\t \n#");
	if (string == NULL || !*string) continue;

	word = new_string(buffer, 0);
	add_word_dodup(list, word);
    }

    fclose(file);
    return list;
}

/*---------------------------------------------------------------------------*/

/*
 *		Function:	Delay
 *
 *		Purpose:		Display the string to stdout as if it was typed by a human.
 */
void delay(char *string)
{
    size_t i,len;

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
    for(i = 0; i < len-1; ++i) typein(string[i]);
    usleep((D_THINK+urnd(V_THINK)-urnd(V_THINK))/2);
    typein(string[i]);
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
    if ( !isalnum(c) &&  urnd(100) < P_THINK)
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
    // signal(SIGINT, saveandexit);
    // signal(SIGILL, die);
    //    signal(SIGSEGV, die);
#endif
    //    signal(SIGFPE, die);
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
void changevoice(DICTIONARY* words, unsigned int position)
{
#ifdef __mac_os
    register int i, index;
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

    for(i = 0; i < words->size-4; ++i)
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
		    // compare ignoring case
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

    for(j = 0; j <COMMAND_SIZE; ++j) {
	printf("#%-7s: %s\n", command[j].word.word, command[j].helpstring);
    }
}

/*---------------------------------------------------------------------------*/

void load_personality(MODEL **model)
{
    FILE *file;
    static char *filename = NULL;

    /*
     *		Allocate memory for the filename
     */
    filename = realloc(filename, strlen(directory)+strlen(SEP)+12);
    if (filename == NULL) error("load_personality","Unable to allocate filename");

    /*
     *		Check to see if the brain exists
     */

    if (strcmp(directory, last_directory)) {
	sprintf(filename, "%s%smegahal.brn", directory, SEP);
	file = fopen(filename, "r");
	if (file == NULL) {
	    sprintf(filename, "%s%smegahal.trn", directory, SEP);
	    file = fopen(filename, "r");
	    if (file == NULL) {
		fprintf(stdout, "Unable to change MegaHAL personality to \"%s\".\n"
			"Reverting to MegaHAL personality \"%s\".\n", directory, last_directory);
		free(directory);
		directory = strdup(last_directory);
		return;
	    }
	}
	fclose(file);
	fprintf(stdout, "Changing to MegaHAL personality \"%s\".\n", directory);
    }

    /*
     *		Free the current personality
     */
    free_model(*model);
    free_words(glob_ban);
    free_dictionary(glob_ban);
    free_words(glob_aux);
    free_dictionary(glob_aux);
    free_words(glob_grt);
    free_dictionary(glob_grt);
    free_swap(glob_swp);

    /*
     *		Create a language model.
     */
    *model = new_model(glob_order);

    /*
     *		Train the model on a text if one exists
     */

    sprintf(filename, "%s%smegahal.brn", directory, SEP);
    if (load_model(filename, *model) == FALSE) {
	sprintf(filename, "%s%smegahal.trn", directory, SEP);
	train(*model, filename);
    }

    /*
     *		Read a dictionary containing banned keywords, auxiliary keywords,
     *		greeting keywords and swap keywords
     */
    sprintf(filename, "%s%smegahal.ban", directory, SEP);
    glob_ban = read_dictionary(filename);
    sprintf(filename, "%s%smegahal.aux", directory, SEP);
    glob_aux = read_dictionary(filename);
    sprintf(filename, "%s%smegahal.grt", directory, SEP);
    glob_grt = read_dictionary(filename);
    sprintf(filename, "%s%smegahal.swp", directory, SEP);
    glob_swp = initialize_swap(filename);
}

/*---------------------------------------------------------------------------*/

void change_personality(DICTIONARY *command, unsigned int position, MODEL **model)
{

    if (directory == NULL) {
	directory = malloc(strlen(DEFAULT_DIR)+1);
	if (directory == NULL) {
	    error("change_personality", "Unable to allocate directory");
	} else {
	    strcpy(directory, DEFAULT_DIR);
	}
    }

    if (last_directory == NULL) {
	last_directory = strdup(directory);
    }

    if (command == NULL || position+2 >= command->size) {
	/* no dir set, so we leave it to whatever was set above */
    } else {
        directory = realloc(directory, command->entry[position+2].string.length+1);
        if (directory == NULL)
            error("change_personality", "Unable to allocate directory");
        memcpy(directory, command->entry[position+2].string.word,
                command->entry[position+2].string.length);
        directory[command->entry[position+2].string.length] ='\0';
    }

    load_personality(model);
}

/*---------------------------------------------------------------------------*/

STATIC void free_words(DICTIONARY *words)
{
    register unsigned int i;

    if (words == NULL) return;

    if (words->entry != NULL)
	for(i = 0; i < words->size; ++i) free_word(words->entry[i].string);
}

/*---------------------------------------------------------------------------*/

STATIC void free_word(STRING word)
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

STATIC WordNum * dict_hnd (DICTIONARY *dict, STRING word)
{
WordNum *np;
unsigned hash,slot;

/* We always assume that the next operation will be an insert.
 * So even if the wanted element is not present, *np will point
 * to the place where it is to be inserted.
 */
if (dict->size >= dict->msize && double_dictionary(dict)) return NULL;

hash = hash_word(word);
slot = hash % dict->msize;

for (np = &dict->entry[slot].tabl ; *np != WORD_NIL ; np = &dict->entry[*np].link ) {
	if ( dict->entry[*np].hash != hash) continue;
	if ( wordcmp(dict->entry[*np].string , word)) continue;
	break;
	}
return np;
}

STATIC WordNum * dict_hnd_tail (DICTIONARY *dict, STRING word)
{
WordNum *np;

for (np = dict_hnd(dict,word); np ; np = &dict->entry[*np].link ) {
	if (*np == WORD_NIL) break;
	// if ( dict->entry[*np].hash != hash) continue;
	// if ( wordcmp(dict->entry[*np].string , word)) continue;
	// continue;
	}
return np;
}

STATIC int double_dictionary(DICTIONARY *dict)
{
    unsigned newsize;

    newsize = dict->size ? dict->size + dict->size/2 : DICT_SIZE_INITIAL;
    return resize_dictionary(dict, newsize);
}


STATIC int resize_dictionary(DICTIONARY *dict, unsigned newsize)
{
    struct dictslot *old;
    WordNum item,slot;

    old = dict->entry ;
    while (newsize < dict->size) newsize += 2;
    dict->entry = malloc (newsize * sizeof *dict->entry);
    if (!dict->entry) {
	error("resize_dictionary", "Unable to allocate dictionary->slots.");
    	dict->entry = old;
	return -1;
	}
    dict->msize = newsize;
    format_dictionary(dict->entry, dict->msize);

    for (item =0 ; item < dict->size; item++) {
		WordNum *np;
		slot = old[item].hash % dict->msize;
		for( np = &dict->entry[slot].tabl; np; np = &dict->entry[*np].link ) {
			if (*np == WORD_NIL) break;
			}
		*np = item;
		dict->entry[item].hash = old[item].hash;
		dict->entry[item].stats.node = old[item].stats.node;
		dict->entry[item].stats.hits = old[item].stats.hits;
		dict->entry[item].string = old[item].string;
		}
    free (old);
    return 0; /* success */
}

