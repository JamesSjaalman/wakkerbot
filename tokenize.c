#if WANT_MAIN
#include <stdio.h>
#include <string.h>

#define STATIC /**/
#endif

STATIC int myiswhite(int ch);
STATIC int myisalpha(int ch);
STATIC int myisupper(int ch);
STATIC int myislower(int ch);
STATIC int myisalnum(int ch);
STATIC int myisalnum_extra(int ch);
STATIC int myisalnum_html(int ch);

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

STATIC int myisalnum_html(int ch)
{
int ret = myisalnum(ch);
if (ret) return ret;
switch (ch){
case '-' :
case '_' :
case '$' :
case '/' :
case '#' :
case '?' :
case '=' :
case '%'  :
case '.': return 1;
default:
	return 0;
	}
}

STATIC int myisalpha(int ch)
{
if (myislower(ch) || myisupper(ch)) return 1;
	/* don't parse, just assume valid utf8*/
if ((ch & 0xf8) == 0xf0) return 0;	/* ellipsis e2 80 a6 */
if ((ch & 0xf0) == 0xe0) return 0;	/* ellipsis e2 80 a6 */
	/* e0 ...c0 are both valid prefixes for characters */
if (ch & 0x80) return 1;
return 0;
}

STATIC int myisutf8(int ch)
{
	/* don't parse, just assume valid utf8*/
if ((ch & 0xf8) == 0xf0) return 1;	/* ellipsis e2 80 a6 */
if ((ch & 0xf0) == 0xe0) return 1;	/* ellipsis e2 80 a6 */
if ((ch & 0xe0) == 0xc0) return 1;
if ((ch & 0xc0) == 0x80) return 1;
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
 * 20160117:
 * Version with http[s]://x.y.z support TOKEN_URL
 */
#define TOKEN_INIT 0
#define TOKEN_ANY 1
#define TOKEN_WORD 2
#define TOKEN_WORDDOT 3
#define TOKEN_WORDDOTLET 4
#define TOKEN_AFKODOT 5
#define TOKEN_AFKO 6
#define TOKEN_NUM 7
#define TOKEN_NUMDOT 8
#define TOKEN_NUMDOTLET 9
#define TOKEN_MEUK 10
#define TOKEN_PUNCT 11
#define TOKEN_ATHASH 12
#define TOKEN_URL 13
#define TOKEN_URL_DANGLING1 (TOKEN_URL +0x100)
#define TOKEN_URL_DANGLING2 (TOKEN_URL +0x101)
#define TOKEN_ELLIPSIS 14

/***************************************************************/
// e2 80 a6
STATIC size_t tokenize(char *str, int *sp)
{
    size_t pos ;

    for(pos=0; str[pos]; ) {
    switch(*sp) {
    case TOKEN_INIT: /* initial */
#if 0
	/* if (str[pos] == '\'' ) { *sp |= 16; return pos; }*/
	/* if (str[posi] == '"' ) { *sp |= 32; return pos; }*/
#endif
	if (myisalpha(str[pos])) {*sp = TOKEN_WORD; pos++; continue; }
	if (myisalnum(str[pos])) {*sp = TOKEN_NUM; pos++; continue; }
	if (strspn(str+pos, "#@")) { *sp = TOKEN_ATHASH; pos++; continue; }
	/* if (strspn(str+pos, "-+")) { *sp = TOKEN_NUM; pos++; continue; }*/
	if ( myisutf8(str[pos]) ) { *sp = TOKEN_ELLIPSIS; pos++; continue; }
	*sp = TOKEN_ANY;
    case TOKEN_ANY: /* either whitespace or meuk: eat it */
	pos += strspn(str+pos, " \t\n\r\f\b" );
	if (pos) {*sp = TOKEN_INIT; return pos; }
	// pos++;
        *sp = TOKEN_MEUK; continue;
        break;
    case TOKEN_WORD: /* inside word */
	while ( myisalnum(str[pos]) ) pos++;
	if ( myisutf8(str[pos]) ) { *sp = TOKEN_ELLIPSIS; return pos; }
	if (str[pos] == '\0' ) { *sp = TOKEN_INIT; return pos; }
	if (str[pos] == '.' ) { *sp = TOKEN_WORDDOT; pos++; continue; }
	if (str[pos] == ':' ) {
		if (pos==4 && !strncasecmp(str, "http", 4)) {*sp=TOKEN_URL_DANGLING1; pos++; continue; }
		if (pos==5 && !strncasecmp(str, "https", 5)) {*sp=TOKEN_URL_DANGLING1; pos++; continue; }
		}
	*sp = TOKEN_INIT;
	return pos;
        break;
    case TOKEN_WORDDOT: /* word. */
	if (myisalpha(str[pos]) ) { *sp=TOKEN_WORDDOTLET; pos++; continue; }
	if (myisutf8(str[pos]) ) { *sp = TOKEN_INIT; return pos-1; }
	*sp = TOKEN_INIT;
	return pos-1;
        break;
    case TOKEN_WORDDOTLET: /* word.A */
	if (str[pos] == '.') { *sp=TOKEN_AFKODOT; pos++; continue; }
	if (myisalpha(str[pos]) ) { *sp = TOKEN_INIT; return pos-2; }
	if ( myisutf8(str[pos]) ) { *sp = TOKEN_INIT; return pos-2; }
	if (myisalnum(str[pos]) ) { *sp=TOKEN_NUM; continue; }
	*sp = TOKEN_INIT;
	return pos-2;
	break;
    case TOKEN_AFKODOT: /* A.B. */
        if (myisalpha(str[pos]) ) { *sp=TOKEN_AFKO; pos++; continue; }
	if ( myisutf8(str[pos]) ) { *sp = TOKEN_INIT; return pos; }
	*sp = TOKEN_INIT;
        return pos >= 3 ? pos : pos -2;
        break;
    case TOKEN_AFKO: /* word.A.B */
	if (str[pos] == '.') { *sp=TOKEN_AFKODOT; pos++; continue; }
	if (myisalpha(str[pos]) ) { *sp = TOKEN_INIT; return pos - 2; }
	if ( myisutf8(str[pos]) ) { *sp = TOKEN_INIT; return pos; }
	*sp = TOKEN_INIT;
	return pos-1;
        break;
    case TOKEN_NUM: /* number */
	if ( myisalnum(str[pos]) ) { pos++; continue; }
	if (strspn(str+pos, ".,")) { *sp=TOKEN_NUMDOT; pos++; continue; }
	*sp = TOKEN_INIT;
	return pos;
        break;
    case TOKEN_NUMDOT: /* number[.,] */
	if (myisalpha(str[pos])) { *sp=TOKEN_NUMDOTLET; pos++; continue; }
	if (myisalnum(str[pos])) { *sp=TOKEN_NUM; pos++; continue; }
	if (strspn(str+pos, "-+")) { *sp=TOKEN_NUM; pos++; continue; }
	if ( myisutf8(str[pos]) ) { *sp = TOKEN_INIT; return pos; }
	*sp = TOKEN_INIT;
	return pos-1;
        break;
    case TOKEN_NUMDOTLET: /* number[.,][a-z] */
	if (myisalpha(str[pos])) { *sp = TOKEN_WORD; return pos-2; }
	if (myisalnum(str[pos])) { *sp=TOKEN_NUM; pos++; continue; }
	if ( myisutf8(str[pos]) ) { *sp = TOKEN_INIT; return pos-2; }
	*sp = TOKEN_INIT;
	return pos-2;
        break;
    case TOKEN_MEUK: /* inside meuk */
	if (myisalnum(str[pos])) { *sp = TOKEN_INIT; return pos; }
	if (myiswhite(str[pos])) { *sp = TOKEN_INIT; return pos; }
	if (strspn(str+pos, ".,?!" )) { *sp = TOKEN_INIT; if (!pos) *sp=TOKEN_PUNCT; else { return pos; }}
	if (strspn(str+pos, "@'\"" )) { *sp = TOKEN_INIT; return pos ? pos : 1; }
	if (strspn(str+pos, ":;" )) { *sp = TOKEN_INIT; return pos ? pos : 1; }
	if (strspn(str+pos, "('\"){}[]" )) { *sp = TOKEN_INIT; return pos ? pos : 1; }
	if ( myisutf8(str[pos]) ) { *sp = TOKEN_INIT; return pos; }
	pos++; continue; /* collect all garbage */
        break;
    case TOKEN_PUNCT: /* punctuation */
	if (strspn(str+pos, "@#" )) { *sp=TOKEN_MEUK; pos++; continue; }
	pos += strspn(str+pos, ".,?!" ) ;
	*sp = TOKEN_INIT;
        return pos ? pos : 1;
        break;
    case TOKEN_ATHASH: /* @ or # should be followed by an "identifier"  */
	while ( myisalpha(str[pos]) ) pos++;
	if (pos  < 2)  { *sp=TOKEN_MEUK; continue; }
        while ( myisalnum_extra(str[pos]) ) {pos++; }
	if ( myisutf8(str[pos]) ) { *sp = TOKEN_INIT; return pos; }
	*sp = TOKEN_INIT;
	return pos ;
    case TOKEN_URL_DANGLING1: /* http: or https: looking for // */
	if ( str[pos] == '/' ) { pos++; *sp=TOKEN_URL_DANGLING2; continue; }
	else { *sp=TOKEN_INIT; return pos-1; }
        break;
    case TOKEN_URL_DANGLING2: /* http:/ or https:/ looking for / */
	if ( str[pos] == '/' ) { pos++; *sp=TOKEN_URL; continue; }
	else { *sp=TOKEN_INIT; return pos-2;}
	break;
    case TOKEN_URL: /* http:// or https:// should be followed by an "identifier"  */
        if (str[pos] == 0xe2) { /* ellipsis */ *sp = TOKEN_INIT; return pos ; }
        if ( !myisalnum_html(str[pos])) { /* suppress trailing period */
		*sp = TOKEN_INIT;
		return (pos && str[pos-1] == '.') ? pos-1: pos ; 
		}
	pos++; continue;
        break;
    case TOKEN_ELLIPSIS:
	while ( myisutf8(str[pos]) ) pos++;
	*sp = TOKEN_INIT;
	return pos ;
        }
    }
    /* This is ugly. Depending on the state,
    ** we need to know how many lookahead chars we consumed */
    switch (*sp) {
    default:
    case TOKEN_INIT: break;
    case TOKEN_ANY: break;
    case TOKEN_WORD: break;
    case TOKEN_WORDDOT: pos -= 1; break;
    case TOKEN_WORDDOTLET: pos -= 2; break;
    case TOKEN_AFKODOT: if (pos < 3) pos -= 2; break;
    case TOKEN_AFKO: break;
    case TOKEN_NUM: break;
    case TOKEN_NUMDOT: pos-= 1; break;
    case TOKEN_NUMDOTLET: pos -= 2; break;
    case TOKEN_MEUK: break;
    case TOKEN_PUNCT: break;
    case TOKEN_ATHASH: break;
    case TOKEN_URL: break;
    }
    *sp = TOKEN_INIT;
    return pos;
}
#if WANT_MAIN
int main (void)
{
char buff[100];
size_t pos,len;
int state;

while (fgets(buff, sizeof buff, stdin)) {
	for (pos = len = 0; buff[pos]; pos += len) {
		state = 0;
		len= tokenize(buff+pos, &state);
		fprintf(stdout, "%d [%zu]:\"%.*s\"\n"
			, state, len, (int) len, buff+pos);
		}
	}
return 0;
}
#endif

