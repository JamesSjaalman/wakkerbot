#include <stdio.h>
#include <string.h>
#include <math.h>

#include "crosstab.h"

static size_t format_num(char *buff, unsigned int num);
static size_t format_num(char *buff, unsigned int num)
{
return sprintf(buff, "%5u", num);
}

int main()
{
char *cp, buff[100];
unsigned one,two;
int rc;
struct crosstab *cdp;
double val;

cdp = crosstab_init(4);
while (fgets(buff, sizeof buff, stdin)) {
	cp = buff + strspn(buff, " \t\n");
	switch (*cp) {
	case 'i': 
		cp += strcspn(cp, " \t\n");
		rc = sscanf( cp, "%u", &one);
		if (rc != 1) continue;
		crosstab_resize( cdp, one); continue;
	case 'z': 
		cp += strcspn(cp, " \t\n");
		rc = sscanf( cp, "%u", &one);
		if (rc != 1) continue;
		crosstab_reduce( cdp, one); continue;
	case 'l': 
		cp += strcspn(cp, " \t\n");
		cp += strspn(cp, " \t\n");
		one = strcspn(cp, " \t\n");
		cp[one] = 0;
		crosstab_bin_load( cdp, cp); continue;
	case 'n': 
		cp += strcspn(cp, " \t\n");
		cp += strspn(cp, " \t\n");
		one = strcspn(cp, " \t\n");
		cp[one] = 0;
		crosstab_labels_load( cdp, cp); continue;
	case 's': 
		crosstab_repack( cdp); continue;
	default:
		cp += strspn(cp, " \t\n");
		rc = sscanf( cp, "%u %u", &one, &two);
		if (rc != 2) continue;
		crosstab_add_pair( cdp, one, two, 1);
	case 'p': crosstab_print(stderr, cdp); continue;
	case 'P': crosstab_pretty_print(stderr, cdp, format_num); continue;
	/* case 'd': crosstab_show(stdout, cdp, format_num); continue; */
	case 'd': crosstab_show(stdout, cdp, NULL); continue;
	case '?': 
		cp += strcspn(cp, " \t\n");
		rc = sscanf( cp, "%u", &one);
		if (rc != 1) continue;
		val = crosstab_ask(cdp, one); 
		fprintf(stderr, "[%u] = %6.4f\n", one, val);
		continue;
	case 'q': goto quit;
	case 'h':
		fprintf(stderr, "i <size>\t:= Initialize\n" );
		fprintf(stderr, "z <size>\t:= Reduce to size\n" );
		fprintf(stderr, "l <name>\t:= Load file with crostabs (crosstab.dmp)\n" );
		fprintf(stderr, "n <name>\t:= Load file with names (megahal.dic)\n" );
		fprintf(stderr, "s <void>\t:= Repack\n" );
		fprintf(stderr, "num1 num2\t:= Insert num1,num2\n" );
		fprintf(stderr, "p \t:= Print\n" );
		fprintf(stderr, "P \t:= Prettyprint\n" );
		fprintf(stderr, "d \t:= Show\n" );
		fprintf(stderr, "? <num> \t:= Ask value(num)\n" );
		}
	}
quit:
return 0;
}

/* Eof */
