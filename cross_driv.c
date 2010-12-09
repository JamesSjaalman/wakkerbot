#include <stdio.h>
#include <string.h>
#include <math.h>

#include "crosstab.h"

int main()
{
char *cp, buff[100];
unsigned one,two;
int rc;
struct crosstab *cdp;

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
	default:
		cp += strspn(cp, " \t\n");
		rc = sscanf( cp, "%u %u", &one, &two);
		if (rc != 2) continue;
		crosstab_add_pair( cdp, one, two);
	case 'p': crosstab_print(stderr, cdp); continue;
	case 'q': goto quit;
		}
	}
quit:
return 0;
}

/* Eof */
