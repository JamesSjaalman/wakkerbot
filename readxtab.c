
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define IDX_NIL (int)-1
unsigned crosstab_convert(char *name)
{
FILE *fp;
unsigned int sum,cnt,res;
struct dmprec {
	int key0;
	int key1;
	int uniq;
	int sum;
	} detail;

sum=cnt=0;
fp = fopen(name, "rb" );
fprintf(stderr,"Load(%s) :=%p\n", name, (void*) fp);

for ( sum=cnt=0;1; cnt++ ) {
	fread(&detail, sizeof detail, 1, fp);
	if (fread(&detail, sizeof detail, 1, fp) <1) break;
	/* fprintf(stderr, "[%u %u] %u\n", detail.key0,  detail.key1, detail.sum); */
	/* if (detail.key0 == IDX_NIL) continue; */
	/* if (detail.key1 == IDX_NIL) continue; */
	/* if (detail.sum == 0) continue; */
	if (detail.key0 != IDX_NIL && detail.key1 != IDX_NIL) sum += detail.sum;
	fprintf(stdout,"%d,%d,%d,%d\n"
		, detail.key0, detail.key1, detail.uniq, detail.sum);
	}
kut:
fclose (fp);
fprintf(stderr,"Sum=%u Cnt=%u\n" , sum, cnt);
return cnt;
}

int main(int argc, char **argv)
{
unsigned cnt;

cnt = crosstab_convert(argv[1] );


return 0;
}
