#
#  Copyright (C) 1998 Jason Hutchens
#
#  This program is free software; you can redistribute it and/or modify it
#  under the terms of the GNU General Public License as published by the Free
#  Software Foundation; either version 2 of the license or (at your option)
#  any later version.
#
#  This program is distributed in the hope that it will be useful, but
#  WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
#  or FITNESS FOR A PARTICULAR PURPOSE.  See the Gnu Public License for more
#  details.
#
#  You should have received a copy of the GNU General Public License along
#  with this program; if not, write to the Free Software Foundation, Inc.,
#  675 Mass Ave, Cambridge, MA 02139, USA.
#

# DEBUG=-DDEBUG
TCLVERSION=8.3
TCLINCLUDE=-I/usr/include/tcl$(TCLVERSION)
#CFLAGS=-g2 -pg -Wall -pedantic -O0
CFLAGS=-g2 -std=c99 -pg -Wall -pedantic -O4 -D_POSIX_SOURCE -D_XOPEN_SOURCE


#all:	megahal tcllib pythonmodule perlmodule
all:	megahal

clean:
	rm -f megahal
	rm -f *.o *.so

megahal: main.o megahal.o crosstab.o # megahal.h backup
	gcc $(CFLAGS) -o megahal megahal.o crosstab.o main.o -lm $(DEBUG)
	@echo "MegaHAL is up to date"

megahal.o: megahal.c megahal.h
	gcc -fPIC $(CFLAGS) -c megahal.c

main.o: main.c megahal.h
	gcc $(CFLAGS) -c main.c

############################
# Note megahal.c contains urnd()
############################

crosstab: cross_driv.o crosstab.o megahal.o
	gcc $(CFLAGS) -o $@ cross_driv.o crosstab.o megahal.o -lm

cross_driv.o: cross_driv.c crosstab.h
	gcc -fPIC $(CFLAGS) -c cross_driv.c

crosstab.o: crosstab.c crosstab.h
	gcc -fPIC $(CFLAGS) -c crosstab.c

readxtab: readxtab.c
	gcc $(CFLAGS) -o $@ $?

############################ Bagger

tcl-interface.o: tcl-interface.c
	gcc -fPIC $(CFLAGS) $(TCLINCLUDE) -c tcl-interface.c

tcllib: megahal.o tcl-interface.o
	gcc -fPIC -shared -Wl,-soname,libmh_tcl.so -o libmh_tcl.so megahal.o tcl-interface.o

pythonmodule: python-interface.c megahal.c
	python setup.py build

pythonmodule-install:
	python setup.py install --root=$(DESTDIR)

perlmodule: megahal.c megahal.h
	cd Megahal && perl Makefile.PL INSTALLDIRS=vendor && make

perlmodule-install:
	cd Megahal && make install DESTDIR=$(DESTDIR)

version:
	./cvsversion.tcl


#
#
