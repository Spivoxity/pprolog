# Makefile for picoProlog on linux

all: pprolog

# The interpreter itself

pprolog: pprolog.c ptclib.i
	$(CC) $(CFLAGS) -o $@ $<

pprolog.c: pprolog.p ptc
	./ptc $< >$@

pprolog.p: pprolog.x ppp
	(echo "define(ptc)"; cat pprolog.x) | ./ppp >pprolog.p


# Pascal preprocessor 'ppp'

ppp: ppp.c ptclib.i
	$(CC) $(CFLAGS) -o $@ $<

ppp.c: ppp.p ptc
	./ptc $< >$@


# Alternate build using Free Pascal
FPC = fpc

fp-pprolog: fp-pprolog.p
	$(FPC) -o$@ $^

fp-pprolog.p: pprolog.x fp-ppp
	(echo "define(fpc)"; cat pprolog.x) | ./fp-ppp >fp-pprolog.p

fp-ppp: ppp.p
	$(FPC) -o$@ $^

# Pascal to C translator

PTC = main.o sem.o expr.o type.o symtab.o emit.o library.o parse.o scan.o

ptc: $(PTC)
	$(CC) $(CFLAGS) -o ptc $(PTC)

$(PTC): ptc.h parse.h

parse.c parse.h: parse.y
	bison -d -o parse.c parse.y

scan.c: scan.l
	flex -t scan.l >scan.c

# Cleanup
clean: force
	rm -f ptc ppp pprolog *.o ppp.c pprolog.c pprolog.p \
		parse.c parse.h scan.c fp-ppp fp-pprolog fp-pprolog.p 

force:

CC = gcc
CFLAGS = -g -O2
