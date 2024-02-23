CC     = gcc
RACKET = racket
RM     = rm

runtime.o: runtime.c runtime.h
	$(CC) -c -g -std=c99 runtime.c

test: runtime.o
	$(RACKET) run-tests.rkt

fuzz: runtime.o
	timeout --signal=HUP --preserve-status 1800 ./fuzz.sh

clean:
	$(RM) -f *.o *.out *.exe *.s *~
