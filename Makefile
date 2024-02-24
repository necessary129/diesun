CC     = gcc
RACKET = racket
RM     = rm
TIMEOUT = 1800

runtime.o: runtime.c runtime.h
	$(CC) -c -g -std=c99 runtime.c

test: runtime.o
	$(RACKET) run-tests.rkt

fuzz: runtime.o
	timeout --signal=HUP --preserve-status $(TIMEOUT) ./fuzz.sh

clean:
	$(RM) -f *.o *.out *.exe *.s *~
