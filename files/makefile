all: cisj

cisj: smpl.o rand.o cisj.o
	$(LINK.c) -o $@ -Bstatic cisj.o smpl.o rand.o -lm

cisj.o: cisj.c
	$(COMPILE.c) -g cisj.c

smpl.o: smpl.c smpl.h
	$(COMPILE.c)  -g smpl.c

rand.o: rand.c
	$(COMPILE.c) -g rand.c


clean:
	$(RM) *.o relat saida

clean:
	-rm -f *~ *\# \#* *.o

purge: clean
	-rm -f cisj
