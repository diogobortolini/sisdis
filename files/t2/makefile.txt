all: cisjAssinc

cisjAssinc: smpl.o rand.o cisjAssinc.o
	$(LINK.c) -o $@ -Bstatic cisjAssinc.o smpl.o rand.o -lm

cisj.o: cisjAssinc.c
	$(COMPILE.c) -g cisjAssinc.c

smpl.o: smpl.c smpl.h
	$(COMPILE.c)  -g smpl.c

rand.o: rand.c
	$(COMPILE.c) -g rand.c


clean:
	$(RM) *.o relat saida

clean:
	-rm -f *~ *\# \#* *.o

purge: clean
	-rm -f cisjAssinc
