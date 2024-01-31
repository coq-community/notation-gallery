VOFILES := $(patsubst %.v, %.vo, *.v)

all: $(VOFILES)

%.vo : *.v
	coqc $<

clean:
	rm *.vo *.vok *.vos *.glob

