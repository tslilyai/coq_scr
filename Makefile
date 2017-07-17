SRCS=$(wildcard *.v)
OBJS=$(SRCS:.v=.vo)

all: $(OBJS)

scr.vo : scr.v helpers.vo model.vo

helpers.vo: helpers.v model.vo
	coqc $<

model.vo: model.v
	coqc $<


clean:
	rm -f *.vo *.glob .*.vo.aux

.PHONY: all clean

