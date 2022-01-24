NAME	:= $(shell basename `pwd`)

all: run

run: $(NAME).lisp
	sbcl --script $<

edit:
	vim -c 'set nu et fdm=marker bg=dark' $(NAME).lisp

.PHONY: all run edit
