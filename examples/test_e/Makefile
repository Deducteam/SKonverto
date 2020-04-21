DIR?=/usr/local/lib/
TIMELIMIT?=10s
TPTP=$(wildcard lemmas/*.p)
DKS=$(TPTP:.p=.lp)
DKO=$(DKS:.lp=.lpo)
all: test_e.lpo $(DKO) $(DKS)
lemmas_lpo: test_e.lpo $(DKO) $(DKS)
proof: proof_test_e.lpo

lemmas/%.lp : lemmas/%.p
	zenon_modulo -itptp -max-time $(TIMELIMIT) -odkterm -sig test_e $< > $@

lemmas/%.lpo : lemmas/%.lp test_e.lpo
	lambdapi check --gen-obj $<

test_e.lpo: test_e.lp
	lambdapi check --gen-obj $<

proof_test_e.lpo : proof_test_e.lp test_e.lpo $(DKO)
	lambdapi check --gen-obj $<

