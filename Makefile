UUFLAGS = -dcfswH

default: coq

all: coq ag

coq: show refinement while auxproofs example 

show: Show.vo
refinement: Refinement.vo
while: While.vo
auxproofs: AuxiliaryProofs.vo
example: Example.vo

Show.vo: Show.v
	coqc Show.v

Refinement.vo: Refinement.v
	coqc Refinement.v

While.vo: Show.vo Refinement.vo While.v
	coqc While.v

AuxiliaryProofs.vo: AuxiliaryProofs.v
	coqc AuxiliaryProofs.v

Example.vo: Show.vo Refinement.vo While.vo AuxiliaryProofs.vo Example.v
	coqc Example.v

ag: CodeGen/AG.hs

CodeGen/AG.hs: CodeGen/AG.ag CodeGen/AG/Base.ag CodeGen/AG/CodeGen.ag
	cd CodeGen/; uuagc $(UUFLAGS) AG.ag; cd -

clean:
	rm -f *.vo *.glob
	rm -f CodeGen/AG.hs
