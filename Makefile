UUFLAGS = -dcfswH

default: coq

all: coq ag

coq: show refinement while auxproofs exampleverify example 

show: Show.vo
refinement: Refinement.vo
while: While.vo
auxproofs: AuxiliaryProofs.vo
usability: Usability.vo
exampleverify: ExampleVerify.vo
example: Example.vo
heap: Heap.vo

Heap.vo: Heap.v
	coqc Heap.v

Show.vo: Show.v
	coqc Show.v

Refinement.vo: Heap.vo Refinement.v
	coqc Refinement.v

While.vo: Show.vo Refinement.vo While.v
	coqc While.v

AuxiliaryProofs.vo: AuxiliaryProofs.v
	coqc AuxiliaryProofs.v

Usability.vo: While.vo Usability.v
	coqc Usability.v

ExampleVerify.vo: AuxiliaryProofs.vo Usability.vo ExampleVerify.v
	coqc ExampleVerify.v

Example.vo: ExampleVerify.vo Example.v
	coqc Example.v

ag: CodeGen/AG.hs

CodeGen/AG.hs: CodeGen/AG.ag CodeGen/AG/Base.ag CodeGen/AG/CodeGen.ag
	cd CodeGen/; uuagc $(UUFLAGS) AG.ag; cd -

clean:
	rm -f *.vo *.glob
	rm -f CodeGen/AG.hs
