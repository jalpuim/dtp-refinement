default: coq

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

clean:
	rm -f *.vo *.glob 
