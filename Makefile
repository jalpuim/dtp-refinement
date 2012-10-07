default: coq

coq: show refinement while auxproofs example 

show: 
	coqc Show.v

refinement:
	coqc Refinement.v

while: show refinement
	coqc While.v

auxproofs: 
	coqc AuxiliaryProofs.v

example: show refinement while auxproofs
	coqc Example.v

clean:
	rm -f *.vo *.glob 
