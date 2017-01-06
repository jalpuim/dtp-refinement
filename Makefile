default: coq

coq: heap refinement while swap sqrt pa 

heap: Heap.vo
refinement: Refinement.vo
while: While.vo
swap: Swap.vo
sqrt: Sqrt.vo
pa: PersistentArrays.vo

Heap.vo: Heap.v
	coqc Heap.v

Refinement.vo: Heap.vo Refinement.v
	coqc Refinement.v

While.vo: Refinement.vo While.v
	coqc While.v

Swap.vo: While.vo Swap.v
	coqc Swap.v

Sqrt.vo: While.vo Sqrt.v
	coqc Sqrt.v

PersistentArrays.vo: While.vo PersistentArrays.v
	coqc PersistentArrays.v

clean:
	rm -f *.vo *.glob
