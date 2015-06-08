
Topology.vo : logic.vo IZF.vo Relation.vo BaseMap.vo
	coqc Topology.v

Order.vo : logic.vo IZF.vo Relation.vo BaseMap.vo Maps.vo
	coqc Order.v

AddMultPower.vo : logic.vo IZF.vo Relation.vo BaseMap.vo Maps.vo TransitiveRecursion.v BOperation1.vo BOperation2.vo AddMultPower.v
	coqc AddMultPower.v

BOperation2.vo : logic.vo IZF.vo Relation.vo BaseMap.vo Maps.vo TransitiveRecursion.vo BOperation1.vo BOperation2.v
	coqc BOperation2.v

BOperation1.vo : logic.vo IZF.vo Relation.vo BaseMap.vo Maps.vo TransitiveRecursion.vo BOperation1.v
	coqc BOperation1.v

TransitiveRecursion.vo : logic.vo IZF.vo Relation.vo BaseMap.vo Maps.vo TransitiveRecursion.v
	coqc TransitiveRecursion.v

Maps.vo : logic.vo IZF.vo Relation.vo BaseMap.vo Maps.v
	coqc Maps.v

BaseMap.vo : logic.vo IZF.vo Relation.vo BaseMap.v
	coqc BaseMap.v

Relation.vo : logic.vo IZF.vo Relation.v
	coqc Relation.v

IZF.vo : logic.vo IZF.v
	coqc IZF.v

logic.vo : logic.v
	coqc logic.v


clean :
	rm *.vo
	rm *.glob
