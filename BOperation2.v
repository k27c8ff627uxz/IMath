Require Import logic.
Require Import IZF.
Require Import Relation.
Require Import BaseMap.
Require Import Maps.
Require Import BOperation1.

Definition BOperation2 A := Cartesian (BOperation A) (BOperation A).

(****************)
(*Distributivity*)
(****************)
Definition LeftDistribute A : #(Relation (BOperation A) (BOperation A)) :=
MakeRelation (fun o1 o2 =>
  forall a b c, %o2 [a ;%o1[b;c]] == %o1[%o2[a;b] ; %o2[a;c]]
).
Definition RightDistribute A : #(Relation (BOperation A) (BOperation A)) :=
MakeRelation (fun o1 o2 =>
  forall a b c, %o2 [%o1[a;b];c] == %o1[%o2[a;c] ; %o2[b;c]]
).
Definition Distribute A : #(Relation (BOperation A) (BOperation A)) :=
%AndRelation [@LeftDistribute A ; @RightDistribute A].


Definition Ope2_LDistDond {A} (o1 : #(BOperation A)) (o2 : #(BOperation A)) :=
forall a b c, %o2 [a ;%o1[b;c]] == %o1[%o2[a;b] ; %o2[a;c]].
Definition Ope2_RDistDond {A} (o1 : #(BOperation A)) (o2 : #(BOperation A)) :=
forall a b c, %o2 [%o1[a;b];c] == %o1[%o2[a;c] ; %o2[b;c]].
Definition Ope2_DistDond {A} (o1 : #(BOperation A)) (o2 : #(BOperation A)) :=
forall a b c, %o2 [a ;%o1[b;c]] == %o1[%o2[a;b] ; %o2[a;c]] /\ %o2 [%o1[a;b];c] == %o1[%o2[a;c] ; %o2[b;c]].
Definition Ope2_DistDond2 {A} (o1 : #(BOperation A)) (o2 : #(BOperation A)) :=
Ope2_LDistDond o1 o2 /\ Ope2_RDistDond o1 o2.

Theorem Ope2_LDist : forall {A} (o1 o2 : #(BOperation A)),
Ope2_LDistDond o1 o2 <-> In [o1;o2] (LeftDistribute A).
Proof.
intros A o1 o2.
split.
 intro cond.
 apply FoForm_If.
 apply MakeRelationTheorem.
 intros o1' o2' Eqo1 Eqo2 a b c.
 apply (TransitivityEq (%o2 [a;%o1[b;c]])).
  apply SymmetryEq.
  apply MapEqAll.
   apply EqualInPair'R.
   apply MapEq.
   apply Eqo1.
  apply Eqo2.
 rewrite cond.
 apply MapEqAll.
  apply EqualInPair'.
  split; apply MapEq; apply Eqo2.
 apply Eqo1.

 intro InoL.
 intros a b c.
 apply ToForm_If in InoL.
 put ((proj1 (MakeRelationTheorem _ _ _ _ _)) InoL) MH.
 apply MH.
 hyperreflexivity.
 hyperreflexivity.
Qed.

Theorem Ope2_RDist : forall {A} (o1 o2 : #(BOperation A)),
Ope2_RDistDond o1 o2 <-> In [o1;o2] (RightDistribute A).
Proof.
intros A o1 o2.
split.
 intro cond.
 apply FoForm_If.
 apply MakeRelationTheorem.
 intros o1' o2' Eqo1 Eqo2 a b c.
 apply (TransitivityEq (%o2 [%o1[a;b];c])).
  apply SymmetryEq.
  apply MapEqAll.
   apply EqualInPair'L.
   apply MapEq.
   apply Eqo1.
  apply Eqo2.
 rewrite cond.
 apply MapEqAll.
  apply EqualInPair'.
  split; apply MapEq; apply Eqo2.
 apply Eqo1.

 intro InoR.
 intros a b c.
 apply ToForm_If in InoR.
 put ((proj1 (MakeRelationTheorem _ _ _ _ _)) InoR) MH.
 apply MH.
 hyperreflexivity.
 hyperreflexivity.
Qed.

Theorem Ope2_Dist2 : forall {A} (o1 o2 : #(BOperation A)),
Ope2_DistDond2 o1 o2 <-> In [o1;o2] (Distribute A).
Proof.
intros A o1 o2.
split.
 intro cond.
 destruct cond as [CL CR].
 apply FoForm_If.
 unfold Distribute.
 apply AndRelationTheorem.
 split.
  apply ToForm_If.
  apply Ope2_LDist.
  apply CL.

  apply ToForm_If.
  apply Ope2_RDist.
  apply CR.

 intro InoD.
 apply ToForm_If in InoD.
 unfold Distribute in InoD.
 apply AndRelationTheorem in InoD.
 destruct InoD as [LC RC].
 split.
  apply Ope2_LDist.
  apply FoForm_If.
  apply LC.

  apply Ope2_RDist.
  apply FoForm_If.
  apply RC.
Qed.

Theorem Ope2_Dist : forall {A} (o1 o2 : #(BOperation A)),
Ope2_DistDond o1 o2 <-> In [o1;o2] (Distribute A).
Proof.
intros A o1 o2.
split.
 intro cond.
 unfold Ope2_DistDond in cond.
 apply Ope2_Dist2.
 split.
 intros a b c.
 apply (proj1 (cond _ _ _)).
 intros a b c.
 apply (proj2 (cond _ _ _)).

 intro InoD.
 unfold Distribute in InoD.
 apply ToForm_If in InoD.
 apply AndRelationTheorem in InoD.
 destruct InoD as [LC RC].
 intros a b c.
 split.
 put ((proj1 (MakeRelationTheorem _ _ _ _ _)) LC) LC'.
 apply LC'; hyperreflexivity.
 put ((proj1 (MakeRelationTheorem _ _ _ _ _)) RC) RC'.
 apply RC'; hyperreflexivity.
Qed.
 
Theorem LDist_Ope2 : forall {A},
Subset (LeftDistribute A) (BOperation2 A).
Proof.
intros A oD InodL.
put (IsPair'Relation _ _ _ _ InodL) EqoD.
destruct EqoD as [o1 EqoD].
destruct EqoD as [o2 EqoD].
rewrite EqoD.
apply SetProp.
Qed.

Theorem RDist_Ope2 : forall {A},
Subset (RightDistribute A) (BOperation2 A).
Proof.
intros A oD InodR.
put (IsPair'Relation _ _ _ _ InodR) EqoD.
destruct EqoD as [o1 EqoD].
destruct EqoD as [o2 EqoD].
rewrite EqoD.
apply SetProp.
Qed.

Theorem Dist_LDist : forall {A},
Subset (Distribute A) (LeftDistribute A).
Proof.
intros A.
intros oD InoDD.
put (IsPair'Relation _ _ _ _ InoDD) EqoD.
destruct EqoD as [o1 EqoD].
destruct EqoD as [o2 EqoD].
rewrite EqoD in InoDD.
rewrite EqoD.
apply Ope2_Dist2 in InoDD.
destruct InoDD as [LC _].
apply Ope2_LDist.
apply LC.
Qed.

Theorem Dist_RDist : forall {A},
Subset (Distribute A) (RightDistribute A).
Proof.
intros A.
intros oD InoDD.
put (IsPair'Relation _ _ _ _ InoDD) EqoD.
destruct EqoD as [o1 EqoD].
destruct EqoD as [o2 EqoD].
rewrite EqoD in InoDD.
rewrite EqoD.
apply Ope2_Dist2 in InoDD.
destruct InoDD as [_ RC].
apply Ope2_RDist.
apply RC.
Qed.

Theorem Dist_Ope2 : forall {A},
Subset (Distribute A) (BOperation2 A).
Proof.
intros A.
apply (TransitivitySubset (LeftDistribute A)).
apply Dist_LDist.
apply LDist_Ope2.
Qed.

Theorem Dist_LDistCommCond : forall {A} (o1 : #(BOperation A)) (o2 : #(BOperation A)),
Ope_CommCond o2 ->
(Ope2_DistDond o1 o2 <-> Ope2_LDistDond o1 o2).
Proof.
intros A o1 o2 CommCond.
split.
intro DisCond.
intros a b c.
unfold Ope2_DistDond in DisCond.
apply (proj1(DisCond _ _ _)).

intro LDisCond.
unfold Ope2_LDistDond in LDisCond.
intros a b c.
split.
apply LDisCond.
apply (TransitivityEq (%o2 [c;%o1[a;b]])).
 apply CommCond.
rewrite LDisCond.
apply MapArgEq.
apply EqualInPair'.
split.
apply CommCond.
apply CommCond.
Qed.

Theorem Dist_RDistCommCond : forall {A} (o1 : #(BOperation A)) (o2 : #(BOperation A)),
Ope_CommCond o2 ->
(Ope2_DistDond o1 o2 <-> Ope2_RDistDond o1 o2).
Proof.
intros A o1 o2 CommCond.
split.
intro DisCond.
intros a b c.
unfold Ope2_DistDond in DisCond.
apply (proj2(DisCond _ _ _)).

intro RDisCond.
unfold Ope2_RDistDond in RDisCond.
intros a b c.
apply SymmetryAnd.
split.
apply RDisCond.
apply (TransitivityEq (%o2 [%o1[b;c];a])).
 apply CommCond.
rewrite RDisCond.
apply MapArgEq.
apply EqualInPair'.
split.
apply CommCond.
apply CommCond.
Qed.


(************)
(*** Ring ***)
(************)

(* definition *)
Definition Ringoid A := Cartesian (CGroup A) (Monoid A).
Definition CRingoid A := Cartesian (CGroup A) (CMonoid A).
Definition Ring A : #(Relation (CGroup A) (Monoid A)) :=
MakeRelation (fun cg sg => &&(Distribute A) (cg{<CGrp_Ope}) (sg{<Monoid_Ope})).
Definition CRing A : #(Relation (CGroup A) (CMonoid A)) :=
MakeRelation (fun cg sg => &&(Distribute A) (cg{<CGrp_Ope}) (sg{<CMonoid_Ope})).

(* Relation Of Ring *)
Theorem Ringoid_Ope2 : forall {A}, Subset (Ringoid A) (BOperation2 A).
Proof.
intros A.
apply SubsetInCartesian.
apply CGrp_Ope.
apply Monoid_Ope.
Qed.
Theorem CRingoid_Ope2 : forall {A}, Subset (CRingoid A) (BOperation2 A).
Proof.
intros A.
apply SubsetInCartesian.
apply CGrp_Ope.
apply CMonoid_Ope.
Qed.
Theorem CRingoid_Ringoid : forall {A}, Subset (CRingoid A) (Ringoid A).
Proof.
intros A.
apply SubsetInCartesian.
apply ReflexivitySubset.
apply CMonoid_Monoid.
Qed.

Theorem Ring_Ringoid : forall {A},
Subset (Ring A) (Ringoid A).
Proof.
intros A.
apply (TransitivitySubset _ (StrongTrueRel _)).
apply ReflexivitySubset.
Qed.
Theorem CRing_CRingoid : forall {A},
Subset (CRing A) (CRingoid A).
Proof.
intros A.
apply (TransitivitySubset _ (StrongTrueRel _)).
apply ReflexivitySubset.
Qed.
Theorem Ring_Ope2 : forall {A},
Subset (Ring A) (BOperation2 A).
Proof.
intro A.
apply (TransitivitySubset (Ringoid A)).
apply Ring_Ringoid.
apply Ringoid_Ope2.
Qed.
Theorem CRing_Ope2 : forall {A},
Subset (CRing A) (BOperation2 A).
Proof.
intro A.
apply (TransitivitySubset (CRingoid A)).
apply CRing_CRingoid.
apply CRingoid_Ope2.
Qed.

Theorem CRing_Ring : forall {A},
Subset (CRing A) (Ring A).
Proof.
intros A.
intros oD InoDC.
put (IsPair'Relation _ _ _ _ InoDC) EqoD.
destruct EqoD as [o1 EqoD].
destruct EqoD as [o2 EqoD].
rewrite EqoD in InoDC.
rewrite EqoD.
apply ToForm_If in InoDC.
cut (In [o1;o2{<CMonoid_Monoid}] (Ring A)).
 apply Arrow2Rewrite; hyperreflexivity.
apply FoForm_If.
put ((proj1 (MakeRelationTheorem _ _ _ _ _)) InoDC) CRH.
apply MakeRelationTheorem.
intros o1' o2' Eqo1 Eqo2.
generalize (CRH _ _ (ReflexivityEq o1) (ReflexivityEq o2)).
apply RelRewriteAll.
apply Eqo1.
apply Eqo2.
hyperreflexivity.
Qed.


Definition Ringoid_RingDond {A} (cg : #(CGroup A)) (m : #(Monoid A)) :=
Ope2_DistDond (cg{<CGrp_Ope}) (m{<Monoid_Ope}).
Theorem Ringoid_Ring : forall {A} (cg : #(CGroup A)) (m : #(Monoid A)),
Ringoid_RingDond cg m <-> In [cg;m] (Ring A).
Proof.
intros A cg m.
split.
 intro cond.
 unfold Ringoid_RingDond in cond.
 apply FoForm_If.
 apply MakeRelationTheorem.
 intros cg' m' Eqcg Eqm.
 cut (&& (Distribute A) (cg{<CGrp_Ope}) (m{<Monoid_Ope})).
  apply RelRewriteAll.
  apply Eqcg.
  apply Eqm.
  hyperreflexivity.
 apply ToForm_If.
 apply Ope2_Dist.
 apply cond.

 intro InR.
 unfold Ringoid_RingDond.
 apply ToForm_If in InR.
 put ((proj1 (MakeRelationTheorem _ _ _ _ _)) InR) RH.
 apply Ope2_Dist.
 apply FoForm_If.
 apply RH; hyperreflexivity.
Qed.

Definition CRingoid_CRingDond {A} (cg : #(CGroup A)) (m : #(CMonoid A)) :=
Ope2_DistDond (cg{<CGrp_Ope}) (m{<CMonoid_Ope}).
Theorem CRingoid_CRing : forall {A} (cg : #(CGroup A)) (m : #(CMonoid A)),
CRingoid_CRingDond cg m <-> In [cg;m] (CRing A).
Proof.
intros A cg m.
split.
 intro cond.
 unfold Ringoid_RingDond in cond.
 apply FoForm_If.
 apply MakeRelationTheorem.
 intros cg' m' Eqcg Eqm.
 cut (&& (Distribute A) (cg{<CGrp_Ope}) (m{<CMonoid_Ope})).
  apply RelRewriteAll.
  apply Eqcg.
  apply Eqm.
  hyperreflexivity.
 apply ToForm_If.
 apply Ope2_Dist.
 apply cond.

 intro InR.
 unfold Ringoid_RingDond.
 apply ToForm_If in InR.
 put ((proj1 (MakeRelationTheorem _ _ _ _ _)) InR) RH.
 apply Ope2_Dist.
 apply FoForm_If.
 apply RH; hyperreflexivity.
Qed.


Definition Ope2_RingDond {A} (o1 : #(BOperation A)) (o2 : #(BOperation A)) :=
Ope_CGrpCond o1 /\ Ope_MonoidCond o2 /\ Ope2_DistDond o1 o2.
Theorem Ope2_Ring : forall {A} (o1 : #(BOperation A)) (o2 : #(BOperation A)),
Ope2_RingDond o1 o2 <-> In [o1;o2] (Ring A).
Proof.
intros A o1 o2.
split.
 intro cond.
 destruct cond as [Co1 RC].
 destruct RC as [Co2 DC].
 cut (In ([o1{<Ope_CGrp ! Co1};o2{<Ope_Monoid ! Co2}]) (Ring A)).
  apply Arrow2Rewrite; hyperreflexivity.
 apply FoForm_If.
 apply MakeRelationTheorem.
 intros o1' o2' Eqo1 Eqo2.
 apply Ope2_Dist in DC.
 apply ToForm_If in DC.
 generalize DC.
 apply RelRewriteAll.
 apply Eqo1.
 apply Eqo2.
 hyperreflexivity.

 intro InoC.
 put (IsPair'Relation _ _ _ _ InoC) Eqo.
 destruct Eqo as [o1' Eqo].
 destruct Eqo as [o2' Eqo].
 put Eqo EqD.
 apply EqualInPair' in EqD.
 destruct EqD as [Eqo1 Eqo2].
 split.
  apply Ope_CGrp.
  rewrite Eqo1.
  apply SetProp.
 split.
  apply Ope_Monoid.
  rewrite Eqo2.
  apply SetProp.
 rewrite Eqo in InoC.
 apply ToForm_If in InoC.
 apply Ope2_Dist.
 apply FoForm_If.
 put ((proj1 (MakeRelationTheorem _ _ _ _ _)) InoC) DH. 
 generalize (DH _ _ (ReflexivityEq _) (ReflexivityEq _)).
 apply RelRewriteAll.
 apply SymmetryEq.
 apply Eqo1.
 apply SymmetryEq.
 apply Eqo2.
 hyperreflexivity.
Qed.


Definition Ope2_CRingDond {A} (o1 : #(BOperation A)) (o2 : #(BOperation A)) :=
Ope_CGrpCond o1 /\ Ope_CMonoidCond o2 /\ Ope2_DistDond o1 o2.
Theorem Ope2_CRing : forall {A} (o1 : #(BOperation A)) (o2 : #(BOperation A)),
Ope2_CRingDond o1 o2 <-> In [o1;o2] (CRing A).
Proof.
intros A o1 o2.
split.
 intro cond.
 destruct cond as [Co1 RC].
 destruct RC as [Co2 DC].
 cut (In ([o1{<Ope_CGrp ! Co1};o2{<Ope_CMonoid ! Co2}]) (CRing A)).
  apply Arrow2Rewrite; hyperreflexivity.
 apply FoForm_If.
 apply MakeRelationTheorem.
 intros o1' o2' Eqo1 Eqo2.
 apply Ope2_Dist in DC.
 apply ToForm_If in DC.
 generalize DC.
 apply RelRewriteAll.
 apply Eqo1.
 apply Eqo2.
 hyperreflexivity.

 intro InoC.
 put (IsPair'Relation _ _ _ _ InoC) Eqo.
 destruct Eqo as [o1' Eqo].
 destruct Eqo as [o2' Eqo].
 put Eqo EqD.
 apply EqualInPair' in EqD.
 destruct EqD as [Eqo1 Eqo2].
 split.
  apply Ope_CGrp.
  rewrite Eqo1.
  apply SetProp.
 split.
  apply Ope_CMonoid.
  rewrite Eqo2.
  apply SetProp.
 rewrite Eqo in InoC.
 apply ToForm_If in InoC.
 apply Ope2_Dist.
 apply FoForm_If.
 put ((proj1 (MakeRelationTheorem _ _ _ _ _)) InoC) DH. 
 generalize (DH _ _ (ReflexivityEq _) (ReflexivityEq _)).
 apply RelRewriteAll.
 apply SymmetryEq.
 apply Eqo1.
 apply SymmetryEq.
 apply Eqo2.
 hyperreflexivity.
Qed.


Theorem Ring_Dist : forall {A},
Subset (Ring A) (Distribute A).
Proof.
intros A.
intros o InoR.
assert(InoO : In o (BOperation2 A)).
 apply Ring_Ope2.
 apply InoR.
put (CartesianIsPair' _ _ _ InoO) Eqo.
destruct Eqo as [o1 Eqo].
destruct Eqo as [o2 Eqo].
rewrite Eqo in InoR.
apply Ope2_Ring in InoR.
destruct InoR as [_ InoR].
destruct InoR as [_ InoR].
apply Ope2_Dist in InoR.
rewrite <- Eqo in InoR.
apply InoR.
Qed.

Theorem CRing_Dist : forall {A},
Subset (CRing A) (Distribute A).
Proof.
intros A.
apply (TransitivitySubset (Ring A)).
apply CRing_Ring.
apply Ring_Dist.
Qed.



(* Operation *)
Definition Mult_of_Ring {A} : #(Map (Ring A) (Monoid A)) :=
RelationAsPairR _.
Definition Mult_of_CRing {A} : #(Map (CRing A) (CMonoid A)) :=
RelationAsPairR _.

Definition Add_of_Ring {A} : #(Map (Ring A) (CGroup A)) :=
RelationAsPairL _.
Definition Add_of_CRing {A} (R : #(CRing A)) :=
%Add_of_Ring (R{<CRing_Ring}).

Definition MultO_of_Ring {A} (R : #(Ring A)) :=
(%Mult_of_Ring R){<Monoid_Ope}.
Definition MultO_of_CRing {A} (R : #(CRing A)) :=
(%Mult_of_CRing R){<CMonoid_Ope}.

Definition AddO_of_Ring {A} (R : #(Ring A)) :=
(%Add_of_Ring R){<CGrp_Ope}.
Definition AddO_of_CRing {A} (R : #(CRing A)) :=
(Add_of_CRing R){<CGrp_Ope}.

Definition MIdent_of_Ring {A} (R : #(Ring A)) :=
MIdent_of_Monoid (%Mult_of_Ring R).
Definition MIdent_of_CRing {A} (R : #(CRing A)) :=
MIdent_of_CMonoid (%Mult_of_CRing R).
Definition Zero_of_Ring {A} (R : #(Ring A)) :=
MIdent_of_CGrp (%Add_of_Ring R).
Definition Zero_of_CRing {A} (R : #(CRing A)) :=
MIdent_of_CGrp (Add_of_CRing R).

Theorem MultO_of_Ring_MonoidCond : forall {A} (R : #(Ring A)),
Ope_MonoidCond (MultO_of_Ring R).
Proof.
intros A R.
apply Ope_Monoid.
unfold MultO_of_Ring.
rewrite USETEq.
apply SetProp.
Qed.

Theorem MultO_of_CRing_CMonoidCond : forall {A} (R : #(CRing A)),
Ope_CMonoidCond (MultO_of_CRing R).
Proof.
intros A R.
apply Ope_CMonoid.
unfold MultO_of_CRing.
rewrite USETEq.
apply SetProp.
Qed.

Theorem AddO_of_Ring_CGrpCond : forall {A} (R : #(Ring A)),
Ope_CGrpCond (AddO_of_Ring R).
Proof.
intros A R.
apply Ope_CGrp.
unfold AddO_of_Ring.
rewrite USETEq.
apply SetProp.
Qed.

Theorem AddO_of_CRing_CGrpCond : forall {A} (R : #(CRing A)),
Ope_CGrpCond (AddO_of_CRing R).
Proof.
intros A R.
apply Ope_CGrp.
unfold AddO_of_CRing.
rewrite USETEq.
apply SetProp.
Qed.


Theorem Mult_of_RingEqWP : forall {A} (o1 : #(BOperation A)) (o2 : #(BOperation A)) (cond : In [o1;o2] (Ring A)),
%Mult_of_Ring {[o1 ; o2] ! cond} == o2.
Proof.
intros A o1 o2 cond.
unfold Mult_of_Ring.
apply RelationAsPairREqWP.
Qed.
Theorem Mult_of_CRingEqWP : forall {A} (o1 : #(BOperation A)) (o2 : #(BOperation A)) (cond : In [o1;o2] (CRing A)),
%Mult_of_CRing {[o1 ; o2] ! cond} == o2.
Proof.
intros A o1 o2 cond.
unfold Mult_of_CRing.
apply RelationAsPairREqWP.
Qed.
Theorem Add_of_RingEqWP : forall {A} (o1 : #(BOperation A)) (o2 : #(BOperation A)) (cond : In [o1;o2] (Ring A)),
%Add_of_Ring {[o1 ; o2] ! cond} == o1.
Proof.
intros A o1 o2 cond.
unfold Add_of_Ring.
apply RelationAsPairLEqWP.
Qed.
Theorem Add_of_CRingEqWP : forall {A} (o1 : #(BOperation A)) (o2 : #(BOperation A)) (cond : In [o1;o2] (CRing A)),
Add_of_CRing {[o1 ; o2] ! cond} == o1.
Proof.
intros A o1 o2 cond.
unfold Add_of_CRing.
assert(InP : In [o1;o2] (Ring A)).
 apply CRing_Ring.
 apply cond.
apply (TransitivityEq (%Add_of_Ring {_ ! InP})).
 hyperreflexivity.
apply Add_of_RingEqWP.
Qed.


Theorem Mult_of_CRing_Ring : forall {A},
StrongRel (@Mult_of_CRing A){<Map_Rel} (@Mult_of_Ring A){<Map_Rel}.
Proof.
intro A.
apply ToMapStrong.
apply CRing_Ring.
intros CR R EqRC.
put (IsPair'Relation _ _ _ _ (SetProp R)) EqR.
destruct EqR as [o1 EqR].
destruct EqR as [o2 EqR].
put (IsPair'Relation _ _ _ _ (SetProp CR)) EqCR.
destruct EqCR as [o'1 EqCR].
destruct EqCR as [o'2 EqCR].
assert(EqR' : R == [o1{<CGrp_Ope} ; o2{<Monoid_Ope}]).
 rewrite EqR.
 hyperreflexivity.
assert(EqCR' : CR == [o'1{<CGrp_Ope} ; o'2{<CMonoid_Ope}]).
 rewrite EqCR.
 hyperreflexivity.
assert(InR : In [o1{<CGrp_Ope};o2{<Monoid_Ope}] (Ring A)).
 rewrite <- EqR'.
 apply SetProp.
assert(InCR : In [o'1{<CGrp_Ope};o'2{<CMonoid_Ope}] (CRing A)).
 rewrite <- EqCR'.
 apply SetProp.
apply (TransitivityEq (%Mult_of_CRing {_ ! InCR})).
 apply MapArgEq.
 apply EqCR.
apply (TransitivityEq o'2).
 apply (Mult_of_CRingEqWP _ _ InCR).
apply SymmetryEq.
apply (TransitivityEq (%Mult_of_Ring {_ ! InR})).
 apply MapArgEq.
 apply EqR.
apply (TransitivityEq o2).
 apply (Mult_of_RingEqWP _ _ InR).
cut ([o1;o2] == [o'1;o'2]).
 intro EqP.
 apply EqualInPair' in EqP.
 apply (proj2 EqP).
rewrite <- EqR.
rewrite <- EqCR.
apply SymmetryEq.
apply EqRC.
Qed.


Definition AddMult_of_RingDistDond : forall {A} (R : #(Ring A)),
Ope2_DistDond (AddO_of_Ring R) (MultO_of_Ring R).
Proof.
intros A R.
apply Ope2_Dist.
cut (R == [AddO_of_Ring R ; MultO_of_Ring R]).
 intro Eq.
 rewrite <- Eq.
 apply Ring_Dist.
 apply SetProp.
assert(InRB : In R (BOperation2 A)).

 apply Ring_Ope2.
 apply SetProp.
put (CartesianIsPair' _ _ _ InRB) EqR.
destruct EqR as [o1 EqR].
destruct EqR as [o2 EqR].
assert(cond : In [o1;o2] (Ring A)).
 rewrite <- EqR.
 apply SetProp.
assert(EqRC : R == {[o1;o2] ! cond}).
 rewrite EqR.
 hyperreflexivity.
rewrite EqR.
apply EqualInPair'.
split.
 apply SymmetryEq.
 unfold AddO_of_Ring.
 rewrite (USETEq _ CGrp_Ope).
 rewrite (MapArgEq _ EqRC).
 apply Add_of_RingEqWP.

 apply SymmetryEq.
 unfold MultO_of_Ring.
 rewrite (USETEq _ Monoid_Ope).
 rewrite (MapArgEq _ EqRC).
 apply Mult_of_RingEqWP.
Qed.

Definition AddMult_of_CRingDistDond : forall {A} (R : #(CRing A)),
Ope2_DistDond (AddO_of_CRing R) (MultO_of_CRing R).
Proof.
intros A R.
apply Ope2_Dist.
cut (In [AddO_of_Ring (R{<CRing_Ring}) ; MultO_of_Ring (R{<CRing_Ring})] (Distribute A)).
 apply Arrow2Rewrite.
  apply EqualInPair'.
  split.
  hyperreflexivity.
  apply SymmetryEq.
  unfold MultO_of_CRing.
  unfold MultO_of_Ring.
  rewrite (USETEq _ CMonoid_Ope).
  rewrite (USETEq _ Monoid_Ope).
  apply MapStrong.
  apply Mult_of_CRing_Ring.
  hyperreflexivity.
 hyperreflexivity.
apply Ope2_Dist.
apply AddMult_of_RingDistDond.
Qed.

Definition Minus_of_Ring {A} : #(Map (Ring A) (Map A A)) :=
%CombineMap' [%CombineMap' [Add_of_Ring ; EmbedMap (CGrp_Grp)] ; MInvert_of_Grp].

Theorem Minus_of_RingTheorem : forall {A} (R : #(Ring A)) (a : #A),
&&(%IsInverseE (AddO_of_Ring R)) a (%(%Minus_of_Ring R) a).
Proof.
intros A R a.
generalize (MInvert_of_GrpTheorem ((%Add_of_Ring R){<CGrp_Grp}) a).
apply RelRewriteAll.
 hyperreflexivity.
 apply MapEq.
 unfold Minus_of_Ring.
 rewrite CombineMap'Theorem.
 apply MapArgEq.
 rewrite (USETEq _ CGrp_Grp).
 rewrite CombineMap'Theorem.
 rewrite EmbedMapEq.
 hyperreflexivity.
unfold IsInverseE_of_Grp.
apply MapArgEq.
hyperreflexivity.
Qed.

Theorem IsIdent_Ident_of_Ring : forall {A} (R : #(Ring A)),
&&IsIdent (MultO_of_Ring R) (MIdent_of_Ring R).
Proof.
intros A R .
unfold MIdent_of_Ring.
unfold MultO_of_Ring.
generalize (MIdentTheorem ((%Mult_of_Ring R){<Monoid_Ident})).
apply RelRewriteL.
hyperreflexivity.
Qed.

Theorem IsIdent_Zero_of_Ring : forall {A} (R : #(Ring A)),
&&IsIdent (AddO_of_Ring R) (Zero_of_Ring R).
Proof.
intros A R .
unfold Zero_of_Ring.
unfold AddO_of_Ring.
generalize (MIdentTheorem ((%Add_of_Ring R){<CGrp_Ident})).
apply RelRewriteL.
hyperreflexivity.
Qed.

Theorem Zero_of_Ring_IsZero : forall {A} (R : #Ring A),
&&IsZero (MultO_of_Ring R) (Zero_of_Ring R).
Proof.
intros A R.
apply IsZeroTheorem.
intro a.
set (Zero_of_Ring R) as z.
set (MIdent_of_Ring R) as e.
set (MultO_of_Ring R) as mult.
set (AddO_of_Ring R) as add.
assert(AssA : Ope_SGrpCond add).
 apply Ope_SGrp.
 unfold add.
 unfold AddO_of_Ring.
 rewrite (USETEq _ CGrp_Ope).
 apply CGrp_SGrp.
 apply SetProp.
put (Minus_of_RingTheorem R a) InvH.
apply IsInverseETheorem in InvH.
destruct InvH as [InvH1 InvH2].
assert(dist : Ope2_DistDond add mult).
 apply AddMult_of_RingDistDond. 
split.
 cut (%add [%mult [z;a];a] == a).
  intro EqH.
  apply (TransitivityEq (%add [%mult [z;a] ; %add[a; %(%Minus_of_Ring R) a]])).
   apply SymmetryEq.
   apply IsRightIdentTheorem.
   apply IsIdent_RightIdent.
   apply InvH1.
  rewrite <- AssA.
  rewrite (MapArgEq _ (EqualInPair'L _ _ _ _ _ EqH)).
  unfold z.
  unfold Zero_of_Ring.
  apply SymmetryEq.
  unfold MIdent_of_CGrp.
  apply MIdentEq.
  apply InvH1.
 apply (TransitivityEq (%add [%mult [z;a] ; %mult[e;a]])).
  apply MapArgEq.
  apply EqualInPair'R.
  apply SymmetryEq.
  apply IsLeftIdentTheorem.
  apply IsIdent_LeftIdent.
  apply IsIdent_Ident_of_Ring.
 rewrite <- (proj2 (dist _ _ _)).
 apply (TransitivityEq (%mult [e;a])).
  apply MapArgEq.
  apply EqualInPair'L.
  apply IsLeftIdentTheorem.
  apply IsIdent_LeftIdent.
  apply IsIdent_Zero_of_Ring.
 apply IsLeftIdentTheorem.
 apply IsIdent_LeftIdent.
 apply IsIdent_Ident_of_Ring.

 cut (%add [%mult [a;z];a] == a).
  intro EqH.
  apply (TransitivityEq (%add [%mult [a;z] ; %add[a; %(%Minus_of_Ring R) a]])).
   apply SymmetryEq.
   apply IsRightIdentTheorem.
   apply IsIdent_RightIdent.
   apply InvH1.
  rewrite <- AssA.
  rewrite (MapArgEq _ (EqualInPair'L _ _ _ _ _ EqH)).
  unfold z.
  unfold Zero_of_Ring.
  apply SymmetryEq.
  unfold MIdent_of_CGrp.
  apply MIdentEq.
  apply InvH1.
 apply (TransitivityEq (%add [%mult [a;z] ; %mult[a;e]])).
  apply MapArgEq.
  apply EqualInPair'R.
  apply SymmetryEq.
  apply IsRightIdentTheorem.
  apply IsIdent_RightIdent.
  apply IsIdent_Ident_of_Ring.
 rewrite <- (proj1 (dist _ _ _)).
 apply (TransitivityEq (%mult [a;e])).
  apply MapArgEq.
  apply EqualInPair'R.
  apply IsLeftIdentTheorem.
  apply IsIdent_LeftIdent.
  apply IsIdent_Zero_of_Ring.
 apply IsRightIdentTheorem.
 apply IsIdent_RightIdent.
 apply IsIdent_Ident_of_Ring.
Qed.

Theorem IsIdent_Ident_of_CRing : forall {A} (R : #(CRing A)),
&&IsIdent (MultO_of_CRing R) (MIdent_of_CRing R).
Proof.
intros A R .
unfold MIdent_of_CRing.
unfold MultO_of_CRing.
generalize (MIdentTheorem ((%Mult_of_CRing R){<CMonoid_Ident})).
apply RelRewriteL.
hyperreflexivity.
Qed.

Theorem IsIdent_Zero_of_CRing : forall {A} (R : #(CRing A)),
&&IsIdent (AddO_of_CRing R) (Zero_of_CRing R).
Proof.
intros A R .
unfold Zero_of_CRing.
unfold AddO_of_CRing.
generalize (MIdentTheorem ((Add_of_CRing R){<CGrp_Ident})).
apply RelRewriteL.
hyperreflexivity.
Qed.

Theorem Zero_of_CRing_IsZero : forall {A} (R : #CRing A),
&&IsZero (MultO_of_CRing R) (Zero_of_CRing R).
Proof.
intros A R.
generalize (Zero_of_Ring_IsZero (R{<CRing_Ring})).
apply IsZero_StrongCons.
 hyperreflexivity.
apply ReflexivityStrongRel2.
rewrite USETEq.
rewrite USETEq.
unfold MultO_of_CRing.
unfold MultO_of_Ring.
rewrite USETEq.
rewrite USETEq.
apply MapStrong.
apply Mult_of_CRing_Ring.
hyperreflexivity.
Qed.


(*****************)
(* Fraction Ring *)
(*****************)

Definition FractionRing {A} (R : #(CRing A)) (S : #(SubCMonoid (%Mult_of_CRing R))) :=
FractionCMonoidSet (%Mult_of_CRing R) S.

Definition FractionRingOpe {A} (R : #(CRing A)) (S : #(SubCMonoid (%Mult_of_CRing R))) : #(BOperation (FractionRing R S)) :=
FractionCMonoid (%Mult_of_CRing R) S.

Definition Fraction_of_Ring {A} (R : #(CRing A)) (S : #(SubCMonoid (%Mult_of_CRing R))) : #(Map (Cartesian A S) (FractionRing R S)) :=
to_FractionCMonoidSet (%Mult_of_CRing R) S.

Definition FractionRingCannProj {A} (R : #(CRing A)) (S : #(SubCMonoid (%Mult_of_CRing R))) : #(Map A (FractionRing R S))
:=
FractionCMonoidCannProj _ _.

Theorem FractionRingIn : forall {A} (R : #(CRing A)) (S : #(SubCMonoid (%Mult_of_CRing R))),
forall (x : #(FractionRing R S)),
exists a : #A, exists p : #S,
x == %(Fraction_of_Ring R S) [a;p].
Proof.
intros A R S x.
unfold Fraction_of_Ring.
apply FractionCMonoidSetIn.
Qed.

Theorem FractionRingEq : forall {A} (R : #(CRing A)) (S : #(SubCMonoid (%Mult_of_CRing R))) (a b : #A) (p q : #S),
%(Fraction_of_Ring R S) [a;p] == %(Fraction_of_Ring R S) [b;q] <->
exists s : #S, 
%(MultO_of_CRing R) [%(MultO_of_CRing R) [a;q{<SubCMonoid_S}] ; s{<SubCMonoid_S}] == 
%(MultO_of_CRing R) [%(MultO_of_CRing R) [b;p{<SubCMonoid_S}] ; s{<SubCMonoid_S}].
Proof.
intros A R S a b p q.
unfold Fraction_of_Ring.
set (MultO_of_CRing R) as m.
set ((%Mult_of_CRing R){<CMonoid_Ope}) as m'.
assert(EqM : m == m').
 hyperreflexivity.
split.
 intro HH.
 apply to_FractionCMonoidSetEq in HH.
 destruct HH as [s HH].
 exists s.
 apply (TransitivityEq (%m' [%m' [a;q{<SubCMonoid_S}] ; s{<SubCMonoid_S}])).
  apply MapEqAll.
   apply EqualInPair'L.
   apply MapEq.
   apply EqM.
  apply EqM.
 apply (TransitivityEq (%m' [%m' [b;p{<SubCMonoid_S}] ; s{<SubCMonoid_S}])).
  apply HH.
 apply SymmetryEq.
 apply MapEqAll.
  apply EqualInPair'L.
  apply MapEq.
  apply EqM.
 apply EqM.

 intro cond.
 destruct cond as [s cond].
 apply to_FractionCMonoidSetEq.
 exists s.
 apply (TransitivityEq (%m [%m [a;q{<SubCMonoid_S}];s{<SubCMonoid_S}])).
  apply SymmetryEq.
  apply MapEqAll.
   apply EqualInPair'L.
   apply MapEq.
   apply EqM.
  apply EqM.
 rewrite cond.
 apply MapEqAll.
  apply EqualInPair'L.
  apply MapEq.
  apply EqM.
 apply EqM.
Qed.

Theorem FractionRingEqSame : forall {A} (R : #(CRing A)) (S : #(SubCMonoid (%Mult_of_CRing R))) (a b : #A) (p q : #S),
b == q ->
%(Fraction_of_Ring R S) [a;p] == 
%(Fraction_of_Ring R S) [%(MultO_of_CRing R) [a;b] ; %(SubCMonoid_to_Ope S) [p;q]].
Proof.
intros A R S a b p q Eqpq.
unfold Fraction_of_Ring at 1.
rewrite (to_FractionCMonoidSetEqSame _ _ _ _ _ _ Eqpq).
unfold Fraction_of_Ring.
apply MapArgEq.
apply EqualInPair'L.
apply MapEq.
apply (TransitivityEq (%Mult_of_CRing R)).
 hyperreflexivity.
hyperreflexivity.
Qed.

Theorem FractionRing_Ope_CommCond : forall {A} (R : #(CRing A)) (S : #(SubCMonoid (%Mult_of_CRing R))),
Ope_CommCond (FractionRingOpe R S).
Proof.
intros A cm S.
unfold FractionRingOpe.
apply FractionCMonoid_Ope_CommCond.
Qed.

Theorem FractionRing_Ope_SGrpCond : forall {A} (R : #(CRing A)) (S : #(SubCMonoid (%Mult_of_CRing R))),
Ope_SGrpCond (FractionRingOpe R S).
Proof.
intros A cm S.
unfold FractionRingOpe.
apply FractionCMonoid_Ope_SGrpCond.
Qed.


Theorem FractionRingTheorem : forall {A} (R : #(CRing A)) (S : #(SubCMonoid (%Mult_of_CRing R))) a b p q,
%(FractionRingOpe R S) [%(Fraction_of_Ring R S) [a;p] ; %(Fraction_of_Ring R S) [b;q]] ==
%(Fraction_of_Ring R S) [%(MultO_of_CRing R) [a;b] ; %(SubCMonoid_to_Ope S) [p;q]].
Proof.
intros A R S.
intros a b p q.
unfold FractionRingOpe.
unfold Fraction_of_Ring.
apply (TransitivityEq _  (FractionCMonoidTheorem (%Mult_of_CRing R) S a b p q)).
apply MapArgEq.
apply EqualInPair'L.
apply MapEq.
apply (TransitivityEq (%Mult_of_CRing R)).
 hyperreflexivity.
unfold MultO_of_CRing.
hyperreflexivity.
Qed.

Theorem FractionRingCannProjTheorem : forall {A} (R : #(CRing A)) (S : #(SubCMonoid (%Mult_of_CRing R))) (a : #A),
%(FractionRingCannProj R S) a ==
%(Fraction_of_Ring R S) [a;(MIdent_of_CMonoid (Sub_to_CMonoid S))].
Proof.
intros A R S a.
unfold FractionRingCannProj.
rewrite (FractionCMonoidCannProjTheorem (%Mult_of_CRing R)).
unfold Fraction_of_Ring.
hyperreflexivity.
Qed.

Theorem FractionRingCannProj_Hom : forall {A} (R : #(CRing A)) (S : #(SubCMonoid (%Mult_of_CRing R))),
&&IsHomomorphism_of_BOpe [MultO_of_CRing R ; FractionRingOpe R S] (FractionRingCannProj R S).
Proof.
intros a R S.
unfold FractionRingOpe.
unfold FractionRingCannProj.
assert(EqRM : (%Mult_of_CRing R){<CMonoid_Ope} == MultO_of_CRing R).
 hyperreflexivity.
apply (RelRewriteL (EqualInPair'L _ _ _ _ _ EqRM)).
apply FractionCMonoidCannProj_Hom.
Qed.

Theorem FractionRingCannProj_IsIdent : forall {A} (R : #(CRing A)) (S : #(SubCMonoid (%Mult_of_CRing R))) e,
&&IsIdent (MultO_of_CRing R) e -> 
&&IsIdent (FractionRingOpe R S) (%(FractionRingCannProj R S) e).
Proof.
intros A R S e IH.
unfold FractionRingOpe.
unfold FractionRingCannProj.
apply FractionCMonoidCannProj_IsIdent.
generalize IH.
apply RelRewriteL.
hyperreflexivity.
Qed.

Theorem FractionRingCannProj_HomIdent : forall {A} (R : #(CRing A)) (S : #(SubCMonoid (%Mult_of_CRing R))),
&&IsHomomorphism_of_Ident [MultO_of_CRing R ; FractionRingOpe R S] (FractionRingCannProj R S).
Proof.
intros A R S.
apply IsHomomorphism_of_IdentTheorem.
split.
apply FractionRingCannProj_Hom.
apply FractionRingCannProj_IsIdent.
Qed.

Theorem FractionRing_Ope_IdentCond : forall {A} (R : #(CRing A)) (S : #(SubCMonoid (%Mult_of_CRing R))),
Ope_IdentCond (FractionRingOpe R S).
Proof.
intros A R S.
exists (%(FractionRingCannProj R S) (MIdent_of_CRing R)).
apply FractionRingCannProj_IsIdent.
apply IsIdent_Ident_of_CRing.
Qed.

Theorem FractionRing_Ope_MonoidCond : forall {A} (R : #(CRing A)) (S : #(SubCMonoid (%Mult_of_CRing R))),
Ope_MonoidCond (FractionRingOpe R S).
Proof.
intros A R S.
split.
apply FractionRing_Ope_SGrpCond.
apply FractionRing_Ope_IdentCond.
Qed.

Theorem FractionRing_Ope_CMonoidCond : forall {A} (R : #(CRing A)) (S : #(SubCMonoid (%Mult_of_CRing R))),
Ope_CMonoidCond (FractionRingOpe R S).
Proof.
intros A R S.
split.
apply FractionRing_Ope_MonoidCond.
apply FractionRing_Ope_CommCond.
Qed.

Theorem FractionRingCannProj_IsInvertible : forall {A} (R : #(CRing A)) (S : #(SubCMonoid (%Mult_of_CRing R))) (a : #A),
&&IsInvertible (MultO_of_CRing R) a -> 
&&IsInvertible (FractionRingOpe R S) (%(FractionRingCannProj R S) a).
Proof.
intros A R S a.
intro HH.
apply FractionCMonoidCannProj_IsInvertible.
apply HH.
Qed.

Theorem FractionRingCannProj_IsInvertibleS : forall {A} (R : #(CRing A)) (S : #(SubCMonoid (%Mult_of_CRing R))) (a : #A),
In a S ->
&&IsInvertible (FractionRingOpe R S) (%(FractionRingCannProj R S) a).
Proof.
intros A R S a InaS.
apply FractionCMonoidCannProj_IsInverseS.
apply InaS.
Qed.

Theorem FractionRingCannProj_is_Invertible : forall {A} (R : #(CRing A)) (S : #(SubCMonoid (%Mult_of_CRing R))) (a : #A),
In a S ->
In (%(FractionRingCannProj R S) a) (%Invertible (FractionRingOpe R S)).
Proof.
intros A R S a InaS.
apply InvertibleTheorem.
apply FractionRingCannProj_IsInvertibleS.
apply InaS.
Qed.



(* add *)
Theorem FrationRingAddMapCond : forall {A} (R : #(CRing A)) (S : #(SubCMonoid (%Mult_of_CRing R))), Rel_MapCond (
  MakeRelation (fun (xy : #(Cartesian (FractionRing R S) (FractionRing R S))) (z : #(FractionRing R S)) =>
    forall (a b : #A) (p q : #S), (%MLeft xy) == (%(Fraction_of_Ring R S) [a;p]) /\ (%MRight xy) == (%(Fraction_of_Ring R S) [b;q]) ->
      z == %(Fraction_of_Ring R S) [%(AddO_of_CRing R) [%(MultO_of_CRing R) [a;q{<SubCMonoid_S}] ; %(MultO_of_CRing R) [b;p{<SubCMonoid_S}]] ; %(SubCMonoid_to_Ope S) [p;q]]
  )
).
Proof.
intros A R S.
intro xy.
put (CartesianIsPair' _ _ _ (SetProp xy)) Eqxy.
destruct Eqxy as [x Eqxy].
destruct Eqxy as [y Eqxy].
set (AddO_of_CRing R) as plus.
set (MultO_of_CRing R) as mult.
set (SubCMonoid_to_Ope S) as smult.
assert(CGrp_plus : Ope_CGrpCond plus).
 apply Ope_CGrp.
 unfold plus.
 unfold AddO_of_CRing.
 rewrite (USETEq _ CGrp_Ope).
 apply SetProp.
assert(CMonoid_mult : Ope_CMonoidCond mult).
 apply Ope_CMonoid.
 unfold mult.
 unfold MultO_of_CRing.
 rewrite (USETEq _ CMonoid_Ope).
 apply SetProp.
assert(Distcond : Ope2_DistDond plus mult).
 apply AddMult_of_CRingDistDond.
assert(smultmult : StrongRel (smult{<Map_Rel}) (mult{<Map_Rel})).
 unfold smult.
 unfold mult.
 unfold SubCMonoid_to_Ope.
 apply (StrongSubBOpe _ _ (S{<SubCMonoid_SubOpe})).
 apply ReflexivityStrongRel2.
 hyperreflexivity.
put (FractionRingIn _ _ x) Eqx.
destruct Eqx as [a Eqx].
destruct Eqx as [p Eqx].
put (FractionRingIn _ _ y) Eqy.
destruct Eqy as [b Eqy].
destruct Eqy as [q Eqy].
set (p{<SubCMonoid_S}) as pA.
set (q{<SubCMonoid_S}) as qA.

split.

 exists (%(Fraction_of_Ring R S) [%plus [%mult [a;qA] ; %mult [b;pA]] ; %smult [p;q]]).
 apply MakeRelationTheorem.
 intros xy' z' Eqxyxy' Eqz.
 intros a' b' p' q' xy'Eq.
 destruct xy'Eq as [EqxyL' EqxyR'].
 assert(Eqap : %(Fraction_of_Ring R S) [a;p] == %(Fraction_of_Ring R S) [a';p']).
  rewrite <- Eqx.
  apply (TransitivityEq (%MLeft [x;y])).
   apply SymmetryEq.
   apply LeftPairTheorem.
  rewrite <- (MapArgEq _ Eqxy).
  rewrite (MapArgEq _ Eqxyxy').
  apply EqxyL'.
 assert(Eqbq : %(Fraction_of_Ring R S) [b;q] == %(Fraction_of_Ring R S) [b';q']).
  rewrite <- Eqy.
  apply (TransitivityEq (%MRight [x;y])).
   apply SymmetryEq.
   apply RightPairTheorem.
  rewrite <- (MapArgEq _ Eqxy).
  rewrite (MapArgEq _ Eqxyxy').
  apply EqxyR'.
 apply FractionRingEq in Eqap.
 destruct Eqap as [s Eqap'].
 apply FractionRingEq in Eqbq.
 destruct Eqbq as [t Eqbq'].
 set (p'{<SubCMonoid_S}) as pA'.
 set (q'{<SubCMonoid_S}) as qA'.
 set (s{<SubCMonoid_S}) as sA.
 set (t{<SubCMonoid_S}) as tA.
 assert(Eqab : %mult [%mult [a;pA'];sA] == %mult [%mult [a';pA];sA]).
  apply Eqap'.
 assert(Eqbq : %mult [%mult [b;qA'];tA] == %mult [%mult [b';qA];tA]).
  apply Eqbq'.
 clear Eqap'.
 clear Eqbq'.
 rewrite <- Eqz.
 apply FractionRingEq.
 exists (%smult [s;t]).
 apply (TransitivityEq (%mult [%mult [%plus [%mult [a;qA] ; %mult [b;pA]] ; %mult [pA';qA']] ; %mult [sA;tA]])).
  apply MapArgEq.
  apply EqualInPair'.
  split.
   apply MapArgEq.
   apply EqualInPair'R.
   rewrite (USETEq _ SubCMonoid_S).
   apply MapStrong.
    apply smultmult.
   hyperreflexivity.
  rewrite (USETEq _ SubCMonoid_S).
  apply MapStrong.
   apply smultmult.
  hyperreflexivity.
 apply (TransitivityEq (%mult [%mult [%plus [%mult [a';qA'] ; %mult[b';pA']] ; %mult[pA;qA]] ; %mult[sA;tA]])).
  rewrite (MapArgEq _ (EqualInPair'L _ _ _ _ _ (proj2 (Distcond _ _ _)))).
  rewrite (proj2 (Distcond _ _ _)).
  rewrite (MapArgEq _ (EqualInPair'L _ _ _ _ _ (proj2 (Distcond _ _ _)))).
  rewrite (proj2 (Distcond _ _ _)).
  apply MapArgEq.
  apply EqualInPair'.
  assert(Com : Ope_CommCond mult).
   apply Ope_Comm.
   apply CMonoid_Comm.
   apply Ope_CMonoid.
   apply CMonoid_mult.
  assert(SGrp : Ope_SGrpCond mult).
   apply Ope_SGrp.
   apply CMonoid_SGrp.
   apply Ope_CMonoid.
   apply CMonoid_mult.
  split.
   rewrite <- SGrp.
   rewrite <- SGrp.
   apply MapArgEq.
   apply EqualInPair'L.
   rewrite (MapArgEq _ (EqualInPair'L _ _ _ _ _ (SGrp _ _ _))).
   rewrite (MapArgEq _ (EqualInPair'L _ _ _ _ _ (SGrp _ _ _))).
   rewrite <- (MapArgEq _ (EqualInPair'L _ _ _ _ _ (MapArgEq _ (EqualInPair'R _ _ _ _ _ (SGrp _ _ _))))).
   rewrite <- (MapArgEq _ (EqualInPair'L _ _ _ _ _ (MapArgEq _ (EqualInPair'R _ _ _ _ _ (SGrp _ _ _))))).
   rewrite (MapArgEq _ (EqualInPair'L _ _ _ _ _ (MapArgEq _ (EqualInPair'R _ _ _ _ _ (MapArgEq _ (EqualInPair'L _ _ _ _ _ (Com _ _))))))).
   apply SymmetryEq.
   rewrite (MapArgEq _ (EqualInPair'L _ _ _ _ _ (MapArgEq _ (EqualInPair'R _ _ _ _ _ (MapArgEq _ (EqualInPair'L _ _ _ _ _ (Com _ _))))))).
   rewrite (MapArgEq _ (EqualInPair'L _ _ _ _ _ (MapArgEq _ (EqualInPair'R _ _ _ _ _ (SGrp _ _ _))))).
   rewrite (MapArgEq _ (EqualInPair'L _ _ _ _ _ (MapArgEq _ (EqualInPair'R _ _ _ _ _ (SGrp _ _ _))))).
   rewrite <- (MapArgEq _ (EqualInPair'L _ _ _ _ _ (SGrp _ _ _))).
   apply SymmetryEq.
   rewrite <- (MapArgEq _ (EqualInPair'L _ _ _ _ _ (SGrp _ _ _))).
   rewrite SGrp.
   apply SymmetryEq.
   rewrite SGrp.
   rewrite (MapArgEq _ (EqualInPair'R _ _ _ _ _ (Com _ _))).
   apply SymmetryEq.
   rewrite (MapArgEq _ (EqualInPair'R _ _ _ _ _ (Com _ _))).
   rewrite <- SGrp.
   apply SymmetryEq.
   rewrite <- SGrp.
   apply MapArgEq.
   apply EqualInPair'.
   split.
    apply SymmetryEq.
    apply Eqab.
   apply Com.

   rewrite (MapArgEq _ (EqualInPair'R _ _ _ _ _ (Com _ _))).
   apply SymmetryEq.
   rewrite (MapArgEq _ (EqualInPair'R _ _ _ _ _ (Com _ _))).
   rewrite <- SGrp.
   apply SymmetryEq.
   rewrite <- SGrp.
   apply MapArgEq.
   apply EqualInPair'L.
   rewrite (MapArgEq _ (EqualInPair'L _ _ _ _ _ (MapArgEq _ (EqualInPair'R _ _ _ _ _ (Com _ _))))).
   apply SymmetryEq.
   rewrite (MapArgEq _ (EqualInPair'L _ _ _ _ _ (MapArgEq _ (EqualInPair'R _ _ _ _ _ (Com _ _))))).
   rewrite (MapArgEq _ (EqualInPair'L _ _ _ _ _ (SGrp _ _ _))).
   apply SymmetryEq.
   rewrite (MapArgEq _ (EqualInPair'L _ _ _ _ _ (SGrp _ _ _))).
   rewrite (MapArgEq _ (EqualInPair'L _ _ _ _ _ (MapArgEq _ (EqualInPair'R _ _ _ _ _(Com _ _))))).
   apply SymmetryEq.
   rewrite (MapArgEq _ (EqualInPair'L _ _ _ _ _ (MapArgEq _ (EqualInPair'R _ _ _ _ _(Com _ _))))).
   rewrite (MapArgEq _ (EqualInPair'L _ _ _ _ _ (MapArgEq _ (EqualInPair'R _ _ _ _ _ (SGrp _ _ _))))).
   apply SymmetryEq.
   rewrite (MapArgEq _ (EqualInPair'L _ _ _ _ _ (MapArgEq _ (EqualInPair'R _ _ _ _ _ (SGrp _ _ _))))).
   rewrite <- (MapArgEq _ (EqualInPair'L _ _ _ _ _ (SGrp _ _ _))).
   apply SymmetryEq.
   rewrite <- (MapArgEq _ (EqualInPair'L _ _ _ _ _ (SGrp _ _ _))).
   rewrite SGrp.
   apply SymmetryEq.
   rewrite SGrp.
   rewrite (MapArgEq _ (EqualInPair'R _ _ _ _ _ (Com _ _))).
   apply SymmetryEq.
   rewrite (MapArgEq _ (EqualInPair'R _ _ _ _ _ (Com _ _))).
   rewrite <- SGrp.
   apply SymmetryEq.
   rewrite <- SGrp.
   apply MapArgEq.
   apply EqualInPair'.
   split.
    apply Eqbq.
   apply Com.
 apply SymmetryEq.
 apply MapArgEq.
 apply EqualInPair'.
 split.
  apply MapArgEq.
  apply EqualInPair'R.
  rewrite (USETEq _ SubCMonoid_S).
  apply MapStrong.
  apply smultmult.
  hyperreflexivity.
 rewrite (USETEq _ SubCMonoid_S).
 apply MapStrong.
 apply smultmult.
 hyperreflexivity.


intros z1 z2 MHD.
destruct MHD as [MH1 MH2].
put ((proj1 (MakeRelationTheorem _ _ _ _ _)) MH1) MH1'.
clear MH1.
put (MH1' _ _ Eqxy (ReflexivityEq _)) MH1.
clear MH1'.
put ((proj1 (MakeRelationTheorem _ _ _ _ _)) MH2) MH2'.
clear MH2.
put (MH2' _ _ Eqxy (ReflexivityEq _)) MH2.
clear MH2'.
assert(MHCond : %MLeft [x;y] == (%(Fraction_of_Ring R S) [a;p]) /\ %MRight [x;y] == (%(Fraction_of_Ring R S) [b;q])).
 split.
 rewrite LeftPairTheorem.
 apply Eqx.
 rewrite RightPairTheorem.
 apply Eqy.
put (MH1 _ _ _ _ MHCond) MH1'.
put (MH2 _ _ _ _ MHCond) MH2'.
clear MH1.
clear MH2.
rewrite MH1'.
rewrite MH2'.
hyperreflexivity.
Qed.

Definition FractionRingAdd {A} (R : #(CRing A)) (S : #(SubCMonoid (%Mult_of_CRing R))) : #(BOperation (FractionRing R S)) :=
_{<Rel_Map ! FrationRingAddMapCond R S}.

Theorem FractionRingAddTheorem : forall {A} (R : #(CRing A)) (S : #(SubCMonoid (%Mult_of_CRing R))) (a b : #A) (p q : #S),
%(FractionRingAdd R S) [%(Fraction_of_Ring R S) [a;p] ; %(Fraction_of_Ring R S) [b;q]] ==
%(Fraction_of_Ring R S) [ %(AddO_of_CRing R) [ %(MultO_of_CRing R) [a;q{<SubCMonoid_S}] ; %(MultO_of_CRing R) [b;p{<SubCMonoid_S}] ] ; %(SubCMonoid_to_Ope S) [p;q] ].
Proof.
intros A R S a b p q.
assert (AppT : &&(FractionRingAdd R S){<Map_Rel} [%(Fraction_of_Ring R S)[a;p] ; %(Fraction_of_Ring R S)[b;q]] (%(FractionRingAdd R S) [%(Fraction_of_Ring R S)[a;p] ; %(Fraction_of_Ring R S)[b;q]])).
 apply AppTheorem.
put ((proj1 (MakeRelationTheorem _ _ _ _ _)) AppT) AppT'.
clear AppT.
put (AppT' _ _ (ReflexivityEq _) (ReflexivityEq _)) AppT.
clear AppT'.
apply AppT.
split.
apply LeftPairTheorem.
apply RightPairTheorem.
Qed.

Theorem FractionRingAddTheoremSameDeno : forall {A} (R : #(CRing A)) (S : #(SubCMonoid (%Mult_of_CRing R))) (a b : #A) (p : #S),
%(FractionRingAdd R S) [%(Fraction_of_Ring R S) [a;p] ; %(Fraction_of_Ring R S) [b;p]] ==
%(Fraction_of_Ring R S) [ %(AddO_of_CRing R) [a;b] ; p].
Proof.
intros A R S a b p.
rewrite FractionRingAddTheorem.
set (AddO_of_CRing R) as plus.
set (MultO_of_CRing R) as mult.
apply (TransitivityEq (%(Fraction_of_Ring R S) [%mult [%plus [a;b] ; p{<SubCMonoid_S}] ; %(SubCMonoid_to_Ope S) [p;p]])).
 apply MapArgEq.
 apply EqualInPair'L.
 rewrite <- (proj2 (AddMult_of_CRingDistDond R _ _ _)).
 hyperreflexivity.
apply SymmetryEq.
apply FractionRingEqSame.
hyperreflexivity.
Qed.

Theorem FractionRingAdd_CommCond : forall {A} (R : #(CRing A)) (S : #(SubCMonoid (%Mult_of_CRing R))),
Ope_CommCond (FractionRingAdd R S).
Proof.
intros A R S.
intros x y.
put (FractionRingIn _ _ x) Eqx.
destruct Eqx as [a Eqx].
destruct Eqx as [p Eqx].
put (FractionRingIn _ _ y) Eqy.
destruct Eqy as [b Eqy].
destruct Eqy as [q Eqy].
rewrite (MapArgEq _ (EqualInPair'L _ _ _ _ _ Eqx)).
rewrite (MapArgEq _ (EqualInPair'R _ _ _ _ _ Eqy)).
rewrite (MapArgEq _ (EqualInPair'L _ _ _ _ _ Eqy)).
rewrite (MapArgEq _ (EqualInPair'R _ _ _ _ _ Eqx)).
rewrite FractionRingAddTheorem.
rewrite FractionRingAddTheorem.
apply FractionRingEq.
set (MultO_of_CRing R) as mult.
set (AddO_of_CRing R) as add.
set (SubCMonoid_to_Ope S) as smult.
exists p.
apply MapArgEq.
apply EqualInPair'L.
apply MapArgEq.
apply EqualInPair'.
assert(smultmult : StrongRel (smult{<Map_Rel}) (mult{<Map_Rel})).
 unfold smult.
 unfold mult.
 unfold SubCMonoid_to_Ope.
 apply (StrongSubBOpe _ _ (S{<SubCMonoid_SubOpe})).
 apply ReflexivityStrongRel2.
 hyperreflexivity.
split.
 cut (Ope_CommCond add).
  intro cond.
  apply cond.
 apply Ope_Comm.
 cut ((Add_of_CRing R) == add).
  intro ew.
  rewrite <- ew.
  apply CGrp_Comm.
  apply SetProp.
 hyperreflexivity.
apply (TransitivityEq (%mult [q{<SubCMonoid_S} ; p{<SubCMonoid_S}])).
 rewrite (USETEq _ SubCMonoid_S).
 apply MapStrong.
 apply smultmult.
 hyperreflexivity.
apply (TransitivityEq (%mult [p{<SubCMonoid_S} ; q{<SubCMonoid_S}])).
 cut (Ope_CommCond mult).
  intro cond.
  apply cond.
 apply Ope_Comm.
 apply CMonoid_Comm.
 cut ((%Mult_of_CRing R) == mult).
  intro ew.
  rewrite <- ew.
  apply SetProp.
 hyperreflexivity.
apply SymmetryEq.
rewrite (USETEq _ SubCMonoid_S).
apply MapStrong.
apply smultmult.
hyperreflexivity.
Qed.

Theorem FractionRingAdd_SGrpCond : forall {A} (R : #(CRing A)) (S : #(SubCMonoid (%Mult_of_CRing R))),
Ope_SGrpCond (FractionRingAdd R S).
Proof.
intros A R S.
intros x y z.
put (FractionRingIn _ _ x) Eqx.
destruct Eqx as [a Eqx].
destruct Eqx as [p Eqx].
put (FractionRingIn _ _ y) Eqy.
destruct Eqy as [b Eqy].
destruct Eqy as [q Eqy].
put (FractionRingIn _ _ z) Eqz.
destruct Eqz as [c Eqz].
destruct Eqz as [r Eqz].
rewrite (MapArgEq _ (EqualInPair'L _ _ _ _ _ (MapArgEq _ (EqualInPair'L _ _ _ _ _ Eqx)))).
rewrite (MapArgEq _ (EqualInPair'L _ _ _ _ _ (MapArgEq _ (EqualInPair'R _ _ _ _ _ Eqy)))).
rewrite (MapArgEq _ (EqualInPair'R _ _ _ _ _ Eqz)).
rewrite (MapArgEq _ (EqualInPair'L _ _ _ _ _ Eqx)).
rewrite (MapArgEq _ (EqualInPair'R _ _ _ _ _ (MapArgEq _ (EqualInPair'L _ _ _ _ _ Eqy)))).
rewrite (MapArgEq _ (EqualInPair'R _ _ _ _ _ (MapArgEq _ (EqualInPair'R _ _ _ _ _ Eqz)))).
rewrite (MapArgEq _ (EqualInPair'L _ _ _ _ _ (FractionRingAddTheorem _ _ _ _ _ _))).
rewrite (MapArgEq _ (EqualInPair'R _ _ _ _ _ (FractionRingAddTheorem _ _ _ _ _ _))).
rewrite FractionRingAddTheorem.
rewrite FractionRingAddTheorem.
apply FractionRingEq.
exists p.
apply MapArgEq.
apply EqualInPair'L.
set (MultO_of_CRing R) as mult.
set (AddO_of_CRing R) as add.
set (SubCMonoid_to_Ope S) as smult.
assert(CGrp_plus : Ope_CGrpCond add).
 apply Ope_CGrp.
 unfold add.
 unfold AddO_of_CRing.
 rewrite (USETEq _ CGrp_Ope).
 apply SetProp.
assert(CMonoid_mult : Ope_CMonoidCond mult).
 apply Ope_CMonoid.
 unfold mult.
 unfold MultO_of_CRing.
 rewrite (USETEq _ CMonoid_Ope).
 apply SetProp.
assert(Distcond : Ope2_DistDond add mult).
 apply AddMult_of_CRingDistDond.
assert(smultmult : StrongRel (smult{<Map_Rel}) (mult{<Map_Rel})).
 unfold smult.
 unfold mult.
 unfold SubCMonoid_to_Ope.
 apply (StrongSubBOpe _ _ (S{<SubCMonoid_SubOpe})).
 apply ReflexivityStrongRel2.
 hyperreflexivity.
assert(SGrp_mult : Ope_SGrpCond mult).
 apply Ope_SGrp.
 apply CMonoid_SGrp.
 apply Ope_CMonoid.
 apply CMonoid_mult.
assert(Com_mult : Ope_CommCond mult).
 apply Ope_Comm.
 apply CMonoid_Comm.
 apply Ope_CMonoid.
 apply CMonoid_mult.
assert(SGrp_add : Ope_SGrpCond add).
 apply Ope_SGrp.
 apply CGrp_SGrp.
 apply Ope_CGrp.
 apply CGrp_plus.
apply MapArgEq.
apply EqualInPair'.
split.
 rewrite (MapArgEq _ (EqualInPair'L _ _ _ _ _ (proj2 (Distcond _ _ _)))).
 rewrite SGrp_add.
 apply MapArgEq.
 apply EqualInPair'.
 split.
  rewrite SGrp_mult.
  apply MapArgEq.
  apply EqualInPair'R.
  rewrite (USETEq _ SubCMonoid_S).
  apply SymmetryEq.
  apply MapStrong.
   apply smultmult.
  hyperreflexivity.
 rewrite (proj2 (Distcond _ _ _)).
 apply MapArgEq.
 apply EqualInPair'.
 split.
  rewrite SGrp_mult.
  apply SymmetryEq.
  rewrite SGrp_mult.
  apply MapArgEq.
  apply EqualInPair'R.
  apply Com_mult.
 apply SymmetryEq.
 rewrite SGrp_mult.
 apply MapArgEq.
 apply EqualInPair'R.
 rewrite Com_mult.
 apply SymmetryEq.
 rewrite (USETEq _ SubCMonoid_S).
 apply MapStrong.
 apply smultmult.
 hyperreflexivity.
apply (TransitivityEq (%mult [p{<SubCMonoid_S} ; %mult [q{<SubCMonoid_S};r{<SubCMonoid_S}]])).
 rewrite (USETEq _ SubCMonoid_S).
 apply MapStrong.
 apply smultmult.
 apply EqualInPair'.
 split.
 hyperreflexivity.
 apply MapStrong.
 apply smultmult.
 hyperreflexivity.
rewrite <- SGrp_mult.
apply SymmetryEq.
rewrite (USETEq _ SubCMonoid_S).
apply MapStrong.
apply smultmult.
apply EqualInPair'.
split.
 apply MapStrong.
 apply smultmult.
 hyperreflexivity.
hyperreflexivity.
Qed.


Theorem FractionRingAddIsIdent_nume0 : forall {A} (R : #(CRing A)) (S : #(SubCMonoid (%Mult_of_CRing R))) (p : #S), 
&&IsIdent (FractionRingAdd R S) (%(Fraction_of_Ring R S) [Zero_of_CRing R ; p]).
Proof.
intros A R S p.
apply IsIdentTheoremL.
apply FractionRingAdd_CommCond.
intros x.
put (FractionRingIn _ _ x) Eqx.
destruct Eqx as [a Eqx].
destruct Eqx as [q Eqx].
rewrite (MapArgEq _ (EqualInPair'R _ _ _ _ _ Eqx)).
rewrite FractionRingAddTheorem.
rewrite Eqx.
apply FractionRingEq.
set (MultO_of_CRing R) as mult.
set (AddO_of_CRing R) as add.
set (q{<SubCMonoid_S}) as qA.
set (p{<SubCMonoid_S}) as pA.
set (Zero_of_CRing R) as z.
exists p.
apply MapArgEq.
apply EqualInPair'L.
apply (TransitivityEq (%mult [%add [z;%mult[a;pA]];qA])).
 apply MapArgEq.
 apply EqualInPair'L.
 apply MapArgEq.
 apply EqualInPair'L.
 apply IsLeftZeroTheorem.
 apply IsZero_LeftZero.
 apply Zero_of_CRing_IsZero.
apply (TransitivityEq (%mult [%mult[a;pA];qA])).
 apply MapArgEq.
 apply EqualInPair'L.
 apply IsLeftIdentTheorem.
 apply IsIdent_LeftIdent.
 apply IsIdent_Zero_of_CRing.
apply (TransitivityEq (%mult [a; %mult[pA;qA]])).
 cut (Ope_SGrpCond mult).
  intro cond.
  apply cond.
 apply Ope_SGrp.
 apply CMonoid_SGrp.
 apply Ope_CMonoid.
 apply MultO_of_CRing_CMonoidCond.
apply MapArgEq.
apply EqualInPair'R.
apply SymmetryEq.
rewrite USETEq.
apply MapStrong.
 unfold SubCMonoid_to_Ope.
 apply (StrongSubBOpe _ _ (S{<SubCMonoid_SubOpe})).
 apply ReflexivityStrongRel2.
 hyperreflexivity.
hyperreflexivity.
Qed.

Theorem FractionRingAddIsIdent_0 : forall {A} (R : #(CRing A)) (S : #(SubCMonoid (%Mult_of_CRing R))), 
&&IsIdent (FractionRingAdd R S) (%(FractionRingCannProj R S) (Zero_of_CRing R)).
Proof.
intros A R S.
apply (RelRewriteR' (FractionRingCannProjTheorem _ _ _)).  
apply FractionRingAddIsIdent_nume0.
Qed.

Theorem FractionRingAdd_IdentCond : forall {A} (R : #(CRing A)) (S : #(SubCMonoid (%Mult_of_CRing R))),
Ope_IdentCond (FractionRingAdd R S).
Proof.
intros A R S.
exists (%(FractionRingCannProj R S) (Zero_of_CRing R)).
apply FractionRingAddIsIdent_0.
Qed.

Theorem FractionRingAdd_InvertCond : forall {A} (R : #(CRing A)) (S : #(SubCMonoid (%Mult_of_CRing R))),
Ope_InvertCond (FractionRingAdd R S).
Proof.
intros A R S.
intro x.
put (FractionRingIn _ _ x) Eqx.
destruct Eqx as [a Eqx].
destruct Eqx as [p Eqx].
apply (RelRewriteR' Eqx).
apply IsInvertibleTheorem.
exists (%(Fraction_of_Ring R S) [%(MInvert_of_CGrp (Add_of_CRing R)) a ; p]).
apply IsInverseETheoremL.
apply FractionRingAdd_CommCond.
generalize (FractionRingAddIsIdent_nume0 R S p).
apply RelRewriteR.
rewrite FractionRingAddTheoremSameDeno.
apply MapArgEq.
apply EqualInPair'L.
unfold Zero_of_CRing.
unfold MIdent_of_CGrp.
apply MIdentEq.
cut (&&(IsInverseE_of_CGrp (Add_of_CRing R)) a (%(MInvert_of_CGrp (Add_of_CRing R)) a)).
 intro cond.
 unfold IsInverseE_of_CGrp in cond.
 apply IsInverseETheorem in cond.
 generalize (proj1 cond).
 apply RelRewriteAll; hyperreflexivity.
apply MInvert_of_CGrpTheorem.
Qed.

Theorem FractionRingAdd_MonoidCond : forall {A} (R : #(CRing A)) (S : #(SubCMonoid (%Mult_of_CRing R))),
Ope_MonoidCond (FractionRingAdd R S).
Proof.
intros A R S.
split.
apply FractionRingAdd_SGrpCond.
apply FractionRingAdd_IdentCond.
Qed.

Theorem FractionRingAdd_CMonoidCond : forall {A} (R : #(CRing A)) (S : #(SubCMonoid (%Mult_of_CRing R))),
Ope_CMonoidCond (FractionRingAdd R S).
Proof.
intros A R S.
split.
apply FractionRingAdd_MonoidCond.
apply FractionRingAdd_CommCond.
Qed.

Theorem FractionRingAdd_GrpCond : forall {A} (R : #(CRing A)) (S : #(SubCMonoid (%Mult_of_CRing R))),
Ope_GrpCond (FractionRingAdd R S).
Proof.
intros A R S.
split.
apply FractionRingAdd_MonoidCond.
apply FractionRingAdd_InvertCond.
Qed.

Theorem FractionRingAdd_CGrpCond : forall {A} (R : #(CRing A)) (S : #(SubCMonoid (%Mult_of_CRing R))),
Ope_CGrpCond (FractionRingAdd R S).
Proof.
intros A R S.
split.
apply FractionRingAdd_GrpCond.
apply FractionRingAdd_CommCond.
Qed.

Theorem FractionRingAddCannProj_Hom : forall {A} (R : #(CRing A)) (S : #(SubCMonoid (%Mult_of_CRing R))),
&&IsHomomorphism_of_BOpe [AddO_of_CRing R ; FractionRingAdd R S] (FractionRingCannProj R S).
Proof.
intros A R S.
apply IsHomomorphism_of_BOpeTheorem.
intros a b.
rewrite FractionRingCannProjTheorem.
rewrite (MapArgEq _ (EqualInPair'L _ _ _ _ _ (FractionRingCannProjTheorem _ _ _))).
rewrite (MapArgEq _ (EqualInPair'R _ _ _ _ _ (FractionRingCannProjTheorem _ _ _))).
rewrite FractionRingAddTheoremSameDeno.
hyperreflexivity.
Qed.

Theorem FractionRingAddOpe_DistDond : forall {A} (R : #(CRing A)) (S : #(SubCMonoid (%Mult_of_CRing R))),
Ope2_DistDond (FractionRingAdd R S) (FractionRingOpe R S).
Proof.
intros A R S.
put (FractionRing_Ope_CommCond R S) CMCond.
apply (Dist_RDistCommCond _ _ CMCond).
intros x y z.
set (FractionRingAdd R S) as nplus.
set (FractionRingOpe R S) as nmult.
put (FractionRingIn _ _ x) Eqx.
destruct Eqx as [a Eqx].
destruct Eqx as [p Eqx].
put (FractionRingIn _ _ y) Eqy.
destruct Eqy as [b Eqy].
destruct Eqy as [q Eqy].
put (FractionRingIn _ _ z) Eqz.
destruct Eqz as [c Eqz].
destruct Eqz as [r Eqz].
rewrite (MapArgEq _ (EqualInPair'L _ _ _ _ _ (MapArgEq _ (EqualInPair'L _ _ _ _ _ Eqx)))).
rewrite (MapArgEq _ (EqualInPair'L _ _ _ _ _ (MapArgEq _ (EqualInPair'R _ _ _ _ _ Eqy)))).
rewrite (MapArgEq _ (EqualInPair'R _ _ _ _ _ Eqz)).
rewrite (MapArgEq _ (EqualInPair'L _ _ _ _ _ (MapArgEq _ (EqualInPair'L _ _ _ _ _ Eqx)))).
rewrite (MapArgEq _ (EqualInPair'L _ _ _ _ _ (MapArgEq _ (EqualInPair'R _ _ _ _ _ Eqz)))).
rewrite (MapArgEq _ (EqualInPair'R _ _ _ _ _ (MapArgEq _ (EqualInPair'L _ _ _ _ _ Eqy)))).
rewrite (MapArgEq _ (EqualInPair'R _ _ _ _ _ (MapArgEq _ (EqualInPair'R _ _ _ _ _ Eqz)))).
rewrite (MapArgEq _ (EqualInPair'L _ _ _ _ _ (FractionRingAddTheorem R S _ _ _ _ ))).
rewrite (FractionRingTheorem R S).
rewrite (MapArgEq _ (EqualInPair'L _ _ _ _ _ (FractionRingTheorem R S _ _ _ _))).
rewrite (MapArgEq _ (EqualInPair'R _ _ _ _ _ (FractionRingTheorem R S _ _ _ _))).
rewrite (FractionRingAddTheorem R S).
set (MultO_of_CRing R) as mult.
set (AddO_of_CRing R) as plus.
set (SubCMonoid_to_Ope S) as smult.
set (p{<SubCMonoid_S}) as pA.
set (q{<SubCMonoid_S}) as qA.
set (r{<SubCMonoid_S}) as rA.
assert(smult_mult : StrongRel (smult{<Map_Rel}) (mult{<Map_Rel})).
 apply (StrongSubBOpe _ _ (S{<SubCMonoid_SubOpe})).
 apply ReflexivityStrongRel2.
 hyperreflexivity.
apply FractionRingEq.
exists r.
apply MapArgEq.
apply EqualInPair'L.
fold mult.
put (MultO_of_CRing_CMonoidCond R) CMon.
fold mult in CMon.
put (AddO_of_CRing_CGrpCond R) CGrp.
fold plus in CGrp.
put (AddMult_of_CRingDistDond R) dist.
fold plus in dist.
fold mult in dist.
assert(mC : Ope_CommCond mult).
 apply Ope_Comm.
 apply CMonoid_Comm.
 apply Ope_CMonoid.
 apply CMon.
assert(mA : Ope_SGrpCond mult).
 apply Ope_SGrp.
 apply CMonoid_SGrp.
 apply Ope_CMonoid.
 apply CMon. 
apply (TransitivityEq (%mult [%mult [%plus [%mult [a;qA] ; %mult [b;pA]] ; c] ; %mult [%mult [pA;rA] ; %mult [qA ; rA]]])).
 apply MapArgEq.
 apply EqualInPair'R.
 rewrite USETEq.
 apply MapStrong.
  apply smult_mult.
 apply EqualInPair'.
 split.
  apply MapStrong.
  apply smult_mult.
  hyperreflexivity.

  apply MapStrong.
  apply smult_mult.
  hyperreflexivity.
apply SymmetryEq.
apply (TransitivityEq (%mult [%plus [%mult [%mult [a;c] ; %mult [qA;rA]] ; %mult [%mult [b;c] ; %mult [pA;rA]]] ; %mult [%mult [pA;qA] ;rA]])).
 apply MapArgEq.
 apply EqualInPair'.
 split.
  apply MapArgEq.
  apply EqualInPair'.
  split.
   apply MapArgEq.
   apply EqualInPair'R.
   rewrite USETEq.
   apply MapStrong.
   apply smult_mult.
   hyperreflexivity.

   apply MapArgEq.
   apply EqualInPair'R.
   rewrite USETEq.
   apply MapStrong.
   apply smult_mult.
   hyperreflexivity.
 
  rewrite USETEq.
  apply MapStrong.
  apply smult_mult.
  apply EqualInPair'.
  split.
   apply MapStrong.
   apply smult_mult.
   hyperreflexivity.
  hyperreflexivity.
rewrite (proj2 (dist _ _ _)).
rewrite (MapArgEq _ (EqualInPair'L _ _ _ _ _ (proj2 (dist _ _ _)))).
rewrite (proj2 (dist _ _ _)).
apply MapArgEq.
apply EqualInPair'.
split.

 rewrite mA.
 apply SymmetryEq.
 rewrite (MapArgEq _ (EqualInPair'L _ _ _ _ _ (mA _ _ _))).
 rewrite (MapArgEq _ (EqualInPair'L _ _ _ _ _ (MapArgEq _ (EqualInPair'R _ _ _ _ _ (mC _ _))))).
 rewrite <- (MapArgEq _ (EqualInPair'L _ _ _ _ _ (mA _ _ _))).
 rewrite mA.
 apply MapArgEq.
 apply EqualInPair'R.
 rewrite (MapArgEq _ (EqualInPair'R _ _ _ _ _ (MapArgEq _ (EqualInPair'L _ _ _ _ _ (mC _ _))))).
 rewrite (MapArgEq _ (EqualInPair'R _ _ _ _ _ (mA _ _ _))).
 rewrite <- mA.
 apply MapArgEq.
 apply EqualInPair'R.
 apply SymmetryEq.
 apply mA.

 rewrite mA.
 apply SymmetryEq.
 rewrite (MapArgEq _ (EqualInPair'L _ _ _ _ _ (mA _ _ _))).
 rewrite (MapArgEq _ (EqualInPair'L _ _ _ _ _ (MapArgEq _ (EqualInPair'R _ _ _ _ _ (mC _ _))))).
 rewrite <- (MapArgEq _ (EqualInPair'L _ _ _ _ _ (mA _ _ _))).
 rewrite mA.
 apply MapArgEq.
 apply EqualInPair'R.
 rewrite mA.
 apply MapArgEq.
 apply EqualInPair'R.
 rewrite <- mA.
 apply SymmetryEq.
 rewrite <- mA.
 apply MapArgEq.
 apply EqualInPair'L.
 rewrite <- mA.
 apply MapArgEq.
 apply EqualInPair'L.
 apply mC.
Qed.

Theorem FractionRing_CRingDond : forall {A} (R : #(CRing A)) (S : #(SubCMonoid (%Mult_of_CRing R))),
Ope2_CRingDond (FractionRingAdd R S) (FractionRingOpe R S).
Proof.
intros A R S.
split.
apply FractionRingAdd_CGrpCond.
split.
apply FractionRing_Ope_CMonoidCond.
apply FractionRingAddOpe_DistDond.
Qed.
 