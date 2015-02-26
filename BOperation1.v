Require Import logic.
Require Import IZF.
Require Import Relation.
Require Import BaseMap.
Require Import Maps.
(*Require Import MOList.*)


(***************************)
(** Fundamental Operation **)
(***************************)

Definition Operation A X := Map (Cartesian A X) X.


Definition BOperation A := Operation A A.

Theorem BOpe_Map : forall {A}, Subset (BOperation A) (Map (Cartesian A A) A).
Proof.
intro A.
unfold BOperation.
unfold Operation.
apply ReflexivitySubset.
Qed.

Theorem StrongBOpeSubset : forall {A B} (o1 : #(BOperation A)) (o2 : #(BOperation B)),
StrongMap o1 o2 -> Subset A B.
Proof.
intros A B o1 o2 SH.
assert(SUBC : Subset (Cartesian A A) (Cartesian B B)).
 apply (MapStrongSubset o1 o2).
 apply SH.
intros a InaA.
assert(InaC : In (Pair a a) (Cartesian A A)).
 apply CartesianTheorem.
 split; apply InaA.
apply SUBC in InaC.
apply CartesianTheorem in InaC.
destruct InaC as [InaB _].
apply InaB.
Qed.



(* quotient operation *)
Definition IsQuotientableBOpeWC {A} : #(Relation (Classifications A) (BOperation A)) :=
MakeRelation (fun C o => (forall a a' b b', (&&(%Class_to_ERel C){<ERel_Rel} a a' /\ &&(%Class_to_ERel C){<ERel_Rel} b b') -> &&(%Class_to_ERel C){<ERel_Rel} (%o [a;b]) (%o [a';b']))).

Theorem IsQuotientableBOpeWCTheorem : forall {A} (C : #(Classifications A)) (o : #(BOperation A)),
&&IsQuotientableBOpeWC C o <->
(forall a a' b b', (&&(%Class_to_ERel C){<ERel_Rel} a a' /\ &&(%Class_to_ERel C){<ERel_Rel} b b') -> &&(%Class_to_ERel C){<ERel_Rel} (%o [a;b]) (%o [a';b'])).
Proof.
intros A C o.
split.
 intro QH.
 put ((proj1 (MakeRelationTheorem _ _ _ _ _)) QH) QH'.
 clear QH.
 apply QH'.
 hyperreflexivity.
 hyperreflexivity.
intros cond.
apply MakeRelationTheorem.
intros C' o' Eqerel Eqo.
intros a a' b b' condH.
destruct condH as [cond1 cond2].
assert(EqC : (%Class_to_ERel C'){<ERel_Rel} == (%Class_to_ERel C){<ERel_Rel}).
 rewrite (USETEq _ ERel_Rel).
 rewrite (USETEq _ ERel_Rel).
 apply MapArgEq.
 apply SymmetryEq.
 apply Eqerel.
apply (RelRewrite EqC) in cond1.
apply (RelRewrite EqC) in cond2.
put (conj cond1 cond2) condD.
apply cond in condD.
generalize condD.
apply RelRewriteAll.
apply MapEq.
apply Eqo.
apply MapEq.
apply Eqo.
apply SymmetryEq.
apply EqC.
Qed.

Definition QuotientableBOpeWC {A} : #(Map (Classifications A) (PowerSet (BOperation A))) :=
%RelImageE IsQuotientableBOpeWC.

Theorem QuotientableBOpeWCTheorem : forall {A} (C : #(Classifications A)) (o : #(BOperation A)),
In o (%QuotientableBOpeWC C) <->
&&IsQuotientableBOpeWC C o.
Proof.
intros A C o.
unfold QuotientableBOpeWC.
apply RelationImageETheorem.
Qed.

Theorem QableBOpeWC_BOpe : forall {A} {C : #(Classifications A)}, Subset (%QuotientableBOpeWC C) (BOperation A).
Proof.
intros A C.
unfold QuotientableBOpeWC.
apply RelationImageESubset.
Qed.

Definition BOpe_QableBOpeWCCond {A} (C : #(Classifications A)) (o : #(BOperation A)) :=
&&IsQuotientableBOpeWC C o.

Theorem BOpe_QableBOpeWC {A} (C : #(Classifications A)) : forall (o : #(BOperation A)),
BOpe_QableBOpeWCCond C o <-> In o (%QuotientableBOpeWC C).
Proof.
intros o.
split.
 intro cond.
 apply QuotientableBOpeWCTheorem.
 apply cond.
intro Ino.
apply QuotientableBOpeWCTheorem in Ino.
apply Ino.
Qed.

Theorem QableBOpeWC_CDMap : forall {A} (C : #(Classifications A)),
Subset (%QuotientableBOpeWC C) (%ClassDividableMap [%DoubleClassifications [C;C] ; C]).
Proof.
intros A C.
intros o_ Qo.
assert(InoO : In o_ (BOperation A)).
 apply QableBOpeWC_BOpe in Qo.
 apply Qo.
set {o_ ! InoO} as o.
assert(Eqo : o_ == o).
 hyperreflexivity.
rewrite Eqo.
rewrite Eqo in Qo.
clear Eqo.
rewrite (USETEq' _ BOpe_Map).
apply ClassDividableMapTheorem.
apply IsClassDividableMapTheorem.
intros aa bb HH.
put (CartesianIsPair' _ _ _ (SetProp aa)) Eqaa.
destruct Eqaa as [a Eqaa].
destruct Eqaa as [a' Eqaa].
put (CartesianIsPair' _ _ _ (SetProp bb)) Eqbb.
destruct Eqbb as [b Eqbb].
destruct Eqbb as [b' Eqbb].
apply (RelRewriteL Eqaa) in HH.
apply (RelRewriteR Eqbb) in HH.
apply DoubleClassificationsRelation in HH.
destruct HH as [HH1 HH2].
cut (&&(%Class_to_ERel C){<ERel_Rel} (%o [a;a']) (%o[b;b'])).
 apply RelRewriteAll.
  apply MapEqAll.
  apply SymmetryEq.
  apply Eqaa.
  hyperreflexivity.

  apply MapEqAll.
  apply SymmetryEq.
  apply Eqbb.
  hyperreflexivity.
 hyperreflexivity.
apply QuotientableBOpeWCTheorem in Qo.
put ((proj1 (IsQuotientableBOpeWCTheorem _ _)) Qo) Qo'.
clear Qo.
apply Qo'.
split.
apply HH1.
apply HH2.
Qed.

Definition QuotientBOpeWC__ {A} (C : #(Classifications A)) (*: #(Map (%QuotientableBOpeWC C) (BOperation C))*)
 :=
%RightCombineMapC [%CombineMap' [EmbedMap (QableBOpeWC_CDMap C) ; ClassDivMap _ _]; DoubleClassification].

Theorem QuotientBOpeWC__Theorem : forall {A} (C : #(Classifications A)) (qo : #(%QuotientableBOpeWC C)) a b,
%(%(QuotientBOpeWC__ C) qo) [%(EqCannProj C) a ; %(EqCannProj C) b] ==
%(EqCannProj C) (%(qo{<QableBOpeWC_BOpe}) [a;b]).
Proof.
intros A C qo a b.
unfold QuotientBOpeWC__.
rewrite RightCombineMapCTheorem.
rewrite (MapEq (CombineMap'Theorem _ _ _ _ _ _)).
rewrite (MapArgEq' _ (DoubleClassificationEqCannProj _ _ _ _)).
rewrite ClassDivMapTheorem.
apply MapArgEq.
apply MapEq.
rewrite (USETEq _ CDMap_Map).
rewrite EmbedMapEq.
hyperreflexivity.
Qed.

Definition QuotientBOpeWC {A} (C : #(Classifications A)) : #(Map (%QuotientableBOpeWC C) (BOperation C)) :=
QuotientBOpeWC__ C.

Theorem QuotientBOpeWCTheorem : forall {A} (C : #(Classifications A)) (qo : #(%QuotientableBOpeWC C)) a b,
%(%(QuotientBOpeWC C) qo) [%(EqCannProj C) a ; %(EqCannProj C) b] ==
%(EqCannProj C) (%(qo{<QableBOpeWC_BOpe}) [a;b]).
Proof.
intros A C qo a b.
unfold QuotientBOpeWC.
apply (TransitivityEq (%(%(QuotientBOpeWC__ C) qo) [%(EqCannProj C) a ; %(EqCannProj C) b])).
hyperreflexivity.
rewrite QuotientBOpeWC__Theorem.
hyperreflexivity.
Qed.

Theorem QuotientBOpeWCTheoremWP : forall {A} (C : #(Classifications A)) (o : #(BOperation A)) (cond : BOpe_QableBOpeWCCond C o) a b,
%(%(QuotientBOpeWC C) (o{<BOpe_QableBOpeWC C ! cond})) [%(EqCannProj C) a ; %(EqCannProj C) b] ==
%(EqCannProj C) (%o [a;b]).
Proof.
intros A C o cond a b.
rewrite QuotientBOpeWCTheorem.
apply MapArgEq.
apply MapEq.
hyperreflexivity.
Qed.

(* homomorphism *)
Definition IsHomomorphism_of_BOpe {A B} : #(Relation (Cartesian (BOperation A) (BOperation B)) (Map A B)) :=
MakeRelation (fun od f => forall a b, %(%MRight od) [%f a ; %f b] == %f (%(%MLeft od) [a;b])).

Definition IsIHomomorphism_of_BOpe {A B} : #(Relation (Cartesian (BOperation A) (BOperation B)) (Map A B)) :=
MakeRelation (fun od f => &&IsHomomorphism_of_BOpe od f /\ In f (Injection A B)).

Definition IsSHomomorphism_of_BOpe {A B} : #(Relation (Cartesian (BOperation A) (BOperation B)) (Map A B)) :=
MakeRelation (fun od f => &&IsHomomorphism_of_BOpe od f /\ In f (Surjection A B)).

Definition Isomorphism_of_BOpe {A B} : #(Relation (Cartesian (BOperation A) (BOperation B)) (Map A B)) :=
MakeRelation (fun od f => &&IsHomomorphism_of_BOpe od f /\ In f (Bijection A B)).

Theorem IsHomomorphism_of_BOpeTheorem : forall {A B} (oa : #(BOperation A)) (ob : #(BOperation B)) (f : #(Map A B)),
&&IsHomomorphism_of_BOpe [oa;ob] f <->
(forall a b, %f (%oa [a;b]) == %ob [%f a ; %f b]).
Proof.
intros A B oa ob f.
split.
 intro HH.
 intros a b.
 put ((proj1 (MakeRelationTheorem _ _ _ _ _)) HH) HH'.
 clear HH.
 put (HH' _ _ (ReflexivityEq _) (ReflexivityEq f)) HH.
 clear HH'.
 apply (TransitivityEq (%f (%(%MLeft [oa;ob]) [a;b]))).
  apply MapArgEq.
  apply MapEq.
  apply SymmetryEq.
  apply LeftPairTheorem.
 rewrite <- HH.
 apply MapEq.
 apply RightPairTheorem.
intro EqfH.
apply MakeRelationTheorem.
intros oaob f' Eqo Eqf a b.
apply (TransitivityEq (%ob [%f a ; %f b])).
 apply MapEqAll.
 apply EqualInPair'.
 split.
  apply MapEq.
  apply SymmetryEq.
  apply Eqf.
 apply MapEq.
 apply SymmetryEq.
 apply Eqf.
 rewrite (MapArgEq' _ Eqo).
 apply RightPairTheorem.
rewrite <- EqfH.
apply MapEqAll.
 apply MapEq.
 apply SymmetryEq.
 rewrite (MapArgEq' _ Eqo).
 apply LeftPairTheorem.
apply Eqf.
Qed.

Theorem IsSHomomorphism_of_BOpeTheorem : forall {A B} (oa : #(BOperation A)) (ob : #(BOperation B)) (f : #(Map A B)),
&&IsSHomomorphism_of_BOpe [oa;ob] f <->
(&&IsHomomorphism_of_BOpe [oa;ob] f /\ In f (Surjection A B)).
Proof.
intros A B oa ob f.
split.
 intro SH.
 put ((proj1 (MakeRelationTheorem _ _ _ _ _)) SH) SH'.
 put (SH' _ _ (ReflexivityEq _) (ReflexivityEq f)) SH''.
 apply SH''.
intro cD.
apply MakeRelationTheorem.
intros oaob f' Eqoaob Eqf'.
destruct cD as [HH InfS].
split.
 generalize HH.
 apply RelRewriteAll.
 apply Eqoaob.
 apply Eqf'.
 hyperreflexivity.
rewrite <- Eqf'.
apply InfS.
Qed.

Theorem IsIHomomorphism_of_BOpeTheorem : forall {A B} (oa : #(BOperation A)) (ob : #(BOperation B)) (f : #(Map A B)),
&&IsIHomomorphism_of_BOpe [oa;ob] f <->
(&&IsHomomorphism_of_BOpe [oa;ob] f /\ In f (Injection A B)).
Proof.
intros A B oa ob f.
split.
 intro SH.
 put ((proj1 (MakeRelationTheorem _ _ _ _ _)) SH) SH'.
 put (SH' _ _ (ReflexivityEq _) (ReflexivityEq f)) SH''.
 apply SH''.
intro cD.
apply MakeRelationTheorem.
intros oaob f' Eqoaob Eqf'.
destruct cD as [HH InfS].
split.
 generalize HH.
 apply RelRewriteAll.
 apply Eqoaob.
 apply Eqf'.
 hyperreflexivity.
rewrite <- Eqf'.
apply InfS.
Qed.

Theorem Isomorphism_of_BOpeTheorem : forall {A B} (oa : #(BOperation A)) (ob : #(BOperation B)) (f : #(Map A B)),
&&Isomorphism_of_BOpe [oa;ob] f <->
(&&IsHomomorphism_of_BOpe [oa;ob] f /\ In f (Bijection A B)).
Proof.
intros A B oa ob f.
split.
 intro SH.
 put ((proj1 (MakeRelationTheorem _ _ _ _ _)) SH) SH'.
 put (SH' _ _ (ReflexivityEq _) (ReflexivityEq f)) SH''.
 apply SH''.
intro cD.
apply MakeRelationTheorem.
intros oaob f' Eqoaob Eqf'.
destruct cD as [HH InfS].
split.
 generalize HH.
 apply RelRewriteAll.
 apply Eqoaob.
 apply Eqf'.
 hyperreflexivity.
rewrite <- Eqf'.
apply InfS.
Qed.

Definition Homomorphism_of_BOpe {A B} : #(Map (Cartesian (BOperation A) (BOperation B)) (PowerSet (Map A B))) :=
%RelImageE IsHomomorphism_of_BOpe.

Theorem HomBOpe_Map : forall {A B} {od : #(Cartesian (BOperation A) (BOperation B))},
Subset (%Homomorphism_of_BOpe od) (Map A B).
Proof.
intros A B od.
unfold Homomorphism_of_BOpe.
apply RelationImageESubset.
Qed.

Theorem Homomorphism_of_BOpeTheorem : forall {A B} (oa : #(BOperation A)) (ob : #(BOperation B)) (f : #(Map A B)),
In f (%Homomorphism_of_BOpe [oa;ob]) <->
&&IsHomomorphism_of_BOpe [oa;ob] f.
Proof.
intros A B oa ob f.
unfold Homomorphism_of_BOpe.
apply RelationImageETheorem.
Qed.


Definition Homomorphic_of_BOpe {A B} : #(Relation (BOperation A) (BOperation B)) :=
MakeRelation (fun oa ob => exists f, &&IsHomomorphism_of_BOpe [oa;ob] f).

Definition SHomomorphic_of_BOpe {A B} : #(Relation (BOperation A) (BOperation B)) :=
MakeRelation (fun oa ob => exists f, &&IsSHomomorphism_of_BOpe [oa;ob] f).

Definition IHomomorphic_of_BOpe {A B} : #(Relation (BOperation A) (BOperation B)) :=
MakeRelation (fun oa ob => exists f, &&IsIHomomorphism_of_BOpe [oa;ob] f).

Definition Isomorphic_of_BOpe {A B} : #(Relation (BOperation A) (BOperation B)) :=
MakeRelation (fun oa ob => exists f, &&Isomorphism_of_BOpe [oa;ob] f).

Theorem Homomorphic_of_BOpeTheorem : forall {A B} (oa : #(BOperation A)) (ob : #(BOperation B)),
(&&Homomorphic_of_BOpe oa ob) <->
exists f, &&IsHomomorphism_of_BOpe [oa;ob] f.
Proof.
intros A B oa ob.
split.
 intro HH.
 put ((proj1 (MakeRelationTheorem _ _ _ _ _)) HH) HH'.
 clear HH.
 put (HH' _ _ (ReflexivityEq oa) (ReflexivityEq ob)) HH.
 clear HH'.
 apply HH.
intro cond.
apply MakeRelationTheorem.
intros oa' ob' Eqoa Eqob.
destruct cond as [f cond].
exists f.
generalize cond.
apply RelRewriteL.
apply EqualInPair'.
split.
apply Eqoa.
apply Eqob.
Qed.

Theorem SHomomorphic_of_BOpeTheorem : forall {A B} (oa : #(BOperation A)) (ob : #(BOperation B)),
(&&SHomomorphic_of_BOpe oa ob) <->
exists f, &&IsSHomomorphism_of_BOpe [oa;ob] f.
Proof.
intros A B oa ob.
split.
 intro HH.
 put ((proj1 (MakeRelationTheorem _ _ _ _ _)) HH) HH'.
 clear HH.
 put (HH' _ _ (ReflexivityEq oa) (ReflexivityEq ob)) HH.
 clear HH'.
 apply HH.
intro cond.
apply MakeRelationTheorem.
intros oa' ob' Eqoa Eqob.
destruct cond as [f cond].
exists f.
generalize cond.
apply RelRewriteL.
apply EqualInPair'.
split.
apply Eqoa.
apply Eqob.
Qed.

Theorem IHomomorphic_of_BOpeTheorem : forall {A B} (oa : #(BOperation A)) (ob : #(BOperation B)),
(&&IHomomorphic_of_BOpe oa ob) <->
exists f, &&IsIHomomorphism_of_BOpe [oa;ob] f.
Proof.
intros A B oa ob.
split.
 intro HH.
 put ((proj1 (MakeRelationTheorem _ _ _ _ _)) HH) HH'.
 clear HH.
 put (HH' _ _ (ReflexivityEq oa) (ReflexivityEq ob)) HH.
 clear HH'.
 apply HH.
intro cond.
apply MakeRelationTheorem.
intros oa' ob' Eqoa Eqob.
destruct cond as [f cond].
exists f.
generalize cond.
apply RelRewriteL.
apply EqualInPair'.
split.
apply Eqoa.
apply Eqob.
Qed.

Theorem Isomorphic_of_BOpeTheorem : forall {A B} (oa : #(BOperation A)) (ob : #(BOperation B)),
(&&Isomorphic_of_BOpe oa ob) <->
exists f, &&Isomorphism_of_BOpe [oa;ob] f.
Proof.
intros A B oa ob.
split.
 intro HH.
 put ((proj1 (MakeRelationTheorem _ _ _ _ _)) HH) HH'.
 clear HH.
 put (HH' _ _ (ReflexivityEq oa) (ReflexivityEq ob)) HH.
 clear HH'.
 apply HH.
intro cond.
apply MakeRelationTheorem.
intros oa' ob' Eqoa Eqob.
destruct cond as [f cond].
exists f.
generalize cond.
apply RelRewriteL.
apply EqualInPair'.
split.
apply Eqoa.
apply Eqob.
Qed.

Theorem IsHomomorphism_QuotientBOpe : forall {A} (C : #(Classifications A)) (o : #(BOperation A)) (cond : BOpe_QableBOpeWCCond C o) ,
&&IsHomomorphism_of_BOpe [o ; %(QuotientBOpeWC C) (o{<BOpe_QableBOpeWC C ! cond})] (EqCannProj C).
Proof.
intros A C o cond.
apply IsHomomorphism_of_BOpeTheorem.
intros a b.
rewrite QuotientBOpeWCTheoremWP.
hyperreflexivity.
Qed.

Theorem CombIsHomomorphis_of_BOpe : forall {A B C} (oa : #(BOperation A)) (ob : #(BOperation B)) (oc : #(BOperation C)) f g,
&&IsHomomorphism_of_BOpe [oa;ob] f -> &&IsHomomorphism_of_BOpe [ob;oc] g ->
&&IsHomomorphism_of_BOpe [oa;oc] (%CombineMap' [f;g]).
Proof.
intros A B C oa ob oc f g.
intros HH1 HH2.
put ((proj1 (IsHomomorphism_of_BOpeTheorem _ _ _)) HH1) Commf1.
put ((proj1 (IsHomomorphism_of_BOpeTheorem _ _ _)) HH2) Commf2.
apply IsHomomorphism_of_BOpeTheorem.
intros a b.
rewrite CombineMap'Theorem.
rewrite (MapArgEq _ (Commf1 _ _)).
rewrite Commf2.
apply MapArgEq.
apply EqualInPair'.
split.
rewrite CombineMap'Theorem.
hyperreflexivity.
rewrite CombineMap'Theorem.
hyperreflexivity.
Qed.


(* Partial Binary Operation *)
Definition IsSubBOperation {A} : #(Relation (BOperation A) (PowerSet A)) :=
MakeRelation (fun o S => forall (a b : #A), In a S -> In b S -> In (%o [a;b]) S).

Theorem IsSubBOperationTheorem : forall {A} (o : #(BOperation A)) (S : #(PowerSet A)),
&&IsSubBOperation o S <-> 
(forall (a b : #A), In a S -> In b S -> In (%o [a;b]) S).
Proof.
intros A o S.
split.
 intro SH.
 intros a b InaS InbS.
 put ((proj1 (MakeRelationTheorem _ _ _ _ _)) SH) SH'.
 apply SH'.
 hyperreflexivity.
 hyperreflexivity.
 assumption.
 assumption.
intro cond.
apply MakeRelationTheorem.
intros o' S' Eqo EqS a b Ina Inb.
rewrite <- EqS.
rewrite (MapEq' Eqo).
apply cond.
rewrite EqS.
assumption.
rewrite EqS.
assumption.
Qed.

Definition SubBOperation {A} : #(Map (BOperation A) (PowerSet (PowerSet A))) :=
%RelImageE IsSubBOperation.

Theorem SubBOperationSubset : forall {A} (o : #(BOperation A)),
Subset (%SubBOperation o) (PowerSet A).
Proof.
intros A o.
unfold SubBOperation.
apply RelationImageESubset.
Qed.

Theorem SubBOperationTheorem : forall {A} (o : #(BOperation A)) (S : #(PowerSet A)),
In S (%SubBOperation o) <-> &&IsSubBOperation o S.
Proof.
intros A o S.
unfold SubBOperation.
apply RelationImageETheorem.
Qed.

Theorem SubBOpe_to_BOpeIn {A} : forall (o : #(BOperation A)) (S : #(%SubBOperation o)),
In o (RistableMap (Cartesian A A) A (Cartesian S S) S).
Proof.
intros o S.
assert(subSA : Subset S A).
 put (SubBOperationSubset o) sub.
 put (SetProp S) InS.
 apply sub in InS.
 apply PowersetTheorem in InS.
 apply InS.
rewrite (USETEq' _ BOpe_Map).
apply RistableMapTheorem.
split.
 apply SubsetInCartesian; apply subSA.
split.
 apply subSA.
intros aa InaaC.
cut (In (%o aa) S).
 apply Arrow2Rewrite.
 hyperreflexivity.
 hyperreflexivity.
put (SetProp S) InSS.
rewrite (DSETEq' S ((proj2 (PowersetTheorem _ _)) subSA)) in InSS.
apply SubBOperationTheorem in InSS.
put ((proj1 (IsSubBOperationTheorem _ _)) InSS) InSS'.
put (CartesianIsPair' _ _ _ InaaC) IsPaa.
destruct IsPaa as [s1 Eqaa].
destruct Eqaa as [s2 Eqaa].
assert(Eqaa' : aa == [s1{<subSA} ; s2{<subSA}]).
 rewrite Eqaa.
 hyperreflexivity.
rewrite (MapArgEq _ Eqaa').
apply InSS'.
apply (SetProp s1).
apply (SetProp s2).
Qed.

Definition Sub_to_BOperation {A} {o : #(BOperation A)} (S : #(%SubBOperation o)) : #(BOperation S) :=
%RistMap {_ ! SubBOpe_to_BOpeIn o S}.

Theorem StrongSubBOpe : forall {A1 A2} (o1 : #(BOperation A1)) (o2 : #(BOperation A2)) (S : #(%SubBOperation o1)),
StrongMap o1 o2 ->
StrongMap (Sub_to_BOperation S) o2.
Proof.
intros A1 A2 o1 o2 S SH.
unfold Sub_to_BOperation.
apply (TransitivityStrongRel (o1{<Map_Rel})).
 cut (StrongMap (%RistMap {o1 ! SubBOpe_to_BOpeIn o1 S}) o1).
  intro SMH.
  apply SMH.
 apply StrongRistMapEq.
 hyperreflexivity.
apply SH.
Qed.

Theorem SubOpe_S : forall {A} {o : #(BOperation A)} (S : #(%SubBOperation o)),
Subset S A.
Proof.
intros A o S.
apply (StrongBOpeSubset (Sub_to_BOperation S) o).
apply StrongSubBOpe.
apply ReflexivitySubset2.
hyperreflexivity.
Qed.



Definition ProductOperation {A B} : #(Map (Cartesian (BOperation A) (BOperation B)) (BOperation (Cartesian A B))) :=
%RightCombineMapC [ DoubleMap ; %CombineMap' [AssocPairRL ; %CombineMap' [%DoubleMap [AssocPairLR; IdMap] ; %CombineMap' [%DoubleMap[%DoubleMap[IdMap;InversePair] ; IdMap] ; %CombineMap' [%DoubleMap[AssocPairRL ; IdMap] ; AssocPairLR]]]]].

Theorem ProductOperationTheorem : forall {A B} (oa : #(BOperation A)) (ob : #(BOperation B)) (a1 a2 : #A) (b1 b2 : #B),
%( %ProductOperation [oa;ob] ) [ [a1;b1] ; [a2;b2] ] == [ %oa[a1;a2] ; %ob[b1;b2] ].
Proof.
intros A B oa ob a1 a2 b1 b2.
unfold ProductOperation.
rewrite (RightCombineMapCTheorem DoubleMap _ [oa;ob] [[a1;b1];[a2;b2]]).
rewrite (MapArgEq _ (CombineMap'Theorem _ _ _ _ _ _)).
rewrite (MapArgEq _ (CombineMap'Theorem _ _ _ _ _ _)).
rewrite (MapArgEq _ (CombineMap'Theorem _ _ _ _ _ _)).
rewrite (MapArgEq _ (CombineMap'Theorem _ _ _ _ _ _)).
rewrite (MapArgEq _ (MapArgEq _ (MapArgEq _ (MapArgEq _ (MapArgEq _ (AssocPairRLTheorem _ _ _)))))).
rewrite (MapArgEq _ (MapArgEq _ (MapArgEq _ (MapArgEq _ (DoubleMapTheorem _ _ _ _))))).
rewrite (MapArgEq _ (MapArgEq _ (MapArgEq _ (DoubleMapTheorem _ _ _ _)))).
rewrite (MapArgEq _ (MapArgEq _ (DoubleMapTheorem _ _ _ _))).
rewrite (MapArgEq _ (MapArgEq _ (EqualInPair'L _ _ _ _ _ (MapArgEq _ (MapArgEq _ (AssocPairLRTheorem _ _ _)))))).
rewrite (MapArgEq _ (MapArgEq _ (EqualInPair'L _ _ _ _ _ (MapArgEq _ (DoubleMapTheorem _ _ _ _))))).
rewrite (MapArgEq _ (MapArgEq _ (EqualInPair'L _ _ _ _ _ (MapArgEq _ (EqualInPair'R _ _ _ _ _ (InversePairTheorem _ _)))))).
rewrite (MapArgEq _ (MapArgEq _ (EqualInPair'L _ _ _ _ _ (AssocPairRLTheorem _ _ _)))).
rewrite (MapArgEq _ (AssocPairLRTheorem _ _ _)).
rewrite (DoubleMapTheorem oa ob _ _).
apply EqualInPair'.
split.
 apply MapArgEq.
 apply EqualInPair'.
 split.
  apply IdMapTheorem.
 hyperreflexivity.
apply MapArgEq.
apply EqualInPair'.
split.
 hyperreflexivity.
rewrite (IdMapTheorem _ _).
rewrite (IdMapTheorem _ _).
rewrite (IdMapTheorem _ _).
hyperreflexivity.
Qed.


Definition ProductOperationWithSub {A} (o : #(BOperation A)) (S : #(%SubBOperation o)) :=
%ProductOperation [o ; Sub_to_BOperation S].


(***********************)
(** Various Operation **)
(***********************)

(* Identity Element *)
Definition IsLeftIdent {A} :=
MakeRelation (fun (o : #(BOperation A)) (e : #A) => forall a : #A, %o [e;a] == a).
Definition IsRightIdent {A} :=
MakeRelation (fun (o : #(BOperation A)) (e : #A) => forall a : #A, %o [a;e] == a).
Definition IsIdent {A} := %AndRelation [@IsLeftIdent A ; @IsRightIdent A].
(* "&&IsIdent o e" means that an element 'e' is identity element of a binary operator 'o' *) 

Theorem IsLeftIdentTheorem : forall {A} (o : #(BOperation A)) (e : #A),
&&IsLeftIdent o e <-> (forall (a : #A), %o [e;a] == a).
Proof.
intros A o e.
split.
 intro relH.
 intro a.
 put ((proj1 (MakeRelationTheorem _ _ _ _ _)) relH) relH'.
 clear relH.
 put (relH' _ _ (ReflexivityEq o) (ReflexivityEq e) a) relH.
 clear relH'.
 apply relH.

 intro cond.
 apply MakeRelationTheorem.
 intros o' e' Eqo Eqe a.
 rewrite <- (cond a).
 apply MapEqAll.
 apply EqualInPair'.
 split.
 rewrite Eqe.
 hyperreflexivity.
 hyperreflexivity.
 apply SymmetryEq.
 apply Eqo.
Qed.

Theorem IsRightIdentTheorem : forall {A} (o : #(BOperation A)) (e : #A),
&&IsRightIdent o e <-> (forall (a : #A), %o [a;e] == a).
Proof.
intros A o e.
split.
 intro relH.
 intro a.
 put ((proj1 (MakeRelationTheorem _ _ _ _ _)) relH) relH'.
 clear relH.
 put (relH' _ _ (ReflexivityEq o) (ReflexivityEq e) a) relH.
 clear relH'.
 apply relH.

 intro cond.
 apply MakeRelationTheorem.
 intros o' e' Eqo Eqe a.
 rewrite <- (cond a).
 apply MapEqAll.
 apply EqualInPair'.
 split.
 hyperreflexivity.
 rewrite Eqe.
 hyperreflexivity.
 apply SymmetryEq.
 apply Eqo.
Qed.

Theorem IsIdentTheorem2 : forall {A} (o : #(BOperation A)) (e : #A),
&&IsIdent o e <-> (&&IsLeftIdent o e /\ &&IsRightIdent o e).
Proof.
intros A o e.
split.
 intro relH.
 unfold IsIdent in relH.
 apply AndRelationTheorem in relH.
 assumption.

 intro relHD.
 destruct relHD as [relH1 relH2].
 unfold IsIdent.
 apply AndRelationTheorem.
 split; assumption.
Qed.

Theorem IsIdentTheorem : forall {A} (o : #(BOperation A)) (e : #A),
&&IsIdent o e <-> (forall a, %o [e;a] == a /\ %o [a;e] == a).
Proof.
intros A o e.
split.
 intro OH.
 intro a.
 apply IsIdentTheorem2 in OH.
 destruct OH as [OHL OHR].
 put ((proj1 (IsLeftIdentTheorem _ _)) OHL) OHL'.
 put ((proj1 (IsRightIdentTheorem _ _)) OHR) OHR'.
 split.
 apply OHL'.
 apply OHR'.

 intro cond.
 apply IsIdentTheorem2.
 split.
  apply IsLeftIdentTheorem.
  intro a.
  destruct (cond a) as [cond1 cond2].
  apply cond1.

  apply IsRightIdentTheorem.
  intro a.
  destruct (cond a) as [cond1 cond2].
  apply cond2.
Qed.

Theorem IsIdent_LeftIdent : forall {A} (o : #(BOperation A)) (e : #A),
&&IsIdent o e -> &&IsLeftIdent o e.
Proof.
intros A o e IH.
apply IsIdentTheorem2 in IH.
destruct IH as [IH _].
apply IH.
Qed.

Theorem IsIdent_RightIdent : forall {A} (o : #(BOperation A)) (e : #A),
&&IsIdent o e -> &&IsRightIdent o e.
Proof.
intros A o e IH.
apply IsIdentTheorem2 in IH.
destruct IH as [_ IH].
apply IH.
Qed.


Theorem RUnqIsIdent : forall {A}, Rel_RUnqCond (@IsIdent A).
Proof.
intro A.
intro o.
intros e1 e2 Eq1 Eq2.
put ((proj1 (IsIdentTheorem _ _)) Eq1) Eq1'.
put ((proj1 (IsIdentTheorem _ _)) Eq2) Eq2'.
destruct (Eq1' e2) as [f1 f2].
destruct (Eq2' e1) as [f3 f4].
rewrite <- f3.
rewrite <- f2.
hyperreflexivity.
Qed.

Theorem IsIdentEq : forall {A} (o : #(BOperation A)) e1 e2,
&&IsIdent o e1 -> &&IsIdent o e2 -> e1 == e2.
Proof.
intros A o e1 e2 H1 H2.
apply (RightUniqueEq IsIdent o).
 apply RUnqIsIdent.
apply H1.
apply H2.
Qed.

Theorem IsIdentProduct : forall {A B} (o1 : #(BOperation A)) (o2 : #(BOperation B)) e1 e2,
&&IsIdent o1 e1 -> &&IsIdent o2 e2 ->
&&IsIdent (%ProductOperation [o1;o2]) [e1;e2].
Proof.
intros A B o1 o2 e1 e2 IH1 IH2.
apply IsIdentTheorem.
intros ab.
put ((proj1 (IsIdentTheorem _ _)) IH1) IH1'.
put ((proj1 (IsIdentTheorem _ _)) IH2) IH2'.
put (CartesianIsPair' _ _ _ (SetProp ab)) Eqab.
destruct Eqab as [a Eqab].
destruct Eqab as [b Eqab].
clear IH1.
clear IH2.
put (IH1' a) IH1.
put (IH2' b) IH2.
clear IH1'.
clear IH2'.
destruct IH1 as [IH11 IH12].
destruct IH2 as [Ih21 IH22].
split.
 rewrite (MapArgEq _ (EqualInPair'R _ _ _ _ _ Eqab)).
 rewrite ProductOperationTheorem.
 rewrite Eqab.
 apply EqualInPair'.
 split; assumption.
rewrite (MapArgEq _ (EqualInPair'L _ _ _ _ _ Eqab)).
rewrite ProductOperationTheorem.
rewrite Eqab.
apply EqualInPair'.
split; assumption.
Qed.


Theorem IsIdent_StrongCons : forall {A B} (o1 : #(BOperation A)) (o2 : #(BOperation B)) (e1 : #A) (e2 : #B),
e1 == e2 -> StrongMap o1 o2 -> 
&&IsIdent o2 e2 -> &&IsIdent o1 e1.
Proof.
intros A B o1 o2 e1 e2 Eqe SH IH.
apply IsIdentTheorem.
put ((proj1 (IsIdentTheorem _ _)) IH) IH'.
clear IH.
intro a.
assert(sub : Subset A B).
 apply (StrongBOpeSubset o1 o2).
 apply SH.
set (a{<sub}) as a'.
destruct (IH' a') as [IH1 IH2].
split.
 apply (TransitivityEq a').
 rewrite <- IH1.
 apply MapStrong.
 apply SH.
 apply EqualInPair'.
 split.
  apply Eqe.
  hyperreflexivity.
 hyperreflexivity.

 apply (TransitivityEq a').
 rewrite <- IH2.
 apply MapStrong.
 apply SH.
 apply EqualInPair'.
 split.
  hyperreflexivity.
  apply Eqe.
 hyperreflexivity.
Qed.

(*
Theorem IsIdent_IsSHomomorphism : forall {A B} (o1 : #(BOperation A)) (o2 : #(BOperation B)) e (f : #(Map A B)),
&&IsSHomomorphism_of_BOpe [o1;o2] f -> 
&&IsIdent o1 e -> &&IsIdent o2 (%f e).
Proof.
intros A B o1 o2 e f HH IH1.
apply IsSHomomorphism_of_BOpeTheorem in HH.
destruct HH as [HH InfS].
put ((proj1 (IsHomomorphism_of_BOpeTheorem _ _ _)) HH) HH'.
clear HH.
put ((proj1 (IsIdentTheorem _ _)) IH1) IH1'.
clear IH1.
apply IsIdentTheorem.
intros b.
apply Map_Sur in InfS.
unfold Map_SurCond in InfS.
destruct (InfS b) as [a InfS'].
put (IH1' a) IH1.
destruct IH1 as [IH1 IH2].
apply SymmetryEq in InfS'.
split.
 rewrite (MapArgEq _ (EqualInPair'R _ _ _ _ _ InfS')).
 rewrite <- HH'.
 rewrite InfS'.
 apply MapArgEq.
 apply IH1.
rewrite (MapArgEq _ (EqualInPair'L _ _ _ _ _ InfS')).
rewrite <- HH'.
rewrite InfS'.
apply MapArgEq.
apply IH2.
Qed.
*)
Definition LeftIdentical A :=
%RelationAllImageL (@IsLeftIdent A).
Definition RightIdentical A :=
%RelationAllImageL (@IsRightIdent A).
Definition Identical A :=
%RelationAllImageL (@IsIdent A).

Theorem LIdent_Ope {A} : Subset (LeftIdentical A) (BOperation A).
Proof.
intros o InoR.
unfold LeftIdentical in InoR.
apply RelationAllImageLSubset in InoR.
apply InoR.
Qed.

Theorem RIdent_Ope {A} : Subset (RightIdentical A) (BOperation A).
Proof.
intros o InoR.
unfold RightIdentical in InoR.
apply RelationAllImageLSubset in InoR.
apply InoR.
Qed.

Theorem Ident_Ope {A} : Subset (Identical A) (BOperation A).
Proof.
intros o InoR.
unfold RightIdentical in InoR.
apply RelationAllImageLSubset in InoR.
apply InoR.
Qed.

Definition Ope_IdentCond {A} (o : #(BOperation A)) :=
exists e, &&IsIdent o e.
Definition Ope_LIdentCond {A} (o : #(BOperation A)) :=
exists e, &&IsLeftIdent o e.
Definition Ope_RIdentCond {A} (o : #(BOperation A)) :=
exists e, &&IsRightIdent o e.

Theorem Ope_LIdent : forall {A} (o : #(BOperation A)),
Ope_LIdentCond o <-> In o (LeftIdentical A).
Proof.
intros A o.
split.
 intro cond.
 destruct cond as [e cond].
 apply RelationAllImageLIn.
 exists e.
 apply cond.

 intro InoL.
 apply RelationAllImageLIn in InoL.
 destruct InoL as [e InoL].
 exists e.
 apply InoL.
Qed.

Theorem Ope_RIdent : forall {A} (o : #(BOperation A)),
Ope_RIdentCond o <-> In o (RightIdentical A).
Proof.
intros A o.
split.
 intro cond.
 destruct cond as [e cond].
 apply RelationAllImageLIn.
 exists e.
 apply cond.

 intro InoL.
 apply RelationAllImageLIn in InoL.
 destruct InoL as [e InoL].
 exists e.
 apply InoL.
Qed.

Theorem Ope_Ident : forall {A} (o : #(BOperation A)),
Ope_IdentCond o <-> In o (Identical A).
Proof.
intros A o.
split.
 intro cond.
 destruct cond as [e cond].
 apply RelationAllImageLIn.
 exists e.
 apply cond.

 intro InoL.
 apply RelationAllImageLIn in InoL.
 destruct InoL as [e InoL].
 exists e.
 apply InoL.
Qed.


Theorem IsIdent_is_MapInIdentical : forall A, 
Rel_MapCond (%(RistrictRelationL Ident_Ope) (@IsIdent A)).
Proof.
intros A.
apply Rel_Map.
apply Rel_Map2.
split.
 intro io.
 put (SetProp io) InioI.
 assert(InioO : In io (BOperation A)).
  apply Ident_Ope.
  apply InioI.
 rewrite (DSETEq' _ InioO) in InioI.
 apply Ope_Ident in InioI.
 destruct InioI as [e cond].
 exists e.
 apply ToRistrictRelationL.
 apply cond.
apply (Rel_RUnqCond_StrongCons _ (@IsIdent A)).
apply StrongRelRistrictL.
apply RUnqIsIdent.
Qed.


Theorem Ope_IdentCond_StrongCons : forall {A B} (o1 : #(BOperation A)) (o2 : #(BOperation B)),
StrongRel (o1{<Map_Rel}) (o2{<Map_Rel}) -> (forall e, &&IsIdent o2 e -> In e A) -> Ope_IdentCond o2 -> Ope_IdentCond o1.
Proof.
intros A B o1 o2 SH cond OH.
destruct OH as [e OH].
assert(IneA : In e A).
 apply cond.
 apply OH.
exists {e ! IneA}.
apply (IsIdent_StrongCons o1 o2 {e!IneA} e).
hyperreflexivity.
apply SH.
apply OH.
Qed.

Theorem Ope_IdentCond_Product : forall {A B} (o1 : #(BOperation A)) (o2 : #(BOperation B)),
Ope_IdentCond o1 -> Ope_IdentCond o2 -> Ope_IdentCond (%ProductOperation [o1;o2]).
Proof.
intros A B o1 o2 C1 C2.
destruct C1 as [e1 C1].
destruct C2 as [e2 C2].
exists [e1;e2].
apply IsIdentProduct.
apply C1.
apply C2.
Qed.

(*
Theorem Ope_IdentCond_SHomomorphic : forall {A B} (o1 : #(BOperation A)) (o2 : #(BOperation B)),
&&SHomomorphic_of_BOpe o1 o2 -> Ope_IdentCond o1 -> Ope_IdentCond o2.
Proof.
intros A B o1 o2 SHH OC.
apply SHomomorphic_of_BOpeTheorem in SHH.
destruct SHH as [f SHH].
apply IsSHomomorphism_of_BOpeTheorem in SHH.
destruct SHH as [HH InfS].
destruct OC as [e1 OC].
exists (%f e1).
apply (IsIdent_IsSHomomorphism o1 o2).
apply IsSHomomorphism_of_BOpeTheorem.
split; assumption.
apply OC.
Qed.
*)




(* MIdent *)


Definition MIdent {A} : #(Map (Identical A) A) := _{<Rel_Map ! IsIdent_is_MapInIdentical A}.

Theorem MIdentTheorem : forall {A} (oi : #(Identical A)),
&&IsIdent (oi{<Ident_Ope}) (%MIdent oi).
Proof.
intros A oi.
cut (&&(%(RistrictRelationL Ident_Ope) IsIdent) oi (%MIdent oi)).
 apply StrongRelationRel.
 hyperreflexivity.
 hyperreflexivity.
 apply StrongRelRistrictL.
unfold MIdent.
apply AppTheorem.
Qed.

Theorem MIdentTheoremWP : forall {A} (o : #(BOperation A)) (cond : Ope_IdentCond o),
&&IsIdent o (%MIdent (o{<Ope_Ident ! cond})).
Proof.
intros A o cond.
generalize (MIdentTheorem (o{<Ope_Ident ! cond})).
apply RelRewriteAll; hyperreflexivity.
Qed.

Theorem MIdentEq : forall {A} (oi : #(Identical A)) (e : #A),
%MIdent oi == e <->
&&IsIdent (oi{<Ident_Ope}) e.
Proof.
intros A oi e.
split.
 intro EqI.
 apply (RelRewriteR EqI).
 apply MIdentTheorem.
intro IH.
apply (IsIdentEq (oi{<Ident_Ope})).
 apply MIdentTheorem.
apply IH.
Qed.

Theorem MIdentEqWP : forall {A} (o : #(BOperation A)) (cond : Ope_IdentCond o) (e : #A),
%MIdent (o{<Ope_Ident ! cond}) == e <->
&&IsIdent o e.
Proof.
intros A o cond e.
split.
 intro EqI.
 apply (RelRewriteR EqI).
 apply MIdentTheoremWP.
intro IH.
apply (IsIdentEq o).
 apply MIdentTheoremWP.
apply IH.
Qed.

Theorem NonEmptyIdentical : forall {A} (I : #(Identical A)),
NonEmpty A.
Proof.
intros A I.
exists (%MIdent I).
apply SetProp.
Qed.



(* SubIdent *)
Definition IsSubIdentical {A} : #(Relation (BOperation A) (PowerSet A)) :=
MakeRelation (fun o S => &&IsSubBOperation o S /\ (forall e, &&IsIdent o e -> In e S)).

Theorem IsSubIdenticalTheorem : forall {A} (o : #(BOperation A)) (S : #(PowerSet A)),
&&IsSubIdentical o S <-> 
(&&IsSubBOperation o S /\ (forall e, &&IsIdent o e -> In e S)).
Proof.
intros A o S.
split.
 intro SH.
 put ((proj1 (MakeRelationTheorem _ _ _ _ _)) SH) SH'.
 apply SH'.
 hyperreflexivity.
 hyperreflexivity.
intro DH.
destruct DH as [DH cond].
apply MakeRelationTheorem.
intros o' S' Eqo EqS.
split.
 generalize DH.
 apply RelRewriteAll.
 apply Eqo.
 apply EqS.
 hyperreflexivity.
intros e IsH.
rewrite <- EqS.
apply cond.
generalize IsH.
apply RelRewriteL.
apply SymmetryEq.
apply Eqo.
Qed.

Theorem IsSubIdentical_s_IsSubBOperation : forall {A},
StrongRel (@IsSubIdentical A) (@IsSubBOperation A).
Proof.
intros A.
apply ToStrongRel.
intros o S ISI.
exists o.
exists S.
split.
 hyperreflexivity.
split.
 hyperreflexivity.
apply IsSubIdenticalTheorem in ISI.
destruct ISI as [IsSB cond].
apply IsSB.
Qed.


Definition SubIdentical {A} : #(Map (BOperation A) (PowerSet (PowerSet A))) :=
%RelImageE IsSubIdentical.

Theorem SubIdenticalSubset : forall {A} (o : #(BOperation A)),
Subset (%SubIdentical o) (PowerSet A).
Proof.
intros A o.
unfold SubIdentical.
apply RelationImageESubset.
Qed.

Theorem SubIdenticalTheorem : forall {A} (o : #(BOperation A)) (S : #(PowerSet A)),
In S (%SubIdentical o) <-> &&IsSubIdentical o S.
Proof.
intros A o S.
unfold SubIdentical.
apply RelationImageETheorem.
Qed.

Theorem SubIdent_SubOpe : forall {A} {o : #(BOperation A)}, Subset (%SubIdentical o) (%SubBOperation o).
Proof.
intros A o.
intros S InSS.
assert(InSP : In S (PowerSet A)).
 apply SubIdenticalSubset in InSS.
 apply InSS.
rewrite (DSETEq' _ InSP) in InSS.
rewrite (DSETEq' _ InSP).
apply SubIdenticalTheorem in InSS.
apply SubBOperationTheorem.
generalize InSS.
apply StrongRelationRelSameD.
apply IsSubIdentical_s_IsSubBOperation.
Qed.


Theorem SubIdent_S : forall {A} {o : #(BOperation A)} (S : #(%SubIdentical o)),
Subset S A.
Proof.
intros A o S.
apply (StrongBOpeSubset (Sub_to_BOperation S{<SubIdent_SubOpe}) o).
apply StrongSubBOpe.
apply ReflexivityStrongRel.
Qed.

Theorem SubIdenticalHasIdent : forall {A} (o : #(BOperation A)) (S : #(%SubIdentical o)) e,
&&IsIdent o e -> In e S.
Proof.
intros A o S.
intros e IH.
put (SetProp S) InSS.
assert(InSP : In S (PowerSet A)).
 apply SubIdenticalSubset in InSS.
 apply InSS.
rewrite (DSETEq' _ InSP) in InSS.
apply SubIdenticalTheorem in InSS.
apply IsSubIdenticalTheorem in InSS.
destruct InSS as [IsSB cond].
cut (In e {S ! InSP}).
 intro; assumption.
apply cond.
apply IH.
Qed.

Definition SubIdent_to_Ope {A} {o : #(BOperation A)} (S : #(%SubIdentical o)) : #(BOperation S) :=
Sub_to_BOperation (S{<SubIdent_SubOpe}).

Theorem IdentCond_SubIdentCond : forall {A} (o : #(BOperation A)) (S : #(%SubIdentical o)),
Ope_IdentCond o ->
Ope_IdentCond (SubIdent_to_Ope S).
Proof.
intros A o S cond.
unfold Ope_IdentCond.
unfold Ope_IdentCond in cond.
destruct cond as [e cond].
assert(IneS : In e S).
 apply (SubIdenticalHasIdent o).
 apply cond.
exists {e!IneS}.
generalize cond.
apply IsIdent_StrongCons.
hyperreflexivity.
apply (StrongSubBOpe _ _ (S{<SubIdent_SubOpe})).
apply ReflexivityStrongRel.
Qed.

Theorem Sub_to_IdenticalCond : forall {A} (I : #(Identical A)) (S : #(%SubIdentical (I{<Ident_Ope}))),
Ope_IdentCond (SubIdent_to_Ope S).
Proof.
intros A I S.
apply IdentCond_SubIdentCond.
apply Ope_Ident.
apply (SetProp I).
Qed.

Definition Sub_to_Identical {A} {I : #(Identical A)} (S : #(%SubIdentical (I{<Ident_Ope}))) :=
_{<Ope_Ident ! Sub_to_IdenticalCond I S}.

(*
Theorem SubIdent_Ident : forall {A} {o : #(BOperation A)},
Subset (%SubIdentical o) (Identical S).
Proof.
intros A o.
intros S InSS.
assert(InSP : In S (PowerSet A)).
 apply SubIdenticalSubset in InSS.
 apply InSS.
rewrite (DSETEq' _ InSP) in InSS.
apply SubIdenticalTheorem in InSS.

apply Ope_Ident.

apply IdenticalTheorem.

assert(InS
*)

(*
Definition SubIdent_to_Ope {A} {o : #(BOperation A)} (S : #(SubIdentical o)) : #(BOperation S) :=
SubBOpe_to_BOpe (.
*)

Theorem MIdent_eq_SubIdent : forall {A} (I : #(Identical A)) (S : #(%SubIdentical (I{<Ident_Ope}))),
%MIdent I == %MIdent (Sub_to_Identical S).
Proof.
intros A I S.
set (%MIdent I) as e.
assert(IneS : In e S).
 apply (SubIdenticalHasIdent (I{<Ident_Ope})).
 apply MIdentTheorem.
rewrite (DSETEq' _ IneS).
apply SymmetryEq.
apply MIdentEq.
generalize (MIdentTheorem I).
apply IsIdent_StrongCons.
hyperreflexivity.
unfold Sub_to_Identical at 1.
unfold SubIdent_to_Ope at 1.
apply (TransitivityStrongRel (Sub_to_BOperation (S{<SubIdent_SubOpe})){<Map_Rel}).
 apply ReflexivityStrongRel2.
 hyperreflexivity.
apply (StrongSubBOpe _ _ (S{<SubIdent_SubOpe})).
apply ReflexivitySubset.
Qed.


(*
Theorem SubMIdentEqWP : forall {A} (I : #(Identical A)) (S : #(SubIdentical (o{<Ident_Ope}))) (cons : Ope_IdentCond o),
%MIdent I == %MIdent (S{<SubIdent_Ident}).
*)

(*
Theorem SubIdent_to_BOpeIn {A} : forall (o : #(BOperation A)) (S : #(%SubIdentical o)),
In o (RistableMap (Cartesian A A) A (Cartesian S S) S).
Proof.
intros o S.
assert(InSB : In S (%SubBOperation o)).
 apply SubIdent_SubOpe.
 apply SetProp.
rewrite (DSETEq' _ InSB).
apply SubBOpe_to_BOpeIn.
Qed.

Definition SubIdent_to_BOpe {A} {o : #(BOperation A)} (S : #(%SubBOperation o)) : #(BOperation S) :=
%RistMap {_ ! SubBOpe_to_BOpeIn o S}.

Theorem SubIdent_s_BOpe : forall {A} (o : #(BOperation A)) (S : #(%SubBOperation o)),
StrongRel (SubBOpe_to_BOpe S){<Map_Rel} (o{<Map_Rel}).
Proof.
intros A o S.
unfold SubBOpe_to_BOpe.
apply StrongRistMap.
Qed.
*)

(* InverseElement *)
Definition IsInverseETripleRight {A} : #(Relation (BOperation A) (Cartesian A A)) :=
MakeRelation (fun o p => &&IsIdent o (%o [%MLeft p ; %MRight p]) /\ &&IsIdent o (%o [%MRight p ; %MLeft p])).

Definition IsInverseE {A} : #(Map (BOperation A) (BRelation A)) := 
%TripleRelR_to_Map IsInverseETripleRight.

Theorem IsInverseETheorem : forall {A} (o : #(BOperation A)) (a b : #A),
&&(%IsInverseE o) a b <-> (&&IsIdent o (%o [a;b]) /\ &&IsIdent o (%o [b;a])).
Proof.
intros A o a b.
split.
 intro InvH.
 unfold IsInverseE in InvH.
 apply (TripleRelR_to_MapTheorem IsInverseETripleRight o a b) in InvH.
 put ((proj1 (MakeRelationTheorem _ _ _ _ _)) InvH) InvH'.
 clear InvH.
 put (InvH' _ _ (ReflexivityEq o) (ReflexivityEq [a;b])) InvH.
 clear InvH'.
 destruct InvH as [InvH1 InvH2].
 split.
  generalize InvH1.
  apply RelRewriteAll.
  hyperreflexivity.
  apply MapArgEq.
  apply EqualInPair'.
  split.
  apply LeftPairTheorem.
  apply RightPairTheorem.
  hyperreflexivity.

  generalize InvH2.
  apply RelRewriteAll.
  hyperreflexivity.
  apply MapArgEq.
  apply EqualInPair'.
  split.
  apply RightPairTheorem.
  apply LeftPairTheorem.
  hyperreflexivity.

 intro relHD.
 destruct relHD as [relH1 relH2].

 unfold IsInverseE.
 apply (TripleRelR_to_MapTheorem IsInverseETripleRight o).
 apply MakeRelationTheorem.
 intros o' p Eqo Eqp.
 split; apply (RelRewriteL Eqo).
  generalize relH1.
  apply RelRewriteR.
  apply MapEqAll.
  apply EqualInPair'.
  split.
  rewrite (MapArgEq' _ Eqp).
  apply SymmetryEq.
  apply LeftPairTheorem.
  rewrite (MapArgEq' _ Eqp).
  apply SymmetryEq.
  apply RightPairTheorem.
  apply Eqo.

  generalize relH2.
  apply RelRewriteR.
  apply MapEqAll.
  apply EqualInPair'.
  split.
  rewrite (MapArgEq' _ Eqp).
  apply SymmetryEq.
  apply RightPairTheorem.
  rewrite (MapArgEq' _ Eqp).
  apply SymmetryEq.
  apply LeftPairTheorem.
  apply Eqo.
Qed.

Theorem IsInverseESymmetry : forall {A}, 
In (@IsInverseE A) (RistableRMap (BOperation A) (BRelation A) (Symmetric A)).
Proof.
intros A.
apply RistableRMapTheorem.
split.
apply Sym_Rel.
intro o.
apply Rel_Sym.
intros a1 a2 relH.
apply (IsInverseETheorem o a2 a1).
apply (IsInverseETheorem o a1 a2) in relH.
apply SymmetryAnd.
apply relH.
Qed.

Theorem IsInverseETheoremComm : forall {A} (o : #(BOperation A)) a b,
&&(%IsInverseE o) a b <->
(&&IsIdent o (%o[a;b]) /\ %o[a;b] == %o[b;a])
.
Proof.
intros A o a b.
split.
 intro IH.
 apply IsInverseETheorem in IH.
 destruct IH as [IH1 IH2].
 split.
 apply IH1.
 apply (IsIdentEq o).
 apply IH1.
 apply IH2.

 intro IHD.
 destruct IHD as [IH com].
 apply IsInverseETheorem.
 split.
 apply IH.
 generalize IH.
 apply RelRewriteR.
 apply com.
Qed.

Theorem IsInverseE_DoubleIsIdent : forall {A} (o : #(BOperation A)) e,
&&IsIdent o e ->
&&(%IsInverseE o) e e.
Proof.
intros A o e IsIoe.
apply IsInverseETheorem.
apply DoubleAnd.
generalize IsIoe.
apply RelRewriteR.
apply SymmetryEq.
apply IsLeftIdentTheorem.
apply IsIdent_LeftIdent.
apply IsIoe.
Qed.


Theorem IsInverseE_IsIdent : forall {A} (o : #(BOperation A)) a b,
&&(%IsInverseE o) a b -> &&IsIdent o (%o [a;b]).
Proof.
intros A o a b InvH.
apply IsInverseETheorem in InvH.
apply (proj1 InvH).
Qed.

Theorem IsInverseE_IsIdent' : forall {A} (o : #(BOperation A)) a b,
&&(%IsInverseE o) a b -> &&IsIdent o (%o [b;a]).
Proof.
intros A o a b InvH.
apply IsInverseETheorem in InvH.
apply (proj2 InvH).
Qed.

Theorem IsInverseESymCond : forall {A} (o : #(BOperation A)),
Rel_SymCond (%IsInverseE o).
Proof.
intros A o.
apply Rel_Sym.
apply RistableRMapTheoremIn.
apply IsInverseESymmetry.
Qed.

Theorem IsInverseE_Com : forall {A} (o : #(BOperation A)) a b,
&&(%IsInverseE o) a b ->
%o[a;b] == %o[b;a].
Proof.
intros A o a b IsI.
apply IsInverseETheorem in IsI.
destruct IsI as [IsI1 IsI2].
apply (IsIdentEq o).
apply IsI1.
apply IsI2.
Qed.

Theorem IsInverseE_StrongCons : forall {A B} (o1 : #(BOperation A)) (o2 : #(BOperation B)) (a1 a2 : #A) (b1 b2 : #B),
a1 == b1 -> a2 == b2 -> StrongMap o1 o2 -> 
&&(%IsInverseE o2) b1 b2 -> &&(%IsInverseE o1) a1 a2.
Proof.
intros A B o1 o2 a1 a2 b1 b2 Eq1 Eq2 SH IsIH.
apply IsInverseETheorem in IsIH.
destruct IsIH as [IsIH1 IsIH2].
apply IsInverseETheorem.
split.
 generalize IsIH1.
 apply IsIdent_StrongCons.
 apply MapStrong.
 apply SH.
 apply EqualInPair'.
 split; assumption.
 apply SH.

 generalize IsIH2.
 apply IsIdent_StrongCons.
 apply MapStrong.
 apply SH.
 apply EqualInPair'.
 split; assumption.
 apply SH.
Qed.



Definition IsInvertible {A} : #(Relation (BOperation A) A) :=
MakeRelation (fun o a => exists b, &&(%IsInverseE o) a b).

Theorem IsInvertibleTheorem : forall {A} (o : #(BOperation A)) a,
&&IsInvertible o a <->
exists b, &&(%IsInverseE o) a b.
Proof.
intros A o a.
split.
 intro IH.
 put ((proj1 (MakeRelationTheorem _ _ _ _ _)) IH) IH'.
 apply IH'.
 hyperreflexivity.
 hyperreflexivity.
intro cond.
destruct cond as [b cond].
apply MakeRelationTheorem.
intros o' a' Eqo Eqa.
exists b.
generalize cond.
apply RelRewriteAll.
apply Eqa.
hyperreflexivity.
apply MapArgEq.
apply Eqo.
Qed.

Definition Invertible {A} : #(Map (BOperation A) (PowerSet A)) :=
%RelImageE IsInvertible.

Theorem InvertibleTheorem : forall {A} (o : #(BOperation A)) (a : #A),
In a (%Invertible o) <-> &&IsInvertible o a.
Proof.
intros A o a.
unfold Invertible.
apply RelationImageETheorem.
Qed.

Theorem InvertibleSubset : forall {A} (o : #(BOperation A)),
Subset (%Invertible o) A.
Proof.
intros A o.
unfold Invertible.
apply RelationImageESubset.
Qed.

Definition Invertical A :=
SSet' (BOperation A) (fun o => In (%IsInverseE o) (LeftTotal A A)).

Theorem Invert_Ope : forall {A}, Subset (Invertical A) (BOperation A).
Proof.
intro A.
apply SSet'Subset.
Qed.

Definition Ope_InvertCond {A} (o : #(BOperation A)) :=
forall a, &&IsInvertible o a.

Theorem IsInverseE_of_InvertInLTtl : forall {A},
In (@IsInverseE A) (RistableMap (BOperation A) (BRelation A) (Invertical A) (LeftTotal A A)).
Proof.
intros A.
apply RistableMapTheorem.
split.
 apply Invert_Ope.
split.
 unfold BRelation.
 apply LTtl_Rel.
intros o InaI.
apply SSet'Theorem in InaI.
destruct InaI as [InoB cond].
generalize (cond InoB).
apply Arrow2Rewrite; hyperreflexivity.
Qed.

Theorem Ope_Invert : forall {A} (o : #(BOperation A)),
Ope_InvertCond o <-> In o (Invertical A).
Proof.
intros A o.
split.
 intro cond.
 apply SSet'Theorem.
 split.
 apply SetProp.
 intro InoB.
 cut (In (%IsInverseE o) (LeftTotal A A)).
  apply Arrow2Rewrite.
  apply MapArgEq.
  hyperreflexivity.
  hyperreflexivity.
 rewrite (USETEq' _ BRel_Rel).
 apply Rel_LTtl.
 intro a.
 put (cond a) cond'.
 apply IsInvertibleTheorem in cond'.
 destruct cond' as [b cond'].
 exists b.
 apply cond'.
intro InoI.
intro a.
apply SSet'Theorem in InoI.
destruct InoI as [InoB cond].
put (cond InoB) cond'.
rewrite (USETEq' _ BRel_Rel) in cond'.
apply Rel_LTtl in cond'.
put (cond' a) cond''.
destruct cond'' as [b cond''].
apply IsInvertibleTheorem.
exists b.
generalize cond''.
apply RelRewrite.
rewrite (USETEq _ BRel_Rel).
apply MapArgEq.
hyperreflexivity.
Qed.
 
Theorem Invert_Identical : forall {A},
NonEmpty A -> Subset (Invertical A) (Identical A).
Proof.
intros A NEA.
intros o_ InoI.
assert(InoB : In o_ (BOperation A)).
 apply Invert_Ope.
 apply InoI.
rewrite (DSETEq' _ InoB).
rewrite (DSETEq' _ InoB) in InoI.
apply Ope_Invert in InoI.
apply Ope_Ident.
destruct NEA as [a_ InaA].
put (InoI {_!InaA}) InoI'.
apply IsInvertibleTheorem in InoI'.
destruct InoI' as [b InoI'].
apply IsInverseETheorem in InoI'.
destruct InoI' as [cond1 cond2].
exists (%{_!InoB} [{_!InaA} ; b]).
apply cond1.
Qed.
  

(* Zero Element *)
Definition IsLeftZero {A} :=
MakeRelation (fun (o : #(BOperation A)) (z : #A) => forall a : #A, %o [z;a] == z).
Definition IsRightZero {A} :=
MakeRelation (fun (o : #(BOperation A)) (z : #A) => forall a : #A, %o [a;z] == z).
Definition IsZero {A} := %AndRelation [@IsLeftZero A ; @IsRightZero A].

Theorem IsLeftZeroTheorem : forall {A} (o : #(BOperation A)) (z : #A),
&&IsLeftZero o z <-> (forall (a : #A), %o [z;a] == z).
Proof.
intros A o z.
split.
 intro relH.
 intro a.
 put ((proj1 (MakeRelationTheorem _ _ _ _ _)) relH) relH'.
 clear relH.
 put (relH' _ _ (ReflexivityEq o) (ReflexivityEq z) a) relH.
 clear relH'.
 apply relH.

 intro cond.
 apply MakeRelationTheorem.
 intros o' z' Eqo Eqz a.
 rewrite <- Eqz.
 rewrite <- (cond a).
 apply MapEqAll.
 apply EqualInPair'.
 split.
 rewrite Eqz.
 hyperreflexivity.
 hyperreflexivity.
 apply SymmetryEq.
 apply Eqo.
Qed.

Theorem IsRightZeroTheorem : forall {A} (o : #(BOperation A)) (z : #A),
&&IsRightZero o z <-> (forall (a : #A), %o [a;z] == z).
Proof.
intros A o z.
split.
 intro relH.
 intro a.
 put ((proj1 (MakeRelationTheorem _ _ _ _ _)) relH) relH'.
 clear relH.
 put (relH' _ _ (ReflexivityEq o) (ReflexivityEq z) a) relH.
 clear relH'.
 apply relH.

 intro cond.
 apply MakeRelationTheorem.
 intros o' z' Eqo Eqz a.
 rewrite <- Eqz.
 rewrite <- (cond a).
 apply MapEqAll.
 apply EqualInPair'.
 split.
 hyperreflexivity.
 rewrite Eqz.
 hyperreflexivity.
 apply SymmetryEq.
 apply Eqo.
Qed.

Theorem IsZeroTheorem2 : forall {A} (o : #(BOperation A)) (z : #A),
&&IsZero o z <-> (&&IsLeftZero o z /\ &&IsRightZero o z).
Proof.
intros A o z.
split.
 intro relH.
 unfold IsZero in relH.
 apply AndRelationTheorem in relH.
 assumption.

 intro relHD.
 destruct relHD as [relH1 relH2].
 unfold IsZero.
 apply AndRelationTheorem.
 split; assumption.
Qed.

Theorem IsZeroTheorem : forall {A} (o : #(BOperation A)) (z : #A),
&&IsZero o z <-> (forall a, %o [z;a] == z /\ %o [a;z] == z).
Proof.
intros A o z.
split.
 intro OH.
 intro a.
 apply IsZeroTheorem2 in OH.
 destruct OH as [OHL OHR].
 put ((proj1 (IsLeftZeroTheorem _ _)) OHL) OHL'.
 put ((proj1 (IsRightZeroTheorem _ _)) OHR) OHR'.
 split.
 apply OHL'.
 apply OHR'.

 intro cond.
 apply IsZeroTheorem2.
 split.
  apply IsLeftZeroTheorem.
  intro a.
  destruct (cond a) as [cond1 cond2].
  apply cond1.

  apply IsRightZeroTheorem.
  intro a.
  destruct (cond a) as [cond1 cond2].
  apply cond2.
Qed.

Theorem IsZero_LeftZero : forall {A} (o : #(BOperation A)) (z : #A),
&&IsZero o z -> &&IsLeftZero o z.
Proof.
intros A o z IH.
apply IsZeroTheorem2 in IH.
destruct IH as [IH _].
apply IH.
Qed.

Theorem IsZero_RightZero : forall {A} (o : #(BOperation A)) (z : #A),
&&IsZero o z -> &&IsRightZero o z.
Proof.
intros A o z IH.
apply IsZeroTheorem2 in IH.
destruct IH as [_ IH].
apply IH.
Qed.

Theorem RUnqIsZero : forall {A}, Rel_RUnqCond (@IsZero A).
Proof.
intro A.
intro o.
intros e1 e2 Eq1 Eq2.
apply (TransitivityEq (%o [e1;e2])).
 apply SymmetryEq.
 apply IsLeftZeroTheorem.
 apply IsZero_LeftZero.
 apply Eq1.

 apply IsRightZeroTheorem.
 apply IsZero_RightZero.
 apply Eq2.
Qed.

Theorem IsZeroEq : forall {A} (o : #(BOperation A)) z1 z2,
&&IsZero o z1 -> &&IsZero o z2 -> z1 == z2.
Proof.
intros A o z1 z2 H1 H2.
apply (RightUniqueEq IsZero o).
 apply RUnqIsZero.
apply H1.
apply H2.
Qed.

Theorem IsZero_StrongCons : forall {A B} (o1 : #(BOperation A)) (o2 : #(BOperation B)) (e1 : #A) (e2 : #B),
e1 == e2 -> StrongRel (o1{<Map_Rel}) (o2{<Map_Rel}) -> 
&&IsZero o2 e2 -> &&IsZero o1 e1.
Proof.
intros A B o1 o2 e1 e2 Eqe SH IH.
apply IsZeroTheorem.
put ((proj1 (IsZeroTheorem _ _)) IH) IH'.
clear IH.
intro a.
assert(sub : Subset A B).
 apply (StrongBOpeSubset o1 o2).
 apply SH.
set (a{<sub}) as a'.
destruct (IH' a') as [IH1 IH2].
split.
 apply (TransitivityEq e2).
 rewrite <- IH1.
 apply MapStrong.
 apply SH.
 apply EqualInPair'.
 split.
  apply Eqe.
  hyperreflexivity.
 apply SymmetryEq.
 apply Eqe.

 apply (TransitivityEq e2).
 rewrite <- IH2.
 apply MapStrong.
 apply SH.
 apply EqualInPair'.
 split.
  hyperreflexivity.
  apply Eqe.
 apply SymmetryEq.
 apply Eqe.
Qed.

(*************************************)
(* Homomorphism in Inverse and Ident *)
(*************************************)
Definition IsHomomorphism_of_Ident {A B} : #(Relation (Cartesian (BOperation A) (BOperation B)) (Map A B)) :=
MakeRelation (fun od f => &&IsHomomorphism_of_BOpe od f /\ (forall e, &&IsIdent (%MLeft od) e -> &&IsIdent (%MRight od) (%f e))).

Theorem IsHomomorphism_of_IdentTheorem : forall {A B} (o1 : #(BOperation A)) (o2 : #(BOperation B)) (f : #(Map A B)),
&&IsHomomorphism_of_Ident [o1;o2] f <->
(&&IsHomomorphism_of_BOpe [o1;o2] f /\ (forall e, &&IsIdent o1 e -> &&IsIdent o2 (%f e))).
Proof.
intros A B o1 o2 f.
split.
 intro HH.
 put ((proj1 (MakeRelationTheorem _ _ _ _ _)) HH) HH'.
 clear HH.
 put (HH' _ _ (ReflexivityEq [o1;o2]) (ReflexivityEq f)) HH.
 clear HH'.
 destruct HH as [HH1 HH2].
 split.
 apply HH1.
 intros e cond.
 cut (&&IsIdent (%MRight [o1;o2]) (%f e)).
  apply RelRewriteL.
  apply RightPairTheorem.
 apply HH2.
 generalize cond.
 apply RelRewriteL.
 apply SymmetryEq.
 apply LeftPairTheorem.
intro cond.
destruct cond as [cond1 cond2].
put ((proj1 (IsHomomorphism_of_BOpeTheorem _ _ _)) cond1) cond1'.
clear cond1.
apply MakeRelationTheorem.
intros o1o2 f' Eqo Eqf.
split.
 apply (RelRewriteL Eqo).
 apply (RelRewriteR Eqf).
 apply IsHomomorphism_of_BOpeTheorem.
 apply cond1'.
intros e IsH.
cut (&&IsIdent o2 (%f e)).
 apply RelRewriteAll.
 rewrite (MapArgEq' _ Eqo).
 apply SymmetryEq.
 apply RightPairTheorem.
 apply MapEq.
 rewrite Eqf.
 hyperreflexivity.
 hyperreflexivity.
apply cond2.
generalize IsH.
apply RelRewriteL.
rewrite (MapArgEq' _ Eqo).
apply LeftPairTheorem.
Qed.

Definition Homomorphism_of_Ident {A B} : #(Map (Cartesian (BOperation A) (BOperation B)) (PowerSet (Map A B))) :=
%RelImageE IsHomomorphism_of_Ident.

Theorem HomIdnt_Map : forall {A B} {od : #(Cartesian (BOperation A) (BOperation B))},
Subset (%Homomorphism_of_Ident od) (Map A B).
Proof.
intros A B od.
unfold Homomorphism_of_Ident.
apply RelationImageESubset.
Qed.

Theorem Homomorphism_of_IdentTheorem : forall {A B} (oa : #(BOperation A)) (ob : #(BOperation B)) (f : #(Map A B)),
In f (%Homomorphism_of_Ident [oa;ob]) <->
&&IsHomomorphism_of_Ident [oa;ob] f.
Proof.
intros A B oa ob f.
unfold Homomorphism_of_Ident.
apply RelationImageETheorem.
Qed.

Definition Homomorphic_of_Ident {A B} : #(Relation (BOperation A) (BOperation B)) :=
MakeRelation (fun oa ob => exists f, &&IsHomomorphism_of_Ident [oa;ob] f).
(*
Definition SHomomorphic_of_BOpe {A B} : #(Relation (BOperation A) (BOperation B)) :=
MakeRelation (fun oa ob => exists f, &&SIsHomomorphism_of_BOpe [oa;ob] f).

Definition IHomomorphic_of_BOpe {A B} : #(Relation (BOperation A) (BOperation B)) :=
MakeRelation (fun oa ob => exists f, &&IIsHomomorphism_of_BOpe [oa;ob] f).

Definition Isomorphic_of_BOpe {A B} : #(Relation (BOperation A) (BOperation B)) :=
MakeRelation (fun oa ob => exists f, &&Isomorphism_of_BOpe [oa;ob] f).
*)
Theorem Homomorphic_of_IdentTheorem : forall {A B} (oa : #(BOperation A)) (ob : #(BOperation B)),
(&&Homomorphic_of_Ident oa ob) <->
exists f, &&IsHomomorphism_of_Ident [oa;ob] f.
Proof.
intros A B oa ob.
split.
 intro HH.
 put ((proj1 (MakeRelationTheorem _ _ _ _ _)) HH) HH'.
 clear HH.
 put (HH' _ _ (ReflexivityEq oa) (ReflexivityEq ob)) HH.
 clear HH'.
 apply HH.
intro cond.
apply MakeRelationTheorem.
intros oa' ob' Eqoa Eqob.
destruct cond as [f cond].
exists f.
generalize cond.
apply RelRewriteL.
apply EqualInPair'.
split.
apply Eqoa.
apply Eqob.
Qed.


Theorem IsIdent_IsSHomomorphism_BOpe : forall {A B} (o1 : #(BOperation A)) (o2 : #(BOperation B)) (f : #(Map A B)),
&&IsSHomomorphism_of_BOpe [o1;o2] f ->
(forall e, &&IsIdent o1 e -> &&IsIdent o2 (%f e)).
Proof.
intros A B o1 o2 f HH e IH1.
apply IsSHomomorphism_of_BOpeTheorem in HH.
destruct HH as [HH InfSur].
apply Map_Sur in InfSur.
put ((proj1 (IsHomomorphism_of_BOpeTheorem _ _ _)) HH) HH'.
put ((proj1 (IsIdentTheorem _ _)) IH1) IH1'.
apply IsIdentTheorem.
intro fa.
destruct (InfSur fa) as [a Eqfa].
destruct (IH1' a) as [IHe1 IHe2].
split.
 apply (TransitivityEq (%o2 [%f e; %f a])).
  apply MapArgEq.
  apply EqualInPair'R.
  apply SymmetryEq.
  apply Eqfa.
 rewrite <- HH'.
 rewrite (MapArgEq _ IHe1).
 apply Eqfa.

 apply (TransitivityEq (%o2 [%f a; %f e])).
  apply MapArgEq.
  apply EqualInPair'L.
  apply SymmetryEq.
  apply Eqfa.
 rewrite <- HH'.
 rewrite (MapArgEq _ IHe2).
 apply Eqfa.
Qed.

(* IsHomomorphism of Inverse *)
Definition IsHomomorphism_of_Invert {A B} : #(Relation (Cartesian (BOperation A) (BOperation B)) (Map A B)) :=
MakeRelation (fun od f => &&IsHomomorphism_of_BOpe od f /\ forall a, &&IsInvertible (%MLeft od) a -> &&IsInvertible (%MRight od) (%f a)).

Theorem IsHomomorphism_of_InvertTheorem : forall {A B} (o1 : #(BOperation A)) (o2 : #(BOperation B)) (f : #(Map A B)),
&&IsHomomorphism_of_Invert [o1;o2] f <->
(&&IsHomomorphism_of_BOpe [o1;o2] f /\ (forall a, &&IsInvertible o1 a -> &&IsInvertible o2 (%f a))).
Proof.
intros A B o1 o2 f.
split.
 intro HH.
 put ((proj1 (MakeRelationTheorem _ _ _ _ _)) HH) HH'.
 clear HH.
 put (HH' _ _ (ReflexivityEq _) (ReflexivityEq f)) HH.
 clear HH'.
 destruct HH as [HH cond].
 split.
 apply HH.
 intros a IH.
 cut (&&IsInvertible (%MRight [o1;o2]) (%f a)).
  apply RelRewriteL.
  apply RightPairTheorem.
 apply cond.
 generalize IH.
 apply RelRewriteL.
 apply SymmetryEq.
 apply LeftPairTheorem.
intro cond.
destruct cond as [HH cond].
apply MakeRelationTheorem.
intros od f' Eqo Eqf.
split.
 apply (RelRewriteR Eqf).
 apply (RelRewriteL Eqo).
 apply HH.
intros a IH.
cut (&&IsInvertible o2 (%f a)).
 apply RelRewriteAll.
 rewrite (MapArgEq' _ Eqo).
 apply SymmetryEq.
 apply RightPairTheorem.
 apply MapEq.
 apply Eqf.
 hyperreflexivity.
apply cond.
generalize IH.
apply RelRewriteL.
rewrite (MapArgEq' _ Eqo).
apply LeftPairTheorem.
Qed.


Definition Homomorphic_of_Invert {A B} : #(Relation (BOperation A) (BOperation B)) :=
MakeRelation (fun oa ob => exists f, &&IsHomomorphism_of_Invert [oa;ob] f).
(*
Definition SHomomorphic_of_BOpe {A B} : #(Relation (BOperation A) (BOperation B)) :=
MakeRelation (fun oa ob => exists f, &&SIsHomomorphism_of_BOpe [oa;ob] f).

Definition IHomomorphic_of_BOpe {A B} : #(Relation (BOperation A) (BOperation B)) :=
MakeRelation (fun oa ob => exists f, &&IIsHomomorphism_of_BOpe [oa;ob] f).

Definition Isomorphic_of_BOpe {A B} : #(Relation (BOperation A) (BOperation B)) :=
MakeRelation (fun oa ob => exists f, &&Isomorphism_of_BOpe [oa;ob] f).
*)

Definition Homomorphism_of_Invert {A B} : #(Map (Cartesian (BOperation A) (BOperation B)) (PowerSet (Map A B))) :=
%RelImageE IsHomomorphism_of_Invert.

Theorem HomInvt_Map : forall {A B} {od : #(Cartesian (BOperation A) (BOperation B))},
Subset (%Homomorphism_of_Invert od) (Map A B).
Proof.
intros A B od.
unfold Homomorphism_of_Invert.
apply RelationImageESubset.
Qed.

Theorem Homomorphism_of_InvertTheorem : forall {A B} (oa : #(BOperation A)) (ob : #(BOperation B)) (f : #(Map A B)),
In f (%Homomorphism_of_Invert [oa;ob]) <->
&&IsHomomorphism_of_Invert [oa;ob] f.
Proof.
intros A B oa ob f.
unfold Homomorphism_of_Invert.
apply RelationImageETheorem.
Qed.

Theorem Homomorphic_of_InvertTheorem : forall {A B} (oa : #(BOperation A)) (ob : #(BOperation B)),
(&&Homomorphic_of_Invert oa ob) <->
exists f, &&IsHomomorphism_of_Invert [oa;ob] f.
Proof.
intros A B oa ob.
split.
 intro HH.
 put ((proj1 (MakeRelationTheorem _ _ _ _ _)) HH) HH'.
 apply HH'.
 hyperreflexivity.
 hyperreflexivity.
intro cond.
destruct cond as [f cond].
apply MakeRelationTheorem.
intros oa' ob' Eqoa Eqob.
exists f.
generalize cond.
apply RelRewriteL.
apply EqualInPair'.
split.
apply Eqoa.
apply Eqob.
Qed.

Definition IsHomomorphism_of_Inverse {A B} : #(Relation (Cartesian (BOperation A) (BOperation B)) (Map A B)) :=
MakeRelation (fun od f => &&IsHomomorphism_of_BOpe od f /\ forall a b, &&(%IsInverseE (%MLeft od)) a b -> &&(%IsInverseE (%MRight od)) (%f a) (%f b)).

Theorem IsHomomorphism_of_InverseTheorem : forall {A B} (o1 : #(BOperation A)) (o2 : #(BOperation B)) (f : #(Map A B)),
&&IsHomomorphism_of_Inverse [o1;o2] f <->
(&&IsHomomorphism_of_BOpe [o1;o2] f /\ (forall a b, &&(%IsInverseE o1) a b -> &&(%IsInverseE o2) (%f a) (%f b))).
Proof.
intros A B o1 o2 f.
split.
 intro HH.
 put ((proj1 (MakeRelationTheorem _ _ _ _ _)) HH) HH'.
 clear HH.
 put (HH' _ _ (ReflexivityEq _) (ReflexivityEq f)) HH.
 clear HH'.
 destruct HH as [HH cond].
 split.
 apply HH.
 intros a b IsE.
 cut (&&(%IsInverseE (%MRight [o1;o2])) (%f a) (%f b)).
  apply RelRewrite.
  apply MapArgEq.
  apply RightPairTheorem.
 apply cond.
 generalize IsE.
 apply RelRewrite.
 apply MapArgEq.
 apply SymmetryEq.
 apply LeftPairTheorem.

 intro cond.
 destruct cond as [HH cond].
 apply MakeRelationTheorem.
 intros o1o2 f' Eqo Eqf.
 split.
  apply (RelRewriteL Eqo).
  apply (RelRewriteR Eqf).
  apply HH.
 intros a b IsH.
 cut (&&(%IsInverseE o2) (%f a) (%f b)).
  apply RelRewriteAll.
  apply MapEq.
  apply Eqf.
  apply MapEq.
  apply Eqf.
  apply MapArgEq.
  apply SymmetryEq.
  rewrite (MapArgEq' _ Eqo).
  apply RightPairTheorem.
 apply cond.
 generalize IsH.
 apply RelRewrite.
 apply MapArgEq.
 rewrite (MapArgEq' _ Eqo).
 apply LeftPairTheorem.
Qed.

Definition Homomorphism_of_Inverse {A B} : #(Map (Cartesian (BOperation A) (BOperation B)) (PowerSet (Map A B))) :=
%RelImageE IsHomomorphism_of_Inverse.

Theorem HomInvs_Map : forall {A B} {od : #(Cartesian (BOperation A) (BOperation B))},
Subset (%Homomorphism_of_Inverse od) (Map A B).
Proof.
intros A B od.
unfold Homomorphism_of_Inverse.
apply RelationImageESubset.
Qed.

Theorem Homomorphism_of_InverseTheorem : forall {A B} (oa : #(BOperation A)) (ob : #(BOperation B)) (f : #(Map A B)),
In f (%Homomorphism_of_Inverse [oa;ob]) <->
&&IsHomomorphism_of_Inverse [oa;ob] f.
Proof.
intros A B oa ob f.
unfold Homomorphism_of_Inverse.
apply RelationImageETheorem.
Qed.

Definition Homomorphic_of_Inverse {A B} : #(Relation (BOperation A) (BOperation B)) :=
MakeRelation (fun oa ob => exists f, &&IsHomomorphism_of_Inverse [oa;ob] f).

Theorem Homomorphic_of_InverseTheorem : forall {A B} (oa : #(BOperation A)) (ob : #(BOperation B)),
(&&Homomorphic_of_Inverse oa ob) <->
exists f, &&IsHomomorphism_of_Inverse [oa;ob] f.
Proof.
intros A B oa ob.
split.
 intro HIH.
 put ((proj1 (MakeRelationTheorem _ _ _ _ _)) HIH) HIH'.
 apply HIH'.
 hyperreflexivity.
 hyperreflexivity.

 intro cond.
 destruct cond as [f cond].
 apply MakeRelationTheorem.
 intros oa' ob' Eqoa Eqob.
 exists f.
 generalize cond.
 apply RelRewriteL.
 apply EqualInPair'.
 split.
 apply Eqoa.
 apply Eqob.
Qed.


Theorem IsHomomorphism_of_Ident_IsHomomorphism_of_Inverse : forall {A B} (oa : #(BOperation A)) (ob : #(BOperation B)) (f : #(Map A B)),
&&IsHomomorphism_of_Ident [oa;ob] f ->
&&IsHomomorphism_of_Inverse [oa;ob] f.
Proof.
intros A B oa ob f HIH.
apply IsHomomorphism_of_IdentTheorem in HIH.
destruct HIH as [HIH cond].
apply IsHomomorphism_of_InverseTheorem.
split.
apply HIH.
intros a b IsIH.
apply IsInverseETheorem in IsIH.
destruct IsIH as [IsIH1 IsIH2].
put ((proj1 (IsHomomorphism_of_BOpeTheorem _ _ _)) HIH) HIH'.
apply IsInverseETheorem.
split.
 cut (&&IsIdent ob (%f (%oa [a;b]))).
  apply RelRewriteR.
  rewrite HIH'.
  hyperreflexivity.
 apply cond.
 apply IsIH1.

 cut (&&IsIdent ob (%f (%oa [b;a]))).
  apply RelRewriteR.
  rewrite HIH'.
  hyperreflexivity.
 apply cond.
 apply IsIH2.
Qed.


Theorem IsHomomorphism_of_Inverse_IsHomomorphism_of_Invert : forall {A B} (oa : #(BOperation A)) (ob : #(BOperation B)) (f : #(Map A B)),
&&IsHomomorphism_of_Inverse [oa;ob] f ->
&&IsHomomorphism_of_Invert [oa;ob] f.
Proof.
intros A B oa ob f HIH.
apply IsHomomorphism_of_InverseTheorem in HIH.
destruct HIH as [Homf InvCond].
apply IsHomomorphism_of_InvertTheorem.
split.
apply Homf.
intros a IsIa.
apply IsInvertibleTheorem in IsIa.
destruct IsIa as [Ia IsIIa].
put (InvCond _ _ IsIIa) Invfa.
apply IsInvertibleTheorem.
exists (%f Ia).
apply Invfa.
Qed.

Theorem IsHomomorphism_of_Ident_IsHomomorphism_of_Invert : forall {A B} (oa : #(BOperation A)) (ob : #(BOperation B)) (f : #(Map A B)),
&&IsHomomorphism_of_Ident [oa;ob] f ->
&&IsHomomorphism_of_Invert [oa;ob] f.
Proof.
intros A B oa ob f HIH.
apply IsHomomorphism_of_Inverse_IsHomomorphism_of_Invert.
apply IsHomomorphism_of_Ident_IsHomomorphism_of_Inverse.
apply HIH.
Qed.





(* Commutative *)
Definition Commutative A :=
SSet' (BOperation A) (fun o => forall a b, %o [a;b] == %o [b;a]).

Theorem Comm_Ope {A} : Subset (Commutative A) (BOperation A).
Proof.
apply SSet'Subset.
Qed.

Definition Ope_CommCond {A} (o : #(BOperation A)) := forall a b, %o [a;b] == %o [b;a].

Theorem Ope_Comm : forall {A} (o : #(BOperation A)),
Ope_CommCond o <-> In o (Commutative A).
Proof.
intros A o.
split.
 intro cond.
 apply SSet'Theorem.
 split.
 apply SetProp.
 intros InoB a b.
 apply (TransitivityEq (%o [a;b])).
  hyperreflexivity.
 apply (TransitivityEq (%o [b;a])).
  apply cond.
 hyperreflexivity.

 intro InoC.
 intros a b.
 apply SSet'Theorem in InoC.
 destruct InoC as [InoB InoC].
 apply (TransitivityEq (%{o ! InoB} [a;b])).
  hyperreflexivity.
 apply (TransitivityEq (%{o ! InoB} [b;a])).
  apply InoC.
 hyperreflexivity.
Qed.

Theorem Ope_CommCond_StrongCons : forall {A B} (o1 : #(BOperation A)) (o2 : #(BOperation B)),
StrongRel (o1{<Map_Rel}) (o2{<Map_Rel}) -> Ope_CommCond o2 -> Ope_CommCond o1.
Proof.
intros A B o1 o2 SH cond.
intros a1 a2.
assert(sub : Subset A B).
 apply (StrongBOpeSubset o1 o2).
 apply SH.
set a1{<sub} as b1.
set a2{<sub} as b2.
apply (TransitivityEq (%o2 [b1;b2])).
 apply MapStrong.
 apply SH.
 hyperreflexivity.
rewrite cond.
apply SymmetryEq.
apply MapStrong.
apply SH.
hyperreflexivity.
Qed.

Theorem Ope_CommCond_SHomomorphic : forall {A B} (o1 : #(BOperation A)) (o2 : #(BOperation B)),
&&SHomomorphic_of_BOpe o1 o2 -> Ope_CommCond o1 -> Ope_CommCond o2.
Proof.
intros A B o1 o2 SHH OC.
intros a2 b2.
apply SHomomorphic_of_BOpeTheorem in SHH.
destruct SHH as [f SHH].
apply IsSHomomorphism_of_BOpeTheorem in SHH.
destruct SHH as [HH InfS].
put ((proj1 (IsHomomorphism_of_BOpeTheorem _ _ _)) HH) HH'.
clear HH.
apply Map_Sur in InfS.
destruct (InfS a2) as [a1 Eqfa1].
destruct (InfS b2) as [b1 Eqfb1].
apply (TransitivityEq (%o2 [%f a1 ; %f b1])).
 apply SymmetryEq.
 apply MapArgEq.
 apply EqualInPair'.
 split; assumption.
 rewrite <- HH'.
apply (TransitivityEq (%f (%o1 [b1;a1]))).
 apply MapArgEq.
 apply OC.
rewrite HH'.
apply MapArgEq.
apply EqualInPair'.
split; assumption.
Qed.

Theorem Ope_CommCond_Product : forall {A B} (o1 : #(BOperation A)) (o2 : #(BOperation B)),
Ope_CommCond o1 -> Ope_CommCond o2 -> Ope_CommCond (%ProductOperation [o1;o2]).
Proof.
intros A B o1 o2 OC1 OC2.
intros ab1 ab2.
put (CartesianIsPair' _ _ _ (SetProp ab1)) Eqab1.
destruct Eqab1 as [a1 Eqab1].
destruct Eqab1 as [b1 Eqab1].
put (CartesianIsPair' _ _ _ (SetProp ab2)) Eqab2.
destruct Eqab2 as [a2 Eqab2].
destruct Eqab2 as [b2 Eqab2].
rewrite (MapArgEq _ (EqualInPair'L _ _ _ _ _ Eqab1)).
rewrite (MapArgEq _ (EqualInPair'R _ _ _ _ _ Eqab2)).
rewrite (MapArgEq _ (EqualInPair'L _ _ _ _ _ Eqab2)).
rewrite (MapArgEq _ (EqualInPair'R _ _ _ _ _ Eqab1)).
apply (TransitivityEq [%o1 [a1;a2] ; %o2 [b1;b2]]).
 rewrite ProductOperationTheorem.
 hyperreflexivity.
apply (TransitivityEq [%o1 [a2;a1] ; %o2 [b2;b1]]).
 apply EqualInPair'.
 split.
  apply OC1.
 apply OC2.
rewrite ProductOperationTheorem.
hyperreflexivity.
Qed.

Theorem IsIdentTheoremL : forall {A} (o : #(BOperation A)) (e : #A),
Ope_CommCond o ->
(forall a, %o [e;a] == a) -> &&IsIdent o e.
Proof.
intros A o e com cond.
apply IsIdentTheorem.
intro a.
split.
 apply cond.
rewrite com.
apply cond.
Qed.

Theorem IsIdentTheoremR : forall {A} (o : #(BOperation A)) (e : #A),
Ope_CommCond o ->
(forall a, %o [a;e] == a) -> &&IsIdent o e.
Proof.
intros A o e com cond.
apply IsIdentTheorem.
intro a.
apply SymmetryAnd.
split.
 apply cond.
rewrite com.
apply cond.
Qed.

Theorem IsZeroTheoremL : forall {A} (o : #(BOperation A)) (z : #A),
Ope_CommCond o ->
(forall a, %o [z;a] == z) -> &&IsZero o z.
Proof.
intros A o z com cond.
apply IsZeroTheorem.
intro a.
split.
 apply cond.
rewrite com.
apply cond.
Qed.

Theorem IsZeroTheoremR : forall {A} (o : #(BOperation A)) (z : #A),
Ope_CommCond o ->
(forall a, %o [a;z] == z) -> &&IsZero o z.
Proof.
intros A o z com cond.
apply IsZeroTheorem.
intro a.
split.
 rewrite com.
 apply cond.
apply cond.
Qed.
 
Theorem IsInverseETheoremL : forall {A} (o : #(BOperation A)) (a b : #A),
Ope_CommCond o ->
(&&IsIdent o (%o [a;b])) -> &&(%IsInverseE o) a b.
Proof.
intros A o a b com cond.
apply IsInverseETheorem.
split.
 apply cond.
apply (RelRewriteR' (com _ _)).
apply cond.
Qed.

Theorem IsInverseETheoremR : forall {A} (o : #(BOperation A)) (a b : #A),
Ope_CommCond o ->
(&&IsIdent o (%o [b;a])) -> &&(%IsInverseE o) a b.
Proof.
intros A o a b com cond.
apply IsInverseESymCond.
apply IsInverseETheoremL.
apply com.
apply cond.
Qed.

(* Associativity *)
Definition SemiGroup A :=
SSet' (BOperation A) (fun r => forall (a b c : #A), %r [%r [a;b]; c] == %r [ a; %r [ b ; c ] ]).

Theorem SGrp_Ope {A} : Subset (SemiGroup A) (BOperation A).
Proof.
apply SSet'Subset.
Qed.

Definition Ope_SGrpCond {A} (o : #(BOperation A)) :=
 forall a b c, %o [%o [a;b] ; c] == %o [a ; %o [b;c]].

Theorem Ope_SGrp : forall {A} (o : #(BOperation A)),
Ope_SGrpCond o <-> In o (SemiGroup A).
Proof.
intros A o.
split.
 intro cond.
 apply SSet'Theorem.
 split.
 apply (SetProp).
 intros InoB a b c.
 apply (TransitivityEq (%o [%o [a;b] ; c])).
  hyperreflexivity.
 rewrite cond.
 hyperreflexivity.

 intro InoS.
 intros a b c.
 apply SSet'Theorem in InoS.
 destruct InoS as [InoB InoS].
 apply (TransitivityEq (%{o ! InoB} [%{o ! InoB} [a;b] ; c])).
  hyperreflexivity.
 rewrite InoS.
 hyperreflexivity.
Qed.

Theorem Ope_SGrpCond_StrongCons : forall {A B} (o1 : #(BOperation A)) (o2 : #(BOperation B)),
StrongRel (o1{<Map_Rel}) (o2{<Map_Rel}) -> Ope_SGrpCond o2 -> Ope_SGrpCond o1.
Proof.
intros A B o1 o2 SH cond.
intros a b c.
assert(sub : Subset A B).
 apply (StrongBOpeSubset o1 o2).
 apply SH.
apply (TransitivityEq (%o2 [%o2 [a{<sub};b{<sub}] ;c{<sub}])).
 apply MapStrong.
 apply SH.
 apply EqualInPair'.
 split.
  apply MapStrong.
  apply SH.
 hyperreflexivity.
 hyperreflexivity.
rewrite cond.
apply SymmetryEq.
apply MapStrong.
apply SH.
apply EqualInPair'.
split.
hyperreflexivity.
apply MapStrong.
apply SH.
hyperreflexivity.
Qed.

Theorem Ope_SGrpCond_SHomomorphic : forall {A B} (o1 : #(BOperation A)) (o2 : #(BOperation B)),
&&SHomomorphic_of_BOpe o1 o2 -> Ope_SGrpCond o1 -> Ope_SGrpCond o2.
Proof.
intros A B o1 o2 SHH OC.
intros a2 b2.
apply SHomomorphic_of_BOpeTheorem in SHH.
destruct SHH as [f SHH].
apply IsSHomomorphism_of_BOpeTheorem in SHH.
destruct SHH as [HH InfS].
put ((proj1 (IsHomomorphism_of_BOpeTheorem _ _ _)) HH) HH'.
clear HH.
apply Map_Sur in InfS.
intro c2.
destruct (InfS a2) as [a1 Eqfa1].
destruct (InfS b2) as [b1 Eqfb1].
destruct (InfS c2) as [c1 Eqfc1].
apply SymmetryEq in Eqfa1.
apply SymmetryEq in Eqfb1.
apply SymmetryEq in Eqfc1.
rewrite (MapArgEq _ (EqualInPair'L _ _ _ _ _ (MapArgEq _ (EqualInPair'L _ _ _ _ _ Eqfa1)))).
rewrite (MapArgEq _ (EqualInPair'L _ _ _ _ _ (MapArgEq _ (EqualInPair'R _ _ _ _ _ Eqfb1)))).
rewrite (MapArgEq _ (EqualInPair'R _ _ _ _ _ Eqfc1)).
rewrite (MapArgEq _ (EqualInPair'L _ _ _ _ _ Eqfa1)).
rewrite (MapArgEq _ (EqualInPair'R _ _ _ _ _ (MapArgEq _ (EqualInPair'L _ _ _ _ _ Eqfb1)))).
rewrite (MapArgEq _ (EqualInPair'R _ _ _ _ _ (MapArgEq _ (EqualInPair'R _ _ _ _ _ Eqfc1)))).
apply (TransitivityEq (%f (%o1 [%o1 [a1;b1]; c1]))).
 rewrite <- (MapArgEq _ (EqualInPair'L _ _ _ _ _ (HH' _ _))).
 rewrite <- HH'.
 hyperreflexivity.
rewrite (MapArgEq _ (OC _ _ _)).
rewrite <- (MapArgEq _ (EqualInPair'R _ _ _ _ _ (HH' _ _))).
rewrite <- HH'.
hyperreflexivity.
Qed.

Theorem IsHomomorphism_of_Invert_IsHomomorphism_of_Ident_inSGrp : forall {A B} (oa : #(BOperation A)) (ob : #(BOperation B)) (f : #(Map A B)),
Ope_SGrpCond ob ->
&&IsHomomorphism_of_Invert [oa;ob] f ->
&&IsHomomorphism_of_Ident [oa;ob] f.
Proof.
intros A B oa ob f SGrpcond HIH.
apply IsHomomorphism_of_InvertTheorem in HIH.
apply IsHomomorphism_of_IdentTheorem.
destruct HIH as [HH Icond].
split.
apply HH.
intros e IsIe.
assert(Eqeee : %oa[e;e] == e).
 apply IsLeftIdentTheorem.
 apply IsIdent_LeftIdent.
 apply IsIe.
assert(IsInve : &&IsInvertible oa e).
 apply IsInvertibleTheorem.
 exists e.
 apply IsInverseETheorem.
 apply DoubleAnd.
 apply (RelRewriteR' Eqeee).
 apply IsIe.
put (Icond _ IsInve) IsInvfe.
apply IsInvertibleTheorem in IsInvfe.
destruct IsInvfe as [feI IsInvfe].
put ((proj1 (IsHomomorphism_of_BOpeTheorem _ _ _)) HH) comf.
assert(Eqfeee : %ob[%f e;%f e] == %f e).
 rewrite <- comf.
 apply MapArgEq.
 apply Eqeee.
assert(EqfeI : %f e == %ob [%f e;feI]).
 apply (TransitivityEq (%ob[%f e;%ob[%f e;feI]])).
  apply SymmetryEq.
  apply IsRightIdentTheorem.
  apply IsIdent_RightIdent.
  apply IsInverseETheorem in IsInvfe.
  destruct IsInvfe as [IsInvfe _].
  apply IsInvfe.
 rewrite <- SGrpcond.
 apply MapArgEq.
 apply EqualInPair'L.
 apply Eqfeee.
apply (RelRewriteR' EqfeI).
apply IsInverseETheorem in IsInvfe.
destruct IsInvfe as [IsInvfe _].
apply IsInvfe.
Qed.

Theorem IsHomomorphism_of_Invert_IsHomomorphism_of_Inverse_inSGrp : forall {A B} (oa : #(BOperation A)) (ob : #(BOperation B)) (f : #(Map A B)),
Ope_SGrpCond ob ->
&&IsHomomorphism_of_Invert [oa;ob] f ->
&&IsHomomorphism_of_Inverse [oa;ob] f.
Proof.
intros A B oa ob f SGrpcond HIH.
apply IsHomomorphism_of_Ident_IsHomomorphism_of_Inverse.
apply IsHomomorphism_of_Invert_IsHomomorphism_of_Ident_inSGrp.
apply SGrpcond.
apply HIH.
Qed.

Theorem Hom_Invert_Ident_inSGrp : forall {A B} (o1 : #(BOperation A)) (o2 : #(BOperation B)) (f : #(Map A B)) e,
Ope_SGrpCond o2 ->
&&IsHomomorphism_of_BOpe [o1;o2] f ->
&&IsInvertible o2 (%f e) ->
&&IsIdent o1 e ->
&&IsIdent o2 (%f e).
Proof.
intros A B o1 o2 f e.
intros AssB HomH InvH IndH.
apply IsInvertibleTheorem in InvH.
destruct InvH as [Invfe InvH].
cut (&&IsIdent o2 (%o2 [%f e ; Invfe])).
 apply RelRewriteR.
 apply SymmetryEq.
 apply (TransitivityEq (%o2 [%f e ; %o2 [%f e ; Invfe]])).
  apply SymmetryEq.
  apply IsRightIdentTheorem.
  apply IsIdent_RightIdent.
  apply IsInverseE_IsIdent.
  apply InvH.
 rewrite <- AssB.
 apply MapArgEq.
 apply EqualInPair'L.
 put ((proj1 (IsHomomorphism_of_BOpeTheorem _ _ _)) HomH) HomH'.
 rewrite <- HomH'.
 apply MapArgEq.
 apply IsLeftIdentTheorem.
 apply IsIdent_LeftIdent.
 apply IndH.
apply IsInverseE_IsIdent.
apply InvH.
Qed.


Theorem Ope_SGrpCond_Product : forall {A B} (o1 : #(BOperation A)) (o2 : #(BOperation B)),
Ope_SGrpCond o1 -> Ope_SGrpCond o2 -> Ope_SGrpCond (%ProductOperation [o1;o2]).
Proof.
intros A B o1 o2 OC1 OC2.
intros aa bb cc.
put (CartesianIsPair' _ _ _ (SetProp aa)) Eqaa.
destruct Eqaa as [a1 Eqaa].
destruct Eqaa as [a2 Eqaa].
put (CartesianIsPair' _ _ _ (SetProp bb)) Eqbb.
destruct Eqbb as [b1 Eqbb].
destruct Eqbb as [b2 Eqbb].
put (CartesianIsPair' _ _ _ (SetProp cc)) Eqcc.
destruct Eqcc as [c1 Eqcc].
destruct Eqcc as [c2 Eqcc].
rewrite (MapArgEq _ (EqualInPair'R _ _ _ _ _ Eqcc)).
rewrite (MapArgEq _ (EqualInPair'L _ _ _ _ _ (MapArgEq _ (EqualInPair'L _ _ _ _ _ Eqaa)))).
rewrite (MapArgEq _ (EqualInPair'L _ _ _ _ _ (MapArgEq _ (EqualInPair'R _ _ _ _ _ Eqbb)))).
rewrite (MapArgEq _ (EqualInPair'L _ _ _ _ _ Eqaa)).
rewrite (MapArgEq _ (EqualInPair'R _ _ _ _ _ (MapArgEq _ (EqualInPair'L _ _ _ _ _ Eqbb)))).
rewrite (MapArgEq _ (EqualInPair'R _ _ _ _ _ (MapArgEq _ (EqualInPair'R _ _ _ _ _ Eqcc)))).
rewrite (MapArgEq _ (EqualInPair'L _ _ _ _ _ (ProductOperationTheorem _ _ _ _ _ _))).
rewrite ProductOperationTheorem.
rewrite (MapArgEq _ (EqualInPair'R _ _ _ _ _ (ProductOperationTheorem _ _ _ _ _ _))).
rewrite ProductOperationTheorem.
apply EqualInPair'.
split.
 apply OC1.
apply OC2.
Qed.

Theorem IfCommThenIsInverseComm : forall {A} (o : #(BOperation A)) x y,
Ope_SGrpCond o ->
%o[x;y]==%o[y;x] -> forall Ix, &&(%IsInverseE o) x Ix -> %o[Ix;y] == %o[y;Ix].
Proof.
(*SymmthenInvdoes*)
intros A o x y Ass Symxy Ix IsIIx.
apply (TransitivityEq (%o [%o [Ix;y] ; %o [x;Ix]])).
 apply SymmetryEq.
 apply IsRightIdentTheorem.
 apply IsIdent_RightIdent.
 apply IsInverseETheorem in IsIIx.
 apply (proj1 IsIIx).
apply (TransitivityEq (%o [%o [Ix ; %o [y;x]];Ix])).
 rewrite <- Ass.
 apply MapArgEq.
 apply EqualInPair'L.
 rewrite Ass.
 hyperreflexivity.
rewrite <- (MapArgEq _ (EqualInPair'L _ _ _ _ _ (MapArgEq _ (EqualInPair'R _ _ _ _ _ Symxy)))).
rewrite <- (MapArgEq _ (EqualInPair'L _ _ _ _ _ (Ass _ _ _))).
rewrite Ass.
apply IsLeftIdentTheorem.
apply IsIdent_LeftIdent.
apply IsInverseE_IsIdent'.
apply IsIIx.
Qed.

(* Invertible *)
Definition IsInverseE_of_SGrp {A} (sg : #(SemiGroup A)) :=
(%IsInverseE (sg{<SGrp_Ope})).

Definition IsInvertible_of_SGrp {A} (sg : #(SemiGroup A)) (a : #A) :=
&&IsInvertible (sg{<SGrp_Ope}) a.

Definition Invertible_of_SGrp {A} (sg : #(SemiGroup A)) := %Invertible (sg{<SGrp_Ope}).

Theorem InvertESGrpSubset : forall {A} {sg : #(SemiGroup A)},
Subset (Invertible_of_SGrp sg) A.
Proof.
intros A sg.
unfold Invertible_of_SGrp.
unfold Invertible.
apply RelationImageESubset.
Qed.

Definition IsInverseE_of_SGrpInRUnq : forall {A},
In (@IsInverseE A) (RistableMap (BOperation A) (BRelation A) (SemiGroup A) (RightUnique A A)).
Proof.
intros A.
apply RistableMapTheorem.
split.
 apply SGrp_Ope.
split.
 apply (TransitivitySubset (Relation A A)).
 apply RUnq_Rel.
 apply Rel_BRel.
intros o InoS.
rewrite (USETEq' _ BRel_Rel).
apply Rel_RUnq.
intros a.
intros b c relH1 relH2.
apply (RelRewrite (USETEq _ BRel_Rel)) in relH1.
apply (RelRewrite (USETEq _ BRel_Rel)) in relH2.
apply IsInverseETheorem in relH1.
destruct relH1 as [relH11' relH12'].
put ((proj1 (IsIdentTheorem _ _)) relH11') relH11.
put ((proj1 (IsIdentTheorem _ _)) relH12') relH12.
clear relH11'.
clear relH12'.
apply IsInverseETheorem in relH2.
destruct relH2 as [relH21' relH22'].
put ((proj1 (IsIdentTheorem _ _)) relH21') relH21.
put ((proj1 (IsIdentTheorem _ _)) relH22') relH22.
clear relH21'.
clear relH22'.
apply (TransitivityEq (%o [%o [c;a] ;b])).
 destruct (relH22 b) as [Eq1 Eq2].
 apply SymmetryEq.
 apply Eq1.
apply (TransitivityEq (%o [c; %o[a;b]])).
 cut (Ope_SGrpCond o).
  intro cond.
  rewrite cond.
  hyperreflexivity.
 apply Ope_SGrp.
 apply InoS.
destruct (relH11 c) as [Eq1 Eq2].
apply Eq2.
Qed.

Theorem IsInverseE_of_SGrpRUnqCond : forall {A} (sg : #(SemiGroup A)),
Rel_RUnqCond (IsInverseE_of_SGrp sg).
Proof.
intros A sg.
apply Rel_RUnq.
put (@IsInverseE_of_SGrpInRUnq A) RU.
apply RistableMapTheorem in RU.
destruct RU as [sub1 RU].
destruct RU as [sub2 RU].
apply RU.
apply (SetProp sg).
Qed.

Theorem IsInverseE_SGrpCond_RUnqCond : forall {A} (o : #(BOperation A)),
Ope_SGrpCond o ->
Rel_RUnqCond (%IsInverseE o).
Proof.
intros A o SC.
apply Rel_RUnq.
cut (In (%IsInverseE ((o{<Ope_SGrp ! SC}){<SGrp_Ope})) (RightUnique A A)).
 apply Arrow2Rewrite.
 hyperreflexivity.
 hyperreflexivity.
apply (@Rel_RUnq A A).
apply IsInverseE_of_SGrpRUnqCond.
Qed.


Definition RUInverseE_SGrp {A} : #(Map (SemiGroup A) (RightUnique A A)) :=
%RistMap {_!(@IsInverseE_of_SGrpInRUnq A)}.

Theorem RUInverseE_of_SGrpTheorem : forall {A} (sg : #(SemiGroup A)) a b,
&&(%RUInverseE_SGrp sg){<RUnq_Rel} a b <->
&&(IsInverseE_of_SGrp sg) a b.
Proof.
intros A sg a b.
unfold RUInverseE_SGrp.
split.
 apply RelRewrite.
 rewrite (USETEq _ RUnq_Rel).
 apply MapStrong.
  apply StrongRistMapEq.
  hyperreflexivity.
 hyperreflexivity.
apply RelRewrite.
rewrite (USETEq _ RUnq_Rel).
apply SymmetryEq.
apply MapStrong.
 apply StrongRistMapEq.
 hyperreflexivity.
hyperreflexivity.
Qed.


Theorem Invert_Domain : forall {A} {sg : #(SemiGroup A)},
Subset (Invertible_of_SGrp sg) (%DomainOfRightUnique (%RUInverseE_SGrp sg)).
Proof.
intros A sg.
intros a InaI.
unfold Invertible_of_SGrp in InaI.
assert(InaA : In a A).
 apply InvertibleSubset in InaI.
 apply InaI.
rewrite (DSETEq' _ InaA) in InaI.
rewrite (DSETEq' _ InaA).
apply InvertibleTheorem in InaI.
apply IsInvertibleTheorem in InaI.
destruct InaI as [b InaI].
apply DomainOfRightUniqueTheorem.
exists b.
apply RUInverseE_of_SGrpTheorem.
apply InaI.
Qed.

Theorem Domain_Invert : forall {A} {sg : #(SemiGroup A)},
Subset (%DomainOfRightUnique (%RUInverseE_SGrp sg)) (Invertible_of_SGrp sg).
Proof.
intros A sg.
intros a InaDR.
assert(InaA : In a A).
 apply DomainOfRightUniqueSubset in InaDR.
 assumption.
rewrite (DSETEq' _ InaA) in InaDR.
rewrite (DSETEq' _ InaA).
apply DomainOfRightUniqueTheorem in InaDR.
destruct InaDR as [b InaDR].
unfold Invertible_of_SGrp.
apply InvertibleTheorem.
apply IsInvertibleTheorem.
exists b.
generalize InaDR.
apply RelRewrite.
unfold RUInverseE_SGrp.
rewrite (USETEq _ RUnq_Rel).
apply MapStrong.
 apply StrongRistMapEq.
 hyperreflexivity.
hyperreflexivity.
Qed.


Definition MInvertE_of_SGrp {A} (sg : #(SemiGroup A)) : #(Map (Invertible_of_SGrp sg) A) :=
%CombineMap' [EmbedMap Invert_Domain ; RUnq_to_Map (%RUInverseE_SGrp sg)].

Theorem MInvertE_of_SGrpEq : forall {A} (sg : #(SemiGroup A)),
MInvertE_of_SGrp sg == (%IsInverseE (sg{<SGrp_Ope})).
Proof.
intros A sg.
unfold MInvertE_of_SGrp.
apply (TransitivityEq (RUnq_to_Map (%RUInverseE_SGrp sg))).
 apply MapEquality.
  apply AntisymmetrySubset.
  apply Invert_Domain.
  apply Domain_Invert.
 intros Ia Da Eqd.
 rewrite CombineMap'Theorem.
 apply MapArgEq.
 rewrite EmbedMapEq.
 apply Eqd.
unfold RUnq_to_Map.
rewrite (DSETEq _ _).
unfold RUInverseE_SGrp.
apply MapStrong.
 apply StrongRistMapEq.
 hyperreflexivity.
hyperreflexivity.
Qed.

Theorem MInvertE_of_SGrpTheorem : forall {A} (sg : #(SemiGroup A)) (a : #(Invertible_of_SGrp sg)),
&&(IsInverseE_of_SGrp sg) (a{<InvertESGrpSubset}) (%(MInvertE_of_SGrp sg) a).
Proof.
intros A sg a.
cut (&&((MInvertE_of_SGrp sg){<Map_Rel}) a (%(MInvertE_of_SGrp sg) a)).
 apply RelRewriteAll.
 hyperreflexivity.
 hyperreflexivity.
 rewrite (USETEq _ Map_Rel).
 unfold IsInverseE_of_SGrp.
 apply MInvertE_of_SGrpEq.
apply AppTheorem.
Qed.

Theorem IsInverseEq_SGrp : forall {A} (sg : #(SemiGroup A)) a b b',
&&(IsInverseE_of_SGrp sg) a b -> &&(IsInverseE_of_SGrp sg) a b' -> b == b'.
Proof.
intros A sg a b b' H1 H2.
apply (RightUniqueEq (IsInverseE_of_SGrp sg) a).
apply IsInverseE_of_SGrpRUnqCond.
apply H1.
apply H2.
Qed.

Theorem MInvertE_of_SGrpREq : forall {A} (sg : #(SemiGroup A)) (a : #(Invertible_of_SGrp sg)) (b : #A),
%(MInvertE_of_SGrp sg) a == b <->
&&(%IsInverseE (sg{<SGrp_Ope})) (a{<InvertESGrpSubset}) b.
Proof.
intros A sg a b.
split.
 intro MH.
 apply (RelRewriteR MH).
 apply MInvertE_of_SGrpTheorem.

 intros HH.
 apply (IsInverseEq_SGrp sg (a{<InvertESGrpSubset})).
 apply MInvertE_of_SGrpTheorem.
 apply HH.
Qed.


Theorem IsInverseEMultSGrp : forall {A} (o : #(BOperation A)) (scond : Ope_SGrpCond o) (a a' b b' : #A),
&&(%IsInverseE o) a a' -> &&(%IsInverseE o) b b' ->
&&(%IsInverseE o) (%o [a;b]) (%o [b';a']).
Proof.
intros A o cond a a' b b' H1 H2.
apply IsInverseETheorem in H1.
apply IsInverseETheorem in H2.
apply IsInverseETheorem.
split.
 cut (&&IsIdent o (%o [%o[a ; %o [b;b']] ; a'])).
  apply RelRewriteR.
  rewrite <- (MapArgEq _ (EqualInPair'L _ _ _ _ _ (cond _ _ _))).
  rewrite cond.
  hyperreflexivity.
 cut (&&IsIdent o (%o [a;a'])).
  apply RelRewriteR.
  apply MapArgEq.
  apply EqualInPair'L.
  apply SymmetryEq.
  apply IsRightIdentTheorem.
  apply IsIdent_RightIdent.
  apply (proj1 H2).
 apply (proj1 H1).

 cut (&&IsIdent o (%o [%o[b';%o[a';a]];b])).
  apply RelRewriteR.
  rewrite <- (MapArgEq _ (EqualInPair'L _ _ _ _ _ (cond _ _ _))).
  rewrite cond.
  hyperreflexivity.
 cut(&&IsIdent o (%o [b';b])).
  apply RelRewriteR.
  apply SymmetryEq.
  apply MapArgEq.
  apply EqualInPair'L.
  apply IsRightIdentTheorem.
  apply IsIdent_RightIdent.
  apply (proj2 H1).
 apply (proj2 H2).
Qed.

Theorem IsInvertMultSGrp : forall {A} (o : #(BOperation A)) (cond : Ope_SGrpCond o) a b,
&&IsInvertible o a -> &&IsInvertible o b ->
&&IsInvertible o (%o[a;b]).
Proof.
intros A o cond a b H1 H2.
apply IsInvertibleTheorem in H1.
destruct H1 as [a' H1].
apply IsInvertibleTheorem in H2.
destruct H2 as [b' H2].
apply IsInvertibleTheorem.
exists (%o[b';a']).
apply IsInverseEMultSGrp.
apply cond.
apply H1.
apply H2.
Qed.



(* Sub SemiGroup *)
Definition IsSubSemiGroup {A} (sg : #(SemiGroup A)) (S : #(PowerSet A)) :=
&&IsSubBOperation (sg{<SGrp_Ope}) S.

Definition SubSemiGroup {A} (sg : #(SemiGroup A)) :=
%SubBOperation (sg{<SGrp_Ope}).

Theorem SubSGrp_SubOpe : forall {A} {sg : #(SemiGroup A)},
Subset (SubSemiGroup sg) (%SubBOperation (sg{<SGrp_Ope})).
Proof.
intros A sg.
unfold SubSemiGroup.
apply ReflexivitySubset.
Qed.

Definition SubSGrp_to_Ope {A} {sg : #(SemiGroup A)} (S : #(SubSemiGroup sg)) : #(BOperation S) :=
Sub_to_BOperation (S{<SubSGrp_SubOpe}).

Theorem Sub_to_SemiGroupCond : forall {A} (sg : #(SemiGroup A)) (S : #(SubSemiGroup sg)),
Ope_SGrpCond (SubSGrp_to_Ope S).
Proof.
intros A sg S.
unfold SubSGrp_to_Ope.
apply (Ope_SGrpCond_StrongCons _ (sg{<SGrp_Ope})).
 apply StrongSubBOpe.
 apply ReflexivityStrongRel.
apply Ope_SGrp.
apply (SetProp sg).
Qed.

Definition SubSGrp_to_SGrp {A} {sg : #(SemiGroup A)} (S : #(SubSemiGroup sg)) : #(SemiGroup S) :=
_{<Ope_SGrp ! Sub_to_SemiGroupCond sg S}.

(* Commutative SemiGroup *)
Definition CSemiGroup A := Section (SemiGroup A) (Commutative A).

Theorem CSGrp_SGrp : forall {A},
Subset (CSemiGroup A) (SemiGroup A).
Proof.
intros A.
apply SectionSubsetL.
Qed.

Theorem CSGrp_Comm : forall {A},
Subset (CSemiGroup A) (Commutative A).
Proof.
intros A.
apply SectionSubsetR.
Qed.

Theorem CSGrp_Ope : forall {A},
Subset (CSemiGroup A) (BOperation A).
Proof.
intros A.
apply (TransitivitySubset (SemiGroup A)).
apply CSGrp_SGrp.
apply SGrp_Ope.
Qed.

Definition Ope_CSGrpCond {A} (o : #(BOperation A)) :=
Ope_SGrpCond o /\ Ope_CommCond o.

Theorem Ope_CSGrp : forall {A} (o : #(BOperation A)),
Ope_CSGrpCond o <-> In o (CSemiGroup A).
Proof.
intros A o.
split.
 intro cond.
 destruct cond as [SC CC].
 apply SectionTheorem.
 split.
 apply Ope_SGrp.
 apply SC.
 apply Ope_Comm.
 apply CC.

 intro InoCS.
 apply SectionTheorem in InoCS.
 destruct InoCS as [InoS InoC].
 split.
 apply Ope_SGrp.
 apply InoS.
 apply Ope_Comm.
 apply InoC.
Qed.


(* Monoid *)
Definition Monoid A := Section (SemiGroup A) (Identical A).

Theorem Monoid_SGrp {A} : Subset (Monoid A) (SemiGroup A).
Proof.
apply SectionSubsetL.
Qed.

Theorem Monoid_Ident {A} : Subset (Monoid A) (Identical A).
Proof.
apply SectionSubsetR.
Qed.

Theorem Monoid_Ope {A} : Subset (Monoid A) (BOperation A).
Proof.
apply (TransitivitySubset (SemiGroup A)).
 apply Monoid_SGrp.
apply SGrp_Ope.
Qed.

Definition Ope_MonoidCond {A} (o : #(BOperation A)) :=
Ope_SGrpCond o /\ Ope_IdentCond o.

Theorem Ope_Monoid : forall {A} (o : #(BOperation A)),
Ope_MonoidCond o <-> In o (Monoid A).
Proof.
intros A o.
split.
 intro cond.
 apply SectionTheorem.
 destruct cond as [cond1 cond2].
 apply Ope_SGrp in cond1.
 apply Ope_Ident in cond2.
 split; assumption.

 intro InoM.
 apply SectionTheorem in InoM.
 destruct InoM.
 split.
 apply Ope_SGrp.
 assumption.
 apply Ope_Ident.
 assumption.
Qed.

Definition SGrp_MonoidCond {A} (o : #(SemiGroup A)) :=
Ope_IdentCond (o{<SGrp_Ope}).

Theorem SGrp_Monoid : forall {A} (o : #(SemiGroup A)),
SGrp_MonoidCond o <-> In o (Monoid A).
Proof.
intros A o.
split.
 intro cond.
 apply SectionTheorem.
 split.
  apply SetProp.
 unfold SGrp_MonoidCond in cond.
 apply Ope_Ident in cond.
 apply cond.
intro InoM.
apply SectionTheorem in InoM.
destruct InoM as [InoS InoI].
unfold SGrp_MonoidCond.
apply Ope_Ident.
apply InoI.
Qed.

Definition MIdent_of_Monoid {A} (m : #(Monoid A)) :=
%MIdent (m{<Monoid_Ident}).

Theorem NonEmptyMonoid : forall {A} (M : #(Monoid A)),
NonEmpty A.
Proof.
intros A M.
exists (MIdent_of_Monoid M).
apply SetProp.
Qed.

Theorem Ope_MonoidCond_StrongCons : forall {A B} (o1 : #(BOperation A)) (o2 : #(BOperation B)),
StrongRel (o1{<Map_Rel}) (o2{<Map_Rel}) -> (forall e, &&IsIdent o2 e -> In e A) ->
Ope_MonoidCond o2 -> Ope_MonoidCond o1.
Proof.
intros A B o1 o2 SH IC cond.
destruct cond as [cond1 cond2].
split.
 apply (Ope_SGrpCond_StrongCons o1 o2).
 apply SH.
 apply cond1.
apply (Ope_IdentCond_StrongCons o1 o2).
apply SH.
apply IC.
apply cond2.
Qed.

Theorem Ope_MonoidCond_Product : forall {A B} (o1 : #(BOperation A)) (o2 : #(BOperation B)),
Ope_MonoidCond o1 -> Ope_MonoidCond o2 -> Ope_MonoidCond (%ProductOperation [o1;o2]).
Proof.
intros A B o1 o2.
intros C1 C2.
destruct C1 as [CS1 CI1].
destruct C2 as [CS2 CI2].
split.
 apply Ope_SGrpCond_Product; assumption.
apply Ope_IdentCond_Product; assumption.
Qed.

(* SubMonoid *)
Definition IsSubMonoid {A} (m : #(Monoid A)) (S : #(PowerSet A)) :=
&&IsSubIdentical (m{<Monoid_Ope}) S.

Definition SubMonoid {A} (m : #(Monoid A)) :=
%SubIdentical (m{<Monoid_Ope}).

Theorem SubMonoid_SubOpe : forall {A} {m : #(Monoid A)},
Subset (SubMonoid m) (%SubBOperation (m{<Monoid_Ope})).
Proof.
intros A m.
unfold SubMonoid.
apply SubIdent_SubOpe.
Qed.

Theorem SubMonoid_SubIdent : forall {A} {m : #(Monoid A)},
Subset (SubMonoid m) (%SubIdentical (m{<Monoid_Ope})).
Proof.
intros A m.
unfold SubMonoid.
apply ReflexivitySubset.
Qed.

Theorem SubMonoid_SubSGrp : forall {A} {m : #(Monoid A)},
Subset (SubMonoid m) (SubSemiGroup (m{<Monoid_SGrp})).
Proof.
intros A m.
unfold SubMonoid.
unfold SubSemiGroup.
apply (TransitivitySubset _ (SubIdent_SubOpe)).
apply ReflexivitySubset2.
hyperreflexivity.
Qed.

Definition SubMonoid_to_Ope {A} {m : #(Monoid A)} (S : #(SubMonoid m)) : #(BOperation S) :=
Sub_to_BOperation (S{<SubMonoid_SubOpe}).

Theorem Sub_to_MonoidCond : forall {A} (m : #(Monoid A)) (S : #(SubMonoid m)),
Ope_MonoidCond (SubMonoid_to_Ope S).
Proof.
intros A m S.
apply (Ope_MonoidCond_StrongCons _ (m{<Monoid_Ope})).
  unfold SubMonoid_to_Ope.
  apply (StrongSubBOpe _ _ (S{<SubMonoid_SubOpe})).
  apply ReflexivityStrongRel.
 intros e IT.
 apply (SubIdenticalHasIdent (m{<Monoid_Ope})).
 apply IT.
apply Ope_Monoid.
apply (SetProp m).
Qed.


(*
(* Monoid Operator *)
Fixpoint MOCompute {A} (mo : #(Monoid A)) (l : @MOList A) : (#A) :=
match l with
| Nil => %MIdent (mo{<Monoid_Ident})
| Cons a l' =>
  let newa := match a with
           | TermE a' => a'
           | TermT t => MOCompute mo t
           end in
  match l' with
  | Nil => newa
  | Cons _ _ => %mo{<Monoid_Ope} [newa ; MOCompute mo l']
  end
end.

Theorem MOComputeRewritelist : forall {A} {mo : #(Monoid A)} {l1 l2 : @MOList A},
l1 = l2 ->
MOCompute mo l1 == MOCompute mo l2.
Proof.
intros A mo l1 l2 Eq.
rewrite Eq.
hyperreflexivity.
Qed.

Theorem MOComputeRewrite'list : forall {A} {mo : #(Monoid A)} {l1 l2 : @MOList A},
l2 = l1 ->
MOCompute mo l1 == MOCompute mo l2.
Proof.
intros A mo l1 l2 eq.
apply SymmetryEq.
apply (MOComputeRewritelist eq).
Qed.

Theorem MOCompute_Comm_ConsE : forall {A} (mo : #(Monoid A)) a (l : @MOList A),
MOCompute mo (Cons (TermE a) l) == %(mo{<Monoid_Ope}) [a ; MOCompute mo l].
Proof.
intros A mo a.
induction l.
 apply (TransitivityEq a).
  unfold MOCompute.
  hyperreflexivity.
 unfold MOCompute.
 put (MIdentTheorem (mo{<Monoid_Ident})) IT.
 put ((proj1 (IsIdentTheorem _ _)) IT) IT'.
 destruct (IT' a) as [IT1 IT2].
 rewrite <- IT2.
 apply MapEqAll.
  hyperreflexivity.
 hyperreflexivity.

 hyperreflexivity.
Qed.

Theorem MOCompute_Comm_ConsT : forall {A} (mo : #(Monoid A)) t (l : @MOList A),
MOCompute mo (Cons (TermT t) l) == %(mo{<Monoid_Ope}) [MOCompute mo t ; MOCompute mo l].
Proof.
intros A mo t.
induction l.
 apply (TransitivityEq (MOCompute mo t)).
  simpl.
  hyperreflexivity.
 unfold MOCompute at 3.
 put (MIdentTheorem (mo{<Monoid_Ident})) IT.
 put ((proj1 (IsIdentTheorem _ _)) IT) IT'.
 destruct (IT' (MOCompute mo t)) as [IT1 IT2].
 rewrite <- IT2.
 apply MapEq.
 hyperreflexivity.

 hyperreflexivity.
Qed.

Theorem MOCompute_Comm_MOAppend : forall {A} (mo : #(Monoid A)) (l1 l2 : @MOList A),
MOCompute mo (MOAppend l1 l2) == %(mo{<Monoid_Ope}) [MOCompute mo l1;MOCompute mo l2].
Proof.
intros A mo.
induction l1.
 intro l2.
 unfold MOAppend.
 unfold MOCompute at 2.
 put (MIdentTheorem (mo{<Monoid_Ident})) IT.
 apply IsIdent_LeftIdent in IT.
 apply SymmetryEq.
 apply IsLeftIdentTheorem.
 apply IT.

 intro l2.
 apply (TransitivityEq (MOCompute mo (Cons m (MOAppend l1 l2)))).
  apply MOComputeRewritelist.
  apply MOAppend_Comm_Cons.
 assert(AssocT : Ope_SGrpCond (mo{<Monoid_Ope})).
  apply Ope_SGrp.
  apply Monoid_SGrp.
  apply (SetProp mo).
 destruct m.
  rewrite MOCompute_Comm_ConsE.
  rewrite (MapArgEq _ (EqualInPair'R _ _ _ _ _ (IHl1 _))).
  rewrite <- AssocT.
  apply MapArgEq.
  apply EqualInPair'L.
  rewrite MOCompute_Comm_ConsE.
  hyperreflexivity.

  rewrite MOCompute_Comm_ConsT.
  rewrite (MapArgEq _ (EqualInPair'R _ _ _ _ _ (IHl1 _))).
  rewrite <- AssocT.
  apply MapArgEq.
  apply EqualInPair'L.
  rewrite MOCompute_Comm_ConsT.
  hyperreflexivity.
Qed.


Theorem MOComputeFloatTheorem : forall {A} (mo : #(Monoid A)) (l : @MOList A),
MOCompute mo l == MOCompute mo (MOFloat l).
Proof.
intros A mo l.
induction l.
 unfold MOFloat.
 hyperreflexivity.
 induction m.
  rewrite MOFloat_Comm_ConsE.
  rewrite MOCompute_Comm_ConsE.
  rewrite MOCompute_Comm_ConsE.
  apply MapArgEq.
  apply EqualInPair'R.
  apply IHl.

  rewrite MOCompute_Comm_ConsT.
  rewrite (MapArgEq _ (EqualInPair'R _ _ _ _ _ IHl)).
  rewrite <- MOCompute_Comm_MOAppend.
  induction m.
   unfold MOAppend.
   apply MOComputeRewritelist.
   simpl.
   reflexivity.

   apply (TransitivityEq (MOCompute mo (Cons m (MOAppend m0 (MOFloat l))))).
    apply MOComputeRewritelist.
    apply MOAppend_Comm_Cons.
   destruct m.
    rewrite MOCompute_Comm_ConsE.
    rewrite (MapArgEq _ (EqualInPair'R _ _ _ _ _ IHm)).
    rewrite <- MOCompute_Comm_ConsE.
    apply MOComputeRewritelist.
    simpl.
    reflexivity.

    rewrite MOCompute_Comm_ConsT.
    rewrite (MapArgEq _ (EqualInPair'R _ _ _ _ _ IHm)).
    rewrite <- MOCompute_Comm_ConsT.
    rewrite (M
    rewrite MOFloat_Comm_ConsE.


   apply (
   apply (TransitivityEq (MOCompute mo (Cons m (MO
   unfold MOFloat.

   apply (TransitivityEq (MOCompute mo (MOFloat l))).
    unfold MOAppend.
    hyperreflexivity.
   
  apply MOComputeRewritelist.
  
  rewrite (MapArgEq _ (Equal
  rewrite MOFloat_Comm_ConsT.
  rewrite MOCompute_Comm_MOAppend.
  apply MapArgEq.
  apply EqualInPair'.
  split.
  apply IHl.

  apply (TransitivityEq (%(mo{<Monoid_Ope}) [MOComute 
  hyperreflexivity.

  rewrite MOCompute_Comm_ConsT.
  
  

  simpl.

  apply MOComputeRewritelist.
  rewrite 
c
 induction l.

 generalize l.
 revert m.
 induction l.
  intro m.
  
induction l.
 destruct m.
  simpl.
  hyperreflexivity.
 simpl.
 fix (MOCompute mo m == MOCompute mo (MOFloat m)) 1.
 fix MOComputeFloatTheorem 1.





c
 simpl.

inversion l.
 induction m.
 simpl.

induction l.
 induction m.
  apply (TransitivityEq (MOCompute mo (Cons (TermE p) Nil))).
   apply MOComputeRewritelist.
   rewrite Heqm0.
   reflexivity.
  apply (TransitivityEq (MOCompute mo (MOFloat (Cons (TermE p) Nil)))).
   simpl.
   hyperreflexivity.
  apply MOComputeRewritelist.
  rewrite Heqm0.c
  reflexivity.
 apply (TransitivityEq (MOCompute mo (Cons (TermT m) Nil))).
  apply MOComputeRewritelist.
  rewrite Heqm0.
  reflexivity.
 apply (TransitivityEq (MOCompute mo (MOFloat (Cons (TermT m) Nil)))).
  simpl.
  rewrite IHl.

  hyperreflexivity.

  simpl.
  
  rewrite (MOComputeRewrite'list Heqm0).

 rewrite <- He
  simpl.
  hyperreflexivity.
 simpl.
 destruct m.

  intro m.
  de
  simpl.
 destruct m.

 induction l.
  induction m.
   simpl.
   hyperreflexivity.
  simpl.
  
  destruct m.
  simpl.
  hyperreflexivity.
 simpl.
 
  unfold MOFloat.
  hyperreflexivity.
 simpl.
 apply (TransitivityEq (MOCompute mo (MOAppend (MOFloat m) (MOFloat Nil)))).
  rewrite (MOComputeRewrite'list (MOFloat_Comm_MOAppend _ _)).
  rewrite (MOComputeRewritelist (MOAppendNileq _)).
  
 rewrite MOAppend
 unfold MOAppend.
 simpl.
 simpl.
 unfold MOCompute at 1.
 simpl.
 unfold MOAppend.

 unfold MOFloat.
 simpl.
 simpl.

 simpl.

unfold MOCompute.
*)

(* Commutative Monoid *)
Definition CMonoid A := Section (Monoid A) (Commutative A).

Theorem CMonoid_Monoid : forall {A}, Subset (CMonoid A) (Monoid A).
Proof.
intro A.
apply SectionSubsetL.
Qed.

Theorem CMonoid_Comm : forall {A}, Subset (CMonoid A) (Commutative A).
Proof.
intro A.
apply SectionSubsetR.
Qed.

Theorem CMonoid_Ope : forall {A}, Subset (CMonoid A) (BOperation A).
Proof.
intro A.
apply (TransitivitySubset (Monoid A)).
apply CMonoid_Monoid.
apply Monoid_Ope.
Qed.

Theorem CMonoid_SGrp : forall {A}, Subset (CMonoid A) (SemiGroup A).
Proof.
intro A.
apply (TransitivitySubset (Monoid A)).
 apply CMonoid_Monoid.
apply Monoid_SGrp.
Qed.

Theorem CMonoid_Ident : forall {A}, Subset (CMonoid A) (Identical A).
Proof.
intros A.
apply (TransitivitySubset (Monoid A)).
apply CMonoid_Monoid.
apply Monoid_Ident.
Qed.

Definition Ope_CMonoidCond {A} (o : #(BOperation A)) :=
Ope_MonoidCond o /\ Ope_CommCond o.

Theorem Ope_CMonoid : forall {A} (o : #(BOperation A)),
Ope_CMonoidCond o <-> In o (CMonoid A).
Proof.
intros A o.
split.
 intro cond.
 destruct cond as [c1 c2].
 apply SectionTheorem.
 split.
  apply Ope_Monoid.
  apply c1.
 apply Ope_Comm.
 apply c2.
intro InoC.
apply SectionTheorem in InoC.
destruct InoC as [InoM InoC].
split.
 apply Ope_Monoid.
 apply InoM.
apply Ope_Comm.
apply InoC.
Qed.

Definition Monoid_CMonoidCond {A} (o : #(Monoid A)) :=
Ope_CommCond (o{<Monoid_Ope}).

Theorem Monoid_CMonoid : forall {A} (o : #(Monoid A)),
Monoid_CMonoidCond o <-> In o (CMonoid A).
Proof.
intros A o.
split.
 intro cond.
 apply SectionTheorem.
 split.
 apply (SetProp o).
 unfold Monoid_CMonoidCond in cond.
 apply Ope_Comm in cond.
 apply cond.

intro InoC.
apply SectionTheorem in InoC.
destruct InoC as [InoM InoC].
unfold Monoid_CMonoidCond.
apply Ope_Comm.
apply InoC.
Qed.

Theorem CMonoid_CSGrp : forall {A}, Subset (CMonoid A) (CSemiGroup A).
Proof.
intros A.
intros o InoCM.
assert(InoB : In o (BOperation A)).
 apply CMonoid_Ope.
 apply InoCM.
rewrite (DSETEq' _ InoB) in InoCM.
rewrite (DSETEq' _ InoB).
apply Ope_CMonoid in InoCM.
destruct InoCM as [CM CC].
destruct CM as [SC IC].
apply SectionTheorem.
split.
apply Ope_SGrp.
apply SC.
apply Ope_Comm.
apply CC.
Qed.


Definition MIdent_of_CMonoid {A} (cm : #(CMonoid A)) :=
%MIdent (cm{<CMonoid_Ident}).

Theorem Ope_CMonoidCond_StrongCons : forall {A B} (o1 : #(BOperation A)) (o2 : #(BOperation B)),
StrongRel (o1{<Map_Rel}) (o2{<Map_Rel}) -> (forall e, &&IsIdent o2 e -> In e A) ->
Ope_CMonoidCond o2 -> Ope_CMonoidCond o1.
Proof.
intros A B o1 o2 SH cond OH.
destruct OH as [MH CH].
split.
 apply (Ope_MonoidCond_StrongCons _ o2).
 apply SH.
 apply cond.
 apply MH.
apply (Ope_CommCond_StrongCons _ o2).
apply SH.
apply CH.
Qed.


Theorem Ope_CMonoidCond_Product : forall {A B} (o1 : #(BOperation A)) (o2 : #(BOperation B)),
Ope_CMonoidCond o1 -> Ope_CMonoidCond o2 -> Ope_CMonoidCond (%ProductOperation [o1;o2]).
Proof.
intros A B o1 o2 CH1 CH2.
destruct CH1 as [MH1 CH1].
destruct CH2 as [MH2 CH2].
split.
 apply Ope_MonoidCond_Product.
 apply MH1.
 apply MH2.
apply Ope_CommCond_Product.
apply CH1.
apply CH2.
Qed.

Definition IsHomomorphism_of_CMonoid {A B} (p1 : #(CMonoid A)) (p2 : #(CMonoid B)) (f : #(Map A B)) :=
&&IsHomomorphism_of_Ident [p1{<CMonoid_Ope} ; p2{<CMonoid_Ope}] f.

(* SubCMonoid*)
Definition IsSubCMonoid {A} (o : #(CMonoid A)) S :=
&&IsSubIdentical (o{<CMonoid_Ope}) S.

Definition SubCMonoid {A} (o : #(CMonoid A)) :=
%SubIdentical (o{<CMonoid_Ope}).

Theorem SubCMonoid_SubOpe : forall {A} {cm : #(CMonoid A)},
Subset (SubCMonoid cm) (%SubBOperation (cm{<CMonoid_Ope})).
Proof.
intros A cm.
unfold SubCMonoid.
apply SubIdent_SubOpe.
Qed.

Theorem SubCMonoid_SubMonoid : forall {A} {cm : #(CMonoid A)},
Subset (SubCMonoid cm) (SubMonoid cm{<CMonoid_Monoid}).
Proof.
intros A cm.
unfold SubCMonoid.
unfold SubMonoid.
apply ReflexivitySubset2.
hyperreflexivity.
Qed.

Theorem SubCMonoid_SubIdent : forall {A} {cm : #(CMonoid A)},
Subset (SubCMonoid cm) (%SubIdentical (cm{<CMonoid_Ope})).
Proof.
intros A cm.
apply (TransitivitySubset (SubMonoid (cm{<CMonoid_Monoid}))).
 apply SubCMonoid_SubMonoid.
apply (TransitivitySubset _ SubMonoid_SubIdent).
apply ReflexivitySubset2.
hyperreflexivity.
Qed.

Theorem SubCMonid_SubSGrp : forall {A} {cm : #(CMonoid A)},
Subset (SubCMonoid cm) (SubSemiGroup (cm{<CMonoid_SGrp})).
Proof.
intros A cm.
apply (TransitivitySubset (SubMonoid (cm{<CMonoid_Monoid}))).
 apply SubCMonoid_SubMonoid.
apply (TransitivitySubset _ SubMonoid_SubSGrp).
apply ReflexivitySubset2.
hyperreflexivity.
Qed.

Theorem SubCMonoid_S : forall {A} {cm : #(CMonoid A)} {S : #(SubCMonoid cm)},
Subset S A.
Proof.
intros A cm S.
unfold SubCMonoid in S.
apply (@SubIdent_S _ (cm{<CMonoid_Ope}) S).
Qed.

Definition SubCMonoid_to_Ope {A} {cm : #(CMonoid A)} (S : #(SubCMonoid cm)) : #(BOperation S) :=
Sub_to_BOperation (S{<SubCMonoid_SubOpe}).

Theorem Sub_to_CMonoidCond : forall {A} (cm : #(CMonoid A)) (S : #(SubCMonoid cm)),
Ope_CMonoidCond (SubCMonoid_to_Ope S).
Proof.
intros A cm S.
split.
 cut (Ope_MonoidCond (SubMonoid_to_Ope (S{<SubCMonoid_SubMonoid}))).
  intro OH.
  apply Ope_Monoid in OH.
  apply Ope_Monoid.
  generalize OH.
  apply Arrow2Rewrite.
   unfold SubMonoid_to_Ope.
   unfold SubCMonoid_to_Ope.
   hyperreflexivity.
  hyperreflexivity.
 apply Sub_to_MonoidCond.
apply (Ope_CommCond_StrongCons _ (cm{<CMonoid_Ope})).
 unfold SubCMonoid_to_Ope.
 apply (StrongSubBOpe _ _ (S{<SubCMonoid_SubOpe})).
 apply ReflexivityStrongRel.
apply Ope_Comm.
apply CMonoid_Comm.
apply (SetProp cm).
Qed.

Definition Sub_to_CMonoid {A} {cm : #(CMonoid A)} (S : #(SubCMonoid cm)) : #(CMonoid S) :=
_{<Ope_CMonoid ! (Sub_to_CMonoidCond cm S)}.


(* Group*)
Definition Group A :=
Section (SemiGroup A) (Section (Identical A) (Invertical A)).

Theorem Grp_SGrp : forall {A}, Subset (Group A) (SemiGroup A).
Proof.
intro A.
apply SectionSubsetL.
Qed.

Theorem Grp_Ope : forall {A}, Subset (Group A) (BOperation A).
Proof.
intro A.
apply (TransitivitySubset (SemiGroup A)).
 apply Grp_SGrp.
apply SGrp_Ope.
Qed.

Theorem Grp_Ident : forall {A}, Subset (Group A) (Identical A).
Proof.
intro A.
apply (TransitivitySubset (Section (Identical A) (Invertical A))).
apply SectionSubsetR.
apply SectionSubsetL.
Qed.

Theorem Grp_Invert : forall {A}, Subset (Group A) (Invertical A).
Proof.
intro A.
apply (TransitivitySubset (Section (Identical A) (Invertical A))).
apply SectionSubsetR.
apply SectionSubsetR.
Qed.

Theorem Grp_Monoid : forall {A}, Subset (Group A) (Monoid A).
Proof.
intro A.
intros g IngG.
apply SectionTheorem in IngG.
apply SectionTheorem.
destruct IngG as [IngS IngI].
apply SectionTheorem in IngI.
split.
apply IngS.
apply (proj1 IngI).
Qed.

Definition Ope_GrpCond {A} (o : #(BOperation A)) := 
Ope_MonoidCond o /\ Ope_InvertCond o.

Theorem Ope_Grp : forall {A} (o : #(BOperation A)),
Ope_GrpCond o <-> In o (Group A).
Proof.
intros A o.
split.
 intro cond.
 destruct cond as [mcond icond].
 destruct mcond as [acond econd].
 apply SectionTheorem.
 split.
 apply Ope_SGrp.
 apply acond.
 apply SectionTheorem.
 split.
 apply Ope_Ident.
 apply econd.
 apply Ope_Invert.
 apply icond.

 intro InoG.
 apply SectionTheorem in InoG.
 destruct InoG as [InoA InoG].
 apply SectionTheorem in InoG.
 destruct InoG as [InoE InoI].
 split.
 split.
 apply Ope_SGrp.
 apply InoA.
 apply Ope_Ident.
 apply InoE.
 apply Ope_Invert.
 apply InoI.
Qed.



(*
Theorem Ope_GrpCond_StrongCons : forall {A B} (o1 : #(BOperation A)) (o2 : #(BOperation B)),
StrongRel (o1{<Map_Rel}) (o2{<Map_Rel}) -> Ope_GrpCond o2 -> Ope_GrpCond o1.
Proof.
intros A B o1 o2 SH OD.
destruct OD as [MC IC].
split.
 apply (Ope_MonoidCond_StrongCons o1 o2 SH).
  intros eb IsIeb.
  destruct MC as [SC EC].
  destruct EC as [ea EC].
  assert(Eqe : ea == eb).
   apply (TransitivityEq (%o1 [ea;ea])).

  unfold Ope_InvertCond in IC.
  destruct IC.
  assert(Sub : Subset A B).
   apply (StrongBOpeSubset _ _ SH).
  
  assert(IsIeA : &&IsIdent o1 (e{<Sub})).

  assert(Eqe : e == %MIdent
 unfold Ope_InvertCond in IC.

 apply SH.
*)

(* Ident of Group *)

Definition MIdent_of_Grp {A} (g : #(Group A)) :=
%MIdent (g{<Grp_Ident}).

Definition IsIdent_of_Grp {A} (g : #(Group A)) (a : #A) :=
&&IsIdent (g{<Grp_Ope}) a.

Definition IsInverseE_of_Grp {A} (g : #(Group A)) :=
%IsInverseE (g{<Grp_Ope}).

Definition IsInvertible_of_Grp {A} (g : #(Group A)) a :=
&&IsInvertible (g{<Grp_Ope}) a.

Definition Invertible_of_Grp {A} (g : #(Group A)) :=
%Invertible (g{<Grp_Ope}).

Theorem Invertible_is_AllInGrp : forall {A} (g : #(Group A)),
%Invertible (g{<Grp_Ope}) == A.
Proof.
intros A g.
unfold Invertible.
apply AntisymmetrySubset.
apply RelationImageESubset.
intros a InaA.
rewrite (DSETEq' _ InaA).
apply InvertibleTheorem.
assert(IngG : In (g{<Grp_Ope}) (Group A)).
 apply (SetProp g).
apply Ope_Grp in IngG.
destruct IngG as [MG IG].
unfold Ope_InvertCond in IG.
apply IG.
Qed.
  
Theorem IsInvertible_of_GrpInMap : forall {A},
In (@IsInverseE A) (RistableMap (BOperation A) (BRelation A) (Group A) (Map A A)).
Proof.
intros A.
apply RistableMapTheorem.
split.
 apply Grp_Ope.
split.
 unfold BRelation.
 apply Map_Rel.
intros o InaG.
rewrite (USETEq' _ BRel_Rel).
apply Rel_Map2.
split.
 apply Rel_LTtl.
 rewrite (USETEq _ BRel_Rel).
 apply (RistableMapTheoremIn (Invertical A)).
 apply IsInverseE_of_InvertInLTtl.
 apply Grp_Invert.
 apply InaG.
apply Rel_RUnq.
rewrite (USETEq _ BRel_Rel).
apply (RistableMapTheoremIn (SemiGroup A)).
apply IsInverseE_of_SGrpInRUnq.
apply Grp_SGrp.
apply InaG.
Qed.

Definition MInvert_of_Grp {A} : #(Map (Group A) (Map A A)) :=
%RistMap {_ ! @IsInvertible_of_GrpInMap A}.

Theorem MInvert_of_Grp_is_MESGrp : forall {A} (g : #(Group A)),
%MInvert_of_Grp g == MInvertE_of_SGrp (g{<Grp_SGrp}).
Proof.
intros A g.
apply MapEquality.
 apply SymmetryEq.
 unfold Invertible_of_SGrp.
 apply (TransitivityEq (%Invertible (g{<Grp_Ope}))).
  hyperreflexivity.
 apply Invertible_is_AllInGrp.
intros a a' Eqa.
apply SymmetryEq.
apply MInvertE_of_SGrpREq.
cut (&&(%IsInverseE (g{<Grp_Ope})) a (%(%MInvert_of_Grp g) a)).
 apply RelRewriteAll.
 rewrite Eqa.
 hyperreflexivity.
 hyperreflexivity.
 hyperreflexivity.
cut (&&((%MInvert_of_Grp g){<Map_Rel}) a (%(%MInvert_of_Grp g) a)).
 apply RelRewrite.
 rewrite (USETEq _ Map_Rel).
 unfold MInvert_of_Grp.
 apply MapStrong.
  apply StrongRistMapEq.
  hyperreflexivity.
 hyperreflexivity.
apply AppTheorem.
Qed.

Theorem MInvert_of_GrpTheorem : forall {A} (g : #(Group A)) a,
&&(IsInverseE_of_Grp g) a (%(%MInvert_of_Grp g) a).
Proof.
intros A g a.
unfold IsInverseE_of_Grp.
cut (&&((%MInvert_of_Grp g){<Map_Rel}) a (%(%MInvert_of_Grp g) a)).
 apply RelRewrite.
 unfold MInvert_of_Grp.
 rewrite (USETEq _ Map_Rel).
 apply MapStrong.
  apply StrongRistMapEq.
  hyperreflexivity.
 hyperreflexivity.
apply AppTheorem.
Qed.

Theorem MInvert_of_GrpREq : forall {A} (g : #(Group A)) (a b : #A),
%(%MInvert_of_Grp g) a == b <->
&&(IsInverseE_of_Grp g) a b.
Proof.
intros A g a b.
assert(InaI : In a (Invertible_of_SGrp (g{<Grp_SGrp}))).
 unfold Invertible_of_SGrp.
 cut (In a (%Invertible (g{<Grp_Ope}))).
  apply Arrow2Rewrite; hyperreflexivity.
 rewrite Invertible_is_AllInGrp.
 apply SetProp.
split.
 intro HEq.
 assert(HEq' : (%(MInvertE_of_SGrp (g{<Grp_SGrp})) {a ! InaI}) == b).
  rewrite <- HEq.
  apply MapEqAll.
  hyperreflexivity.
  apply SymmetryEq.
  apply MInvert_of_Grp_is_MESGrp.
 apply MInvertE_of_SGrpREq in HEq'.
 generalize HEq'.
 apply RelRewriteAll; hyperreflexivity.

 intro IsIH.
 apply (TransitivityEq (%(MInvertE_of_SGrp (g{<Grp_SGrp})) {a ! InaI})).
  apply MapEqAll.
   hyperreflexivity.
  apply MInvert_of_Grp_is_MESGrp.
 apply MInvertE_of_SGrpREq.
 generalize IsIH.
 apply RelRewriteAll; hyperreflexivity.
Qed.
 
Theorem IsInverseEMultGrp : forall {A} (g : #(Group A)) (a a' b b' : #A),
&&(IsInverseE_of_Grp g) a a' -> &&(IsInverseE_of_Grp g) b b' ->
&&(IsInverseE_of_Grp g) (%g{<Grp_Ope} [a;b]) (%g{<Grp_Ope} [b';a']).
Proof.
intros A g a a' b b'.
intros H1 H2.
unfold IsInverseE_of_Grp.
apply IsInverseEMultSGrp.
 apply Ope_SGrp.
 apply Grp_SGrp.
 apply (SetProp g).
apply H1.
apply H2.
Qed.

Theorem MInvert_of_GrpMultTheorem : forall {A} (g : #(Group A)) a b,
%(%MInvert_of_Grp g) (%g{<Grp_Ope} [a;b]) ==
%g{<Grp_Ope} [%(%MInvert_of_Grp g) b ; %(%MInvert_of_Grp g) a].
Proof.
intros A g a b.
apply MInvert_of_GrpREq.
apply IsInverseEMultGrp.
apply MInvert_of_GrpTheorem.
apply MInvert_of_GrpTheorem.
Qed.

Theorem MInvert_of_GrpMultTheoremWP : forall {A} (o : #(BOperation A)) (gcond : Ope_GrpCond o) a b,
%(%MInvert_of_Grp (o{<Ope_Grp ! gcond})) (%o [a;b]) ==
%o [%(%MInvert_of_Grp (o{<Ope_Grp ! gcond})) b ; %(%MInvert_of_Grp (o{<Ope_Grp ! gcond})) a].
Proof.
intros A o gcond a b.
apply (TransitivityEq (%(%MInvert_of_Grp (o{<Ope_Grp ! gcond})) (%(o{<Ope_Grp ! gcond}){<Grp_Ope} [a;b]))).
 hyperreflexivity.
rewrite MInvert_of_GrpMultTheorem.
hyperreflexivity.
Qed.


Theorem NonEmptyGroup : forall {A} (g : #(Group A)), NonEmpty A.
Proof.
intros A g.
apply (NonEmptyMonoid (g{<Grp_Monoid})).
Qed.


(* Sub Group *)
Definition IsSubGroup {A} : #(Relation (Group A) (PowerSet A)) :=
%AndRelation [
  %(RistrictRelationL Grp_Ope) IsSubBOperation ;
  MakeRelation (fun g S =>
    NonEmpty S /\
    forall a : #A, In a S -> In (%(%MInvert_of_Grp g) a) S
  )
].

Theorem IsSubGroupTheorem : forall {A} (g : #(Group A)) (S : #(PowerSet A)),
&&IsSubGroup g S <->
(&&IsSubBOperation (g{<Grp_Ope}) S /\ NonEmpty S /\ forall a : #A, In a S -> In (%(%MInvert_of_Grp g) a) S).
Proof.
intros A g S.
split.
 intro IsSH.
 apply AndRelationTheorem in IsSH.
 destruct IsSH as [RH MH].
 split.
  generalize RH.
  apply StrongRelationRel.
   hyperreflexivity.
   hyperreflexivity.
  apply StrongRelRistrictL.
 put ((proj1 (MakeRelationTheorem _ _ _ _ _)) MH) MH'.
 apply MH'; hyperreflexivity.

 intro HD.
 destruct HD as [IsSubB HH].
 unfold IsSubGroup.
 apply AndRelationTheorem.
 split.
  apply ToRistrictRelationL.
  apply IsSubB.
 apply MakeRelationTheorem.
 intros g' S' Eqg EqS.
 split.
  rewrite <- EqS.
  apply (proj1 HH).
 intros a InaS.
 cut (In (%(%MInvert_of_Grp g) a) S).
  apply Arrow2Rewrite.
  apply MapEq.
  apply MapArgEq.
  apply Eqg.
  apply EqS.
 apply HH.
 generalize InaS.
 apply ArrowRewrite.
 apply SymmetryEq.
 apply EqS.
Qed.

Definition SubGroup {A} :=
%RelImageE (@IsSubGroup A).

Theorem SubGroupHasIdent : forall {A} (g : #(Group A)) (S : #(%SubGroup g)),
In (MIdent_of_Grp g) S.
Proof.
intros A g S.
put (SetProp S) IsSS.
unfold SubGroup in IsSS.
apply RelationImageETheoremExists in IsSS.
destruct IsSS as [InSP IsSg].
apply IsSubGroupTheorem in IsSg.
destruct IsSg as [IsSubB IsSg].
assert(NES : NonEmpty S).
 apply (proj1 IsSg).
destruct IsSg as [_ IsSg].
destruct NES as [_s InsS].
put InSP SubSA.
apply PowersetTheorem in SubSA.
assert(InsA : In _s A).
 apply SubSA.
 apply InsS.
set {_ ! InsA} as s.
set (%(%MInvert_of_Grp g) s) as sI.
assert (InsIS : In sI S).
 apply IsSg.
 apply InsS.
cut (In (%(g{<Grp_Ope}) [s;sI]) S).
 apply Arrow2Rewrite.
 apply SymmetryEq.
 unfold MIdent_of_Grp.
 apply MIdentEq.
 cut (&&IsIdent (g{<Grp_Ope}) (%(g{<Grp_Ope}) [s;sI])).
  apply RelRewriteL.
  hyperreflexivity.
 apply IsInverseE_IsIdent.
 apply MInvert_of_GrpTheorem.
 hyperreflexivity.
put ((proj1 (IsSubBOperationTheorem _ _)) IsSubB) SubH.
apply SubH.
apply InsS.
apply InsIS.
Qed.

Theorem SubGrp_SubMonoid : forall {A} {g : #(Group A)},
Subset (%SubGroup g) (SubMonoid (g{<Grp_Monoid})).
Proof.
intros A g.
unfold SubGroup.
intros H InHS.
apply RelationImageETheoremExists in InHS.
destruct InHS as [InHP IsSG].
assert(InHSG : In H (%SubGroup g)).
 rewrite (DSETEq' _ InHP).
 unfold SubGroup.
 apply RelationImageETheorem.
 apply IsSG.
apply IsSubGroupTheorem in IsSG.
rewrite (DSETEq' _ InHP).
unfold SubMonoid.
unfold SubIdentical.
apply RelationImageETheorem.
apply IsSubIdenticalTheorem.
split.
 generalize (proj1 IsSG).
 apply RelRewriteL.
 hyperreflexivity.
intros e IsIe.
cut (In (MIdent_of_Grp g) {_!InHSG}).
 apply Arrow2Rewrite.
  unfold MIdent_of_Grp.
  apply MIdentEq.
  apply IsIe.
 hyperreflexivity.
apply SubGroupHasIdent.
Qed.

Theorem SubGrp_SubSGrp : forall {A} {g : #(Group A)},
Subset (%SubGroup g) (SubSemiGroup (g{<Grp_SGrp})).
Proof.
intros A m.
apply (TransitivitySubset _ SubGrp_SubMonoid).
apply (TransitivitySubset _ SubMonoid_SubSGrp).
apply ReflexivitySubset2.
hyperreflexivity.
Qed.

Theorem SubGrp_SubOpe : forall {A} {g : #(Group A)},
Subset (%SubGroup g) (%SubBOperation (g{<Grp_Ope})).
Proof.
intros A g.
apply (TransitivitySubset _ SubGrp_SubSGrp).
apply (TransitivitySubset _ SubSGrp_SubOpe).
apply ReflexivitySubset2.
hyperreflexivity.
Qed.



Definition SubGrp_to_Ope {A} {g : #(Group A)} (S : #(%SubGroup g)) : #(BOperation S) :=
Sub_to_BOperation (S{<SubGrp_SubOpe}).


Theorem Sub_to_GroupCond : forall {A} (g : #(Group A)) (S : #(%SubGroup g)),
Ope_GrpCond (SubGrp_to_Ope S).
Proof.
intros A g S.
unfold SubGrp_to_Ope.
put (SetProp S) InSubG.
unfold SubGroup in InSubG.
apply RelationImageETheoremExists in InSubG.
destruct InSubG as [InSP InSubG].
apply IsSubGroupTheorem in InSubG.
destruct InSubG as [IsSubB cond].
destruct cond as [_ cond].
put InSP subSP.
apply PowersetTheorem in subSP.
put ((proj1 (IsSubBOperationTheorem _ _)) IsSubB) CC.
split.
split.
 cut (Ope_SGrpCond (g{<Grp_Ope})).
  apply Ope_SGrpCond_StrongCons.
  apply (StrongSubBOpe _ _ (S{<SubGrp_SubOpe})).
  apply ReflexivityStrongRel.
 apply Ope_SGrp.
 apply Grp_SGrp.
 apply (SetProp g).

 unfold Ope_IdentCond.
 set (MIdent_of_Grp g) as e.
 assert(IneS : In e S).
  apply SubGroupHasIdent.
 exists {_ ! IneS}.
 cut (&&IsIdent (g{<Grp_Ope}) e).
  apply IsIdent_StrongCons.
  hyperreflexivity.
  apply (StrongSubBOpe _ _ (S{<SubGrp_SubOpe})).
  apply ReflexivityStrongRel.
 generalize (MIdentTheorem (g{<Grp_Ident})).
 apply RelRewriteAll.
  hyperreflexivity.
  hyperreflexivity.
  hyperreflexivity.

 unfold Ope_InvertCond.
 intros a.
 apply IsInvertibleTheorem.
 set (a{<subSP}) as aA.
 set (%(%MInvert_of_Grp g) aA) as aIA.
 assert(InaIS : In aIA S).
  apply cond.
  apply (SetProp a).
 exists {_ ! InaIS}.
 cut (&&(%IsInverseE (g{<Grp_Ope})) aA aIA).
  apply IsInverseE_StrongCons.
  hyperreflexivity.
  hyperreflexivity.
  apply (StrongSubBOpe _ _ (S{<SubGrp_SubOpe})).
  apply ReflexivityStrongRel.
 apply MInvert_of_GrpTheorem.
Qed.

Definition Sub_to_Group {A} {g : #(Group A)} (S : #(%SubGroup g)) : #(Group S) :=
_{<Ope_Grp ! Sub_to_GroupCond g S}.


Theorem StrongSubGrp : forall {A B} (g1 : #(Group A)) (g2 : #(Group B)) (S : #(%SubGroup g1)),
StrongMap (g1{<Grp_Ope}) (g2{<Grp_Ope}) ->
StrongMap (Sub_to_Group S){<Grp_Ope} (g2{<Grp_Ope}).
Proof.
intros A B g1 g2 S SH.
apply (TransitivityStrongRel (Sub_to_BOperation (S{<SubGrp_SubOpe})){<Map_Rel}).
 apply ReflexivityStrongRel2.
 hyperreflexivity.
apply (StrongSubBOpe _ _ (S{<SubGrp_SubOpe})).
apply SH.
Qed.



(* Commtative Group *)
Definition CGroup A := Section (Group A) (Commutative A).

Theorem CGrp_Grp : forall {A}, Subset (CGroup A) (Group A).
Proof.
intros A.
apply SectionSubsetL.
Qed.

Theorem CGrp_Comm : forall {A}, Subset (CGroup A) (Commutative A).
Proof.
intros A.
apply SectionSubsetR.
Qed.

Theorem CGrp_Ope : forall {A}, Subset (CGroup A) (BOperation A).
Proof.
intro A.
apply (TransitivitySubset (Group A)).
apply CGrp_Grp.
apply Grp_Ope.
Qed.

Theorem CGrp_SGrp : forall {A}, Subset (CGroup A) (SemiGroup A).
Proof.
intro A.
apply (TransitivitySubset (Group A)).
apply CGrp_Grp.
apply Grp_SGrp.
Qed.

Theorem CGrp_Ident : forall {A}, Subset (CGroup A) (Identical A).
Proof.
intro A.
apply (TransitivitySubset (Group A)).
apply CGrp_Grp.
apply Grp_Ident.
Qed.

Theorem CGrp_Monoid : forall {A}, Subset (CGroup A) (Monoid A).
Proof.
intro A.
apply (TransitivitySubset (Group A)).
apply CGrp_Grp.
apply Grp_Monoid.
Qed.

Theorem CGrp_CMonoid : forall {A}, Subset (CGroup A) (CMonoid A).
Proof.
intro A.
intros g IngCG.
apply SectionTheorem.
split.
apply CGrp_Monoid.
apply IngCG.
apply SectionTheorem in IngCG.
apply (proj2 IngCG).
Qed.


Definition Ope_CGrpCond {A} (o : #(BOperation A)) := 
Ope_GrpCond o /\ Ope_CommCond o.

Theorem Ope_CGrp : forall {A} (o : #(BOperation A)),
Ope_CGrpCond o <-> In o (CGroup A).
Proof.
intros A o.
split.
 intro OCG.
 apply SectionTheorem.
 destruct OCG as [GC CC].
 split.
 apply Ope_Grp.
 apply GC.
 apply Ope_Comm.
 apply CC.

 intro oCG.
 apply SectionTheorem in oCG.
 destruct oCG as [InoG InOC].
 split.
 apply Ope_Grp.
 apply InoG.
 apply Ope_Comm.
 apply InOC.
Qed.

Definition MIdent_of_CGrp {A} (g : #(CGroup A)) :=
%MIdent (g{<CGrp_Ident}).

Definition IsIdent_of_CGrp {A} (g : #(CGroup A)) (a : #A) :=
&&IsIdent (g{<CGrp_Ope}) a.

Definition IsInverseE_of_CGrp {A} (g : #(CGroup A)) :=
%IsInverseE (g{<CGrp_Ope}).

Definition IsInvertible_of_CGrp {A} (g : #(CGroup A)) a :=
&&IsInvertible (g{<CGrp_Ope}) a.

Definition Invertible_of_CGrp {A} (g : #(CGroup A)) :=
%Invertible (g{<CGrp_Ope}).

Definition MInvert_of_CGrp {A} (g : #(CGroup A)) :=
%MInvert_of_Grp (g{<CGrp_Grp}).

Theorem MInvert_of_CGrpTheorem : forall {A} (g : #(CGroup A)) a,
&&(IsInverseE_of_CGrp g) a (%(MInvert_of_CGrp g) a).
Proof.
intros A g a.
generalize (MInvert_of_GrpTheorem (g{<CGrp_Grp}) a).
apply RelRewriteAll; hyperreflexivity.
Qed.

Theorem MInvert_of_CGrpREq : forall {A} (g : #(CGroup A)) (a b : #A),
%(MInvert_of_CGrp g) a == b <->
&&(IsInverseE_of_CGrp g) a b.
Proof.
intros A g a b.
unfold MInvert_of_CGrp.
apply (TransitivityEquiv (&&(IsInverseE_of_Grp g{<CGrp_Grp}) a b)).
apply MInvert_of_GrpREq.
split; apply RelRewrite; hyperreflexivity.
Qed.
 
Theorem IsInverseEMultCGrp : forall {A} (g : #(CGroup A)) (a a' b b' : #A),
&&(IsInverseE_of_CGrp g) a a' -> &&(IsInverseE_of_CGrp g) b b' ->
&&(IsInverseE_of_CGrp g) (%g{<CGrp_Ope} [a;b]) (%g{<CGrp_Ope} [b';a']).
Proof.
intros A g a a' b b'.
unfold IsInverseE_of_CGrp.
apply IsInverseEMultSGrp.
 apply Ope_SGrp.
 apply CGrp_SGrp.
 apply (SetProp g).
Qed.

Theorem MInvert_of_CGrpMultTheorem : forall {A} (g : #(CGroup A)) a b,
%(MInvert_of_CGrp g) (%g{<CGrp_Ope} [a;b]) ==
%g{<CGrp_Ope} [%(MInvert_of_CGrp g) a ; %(MInvert_of_CGrp g) b].
Proof.
intros A g a b.
unfold MInvert_of_CGrp at 1.
cut (Ope_CommCond (g{<CGrp_Ope})).
 intro cond.
 rewrite cond.
 apply (TransitivityEq (%(%MInvert_of_Grp (g{<CGrp_Grp})) (%(g{<CGrp_Grp}{<Grp_Ope}) [a;b]))).
  hyperreflexivity.
 rewrite MInvert_of_GrpMultTheorem.
 hyperreflexivity.
apply Ope_Comm.
apply CGrp_Comm.
apply (SetProp g).
Qed.

Theorem MInvert_of_CGrpMultTheoremWP : forall {A} (o : #(BOperation A)) (gcond : Ope_CGrpCond o) a b,
%(MInvert_of_CGrp (o{<Ope_CGrp ! gcond})) (%o [a;b]) ==
%o [%(MInvert_of_CGrp (o{<Ope_CGrp ! gcond})) a ; %(MInvert_of_CGrp (o{<Ope_CGrp ! gcond})) b].
Proof.
intros A o gcond a b.
apply (TransitivityEq (%(MInvert_of_CGrp (o{<Ope_CGrp ! gcond})) (%(o{<Ope_CGrp ! gcond}){<CGrp_Ope} [a;b]))).
 hyperreflexivity.
rewrite MInvert_of_CGrpMultTheorem.
hyperreflexivity.
Qed.


(********************************************)
(** Commutative Monoid to Commutative Group *)
(********************************************)

(* Preparations *)
Definition ProductOfCMonoid_SubCMonoid {A} (CM : #(CMonoid A)) (S : #(SubCMonoid CM)) :=
%ProductOperation [CM{<CMonoid_Ope} ; (Sub_to_BOperation (S{<SubCMonoid_SubOpe}))].

Theorem ProductOfCMonoid_SubCMonoidTheorem : forall {A} (CM : #(CMonoid A)) (S : #(SubCMonoid CM)) (a b : #A) (p q : #S),
%(ProductOfCMonoid_SubCMonoid CM S) [[a;p] ; [b;q]] ==
[%(CM{<CMonoid_Ope}) [a;b] ; %(SubCMonoid_to_Ope S) [p;q]].
Proof.
intros.
unfold ProductOfCMonoid_SubCMonoid.
rewrite ProductOperationTheorem.
hyperreflexivity.
Qed.


Theorem ProductOfCMonoid_SubCMonoid_Ope_CMonoidCond : forall {A} (CM : #(CMonoid A)) (S : #(SubCMonoid CM)),
Ope_CMonoidCond (ProductOfCMonoid_SubCMonoid CM S).
intros A CM S.
unfold ProductOfCMonoid_SubCMonoid.
apply Ope_CMonoidCond_Product.
 apply Ope_CMonoid.
 apply (SetProp CM).
apply (Ope_CMonoidCond_StrongCons _ (CM{<CMonoid_Ope})).
  apply StrongSubBOpe.
  apply ReflexivityStrongRel.
 intros e IH.
 rewrite USETEq.
 rewrite (USETEq' _ SubCMonoid_SubIdent).
 apply SubIdenticalHasIdent.
 apply IH.
apply Ope_CMonoid.
apply (SetProp CM).
Qed.

Definition ProductOfCMonoid_SubCMonoidERelationRel {A} {CM : #(CMonoid A)} {S : #(SubCMonoid CM)} : #(BRelation (Cartesian A S)) :=
let o := (CM{<CMonoid_Ope}) in
MakeRelation (fun aa bb => exists s : #S, %o [%o [%MLeft aa ; (%MRight bb){<SubCMonoid_S}] ; s{<SubCMonoid_S}] == %o [%o [%MLeft bb ; (%MRight aa){<SubCMonoid_S}] ; s{<SubCMonoid_S}]).

Theorem ProductOfCMonoid_SubCMonoidERelationRelTheorem : forall {A} (CM : #(CMonoid A)) (S : #(SubCMonoid CM)) (a : #A) (b : #A) (p : #S) (q : #S),
&&ProductOfCMonoid_SubCMonoidERelationRel [a;p] [b;q] <->
exists s : #S, (%(CM{<CMonoid_Ope}) [%CM{<CMonoid_Ope} [a;q{<SubCMonoid_S}] ; s{<SubCMonoid_S}]) == (%(CM{<CMonoid_Ope}) [%CM{<CMonoid_Ope} [b;p{<SubCMonoid_S}] ; s{<SubCMonoid_S}]).
(* aqs == bps *)
Proof.
intros A CM S a b p q.
split.
 intro PH.
 put ((proj1 (MakeRelationTheorem _ _ _ _ _)) PH) PH'.
 clear PH.
 put (PH' _ _ (ReflexivityEq _) (ReflexivityEq _)) PH.
 clear PH'.
 destruct PH as [s PH].
 exists s.
 apply (TransitivityEq (%(CM{<CMonoid_Ope}) [%(CM{<CMonoid_Ope}) [%MLeft [a;p] ; (%MRight[b;q]){<SubCMonoid_S}] ; s{<SubCMonoid_S}])).
  apply MapArgEq.
  apply EqualInPair'L.
  apply MapArgEq.
  apply EqualInPair'.
  split.
   apply SymmetryEq.
   apply LeftPairTheorem.
  apply SymmetryEq.
  rewrite (USETEq _ SubCMonoid_S).
  rewrite (USETEq _ SubCMonoid_S).
  apply RightPairTheorem.
 rewrite PH.
 apply MapArgEq.
 apply EqualInPair'L.
 apply MapArgEq.
 apply EqualInPair'.
 split.
  apply LeftPairTheorem.
 rewrite (USETEq _ SubCMonoid_S).
 rewrite (USETEq _ SubCMonoid_S).
 apply RightPairTheorem.
intro cond.
destruct cond as [s cond].
apply MakeRelationTheorem.
intros aa' bb' Eqaa' Eqbb'.
exists s.
apply (TransitivityEq (%(CM{<CMonoid_Ope}) [%(CM{<CMonoid_Ope}) [a ; q{<SubCMonoid_S}] ; s{<SubCMonoid_S}])).
 apply MapArgEq.
 apply EqualInPair'L.
 apply MapArgEq.
 apply EqualInPair'.
 split.
  rewrite (MapArgEq' _ Eqaa').
  apply LeftPairTheorem.
 rewrite (USETEq _ SubCMonoid_S).
 rewrite (USETEq _ SubCMonoid_S).
 rewrite (MapArgEq' _ Eqbb').
 apply RightPairTheorem.
rewrite cond.
apply MapArgEq.
apply EqualInPair'L.
apply MapArgEq.
apply EqualInPair'.
split.
 rewrite (MapArgEq' _ Eqbb').
 apply SymmetryEq.
 apply LeftPairTheorem.
rewrite (USETEq _ SubCMonoid_S).
rewrite (USETEq _ SubCMonoid_S).
apply SymmetryEq.
rewrite (MapArgEq' _ Eqaa').
apply RightPairTheorem.
Qed.

Theorem ProductOfCMonoid_SubCMonoidERelationRel_RefCond : forall {A} (CA : #(CMonoid A)) (S : #(SubCMonoid CA)),
Rel_RefCond (@ProductOfCMonoid_SubCMonoidERelationRel _ CA S).
Proof.
intros A CA S.
intro aa.
put (CartesianIsPair' _ _ _ (SetProp aa)) Eqaa.
destruct Eqaa as [a Eqaa].
destruct Eqaa as [s Eqaa].
apply (RelRewriteL' Eqaa).
apply (RelRewriteR' Eqaa).
apply ProductOfCMonoid_SubCMonoidERelationRelTheorem.
exists s.
hyperreflexivity.
Qed.

Theorem ProductOfCMonoid_SubCMonoidERelationRel_SymCond : forall {A} (CA : #(CMonoid A)) (S : #(SubCMonoid CA)),
Rel_SymCond (@ProductOfCMonoid_SubCMonoidERelationRel _ CA S).
Proof.
intros A CA S.
intros aa bb HH.
put (CartesianIsPair' _ _ _ (SetProp aa)) Eqaa.
destruct Eqaa as [a Eqaa].
destruct Eqaa as [p Eqaa].
put (CartesianIsPair' _ _ _ (SetProp bb)) Eqbb.
destruct Eqbb as [b Eqbb].
destruct Eqbb as [q Eqbb].
apply (RelRewriteL' Eqbb).
apply (RelRewriteR' Eqaa).
apply (RelRewriteL Eqaa) in HH.
apply (RelRewriteR Eqbb) in HH.
apply ProductOfCMonoid_SubCMonoidERelationRelTheorem in HH.
destruct HH as [s HH].
apply ProductOfCMonoid_SubCMonoidERelationRelTheorem.
exists s.
apply SymmetryEq.
apply HH.
Qed.

Theorem ProductOfCMonoid_SubCMonoidERelationRel_TransCond : forall {A} (CA : #(CMonoid A)) (S : #(SubCMonoid CA)),
Rel_TransCond (@ProductOfCMonoid_SubCMonoidERelationRel _ CA S).
Proof.
intros A CA S.
intros aa bb cc HH1 HH2.
put (CartesianIsPair' _ _ _ (SetProp aa)) Eqaa.
destruct Eqaa as [a Eqaa].
destruct Eqaa as [p Eqaa].
put (CartesianIsPair' _ _ _ (SetProp bb)) Eqbb.
destruct Eqbb as [b Eqbb].
destruct Eqbb as [q Eqbb].
put (CartesianIsPair' _ _ _ (SetProp cc)) Eqcc.
destruct Eqcc as [c Eqcc].
destruct Eqcc as [r Eqcc].
apply (RelRewriteL Eqaa) in HH1.
apply (RelRewriteR Eqbb) in HH1.
apply (RelRewriteL Eqbb) in HH2.
apply (RelRewriteR Eqcc) in HH2.
apply (RelRewriteL' Eqaa).
apply (RelRewriteR' Eqcc).
apply ProductOfCMonoid_SubCMonoidERelationRelTheorem in HH1.
destruct HH1 as [s HH1].
apply ProductOfCMonoid_SubCMonoidERelationRelTheorem in HH2.
destruct HH2 as [t HH2].
apply ProductOfCMonoid_SubCMonoidERelationRelTheorem.
set (CA{<CMonoid_Ope}) as o.
set (p{<SubCMonoid_S}) as pp.
set (q{<SubCMonoid_S}) as qq.
set (r{<SubCMonoid_S}) as rr.
set (s{<SubCMonoid_S}) as ss.
set (t{<SubCMonoid_S}) as tt.
assert(HH1' : %o [%o [a;qq]; ss] == %o [%o [b;pp] ; ss]).
 apply HH1.
assert(HH2' : %o [%o [b;rr]; tt] == %o [%o [c;qq] ; tt]).
 apply HH2.
clear HH1.
clear HH2.
set (%o [%o [ss;tt] ; qq]) as v.
assert(InvS : In v S).
 put (SetProp S) InSS'.
 unfold SubCMonoid in InSS'.
 assert(InSP : In S (PowerSet A)).
  apply SubIdenticalSubset in InSS'.
  apply InSS'.
 set {_ ! InSP} as S'.
 assert(InSS : In S' (%SubIdentical (CA{<CMonoid_Ope}))).
  apply InSS'.
 clear InSS'.
 apply SubIdenticalTheorem in InSS.
 apply IsSubIdenticalTheorem in InSS.
 destruct InSS as [IsSB cond].
 put ((proj1 (IsSubBOperationTheorem _ _)) IsSB) IsSB'.
 clear IsSB.
 cut (In v S').
  intro; assumption.
 unfold v.
 apply IsSB'.
 apply IsSB'.
 apply (SetProp s).
 apply (SetProp t).
 apply (SetProp q).
exists {v ! InvS}.
apply (TransitivityEq (%o [%o [a; rr] ; v])).
 hyperreflexivity.
unfold v.
assert(Ass : Ope_SGrpCond o).
 apply Ope_SGrp.
 apply CMonoid_SGrp.
 unfold o.
 apply (SetProp CA).
assert(Comm : Ope_CommCond o).
 apply Ope_Comm.
 apply CMonoid_Comm.
 unfold o.
 apply (SetProp CA).
apply (TransitivityEq (%o [%o [a;rr] ; %o [qq;%o[ss;tt]]])).
 apply MapArgEq.
 apply EqualInPair'R.
 apply Comm.
apply (TransitivityEq (%o [%o [a;rr] ; %o [%o [qq;ss] ; tt]])).
 apply MapArgEq.
 apply EqualInPair'R.
 apply SymmetryEq.
 apply Ass.
apply (TransitivityEq (%o [a ; %o [rr ; %o [ %o [qq;ss] ; tt]]])).
 apply Ass.
apply (TransitivityEq (%o [a ; %o [%o [%o [qq;ss] ; tt] ; rr]])).
 apply MapArgEq.
 apply EqualInPair'R.
 apply Comm.
apply (TransitivityEq (%o [%o [a;%o[%o[qq;ss] ; tt]] ; rr])).
 apply SymmetryEq.
 apply Ass.
apply (TransitivityEq (%o [%o [%o [a ; %o [qq;ss]] ; tt] ; rr])).
 apply MapArgEq.
 apply EqualInPair'L.
 apply SymmetryEq.
 apply Ass.
apply (TransitivityEq (%o [%o [%o [%o [a ; qq] ; ss] ; tt] ; rr])).
 apply MapArgEq.
 apply EqualInPair'L.
 apply MapArgEq.
 apply EqualInPair'L.
 apply SymmetryEq.
 apply Ass.
apply (TransitivityEq (%o [%o [%o [%o [b ; pp] ; ss] ;tt] ; rr])).
 apply MapArgEq.
 apply EqualInPair'L.
 apply MapArgEq.
 apply EqualInPair'L.
 apply HH1'.
apply (TransitivityEq (%o [%o [%o [b;pp];ss] ; %o[tt;rr]])).
 apply Ass.
apply (TransitivityEq (%o [%o [%o [b;pp];ss] ; %o[rr;tt]])).
 apply MapArgEq.
 apply EqualInPair'R.
 apply Comm.
apply (TransitivityEq (%o [%o [b;pp] ; %o [ss; %o [rr;tt]]])).
 apply Ass.
apply (TransitivityEq (%o [%o [b;pp] ; %o [%o [rr;tt] ; ss]])).
 apply MapArgEq.
 apply EqualInPair'R.
 apply SymmetryEq.
 apply Comm.
apply (TransitivityEq (%o [b ; %o [pp ; %o [%o [rr;tt] ; ss]]])).
 apply Ass.
apply (TransitivityEq (%o [b ; %o [%o [%o [rr;tt] ; ss] ; pp]])).
 apply MapArgEq.
 apply EqualInPair'R.
 apply SymmetryEq.
 apply Comm.
apply (TransitivityEq (%o [%o [b ; %o [%o [rr;tt]; ss]] ; pp])).
 apply SymmetryEq.
 apply Ass.
apply (TransitivityEq (%o [%o [%o [b ; %o [rr;tt]] ; ss] ; pp])).
 apply MapArgEq.
 apply EqualInPair'L.
 apply SymmetryEq.
 apply Ass.
apply (TransitivityEq (%o [%o [%o [%o [b;rr];tt] ; ss] ; pp])).
 apply MapArgEq.
 apply EqualInPair'L.
 apply MapArgEq.
 apply EqualInPair'L.
 apply SymmetryEq.
 apply Ass.
apply (TransitivityEq (%o [%o [%o [%o [c;qq];tt];ss];pp])).
 apply MapArgEq.
 apply EqualInPair'L.
 apply MapArgEq.
 apply EqualInPair'L.
 apply HH2'.
rewrite (MapArgEq _ (EqualInPair'L _ _ _ _ _ (Ass _ _ _))).
rewrite (MapArgEq _ (EqualInPair'L _ _ _ _ _ (MapArgEq _ (EqualInPair'R _ _ _ _ _ (Comm _ _))))).
rewrite (MapArgEq _ (EqualInPair'L _ _ _ _ _ (Ass _ _ _))).
rewrite (MapArgEq _ (EqualInPair'L _ _ _ _ _ (MapArgEq _ (EqualInPair'R _ _ _ _ _ (Comm _ _))))).
rewrite Ass.
rewrite (MapArgEq _ (EqualInPair'R _ _ _ _ _ (Comm _ _))).
rewrite <- Ass.
hyperreflexivity.
Qed.

Theorem ProductOfCMonoid_SubCMonoidERelationRel_ERelCond : forall {A} (CA : #(CMonoid A)) (S : #(SubCMonoid CA)),
Rel_ERelCond (@ProductOfCMonoid_SubCMonoidERelationRel _ CA S).
Proof.
intros A CA S.
split.
 apply ProductOfCMonoid_SubCMonoidERelationRel_RefCond.
split.
 apply ProductOfCMonoid_SubCMonoidERelationRel_SymCond.
apply ProductOfCMonoid_SubCMonoidERelationRel_TransCond.
Qed.

Definition ProductOfCMonoid_SubCMonoidERelation {A} (CA : #(CMonoid A)) (S : #(SubCMonoid CA)) :=
(_{<Rel_ERel ! (ProductOfCMonoid_SubCMonoidERelationRel_ERelCond CA S)}).

Theorem ProductOfCMonoid_SubMonoidERelationIsQable : forall {A} (CA : #(CMonoid A)) (S : #(SubCMonoid CA)), 
BOpe_QableBOpeWCCond (%ERel_to_Class (ProductOfCMonoid_SubCMonoidERelation CA S)) (ProductOfCMonoid_SubCMonoid CA S).
Proof.
intros A CA S.
unfold BOpe_QableBOpeWCCond.
apply IsQuotientableBOpeWCTheorem.
set (ProductOfCMonoid_SubCMonoid CA S) as o.
set (ProductOfCMonoid_SubCMonoidERelation CA S) as erel.
set (@ProductOfCMonoid_SubCMonoidERelationRel _ CA S) as rel.
intros aa aa' bb bb' relH.
destruct relH as [relH1' relH2'].
assert(relH1 : &&rel aa aa').
 generalize relH1'.
 apply RelRewrite.
 unfold rel.
 apply (TransitivityEq erel).
  rewrite <- Class_to_ERel_to_Class.
  hyperreflexivity.
 hyperreflexivity.
assert(relH2 : &&rel bb bb').
 generalize relH2'.
 apply RelRewrite.
 unfold rel.
 apply (TransitivityEq erel).
  rewrite <- Class_to_ERel_to_Class.
  hyperreflexivity.
 hyperreflexivity.
clear relH1'.
clear relH2'.
put (CartesianIsPair' _ _ _ (SetProp aa)) Eqaa.
destruct Eqaa as [a Eqaa].
destruct Eqaa as [p Eqaa].
put (CartesianIsPair' _ _ _ (SetProp aa')) Eqaa'.
destruct Eqaa' as [a' Eqaa'].
destruct Eqaa' as [p' Eqaa'].
put (CartesianIsPair' _ _ _ (SetProp bb)) Eqbb.
destruct Eqbb as [b Eqbb].
destruct Eqbb as [q Eqbb].
put (CartesianIsPair' _ _ _ (SetProp bb')) Eqbb'.
destruct Eqbb' as [b' Eqbb'].
destruct Eqbb' as [q' Eqbb'].
apply (RelRewriteL Eqaa) in relH1.
apply (RelRewriteR Eqaa') in relH1.
apply (RelRewriteL Eqbb) in relH2.
apply (RelRewriteR Eqbb') in relH2.
cut (&&rel (%o[[a;p] ; [b;q]]) (%o [[a';p'] ; [b';q']])).
 apply RelRewriteAll.
   apply MapArgEq.
   apply EqualInPair'.
   split.
    apply SymmetryEq.
    apply Eqaa.
   apply SymmetryEq.
   apply Eqbb.
  apply MapArgEq.
  apply EqualInPair'.
  split.
   apply SymmetryEq.
   apply Eqaa'.
  apply SymmetryEq.
  apply Eqbb'.
 apply SymmetryEq.
 apply (TransitivityEq erel).
  rewrite <- Class_to_ERel_to_Class.
  hyperreflexivity.
 hyperreflexivity.
clear Eqaa.
clear Eqaa'.
clear Eqbb.
clear Eqbb'.
clear aa.
clear bb.
clear aa'.
clear bb'.
clear erel.
apply ProductOfCMonoid_SubCMonoidERelationRelTheorem in relH1.
apply ProductOfCMonoid_SubCMonoidERelationRelTheorem in relH2.
set (CA{<CMonoid_Ope}) as co.
destruct relH1 as [s relH1'].
destruct relH2 as [t relH2'].
set (p{<SubCMonoid_S}) as pa.
set (q{<SubCMonoid_S}) as qa.
set (s{<SubCMonoid_S}) as sa.
set (t{<SubCMonoid_S}) as ta.
set (p'{<SubCMonoid_S}) as pa'.
set (q'{<SubCMonoid_S}) as qa'.
assert(relH1 : %co [%co [a;pa'] ; sa] == %co [%co [a';pa] ; sa]).
 apply relH1'.
assert(relH2 : %co [%co [b;qa'] ; ta] == %co [%co [b';qa] ; ta]).
 apply relH2'.
clear relH1'.
clear relH2'.
set (Sub_to_BOperation (S{<SubCMonoid_SubOpe})) as so.
assert(CommSO : forall a b : (#S), %so [a;b] == %co[a{<SubCMonoid_S} ; b{<SubCMonoid_S}]).
 intros s1 s2.
 apply MapStrong.
  unfold so.
  unfold co.
  apply (StrongSubBOpe _ _ (S{<SubCMonoid_SubOpe})).
  apply ReflexivityStrongRel.
 hyperreflexivity.
cut (&&rel [%co[a;b] ; %so[p;q]] [%co[a';b'] ; %so[p';q']]).
 apply RelRewriteAll.
   apply SymmetryEq.
   unfold o.
   unfold ProductOfCMonoid_SubCMonoid.
   rewrite ProductOperationTheorem.
   hyperreflexivity.
  apply SymmetryEq.
  unfold o.
  unfold ProductOfCMonoid_SubCMonoid.
  rewrite ProductOperationTheorem.
  hyperreflexivity.
 hyperreflexivity.
apply (@ProductOfCMonoid_SubCMonoidERelationRelTheorem _ _ _ _ _ (%so [p;q]) (%so [p';q'])). 
exists (%so [s;t]).
apply (TransitivityEq (%co [%co [%co [a;b] ; %co [pa';qa']] ; %co[sa;ta]])).
 apply MapArgEq.
 apply EqualInPair'.
 split.
  apply MapArgEq.
  apply EqualInPair'R.
  rewrite (USETEq _ SubCMonoid_S).
  rewrite CommSO.
  hyperreflexivity.
 rewrite (USETEq _ SubCMonoid_S).
 rewrite CommSO.
 hyperreflexivity.
apply (TransitivityEq (%co [%co [%co[a';b'];%co[pa;qa]];%co[sa;ta]])).
 assert(AssocT : Ope_SGrpCond co).
  apply Ope_SGrp.
  apply CMonoid_SGrp.
  apply (SetProp CA).
 assert(CommT : Ope_CommCond co).
  apply Ope_Comm.
  apply CMonoid_Comm.
  apply (SetProp CA).
 apply (TransitivityEq (%co [%co [%co [a;pa'] ; sa] ; %co [%co [b;qa'] ; ta]])).
  rewrite (MapArgEq' _ (EqualInPair'L _ _ _ _ _ (AssocT _ _ _))).
  rewrite (MapArgEq _ (EqualInPair'L _ _ _ _ _ (MapArgEq _ (EqualInPair'L _ _ _ _ _ (AssocT _ _ _))))).
  rewrite (MapArgEq _ (EqualInPair'L _ _ _ _ _ (MapArgEq _ (EqualInPair'L _ _ _ _ _ (MapArgEq _ (EqualInPair'R _ _ _ _ _ (CommT _ _))))))).
  rewrite (MapArgEq' _ (EqualInPair'L _ _ _ _ _ (MapArgEq _ (EqualInPair'L _ _ _ _ _ (AssocT _ _ _))))).
  rewrite (MapArgEq _ (EqualInPair'L _ _ _ _ _ (AssocT _ _ _))).
  rewrite AssocT.
  rewrite (MapArgEq' _ (EqualInPair'R _ _ _ _ _ (AssocT _ _ _))).
  rewrite (MapArgEq _ (EqualInPair'R _ _ _ _ _ (MapArgEq _ (EqualInPair'L _ _ _ _ _ (CommT _ _))))).
  rewrite (MapArgEq _ (EqualInPair'R _ _ _ _ _ (AssocT _ _ _))).
  rewrite <- AssocT.
  hyperreflexivity.
 apply (TransitivityEq (%co [%co [%co [a';pa] ; sa] ; %co [%co [b';qa] ; ta]])).
  rewrite (MapArgEq _ (EqualInPair'L _ _ _ _ _ relH1)).
  rewrite (MapArgEq _ (EqualInPair'R _ _ _ _ _ relH2)).
  hyperreflexivity.
 rewrite AssocT. 
 rewrite (MapArgEq' _ (EqualInPair'R _ _ _ _ _ (AssocT _ _ _))).
 rewrite (MapArgEq' _ (EqualInPair'R _ _ _ _ _ (MapArgEq _ (EqualInPair'L _ _ _ _ _ (CommT _ _))))).
 rewrite (MapArgEq _ (EqualInPair'R _ _ _ _ _ (AssocT _ _ _))).
 rewrite <- AssocT.
 rewrite (MapArgEq' _ (EqualInPair'L _ _ _ _ _ (AssocT _ _ _))).
 rewrite (MapArgEq _ (EqualInPair'L _ _ _ _ _ (MapArgEq _ (EqualInPair'L _ _ _ _ _ (AssocT _ _ _))))).
 rewrite (MapArgEq _ (EqualInPair'L _ _ _ _ _ (MapArgEq _ (EqualInPair'L _ _ _ _ _ (MapArgEq _ (EqualInPair'R _ _ _ _ _ (CommT _ _))))))).
 rewrite (MapArgEq' _ (EqualInPair'L _ _ _ _ _ (MapArgEq _ (EqualInPair'L _ _ _ _ _ (AssocT _ _ _))))).
 rewrite (MapArgEq _ (EqualInPair'L _ _ _ _ _ (AssocT _ _ _))).
 hyperreflexivity.
apply MapArgEq.
apply EqualInPair'.
split.
 apply MapArgEq.
 apply EqualInPair'R.
 rewrite (USETEq _ SubCMonoid_S).
 rewrite CommSO.
 hyperreflexivity.
rewrite (USETEq _ SubCMonoid_S).
rewrite CommSO.
hyperreflexivity.
Qed.

Definition ProductOfCMonoid_SubCMonoidQable {A} (cm : #(CMonoid A)) (S : #(SubCMonoid cm)) :=
(ProductOfCMonoid_SubCMonoid cm S){<BOpe_QableBOpeWC _ ! ProductOfCMonoid_SubMonoidERelationIsQable cm S}.

(* Fraction *)
Definition FractionCMonoidSet {A} (cm : #(CMonoid A)) (S : #(SubCMonoid cm)) :=
%ERel_to_Class (ProductOfCMonoid_SubCMonoidERelation cm S).

Definition FractionCMonoid {A} (cm : #(CMonoid A)) (S : #(SubCMonoid cm)) : #(BOperation (FractionCMonoidSet cm S)) :=
%(QuotientBOpeWC _) (ProductOfCMonoid_SubCMonoidQable cm S).

Definition to_FractionCMonoidSet {A} (cm : #(CMonoid A)) (S : #(SubCMonoid cm)) : #(Map (Cartesian A S) (FractionCMonoidSet cm S)) := EqCannProj _.

Theorem FractionCMonoidSetIn : forall {A} (cm : #(CMonoid A)) (S : #(SubCMonoid cm)),
forall (x : #(FractionCMonoidSet cm S)),
exists a : #A, exists p : #S,
x == %(to_FractionCMonoidSet cm S) [a;p].
Proof.
intros A cm S x.
put (SetProp x) InxF.
unfold FractionCMonoidSet in InxF.
apply EqCannProjIn in InxF.
destruct InxF as [ap Eqapx].
put (CartesianIsPair' _ _ _ (SetProp ap)) Eqap.
destruct Eqap as [a Eqap].
destruct Eqap as [p Eqap].
exists a.
exists p.
apply SymmetryEq in Eqapx.
apply (TransitivityEq (%(EqCannProj (%ERel_to_Class  (ProductOfCMonoid_SubCMonoidERelation cm S))) ap)).
 apply Eqapx.
rewrite (MapArgEq _ Eqap).
apply MapEq.
unfold to_FractionCMonoidSet.
unfold FractionCMonoidSet.
hyperreflexivity.
Qed.

Theorem SHomomorphic_Product_FractionCMonoid : forall {A} (cm : #(CMonoid A)) (S : #(SubCMonoid cm)),
&&SHomomorphic_of_BOpe (ProductOfCMonoid_SubCMonoid cm S) (FractionCMonoid cm S).
Proof.
intros A cm S.
apply SHomomorphic_of_BOpeTheorem.
exists (EqCannProj _).
apply IsSHomomorphism_of_BOpeTheorem.
apply SymmetryAnd.
split.
 apply Map_Sur.
 apply EqCannProjSurjection.
unfold FractionCMonoid.
apply IsHomomorphism_QuotientBOpe.
Qed.

Theorem FractionCMonoid_Ope_CommCond : forall {A} (cm : #(CMonoid A)) (S : #(SubCMonoid cm)),
Ope_CommCond (FractionCMonoid cm S).
Proof.
intros A cm S.
apply (Ope_CommCond_SHomomorphic (ProductOfCMonoid_SubCMonoid cm S)).
 apply SHomomorphic_Product_FractionCMonoid.
unfold ProductOfCMonoid_SubCMonoid.
apply Ope_CommCond_Product.
 apply Ope_Comm.
 apply CMonoid_Comm.
 apply (SetProp cm).
apply Ope_Comm.
apply CMonoid_Comm.
cut (In (Sub_to_CMonoid S) (CMonoid S)).
 intro IH. apply IH.
apply SetProp.
Qed.

Theorem FractionCMonoid_Ope_SGrpCond : forall {A} (cm : #(CMonoid A)) (S : #(SubCMonoid cm)),
Ope_SGrpCond (FractionCMonoid cm S).
Proof.
intros A cm S.
apply (Ope_SGrpCond_SHomomorphic (ProductOfCMonoid_SubCMonoid cm S)).
 apply SHomomorphic_Product_FractionCMonoid.
unfold ProductOfCMonoid_SubCMonoid.
apply Ope_SGrpCond_Product.
 apply Ope_SGrp.
 apply CMonoid_SGrp.
 apply (SetProp cm).
apply Ope_SGrp.
apply CMonoid_SGrp.
cut (In (Sub_to_CMonoid S) (CMonoid S)).
 intro IH. apply IH.
apply SetProp.
Qed.


Definition FractionCMonoidSGrp {A} (cm : #(CMonoid A)) (S : #(SubCMonoid cm)) : #(SemiGroup (FractionCMonoidSet cm S))
:=
_{<Ope_SGrp ! FractionCMonoid_Ope_SGrpCond cm S}.


Theorem FractionCMonoidProduct_Hom : forall {A} (cm : #(CMonoid A)) (S : #(SubCMonoid cm)),
&&IsHomomorphism_of_BOpe [ProductOfCMonoid_SubCMonoid cm S ; (FractionCMonoid cm S)] (to_FractionCMonoidSet cm S).
Proof.
intros A cm S.
unfold FractionCMonoid.
unfold to_FractionCMonoidSet.
apply IsHomomorphism_QuotientBOpe.
Qed.

Theorem FractionCMonoidTheorem : forall {A} (cm : #(CMonoid A)) (S : #(SubCMonoid cm)) a b p q,
%(FractionCMonoid cm S) [%(to_FractionCMonoidSet cm S) [a;p] ; %(to_FractionCMonoidSet cm S) [b;q]] ==
%(to_FractionCMonoidSet cm S) [%(cm{<CMonoid_Ope}) [a;b] ; %(SubCMonoid_to_Ope S) [p;q]].
Proof.
intros.
apply (TransitivityEq (%(to_FractionCMonoidSet cm S) (%(ProductOfCMonoid_SubCMonoid cm S) [[a;p];[b;q]]))).
 put (FractionCMonoidProduct_Hom cm S) HH'.
 put ((proj1 (IsHomomorphism_of_BOpeTheorem _ _ _)) HH') HH.
 apply SymmetryEq.
 apply HH.
apply MapArgEq.
apply (TransitivityEq (%(ProductOfCMonoid_SubCMonoid cm S) [[a;p] ; [b;q]])).
 hyperreflexivity.
rewrite ProductOfCMonoid_SubCMonoidTheorem.
hyperreflexivity.
Qed.

Definition FractionCMonoidCannProj {A} (cm : #(CMonoid A)) (S : #(SubCMonoid cm)) : #(Map A (FractionCMonoidSet cm S)) :=
%CombineMap' [%CartesianDMap [IdMap ; %ConstMap (MIdent_of_CMonoid (Sub_to_CMonoid S))] ; to_FractionCMonoidSet cm S].

Theorem FractionCMonoidCannProjTheorem : forall {A} (cm : #(CMonoid A)) (S : #(SubCMonoid cm)) (a : #A),
%(FractionCMonoidCannProj cm S) a ==
%(to_FractionCMonoidSet cm S) [a;(MIdent_of_CMonoid (Sub_to_CMonoid S))].
Proof.
intros A cm S a.
unfold FractionCMonoidCannProj.
rewrite CombineMap'Theorem.
apply MapArgEq.
rewrite CartesianDMapTheorem.
apply EqualInPair'.
split.
 rewrite IdMapTheorem.
 hyperreflexivity.
rewrite ConstMapTheorem.
hyperreflexivity.
Qed.

Theorem FractionCMonoidCannProj_Hom : forall {A} (cm : #(CMonoid A)) (S : #(SubCMonoid cm)),
&&IsHomomorphism_of_BOpe [cm{<CMonoid_Ope};(FractionCMonoid cm S)] (FractionCMonoidCannProj cm S).
Proof.
intros.
apply IsHomomorphism_of_BOpeTheorem.
intros a b.
rewrite FractionCMonoidCannProjTheorem.
set (MIdent_of_CMonoid (Sub_to_CMonoid S)) as es.
apply (TransitivityEq (%(to_FractionCMonoidSet cm S) [%(cm{<CMonoid_Ope}) [a;b] ; %(SubCMonoid_to_Ope S) [es;es]])).
 apply MapArgEq.
 apply EqualInPair'R.
 apply SymmetryEq.
 apply IsLeftIdentTheorem.
 apply IsIdent_LeftIdent.
 generalize (MIdentTheorem ((Sub_to_CMonoid S){<CMonoid_Ident})).
 apply RelRewriteAll; hyperreflexivity.
rewrite <- FractionCMonoidTheorem.
apply MapArgEq.
apply EqualInPair'.
split.
 rewrite FractionCMonoidCannProjTheorem.
 apply MapArgEq.
 apply EqualInPair'R.
 hyperreflexivity.
rewrite FractionCMonoidCannProjTheorem.
apply MapArgEq.
apply EqualInPair'R.
hyperreflexivity.
Qed.

Theorem FractionCMonoidCannProj_IsIdent : forall {A} (cm : #(CMonoid A)) (S : #(SubCMonoid cm)) (e : #A),
&&IsIdent (cm{<CMonoid_Ope}) e -> 
&&IsIdent (FractionCMonoid cm S) (%(FractionCMonoidCannProj cm S) e).
Proof.
intros A cm S e IH.
apply IsIdentTheoremL.
 apply FractionCMonoid_Ope_CommCond.
intro ap.
put (FractionCMonoidSetIn _ _ ap) Eqap.
destruct Eqap as [a Eqap].
destruct Eqap as [p Eqap].
rewrite Eqap.
set (%(FractionCMonoidCannProj cm S) e) as e'.
assert(IneS : In e S).
 apply (SubIdenticalHasIdent (cm{<CMonoid_Ope})).
 apply IH.
set {e ! IneS} as es.
assert(IH' : &&IsIdent (SubCMonoid_to_Ope S) es).
 generalize IH.
 apply IsIdent_StrongCons.
 hyperreflexivity.
 apply (StrongSubBOpe _ _ (S{<SubCMonoid_SubOpe})).
 apply ReflexivityStrongRel.
assert(Eqe' : e' == (%(to_FractionCMonoidSet cm S) [e;es])).
 unfold e'.
 rewrite FractionCMonoidCannProjTheorem.
 apply MapArgEq.
 apply EqualInPair'R.
 unfold MIdent_of_CMonoid.
 apply MIdentEq.
 generalize IH'.
 apply RelRewriteL.
 hyperreflexivity.
rewrite (MapArgEq _ (EqualInPair'L _ _ _ _ _ Eqe')).
rewrite (MapArgEq _ (EqualInPair'R _ _ _ _ _ Eqap)).
rewrite FractionCMonoidTheorem.
apply MapArgEq.
apply EqualInPair'.
split.
 apply IsLeftIdentTheorem.
 apply IsIdent_LeftIdent.
 apply IH.
apply IsLeftIdentTheorem.
apply IsIdent_LeftIdent.
apply IH'.
Qed.

Theorem FractionCMonoid_Ope_IdentCond : forall {A} (cm : #(CMonoid A)) (S : #(SubCMonoid cm)),
Ope_IdentCond (FractionCMonoid cm S).
Proof.
intros A cm S.
unfold Ope_IdentCond.
set (MIdent_of_CMonoid cm) as e.
exists (%(FractionCMonoidCannProj cm S) e).
apply IsIdentTheoremL.
 apply FractionCMonoid_Ope_CommCond.
intro ap.
apply IsLeftIdentTheorem.
apply IsIdent_LeftIdent.
apply FractionCMonoidCannProj_IsIdent.
generalize (MIdentTheorem (cm{<CMonoid_Ident})).
apply RelRewriteAll; hyperreflexivity.
Qed.


Theorem FractionCMonoid_Ope_MonoidCond : forall {A} (cm : #(CMonoid A)) (S : #(SubCMonoid cm)),
Ope_MonoidCond (FractionCMonoid cm S).
Proof.
intros A cm S.
split.
apply FractionCMonoid_Ope_SGrpCond.
apply FractionCMonoid_Ope_IdentCond.
Qed.

Theorem FractionCMonoid_Ope_CMonoidCond : forall {A} (cm : #(CMonoid A)) (S : #(SubCMonoid cm)),
Ope_CMonoidCond (FractionCMonoid cm S).
Proof.
intros A cm S.
split.
apply FractionCMonoid_Ope_MonoidCond.
apply FractionCMonoid_Ope_CommCond.
Qed.


Theorem FractionCMonoidCannProj_IsInvertible : forall {A} (cm : #(CMonoid A)) (S : #(SubCMonoid cm)) (a : #A),
&&IsInvertible (cm{<CMonoid_Ope}) a -> 
&&IsInvertible (FractionCMonoid cm S) (%(FractionCMonoidCannProj cm S) a).
Proof.
intros A cm S a IH.
apply IsInvertibleTheorem in IH.
destruct IH as [Ia IH].
apply IsInverseETheorem in IH.
destruct IH as [IH1 IH2].
apply IsInvertibleTheorem.
exists (%(FractionCMonoidCannProj cm S) Ia).
apply (RelRewriteL' (FractionCMonoidCannProjTheorem _ _ _)).
apply (RelRewriteR' (FractionCMonoidCannProjTheorem _ _ _)).
apply IsInverseETheoremL.
 apply FractionCMonoid_Ope_CommCond.
set (MIdent_of_CMonoid (Sub_to_CMonoid S)) as e.
assert(IsIH : &&IsIdent (SubCMonoid_to_Ope S) e).
 generalize (MIdentTheorem ((Sub_to_CMonoid S){<CMonoid_Ident})).
 apply RelRewriteL.
 hyperreflexivity.
cut (&&IsIdent (FractionCMonoid cm S) (%(FractionCMonoidCannProj cm S) (%(cm{<CMonoid_Ope}) [a;Ia]))).
 apply RelRewriteR.
 rewrite FractionCMonoidTheorem.
 rewrite FractionCMonoidCannProjTheorem.
 apply MapArgEq.
 apply EqualInPair'R.
 apply SymmetryEq.
 apply IsLeftIdentTheorem.
 apply IsIdent_LeftIdent.
 apply IsIH.
apply FractionCMonoidCannProj_IsIdent.
apply IH1.
Qed.

Theorem FractionCMonoidCannProj_Hom_Ident : forall {A} (cm : #(CMonoid A)) (S : #(SubCMonoid cm)),
&&IsHomomorphism_of_Ident [cm{<CMonoid_Ope};(FractionCMonoid cm S)] (FractionCMonoidCannProj cm S).
Proof.
intros A cm S.
apply IsHomomorphism_of_IdentTheorem.
split.
 apply FractionCMonoidCannProj_Hom.
apply FractionCMonoidCannProj_IsIdent.
Qed.

Theorem FractionCMonoidCannProj_Hom_Invert : forall {A} (cm : #(CMonoid A)) (S : #(SubCMonoid cm)),
&&IsHomomorphism_of_Invert [cm{<CMonoid_Ope};(FractionCMonoid cm S)] (FractionCMonoidCannProj cm S).
Proof.
intros A cm S.
apply IsHomomorphism_of_InvertTheorem.
split.
 apply FractionCMonoidCannProj_Hom.
apply FractionCMonoidCannProj_IsInvertible.
Qed.

Theorem to_FractionCMonoidSetEq : forall {A} (cm : #(CMonoid A)) (S : #(SubCMonoid cm)) (a b : #A) (p q : #S),
%(to_FractionCMonoidSet cm S) [a;p] == %(to_FractionCMonoidSet cm S) [b;q] <->
exists s : #S, 
%(cm{<CMonoid_Ope}) [%(cm{<CMonoid_Ope}) [a;q{<SubCMonoid_S}] ; s{<SubCMonoid_S}] == 
%(cm{<CMonoid_Ope}) [%(cm{<CMonoid_Ope}) [b;p{<SubCMonoid_S}] ; s{<SubCMonoid_S}].
Proof.
intros.
unfold to_FractionCMonoidSet.
split.

intro HH.
assert(InPE : In [a;p] (%(EqCannProj (FractionCMonoidSet cm S)) [a;p])).
 apply EqCannProjOwnIn.
rewrite HH in InPE.
unfold FractionCMonoidSet in InPE.
apply EqCannProjTheorem in InPE.
assert (PH : &&(@ProductOfCMonoid_SubCMonoidERelationRel _ cm S) [b;q] [a;p]).
 generalize InPE.
 apply RelRewrite.
 apply (TransitivityEq (%Class_to_ERel (%ERel_to_Class (ProductOfCMonoid_SubCMonoidERelation cm S)))).
  hyperreflexivity.
 rewrite Class_to_ERel_to_Class.
 hyperreflexivity.
apply ProductOfCMonoid_SubCMonoidERelationRelTheorem in PH.
destruct PH as [s PH].
exists s.
apply SymmetryEq.
apply PH.

intro cond.
destruct cond as [s cond].
unfold FractionCMonoidSet.
apply ERel_to_ClassTheorem.
cut (&&(@ProductOfCMonoid_SubCMonoidERelationRel _ cm S) [a;p] [b;q]).
 apply RelRewrite.
 hyperreflexivity.
apply ProductOfCMonoid_SubCMonoidERelationRelTheorem.
exists s.
apply cond.
Qed.

Theorem to_FractionCMonoidSetEqSame : forall {A} (cm : #(CMonoid A)) (S : #(SubCMonoid cm)) (a b : #A) (p q : #S),
b == q ->
%(to_FractionCMonoidSet cm S) [a;p] == 
%(to_FractionCMonoidSet cm S) [%(cm{<CMonoid_Ope})[a;b] ; %(SubCMonoid_to_Ope S) [p;q]].
Proof.
intros A cm S a b p q Eqbq.
apply to_FractionCMonoidSetEq.
set (cm{<CMonoid_Ope}) as o.
set (SubCMonoid_to_Ope S) as so.
exists p.
apply MapArgEq.
apply EqualInPair'L.
assert(so_o : StrongRel (so{<Map_Rel}) (o{<Map_Rel})).
 apply (StrongSubBOpe _ _ (S{<SubCMonoid_SubOpe})).
 apply ReflexivitySubset2.
 hyperreflexivity.
set (p{<SubCMonoid_S}) as pA.
set (q{<SubCMonoid_S}) as qA.
assert(sgc : Ope_SGrpCond o).
 apply Ope_SGrp.
 apply CMonoid_SGrp.
 apply (SetProp cm).
assert(coc : Ope_CommCond o).
 apply Ope_Comm.
 apply CMonoid_Comm.
 apply (SetProp cm).
apply (TransitivityEq (%o[a;%o[pA;qA]])).
 apply MapArgEq.
 apply EqualInPair'R.
 rewrite (USETEq _ SubCMonoid_S).
 apply MapStrong.
 apply so_o.
 hyperreflexivity.
rewrite (MapArgEq _ (EqualInPair'R _ _ _ _ _ (coc _ _))).
rewrite <- sgc.
apply MapArgEq.
apply EqualInPair'L.
apply MapArgEq.
apply EqualInPair'R.
rewrite Eqbq.
hyperreflexivity.
Qed.


Theorem to_FractionCMonoidSet_Ident : forall {A} (cm : #(CMonoid A)) (S : #(SubCMonoid cm)) (s : #S),
&&IsIdent (FractionCMonoid cm S) (%(to_FractionCMonoidSet cm S) [s{<SubCMonoid_S};s]).
Proof.
intros A cm S s.
set (MIdent_of_CMonoid cm) as e.
assert(IsIdente : &&IsIdent (cm{<CMonoid_Ope}) e).
 generalize (MIdentTheorem (cm{<CMonoid_Ident})).
 apply RelRewriteAll; hyperreflexivity.
assert(IneS : In e S).
 apply (SubIdenticalHasIdent (cm{<CMonoid_Ope})).
 apply IsIdente.
set {e ! IneS} as es.

assert(EqIdent : (%(to_FractionCMonoidSet cm S) [s{<SubCMonoid_S};s]) == %(FractionCMonoidCannProj cm S) e).
 rewrite FractionCMonoidCannProjTheorem.
 apply to_FractionCMonoidSetEq.
 exists s.
 set (cm{<CMonoid_Ope}) as o.
 set (s{<SubCMonoid_S}) as sa.
 apply MapArgEq.
 apply EqualInPair'L.
 apply SymmetryEq.
 apply (TransitivityEq sa).
  apply IsLeftIdentTheorem.
  apply IsIdent_LeftIdent.
  apply IsIdente.
 apply SymmetryEq.
 apply IsRightIdentTheorem.
 apply IsIdent_RightIdent.
 generalize IsIdente.
 apply RelRewriteR.
 apply (TransitivityEq es).
 hyperreflexivity.
 rewrite (USETEq _ SubCMonoid_S).
 apply SymmetryEq.
 unfold MIdent_of_CMonoid.
 apply MIdentEq.
 generalize IsIdente.
 apply IsIdent_StrongCons.
  hyperreflexivity.
 apply (TransitivityStrongRel ((SubCMonoid_to_Ope S){<Map_Rel})).
  apply ReflexivityStrongRel2.
  hyperreflexivity.
 apply (StrongSubBOpe _ _ (S{<SubCMonoid_SubOpe})).
 apply ReflexivitySubset.
apply (RelRewriteR' EqIdent).
apply FractionCMonoidCannProj_IsIdent.
apply IsIdente.
Qed.

Theorem to_FractionCMonoidSet_Ident2 : forall {A} (cm : #(CMonoid A)) (S : #(SubCMonoid cm)) (a : #A) (s : #S),
a == s ->
&&IsIdent (FractionCMonoid cm S) (%(to_FractionCMonoidSet cm S) [a;s]).
Proof.
intros A cm S a s Eqas.
generalize (to_FractionCMonoidSet_Ident cm S s).
apply RelRewriteR.
apply MapArgEq.
apply EqualInPair'.
apply SymmetryAnd.
split.
hyperreflexivity.
rewrite Eqas.
hyperreflexivity.
Qed.

Theorem InversePairIsInverseE_FractionCMonoid : forall {A} (cm : #(CMonoid A)) (S : #(SubCMonoid cm)) (a b : #S),
&&
(%IsInverseE (FractionCMonoid cm S)) 
(%(to_FractionCMonoidSet cm S) [a{<SubCMonoid_S};b])
(%(to_FractionCMonoidSet cm S) [b{<SubCMonoid_S};a])
.
Proof.
intros A cm S a b.
apply IsInverseETheoremL.
 apply FractionCMonoid_Ope_CommCond.
apply (RelRewriteR' (FractionCMonoidTheorem _ _ _ _ _ _)).
apply to_FractionCMonoidSet_Ident2.
assert(com : Ope_CommCond (cm{<CMonoid_Ope})).
 apply Ope_Comm.
 apply CMonoid_Comm.
 apply (SetProp cm).
rewrite com.
apply SymmetryEq.
apply MapStrong.
 apply (StrongSubBOpe _ _ (S{<SubCMonoid_SubOpe})).
 apply ReflexivityStrongRel.
 hyperreflexivity.
Qed. 

Theorem InversePairIsInverseE_FractionCMonoid2 : forall {A} (cm : #(CMonoid A)) (S : #(SubCMonoid cm)) (a b : #A) (p q : #S),
a == q /\ b == p ->
&&
(%IsInverseE (FractionCMonoid cm S)) 
(%(to_FractionCMonoidSet cm S) [a;p])
(%(to_FractionCMonoidSet cm S) [b;q])
.
Proof.
intros A cm S a b p q EqD.
destruct EqD as [Eq1 Eq2].
assert(EqP1 : [a;p] == [q{<SubCMonoid_S};p]).
 apply EqualInPair'.
 split.
 rewrite Eq1.
 hyperreflexivity.
 hyperreflexivity.
assert(EqP2 : [b;q] == [p{<SubCMonoid_S};q]).
 apply EqualInPair'.
 split.
 rewrite Eq2.
 hyperreflexivity.
 hyperreflexivity.
apply (RelRewriteL' (MapArgEq _ EqP1)).
apply (RelRewriteR' (MapArgEq _ EqP2)).
apply InversePairIsInverseE_FractionCMonoid.
Qed.


Theorem FractionCMonoidCannProj_IsInverseS : forall {A} (cm : #(CMonoid A)) (S : #(SubCMonoid cm)) (a : #A),
In a S ->
&&IsInvertible (FractionCMonoid cm S) (%(FractionCMonoidCannProj cm S) a).
Proof.
intros A cm S a InaS.
apply IsInvertibleTheorem.
set {a ! InaS} as sa.
set (MIdent_of_CMonoid cm) as e.
exists (%(to_FractionCMonoidSet cm S) [e;sa]).
apply (RelRewriteL' (FractionCMonoidCannProjTheorem _ _ _)).
apply InversePairIsInverseE_FractionCMonoid2.
split.
hyperreflexivity.
assert(IsIe : &&IsIdent (cm{<CMonoid_Ope}) e).
 generalize (MIdentTheorem (cm{<CMonoid_Ident})).
 apply RelRewriteAll; hyperreflexivity.
assert(IneS : In e S).
 apply (SubIdenticalHasIdent (cm{<CMonoid_Ope})).
 apply IsIe.
apply (TransitivityEq {e!IneS}).
 hyperreflexivity.
apply SymmetryEq.
unfold MIdent_of_CMonoid.
apply MIdentEq.
generalize IsIe.
apply IsIdent_StrongCons.
 hyperreflexivity.
apply (StrongSubBOpe _ _ (S{<SubCMonoid_SubOpe})).
apply ReflexivityStrongRel.
Qed.

Theorem FractionCMonoidCannProj_is_Invertible : forall {A} (cm : #(CMonoid A)) (S : #(SubCMonoid cm)) (a : #A),
In a S ->
In (%(FractionCMonoidCannProj cm S) a) (%Invertible (FractionCMonoid cm S)).
Proof.
intros A cm S a InaS.
apply InvertibleTheorem.
apply FractionCMonoidCannProj_IsInverseS.
apply InaS.
Qed.

Theorem FractionCMonoidCannProjEq : forall {A} (cm : #(CMonoid A)) (S : #(SubCMonoid cm)) a b,
%(FractionCMonoidCannProj cm S) a == %(FractionCMonoidCannProj cm S) b <->
exists s : #S, %(cm{<CMonoid_Ope}) [a;s{<SubCMonoid_S}] == %(cm{<CMonoid_Ope}) [b;s{<SubCMonoid_S}].
Proof.
intros A cm S a b.
set (cm{<CMonoid_Ope}) as o.
set (MIdent_of_CMonoid ((Sub_to_CMonoid S))){<SubCMonoid_S} as e.
(* 以下はもっと簡単にできる可能性アリ *)
assert(IsIe : &&IsIdent o e).
 generalize (MIdentTheorem (cm{<CMonoid_Ident})).
 apply RelRewriteAll.
 hyperreflexivity.
  unfold e.
  unfold MIdent_of_CMonoid.
  rewrite (USETEq _ SubCMonoid_S).
  apply SymmetryEq.
  assert(InMS : In (%MIdent (cm{<CMonoid_Ident})) S).
   apply (SubIdenticalHasIdent o).
   unfold o.
   generalize (MIdentTheorem (cm{<CMonoid_Ident})).
   apply RelRewriteAll; hyperreflexivity.
  rewrite (DSETEq' _ InMS).   
  apply MIdentEq.
  generalize (MIdentTheorem (cm{<CMonoid_Ident})).
  apply IsIdent_StrongCons.
   hyperreflexivity.
  apply (StrongSubBOpe _ _ (S{<SubCMonoid_SubOpe})).
  apply ReflexivityStrongRel2.
  hyperreflexivity.
 hyperreflexivity.
 (*ここまで*)
split.

intro FH.
rewrite FractionCMonoidCannProjTheorem in FH.
rewrite FractionCMonoidCannProjTheorem in FH.
apply to_FractionCMonoidSetEq in FH.
destruct FH as [s FH].
exists s.
set (s{<SubCMonoid_S}) as sa.
assert(FH' : %o [%o[a;e];sa] == %o[%o[b;e];sa]).
 apply FH.
apply (TransitivityEq (%o [%o[a;e];sa])).
 apply MapArgEq.
 apply EqualInPair'L.
 apply SymmetryEq.
 apply IsRightIdentTheorem.
 apply IsIdent_RightIdent.
 apply IsIe.
rewrite FH'.
apply MapArgEq.
apply EqualInPair'L.
apply IsRightIdentTheorem.
apply IsIdent_RightIdent.
apply IsIe.


intro cond.
destruct cond as [s cond].
rewrite FractionCMonoidCannProjTheorem.
rewrite FractionCMonoidCannProjTheorem.
apply to_FractionCMonoidSetEq.
exists s.
set (s{<SubCMonoid_S}) as sa.
apply (TransitivityEq (%o [%o [a;e];sa])).
 hyperreflexivity.
apply (TransitivityEq (%o [a;sa])).
 apply MapArgEq.
 apply EqualInPair'L.
 apply IsRightIdentTheorem.
 apply IsIdent_RightIdent.
 apply IsIe.
apply (TransitivityEq (%o [b;sa])).
 apply cond.
apply (TransitivityEq (%o [%o [b;e];sa])).
 apply MapArgEq.
 apply EqualInPair'L.
 apply SymmetryEq.
 apply IsRightIdentTheorem.
 apply IsIdent_RightIdent.
 apply IsIe.
hyperreflexivity.
Qed.

Theorem to_FractionCMonoid_in_CannProj : forall {A} (cm : #(CMonoid A)) (S : #(SubCMonoid cm)) (a : #A) (p : #S),
forall ICp, &&(%IsInverseE (FractionCMonoid cm S)) (%(FractionCMonoidCannProj cm S) (p{<SubCMonoid_S})) ICp ->
%(to_FractionCMonoidSet cm S) [a;p] ==
%(FractionCMonoid cm S) [%(FractionCMonoidCannProj cm S) a ; ICp].
Proof.
intros A cm S a p ICp IsICp.
set (%MIdent (cm{<CMonoid_Ident})) as e.
assert(IsIe : &&IsIdent (cm{<CMonoid_Ope}) e).
 generalize (MIdentTheorem (cm{<CMonoid_Ident})).
 apply RelRewriteAll; hyperreflexivity.
assert(IneS : In e S).
 apply (SubIdenticalHasIdent (cm{<CMonoid_Ope})).
 apply IsIe.
set {e ! IneS} as es.
assert(IsIes : &&IsIdent (SubCMonoid_to_Ope S) es).
 generalize IsIe.
 apply IsIdent_StrongCons.
 hyperreflexivity.
 apply (StrongSubBOpe _ _ (S{<SubCMonoid_SubOpe})).
 apply ReflexivityStrongRel.
apply (TransitivityEq (%(to_FractionCMonoidSet cm S) (%(ProductOfCMonoid_SubCMonoid cm S) [[a;es] ; [e;p]]))).
 apply MapArgEq.
 apply SymmetryEq.
 unfold ProductOfCMonoid_SubCMonoid.
 rewrite ProductOperationTheorem.
 apply EqualInPair'.
 split.
  apply IsRightIdentTheorem.
  apply IsIdent_RightIdent.
  apply IsIe.
 apply IsLeftIdentTheorem.
 apply IsIdent_LeftIdent.
 apply IsIes.
put (FractionCMonoidProduct_Hom cm S) HH.
put ((proj1 (IsHomomorphism_of_BOpeTheorem _ _ _)) HH) HH'.
rewrite HH'.
apply MapArgEq.
apply EqualInPair'.
split.
 rewrite FractionCMonoidCannProjTheorem.
 apply MapArgEq.
 apply EqualInPair'R.
 apply SymmetryEq.
 unfold MIdent_of_CMonoid.
 apply MIdentEq.
 apply IsIes.
 apply (RightUniqueEq (%IsInverseE (FractionCMonoid cm S)) (%(FractionCMonoidCannProj cm S) (p{<SubCMonoid_S}))).
 apply IsInverseE_SGrpCond_RUnqCond.
 apply FractionCMonoid_Ope_SGrpCond.
 apply (RelRewriteL' (FractionCMonoidCannProjTheorem _ _ _)).
 apply (InversePairIsInverseE_FractionCMonoid2 cm S).
 split.
 hyperreflexivity.
 apply (TransitivityEq es).
 hyperreflexivity.
 apply SymmetryEq.
 unfold MIdent_of_CMonoid.
 apply MIdentEq.
 apply IsIes.
apply IsICp.
Qed.


(* representation of FractionCMonoid *)
Definition RepresentOfFractionCMonoidableSet {A B} (MA : #(CMonoid A)) (MB : #(Monoid B)) (S : #(SubCMonoid MA)) := SSet'
(%Homomorphism_of_BOpe [MA{<CMonoid_Ope} ; MB{<Monoid_Ope}])
(fun f => forall (s : #A), In s S -> &&IsInvertible (MB{<Monoid_Ope}) (%(f{<HomBOpe_Map}) s)).

Theorem RepresentOfFractionCMonoidableSetTheorem : forall {A B} (MA : #(CMonoid A)) (MB : #(Monoid B)) (S : #(SubCMonoid MA)) (f : #(Map A B)),
In f (RepresentOfFractionCMonoidableSet MA MB S) <->
(&&IsHomomorphism_of_BOpe [MA{<CMonoid_Ope};MB{<Monoid_Ope}] f /\ forall s : #A, In s S -> &&IsInvertible (MB{<Monoid_Ope}) (%f s)).
Proof.
intros A B MA MB S f.
split.
 intro InfR.
 apply SSet'Theorem in InfR.
 destruct InfR as [IsHomf cond].
 split.
  apply Homomorphism_of_BOpeTheorem in IsHomf.
  apply IsHomf.
 intros s InsS.
 put (cond IsHomf _ InsS) cond'.
 generalize cond'.
 apply RelRewriteR.
 hyperreflexivity.
intro cond.
destruct cond as [H1 H2].
apply SSet'Theorem.
split.
 apply Homomorphism_of_BOpeTheorem.
 apply H1.
intros InfH s InsS.
generalize (H2 _ InsS).
apply RelRewriteR.
hyperreflexivity.
Qed.

Theorem RepresentOfFCM_Map : forall {A B} {MA : #(CMonoid A)} {MB : #(Monoid B)} {S : #(SubCMonoid MA)},
Subset (RepresentOfFractionCMonoidableSet MA MB S) (Map A B).
Proof.
intros A B MA MB S.
apply (TransitivitySubset (%Homomorphism_of_BOpe [MA{<CMonoid_Ope} ; MB{<Monoid_Ope}])).
 apply SSet'Subset.
apply HomBOpe_Map.
Qed.

Definition PreRepresentOfFractionCMonoidRel {A B} (MA : #(CMonoid A)) (MB : #(Monoid B)) (S : #(SubCMonoid MA)) (f : #(RepresentOfFractionCMonoidableSet MA MB S)) :=
MakeRelation (fun (x : #(FractionCMonoidSet MA S)) (b : #B) => forall (a : #A) (p : #S),
  %(to_FractionCMonoidSet MA S) [a;p] == x -> forall fpI, &&(%IsInverseE (MB{<Monoid_Ope})) (%(f{<RepresentOfFCM_Map}) (p{<SubCMonoid_S})) fpI -> b == %(MB{<Monoid_Ope}) [%(f{<RepresentOfFCM_Map}) a ; fpI]
).

Theorem PreRepresentOfFractionCMonoidRel_MapCond : forall {A B} (MA : #(CMonoid A)) (MB : #(Monoid B)) (S : #(SubCMonoid MA)) (f : #(RepresentOfFractionCMonoidableSet MA MB S)),
Rel_MapCond (PreRepresentOfFractionCMonoidRel MA MB S f).
Proof.
intros A B MA MB S fR.
set (PreRepresentOfFractionCMonoidRel MA MB S fR) as frel.
set (MB{<Monoid_Ope}) as ob.
set (MA{<CMonoid_Ope}) as oa.
set (fR{<RepresentOfFCM_Map}) as ff.
assert(AssB : Ope_SGrpCond ob).
 apply Ope_SGrp.
 apply Monoid_SGrp.
 apply (SetProp MB).
assert(CommA : Ope_CommCond oa).
 apply Ope_Comm.
 apply CMonoid_Comm.
 apply (SetProp MA).
assert(InRepff : (In ff (RepresentOfFractionCMonoidableSet MA MB S))).
 apply (SetProp fR).
apply RepresentOfFractionCMonoidableSetTheorem in InRepff.
destruct InRepff as [IsHomff ffCond].
fold oa in IsHomff.
fold ob in IsHomff.
put ((proj1 (IsHomomorphism_of_BOpeTheorem _ _ _)) IsHomff) Commff.
fold ob in Commff.
fold oa in Commff.

intro ap.
put (FractionCMonoidSetIn _ _ ap) Eqap.
destruct Eqap as [a Eqap].
destruct Eqap as [p Eqap].
set (p{<SubCMonoid_S}) as pA.
split.

(*Existence*)
put (ffCond pA (SetProp p)) IsInvp.
apply IsInvertibleTheorem in IsInvp.
destruct IsInvp as [Invfp IsInvp].
exists (%ob [%ff a ; Invfp]).
apply (RelRewriteL' Eqap).
apply MakeRelationTheorem.
intros ap' b' Eqap' Eqb a' p' Eqapap' fpI' InvH.
set (p'{<SubCMonoid_S}) as pA'.
fold ff.
rewrite <- Eqb.
fold ob.
cut (%ob [Invfp ; %ff a] == %ob [%ff a' ; fpI']).
 intro EqH.
 rewrite <- EqH.
 apply SymmetryEq.
 generalize IsInvp.
 apply (IfCommThenIsInverseComm _ _ _ AssB).
 rewrite <- Commff.
 rewrite (MapArgEq _ (CommA _ _)).
 apply Commff.
cut (%ff a == %ob [%ob [%ff pA ; %ff a'] ; fpI']).
 intro EqH.
 rewrite (MapArgEq _ (EqualInPair'R _ _ _ _ _ EqH)).
 rewrite <- AssB.
 apply MapArgEq.
 apply EqualInPair'L.
 rewrite <- AssB.
 apply IsLeftIdentTheorem.
 apply IsIdent_LeftIdent.
 apply IsInverseETheorem in IsInvp.
 apply (proj2 IsInvp).
cut (%ob [%ff a; %ff pA'] == %ob [%ff pA ; %ff a']).
 intro EqH.
 rewrite <- (MapArgEq _ (EqualInPair'L _ _ _ _ _ EqH)).
 apply SymmetryEq.
 rewrite AssB.
 apply IsRightIdentTheorem.
 apply IsIdent_RightIdent.
 apply IsInverseETheorem in InvH.
 apply (proj1 InvH).
assert(Eqapap : %(to_FractionCMonoidSet MA S) [a;p] == %(to_FractionCMonoidSet MA S) [a';p']).
 rewrite Eqap'.
 rewrite Eqapap'.
 hyperreflexivity.
apply to_FractionCMonoidSetEq in Eqapap.
destruct Eqapap as [s Eqapap].
set (s{<SubCMonoid_S}) as sA.
fold oa in Eqapap.
fold pA' in Eqapap.
fold pA in Eqapap.
fold sA in Eqapap.
rewrite <- Commff.
put (ffCond sA (SetProp s)) Invs.
apply IsInvertibleTheorem in Invs.
destruct Invs as [Invfs Invs].
apply (TransitivityEq (%ob [%ff (%oa [a;pA']) ; %ob [%ff sA ; Invfs]])).
 apply SymmetryEq.
 apply IsRightIdentTheorem.
 apply IsIdent_RightIdent.
 apply IsInverseETheorem in Invs.
 apply (proj1 Invs).
rewrite  <- AssB.
rewrite <- (MapArgEq _ (EqualInPair'L _ _ _ _ _ (Commff _ _))).
rewrite (MapArgEq _ (EqualInPair'L _ _ _ _ _ (MapArgEq _ Eqapap))).
rewrite (MapArgEq _ (EqualInPair'L _ _ _ _ _ (Commff _ _))).
rewrite AssB.
apply (TransitivityEq (%ff (%oa [a' ; pA]))).
 apply IsRightIdentTheorem.
 apply IsIdent_RightIdent.
 apply IsInverseETheorem in Invs.
 apply (proj1 Invs).
apply SymmetryEq.
rewrite <- Commff.
apply MapArgEq.
apply CommA.


(*Uniqueness*)
intros b1 b2 HD.
destruct HD as [H1 H2].
put (ffCond pA (SetProp p)) IsInvp.
apply IsInvertibleTheorem in IsInvp.
destruct IsInvp as [Invfp IsInvp].
put ((proj1 (MakeRelationTheorem _ _ _ _ _)) H1) H1'.
apply SymmetryEq in Eqap.
clear H1.
put (H1' _ _ (ReflexivityEq _) (ReflexivityEq _) _ _ Eqap _ IsInvp) H1.
clear H1'.
apply SymmetryEq in Eqap.
put ((proj1 (MakeRelationTheorem _ _ _ _ _)) H2) H2'.
apply SymmetryEq in Eqap.
clear H2.
put (H2' _ _ (ReflexivityEq _) (ReflexivityEq _) _ _ Eqap _ IsInvp) H2.
clear H2'.
rewrite H1.
rewrite H2.
hyperreflexivity.
Qed.

Definition PreRepresentOfFractionCMonoid {A B} (MA : #(CMonoid A)) (MB : #(Monoid B)) (S : #(SubCMonoid MA)) (f : #(RepresentOfFractionCMonoidableSet MA MB S)) :=
_{<Rel_Map ! PreRepresentOfFractionCMonoidRel_MapCond MA MB S f}.

Theorem PreRepresentOfFractionCMonoidTheorem : forall {A B} (MA : #(CMonoid A)) (MB : #(Monoid B)) (S : #(SubCMonoid MA)) (f : #(RepresentOfFractionCMonoidableSet MA MB S))
a p Ifp,
&&(%IsInverseE (MB{<Monoid_Ope})) (%(f{<RepresentOfFCM_Map}) (p{<SubCMonoid_S})) Ifp ->
%(PreRepresentOfFractionCMonoid MA MB S f) (%(to_FractionCMonoidSet MA S) [a;p]) ==
%(MB{<Monoid_Ope}) [%(f{<RepresentOfFCM_Map}) a ; Ifp].
Proof.
intros A B MA MB S f a p Ifp Invfp.
set (MA{<CMonoid_Ope}) as oa.
set (MB{<Monoid_Ope}) as ob.
set (f{<RepresentOfFCM_Map}) as ff.
assert(AssB : Ope_SGrpCond ob).
 apply Ope_SGrp.
 apply Monoid_SGrp.
 apply (SetProp MB).
assert(CommA : Ope_CommCond oa).
 apply Ope_Comm.
 apply CMonoid_Comm.
 apply (SetProp MA).
assert(InRepff : (In ff (RepresentOfFractionCMonoidableSet MA MB S))).
 apply (SetProp f).
apply RepresentOfFractionCMonoidableSetTheorem in InRepff.
destruct InRepff as [IsHomff ffCond].
fold oa in IsHomff.
fold ob in IsHomff.
put ((proj1 (IsHomomorphism_of_BOpeTheorem _ _ _)) IsHomff) Commff.
fold ob in Commff.
fold oa in Commff.

apply AppTheoremReverse.
cut (&&(PreRepresentOfFractionCMonoidRel MA MB S f) (%(to_FractionCMonoidSet MA S) [a;p]) (%(MB{<Monoid_Ope}) [%(f{<RepresentOfFCM_Map}) a ; Ifp])).
 apply RelRewrite.
 hyperreflexivity.
apply MakeRelationTheorem.
intros ap' ob' Eqap Eqob a' p' Eqap' fpI InvH.
set (p{<SubCMonoid_S}) as pA.
set (p'{<SubCMonoid_S}) as pA'.
rewrite <- Eqob.
fold ob.
fold ff.
cut (%ob [Ifp ; %ff a] == %ob [%ff a' ; fpI]).
 intro EqH.
 rewrite <- EqH.
 apply SymmetryEq.
 generalize Invfp.
 apply (IfCommThenIsInverseComm _ _ _ AssB).
 rewrite <- Commff.
 rewrite (MapArgEq _ (CommA _ _)).
 apply Commff.
cut (%ff a == %ob [%ob [%ff pA ; %ff a'] ; fpI]).
 intro EqH.
 rewrite (MapArgEq _ (EqualInPair'R _ _ _ _ _ EqH)).
 rewrite <- AssB.
 apply MapArgEq.
 apply EqualInPair'L.
 rewrite <- AssB.
 apply IsLeftIdentTheorem.
 apply IsIdent_LeftIdent.
 apply IsInverseETheorem in Invfp.
 apply (proj2 Invfp).
cut (%ob [%ff a; %ff pA'] == %ob [%ff pA ; %ff a']).
 intro EqH.
 rewrite <- (MapArgEq _ (EqualInPair'L _ _ _ _ _ EqH)).
 apply SymmetryEq.
 rewrite AssB.
 apply IsRightIdentTheorem.
 apply IsIdent_RightIdent.
 apply IsInverseETheorem in InvH.
 apply (proj1 InvH).
assert(Eqapap : %(to_FractionCMonoidSet MA S) [a;p] == %(to_FractionCMonoidSet MA S) [a';p']).
 rewrite Eqap'.
 rewrite Eqap.
 hyperreflexivity.
apply to_FractionCMonoidSetEq in Eqapap.
destruct Eqapap as [s Eqapap].
set (s{<SubCMonoid_S}) as sA.
fold oa in Eqapap.
fold pA' in Eqapap.
fold pA in Eqapap.
fold sA in Eqapap.
rewrite <- Commff.
put (ffCond sA (SetProp s)) Invs.
apply IsInvertibleTheorem in Invs.
destruct Invs as [Invfs Invs].
apply (TransitivityEq (%ob [%ff (%oa [a;pA']) ; %ob [%ff sA ; Invfs]])).
 apply SymmetryEq.
 apply IsRightIdentTheorem.
 apply IsIdent_RightIdent.
 apply IsInverseETheorem in Invs.
 apply (proj1 Invs).
rewrite  <- AssB.
rewrite <- (MapArgEq _ (EqualInPair'L _ _ _ _ _ (Commff _ _))).
rewrite (MapArgEq _ (EqualInPair'L _ _ _ _ _ (MapArgEq _ Eqapap))).
rewrite (MapArgEq _ (EqualInPair'L _ _ _ _ _ (Commff _ _))).
rewrite AssB.
apply (TransitivityEq (%ff (%oa [a' ; pA]))).
 apply IsRightIdentTheorem.
 apply IsIdent_RightIdent.
 apply IsInverseETheorem in Invs.
 apply (proj1 Invs).
apply SymmetryEq.
rewrite <- Commff.
apply MapArgEq.
apply CommA.
Qed.

Theorem RFunPreRepresentOfFractionCMonoid : forall {A B} (MA : #(CMonoid A)) (MB : #(Monoid B)) (S : #(SubCMonoid MA)),
RFun (fun f => PreRepresentOfFractionCMonoid MA MB S f).
Proof.
intros A B MA MB S.
intros f1 f2 Eqf.
apply MapEquality.
 hyperreflexivity.
intros ap bq Eqapbq.
set (MA{<CMonoid_Ope}) as oa.
set (MB{<Monoid_Ope}) as ob.
set (f1{<RepresentOfFCM_Map}) as ff1.
set (f2{<RepresentOfFCM_Map}) as ff2.
put (FractionCMonoidSetIn _ _ ap) Eqap.
destruct Eqap as [a Eqap].
destruct Eqap as [p Eqap].
set (p{<SubCMonoid_S}) as pA.
put (FractionCMonoidSetIn _ _ bq) Eqbq.
destruct Eqbq as [b Eqbq].
destruct Eqbq as [q Eqbq].
set (q{<SubCMonoid_S}) as qA.
assert(Invfp : &&IsInvertible ob (%(f1{<RepresentOfFCM_Map}) pA)).
 assert(InfR1 : In ff1 (RepresentOfFractionCMonoidableSet MA MB S)).
  apply (SetProp f1).
 apply RepresentOfFractionCMonoidableSetTheorem in InfR1.
 destruct InfR1 as [_ InfR1].
 apply InfR1.
 apply (SetProp p).
apply IsInvertibleTheorem in Invfp.
destruct Invfp as [Ifp Invfp].
assert(Invfq : &&IsInvertible ob (%(f2{<RepresentOfFCM_Map}) qA)).
 assert(InfR2 : In ff2 (RepresentOfFractionCMonoidableSet MA MB S)).
  apply (SetProp f2).
 apply RepresentOfFractionCMonoidableSetTheorem in InfR2.
 destruct InfR2 as [_ InfR2].
 apply InfR2.
 apply (SetProp q).
apply IsInvertibleTheorem in Invfq.
destruct Invfq as [Ifq Invfq].
rewrite (MapArgEq _ Eqap).
rewrite (MapArgEq _ Eqbq).
rewrite (PreRepresentOfFractionCMonoidTheorem _ _ _ _ _ _ _ Invfp).
rewrite (PreRepresentOfFractionCMonoidTheorem _ _ _ _ _ _ _ Invfq).
fold ob.
fold ff1.
apply (TransitivityEq (%ob [%ff1 b ; Ifq])).
assert(AssB : Ope_SGrpCond ob).
 apply Ope_SGrp.
 apply Monoid_SGrp.
 apply (SetProp MB).
assert(CommA : Ope_CommCond oa).
 apply Ope_Comm.
 apply CMonoid_Comm.
 apply (SetProp MA).
assert(InRepff : (In ff1 (RepresentOfFractionCMonoidableSet MA MB S))).
 apply (SetProp f1).
apply RepresentOfFractionCMonoidableSetTheorem in InRepff.
destruct InRepff as [IsHomff ffCond].
fold oa in IsHomff.
fold ob in IsHomff.
put ((proj1 (IsHomomorphism_of_BOpeTheorem _ _ _)) IsHomff) Commff.
fold ob in Commff.
fold oa in Commff.
cut (%ob [Ifp ; %ff1 a] == %ob [%ff1 b ; Ifq]).
 intro EqH.
 rewrite <- EqH.
 apply SymmetryEq.
 generalize Invfp.
 apply (IfCommThenIsInverseComm _ _ _ AssB).
 rewrite <- Commff.
 rewrite (MapArgEq _ (CommA _ _)).
 apply Commff.
cut (%ff1 a == %ob [%ob [%ff1 pA ; %ff1 b] ; Ifq]).
 intro EqH.
 rewrite (MapArgEq _ (EqualInPair'R _ _ _ _ _ EqH)).
 rewrite <- AssB.
 apply MapArgEq.
 apply EqualInPair'L.
 rewrite <- AssB.
 apply IsLeftIdentTheorem.
 apply IsIdent_LeftIdent.
 apply IsInverseETheorem in Invfp.
 apply (proj2 Invfp).
cut (%ob [%ff1 a; %ff1 qA] == %ob [%ff1 pA ; %ff1 b]).
 intro EqH.
 rewrite <- (MapArgEq _ (EqualInPair'L _ _ _ _ _ EqH)).
 apply SymmetryEq.
 rewrite AssB.
 apply IsRightIdentTheorem.
 apply IsIdent_RightIdent.
 apply IsInverseETheorem in Invfq.
 cut (&&IsIdent ob (%ob [%ff2 qA ; Ifq])).
  apply RelRewriteR.
  apply MapArgEq.
  apply EqualInPair'L.
  apply MapEq.
  apply SymmetryEq.
  apply Eqf.
 apply (proj1 Invfq).
assert(Eqapap : %(to_FractionCMonoidSet MA S) [a;p] == %(to_FractionCMonoidSet MA S) [b;q]).
 rewrite <- Eqap.
 rewrite <- Eqbq.
 apply Eqapbq.
apply to_FractionCMonoidSetEq in Eqapap.
destruct Eqapap as [s Eqapap].
set (s{<SubCMonoid_S}) as sA.
rewrite <- Commff.
put (ffCond sA (SetProp s)) Invs.
apply IsInvertibleTheorem in Invs.
destruct Invs as [Invfs Invs].
apply (TransitivityEq (%ob [%ff1 (%oa [a;qA]) ; %ob [%ff1 sA ; Invfs]])).
 apply SymmetryEq.
 apply IsRightIdentTheorem.
 apply IsIdent_RightIdent.
 apply IsInverseETheorem in Invs.
 apply (proj1 Invs).
rewrite  <- AssB.
rewrite <- (MapArgEq _ (EqualInPair'L _ _ _ _ _ (Commff _ _))).
rewrite (MapArgEq _ (EqualInPair'L _ _ _ _ _ (MapArgEq _ Eqapap))).
rewrite (MapArgEq _ (EqualInPair'L _ _ _ _ _ (Commff _ _))).
rewrite AssB.
apply (TransitivityEq (%ff1 (%oa [b ; pA]))).
 apply IsRightIdentTheorem.
 apply IsIdent_RightIdent.
 apply IsInverseETheorem in Invs.
 apply (proj1 Invs).
apply SymmetryEq.
rewrite <- Commff.
apply MapArgEq.
apply CommA.

apply MapArgEq.
apply EqualInPair'L.
apply MapEq.
apply Eqf.
Qed.

Definition RepresentOfFractionCMonoid {A B} (MA : #(CMonoid A)) (MB : #(Monoid B)) (S : #(SubCMonoid MA)) : #(Map (RepresentOfFractionCMonoidableSet MA MB S) (Map (FractionCMonoidSet MA S) B)) :=
MakeMap _ _ _ (RFunPreRepresentOfFractionCMonoid MA MB S).

Theorem RepresentOfFractionCMonoidTheorem : forall {A B} (MA : #(CMonoid A)) (MB : #(Monoid B)) (S : #(SubCMonoid MA)) (f : #(RepresentOfFractionCMonoidableSet MA MB S))
a p Ifp,
&&(%IsInverseE (MB{<Monoid_Ope})) (%(f{<RepresentOfFCM_Map}) (p{<SubCMonoid_S})) Ifp ->
%(%(RepresentOfFractionCMonoid MA MB S) f) (%(to_FractionCMonoidSet MA S) [a;p]) ==
%(MB{<Monoid_Ope}) [%(f{<RepresentOfFCM_Map}) a ; Ifp].
Proof.
intros A B MA MB S f a p Ifp Invfp.
unfold RepresentOfFractionCMonoid.
rewrite (MapEq (MakeMapTheorem _ _ _ _ _)).
apply PreRepresentOfFractionCMonoidTheorem.
apply Invfp.
Qed.

Theorem RepresentOfFractionCMonoidTheoremWP : forall {A B} (MA : #(CMonoid A)) (MB : #(Monoid B)) (S : #(SubCMonoid MA)) (f : #(Map A B)) (cond : In f (RepresentOfFractionCMonoidableSet MA MB S))
a p Ifp,
&&(%IsInverseE (MB{<Monoid_Ope})) (%f (p{<SubCMonoid_S})) Ifp ->
%(%(RepresentOfFractionCMonoid MA MB S) {f ! cond}) (%(to_FractionCMonoidSet MA S) [a;p]) ==
%(MB{<Monoid_Ope}) [%f a ; Ifp].
Proof.
intros A B MA MB S f cond a p Ifp Invfp.
apply (TransitivityEq (%(MB{<Monoid_Ope}) [%({f!cond}{<RepresentOfFCM_Map}) a ; Ifp])).
 apply RepresentOfFractionCMonoidTheorem.
 generalize Invfp.
 apply RelRewriteL.
 hyperreflexivity.
hyperreflexivity.
Qed.




Theorem RepresentOfFractionCMonoidEq : forall {A B} (MA : #(CMonoid A)) (MB : #(Monoid B)) (S : #(SubCMonoid MA)) (fR : #(RepresentOfFractionCMonoidableSet MA MB S)),
fR == %CombineMap' [FractionCMonoidCannProj MA S ; %(RepresentOfFractionCMonoid MA MB S) fR].
Proof.
intros A B MA MB S fR.
set (fR{<RepresentOfFCM_Map}) as f.
apply (TransitivityEq f).
hyperreflexivity. 
apply MapEquality.
hyperreflexivity.
intros a1 a2 Eqa.
apply SymmetryEq.
rewrite <- (MapArgEq _ Eqa).
rewrite CombineMap'Theorem.
rewrite (MapArgEq _ (FractionCMonoidCannProjTheorem _ _ _)).
apply (TransitivityEq (%(MB{<Monoid_Ope}) [%f a1 ; MIdent_of_Monoid MB])).
 apply RepresentOfFractionCMonoidTheorem.
 cut (&&(%IsInverseE (MB{<Monoid_Ope})) (MIdent_of_Monoid MB) (MIdent_of_Monoid MB)).
  apply RelRewriteL.
  unfold MIdent_of_Monoid.
  apply MIdentEq.
  cut (&&IsIdent (MB{<Monoid_Ope}) (%f (MIdent_of_CMonoid MA))).
   apply RelRewriteAll.
    hyperreflexivity.
    apply MapArgEq.
    rewrite USETEq.
    unfold MIdent_of_CMonoid.
    unfold SubCMonoid in S.
    assert(InSSI : In S (%SubIdentical (MA{<CMonoid_Ident}{<Ident_Ope}))).
     cut (In S (%SubIdentical (MA{<CMonoid_Ope}))).
      apply Arrow2Rewrite; hyperreflexivity.
     apply (SetProp S).
    rewrite (MIdent_eq_SubIdent _ {S ! InSSI}).
    apply MapArgEq.
    rewrite USETEq.
    unfold Sub_to_Identical.
    unfold Sub_to_CMonoid.
    rewrite DSETEq.
    apply SymmetryEq.
    rewrite DSETEq.
    unfold SubCMonoid_to_Ope.
    unfold SubIdent_to_Ope.
    hyperreflexivity.
   hyperreflexivity.
  assert(InfR : In f (RepresentOfFractionCMonoidableSet MA MB S)).
   apply (SetProp fR).
  apply RepresentOfFractionCMonoidableSetTheorem in InfR.
  apply (Hom_Invert_Ident_inSGrp (MA{<CMonoid_Ope})).
     apply Ope_SGrp.
     apply Monoid_SGrp.
     apply (SetProp MB).
    apply (proj1 InfR).
   apply (proj2 InfR).
   apply (SubIdenticalHasIdent (MA{<CMonoid_Ope})).
   generalize (MIdentTheorem (MA{<CMonoid_Ident})).
   apply RelRewriteAll; hyperreflexivity.
  generalize (MIdentTheorem (MA{<CMonoid_Ident})).
  apply RelRewriteAll; hyperreflexivity.
 apply IsInverseE_DoubleIsIdent.
 generalize (MIdentTheorem (MB{<Monoid_Ident})).
 apply RelRewriteAll; hyperreflexivity.
apply IsRightIdentTheorem.
apply IsIdent_RightIdent.
generalize (MIdentTheorem (MB{<Monoid_Ident})).
apply RelRewriteAll; hyperreflexivity.
Qed.


Theorem RepresentOfFractionCMonoid_HomBOpe : forall {A B} (MA : #(CMonoid A)) (MB : #(Monoid B)) (S : #(SubCMonoid MA)) (fR : #(RepresentOfFractionCMonoidableSet MA MB S)),
&&IsHomomorphism_of_BOpe [FractionCMonoid MA S;MB{<Monoid_Ope}] (%(RepresentOfFractionCMonoid MA MB S) fR).
Proof.
intros A B MA MB S fR.
set (MA{<CMonoid_Ope}) as oa.
set (MB{<Monoid_Ope}) as ob.
set (fR{<RepresentOfFCM_Map}) as f.
apply IsHomomorphism_of_BOpeTheorem.
intros ap bq.
put (FractionCMonoidSetIn _ _ ap) Eqap.
destruct Eqap as [a Eqap].
destruct Eqap as [p Eqap].
set (p{<SubCMonoid_S}) as pA.
put (FractionCMonoidSetIn _ _ bq) Eqbq.
destruct Eqbq as [b Eqbq].
destruct Eqbq as [q Eqbq].
set (q{<SubCMonoid_S}) as qA.
rewrite (MapArgEq _ (MapArgEq _ (EqualInPair'L _ _ _ _ _ Eqap))).
rewrite (MapArgEq _ (MapArgEq _ (EqualInPair'R _ _ _ _ _ Eqbq))).
rewrite (MapArgEq _ (FractionCMonoidTheorem _ _ _ _ _ _)).
fold oa.
assert( EqSM : %(SubCMonoid_to_Ope S) [p;q] == %oa [pA;qA]).
 apply MapStrong.
 unfold SubCMonoid_to_Ope.
 apply (StrongSubBOpe _ _ (S{<SubCMonoid_SubOpe})).
 apply ReflexivityStrongRel2.
 hyperreflexivity.
 hyperreflexivity.
assert(Inpq : In (%oa [pA;qA]) S).
 put (SetProp S) InSSI.
 assert(SubSP : In S (PowerSet A)).
  apply SubIdenticalSubset in InSSI.
  apply InSSI.
 rewrite (DSETEq' _ SubSP) in InSSI.
 apply SubIdenticalTheorem in InSSI.
 apply IsSubIdenticalTheorem in InSSI.
 destruct InSSI as [IsSubB _].
 put ((proj1 (IsSubBOperationTheorem _ _)) IsSubB) IsSubB'.
 apply IsSubB'.
 apply (SetProp p).
 apply (SetProp q).
assert(InfR : In f (RepresentOfFractionCMonoidableSet MA MB S)).
 apply (SetProp fR).
apply RepresentOfFractionCMonoidableSetTheorem in InfR.
destruct InfR as [HomH InvH].
apply InvH in Inpq.
apply IsInvertibleTheorem in Inpq.
destruct Inpq as [Invfpq InvfpqH].
fold ob in InvfpqH.
apply (TransitivityEq (%ob [%f (%oa[a;b]) ; Invfpq])).
 apply RepresentOfFractionCMonoidTheorem.
 generalize InvfpqH.
 apply RelRewriteAll.
  apply MapArgEq.
  apply SymmetryEq.
  apply EqSM.
 hyperreflexivity.
 hyperreflexivity.
apply SymmetryEq.
rewrite (MapArgEq _ (EqualInPair'L _ _ _ _ _ (MapArgEq _ Eqap))).
rewrite (MapArgEq _ (EqualInPair'R _ _ _ _ _ (MapArgEq _ Eqbq))).
put (InvH pA (SetProp p)) InvfpH.
apply IsInvertibleTheorem in InvfpH.
destruct InvfpH as [Invfp InvfpH].
put (InvH qA (SetProp q)) InvfqH.
apply IsInvertibleTheorem in InvfqH.
destruct InvfqH as [Invfq InvfqH].
apply (TransitivityEq (%ob [%ob [%f a ; Invfp] ; %ob [%f b ; Invfq]])).
 apply MapArgEq.
 apply EqualInPair'.
 split.
 apply RepresentOfFractionCMonoidTheorem.
 apply InvfpH.
 apply RepresentOfFractionCMonoidTheorem.
 apply InvfqH.
assert(AssB : Ope_SGrpCond ob).
 apply Ope_SGrp.
 apply Monoid_SGrp.
 apply (SetProp MB).
assert(CommA : Ope_CommCond oa).
 apply Ope_Comm.
 apply CMonoid_Comm.
 apply (SetProp MA).
put ((proj1 (IsHomomorphism_of_BOpeTheorem _ _ _)) HomH) Commf.
fold oa in Commf.
fold ob in Commf.
rewrite AssB.
rewrite <- (MapArgEq _ (EqualInPair'R _ _ _ _ _ (AssB _ _ _))).
apply (TransitivityEq (%ob [%f a ; %ob [%ob [%f b ; Invfp] ; Invfq]])).
 apply MapArgEq.
 apply EqualInPair'R.
 apply MapArgEq.
 apply EqualInPair'L.
 generalize InvfpH.
 apply (IfCommThenIsInverseComm _ _ _ AssB).
 rewrite <- Commf.
 rewrite (MapArgEq _ (CommA _ _)).
 rewrite Commf.
 hyperreflexivity.
rewrite (MapArgEq _ (EqualInPair'R _ _ _ _ _ (AssB _ _ _))).
rewrite <- AssB.
rewrite <- (MapArgEq _ (EqualInPair'L _ _ _ _ _ (Commf _ _))).
apply MapArgEq.
apply EqualInPair'R.
cut (Invfq == %ob [%f pA ; Invfpq]).
 intro EqH.
 rewrite (MapArgEq _ (EqualInPair'R _ _ _ _ _ EqH)).
 rewrite <- AssB.
 apply IsLeftIdentTheorem.
 apply IsIdent_LeftIdent.
 apply IsInverseE_IsIdent'.
 apply InvfpH.
cut (%ob [Invfq ; %f (%oa [pA;qA])] == %f pA).
 intro EqH.
 apply SymmetryEq.
 rewrite <- (MapArgEq _ (EqualInPair'L _ _ _ _ _ EqH)).
 rewrite AssB.
 apply IsRightIdentTheorem.
 apply IsIdent_RightIdent.
 apply IsInverseE_IsIdent.
 apply InvfpqH.
cut (%f (%oa [pA;qA]) == %ob [%f qA ; %f pA]).
 intro EqH.
 rewrite (MapArgEq _ (EqualInPair'R _ _ _ _ _ EqH)).
 rewrite <- AssB.
 apply IsLeftIdentTheorem.
 apply IsIdent_LeftIdent.
 apply IsInverseE_IsIdent'.
 apply InvfqH.
rewrite (MapArgEq _ (CommA _ _)).
apply Commf.
Qed.

Theorem RepresentOfFractionCMonoid_HomIdent : forall {A B} (MA : #(CMonoid A)) (MB : #(Monoid B)) (S : #(SubCMonoid MA)) (fR : #(RepresentOfFractionCMonoidableSet MA MB S)),
&&IsHomomorphism_of_Ident [FractionCMonoid MA S;MB{<Monoid_Ope}] (%(RepresentOfFractionCMonoid MA MB S) fR).
Proof.
intros A B MA MB S fR.
set (MB{<Monoid_Ope}) as ob.
apply IsHomomorphism_of_IdentTheorem.
split.
apply RepresentOfFractionCMonoid_HomBOpe.
intros e IsIe.
set (fR{<RepresentOfFCM_Map}) as f.
set (MIdent_of_CMonoid MA) as ea.
assert(IsIea : &&IsIdent (MA{<CMonoid_Ope}) ea).
 generalize (MIdentTheorem (MA{<CMonoid_Ident})).
 apply RelRewriteAll; hyperreflexivity.
assert(Eqe : e == %(FractionCMonoidCannProj MA S) ea).
 apply (IsIdentEq (FractionCMonoid MA S)).
 apply IsIe.
 apply FractionCMonoidCannProj_IsIdent.
 apply IsIea.
cut (&&IsIdent ob (%(%(RepresentOfFractionCMonoid MA MB S) fR) (%(FractionCMonoidCannProj MA S) ea))).
 apply RelRewriteR.
 apply MapArgEq.
 apply SymmetryEq.
 apply Eqe.
cut (&&IsIdent ob (%f ea)).
 apply RelRewriteR.
 apply (TransitivityEq (%(%CombineMap' [FractionCMonoidCannProj MA S ; %(RepresentOfFractionCMonoid MA MB S) fR]) ea)).
  apply MapEq.
  apply SymmetryEq.
  rewrite <- RepresentOfFractionCMonoidEq.
  hyperreflexivity.
 rewrite CombineMap'Theorem.
 hyperreflexivity.
assert(InfR : In f (RepresentOfFractionCMonoidableSet MA MB S)).
 apply (SetProp fR).
apply RepresentOfFractionCMonoidableSetTheorem in InfR.
destruct InfR as [IsHom InvCond].
assert(IneS : In ea S).
 apply (SubIdenticalHasIdent (MA{<CMonoid_Ope})).
 apply IsIea.
put (InvCond _ IneS) Invtfe.
apply IsInvertibleTheorem in Invtfe.
destruct Invtfe as [Ife IsIIfe].
apply IsInverseETheorem in IsIIfe.
assert(AssB : Ope_SGrpCond ob).
 apply Ope_SGrp.
 apply Monoid_SGrp.
 apply (SetProp MB).
cut (&&IsIdent ob (%ob [%f ea;Ife])).
 apply RelRewriteR.
 cut (%ob [%ob [%f ea;Ife] ; %f ea] == %ob [%f ea;%f ea]).
  intro Eq1.
  apply (TransitivityEq (%ob [%ob [%f ea;Ife] ; %ob [%f ea;Ife]])).
   apply SymmetryEq.
   apply IsLeftIdentTheorem.
   apply IsIdent_LeftIdent.
   apply (proj1 IsIIfe).
  rewrite <- AssB.
  rewrite (MapArgEq _ (EqualInPair'L _ _ _ _ _ Eq1)).
  rewrite AssB.
  apply IsRightIdentTheorem.
  apply IsIdent_RightIdent.
  apply (proj1 IsIIfe).
 rewrite AssB.
 apply (TransitivityEq (%f ea)).
  apply IsRightIdentTheorem.
  apply IsIdent_RightIdent.
  apply (proj2 IsIIfe).
 apply SymmetryEq.
 put ((proj1 (IsHomomorphism_of_BOpeTheorem _ _ _)) IsHom) Commf.
 rewrite <- Commf.
 apply MapArgEq.
 apply IsLeftIdentTheorem.
 apply IsIdent_LeftIdent.
 apply IsIea.
apply (proj1 IsIIfe).
Qed.


Theorem RepresentOfFractionCMonoid_HomInverse : forall {A B} (MA : #(CMonoid A)) (MB : #(Monoid B)) (S : #(SubCMonoid MA)) (fR : #(RepresentOfFractionCMonoidableSet MA MB S)),
&&IsHomomorphism_of_Inverse [FractionCMonoid MA S;MB{<Monoid_Ope}] (%(RepresentOfFractionCMonoid MA MB S) fR).
Proof.
intros A B MA MB S fR.
apply IsHomomorphism_of_Ident_IsHomomorphism_of_Inverse.
apply RepresentOfFractionCMonoid_HomIdent.
Qed.

Theorem RepresentOfFractionCMonoid_HomInvert : forall {A B} (MA : #(CMonoid A)) (MB : #(Monoid B)) (S : #(SubCMonoid MA)) (fR : #(RepresentOfFractionCMonoidableSet MA MB S)),
&&IsHomomorphism_of_Invert [FractionCMonoid MA S;MB{<Monoid_Ope}] (%(RepresentOfFractionCMonoid MA MB S) fR).
Proof.
intros A B MA MB S fR.
apply IsHomomorphism_of_Inverse_IsHomomorphism_of_Invert.
apply RepresentOfFractionCMonoid_HomInverse.
Qed.

(*
Theorem RepresentOfFractionCMonoid_Eq : forall {A B} (MA : #(CMonoid A)) (MB : #(Monoid B)) (S : #(SubCMonoid MA)) (f : #(Map A B)) (g1 g2 : #(Map (FractionCMonoidSet MA S) B)),
In f (RepresentOfFractionCMonoidableSet MA MB S) ->
&&IsHomomorphism_of_BOpe [FractionCMonoid MA S ; MB{<Monoid_Ope}] g1 ->
&&IsHomomorphism_of_BOpe [FractionCMonoid MA S ; MB{<Monoid_Ope}] g2 ->
f == %CombineMap' [FractionCMonoidCannProj MA S ; g1] ->
f == %CombineMap' [FractionCMonoidCannProj MA S ; g2] ->
g1 == g2.
Proof.
intros A B MA MB S f g1 g2.
intros conf cong1 cong2 Eg1 Eg2.
assert(App1 : &&(RepresentOfFractionCMonoid MA MB S){<Map_Rel} {f ! conf} g1).
 cut (&&(RepresentOfFractionCMonoidRel MA MB S) {f ! conf} g1).
  apply RelRewrite.
  hyperreflexivity.
 apply MakeRelationTheorem.
 intros f' g1' Eqf Eqg1.
 split.
  rewrite <- Eqf.
  rewrite DSETEq.
  rewrite Eg1.
  apply MapArgEq.
  apply EqualInPair'R.
  apply Eqg1.
 apply (RelRewriteR Eqg1).
 apply cong1.
assert(App2 : &&(RepresentOfFractionCMonoid MA MB S){<Map_Rel} {f ! conf} g2).
 cut (&&(RepresentOfFractionCMonoidRel MA MB S) {f ! conf} g2).
  apply RelRewrite.
  hyperreflexivity.
 apply MakeRelationTheorem.
 intros f' g2' Eqf Eqg2.
 split.
  rewrite <- Eqf.
  rewrite DSETEq.
  rewrite Eg2.
  apply MapArgEq.
  apply EqualInPair'R.
  apply Eqg2.
 apply (RelRewriteR Eqg2).
 apply cong2.
generalize App2.
generalize App1.
apply RightUniqueEq.
apply Rel_RUnq.
apply Map_RUnq.
rewrite USETEq.
apply SetProp.
Qed.
*)


(*



Definition LeftCancellable A :=
nSSet' (BOperation A) (fun o => forall x a b, (%o)[x;a] == (%o)[x;b] -> a == b).

Definition RightCancellable A :=
SSet' (BOperation A) (fun o => forall x a b, (%o)[a;x] == (%o)[b;x] -> a == b).

Definition Cancellable A :=
SSet' (BOperation A) (fun o => (forall x a b, (%o)[x;a] == (%o)[x;b] -> a == b) /\ (forall x a b, (%o)[a;x] == (%o)[b;x] -> a == b)).

Definition RightSolvable A :=
SSet' (BOperation A) (fun o => forall a b, exists c, (%o)[a;c] == b).

Definition Solvable A :=
SSet' (BOperation A) (fun o => (forall a b, exists c, (%o)[c;a] == b) /\ (forall a b, exists c, (%o)[a;c] == b)).


*)

(* Trivial BOperation *)
Definition TrivialBOperation a : #(BOperation (Singleton a)) :=
%CombineMap' [%DoubleMap [IdMap;IdMap] ; MLeft].

Theorem TrivialBOperationTheorem : forall {a} (x y z : #(Singleton a)),
%(TrivialBOperation _) [x;y] == z.
Proof.
intros a x y z.
apply SingletonInEq.
Qed.

Theorem TrivialBOperation_Ope_SGrpCond : forall a,
Ope_SGrpCond (TrivialBOperation a).
Proof.
intro a.
intros x y z.
apply TrivialBOperationTheorem.
Qed.

Theorem TrivialBOperation_Ope_CommCond : forall a,
Ope_CommCond (TrivialBOperation a).
Proof.
intro a.
intros x y.
apply TrivialBOperationTheorem.
Qed.


Theorem TrivialBOperation_Ope_IdentCond : forall a,
Ope_IdentCond (TrivialBOperation a).
Proof.
intro a.
unfold Ope_IdentCond.
assert(Inaa : In a (Singleton a)).
 apply SingletonTheorem.
 hyperreflexivity.
exists {a!Inaa}.
apply IsIdentTheorem.
intros b.
split; apply TrivialBOperationTheorem.
Qed.

Theorem TrivialBOperation_Ope_MonoidCond : forall a,
Ope_MonoidCond (TrivialBOperation a).
Proof.
intro a.
split.
apply TrivialBOperation_Ope_SGrpCond.
apply TrivialBOperation_Ope_IdentCond.
Qed.

Theorem TrivialBOperation_Ope_CMonoidCond : forall a,
Ope_CMonoidCond (TrivialBOperation a).
Proof.
intro a.
split.
apply TrivialBOperation_Ope_MonoidCond.
apply TrivialBOperation_Ope_CommCond.
Qed.

Theorem TrivialBOperation_Ope_InvertCond : forall a,
Ope_InvertCond (TrivialBOperation a).
Proof.
intro a.
intro x.
apply IsInvertibleTheorem.
exists x.
apply IsInverseETheorem.
split; apply IsIdentTheorem; split; apply TrivialBOperationTheorem.
Qed.


Theorem TrivialBOperation_Ope_GrpCond : forall a,
Ope_GrpCond (TrivialBOperation a).
Proof.
intro a.
split.
apply TrivialBOperation_Ope_MonoidCond.
apply TrivialBOperation_Ope_InvertCond.
Qed.

Theorem TrivialBOperation_Ope_CGrpCond : forall a,
Ope_CGrpCond (TrivialBOperation a).
Proof.
intro a.
split.
apply TrivialBOperation_Ope_GrpCond.
apply TrivialBOperation_Ope_CommCond.
Qed.






