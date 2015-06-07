Require Import logic.
Require Import IZF.
Require Import Relation.
Require Import BaseMap.

(* MapImage *)
Theorem RelationImageRRistableRUnq : forall A B,
In (@RelationImageR A B) (RistableMap (Relation A B) (Map (PowerSet A) (PowerSet B)) (RightUnique A B) (Map (PowerSet A) (PowerSet B))).
Proof.
intros A B.
apply RistableMapTheorem.
split.
{
  split.
  apply RUnq_Rel.
  apply ReflexivitySubset.
}
intros rel InrR.
apply (SetProp).
Qed.

Theorem RelationImageRRistableLTtl : forall A B,
In (@RelationImageR A B) (RistableMap (Relation A B) (Map (PowerSet A) (PowerSet B)) (LeftTotal A B) (Map (PowerSet A) (PowerSet B))).
Proof.
intros A B.
apply RistableMapTheorem.
split.
{
  split.
  apply LTtl_Rel.
  apply ReflexivitySubset.
}
intros rel InreL.
apply (SetProp).
Qed.

Theorem RelationImageRRistableMap : forall A B,
In (@RelationImageR A B) (RistableMap (Relation A B) (Map (PowerSet A) (PowerSet B)) (Map A B) (Map (PowerSet A) (PowerSet B))).
Proof.
intros A B.
apply RistableMapTheorem.
split.
{
  split.
  apply Map_Rel.
  apply ReflexivitySubset.
}
intros rel InreM.
apply (SetProp).
Qed.

Definition MapImage {A B} := %RistMap {_!(RelationImageRRistableMap A B)}.

Theorem MapImageTheorem : forall {A B} (f : #(Map A B)) X,
forall y,
In y (%(%MapImage f) X) <-> (exists x : #A, In x X /\ ((%f) x) == y).
Proof.
intros A B f X y.
assert(EqM : ((%(%MapImage f) X) == (%(%RelationImageR (f{<Map_Rel})) X))).
 apply MapEq.
 apply MapStrong.
  unfold MapImage.
  apply StrongRistMapEq.
  hyperreflexivity.
 hyperreflexivity.
split.

 intro InyM.
 rewrite EqM in InyM.
 assert(InyB : In y B).
  assert(InRR : In (%(%RelationImageR (f{<Map_Rel})) X) (PowerSet B)).
   apply MapIn.
  apply PowersetTheorem in InRR.
  apply InRR in InyM.
  assumption.
 rewrite <- (DSETEq _ InyB) in InyM.
 apply RelationImageRTheorem in InyM.
 destruct InyM as [a InyM].
 destruct InyM as [InaX fH].
 exists a.
 split.
 assumption.
 apply (TransitivityEq {y ! InyB}).
  apply AppTheoremReverse.
  apply fH.
 apply ReflexivityEq.

 intro HH.
 destruct HH as [a HH].
 destruct HH as [InaX fay].
 rewrite <- fay.
 rewrite EqM.
 apply RelationImageRTheorem.
 exists a.
 split.
 assumption.
 apply AppTheorem.
Qed.


Theorem CartesianRelationRRistableLTtl : forall A X Y,
In (@CartesianRelationR A X Y) (RistableMap (Cartesian (Relation A X) (Relation A Y)) (Relation A (Cartesian X Y)) (Cartesian (LeftTotal A X) (LeftTotal A Y)) (LeftTotal A (Cartesian X Y))).
Proof.
intros A X Y.
apply RistableMapTheorem.
split.
{
  split.
  apply SubsetInCartesian.
  apply LTtl_Rel.
  apply LTtl_Rel.
  apply LTtl_Rel.
}
intros cc InrelC.
put (CartesianIsPair' _ _ _ InrelC) IsrelD.
destruct IsrelD as [rel1 IsrelD].
destruct IsrelD as [rel2 IsrelD].
assert(rel1C : Rel_LTtlCond (rel1{<LTtl_Rel})).
{
 apply Rel_LTtl.
 apply (SetProp rel1).
}
assert(rel2C : Rel_LTtlCond (rel2{<LTtl_Rel})).
{
  apply Rel_LTtl.
  apply (SetProp rel2).
}
apply Rel_LTtl.
intro a.
destruct (rel1C a) as [b rel1C'].
destruct (rel2C a) as [c rel2C'].
exists [b;c].
cut (&&(%CartesianRelationR [rel1{<LTtl_Rel};rel2{<LTtl_Rel}]) a [b;c]).
 apply RelRewrite.
 apply MapArgEq.
 rewrite IsrelD.
 hyperreflexivity.
apply CartesianRelationRTheorem.
split; assumption.
Qed.

Theorem CartesianRelationRRistableRUnq : forall A X Y,
In (@CartesianRelationR A X Y) (RistableMap (Cartesian (Relation A X) (Relation A Y)) (Relation A (Cartesian X Y)) (Cartesian (RightUnique A X) (RightUnique A Y)) (RightUnique A (Cartesian X Y))).
Proof.
intros A X Y.
apply RistableMapTheorem.
split.
{
  split.
  apply SubsetInCartesian.
  apply RUnq_Rel.
  apply RUnq_Rel.
  apply RUnq_Rel.
}
intros relD InrelC.
apply Rel_RUnq.
intro a.
intros p1 p2 H1 H2.
put (CartesianIsPair' _ _ _ InrelC) IsrelD.
destruct IsrelD as [rel1 IsrelD].
destruct IsrelD as [rel2 IsrelD].
put (CartesianIsPair' _ _ _ (SetProp p1)) IsP1.
destruct IsP1 as [x1 IsP1].
destruct IsP1 as [y1 IsP1].
put (CartesianIsPair' _ _ _ (SetProp p2)) IsP2.
destruct IsP2 as [x2 IsP2].
destruct IsP2 as [y2 IsP2].
assert(H1' : &&(%CartesianRelationR [rel1{<RUnq_Rel};rel2{<RUnq_Rel}]) a [x1;y1]).
 generalize H1.
 apply RelRewriteAll.
 hyperreflexivity.
 apply IsP1.
 apply MapArgEq.
 rewrite IsrelD.
 hyperreflexivity.
assert(H2' : &&(%CartesianRelationR [rel1{<RUnq_Rel};rel2{<RUnq_Rel}]) a [x2;y2]).
 generalize H2.
 apply RelRewriteAll.
 hyperreflexivity.
 apply IsP2.
 apply MapArgEq.
 rewrite IsrelD.
 hyperreflexivity.
clear H1.
clear H2.
apply CartesianRelationRTheorem in H1'.
apply CartesianRelationRTheorem in H2'.
destruct H1' as [relH11 relH12].
destruct H2' as [relH21 relH22].
assert(Eqx : x1 == x2).
 assert(RCond : Rel_RUnqCond (rel1{<RUnq_Rel})).
  apply Rel_RUnq.
  apply (SetProp rel1).
 apply (Atmost'EqApply _ (RCond a)).
 split; assumption.
assert(Eqy : y1 == y2).
 assert(RCond : Rel_RUnqCond (rel2{<RUnq_Rel})).
  apply Rel_RUnq.
  apply (SetProp rel2).
 apply (Atmost'EqApply _ (RCond a)).
 split; assumption.
rewrite IsP1.
rewrite IsP2.
apply EqualInPair'.
split; assumption.
Qed.

Theorem CartesianRelationRRistableMap : forall A X Y,
In (@CartesianRelationR A X Y) (RistableMap (Cartesian (Relation A X) (Relation A Y)) (Relation A (Cartesian X Y)) (Cartesian (Map A X) (Map A Y)) (Map A (Cartesian X Y))).
Proof.
intros A X Y.
apply RistableMapTheorem.
split.
{
  split.
  apply SubsetInCartesian.
  apply Map_Rel.
  apply Map_Rel.
  apply Map_Rel.
}
intros p InpC.
apply Rel_Map2.
split.
 apply Rel_LTtl.
 put (CartesianRelationRRistableLTtl A X Y) LTR.
 apply RistableMapTheorem in LTR.
 destruct LTR as [[S1 S2] LTR].
 apply LTR.
 assert(sub : Subset (Cartesian (Map A X) (Map A Y)) (Cartesian (LeftTotal A X) (LeftTotal A Y))).
  apply SubsetInCartesian; apply Map_LTtl.
 apply sub.
 apply InpC.

 apply Rel_RUnq.
 put (CartesianRelationRRistableRUnq A X Y) RUR.
 apply RistableMapTheorem in RUR.
 destruct RUR as [[S1 S2] RUR].
 apply RUR.
 assert(sub : Subset (Cartesian (Map A X) (Map A Y)) (Cartesian (RightUnique A X) (RightUnique A Y))).
  apply SubsetInCartesian; apply Map_RUnq.
 apply sub.
 apply InpC.
Qed.

(* CartesianDMap*)
 
Definition CartesianDMap {A X Y} : #(Map (Cartesian (Map A X) (Map A Y)) (Map A (Cartesian X Y))) :=
%RistMap {_!(CartesianRelationRRistableMap A X Y)}.


Theorem CartesianDMapTheorem : forall {A X Y} (f : #(Map A X)) (g : #(Map A Y)),
forall a : #A,
%(%CartesianDMap [f;g]) a == [%f a; %g a].
Proof.
intros A X Y f g a.
apply AppTheoremReverse.
cut (&&(%CartesianRelationR [f{<Map_Rel};g{<Map_Rel}]) a [%f a; %g a]).
 apply RelRewrite.
 rewrite (USETEq (%CartesianDMap [f;g]) _).
 apply SymmetryEq.
 apply MapStrong.
  unfold CartesianDMap.
  apply StrongRistMapEq.
  hyperreflexivity.
 hyperreflexivity.
apply CartesianRelationRTheorem.
split; apply AppTheorem.
Qed.

Theorem CaratesianDMapRistableInj : forall {A X Y},
In (@CartesianDMap A X Y) (RistableMap (Cartesian (Map A X) (Map A Y)) (Map A (Cartesian X Y)) (Cartesian (Injection A X) (Injection A Y)) (Injection A (Cartesian X Y))).
Proof.
intros A X Y.
apply RistableMapTheorem.
split.
{
  split.
  apply SubsetInCartesian; apply Inj_Map.
  apply Inj_Map.
}
intros fD InfDC.
put (CartesianIsPair' _ _ _ InfDC) fD'.
destruct fD' as [f1 fD'].
destruct fD' as [f2 EqfD].
assert(EqfD' : fD == [f1{<Inj_Map} ; f2{<Inj_Map}]).
 rewrite EqfD.
 hyperreflexivity.
rewrite (MapArgEq _ EqfD').
apply Map_Inj.
intros a1 a2 Eqf.
assert(EqPf : [%f1{<Inj_Map} a1 ; %f2{<Inj_Map} a1] == [%f1{<Inj_Map} a2 ; %f2{<Inj_Map} a2]).
 apply (TransitivityEq (%(%CartesianDMap [f1{<Inj_Map};f2{<Inj_Map}]) a1)).
 rewrite CartesianDMapTheorem.
 hyperreflexivity.
 rewrite Eqf.
 rewrite CartesianDMapTheorem.
 hyperreflexivity.
apply EqualInPair' in EqPf.
destruct EqPf as [EqPf1 EqPf2].
assert(InjC1 : Map_InjCond (f1{<Inj_Map})).
 apply Map_Inj.
 apply (SetProp f1).
assert(InjC2 : Map_InjCond (f2{<Inj_Map})).
 apply Map_Inj.
 apply (SetProp f2).
apply InjC1 in EqPf1.
apply InjC2 in EqPf2.
assumption.
Qed.


(* Inverse Relation *)
Definition InversePair {L R} := %(@CartesianDMap (Cartesian L R) R L) [MRight; MLeft].

Theorem InversePairTheorem : forall {L R} (l : #L) (r : #R),
%InversePair [l;r] == [r;l].
Proof.
intros L R l r.
unfold InversePair.
apply (TransitivityEq [%MRight [l;r] ; %MLeft [l;r]]).
 apply CartesianDMapTheorem.
apply EqualInPair'.
split.
apply RightPairTheorem.
apply LeftPairTheorem.
Qed.

Definition InverseRel {A B} 
: #(Map (Relation A B) (Relation B A)) := (%MapImage InversePair).

Theorem InverseRelTheorem : forall {A B} (rel : #(Relation A B)),
forall a b,
&&rel a b <-> &&(%InverseRel rel) b a.
Proof.
intros A B rel a b.
split.

intro relH.
unfold If.
unfold InverseRel.
apply MapImageTheorem.
exists [a;b].
split.
apply relH.
apply (TransitivityEq [b;a]).
 apply InversePairTheorem.
hyperreflexivity.

intro relI.
unfold If in relI.
unfold InverseRel in relI.
apply MapImageTheorem in relI.
destruct relI as [p relI].
destruct relI as [Inprel Eqp].
assert(IsPp : IsPair p).
 apply (IsPairRelation _ _ Inprel).
destruct IsPp as [a' IsPp].
destruct IsPp as [b' EqP].
assert(InD : In a' A /\ In b' B).
 apply CartesianTheorem.
 rewrite <- EqP.
 apply SetProp.
destruct InD as [InaA' InbB'].
assert(EqP' : Pair b' a' == Pair b a).
 apply (TransitivityEq [{b'!InbB'} ; {a'!InaA'}]).
  hyperreflexivity.
 apply (TransitivityEq (%InversePair [{a'!InaA'};{b'!InbB'}])).
  apply SymmetryEq.
  apply InversePairTheorem.
 apply (TransitivityEq (%InversePair p)).
  apply MapArgEq.
  rewrite EqP.
  hyperreflexivity.
 apply Eqp.
apply EqualInPair in EqP'.
destruct EqP' as [Eqb Eqa].
assert(relH' : &&rel {a'!InaA'} {b'!InbB'}).
 unfold If.
 rewrite EqP in Inprel.
 apply Inprel.
generalize relH'.
apply RelRewriteAll.
apply (TransitivityEq a').
hyperreflexivity.
apply Eqa.
apply (TransitivityEq b').
hyperreflexivity.
apply Eqb.
hyperreflexivity.
Qed.

Theorem InverseRelTheorem' : forall {A B} (rel : #(Relation A B)),
forall a b,
&&(%InverseRel rel) b a <-> &&rel a b.
Proof.
intros.
apply SymmetryEquiv.
apply InverseRelTheorem.
Qed.

Theorem InverseRelMapRCondLUnq : forall A B,
  In (@InverseRel A B) (RistableMap (Relation A B) (Relation B A) (RightUnique A B) (LeftUnique B A)).
Proof.
intros A B.
apply RistableMapTheorem.
split.
{
  split.  
  apply RUnq_Rel.
  apply LUnq_Rel.
}
intros rel InrelR.
apply Rel_RUnq in InrelR.
apply Rel_LUnq.
intro a.
intros b1 b2 H1 H2.
apply InverseRelTheorem in H1.
apply InverseRelTheorem in H2.
apply (Atmost'EqApply _ (InrelR a)).
split; assumption.
Qed.

Theorem InverseRelMapRCondRUnq : forall A B,
  In (@InverseRel A B) (RistableMap (Relation A B) (Relation B A) (LeftUnique A B) (RightUnique B A)).
Proof.
intros A B.
apply RistableMapTheorem.
split.
{
  split.
  apply LUnq_Rel.
  apply RUnq_Rel.
}
intros rel InrelR.
apply Rel_LUnq in InrelR.
apply Rel_RUnq.
intro a.
intros b1 b2 H1 H2.
apply InverseRelTheorem in H1.
apply InverseRelTheorem in H2.
apply (Atmost'EqApply _ (InrelR a)).
split; assumption.
Qed.

Theorem InverseRelMapRCondRTtl : forall A B,
  In (@InverseRel A B) (RistableMap (Relation A B) (Relation B A) (LeftTotal A B) (RightTotal B A)).
Proof.
intros A B.
apply RistableMapTheorem.
split.
{
  split.
  apply LTtl_Rel.
  apply RTtl_Rel.
}
intros rel InrelL.
apply Rel_LTtl in InrelL.
apply Rel_RTtl.
intros a.
destruct (InrelL a) as [b InrelL'].
exists b.
apply InverseRelTheorem'.
assumption.
Qed.

Theorem InverseRelMapRCondLTtl : forall A B,
  In (@InverseRel A B) (RistableMap (Relation A B) (Relation B A) (RightTotal A B) (LeftTotal B A)).
Proof.
intros A B.
apply RistableMapTheorem.
split.
{
  split.
  apply RTtl_Rel.
  apply LTtl_Rel.
}
intros rel InrelL.
apply Rel_RTtl in InrelL.
apply Rel_LTtl.
intros a.
destruct (InrelL a) as [b InrelL'].
exists b.
apply InverseRelTheorem'.
assumption.
Qed.


(* Combine *)
Theorem CombineRelationRistableMap : forall A B C,
In (@CombineRelation A B C) (RistableMap (Cartesian (Relation A B) (Relation B C)) (Relation A C) (Cartesian (Map A B) (Map B C)) (Map A C)).
Proof.
intros A B C.
apply RistableMapTheorem.
split.
{
  split.
  apply SubsetInCartesian.
  apply Map_Rel.
  apply Map_Rel.
  apply Map_Rel.
}
intros relD InrelDC.
put (CartesianIsPair' _ _ _ InrelDC) IsPrelD.
destruct IsPrelD as [rel1 IsPrelD].
destruct IsPrelD as [rel2 IsPrelD].
assert(EqrelD' : [rel1{<Map_Rel} ; rel2{<Map_Rel}] == relD).
 rewrite IsPrelD.
 hyperreflexivity.
rewrite (MapArgEq' _ EqrelD').
apply Rel_Map.
intros a.
split.
 exists (%rel2 (%rel1 a)).
 apply CombineRelationTheorem.
 exists (%rel1 a).
 split; apply AppTheorem.

 intros c1 c2 HD.
 destruct HD as [H1 H2].
 apply CombineRelationTheorem in H1.
 apply CombineRelationTheorem in H2.
 destruct H1 as [b1 H1].
 destruct H2 as [b2 H2].
 destruct H1 as [H11 H12].
 destruct H2 as [H21 H22].
 assert(rel2RU : Rel_RUnqCond (rel2{<Map_Rel})).
  apply Rel_RUnq.
  apply Map_RUnq.
  apply (SetProp rel2).
 assert(rel1RU : Rel_RUnqCond (rel1{<Map_Rel})).
  apply Rel_RUnq.
  apply Map_RUnq.
  apply (SetProp rel1).
 assert(Eqb : b1 == b2).
  apply (Atmost'EqApply _ (rel1RU a)).
  split; assumption.
 apply (Atmost'EqApply _ (rel2RU b1)).
 split.
  apply H12.
  apply (RelRewriteL' Eqb).
  apply H22.
Qed.

Definition CombineMap' {A B C} : #(Map (Cartesian (Map A B) (Map B C)) (Map A C)) :=
%RistMap {_!CombineRelationRistableMap A B C}.

Theorem CombineMap'Theorem : forall A B C (f : #(Map A B)) (g : #(Map B C)),
forall (a : #A),
%(%CombineMap' [f;g]) a == %g (%f a).
Proof.
intros A B C f g a.
unfold CombineMap'.
apply AppTheoremReverse.
cut (&&(%CombineRelation [f{<Map_Rel} ; g{<Map_Rel}]) a (%g (%f a))).
 apply RelRewrite.
 apply SymmetryEq.
 rewrite (USETEq (%(%RistMap {_!(CombineRelationRistableMap A B C)}) [f;g]) Map_Rel).
 apply MapStrong.
  apply StrongRistMapEq.
  hyperreflexivity.
 hyperreflexivity.
apply CombineRelationTheorem.
exists (%f a).
split; apply AppTheorem.
Qed.


Definition CombineMap {A B C} : #(Map (Cartesian (Map B C) (Map A B)) (Map A C)) :=
%CombineMap' [InversePair; CombineMap'].

Theorem CombineMapTheorem : forall A B C  (g : #(Map B C)) (f : #(Map A B)),
forall (a : #A),
%(%CombineMap [g;f]) a == %g (%f a).
Proof.
intros A B C g f a.
unfold CombineMap.
apply (TransitivityEq (%(%CombineMap' (%InversePair [g;f])) a)).
 apply MapEq.
 apply CombineMap'Theorem.
apply (TransitivityEq (%(%CombineMap' [f;g]) a)).
 apply MapEq.
 apply MapArgEq.
 apply InversePairTheorem.
apply CombineMap'Theorem.
Qed.

Definition CombMap {A B C} : #(Map (Map B C) (Map (Map A B) (Map A C))) := %Currying CombineMap.
Definition CombMap' {A B C} : #(Map (Map A B) (Map (Map B C) (Map A C))) := %Currying CombineMap'.

Theorem CombMapTheorem : forall A B C (g : #(Map B C)) (f : #(Map A B)),
forall (a : #A),
%(%(%CombMap g) f) a == %g (%f a).
Proof.
intros A B C g f a.
unfold CombMap.
apply (TransitivityEq (%(%CombineMap [g; f]) a)).
 apply MapEq.
 apply CurryingTheorem.
apply CombineMapTheorem.
Qed.

Theorem CombMap'Theorem : forall A B C (f : #(Map A B)) (g : #(Map B C)),
forall (a : #A),
%(%(%CombMap' f) g) a == %g (%f a).
Proof.
intros A B C f g a.
unfold CombMap'.
apply (TransitivityEq (%(%CombineMap' [f; g]) a)).
 apply MapEq.
 apply CurryingTheorem.
apply CombineMap'Theorem.
Qed.

 

(* Inverse Map *)
Theorem InverseRelMapRCondBij : forall A B,
  In (@InverseRel A B) (RistableMap (Relation A B) (Relation B A) (Bijection A B) (Map B A)).
Proof.
intros A B.
apply RistableMapTheorem.
split.
{
  split.
  apply (TransitivitySubset (Map A B)).
  apply Bij_Map.
  apply Map_Rel.
  apply Map_Rel.
}
intros rel InrelB.
assert(InrelM : In rel (Map A B)).
 apply Bij_Map.
 assumption.
apply Rel_Map.
intro b.
assert(BijCond : Map_BijCond {rel ! InrelM}).
 apply Map_Bij.
 apply (InrelB).
destruct BijCond as [InjCond SurCond].
split.
 destruct (SurCond b) as [a SurCond'].
 exists a.
 apply InverseRelTheorem'.
 cut (&&({rel ! InrelM}{<Map_Rel}) a (%{rel ! InrelM} a)).
  apply RelRewriteAll.
  hyperreflexivity.
  apply SurCond'.
  hyperreflexivity.
 apply AppTheorem.

 intros a1 a2 D2.
 destruct D2 as [H1 H2].
 apply InverseRelTheorem in H1.
 apply InverseRelTheorem in H2.
 apply InjCond.
 apply (TransitivityEq b).
  apply AppTheoremReverse.
  apply H1.

  apply SymmetryEq.
  apply AppTheoremReverse.
  apply H2.
Qed.

Definition InverseMap {A B} : #(Map (Bijection A B) (Map B A)) :=
%RistMap {InverseRel ! InverseRelMapRCondBij A B}.

Theorem InverseMapTheorem : forall {A B} (f : #(Bijection A B)) (a : #A),
%(%InverseMap f) (%f{<Bij_Map} a) == a.
Proof.
intros A B f a.
apply AppTheoremReverse.
unfold InverseMap.
cut (&&(%InverseRel f{<Bij_Map}{<Map_Rel}) (%f{<Bij_Map} a) a).
 apply RelRewrite.
 apply (TransitivityEq (%(%RistMap {_!InverseRelMapRCondBij A B})f)). 
  apply SymmetryEq.
  apply MapStrong.
   apply StrongRistMapEq.
   hyperreflexivity.
  hyperreflexivity.
 hyperreflexivity.
apply InverseRelTheorem'.
apply AppTheorem.
Qed.

Theorem MapInverseTheorem : forall {A B} (f : #(Bijection A B)) (b : #B),
%(f{<Bij_Map}) (%(%InverseMap f) b) == b.
Proof.
intros A B f b.
assert(SurC : Map_SurCond (f{<Bij_Map})).
 apply Map_Sur.
 apply Bij_Sur.
 apply (SetProp f).
destruct (SurC b) as [a SurC'].
apply (TransitivityEq ((%f{<Bij_Map}) (%(%InverseMap f) (%f{<Bij_Map} a)))).
 apply MapArgEq.
 apply MapArgEq.
 rewrite <- SurC'.
 hyperreflexivity.
apply (TransitivityEq (%f{<Bij_Map} a)).
 apply MapArgEq.
 rewrite InverseMapTheorem.
 hyperreflexivity.
apply SurC'.
Qed.

Theorem InverseMapTheoremRC : forall {A B} (f : #(Map A B)) (cond : Map_BijCond f) (a : #A),
%(%InverseMap (f{<Map_Bij ! cond})) (%f a) == a.
Proof.
intros A B f cond a.
assert(Eqf : f == (f{<Map_Bij ! cond}{<Bij_Map})).
 hyperreflexivity.
rewrite (MapArgEq _ (MapEq Eqf)).
rewrite (InverseMapTheorem _ _).
hyperreflexivity.
Qed.

Theorem MapInverseTheoremRC : forall {A B} (f : #(Map A B)) (cond : Map_BijCond f) (b : #B),
%f (%(%InverseMap (f{<Map_Bij ! cond})) b) == b.
Proof.
intros A B f cond a.
assert(Eqf : (f) == (f{<Map_Bij ! cond}{<Bij_Map})).
 hyperreflexivity.
rewrite (MapEq Eqf).
rewrite MapInverseTheorem.
hyperreflexivity.
Qed.

Theorem SurjectionInverseMap : forall {A B} (f: #(Bijection A B)),
Map_SurCond (%InverseMap f).
Proof.
intros A B f.
intros a.
exists (%f{<Bij_Map} a).
apply InverseMapTheorem.
Qed.

Theorem InjectionInverseMap : forall {A B} (f : #(Bijection A B)),
Map_InjCond (%InverseMap f).
Proof.
intros A B f.
intros b1 b2 Eqb.
apply (TransitivityEq (%(f{<Bij_Map}) (%(%InverseMap f) b1))).
 apply SymmetryEq.
 apply MapInverseTheorem.
apply (TransitivityEq (%(f{<Bij_Map}) (%(%InverseMap f) b2))).
 apply MapArgEq.
 apply Eqb.
apply MapInverseTheorem.
Qed.



(* Cartesian Associativity *)
Definition AssocPairLR {A B C} : #(Map (Cartesian (Cartesian A B) C) (Cartesian A (Cartesian B C))) :=
(%CartesianDMap [%CombineMap [MLeft;MLeft]; %CartesianDMap [%CombineMap[MRight;MLeft]; MRight]]).

Theorem AssocPairLRTheorem : forall {A B C} (a : #A) (b : #B) (c : #C),
%AssocPairLR [[a;b];c] == [a;[b;c]].
Proof.
intros A B C a b c.
unfold AssocPairLR.
apply (TransitivityEq [%(%CombineMap [MLeft;MLeft]) [[a;b];c] ; %(%CartesianDMap [%CombineMap [MRight;MLeft];MRight]) [[a;b];c] ]).
 apply CartesianDMapTheorem.
apply EqualInPair'.
split.
 apply (TransitivityEq (%MLeft (%MLeft [[a;b];c]))).
  apply CombineMapTheorem.
 apply (TransitivityEq (%MLeft [a;b])).
  apply MapEqAll.
  apply LeftPairTheorem.
  apply ReflexivityEq.
 apply LeftPairTheorem.
apply (TransitivityEq [%(%CombineMap [MRight;MLeft]) [[a;b];c]; %MRight [[a;b];c]]).
 apply CartesianDMapTheorem.
apply EqualInPair'.
split.
 apply (TransitivityEq (%MRight (%MLeft [[a;b];c]))).
  apply CombineMapTheorem.
 apply (TransitivityEq (%MRight [a;b])).
  apply MapArgEq.
  apply LeftPairTheorem.
 apply RightPairTheorem.
apply RightPairTheorem.
Qed.

Theorem InjectionAssocPairLR : forall {A B C},
Map_InjCond (@AssocPairLR A B C).
Proof.
intros A B C.
intros p1 p2 EqAp.
put (CartesianIsPair' _ _ _ (SetProp p1)) Eqp1.
destruct Eqp1 as [ab1 Eqp1].
destruct Eqp1 as [c1 Eqp1].
put (CartesianIsPair' _ _ _ (SetProp p2)) Eqp2.
destruct Eqp2 as [ab2 Eqp2].
destruct Eqp2 as [c2 Eqp2].
put (CartesianIsPair' _ _ _ (SetProp ab1)) Eqab1.
destruct Eqab1 as [a1 Eqab1].
destruct Eqab1 as [b1 Eqab1].
put (CartesianIsPair' _ _ _ (SetProp ab2)) Eqab2.
destruct Eqab2 as [a2 Eqab2].
destruct Eqab2 as [b2 Eqab2].
assert(EqP : [a1;[b1;c1]] == [a2;[b2;c2]]).
 apply (TransitivityEq (%AssocPairLR [[a1;b1];c1])).
  rewrite (AssocPairLRTheorem).
  hyperreflexivity.
 apply (TransitivityEq (%AssocPairLR p1)).
  apply MapArgEq.
  rewrite Eqp1.
  apply EqualInPair'.
  rewrite Eqab1.
  split; hyperreflexivity.
 rewrite EqAp.
 apply (TransitivityEq (%AssocPairLR [[a2;b2];c2])).
  apply MapArgEq.
  rewrite Eqp2.
  apply EqualInPair'.
  rewrite Eqab2.
  split; hyperreflexivity.
 rewrite (AssocPairLRTheorem).
 hyperreflexivity.
apply EqualInPair' in EqP.
destruct EqP as [Eqa EqP].
apply EqualInPair' in EqP.
destruct EqP as [Eqb Eqc].
rewrite (Eqp1).
rewrite (Eqp2).
apply EqualInPair'.
rewrite Eqab1.
rewrite Eqab2.
split.
apply EqualInPair'.
split; assumption.
assumption.
Qed.

Theorem SurjectionAssocPairLR : forall {A B C},
Map_SurCond (@AssocPairLR A B C).
Proof.
intros A B C.
intros p.
put (CartesianIsPair' _ _ _ (SetProp p)) Eqp.
destruct Eqp as [a Eqp].
destruct Eqp as [bc Eqp].
put (CartesianIsPair' _ _ _ (SetProp bc)) Eqbc.
destruct Eqbc as [b Eqbc].
destruct Eqbc as [c Eqbc].
exists [[a;b];c].
rewrite AssocPairLRTheorem.
rewrite Eqp.
apply EqualInPair'.
split.
hyperreflexivity.
rewrite Eqbc.
hyperreflexivity.
Qed.

Theorem BijectionAssocPairLR : forall {A B C},
Map_BijCond (@AssocPairLR A B C).
Proof.
intros A B C.
split.
apply InjectionAssocPairLR.
apply SurjectionAssocPairLR.
Qed.

Definition AssocPairRL {A B C} : #(Map (Cartesian A (Cartesian B C)) (Cartesian (Cartesian A B) C)) :=
%InverseMap (AssocPairLR{<Map_Bij ! BijectionAssocPairLR}).

Theorem AssocPairRLTheorem : forall {A B C} (a : #A) (b : #B) (c : #C),
%AssocPairRL [a;[b;c]] == [[a;b];c].
Proof.
intros A B C a b c.
apply (TransitivityEq (%AssocPairRL (%AssocPairLR [[a;b];c]))).
 apply MapArgEq.
 apply SymmetryEq.
 apply AssocPairLRTheorem. 
unfold AssocPairRL.
rewrite (InverseMapTheoremRC _ _ _).
hyperreflexivity.
Qed.

Theorem InjectionAssocPairRL : forall {A B C},
Map_InjCond (@AssocPairRL A B C).
Proof.
intros A B C.
unfold AssocPairRL.
apply InjectionInverseMap.
Qed.

Theorem SurjectionAssocPairRL : forall {A B C},
Map_SurCond (@AssocPairRL A B C).
Proof.
intros A B C.
unfold AssocPairRL.
apply SurjectionInverseMap.
Qed.

Theorem BijectionAssocPairRL : forall {A B C},
Map_BijCond (@AssocPairRL A B C).
Proof.
intros A B C.
split.
apply InjectionAssocPairRL.
apply SurjectionAssocPairRL.
Qed.

(* Triple Relation *)
Definition AssocRelationLR {A B C} : #(Map (Relation (Cartesian A B) C) (Relation A (Cartesian B C))) :=
%MapImage AssocPairLR.

Theorem AssocRelationLRTheorem : forall {A B C} (rel : #(Relation (Cartesian A B) C)),
forall a b c,
(&&rel [a;b] c) <-> (&&(%AssocRelationLR rel) a [b;c]).
Proof.
intros A B C rel a b c.
split.

intro relH.
unfold If.
unfold AssocRelationLR.
apply MapImageTheorem.
exists [[a;b];c].
split.
apply relH.
apply (TransitivityEq [a;[b;c]]).
apply AssocPairLRTheorem.
hyperreflexivity.

intro relH.
unfold If in relH.
apply MapImageTheorem in relH.
destruct relH as [p relH].
destruct relH as [InpR Eqp].
assert(InpP : IsPair p).
 apply (IsPairRelation _ _ InpR).
destruct InpP as [ab InpP].
destruct InpP as [c' InpP].
assert(InD : In ab (Cartesian A B) /\ In c' C).
 apply CartesianTheorem.
 rewrite <- InpP.
 apply SetProp.
destruct InD as [InabC IncC].
assert(IsPab : IsPair ab).
 apply (CartesianIsPair _ _ _ InabC).
destruct IsPab as [a' IsPab].
destruct IsPab as [b' Eqab].
assert(InD : In a' A /\ In b' B).
 apply CartesianTheorem.
 rewrite <- Eqab.
 apply InabC.
destruct InD as [InaA InbB].
assert(EqPP : [{a'!InaA};[{b'!InbB};{c'!IncC}]] == [a;[b;c]]).
 apply (TransitivityEq (%AssocPairLR [[{a'!InaA};{b'!InbB}];{c'!IncC}])).
  apply SymmetryEq.
  apply AssocPairLRTheorem.
 apply (TransitivityEq (%AssocPairLR p)).
  apply MapArgEq.
  rewrite InpP.
  rewrite Eqab.
  hyperreflexivity.
 rewrite Eqp.
 hyperreflexivity.
apply EqualInPair' in EqPP.
destruct EqPP as [Eqa EqPP].
apply EqualInPair' in EqPP.
destruct EqPP as [Eqb Eqc].
cut (&&rel [{a'!InaA};{b'!InbB}] {c'!IncC}).
 apply RelRewriteAll.
 apply EqualInPair'.
 split; assumption.
 assumption.
 hyperreflexivity.
rewrite InpP in InpR.
rewrite Eqab in InpR.
apply InpR.
Qed.

Definition AssocRelationRL {A B C} : #(Map (Relation A (Cartesian B C)) (Relation (Cartesian A B) C)) :=
%MapImage AssocPairRL.

Theorem AssocRelationRLTheorem : forall {A B C} (rel : #(Relation A (Cartesian B C))),
forall a b c,
(&&rel a [b;c]) <-> (&&(%AssocRelationRL rel) [a;b] c).
Proof.
intros A B C rel a b c.
split.

intro relH.
unfold If.
unfold AssocRelationRL.
apply MapImageTheorem.
exists [a;[b;c]].
split.
 apply relH.
apply (TransitivityEq [[a;b];c]).
apply AssocPairRLTheorem.
hyperreflexivity.

intros relH.
unfold If in relH.
apply MapImageTheorem in relH.
destruct relH as [p relH].
destruct relH as [Inpr EqApP].
put (CartesianIsPair' _ _ _ (SetProp p)) IsPp.
destruct IsPp as [a' IsPp].
destruct IsPp as [bc' IsPp].
put (CartesianIsPair' _ _ _ (SetProp bc')) Isbcp.
destruct Isbcp as [b' Isbcp].
destruct Isbcp as [c' Isbcp].
assert(EqP : [[a';b'];c'] == [[a;b];c]).
 apply (TransitivityEq (%AssocPairRL [a';[b';c']])).
  apply SymmetryEq.
  apply AssocPairRLTheorem.
 apply (TransitivityEq (%AssocPairRL p)).
  apply MapArgEq.
  rewrite IsPp.
  apply EqualInPair'.
  split.
  hyperreflexivity.
  rewrite Isbcp.
  hyperreflexivity.
 rewrite EqApP.
 hyperreflexivity.
apply EqualInPair' in EqP.
destruct EqP as [EqP Eqc].
apply EqualInPair' in EqP.
destruct EqP as [Eqa Eqb].
cut (&&rel a' [b';c']).
 apply RelRewriteAll.
 apply Eqa.
 apply EqualInPair'.
 split.
 apply Eqb.
 apply Eqc.
 hyperreflexivity.
unfold If.
cut (In p rel).
 apply Arrow2Rewrite.
 rewrite IsPp.
 apply SymmetryEq.
 apply EqualInPairPair'.
 split.
 rewrite Eqa.
 hyperreflexivity.
 rewrite Isbcp.
 hyperreflexivity.
 hyperreflexivity.
apply Inpr.
Qed.

(* Currying *)

Theorem CurryingInjection : forall A B C,
Map_InjCond (@Currying A B C).
Proof.
intros A B C.
intros f1 f2 Eqf.
apply MapEquality.
apply ReflexivityEq.
intros ab1 ab2 Eqab.
assert(IsP1 : IsPair ab1).
 apply (CartesianIsPair _ _ _ (SetProp ab1)).
 destruct IsP1 as [a1 IsP1].
 destruct IsP1 as [b1 Eqp1]. 
assert(InD : In a1 A /\ In b1 B).
 apply CartesianTheorem.
 rewrite <- Eqp1.
 apply (SetProp ab1).
destruct InD as [InaA1 InbB1].
assert(IsP2 : IsPair ab2).
 apply (CartesianIsPair _ _ _ (SetProp ab2)).
 destruct IsP2 as [a2 IsP2].
 destruct IsP2 as [b2 Eqp2]. 
assert(InD : In a2 A /\ In b2 B).
 apply CartesianTheorem.
 rewrite <- Eqp2.
 apply (SetProp ab2).
destruct InD as [InaA2 InbB2].
assert(EqP : (Pair a1 b1) == (Pair a2 b2)).
 rewrite <- Eqp1.
 rewrite <- Eqp2.
 apply Eqab.
apply EqualInPair in EqP.
destruct EqP as [Eqa Eqb].
apply (TransitivityEq (%f1 [{a1!InaA1};{b1!InbB1}])).
 apply MapArgEq.
 rewrite Eqp1.
 hyperreflexivity.
apply (TransitivityEq (%(%(%Currying f1) {a1!InaA1}) {b1!InbB1})).
 apply SymmetryEq.
 apply CurryingTheorem.
apply (TransitivityEq (%(%(%Currying f2) {a2!InaA2}) {b2!InbB2})).
 apply MapEqAll.
 apply Eqb.
 apply MapEqAll.
 apply Eqa.
 apply Eqf.
apply (TransitivityEq (%f2 [{a2!InaA2};{b2!InbB2}])).
 apply CurryingTheorem.
apply MapArgEq.
rewrite Eqp2.
hyperreflexivity.
Qed.

Theorem CurryingSurjection : forall A B C,
Map_SurCond (@Currying A B C).
Proof.
intros A B C.
intro cur.
set ((fun p : #(Cartesian A B) => %(%cur (%MLeft p)) (%MRight p))) as F.
assert (RF : RFun F).
 proofRFun.
exists (MakeMap _ _ _ RF).
apply MapEquality.
hyperreflexivity.
intros a1 a2 Eqa.
apply MapEquality.
hyperreflexivity.
intros b1 b2 Eqb.
rewrite CurryingTheorem.
rewrite MakeMapTheorem.
apply MapEqAll.
rewrite <- Eqb.
apply RightPairTheorem.
apply MapArgEq.
rewrite <- Eqa.
apply LeftPairTheorem.
Qed.

Theorem CurryingBijection : forall A B C,
Map_BijCond (@Currying A B C).
Proof.
intros A B C.
split.
apply CurryingInjection.
apply CurryingSurjection.
Qed.

Definition Uncurrying {A B C} : #(Map (Map A (Map B C)) (Map (Cartesian A B) C)) :=
%InverseMap (Currying{<Map_Bij ! (CurryingBijection A B C)}).

Theorem UncurryingInjection : forall A B C,
Map_InjCond (@Uncurrying A B C).
Proof.
intros A B C.
unfold Uncurrying.
apply (InjectionInverseMap).
Qed.

Theorem UncurryingSurjection : forall A B C,
Map_SurCond (@Uncurrying A B C).
Proof.
intros A B C.
unfold Uncurrying.
apply (SurjectionInverseMap).
Qed.

Theorem UncurryingTheorem : forall {A B C} (f : #(Map A (Map B C))) (a : #A) (b : #B),
%(%Uncurrying f) [a;b] == %(%f a) b.
Proof.
intros A B C f a b.
apply (TransitivityEq (%(%(%Currying (%Uncurrying f)) a) b)).
 rewrite CurryingTheorem.
 hyperreflexivity.
unfold Uncurrying.
apply MapEq.
apply MapEq.
rewrite (MapInverseTheoremRC _ _ _).
hyperreflexivity.
Qed.


(*Binary Map*)
Definition InverseBinaryMap {A B X} : #(Map (Map (Cartesian A B) X) (Map (Cartesian B A) X)) :=
(%CombMap' InversePair).

Theorem InverseBinaryMapTheorem : forall {A B X} (f : #(Map (Cartesian A B) X)),
forall a b,
%(%InverseBinaryMap f) [b;a] == %f [a;b].
Proof.
intros A B X f a b.
unfold InverseBinaryMap.
rewrite CombMap'Theorem.
apply MapArgEq.
apply InversePairTheorem.
Qed.

Definition LeftMove {A B X} : #(Map (Map (Cartesian A B) X) (Map A (Map B X))) := Currying.
Definition RightMove {A B X} : #(Map (Map (Cartesian A B) X) (Map B (Map A X))) :=
%CombineMap' [InverseBinaryMap; LeftMove].

Theorem LeftMoveTheorem : forall {A B X} (f : (#Map (Cartesian A B) X)), forall a b,
(%(%(%LeftMove f) a) b) == %f[a;b].
Proof.
intros A B X f a b.
unfold LeftMove.
apply CurryingTheorem.
Qed.

Theorem RightMoveTheorem : forall {A B X} (f : (#Map (Cartesian A B) X)), forall a b,
(%(%(%RightMove f) b) a) == %f[a;b].
Proof.
intros A B X f a b.
unfold RightMove.
apply (TransitivityEq (%(%(%LeftMove (%InverseBinaryMap f)) b) a)).
 apply MapEqAll.
 hyperreflexivity.
 apply MapEq.
 apply CombineMap'Theorem.
apply (TransitivityEq (%(%InverseBinaryMap f) [b;a])).
 apply LeftMoveTheorem.
apply InverseBinaryMapTheorem.
Qed.


Definition DoubleMap {A B X Y} : #(Map (Cartesian (Map A X) (Map B Y)) (Map (Cartesian A B) (Cartesian X Y))) :=
%CombineMap' [%CartesianDMap [%CombineMap'[MLeft; (%CombMap' MLeft)] ; %CombineMap'[MRight; (%CombMap' MRight)]] ; CartesianDMap].

Theorem DoubleMapTheorem : forall {A B X Y} (f : #(Map A X)) (g : #(Map B Y)) a b,
%(%DoubleMap [f;g]) [a;b] == [%f a; %g b].
Proof.
intros A B X Y f g a b.
unfold DoubleMap.
rewrite (MapEq (CombineMap'Theorem _ _ _ _ _ _)).
rewrite (MapEq (MapArgEq _ (CartesianDMapTheorem _ _ _))).
rewrite (CartesianDMapTheorem _ _ _).
apply EqualInPair'.
split.
 rewrite (MapEq (CombineMap'Theorem _ _ _ _ _ _)).
 rewrite (CombMap'Theorem _ _ _ _ _ _).
 rewrite (MapArgEq _ (LeftPairTheorem _ _)).
 apply MapEq.
apply LeftPairTheorem.

 rewrite (MapEq (CombineMap'Theorem _ _ _ _ _ _)).
 rewrite (CombMap'Theorem _ _ _ _ _ _).
 rewrite (MapArgEq _ (RightPairTheorem _ _)).
 apply MapEq.
 apply RightPairTheorem.
Qed.

(* CombineRelation *)
Definition CombineRelation' {A B C} : #(Map (Cartesian (Relation B C) (Relation A B)) (Relation A C)) := %InverseBinaryMap (@CombineRelation A B C).

Theorem CombineRelation'Theorem : forall {A B C} (rel1 : #(Relation A B)) (rel2 : #(Relation B C)),
forall (a : #A) (c : #C),
&&(%CombineRelation' [rel2; rel1]) a c <->
(exists b : #B, (&&rel1 a b) /\ (&&rel2 b c)).
Proof.
intros A B C rel1 rel2 a c.
split.
 intro relH.
 unfold CombineRelation' in relH.
 apply (RelRewrite (InverseBinaryMapTheorem _ _ _)) in relH.
 apply CombineRelationTheorem in relH.
 apply relH.

intro cond.
unfold CombineRelation'.
apply (RelRewrite' (InverseBinaryMapTheorem _ _ _)).
apply (CombineRelationTheorem).
apply cond.
Qed.


Definition CombRelation {A B C} : #(Map (Relation A B) (Map (Relation B C) (Relation A C))) := %Currying (@CombineRelation A B C).

Theorem CombRelationTheorem : forall {A B C} (rel1 : #(Relation A B)) (rel2 : #(Relation B C)) (a : #A) (c : #C),
&&(%(%CombRelation rel1) rel2) a c <->
(exists b : #B, (&&rel1 a b) /\ (&&rel2 b c)).
Proof.
intros A B C rel1 rel2 a c.
split.
 intro relH.
 unfold CombRelation in relH.
 apply (RelRewrite (CurryingTheorem _ _ _)) in relH.
 apply CombineRelationTheorem in relH.
 apply relH.

intro cond.
unfold CombRelation.
apply (RelRewrite' (CurryingTheorem _ _ _)).
apply CombineRelationTheorem.
apply cond.
Qed.



Definition CombRelation' {A B C} : #(Map (Relation B C) (Map (Relation A B) (Relation A C))) := %Currying (@CombineRelation' A B C).

Theorem CombRelation'Theorem : forall {A B C} (rel1 : #(Relation A B)) (rel2 : #(Relation B C)) (a : #A) (c : #C),
&&(%(%CombRelation' rel2) rel1) a c <->
(exists b : #B, (&&rel1 a b) /\ (&&rel2 b c)).
Proof.
intros A B C rel2 rel1 a c.
split.
 intro relH.
 unfold CombRelation in relH.
 apply (RelRewrite (CurryingTheorem _ _ _)) in relH.
 apply CombineRelation'Theorem in relH.
 apply relH.

intro cond.
unfold CombRelation'.
apply (RelRewrite' (CurryingTheorem _ _ _)).
apply CombineRelation'Theorem.
apply cond.
Qed.



(* RistrictionD *)
Theorem RistableMapDIn : forall {A B S} (f : #(Map A B)) (sub : Subset S A),
In f (RistableMap A B S B).
Proof.
intros A B S f sub.
apply RistableMapTheorem.
split.
{
  split.
  assumption.
  apply ReflexivitySubset.
}
intros a InaS.
apply MapIn. 
Qed.

Definition RistrictRistableMapRUnq : forall {A B S} (sub : Subset S A),
In (@RistrictRelationL A S B sub) (RistableMap (Relation A B) (Relation S B) (RightUnique A B) (RightUnique S B)).
Proof.
intros A B S sub.
apply RistableMapTheorem.
split.
{
  split.
  apply RUnq_Rel.
  apply RUnq_Rel.
}
intros rel InrelRU.
apply Rel_RUnq.
intros s b1 b2 HH1 HH2.
apply (StrongRelationRelExists _ _ _ _ (StrongRelRistrictL _ _ _ _ _)) in HH1.
apply (StrongRelationRelExists _ _ _ _ (StrongRelRistrictL _ _ _ _ _)) in HH2.
destruct HH1 as [InsA1 HH1].
destruct HH1 as [InbB1 HH1].
destruct HH2 as [InsA2 HH2].
destruct HH2 as [InbB2 HH2].
apply Rel_RUnq in InrelRU.
rewrite <- (DSETEq _ InbB1).
rewrite <- (DSETEq _ InbB2).
apply (Atmost'EqApply _ (InrelRU {s!InsA1})).
 split.
 apply HH1.
 apply HH2.
Qed.

Definition RistrictRistableMapLTl : forall {A B S} (sub : Subset S A),
In (@RistrictRelationL A S B sub) (RistableMap (Relation A B) (Relation S B) (LeftTotal A B) (LeftTotal S B)).
Proof.
intros A B S sub.
apply RistableMapTheorem.
split.
{
  split.
  apply LTtl_Rel.
  apply LTtl_Rel.
}
intros rel InrelLT.
apply Rel_LTtl.
intros s.
assert(InsA : In s A).
 apply sub.
 apply SetProp.
apply Rel_LTtl in InrelLT.
destruct (InrelLT {s ! InsA}) as [b relH].
exists b.
apply ToRistrictRelationL.
apply relH.
Qed.

Definition RistrictRistableMapMap : forall {A B S} (sub : Subset S A),
In (@RistrictRelationL A S B sub) (RistableMap (Relation A B) (Relation S B) (Map A B) (Map S B)).
Proof.
intros A B S sub.
apply RistableMapTheorem.
split.
{
  split.
  apply Map_Rel.
  apply Map_Rel.
}
intros rel InrelM.
apply Rel_Map2.
split.
 apply Rel_LTtl.
 put (@RistrictRistableMapLTl A B S sub) LC.
 apply RistableMapTheorem in LC.
 destruct LC as [[T1 T2] LC].
 apply LC.
 apply Map_LTtl.
 apply InrelM.

 apply Rel_RUnq.
 put (@RistrictRistableMapRUnq A B S sub) RC.
 apply RistableMapTheorem in RC.
 destruct RC as [[T1 T2] RC].
 apply RC.
 apply Map_RUnq.
 apply InrelM.
Qed.

Definition RistrictMapD {A S B} (sub : Subset S A) : #(Map (Map A B) (Map S B)) :=
  %RistMap {_!@RistrictRistableMapMap A B S sub}.

Theorem StrongRistrictMapD : forall {A S B} (sub : Subset S A) (f : #(Map A B)),
StrongRel (%(RistrictMapD sub) f){<Map_Rel} (f{<Map_Rel}).
Proof.
intros A S B sub f.
unfold RistrictMapD.
apply (TransitivityStrongRel (%(RistrictRelationL sub) (f{<Map_Rel}))).
 apply ReflexivityStrongRel2.
 rewrite (USETEq _ Map_Rel).
 apply MapStrong.
  apply StrongRistMapEq.
  hyperreflexivity.
 hyperreflexivity.
apply StrongRelRistrictL.
Qed.

Theorem RistrictMapDEq : forall {A S B} (sub : Subset S A) (f : #(Map A B)) (sa : #S) (a : #A),
sa == a -> %(%(RistrictMapD sub) f) sa == %f a.
Proof.
intros A S B sub f sa a Eqa.
apply MapStrong.
apply StrongRistrictMapD.
apply Eqa.
Qed.

Theorem RistrictMapDEqSubp : forall {A S B} (sub : Subset S A) (f : #(Map A B)) (a : #S),
%(%(RistrictMapD sub) f) a == %f (a{<sub}).
Proof.
intros A S B sub f a.
apply MapStrong.
apply StrongRistrictMapD.
hyperreflexivity.
Qed.

(* RistrictRMap *)
Definition RistableRMap A B SB := RistableMap A B A SB.

Theorem RistableRMapTheorem : forall {A B} SB (f : #(Map A B)),
In f (RistableRMap A B SB) <-> 
Subset SB B /\ forall (a : #A), In (%f a) SB.
Proof.
intros A B SB f.
split.

intro InfR.
unfold RistableRMap in InfR.
apply RistableMapTheorem in InfR.
destruct InfR as [[SubA SubB] InfR].
split.
assumption.
intro a.
apply InfR.
apply SetProp.

intro Cond.
destruct Cond as [SubB Cond].
unfold RistableRMap.
apply RistableMapTheorem.
split.
{
  split.
  apply ReflexivitySubset.
  assumption.
}
intros a InaA.
apply Cond.
Qed.


Theorem RistableRMap_Map {A B S} : Subset (RistableRMap A B S) (Map A B).
Proof.
unfold RistableRMap.
apply RistableMap_Map.
Qed.

Theorem RistableRMapTheoremSub : forall A B SB, 
NonEmpty (RistableRMap A B SB) -> Subset SB B.
Proof.
intros A B SB NER.
destruct NER as [f NER].
assert(InfM : In f (Map A B)).
 apply RistableRMap_Map in NER.
 assumption.
rewrite (DSETEq' _ InfM) in NER.
apply RistableRMapTheorem in NER.
destruct NER.
assumption.
Qed.

Theorem RistableRMapTheoremIn : forall {A B} SB (f : #(Map A B)),
In f (RistableRMap A B SB) -> 
forall (a : #A), In (%f a) SB.
Proof.
intros A B SB f InfR.
apply RistableRMapTheorem in InfR.
destruct InfR as [Sub InfR].
apply InfR.
Qed.



Definition RistrictMapR {A B S} : #(Map (RistableRMap A B S) (Map A S)) :=
RistMap.

Theorem StrongRistrictMapR : forall {A B S} (f : #(RistableRMap A B S)),
StrongRel (%RistrictMapR f){<Map_Rel} (f{<RistableRMap_Map}{<Map_Rel}).
Proof.
intros A B S f.
unfold RistrictMapR.
apply (TransitivityStrongRel (f{<RistableMap_Map}{<Map_Rel})).
 cut (StrongMap (%RistMap f) (f{<RistableMap_Map})).
  intro STH.
  apply STH.
 apply StrongRistMapEq.
 hyperreflexivity.
apply StrongRelRewrite.
hyperreflexivity.
Qed.


Theorem StrongRistrictMapR2 : forall {A B S} (f : #(Map A B)) (cond : In f (RistableRMap A B S)),
StrongRel ((%RistMap {f ! cond}){<Map_Rel}) (f{<Map_Rel}).
Proof.
intros A B S f cond.
apply (TransitivityStrongRel ({f ! cond}{<RistableRMap_Map}{<Map_Rel})).
 apply StrongRistrictMapR.
apply ReflexivityStrongRel2.
hyperreflexivity.
Qed.

Theorem RistrictMapREq : forall {A B S} (f : #(RistableRMap A B S)),
(%RistrictMapR f) == f.
Proof.
intros A B S f.
apply (TransitivityEq (f{<RistableRMap_Map})).
apply MapStrongSameDomain.
apply StrongRistrictMapR.
hyperreflexivity.
Qed.

Theorem RistrictMapREq2 : forall {A B S} (f : #(Map A B)) (cond : In f (RistableRMap A B S)),
(%RistrictMapR {f ! cond}) == f.
Proof.
intros A B S f cond.
apply MapStrongSameDomain.
apply (StrongRistrictMapR2 f cond).
Qed.

Definition RistrictMapREq' {A B S} (f : #(RistableRMap A B S)) := SymmetryEq _ _ (RistrictMapREq f).
Definition RistrictMapREq2' {A B S} (f : #(Map A B)) (cond : In f (RistableRMap A B S)) :=
SymmetryEq _ _ (RistrictMapREq2 f cond).

(* ExpandRMap *)
Theorem ExpandRRistableRUnq : forall A B X (sub : Subset B X),
In (@ExpandRelationR A B X sub) (RistableMap (Relation A B) (Relation A X) (RightUnique A B) (RightUnique A X)).
Proof.
intros A B X sub.
apply RistableMapTheorem.
split.
{
  split.
  apply RUnq_Rel.
  apply RUnq_Rel.
}
intros rel InrelR.
apply Rel_RUnq.
intro a.
intros b1 b2 H1 H2.
apply Rel_RUnq in InrelR.
put (ExpandRelationREq sub rel) eqE.
apply RelEquality in eqE.
destruct eqE as [SR1 SR2].
put (StrongRelationRelExists _ _ _ _ SR1 H1) H1'.
put (StrongRelationRelExists _ _ _ _ SR1 H2) H2'.
destruct H1' as [InaA1 H1'].
destruct H1' as [Inb1B H1'].
destruct H2' as [InaA2 H2'].
destruct H2' as [Inb2B H2'].
set {b1 ! Inb1B} as b1'.
set {b2 ! Inb2B} as b2'.
apply (TransitivityEq b1').
hyperreflexivity.
apply (TransitivityEq b2').
 apply (Atmost'EqApply _ (InrelR a)).
 split.
  generalize H1'.
  apply RelRewriteAll; hyperreflexivity.
 generalize H2'.
 apply RelRewriteAll; hyperreflexivity.
hyperreflexivity.
Qed.

Theorem ExpandRRistableLTtl : forall A B X (sub : Subset B X),
In (@ExpandRelationR A B X sub) (RistableMap (Relation A B) (Relation A X) (LeftTotal A B) (LeftTotal A X)).
Proof.
intros A B X sub.
apply RistableMapTheorem.
split.
{
  split.
  apply LTtl_Rel.
  apply LTtl_Rel.
}
intros rel InrelL.
apply Rel_LTtl in InrelL.
apply Rel_LTtl.
intros a.
destruct (InrelL a) as [b InrelL'].
exists (b{<sub}).
generalize InrelL'.
apply RelRewriteAll.
hyperreflexivity.
hyperreflexivity.
apply SymmetryEq.
apply ExpandRelationREq.
Qed.

Theorem ExpandRRistableMap : forall A B X (sub : Subset B X),
In (@ExpandRelationR A B X sub) (RistableMap (Relation A B) (Relation A X) (Map A B) (Map A X)).
Proof.
intros A B X sub.
apply RistableMapTheorem.
split.
{
  split.
  apply Map_Rel.
  apply Map_Rel.
}
intros rel InrelM.
apply Rel_Map2.
split.
 apply Rel_LTtl.
 put (ExpandRRistableLTtl A B X sub) EL.
 apply RistableMapTheorem in EL.
 destruct EL as [[EL1 EL2] EL3].
 apply EL3.
 apply Map_LTtl.
 assumption.

 apply Rel_RUnq.
 put (ExpandRRistableRUnq A B X sub) ER.
 apply RistableMapTheorem in ER.
 destruct ER as [[ER1 ER2] ER3].
 apply ER3.
 apply Map_RUnq.
 assumption.
Qed.

Definition ExpandRMap {A B X} (sub : Subset B X) : #(Map (Map A B) (Map A X)) :=
(%RistMap {_ ! (ExpandRRistableMap A B X sub)}).

Theorem ExpandRMapEq : forall {A B X} (sub : Subset B X) (f : #(Map A B)),
(%(ExpandRMap sub) f) == f.
Proof.
intros A B X sub f.
apply (TransitivityEq (%(ExpandRelationR sub) (f{<Map_Rel}))).
 apply MapStrong.
  unfold ExpandRMap.
  apply StrongRistMapEq.
  hyperreflexivity.
 hyperreflexivity.
apply ExpandRelationREq.
Qed.

(* ID CONST *)
Definition ConstMap {A B} : #(Map A (Map B A)) := %Currying MLeft.

Theorem ConstMapTheorem : forall {A B} a b,
%(%(@ConstMap A B) a) b == a.
Proof.
intros A B a b.
unfold ConstMap.
rewrite CurryingTheorem.
apply LeftPairTheorem.
Qed.

Definition IdMap' {A B} : #(Map A (Map B B)) := %Currying MRight.

Definition IdMap {A} : #(Map A A).
assert(InE : In Empty (Singleton Empty)).
 apply SingletonTheorem.
 apply ReflexivityEq.
apply (%IdMap' {Empty!InE}).
Defined.

Theorem IdMapTheorem : forall A, forall a,
%(@IdMap A) a == a.
Proof.
intros A a.
unfold IdMap.
unfold IdMap'.
rewrite CurryingTheorem.
apply RightPairTheorem.
Qed.

Definition EmbedMap {A B} (sub : Subset A B) : #(Map A B) :=
%(ExpandRMap sub) IdMap.

Theorem EmbedMapIdMap : forall {A B} (sub : Subset A B),
(@IdMap A) == (@EmbedMap A B sub).
Proof.
intros A B sub.
unfold EmbedMap.
rewrite (ExpandRMapEq sub IdMap).
hyperreflexivity.
Qed.

Theorem EmbedMapEq : forall {A B} (sub : Subset A B),
forall (a : #A),
(%(EmbedMap sub) a) == a.
Proof.
intros A B sub a.
apply (TransitivityEq (%IdMap a)).
 apply MapEq.
 rewrite (EmbedMapIdMap sub).
 hyperreflexivity.
apply IdMapTheorem.
Qed.

Definition IdRel {A} : #(BRelation A) := (@IdMap A){<Map_Rel}.

Theorem IdRelTheorem : forall {A} (a : #A),
&&IdRel a a.
Proof.
intros A a.
unfold IdRel.
cut (&&(IdMap{<Map_Rel}) a (%IdMap a)).
 apply RelRewriteR.
 apply IdMapTheorem.
apply AppTheorem.
Qed.


(* Relation as Pair *)
Definition RelationAsPairL {A B} (rel : #(Relation A B)) : #(Map rel A) :=
%CombineMap' [EmbedMap (Relation_Cartesian _ _ _) ; MLeft].
Definition RelationAsPairR {A B} (rel : #(Relation A B)) : #(Map rel B) :=
%CombineMap' [EmbedMap (Relation_Cartesian _ _ _) ; MRight].

Theorem RelationAsPairLEqWP : forall {A B A' B'} (rel : #(Relation A B)) (a : #A') (b : #B') (cond : In [a;b] rel),
%(RelationAsPairL rel) {[a;b] ! cond} == a.
Proof.
intros A B A' B' rel a b cond.
put (IsPair'Relation _ _ _ _ cond) Eqrel.
destruct Eqrel as [aa Eqrel].
destruct Eqrel as [bb Eqrel].
assert(cond' : In [aa;bb] rel).
 rewrite <- Eqrel.
 apply cond.
apply (TransitivityEq (%(RelationAsPairL rel) {[aa;bb] ! cond'})).
 apply MapArgEq.
 rewrite (DSETEq _ cond).
 rewrite (DSETEq _ cond').
 apply Eqrel.
unfold RelationAsPairL.
rewrite CombineMap'Theorem.
apply (TransitivityEq (%MLeft [aa;bb])).
 apply MapArgEq.
 rewrite EmbedMapEq.
 hyperreflexivity.
apply (TransitivityEq aa).
 apply LeftPairTheorem.
apply SymmetryEq.
apply EqualInPair' in Eqrel.
apply (proj1 Eqrel).
Qed.

Theorem RelationAsPairREqWP : forall {A B A' B'} (rel : #(Relation A B)) (a : #A') (b : #B') (cond : In [a;b] rel),
%(RelationAsPairR rel) {[a;b] ! cond} == b.
Proof.
intros A B A' B' rel a b cond.
put (IsPair'Relation _ _ _ _ cond) Eqrel.
destruct Eqrel as [aa Eqrel].
destruct Eqrel as [bb Eqrel].
assert(cond' : In [aa;bb] rel).
 rewrite <- Eqrel.
 apply cond.
apply (TransitivityEq (%(RelationAsPairR rel) {[aa;bb] ! cond'})).
 apply MapArgEq.
 rewrite (DSETEq _ cond).
 rewrite (DSETEq _ cond').
 apply Eqrel.
unfold RelationAsPairR.
rewrite CombineMap'Theorem.
apply (TransitivityEq (%MRight [aa;bb])).
 apply MapArgEq.
 rewrite EmbedMapEq.
 hyperreflexivity.
apply (TransitivityEq bb).
 apply RightPairTheorem.
apply SymmetryEq.
apply EqualInPair' in Eqrel.
apply (proj2 Eqrel).
Qed.


(* Left_or_Right Combine *)
Definition LeftCombineMapC {L1 L2 R X} : #(Map (Cartesian (Map L2 (Map R X)) (Map L1 L2)) (Map L1 (Map R X))) :=
@CombineMap L1 L2 (Map R X).

Definition LeftCombineMap'C {L1 L2 R X} : #(Map (Cartesian (Map L1 L2) (Map L2 (Map R X))) (Map L1 (Map R X))) :=
@CombineMap' L1 L2 (Map R X).

Definition LeftCombineMap {L1 L2 R X} : #(Map (Cartesian (Map (Cartesian L2 R) X) (Map L1 L2)) (Map (Cartesian L1 R) X)) :=
%CombineMap' [ (%DoubleMap [Currying ; IdMap]) ; %CombineMap'[(@LeftCombineMapC L1 L2 R X) ; Uncurrying]].

Definition LeftCombineMap' {L1 L2 R X} : #(Map (Cartesian (Map L1 L2) (Map (Cartesian L2 R) X)) (Map (Cartesian L1 R) X)) :=
%CombineMap' [ (%DoubleMap [IdMap; Currying]) ; %CombineMap'[(@LeftCombineMap'C L1 L2 R X) ; Uncurrying]].

Definition RightCombineMap' {L R1 R2 X} : #(Map (Cartesian (Map R1 R2) (Map (Cartesian L R2) X)) (Map (Cartesian L R1) X)) :=
%CombineMap' [ (%DoubleMap [IdMap ; InverseBinaryMap]) ; %CombineMap' [@LeftCombineMap' R1 R2 L X ; InverseBinaryMap]].

Definition RightCombineMap {L R1 R2 X} : #(Map (Cartesian (Map (Cartesian L R2) X) (Map R1 R2)) (Map (Cartesian L R1) X)) :=
%CombineMap' [ (%DoubleMap [InverseBinaryMap ; IdMap]) ; %CombineMap' [@LeftCombineMap R1 R2 L X ; InverseBinaryMap]].

Definition RightCombineMapC {L R1 R2 X} : #(Map (Cartesian (Map L (Map R2 X)) (Map R1 R2)) (Map L (Map R1 X))) :=
%CombineMap' [ (%DoubleMap [@Uncurrying L R2 X; IdMap]) ; %CombineMap' [RightCombineMap ; Currying]].

Definition RightCombineMap'C {L R1 R2 X} : #(Map (Cartesian (Map R1 R2) (Map L (Map R2 X))) (Map L (Map R1 X))) :=
%CombineMap' [ (%DoubleMap [IdMap; @Uncurrying L R2 X]) ; %CombineMap' [RightCombineMap' ; Currying]].

Theorem LeftCombineMapCTheorem : forall {L1 L2 R X} (f : #(Map L2 (Map R X))) (g : #(Map L1 L2)) (a : #L1),
(%(%LeftCombineMapC [f;g]) a) == (%f (%g a)).
Proof.
intros L1 L2 R X f g a.
unfold LeftCombineMapC.
rewrite (CombineMapTheorem _ _ _).
hyperreflexivity.
Qed.

Theorem LeftCombineMap'CTheorem : forall {L1 L2 R X} (f : #(Map L2 (Map R X))) (g : #(Map L1 L2)) (a : #L1),
(%(%LeftCombineMap'C [g;f]) a) == (%f (%g a)).
Proof.
intros L1 L2 R X f g a.
unfold LeftCombineMap'C.
rewrite (CombineMap'Theorem _ _ _).
hyperreflexivity.
Qed.

Theorem LeftCombineMapTheorem : forall {L1 L2 R X} (f : #(Map (Cartesian L2 R) X)) (g : #(Map L1 L2)) (a : #L1) (b : #R),
(%(%LeftCombineMap [f;g]) [a;b]) == (%f [%g a; b]).
Proof.
intros L1 L2 R X f g a b.
unfold LeftCombineMap.
rewrite (MapEq (CombineMap'Theorem _ _ _ _ _ _)).
rewrite (MapEq (CombineMap'Theorem _ _ _ _ _ _)).
rewrite (UncurryingTheorem _ _ _).
rewrite (MapEq (MapEq (MapArgEq _ (DoubleMapTheorem _ _ _ _)))).
rewrite (MapEq (LeftCombineMapCTheorem _ _ _)).
rewrite (CurryingTheorem _ _ _).
apply MapArgEq.
apply EqualInPair'.
split.
 apply MapEq.
 rewrite (IdMapTheorem).
 hyperreflexivity.
hyperreflexivity.
Qed.

Theorem LeftCombineMap'Theorem : forall {L1 L2 R X} (f : #(Map (Cartesian L2 R) X)) (g : #(Map L1 L2)) (a : #L1) (b : #R),
(%(%LeftCombineMap' [g;f]) [a;b]) == (%f [%g a; b]).
Proof.
intros L1 L2 R X f g a b.
unfold LeftCombineMap'.
rewrite (MapEq (CombineMap'Theorem _ _ _ _ _ _)).
rewrite (MapEq (CombineMap'Theorem _ _ _ _ _ _)).
rewrite (UncurryingTheorem _ _ _).
rewrite (MapEq (MapEq (MapArgEq _ (DoubleMapTheorem _ _ _ _)))).
rewrite (MapEq (LeftCombineMap'CTheorem _ _ _)).
rewrite (CurryingTheorem _ _ _).
apply MapArgEq.
apply EqualInPair'.
split.
 apply MapEq.
 rewrite (IdMapTheorem).
 hyperreflexivity.
hyperreflexivity.
Qed.

Theorem RightCombineMapTheorem : forall {L R1 R2 X} (f : #(Map (Cartesian L R2) X)) (g : #(Map R1 R2)) (a : #L) (b : #R1),
(%(%RightCombineMap [f;g]) [a;b]) == (%f [a; %g b]).
Proof.
intros L R1 R2 X f g a b.
unfold RightCombineMap.
rewrite (MapEq (CombineMap'Theorem _ _ _ _ _ _)).
rewrite (MapEq (CombineMap'Theorem _ _ _ _ _ _)).
rewrite (InverseBinaryMapTheorem _ _ _).
rewrite (MapEq (MapArgEq _ (DoubleMapTheorem _ _ _ _))).
rewrite (LeftCombineMapTheorem _ _ _).
rewrite (InverseBinaryMapTheorem _ _ _).
apply MapArgEq.
apply EqualInPair'.
split.
hyperreflexivity.
apply MapEq.
rewrite IdMapTheorem.
hyperreflexivity.
Qed.

Theorem RightCombineMap'Theorem : forall {L R1 R2 X} (f : #(Map (Cartesian L R2) X)) (g : #(Map R1 R2)) (a : #L) (b : #R1),
(%(%RightCombineMap' [g;f]) [a;b]) == (%f [a; %g b]).
Proof.
intros L R1 R2 X f g a b.
unfold RightCombineMap'.
rewrite (MapEq (CombineMap'Theorem _ _ _ _ _ _)).
rewrite (MapEq (CombineMap'Theorem _ _ _ _ _ _)).
rewrite (InverseBinaryMapTheorem _ _ _).
rewrite (MapEq (MapArgEq _ (DoubleMapTheorem _ _ _ _))).
rewrite (LeftCombineMap'Theorem _ _ _).
rewrite (InverseBinaryMapTheorem _ _ _).
apply MapArgEq.
apply EqualInPair'.
split.
hyperreflexivity.
apply MapEq.
rewrite IdMapTheorem.
hyperreflexivity.
Qed.

Theorem RightCombineMapCTheorem : forall {L R1 R2 X} (f : #(Map L (Map R2 X))) (g : #(Map R1 R2)) (a : #L) (b : #R1),
(%(%(%RightCombineMapC [f;g]) a) b) == (%(%f a) (%g b)).
Proof.
intros L R1 R2 X f g a b.
unfold RightCombineMapC.
rewrite (MapEq (MapEq (CombineMap'Theorem _ _ _ _ _ _))).
rewrite (MapEq (MapEq (CombineMap'Theorem _ _ _ _ _ _))).
rewrite (CurryingTheorem _ _ _).
rewrite (MapEq (MapArgEq _ (DoubleMapTheorem _ _ _ _))).
rewrite (RightCombineMapTheorem _ _ _).
rewrite (UncurryingTheorem _ _ _).
apply MapArgEq.
apply MapEq.
rewrite (IdMapTheorem).
hyperreflexivity.
Qed.

Theorem RightCombineMap'CTheorem : forall {L R1 R2 X} (f : #(Map L (Map R2 X))) (g : #(Map R1 R2)) (a : #L) (b : #R1),
(%(%(%RightCombineMap'C [g;f]) a) b) == (%(%f a) (%g b)).
Proof.
intros L R1 R2 X f g a b.
unfold RightCombineMap'C.
rewrite (MapEq (MapEq (CombineMap'Theorem _ _ _ _ _ _))).
rewrite (MapEq (MapEq (CombineMap'Theorem _ _ _ _ _ _))).
rewrite (CurryingTheorem _ _ _).
rewrite (MapEq (MapArgEq _ (DoubleMapTheorem _ _ _ _))).
rewrite (RightCombineMap'Theorem _ _ _ _).
rewrite (UncurryingTheorem _ _ _).
apply MapArgEq.
apply MapEq.
rewrite IdMapTheorem.
hyperreflexivity.
Qed.



(* MapIntoRelationL *)
Definition MapIntoRelationL {A B C} : #(Map (Cartesian (Map A B) (Relation B C)) (Relation A C)).
assert(sub : Subset (Cartesian (Map A B) (Relation B C)) (Cartesian (Relation A B) (Relation B C))).
 apply SubsetInCartesianL.
  apply Map_Rel.
apply (%(RistrictMapD sub) CombineRelation).
Defined.

Theorem MapIntoRelationLTheorem : forall {A B C} (f : #(Map A B)) (rel : #(Relation B C)),
forall a c,
&&(%MapIntoRelationL [f;rel]) a c <->
(&&rel (%f a) c).
Proof.
intros A B C f rel a c.
assert(subp : Subset (Cartesian (Map A B) (Relation B C)) (Cartesian (Relation A B) (Relation B C))).
 apply SubsetInCartesianL.
 apply Map_Rel.
split.
 intro MH.
 unfold MapIntoRelationL in MH.
 assert(MH' : &&(%CombineRelation [f{<Map_Rel} ; rel]) a c).
  generalize MH.
  apply RelRewrite.
  apply MapStrong.
  apply StrongRistrictMapD.
  hyperreflexivity.
 clear MH.
 apply CombineRelationTheorem in MH'.
 destruct MH' as [b MH].
 destruct MH as [MH1 MH2].
 generalize MH2.
 apply RelRewriteL.
 assert(MC : Rel_MapCond (f{<Map_Rel})).
  apply Rel_Map.
  apply (SetProp f).
 apply (Unique'EqApply _ (MC a)).
 split.
 apply MH1.
 apply AppTheorem.

 intro relH.
 cut (&&(%CombineRelation [(f{<Map_Rel});rel]) a c).
  apply RelRewrite.
  unfold MapIntoRelationL.
  apply SymmetryEq.
  apply MapStrong.
  apply StrongRistrictMapD.
  hyperreflexivity.
 apply CombineRelationTheorem.
 exists (%f a).
 split.
 apply AppTheorem.
 apply relH.
Qed.

Definition MapIntoRelationR {A B C} : #(Map (Cartesian (Map A C) (Relation B C)) (Relation B A)) :=
%CombineMap' [(%DoubleMap [IdMap ; InverseRel]) ; %CombineMap' [(@MapIntoRelationL A C B) ; InverseRel]].

Theorem MapIntoRelationRTheorem : forall {A B C} (f : #(Map A C)) (rel : #(Relation B C)),
forall (a : #A) (b : #B),
&&(%MapIntoRelationR [f;rel]) b a <->
(&&rel b (%f a)).
Proof.
intros A B C f rel a b.
split.
 intro InMH.
 unfold MapIntoRelationR in InMH.
 apply (RelRewrite (CombineMap'Theorem _ _ _ _ _ _)) in InMH.
 apply (RelRewrite (CombineMap'Theorem _ _ _ _ _ _)) in InMH.
 apply InverseRelTheorem in InMH.
 apply (RelRewrite (MapArgEq _ (DoubleMapTheorem _ _ _ _))) in InMH.
 apply MapIntoRelationLTheorem in InMH.
 apply InverseRelTheorem in InMH.
 apply (RelRewriteR (MapEq (IdMapTheorem _ _))) in InMH.
 apply InMH.


 intro relH.
 unfold MapIntoRelationR.
 apply (RelRewrite' (CombineMap'Theorem _ _ _ _ _ _)).
 apply (RelRewrite' (CombineMap'Theorem _ _ _ _ _ _)).
 apply InverseRelTheorem'.
 apply (RelRewrite' (MapArgEq _ (DoubleMapTheorem _ _ _ _))).
 apply MapIntoRelationLTheorem.
 apply InverseRelTheorem'.
 apply (RelRewriteR (MapEq' (IdMapTheorem _ _))).
 apply relH.
Qed.


(* ValueMap *)
Definition RelCheck {A B} : #(Relation (Relation A B) (Cartesian A B)) :=
  %InverseRel (@InRelation (Cartesian A B) (Relation A B)).

Theorem RelCheckTheorem : forall {A B} (rel : #(Relation A B)) (a : #A) (b : #B),
&&RelCheck rel [a;b] <-> &&rel a b.
Proof.
intros A B rel a b.
split.

intro RelH.
unfold RelCheck in RelH.
apply InverseRelTheorem in RelH.
apply InRelationTheorem in RelH.
apply RelH.

intro relH.
unfold RelCheck.
apply InverseRelTheorem'.
apply InRelationTheorem.
apply relH.
Qed.

Theorem RelCheckTheorem' : forall {A B} (rel : #(Relation A B)) (a : #A) (b : #B),
&&rel a b <-> &&RelCheck rel [a;b].
Proof.
intros A B rel a b.
apply SymmetryEquiv.
apply RelCheckTheorem.
Qed.

Definition RelCheckA {A B} : #(Relation (Cartesian (Relation A B) A) B) :=
  %AssocRelationRL RelCheck.

Theorem RelCheckATheorem : forall {A B} (rel : #(Relation A B)) (a : #A) (b : #B),
&&RelCheckA [rel;a] b <-> &&rel a b.
Proof.
intros A B rel a b.
split.

intro RelH.
unfold RelCheckA in RelH.
apply AssocRelationRLTheorem in RelH.
unfold RelCheck in RelH.
apply RelCheckTheorem' in RelH.
apply RelH.

intro relH.
unfold RelCheckA.
apply AssocRelationRLTheorem.
unfold RelCheck.
apply RelCheckTheorem.
apply relH.
Qed.


Theorem RelCheckATheorem' : forall {A B} (rel : #(Relation A B)) (a : #A) (b : #B),
&&rel a b <-> &&RelCheckA [rel;a] b.
Proof.
intros A B rel a b.
apply SymmetryEquiv.
apply RelCheckATheorem.
Qed.

Definition ApplyMapRel {A B} : #(Relation (Cartesian (Map A B) A) B).
assert(sub : Subset (Cartesian (Map A B) A) (Cartesian (Relation A B) A)).
 apply SubsetInCartesianL.
 apply Map_Rel.
apply (%MapIntoRelationL [(EmbedMap sub) ; RelCheckA]).
Defined.

Theorem ApplyMapRelMapCond {A B} : Rel_MapCond (@ApplyMapRel A B).
Proof.
intros fa.
split.

put (CartesianIsPair' _ _ _ (SetProp fa)) IsPc.
destruct IsPc as [f IsPc].
destruct IsPc as [a Eqfa].
exists (%f a).
apply (RelRewriteL' Eqfa).
unfold ApplyMapRel.
apply MapIntoRelationLTheorem.
cut (&&RelCheckA [f{<Map_Rel} ; a] (%f a)).
 apply RelRewriteL.
 apply SymmetryEq.
 rewrite (EmbedMapEq _ [f;a]).
 hyperreflexivity.
apply RelCheckATheorem.
apply AppTheorem.

intros b1 b2 HD.
destruct HD as [H1 H2].
put (CartesianIsPair' _ _ _ (SetProp fa)) IsPc.
destruct IsPc as [f IsPc].
destruct IsPc as [a Eqfa].
apply (RelRewriteL Eqfa) in H1.
apply (RelRewriteL Eqfa) in H2.
unfold ApplyMapRel in H1.
unfold ApplyMapRel in H2.
apply MapIntoRelationLTheorem in H1.
apply MapIntoRelationLTheorem in H2.
assert(H1' : &&RelCheckA [f{<Map_Rel} ; a] b1).
 generalize H1.
 apply RelRewriteL.
 rewrite (EmbedMapEq _ [f;a]).
 hyperreflexivity.
assert(H2' : &&RelCheckA [f{<Map_Rel} ; a] b2).
 generalize H2.
 apply RelRewriteL.
 rewrite (EmbedMapEq _ [f;a]).
 hyperreflexivity.
clear H1.
clear H2.
apply RelCheckATheorem' in H1'.
apply RelCheckATheorem' in H2'.
assert(MU : Rel_MapCond (f{<Map_Rel})).
 apply Rel_Map.
 apply (SetProp f).
apply (Unique'EqApply _ (MU a)).
split; assumption.
Qed.

Definition ApplyMap {A B} : #(Map (Cartesian (Map A B) A) B) :=
_{<Rel_Map ! @ApplyMapRelMapCond A B}.
 
Theorem ApplyMapTheorem : forall {A B} (f : #(Map A B)) (a : #A),
%ApplyMap [f;a] == (%f a).
Proof.
intros A B f a.
apply AppTheoremReverse.
unfold ApplyMap.
cut (&&ApplyMapRel [f;a] (%f a)).
 apply RelRewrite.
 hyperreflexivity.
unfold ApplyMapRel.
apply MapIntoRelationLTheorem.
cut (&&RelCheckA [f{<Map_Rel} ; a] (%f a)).
 apply RelRewriteL.
 apply SymmetryEq.
apply (EmbedMapEq _ [f;a]).
apply RelCheckATheorem.
apply AppTheorem.
Qed.

Definition ValueMap {A B} : #(Map A (Map (Map A B) B)) :=
%Currying (%InverseBinaryMap (@ApplyMap A B)).

Theorem ValueMapTheorem : forall {A B} (a : #A) (f : #(Map A B)),
(%(%ValueMap a) f) == %f a.
Proof.
intros A B a f.
unfold ValueMap.
rewrite (CurryingTheorem _ _ _).
rewrite (InverseBinaryMapTheorem _ _ _).
apply ApplyMapTheorem.
Qed.



(* BinaryMapPower *)
Definition BinaryMapImage {A B X} : #(Map (Map (Cartesian A B) X) (Map (Cartesian (PowerSet A) (PowerSet B)) (PowerSet X))) :=
%CombineMap' [MapImage ; (%CombMap' (@MCartesian A B))].


Theorem BinaryMapImageTheorem : forall {A B X} (f : #(Map (Cartesian A B) X)) (SA : #(PowerSet A)) (SB : #(PowerSet B)),
forall x,
In x (%(%BinaryMapImage f) [SA;SB]) <-> (exists a : #A, exists b : #B, In a SA /\ In b SB /\ (%f [a;b]) == x).
Proof.
intros A B X f SA SB x.
unfold BinaryMapImage.
rewrite (MapEq (CombineMap'Theorem _ _ _ _ _ _)).
rewrite (CombMap'Theorem _ _ _ _ _ _).
assert (SubA : Subset SA A).
 put (SetProp SA) SAP.
 apply PowersetTheorem in SAP.
 assumption.
assert (SubB : Subset SB B).
 put (SetProp SB) SBP.
 apply PowersetTheorem in SBP.
 assumption.
split.
 intro InxBf.
 apply MapImageTheorem in InxBf.
 destruct InxBf as [p InxBf].
 destruct InxBf as [InpMC Eqpx].
 rewrite (MCartesianEq _ _) in InpMC.
 put (CartesianIsPair' _ _ _ InpMC) Eqp.
 destruct Eqp as [a Eqp].
 destruct Eqp as [b Eqp].
 exists (a{<SubA}).
 exists (b{<SubB}).
 split.
 apply (SetProp a).
 split.
 apply (SetProp b).
 rewrite <- Eqpx.
 apply MapArgEq.
 rewrite Eqp.
 hyperreflexivity.

 intro cond.
 destruct cond as [a cond].
 destruct cond as [b cond].
 destruct cond as [InaSA cond].
 destruct cond as [InbSB Eqfx].
 apply MapImageTheorem.
 exists [a;b].
 split.
 rewrite (MCartesianEq _ _).
 apply CartesianTheorem'.
 split; assumption.
 apply Eqfx.
Qed.


(* RelationAllImage *)
Definition RelationImageL {A B} : #(Map (Relation A B) (Map (PowerSet B) (PowerSet A))) :=
%CombineMap' [InverseRel ; RelationImageR].

Theorem RelationImageLTheorem : forall A B (rel : #(Relation A B)),
forall (SB : #(PowerSet B)),
(forall a : #A, In a (%(%RelationImageL rel) SB) <-> exists b : #B, In b SB /\ &&rel a b).
Proof.
intros A B rel SB a.
unfold RelationImageL.
rewrite (MapEq (CombineMap'Theorem _ _ _ _ _ _)).
split.
 intro RrelH.
 apply RelationImageRTheorem in RrelH.
 destruct RrelH as [b RrelH].
 destruct RrelH as [InbSB relH].
 exists b.
 split.
 assumption.
 apply InverseRelTheorem in relH.
 apply relH.

 intro cond.
 destruct cond as [b cond].
 destruct cond as [InbSB relH].
 apply RelationImageRTheorem.
 exists b.
 split.
 assumption.
 apply InverseRelTheorem'.
 apply relH.
Qed.

Theorem RelationImageLSubset : forall {A B} (rel : #(Relation A B)) (sb : #(PowerSet B)),
Subset (%(%RelationImageL rel) sb) A.
Proof.
intros A B rel sb a InaR.
unfold RelationImageL in InaR.
rewrite (MapEq (CombineMap'Theorem _ _ _ _ _ _)) in InaR.
apply RelationImageRSubset in InaR.
apply InaR.
Qed.


Definition RelationAllImageR {A B} : #(Map (Relation A B) (PowerSet B)) :=
  %CombineMap' [RelationImageR ; %(@ValueMap (PowerSet A) (PowerSet B)) {A ! PowersetHasOwn A}].

Theorem RelationAllImageREq : forall {A B} (rel : #(Relation A B)),
(%(%RelationImageR rel) {A ! PowersetHasOwn A}) == (%RelationAllImageR rel).
intros A B rel.
unfold RelationAllImageR.
rewrite (CombineMap'Theorem _ _ _).
rewrite (ValueMapTheorem _ _).
hyperreflexivity.
Qed.

Theorem RelationAllImageRIn : forall {A B} (rel : #(Relation A B)) (b : #B),
In b (%RelationAllImageR rel) <-> exists a : #A, &&rel a b.
Proof.
intros A B rel b.
rewrite <- (RelationAllImageREq _).
split.
 intro InbR.
 apply RelationImageRTheorem in InbR.
 destruct InbR as [a InbR].
 destruct InbR as [InaA relH].
 exists a.
 apply relH.

 intro relH.
 destruct relH as [a relH].
 apply RelationImageRTheorem.
 exists a.
 split.
 apply (SetProp a).
 apply relH.
Qed.

Theorem RelationAllImageRSubset : forall {A B} (rel : #(Relation A B)),
Subset (%RelationAllImageR rel) B.
Proof.
intros A B rel b InbR.
rewrite <- (RelationAllImageREq _) in InbR.
apply RelationImageRSubset in InbR.
assumption.
Qed.

Definition RelationAllImageL {A B} : #(Map (Relation A B) (PowerSet A)) :=
%CombineMap' [InverseRel ; RelationAllImageR].

Theorem RelationAllImageLEq : forall {A B} (rel : #(Relation A B)),
(%(%RelationImageL rel) {B ! PowersetHasOwn B}) == (%RelationAllImageL rel).
intros A B rel.
unfold RelationAllImageL.
rewrite (CombineMap'Theorem _ _ _).
apply EA.
intro a.
 split.
 intro InaR.
 assert(InaA : In a A).
  apply RelationImageLSubset in InaR.
  assumption.
 rewrite (DSETEq' _ InaA) in InaR.
 rewrite (DSETEq' _ InaA).
 apply RelationAllImageRIn.
 apply RelationImageLTheorem in InaR.
 destruct InaR as [b InaR].
 destruct InaR as [InbB relH].
 exists b.
 apply InverseRelTheorem'.
 apply relH.

 intro InaR.
 assert(InaA : In a A).
  apply RelationAllImageRSubset in InaR.
  assumption.
 rewrite (DSETEq' _ InaA) in InaR.
 rewrite (DSETEq' _ InaA).
 apply RelationAllImageRIn in InaR.
 destruct InaR as [b relH].
 apply InverseRelTheorem in relH.
 apply RelationImageLTheorem.
 exists b.
 split.
 apply (SetProp b).
 apply relH.
Qed.

Theorem RelationAllImageLIn : forall {A B} (rel : #(Relation A B)) (a : #A),
In a (%RelationAllImageL rel) <-> exists b : #B, &&rel a b.
Proof.
intros A B rel a.
rewrite <- (RelationAllImageLEq _).
split.
 intro InbR.
 apply RelationImageLTheorem in InbR.
 destruct InbR as [b InbR].
 destruct InbR as [InbB relH].
 exists b.
 apply relH.

 intro relH.
 destruct relH as [b relH].
 apply RelationImageLTheorem.
 exists b.
 split.
 apply (SetProp b).
 apply relH.
Qed.

Theorem RelationAllImageLSubset : forall {A B} (rel : #(Relation A B)),
Subset (%RelationAllImageL rel) A.
Proof.
intros A B rel a InaR.
rewrite <- (RelationAllImageLEq _) in InaR.
apply RelationImageLSubset in InaR.
assumption.
Qed.


Definition Image {A B} : #(Map (Map A B) (PowerSet B)) :=
%(RistrictMapD Map_Rel) RelationAllImageR.

Theorem ImageTheorem : forall {A B} (f : #(Map A B)) b,
In b (%Image f) <-> exists a : #A, %f a == b.
Proof.
intros A B f b.
unfold Image.
assert(EqM : f == (f{<Map_Rel})).
 hyperreflexivity.
rewrite (MapStrong (StrongRistrictMapD _ _) EqM).
split.

intros InbI.
assert(Inb : In b B).
 apply RelationAllImageRSubset in InbI.
 assumption.
rewrite <- (DSETEq _ Inb) in InbI.
apply RelationAllImageRIn in InbI.
destruct InbI as [a relH].
exists a.
rewrite <- (DSETEq _ Inb).
apply AppTheoremReverse.
apply relH.

intros FaEq.
destruct FaEq as [a FaEa].
assert (Inb : In b B).
 rewrite <- FaEa.
 apply MapIn.
rewrite <- (DSETEq _ Inb).
apply RelationAllImageRIn.
exists a.
apply AppMapRel.
rewrite FaEa.
hyperreflexivity.
Qed.

Theorem SubsetImageRange : forall {A B} (f : #(Map A B)), Subset (%Image f) B.
Proof.
intros A B f.
intros b InbI.
apply ImageTheorem in InbI.
destruct InbI as [a Eqfab].
rewrite <- Eqfab.
apply MapIn.
Qed.

Theorem RistableRMapImageIn : forall {A B} (f : #(Map A B)),
In f (RistableRMap A B (%Image f)).
Proof.
intros A B f.
apply RistableRMapTheorem.
split.
apply SubsetImageRange.
intro a.
apply ImageTheorem.
exists a.
hyperreflexivity.
Qed.

Definition RistableRMapImage {A B} (f : #(Map A B)) : #(Map A (%Image f)) :=
%RistrictMapR {f ! RistableRMapImageIn f}.

Theorem RistableRMapImageEq : forall {A B} (f : #(Map A B)),
RistableRMapImage f == f.
Proof.
intros A B f.
unfold RistableRMapImage.
rewrite RistrictMapREq.
hyperreflexivity.
Qed.


(* MapRangeImage *)
Definition RelImageE {A B} : #(Map (Relation A B) (Map A (PowerSet B))) :=
%RightCombineMapC [RelationImageR ; SingletonMap].


Theorem RelationImageETheorem : forall {A B} (rel : #(Relation A B)),
forall (a : #A) (b : #B), In b (%(%RelImageE rel) a) <-> &&rel a b.
Proof.
intros A B rel a b.
split.

intro Inrel.
unfold RelImageE in Inrel.
rewrite (RightCombineMapCTheorem _ _ _) in Inrel.
apply RelationImageRTheorem in Inrel.
destruct Inrel as [a' Inrel].
destruct Inrel as [Eqa relH].
rewrite (SingletonMapTheorem _) in Eqa.
apply SingletonTheorem in Eqa.
generalize relH.
apply RelRewriteL.
rewrite Eqa.
hyperreflexivity.

intros relH.
unfold RelImageE.
rewrite (RightCombineMapCTheorem _ _ _).
apply RelationImageRTheorem.
exists a.
split.
rewrite (SingletonMapTheorem _).
apply SingletonTheorem.
hyperreflexivity.
apply relH.
Qed.

Theorem RelationImageESubset : forall {A B} (rel : #(Relation A B)) (a : #A),
Subset (%(%RelImageE rel) a) B.
Proof.
intros A B rel a b Inrel.
unfold RelImageE in Inrel.
rewrite (RightCombineMapCTheorem _ _ _) in Inrel.
apply RelationImageRSubset in Inrel.
assumption.
Qed.

Theorem RelationImageETheoremExists : forall {A B} (rel : #(Relation A B)),
forall (a : #A) b, In b (%(%RelImageE rel) a) <-> (exists Inb : In b B, &&rel a {b ! Inb}).
Proof.
intros A B rel a b.
split.
 intro InbR.
 assert(Inb : In b B).
  apply RelationImageESubset in InbR.
  apply InbR.
 exists Inb.
 rewrite (DSETEq' _ Inb) in InbR.
 apply RelationImageETheorem in InbR.
 apply InbR.

 intro cond.
 destruct cond as [Inb relH].
 rewrite (DSETEq' _ Inb).
 apply RelationImageETheorem.
 apply relH.
Qed.


(* RightUnique Is PartialMap *)
Definition DomainOfRightUnique {A B} : #(Map (RightUnique A B) (PowerSet A)) :=
%(RistrictMapD (RUnq_Rel)) RelationAllImageL.

Theorem DomainOfRightUniqueTheorem : forall {A B} (ru : #(RightUnique A B)) (a : #A),
In a (%DomainOfRightUnique ru) <->
(exists b, &&(ru{<RUnq_Rel}) a b).
Proof.
intros A B ru a.
unfold DomainOfRightUnique.
rewrite (RistrictMapDEqSubp RUnq_Rel).
split.
 intro InaD.
 apply RelationAllImageLIn in InaD.
 apply InaD.
intro cond.
apply RelationAllImageLIn.
apply cond.
Qed.

Theorem DomainOfRightUniqueSubset : forall {A B} (ru : #(RightUnique A B)),
Subset (%DomainOfRightUnique ru) A.
Proof.
intros A B ru.
intros a InaD.
unfold DomainOfRightUnique in InaD.
rewrite (RistrictMapDEqSubp RUnq_Rel) in InaD.
apply RelationAllImageLSubset in InaD.
apply InaD.
Qed.


Theorem RightUniqueInMap : forall {A B} (ru : #(RightUnique A B)),
In ru (Map (%DomainOfRightUnique ru) B).
Proof.
intros A B ru.
assert(InruRel : In ru (Relation (%DomainOfRightUnique ru) B)).
 apply PowersetTheorem.
 intros p Inpru.
 rewrite (USETEq' _ RUnq_Rel) in Inpru.
 put (IsPair'Relation _ _ _ _ Inpru) IsPp.
 destruct IsPp as [a IsPp].
 destruct IsPp as [b Eqp].
 rewrite Eqp.
 apply CartesianTheorem'.
 split.
  unfold DomainOfRightUnique.
  rewrite (RistrictMapDEqSubp RUnq_Rel).
  apply RelationAllImageLIn.
  exists b.
  unfold If.
  rewrite Eqp in Inpru.
  apply Inpru.
 apply SetProp.
rewrite (DSETEq' _ InruRel).
apply Rel_Map2.
split.
 intro a.
 assert(InaA : In a A).
  put (SetProp a) InaD.
  apply DomainOfRightUniqueSubset in InaD.
  apply InaD.
 put (SetProp a) InaSD.
 unfold DomainOfRightUnique in InaSD.
 rewrite (RistrictMapDEqSubp RUnq_Rel) in InaSD.
 assert(InaSD' : In {a ! InaA} (%RelationAllImageL (ru{<RUnq_Rel}))).
  apply InaSD.
 apply RelationAllImageLIn in InaSD'.
 destruct InaSD' as [b InaSD'].
 exists b.
 generalize InaSD'.
 apply RelRewriteAll; hyperreflexivity.

 intro a.
 intros b1 b2 H1 H2.
 put (SetProp ru) Inru.
 rewrite (USETEq' _ RUnq_Rel) in Inru.
 apply Rel_RUnq in Inru.
 assert(InaA : In a A).
  put (SetProp a) Ina.
  apply DomainOfRightUniqueSubset in Ina.
  apply Ina.
 apply (Atmost'EqApply _ (Inru {a ! InaA})).
 split.
  generalize H1.
  apply RelRewriteAll; hyperreflexivity.
 generalize H2.
 apply RelRewriteAll; hyperreflexivity.
Qed.

Definition RUnq_to_Map {A B} (ru : #(RightUnique A B)) : #(Map (%DomainOfRightUnique ru) B)
:= {ru ! RightUniqueInMap ru}.

Definition SubMap {A B} : #(Relation (Map A B) (RightUnique A B)) :=
%InverseRel (SubsetRelation _ _).


Definition PApp {D R} (f : #(RightUnique D R)) (a : #D) (cond : In a (%DomainOfRightUnique f)) :=
%(RUnq_to_Map f) {a ! cond}.

Notation "%? F a ! cond" := (PApp F {a ! cond}) (at level 10, x at next level).

Theorem StrongSubMap : forall {A B} (f : #(Map A B)) (ru : #(RightUnique A B)),
&&SubMap f ru <->
StrongRel ((RUnq_to_Map ru){<Map_Rel}) (f{<Map_Rel}).
Proof.
intros A B f ru.
split.
 intro SH.
 unfold SubMap in SH.
 apply InverseRelTheorem in SH.
 apply SubsetRelationTheorem in SH.
 apply SH.

 intro SR.
 apply InverseRelTheorem'.
 apply SubsetRelationTheorem.
 apply SR.
Qed.



(* TripleRelation to Map *)
Definition TripleRelR_to_Map {A B C} : #(Map (Relation A (Cartesian B C)) (Map A (Relation B C))) :=
@RelImageE A (Cartesian B C).

Theorem TripleRelR_to_MapTheorem : forall {A B C} (rel : #(Relation A (Cartesian B C))) a b c,
&&rel a [b;c] <-> &&(%(%TripleRelR_to_Map rel) a) b c.
Proof.
intros A B C rel a b c.
split.
 intro relH.
 apply RelationImageETheorem in relH.
 unfold TripleRelR_to_Map.
 unfold If.
 apply relH.

 intro TRelH.
 apply RelationImageETheorem.
 unfold TripleRelR_to_Map in TRelH.
 unfold If in TRelH.
 apply TRelH.
Qed.



(* Equivalence Class *)
Definition EquivalenceClass {E} : #(Map (ERelation E) (Map E (PowerSet E)))
  := %(RistrictMapD ERel_Rel) RelImageE.


Theorem EquivalenceClassTheorem : forall {E} (erel : #(ERelation E)) (a b : #E),
&&(erel{<ERel_Rel}) a b <-> In b (%(%EquivalenceClass erel) a).
Proof.
intros E erel a b.
unfold EquivalenceClass.
assert(Eqrel : erel == (erel{<ERel_Rel})).
 hyperreflexivity.
rewrite (MapEq (MapStrong (StrongRistrictMapD _ _) Eqrel)).
clear Eqrel.
split.

intro relH.
apply (RelationImageETheorem (erel{<ERel_Rel})).
apply relH.

intros relH.
apply (RelationImageETheorem (erel{<ERel_Rel})) in relH.
apply relH.
Qed.

Theorem EquivalenceClassInE : forall {E} (erel : #(ERelation E)) (a : #E) (b : SET),
In b (%(%EquivalenceClass erel) a) -> In b E.
Proof.
intros E erel a b relH.
unfold EquivalenceClass in relH.
assert(Eqrel : erel == (erel{<ERel_Rel})).
 hyperreflexivity.
rewrite (MapEq (MapStrong (StrongRistrictMapD _ _) Eqrel)) in relH.
apply (RelationImageESubset (erel{<ERel_Rel})) in relH.
assumption.
Qed.


Theorem EquivalenceClassEq : forall {E} (erel : #(ERelation E)) (a b : #E),
&&(erel{<ERel_Rel}) a b <-> 
%(%EquivalenceClass erel) a == %(%EquivalenceClass erel) b.
Proof.
intros E erel a b.
assert(RT : Rel_TransCond (erel{<ERel_Rel})).
 apply Rel_Trans.
 apply ERel_Trans.
 apply (SetProp erel).
assert(RS : Rel_SymCond (erel{<ERel_Rel})).
 apply Rel_Sym.
 apply ERel_Sym.
 apply (SetProp erel).
assert(RR : Rel_RefCond (erel{<ERel_Rel})).
 apply Rel_Ref.
 apply ERel_Ref.
 apply (SetProp erel).
split.

intro relH.
apply EA.
intro x.
split.
 intro InxEC.
 assert(InxE : In x E).
  apply (EquivalenceClassInE erel) in InxEC.
  assumption.
 rewrite <- (DSETEq _ InxE).
 rewrite <- (DSETEq _ InxE) in InxEC.
 apply EquivalenceClassTheorem.
 apply EquivalenceClassTheorem in InxEC.
 apply (RT _ a).
 apply RS.
 apply relH.
 apply InxEC.

 intro InxEC.
 assert(InxE : In x E).
  apply (EquivalenceClassInE erel) in InxEC.
  assumption.
 rewrite <- (DSETEq _ InxE).
 rewrite <- (DSETEq _ InxE) in InxEC.
 apply EquivalenceClassTheorem.
 apply EquivalenceClassTheorem in InxEC.
 apply (RT _ b).
  apply relH.
 apply InxEC.


intro Eqerel.
assert(InbERel : In b (%(%EquivalenceClass erel) b)).
 apply EquivalenceClassTheorem.
 apply RR.
rewrite <- Eqerel in InbERel.
apply EquivalenceClassTheorem in InbERel.
apply InbERel.
Qed.

Definition ERel_to_Class__ {E} : #(Map (ERelation E) (PowerSet (PowerSet E))) :=
%CombineMap' [ EquivalenceClass ; Image ].

Theorem ERel_to_Class__In : forall {E} (erel : #(ERelation E)) S,
In S (%ERel_to_Class__ erel) <-> exists a : #E, (%(%EquivalenceClass erel) a) == S.
Proof.
intros E erel S.
unfold ERel_to_Class__.
rewrite (CombineMap'Theorem _ _ _).
split.

intro InSEE.
apply ImageTheorem in InSEE.
destruct InSEE as [a InSEE].
exists a.
rewrite InSEE.
hyperreflexivity.

intro Cond.
destruct Cond as [a EqES].
apply ImageTheorem.
exists a.
rewrite EqES.
hyperreflexivity.
Qed.

Theorem ERel_to_ClassClassificationsCond : forall {E},
In (@ERel_to_Class__ E) (RistableRMap (ERelation E) (PowerSet (PowerSet E)) (Classifications E)).
Proof.
intros E.
apply RistableRMapTheorem.
split.
apply SSetSubset.
intros erel.
assert(RR : Rel_RefCond (erel{<ERel_Rel})).
 apply Rel_Ref.
 apply ERel_Ref.
 apply (SetProp erel).
assert(RS : Rel_SymCond (erel{<ERel_Rel})).
 apply Rel_Sym.
 apply ERel_Sym.
 apply (SetProp erel).
assert(RT : Rel_TransCond (erel{<ERel_Rel})).
 apply Rel_Trans.
 apply ERel_Trans.
 apply (SetProp erel).

apply ClassificationTheorem.

split.
 intros S InSE.
 apply ERel_to_Class__In in InSE.
 destruct InSE as [a InSE].
 rewrite <- InSE.
 exists a.
 apply EquivalenceClassTheorem.
 apply RR.

split.
 apply EA.
 intro e.
 split.
  intro IneU.
  apply UnionsTheorem in IneU.
  destruct IneU as [S IneU].
  destruct IneU as [InSE IneS].
  apply ERel_to_Class__In in InSE.
  destruct InSE as [a EqaS].
  rewrite <- EqaS in IneS.
  apply EquivalenceClassInE in IneS.
  assumption.

  intro IneE.
  apply UnionsTheorem.
  exists (%(%EquivalenceClass erel) {e ! IneE}).
  split.
   apply ERel_to_Class__In.
   exists {e ! IneE}.
   hyperreflexivity.
  cut (In {e ! IneE} (%(%EquivalenceClass erel) {e ! IneE})).
   intro HHH; apply HHH.
  apply EquivalenceClassTheorem.
  apply RR.

intros S1 S2 InSE1 InSE2 NES.
apply (ERel_to_Class__In) in InSE1.
destruct InSE1 as [a EqaS1].
apply (ERel_to_Class__In) in InSE2.
destruct InSE2 as [b EqbS2].
destruct NES as [x NES].
apply SectionTheorem in NES.
destruct NES as [InxS1 InxS2].
rewrite <- EqaS1 in InxS1.
rewrite <- EqbS2 in InxS2.
assert(InxE : In x E).
 apply EquivalenceClassInE in InxS1.
 assumption.
rewrite <- (DSETEq _ InxE) in InxS1.
rewrite <- (DSETEq _ InxE) in InxS2.
apply EquivalenceClassTheorem in InxS1.
apply EquivalenceClassTheorem in InxS2.
rewrite <- EqaS1.
rewrite <- EqbS2.
apply EquivalenceClassEq.
apply (RT _ {x ! InxE}).
apply InxS1.
apply RS.
apply InxS2.
Qed.

Definition ERel_to_Class {E} : #(Map (ERelation E) (Classifications E)) :=
%RistrictMapR {_ ! @ERel_to_ClassClassificationsCond E}.

Theorem ERel_to_ClassIn : forall {E} (erel : #(ERelation E)) S,
In S (%ERel_to_Class erel) <-> exists a : #E, (%(%EquivalenceClass erel) a) == S.
Proof.
intros E erel S.
unfold ERel_to_Class.
rewrite (MapEq (RistrictMapREq2 _ _)).
apply ERel_to_Class__In.
Qed.

Theorem EqCannProj_is_EqCls : forall {E} (rel : #(ERelation E)),
EqCannProj (%ERel_to_Class rel) == %EquivalenceClass rel.
Proof.
intros E rel.
apply MapEquality.
hyperreflexivity.
intros a b Eqab.
apply EA.
intro x.
split.
 intro InxEE.
 rewrite <- (MapArgEq _ Eqab).
 assert(InEqCPj : In (%(EqCannProj (%ERel_to_Class rel)) a) (%ERel_to_Class rel)).
  apply MapIn.
 apply ERel_to_ClassIn in InEqCPj.
 destruct InEqCPj as [c InEqCPj].
 rewrite <- InEqCPj in InxEE.
 assert(Eqac : %(%EquivalenceClass rel) a == %(%EquivalenceClass rel) c).
  apply EquivalenceClassEq.
  assert(InaRE : In a (%(%EquivalenceClass rel) c)).
   rewrite InEqCPj.
   apply EqCannProjOwnIn.
  apply EquivalenceClassTheorem in InaRE.
  cut (Rel_SymCond (rel{<ERel_Rel})).
   intro cond.
   apply cond.
   apply InaRE.
  apply Rel_Sym.
  apply ERel_Sym.
  apply (SetProp rel).
 rewrite Eqac.
 apply InxEE.

 intro InxERb.
 rewrite (MapArgEq _ Eqab).
 assert(InEqCPj : In (%(EqCannProj (%ERel_to_Class rel)) b) (%ERel_to_Class rel)).
  apply MapIn.
 apply ERel_to_ClassIn in InEqCPj.
 destruct InEqCPj as [c InEqCPj].
 rewrite <- InEqCPj.
 assert(Eqac : %(%EquivalenceClass rel) c == %(%EquivalenceClass rel) b).
  apply EquivalenceClassEq.
  assert(InaRE : In b (%(%EquivalenceClass rel) c)).
   rewrite InEqCPj.
   apply EqCannProjOwnIn.
  apply EquivalenceClassTheorem in InaRE.
  apply InaRE.
 rewrite Eqac.
 apply InxERb.
Qed.


Theorem ERel_to_ClassTheorem : forall {E} (erel : #(ERelation E)) (a b : #E),
&&(erel{<ERel_Rel}) a b <->  (%(EqCannProj (%ERel_to_Class erel)) a) == (%(EqCannProj (%ERel_to_Class erel)) b).
Proof.
intros E erel a b.
rewrite (MapEq (EqCannProj_is_EqCls _)).
rewrite (MapEq (EqCannProj_is_EqCls _)).
apply EquivalenceClassEq.
Qed.


 
Theorem ERel_to_ClassSurjection : forall {E},
Map_SurCond (@ERel_to_Class E).
Proof.
intro E.
intro C.
set (MakeRelation (fun (a : #E) (b : #E) => In b (%(EqCannProj C) a))) as rel.
assert(rel_erelcond : Rel_ERelCond rel).
 split.
  intro a.
  apply MakeRelationTheorem.
  intros a1 a2 Eqa1 Eqa2.
  rewrite <- Eqa2.
  rewrite Eqa1.
  apply EqCannProjOwnIn.
 split.
  intros x y RelH.
  put ((proj1 (MakeRelationTheorem _ _ _ _ _)) RelH) RelH'.
  clear RelH.
  put (RelH' _ _ (ReflexivityEq x) (ReflexivityEq y)) RelH.
  clear RelH'.
  apply MakeRelationTheorem.
  intros y' x' Eqy Eqx.
  rewrite <- Eqx.
  rewrite (MapArgEq _ (SymmetryEq _ _ Eqy)).
  assert(EqCP : %(EqCannProj C) x == %(EqCannProj C) y).
   apply (ClassificationTheorem2 _ _ _ _ (SetProp C)).
   apply MapIn.
   apply MapIn.
   exists y.
   apply SectionTheorem.
   split.
   apply RelH.
   apply EqCannProjOwnIn.
  rewrite <- EqCP.
  apply EqCannProjOwnIn.
 intros a b c relH1 relH2.
 put ((proj1 (MakeRelationTheorem _ _ _ _ _)) relH1) relH1'.
 clear relH1.
 put (relH1' _ _ (ReflexivityEq a) (ReflexivityEq b)) relH1.
 clear relH1'.
 put ((proj1 (MakeRelationTheorem _ _ _ _ _)) relH2) relH2'.
 clear relH2.
 put (relH2' _ _ (ReflexivityEq b) (ReflexivityEq c)) relH2.
 clear relH2'.
 apply MakeRelationTheorem.
 intros a' c' Eqaaa Eqc.
 rewrite <- Eqc.
 rewrite <- (MapArgEq _ (Eqaaa)).
 assert(EqCPab : (%(EqCannProj C) a) == (%(EqCannProj C) b)).
  apply (ClassificationTheorem2 _ _ _ _ (SetProp C)).
  apply MapIn.
  apply MapIn.
  exists b.
  apply SectionTheorem.
  split.
  apply relH1.
  apply EqCannProjOwnIn.
 assert(EqCPbc : (%(EqCannProj C) b) == (%(EqCannProj C) c)).
  apply (ClassificationTheorem2 _ _ _ _ (SetProp C)).
  apply MapIn.
  apply MapIn.
  exists c.
  apply SectionTheorem.
  split.
  apply relH2.
  apply EqCannProjOwnIn.
 rewrite EqCPab.
 rewrite EqCPbc.
 apply EqCannProjOwnIn.
set (rel{<Rel_ERel ! rel_erelcond}) as erel.
exists erel.
assert(EqERR : (EqCannProj C) == ((%EquivalenceClass) erel)).
 apply MapEquality.
 hyperreflexivity.
 intros a aa Eqaaa.
 rewrite (MapArgEq' _ Eqaaa).
 apply EA.
 intros b.
 split.
  intro InbEC.
  assert(InbE : In b E).
   apply EqCannProjInA in InbEC.
   assumption.
  rewrite (DSETEq' _ InbE).
  apply EquivalenceClassTheorem.
  cut (&&rel a {b ! InbE}).
   apply RelRewrite.
   hyperreflexivity.
  apply MakeRelationTheorem.
  intros a' b' Eqa Eqb.
  rewrite <- Eqb.
  rewrite <- (MapArgEq _ Eqa).
  apply InbEC.

  intro InbEC.
  assert(InbE : In b E).
   apply EquivalenceClassInE in InbEC.
   assumption.
  rewrite (DSETEq' _ InbE) in InbEC.
  apply EquivalenceClassTheorem in InbEC.
  assert(relEq : (erel{<ERel_Rel}) == rel).
   hyperreflexivity.
  apply (RelRewrite relEq) in InbEC.
  clear relEq.
  put ((proj1 (MakeRelationTheorem _ _ _ _ _)) InbEC) relH'.
  clear InbEC.
  put (relH' _ _ (ReflexivityEq a) (ReflexivityEq _)) relH.
  clear relH'.
  apply relH.

apply EA.
intro S.
split.
 intro InSER.
 apply ERel_to_ClassIn in InSER.
 destruct InSER as [a EqEerelaS].
 rewrite <- EqEerelaS.
 rewrite <- (MapEq (EqCannProj_is_EqCls _)).
 apply EqCannProjIn.
 exists a.
 rewrite (MapEq (EqCannProj_is_EqCls _)).
 apply MapEq.
 apply EqERR.

 intro InSC.
 apply ERel_to_ClassIn.
 assert(NES : NonEmpty S).
  apply (ClassificationTheorem3 _ _ (SetProp C)).
  assumption.
 destruct NES as [a_ NES].
 assert(InaE : In a_ E).
  apply (ClassificationIn _ _ _ _ (SetProp C) InSC NES).
 set {a_ ! InaE} as a.
 exists a.
 rewrite (MapEq' EqERR).
 apply (ClassificationTheorem2 _ _ _ _ (SetProp C)).
 apply MapIn.
 assumption.
 exists a.
 apply SectionTheorem.
 split.
  apply EqCannProjOwnIn.
 apply NES.
Qed.


Theorem ERel_to_ClassInjection : forall {E},
Map_InjCond (@ERel_to_Class E).
Proof.
intros E.
intros erel1 erel2 erelME.
set (erel1{<ERel_Rel}) as rel1.
set (erel2{<ERel_Rel}) as rel2.
apply SymmetryEq.
apply (TransitivityEq rel2).
hyperreflexivity.
apply SymmetryEq.
apply (TransitivityEq rel1).
hyperreflexivity.
apply (RelEquality rel1 rel2).
assert(TR1 : Rel_RefCond rel1).
 apply Rel_ERel.
 apply (SetProp erel1).
assert(TR2 : Rel_RefCond rel2).
 apply Rel_ERel.
 apply (SetProp erel2).
assert(TS1 : Rel_SymCond rel1).
 apply Rel_ERel.
 apply (SetProp erel1).
assert(TS2 : Rel_SymCond rel2).
 apply Rel_ERel.
 apply (SetProp erel2).
assert(TT1 : Rel_TransCond rel1).
 apply Rel_ERel.
 apply (SetProp erel1).
assert(TT2 : Rel_TransCond rel2).
 apply Rel_ERel.
 apply (SetProp erel2).
split.
 apply ToStrongRel.
 intros a b relH.
 exists a.
 exists b.
 split.
 hyperreflexivity.
 split.
 hyperreflexivity.
 assert(InSE : In (%(%EquivalenceClass erel1) a) (%ERel_to_Class erel2)).
  rewrite <- erelME.
  apply (ERel_to_ClassIn).
  exists a.
  hyperreflexivity.
 apply ERel_to_ClassIn in InSE.
 destruct InSE as [c EQc].
 apply (TT2 _ c).
  apply TS2.
  apply EquivalenceClassTheorem.
  rewrite EQc.
  apply EquivalenceClassTheorem.
  apply TR1.
 apply EquivalenceClassTheorem.
 rewrite EQc.
 apply EquivalenceClassTheorem.
 apply relH.

 apply ToStrongRel.
 intros a b relH.
 exists a.
 exists b.
 split.
 hyperreflexivity.
 split.
 hyperreflexivity.
 assert(InSE : In (%(%EquivalenceClass erel2) a) (%ERel_to_Class erel1)).
  rewrite erelME.
  apply (ERel_to_ClassIn).
  exists a.
  hyperreflexivity.
 apply ERel_to_ClassIn in InSE.
 destruct InSE as [c EQc].
 apply (TT1 _ c).
  apply TS1.
  apply EquivalenceClassTheorem.
  rewrite EQc.
  apply EquivalenceClassTheorem.
  apply TR2.
 apply EquivalenceClassTheorem.
 rewrite EQc.
 apply EquivalenceClassTheorem.
 apply relH.
Qed.
 
Theorem ERel_to_ClassBijection : forall {E},
Map_BijCond (@ERel_to_Class E).
Proof.
intros E.
split.
apply ERel_to_ClassInjection.
apply ERel_to_ClassSurjection.
Qed.


Definition Class_to_ERel {E} : #(Map (Classifications E) (ERelation E)) :=
%InverseMap (@ERel_to_Class E){<Map_Bij ! ERel_to_ClassBijection}.

Theorem Class_to_ERelSurjection : forall {E},
Map_SurCond (@Class_to_ERel E).
Proof.
intro E.
unfold Class_to_ERel.
apply SurjectionInverseMap.
Qed.

Theorem Class_to_ERelInjection : forall {E},
Map_InjCond (@Class_to_ERel E).
Proof.
intro E.
unfold Class_to_ERel.
apply InjectionInverseMap.
Qed.

Theorem Class_to_ERelTheorem : forall {E} (C : #(Classifications E)) (a b : #E),
&&(%Class_to_ERel C){<ERel_Rel} a b <-> (%(EqCannProj C) a) == (%(EqCannProj C) b).
Proof.
intros E C a b.
assert(EqC : EqCannProj C == EqCannProj (%ERel_to_Class (%Class_to_ERel C))).
 apply RewriteEqCannProj.
 rewrite <- (MapInverseTheorem (ERel_to_Class{<Map_Bij ! ERel_to_ClassBijection}) C).
 apply MapEqAll.
  apply MapEq.
  hyperreflexivity.
 hyperreflexivity.

split.

intro RelH.
apply (ClassificationTheorem2 _ _ _ _ (SetProp C)).
apply MapIn.
apply MapIn.
exists a.
apply SectionTheorem.
split.
apply EqCannProjOwnIn.
rewrite (MapEq EqC).
rewrite (MapEq (EqCannProj_is_EqCls _)).
apply EquivalenceClassTheorem.
cut (Rel_SymCond (%Class_to_ERel C){<ERel_Rel}).
 intro SC.
 apply SC.
 apply RelH.
apply Rel_ERel.
rewrite (USETEq _ ERel_Rel).
apply SetProp.

intro EqCPC.
rewrite (MapEq EqC) in EqCPC.
rewrite (MapEq EqC) in EqCPC.
rewrite (MapEq (EqCannProj_is_EqCls _)) in EqCPC.
rewrite (MapEq (EqCannProj_is_EqCls _)) in EqCPC.
apply EquivalenceClassTheorem.
rewrite EqCPC.
rewrite (MapEq' (EqCannProj_is_EqCls _)).
apply EqCannProjOwnIn.
Qed.

Theorem ERel_to_Class_to_ERel : forall {A} (C : #(Classifications A)),
(%ERel_to_Class (%Class_to_ERel C)) == C.
Proof.
intros A C.
unfold Class_to_ERel.
apply MapInverseTheoremRC.
Qed.

Theorem Class_to_ERel_to_Class : forall {A} (erel : #(ERelation A)),
(%Class_to_ERel (%ERel_to_Class erel)) == erel.
Proof.
intros A erel.
unfold Class_to_ERel.
apply InverseMapTheoremRC.
Qed.


Theorem EqCls_is_EqCannProj : forall {E} (C : #(Classifications E)),
EqCannProj C == %EquivalenceClass (%Class_to_ERel C).
Proof.
intros E C.
rewrite(Rewrite'EqCannProj _ _ (ERel_to_Class_to_ERel _)).
rewrite EqCannProj_is_EqCls.
hyperreflexivity.
Qed.

Theorem EqCannProjTheorem : forall {E} (C : #(Classifications E)) a b,
&&(%Class_to_ERel C){<ERel_Rel} a b <->
In b (%(EqCannProj C) a).
Proof.
intros E C a b.
split.
 intro CH.
 rewrite (MapEq (EqCls_is_EqCannProj _)).
 apply EquivalenceClassTheorem.
 apply CH.

 intro InbE.
 rewrite (MapEq (EqCls_is_EqCannProj _)) in InbE.
 apply EquivalenceClassTheorem in InbE.
 apply InbE.
Qed.

(* Double Classification *)
Theorem DoubleClassificationsInRistrictableMap : forall {A B},
In (%BinaryMapImage (@MCartesian A B)) (RistableMap (Cartesian (PowerSet (PowerSet A)) (PowerSet (PowerSet B))) (PowerSet (PowerSet (Cartesian A B))) (Cartesian (Classifications A) (Classifications B)) (Classifications (Cartesian A B))).
Proof.
intros A B.
assert(SubA : Subset (Classifications A) (PowerSet (PowerSet A))).
 apply ClassificationPPSubset.
assert(SubB : Subset (Classifications B) (PowerSet (PowerSet B))).
 apply ClassificationPPSubset.
apply RistableMapTheorem.
split.
{
  split.
  apply SubsetInCartesian; assumption.
  apply ClassificationPPSubset.
}
intros SSAB InSSAB.
put (CartesianIsPair' _ _ _ InSSAB) EqSSAB.
destruct EqSSAB as [CA EqSSAB].
destruct EqSSAB as [CB EqSSAB].
set (CA{<SubA}) as CAP.
set (CB{<SubB}) as CBP.
assert(EqSSABP : SSAB == [CAP ; CBP]).
 rewrite EqSSAB.
 hyperreflexivity.
rewrite (MapArgEq _ EqSSABP).
apply ClassificationTheorem.
split.
 intros SX InSX.
 apply BinaryMapImageTheorem in InSX.
 destruct InSX as [PA InSX].
 destruct InSX as [PB InSX].
 destruct InSX as [InPAC InSX].
 destruct InSX as [InPBC EqMS].
 rewrite (MCartesianEq _ _) in EqMS.
 put (ClassificationTheorem3 _ _ (SetProp CA) _ InPAC) NEA.
 put (ClassificationTheorem3 _ _ (SetProp CB) _ InPBC) NEB.
 destruct NEA as [a NEA].
 destruct NEB as [b NEB].
 rewrite <- EqMS.
 exists (Pair a b).
 apply CartesianTheorem.
 split; assumption.
split.
 apply EA.
 intro p.
 split.
  intro InpU.
  apply UnionsTheorem in InpU.
  destruct InpU as [CX InpU].
  destruct InpU as [InCX InpCX].
  apply BinaryMapImageTheorem in InCX.
  destruct InCX as [a InCX].
  destruct InCX as [b InCX].
  destruct InCX as [InaCAP InCX].
  destruct InCX as [InbCBP EqPCX].
  rewrite (MCartesianEq _ _) in EqPCX.
  rewrite <- EqPCX in InpCX.
  put (CartesianIsPair _ _ _ InpCX) IsPp.
  destruct IsPp as [aa IsPp].
  destruct IsPp as [bb Eqp].
  assert(InD : In aa a /\ In bb b).
   apply CartesianTheorem.
   rewrite <- Eqp.
   assumption.
  destruct InD as [Inaaa Inbbb].
  rewrite Eqp.
  apply CartesianTheorem.
  put (SetProp a) InaP.
  put (SetProp b) InbP.
  apply PowersetTheorem in InaP.
  apply PowersetTheorem in InbP.
  split.
  apply InaP.
  assumption.
  apply InbP.
  assumption.

 intro InpC.
 put (CartesianIsPair _ _ _ InpC) IsPp.
 destruct IsPp as [a_ IsPp].
 destruct IsPp as [b_ Eqp].
 assert(InD : In a_ A /\ In b_ B).
  apply CartesianTheorem.
  rewrite <- Eqp.
  assumption.
 destruct InD as [InaA InbB].
 set {a_ ! InaA} as a.
 set {b_ ! InbB} as b.
 apply UnionsTheorem.
 exists (Cartesian (%(EqCannProj CA) a) (%(EqCannProj CB) b)).
 split.
  apply BinaryMapImageTheorem.
  assert(InaP : In (%(EqCannProj CA) a) (PowerSet A)).
   apply PowersetTheorem.
   apply (ClassificationSubset CA).
   apply MapIn.
  assert(InbP : In (%(EqCannProj CB) b) (PowerSet B)).
   apply PowersetTheorem.
   apply (ClassificationSubset CB).
   apply MapIn.
  exists {_ ! InaP}.
  exists {_ ! InbP}.
  split.
   rewrite (DSETEq _ InaP).
   apply MapIn.
  split.
   rewrite (DSETEq _ InbP).
   apply MapIn.
  rewrite (MCartesianEq _ _).
  hyperreflexivity.
 rewrite Eqp.
 apply CartesianTheorem.
 split.
  rewrite (DSETEq' _ InaA).
  apply EqCannProjOwnIn.

  rewrite (DSETEq' _ InbB).
  apply EqCannProjOwnIn.

intros S1 S2 InS1 InS2 NE.
destruct NE as [x NE].
apply SectionTheorem in NE.
destruct NE as [InxSA InxSB].
apply BinaryMapImageTheorem in InS1.
destruct InS1 as [SA1 InS1].
destruct InS1 as [SB1 InS1].
destruct InS1 as [InSA1 InS1].
destruct InS1 as [InSB1 EqCS1].
rewrite (MCartesianEq _ _) in EqCS1.
apply BinaryMapImageTheorem in InS2.
destruct InS2 as [SA2 InS2].
destruct InS2 as [SB2 InS2].
destruct InS2 as [InSA2 InS2].
destruct InS2 as [InSB2 EqCS2].
rewrite (MCartesianEq _ _) in EqCS2.
assert(IsPx : IsPair x).
 rewrite <- EqCS1 in InxSA.
 apply (CartesianIsPair _ _ _ InxSA).
destruct IsPx as [a IsPx].
destruct IsPx as [b Eqx].
rewrite Eqx in InxSA.
rewrite Eqx in InxSB.
assert(InD : In a SA1 /\ In b SB1).
 apply CartesianTheorem.
 rewrite EqCS1.
 assumption.
destruct InD as [Ina1 Inb1].
assert(InD : In a SA2 /\ In b SB2).
 apply CartesianTheorem.
 rewrite EqCS2.
 assumption.
destruct InD as [Ina2 Inb2].
assert(EqSA : SA1 == SA2).
 apply (ClassificationTheorem2 _ _ _ _ (SetProp CA)).
 apply InSA1.
 apply InSA2.
 exists a.
 apply SectionTheorem.
 split; assumption.
assert(EqSB : SB1 == SB2).
 apply (ClassificationTheorem2 _ _ _ _ (SetProp CB)).
 apply InSB1.
 apply InSB2.
 exists b.
 apply SectionTheorem.
 split; assumption.
rewrite <- EqCS1.
rewrite <- EqCS2.
apply FunRewrite2.
assumption.
assumption.
Qed.

Definition DoubleClassifications {A B} : #(Map (Cartesian (Classifications A) (Classifications B)) (Classifications (Cartesian A B))) :=
%RistMap {_ ! @DoubleClassificationsInRistrictableMap A B}.

Theorem DoubleClassificationInRistrictableMap : forall {A B} (CA : #(Classifications A)) (CB : #(Classifications B)),
In (@MCartesian A B) (RistableMap (Cartesian (PowerSet A) (PowerSet B)) (PowerSet (Cartesian A B)) (Cartesian CA CB) (%DoubleClassifications [CA ; CB])).
Proof.
intros A B CA CB.
assert(SubA : Subset CA (PowerSet A)).
 apply ClassificationPSubset.
assert(SubB : Subset CB (PowerSet B)).
 apply ClassificationPSubset. 
assert(SubPA : Subset (Classifications A) (PowerSet (PowerSet A))).
 apply ClassificationPPSubset.
assert(SubPB : Subset (Classifications B) (PowerSet (PowerSet B))).
 apply ClassificationPPSubset.
apply RistableMapTheorem.
split.
{
  split.
  apply SubsetInCartesian; assumption.
  intros SASB InSASB.
  unfold DoubleClassifications in InSASB.
  assert (InSASB' : In SASB (%(%BinaryMapImage MCartesian) [CA{<SubPA} ; CB{<SubPB}])).
  {
    generalize InSASB.
    apply ArrowRewrite.
    apply MapStrong.
    apply StrongRistMapEq.
    hyperreflexivity.
    hyperreflexivity.
  }
  clear InSASB.
  rename InSASB' into InSASB.
  apply BinaryMapImageTheorem in InSASB.
  destruct InSASB as [SA InSASB].
  destruct InSASB as [SB InSASB].
  destruct InSASB as [InSA InSASB].
  destruct InSASB as [InSB EqSASB].
  rewrite (MCartesianEq _ _) in EqSASB.
  rewrite <- EqSASB.
  apply PowersetTheorem.
  intros p InpC.
  put (CartesianIsPair' _ _ _ InpC) IsPp.
  destruct IsPp as [a IsPp].
  destruct IsPp as [b Eqp].
  rewrite Eqp.
  apply CartesianTheorem'.
  split.
  {
    assert(InSAA : In SA (PowerSet A)).
    apply SubA.
    apply InSA.
    apply PowersetTheorem in InSAA.
    apply InSAA.
    apply SetProp.
  }
  assert(InSBB : In SB (PowerSet B)).
  {
    apply SubB.
    apply InSB.
  }
  apply PowersetTheorem in InSBB.
  apply InSBB.
  apply SetProp.
}
intros SASB InSASB.
put (CartesianIsPair' _ _ _ InSASB) IsPSASB.
destruct IsPSASB as [SA IsPSASB].
destruct IsPSASB as [SB EqSASB].
assert(EqC : %MCartesian SASB == (Cartesian SA SB)).
 apply (TransitivityEq (%MCartesian [SA{<SubA};SB{<SubB}])).
 apply MapArgEq.
 rewrite EqSASB.
 hyperreflexivity.
 rewrite (MCartesianEq _ _).
 hyperreflexivity.
rewrite EqC.
clear EqC.
unfold DoubleClassifications.
cut (In (Cartesian SA SB) (%(%BinaryMapImage MCartesian) [CA{<SubPA} ; CB{<SubPB}])).
 apply ArrowRewrite.
 apply SymmetryEq.
 apply MapStrong.
  apply StrongRistMapEq.
  hyperreflexivity.
 hyperreflexivity.
apply BinaryMapImageTheorem.
exists (SA{<SubA}).
exists (SB{<SubB}).
split.
apply (SetProp SA).
split.
apply (SetProp SB).
rewrite (MCartesianEq _ _).
hyperreflexivity.
Qed.

Definition DoubleClassification {A B} {CA : #(Classifications A)} {CB : #(Classifications B)} : #(Map (Cartesian CA CB) (%DoubleClassifications [CA;CB])) :=
%RistMap {_ ! DoubleClassificationInRistrictableMap CA CB}.

Theorem DoubleClassificationEq : forall {A B} {CA : #(Classifications A)} {CB : #(Classifications B)} (SA : #CA) (SB : #CB),
%DoubleClassification [SA ; SB] == Cartesian SA SB.
Proof.
intros A B CA CB SA SB.
unfold DoubleClassification.
assert(SubA : Subset CA (PowerSet A)).
 apply ClassificationPSubset.
assert(SubB : Subset CB (PowerSet B)).
 apply ClassificationPSubset. 
apply (TransitivityEq (%MCartesian [SA{<SubA} ; SB{<SubB}])).
 apply MapStrong.
  apply StrongRistMapEq.
  hyperreflexivity.
 hyperreflexivity.
rewrite (MCartesianEq _ _).
hyperreflexivity.
Qed.


Theorem DoubleClassificationInjection : forall {A B} {CA : #(Classifications A)} {CB : #(Classifications B)},
Map_InjCond (@DoubleClassification A B CA CB).
Proof.
intros A B CA CB.
intros S1 S2 EqS.
put (CartesianIsPair' _ _ _ (SetProp S1)) IsPS1.
destruct IsPS1 as [SA1 IsPS1].
destruct IsPS1 as [SB1 EqS1].
put (CartesianIsPair' _ _ _ (SetProp S2)) IsPS2.
destruct IsPS2 as [SA2 IsPS2].
destruct IsPS2 as [SB2 EqS2].
rewrite EqS1.
rewrite EqS2.
rewrite (MapArgEq _ EqS1) in EqS.
rewrite (MapArgEq _ EqS2) in EqS.
rewrite (DoubleClassificationEq _ _) in EqS.
rewrite (DoubleClassificationEq _ _) in EqS.
apply (TransitivityEq (Pair SA1 SB1)).
 hyperreflexivity.
apply (TransitivityEq (Pair SA2 SB2)).
 apply EqualInPair.
 apply CartesianInjection.
 apply (ClassificationTheorem3 _ _ (SetProp CA)).
 apply SetProp.
 apply (ClassificationTheorem3 _ _ (SetProp CA)).
 apply SetProp.
 apply (ClassificationTheorem3 _ _ (SetProp CB)).
 apply SetProp.
 apply (ClassificationTheorem3 _ _ (SetProp CB)).
 apply SetProp.
 apply EqS.
hyperreflexivity.
Qed.
 
Theorem DoubleClassificationSurjection : forall {A B} {CA : #(Classifications A)} {CB : #(Classifications B)},
Map_SurCond (@DoubleClassification A B CA CB).
Proof.
intros A B CA CB.
intro SASB.
put (SetProp SASB) InSASB.
unfold DoubleClassifications in InSASB.
assert(SubPA : Subset (Classifications A) (PowerSet (PowerSet A))).
 apply ClassificationPPSubset.
assert(SubPB : Subset (Classifications B) (PowerSet (PowerSet B))).
 apply ClassificationPPSubset.
assert(InSASB' : In SASB (%(%BinaryMapImage MCartesian) [CA{<SubPA} ; CB{<SubPB}])).
 generalize InSASB.
 apply ArrowRewrite.
 apply MapStrong.
  apply StrongRistMapEq.
  hyperreflexivity.
 hyperreflexivity.
clear InSASB.
rename InSASB' into InSASB.
apply BinaryMapImageTheorem in InSASB.
destruct InSASB as [SA InSASB].
destruct InSASB as [SB InSASB].
destruct InSASB as [InSA InSASB].
destruct InSASB as [InSB EqSASB].
rewrite (MCartesianEq _ _) in EqSASB.
exists [{SA ! InSA} ; {SB ! InSB}].
unfold DoubleClassification.
apply (TransitivityEq (%MCartesian [SA ; SB])).
 apply MapStrong.
  apply StrongRistMapEq.
  hyperreflexivity.
 hyperreflexivity.
rewrite (MCartesianEq _ _).
rewrite EqSASB.
hyperreflexivity.
Qed.

Definition DoubleERelation {A B} : #(Map (Cartesian (ERelation A) (ERelation B)) (ERelation (Cartesian A B))) :=
%CombineMap' [ (%DoubleMap [@ERel_to_Class A ; @ERel_to_Class B]) ; %CombineMap' [DoubleClassifications ; Class_to_ERel] ].


Theorem DoubleERelationTheorem : forall {A B} (erelA : #(ERelation A)) (erelB : #(ERelation B)) (a1 : #A) (a2 : #A) (b1 : #B) (b2 : #B),
&&(%DoubleERelation [erelA ; erelB]){<ERel_Rel} [a1;b1] [a2;b2] <->
(&&(erelA{<ERel_Rel}) a1 a2 /\ &&(erelB{<ERel_Rel}) b1 b2).
Proof.
intros A B erelA erelB a1 a2 b1 b2.
assert(SubPA : Subset (Classifications A) (PowerSet (PowerSet A))).
 apply ClassificationPPSubset.
assert(SubPB : Subset (Classifications B) (PowerSet (PowerSet B))).
 apply ClassificationPPSubset.
split.

intro InDR.
unfold DoubleERelation in InDR.
unfold If in InDR.
rewrite (USETEq _ (@ERel_Rel (Cartesian A B))) in InDR.
rewrite (CombineMap'Theorem _ _ _ _ _ _) in InDR.
rewrite (CombineMap'Theorem _ _ _ _ _ _) in InDR.
rewrite (MapArgEq _ (MapArgEq _ (DoubleMapTheorem _ _ _ _))) in InDR.
rewrite <- (USETEq _ (@ERel_Rel (Cartesian A B))) in InDR.
rewrite <- EqPairPair' in InDR.
apply ToForm_If in InDR.
apply Class_to_ERelTheorem in InDR.
assert(EqCab : (Cartesian (%(EqCannProj (%ERel_to_Class erelA)) a1) (%(EqCannProj (%ERel_to_Class erelB)) b1) ==  (Cartesian (%(EqCannProj (%ERel_to_Class erelA)) a2) (%(EqCannProj (%ERel_to_Class erelB)) b2)))).
 apply (TransitivityEq (%DoubleClassification [%(EqCannProj (%ERel_to_Class erelA)) a1 ; %(EqCannProj (%ERel_to_Class erelB)) b1])).
  rewrite (DoubleClassificationEq _ _).
  hyperreflexivity.
 apply (TransitivityEq (%(EqCannProj (%DoubleClassifications [%ERel_to_Class erelA ; %ERel_to_Class erelB])) [a1 ; b1])).
  apply (ClassificationTheorem2 (Cartesian A B) (%DoubleClassifications [%ERel_to_Class erelA ; %ERel_to_Class erelB])).
  apply MapIn.
  apply SetProp.
  apply SetProp.
  exists [a1 ; b1].
  apply SectionTheorem.
  split.
   rewrite (DoubleClassificationEq _ _).
   apply CartesianTheorem'.
   split.
   apply EqCannProjOwnIn.
   apply EqCannProjOwnIn.
 apply EqCannProjOwnIn.
 rewrite InDR.
 apply (TransitivityEq (%DoubleClassification [%(EqCannProj (%ERel_to_Class erelA)) a2 ; %(EqCannProj (%ERel_to_Class erelB)) b2])).
  apply (ClassificationTheorem2 (Cartesian A B) (%DoubleClassifications [%ERel_to_Class erelA ; %ERel_to_Class erelB])).
  apply MapIn.
  apply SetProp.
  apply SetProp.
  exists [a2 ; b2].
  apply SectionTheorem.
  split.
  apply EqCannProjOwnIn.
  rewrite (DoubleClassificationEq _ _).
  apply CartesianTheorem'.
  split.
  apply EqCannProjOwnIn.
  apply EqCannProjOwnIn.
 rewrite (DoubleClassificationEq _ _).
 hyperreflexivity.
assert(Inab : In [a2 ; b2] (Cartesian (%(EqCannProj (%ERel_to_Class erelA)) a1) (%(EqCannProj (%ERel_to_Class erelB)) b1))).
 rewrite EqCab.
 apply CartesianTheorem'.
 split.
 apply EqCannProjOwnIn.
 apply EqCannProjOwnIn.
apply CartesianTheorem' in Inab.
destruct Inab as [InaE2 InbE2].
rewrite (MapEq (EqCannProj_is_EqCls _)) in InaE2.
rewrite (MapEq (EqCannProj_is_EqCls _)) in InbE2.
apply EquivalenceClassTheorem in InaE2.
apply EquivalenceClassTheorem in InbE2.
split.
apply InaE2.
apply InbE2.


intro relHD.
destruct relHD as [relH1 relH2].
unfold DoubleERelation.
unfold If.
rewrite (USETEq _ (@ERel_Rel (Cartesian A B))).
rewrite (CombineMap'Theorem _ _ _ _ _ _).
rewrite (CombineMap'Theorem _ _ _ _ _ _).
rewrite (MapArgEq _ (MapArgEq _ (DoubleMapTheorem _ _ _ _))).
rewrite <- (USETEq _ (@ERel_Rel (Cartesian A B))).
rewrite <- EqPairPair'.
apply FoForm_If.
apply Class_to_ERelTheorem.
apply (ClassificationTheorem2 (Cartesian A B) (%DoubleClassifications [%ERel_to_Class erelA ; %ERel_to_Class erelB])).
 apply MapIn.
 apply SetProp.
 apply SetProp.
exists [a1 ; b1].
apply SectionTheorem.
split.
apply EqCannProjOwnIn.
assert(EqC : (%(EqCannProj (%DoubleClassifications [%ERel_to_Class erelA ; %ERel_to_Class erelB])) [a2 ; b2]) == (%DoubleClassification [%(EqCannProj (%ERel_to_Class erelA)) a1 ; %(EqCannProj (%ERel_to_Class erelB)) b1])).
 apply (ClassificationTheorem2 (Cartesian A B) (%DoubleClassifications [%ERel_to_Class erelA ; %ERel_to_Class erelB])).
 apply MapIn.
 apply SetProp.
 apply SetProp.
 exists [a2;b2].
 apply SectionTheorem.
 split.
 apply EqCannProjOwnIn.
 rewrite (DoubleClassificationEq _ _).
 apply CartesianTheorem'.
 split.
  rewrite (MapEq (EqCannProj_is_EqCls _)).
  apply EquivalenceClassTheorem.
  apply relH1.

  rewrite (MapEq (EqCannProj_is_EqCls _)).
  apply EquivalenceClassTheorem.
  apply relH2.
rewrite EqC.
rewrite (DoubleClassificationEq _ _).
apply CartesianTheorem'.
split.
 rewrite (MapEq (EqCannProj_is_EqCls _)).
 apply EquivalenceClassTheorem.
 cut (Rel_RefCond (erelA{<ERel_Rel})).
  intro cond.
  apply cond.
 apply Rel_Ref.
 apply ERel_Ref.
 apply (SetProp erelA).
 
 rewrite (MapEq (EqCannProj_is_EqCls _)).
 apply EquivalenceClassTheorem.
 cut (Rel_RefCond (erelB{<ERel_Rel})).
  intro cond.
  apply cond.
 apply Rel_Ref.
 apply ERel_Ref.
 apply (SetProp erelB).
Qed.

Theorem DoubleClassificationEqCannProj : forall {A B} (CA : #(Classifications A)) (CB : #(Classifications B)), forall a b,
%(EqCannProj (%DoubleClassifications [CA;CB])) [a ; b] ==
(%DoubleClassification [%(EqCannProj CA) a ; %(EqCannProj CB) b]).
Proof.
intros A B CA CB a b.
apply (ClassificationTheorem2 _ _ _ _ (SetProp (%DoubleClassifications [CA;CB]))).
 apply SetProp.
 apply SetProp.
exists [a;b].
apply SectionTheorem.
split.
apply EqCannProjOwnIn.
rewrite DoubleClassificationEq.
apply CartesianTheorem'.
split.
apply EqCannProjOwnIn.
apply EqCannProjOwnIn.
Qed.
 
Theorem DoubleClassificationsRelation : forall {A B} (CA : #(Classifications A)) (CB : #(Classifications B)), forall a a' b b',
&&(%Class_to_ERel (%DoubleClassifications [CA;CB])){<ERel_Rel} [a;b] [a';b'] <->
(&&(%Class_to_ERel CA){<ERel_Rel} a a' /\ &&(%Class_to_ERel CB){<ERel_Rel}b b').
Proof.
intros A B CA CB a a' b b'.
split.
 intro CH.
 apply Class_to_ERelTheorem in CH.
 rewrite DoubleClassificationEqCannProj in CH.
 rewrite DoubleClassificationEq in CH.
 rewrite DoubleClassificationEqCannProj in CH.
 rewrite DoubleClassificationEq in CH.
 assert(EqD : (%(EqCannProj CA) a) == (%(EqCannProj CA) a') /\ (%(EqCannProj CB) b) == (%(EqCannProj CB) b')).
  apply CartesianInjection.
   exists a.
   apply EqCannProjOwnIn.
   exists a'.
   apply EqCannProjOwnIn.
   exists b.
   apply EqCannProjOwnIn.
   exists b'.
   apply EqCannProjOwnIn.
  apply CH.
 destruct EqD as [Eqa Eqb].
 split.
  apply Class_to_ERelTheorem.
  apply Eqa.
 apply Class_to_ERelTheorem.
 apply Eqb.

 intro HD.
 destruct HD as [H1 H2].
 apply Class_to_ERelTheorem.
 rewrite DoubleClassificationEqCannProj.
 rewrite DoubleClassificationEq.
 rewrite DoubleClassificationEqCannProj.
 rewrite DoubleClassificationEq.
 apply Class_to_ERelTheorem in H1.
 apply Class_to_ERelTheorem in H2.
 rewrite H1.
 rewrite H2.
 hyperreflexivity.
Qed.
 

(* Class Quotient Map *)
Definition IsClassDividableMap {A B} : #(Relation (Cartesian (Classifications A) (Classifications B)) (Map A B)) :=
MakeRelation (fun co f => forall (a b : #A), &&(%Class_to_ERel (%MLeft co)){<ERel_Rel} a b -> &&(%Class_to_ERel (%MRight co)){<ERel_Rel} (%f a) (%f b)
).

Theorem IsClassDividableMapTheorem : forall {A B} (CA : #(Classifications A)) (CB : #(Classifications B)) (f : #(Map A B)),
&&IsClassDividableMap [CA;CB] f <->
(
  forall (a b : #A), &&(%Class_to_ERel CA){<ERel_Rel} a b -> &&(%Class_to_ERel CB){<ERel_Rel} (%f a) (%f b)
).
Proof.
intros.
split.
 intro IH.
 put ((proj1 (MakeRelationTheorem _ _ _ _ _)) IH) IH'.
 clear IH.
 put (IH' _ _ (ReflexivityEq _) (ReflexivityEq f)) IH.
 clear IH'.
 intros a b CH.
 cut ((&& ((%Class_to_ERel) ((%MLeft) [CA; CB])) {<ERel_Rel}) a b).
  intro CH'.
  generalize (IH _ _ CH').
  apply RelRewrite.
  apply (TransitivityEq _ (USETEq _ ERel_Rel)).
  apply SymmetryEq.
  apply (TransitivityEq _ (USETEq _ ERel_Rel)).
  apply MapArgEq.
  apply SymmetryEq.
  apply RightPairTheorem.
 generalize CH.
 apply RelRewrite.
 apply (TransitivityEq _ (USETEq _ ERel_Rel)).
 apply SymmetryEq.
 apply (TransitivityEq _ (USETEq _ ERel_Rel)).
 apply MapArgEq.
 apply LeftPairTheorem.
intro cond.
apply MakeRelationTheorem.
intros cacb f' Eqc Eqf a b relH.
apply SymmetryEq in Eqc.
cut (&&(%Class_to_ERel CB){<ERel_Rel} (%f a) (%f b)).
 apply RelRewriteAll.
 apply MapEq.
 apply Eqf.
 apply MapEq.
 apply Eqf.
 apply (TransitivityEq _ (USETEq _ ERel_Rel)).
 apply SymmetryEq.
 apply (TransitivityEq _ (USETEq _ ERel_Rel)).
 apply MapArgEq.
 rewrite (MapArgEq _ Eqc).
 apply RightPairTheorem.
apply cond.
generalize relH.
apply RelRewrite.
apply (TransitivityEq _ (USETEq _ ERel_Rel)).
apply SymmetryEq.
apply (TransitivityEq _ (USETEq _ ERel_Rel)).
apply SymmetryEq.
apply MapArgEq.
rewrite (MapArgEq _ Eqc).
apply LeftPairTheorem.
Qed.

Theorem IsClassDividableMapTheorem' : forall {A B} (CA : #(Classifications A)) (CB : #(Classifications B)) (f : #(Map A B)),
(
  forall (a b : #A), &&(%Class_to_ERel CA){<ERel_Rel} a b -> &&(%Class_to_ERel CB){<ERel_Rel} (%f a) (%f b)
)
<->
&&IsClassDividableMap [CA;CB] f
.
Proof.
intros A B CA CB f.
apply SymmetryEquiv.
apply IsClassDividableMapTheorem.
Qed.


Definition ClassDividableMap {A B} : #(Map (Cartesian (Classifications A) (Classifications B)) (PowerSet (Map A B))) :=
%RelImageE (IsClassDividableMap).

Theorem ClassDividableMapTheorem : forall {A B} (CA : #(Classifications A)) (CB : #(Classifications B)) (f : #(Map A B)),
In f (%ClassDividableMap [CA ; CB]) <->
(&&IsClassDividableMap [CA ; CB] f).
Proof.
intros A B CA CB f.
unfold ClassDividableMap.
unfold ClassDividableMap.
apply RelationImageETheorem.
Qed.

Theorem CDMap_Map : forall {A B} {CA : #(Classifications A)} {CB : #(Classifications B)},
Subset (%ClassDividableMap [CA;CB]) (Map A B).
Proof.
intros A B CA CB.
unfold ClassDividableMap.
apply RelationImageESubset.
Qed.

Theorem CDMap_Rel : forall {A B} {CA : #(Classifications A)} {CB : #(Classifications B)},
Subset (%ClassDividableMap [CA;CB]) (Relation A B).
Proof.
intros A B CA CB.
apply (TransitivitySubset (Map A B)).
 apply CDMap_Map.
apply Map_Rel.
Qed.

Theorem ClassDivMapInCond : forall {A B} (CA : #(Classifications A)) (CB : #(Classifications B)),
In 
(%CombineMap' [(%CombMap (EqCannProj CB)) ; %CombineMap' [EmbedMap Map_Rel ; %CombRelation (%InverseRel ((EqCannProj CA){<Map_Rel}))]])
(RistableMap (Map A B) (Relation CA CB) (%ClassDividableMap [CA ; CB]) (Map CA CB)).
Proof.
intros A B CA CB.
apply RistableMapTheorem.
split.
{
  split. 
  apply CDMap_Map.
  apply Map_Rel.
}
intros f InfC.
rewrite (CombineMap'Theorem _ _ _ _ _ _).
rewrite (CombineMap'Theorem _ _ _ _ _ _).
apply Rel_Map.
intro sa.
split.
 assert(NEsa : NonEmpty sa).
  apply (ClassificationTheorem3 _ _ (SetProp CA)).
  apply SetProp.
 destruct NEsa as [_a Inasa].
 assert(InaA : In _a A).
  apply (ClassificationIn A CA sa).
  apply SetProp.
  apply SetProp.
  apply Inasa.
 set {_a ! InaA} as a.
 exists (%(EqCannProj CB) (%f a)).
 apply CombRelationTheorem.
 exists a.
 split.
  apply InverseRelTheorem'.
  apply AppMapRel.
  apply (ClassificationTheorem2 _ _ _ _ (SetProp CA)).
  apply SetProp.
  apply SetProp.
  exists a.
  apply SectionTheorem.
  split.
  apply EqCannProjOwnIn.
  apply Inasa.

  cut (&&(%(%CombMap (EqCannProj CB)) f){<Map_Rel} a (%(EqCannProj CB) (%f a))).
   apply RelRewrite.
   rewrite (USETEq _ Map_Rel).
   apply SymmetryEq.
   rewrite EmbedMapEq.
   hyperreflexivity.
  apply AppMapRel.
  rewrite (CombMapTheorem _ _ _ _ _ _).
  hyperreflexivity.

 intros sb1 sb2 condD.
 destruct condD as [cond1 cond2].
 apply CombRelationTheorem in cond1.
 destruct cond1 as [a1 cond1].
 destruct cond1 as [cond11 cond12'].
 apply InverseRelTheorem in cond11.
 assert(cond12 : &&(%(%CombMap (EqCannProj CB)) f){<Map_Rel} a1 sb1).
  generalize cond12'.
  apply RelRewrite.
  rewrite (USETEq _ Map_Rel).  
  rewrite EmbedMapEq.
  hyperreflexivity.
 clear cond12'.
 apply AppTheoremReverse in cond12.
 rewrite CombMapTheorem in cond12.
 apply CombRelationTheorem in cond2.
 destruct cond2 as [a2 cond2].
 destruct cond2 as [cond21 cond22'].
 apply InverseRelTheorem in cond21.
 assert(cond22 : &&(%(%CombMap (EqCannProj CB)) f){<Map_Rel} a2 sb2).
  generalize cond22'.
  apply RelRewrite.
  rewrite (USETEq _ Map_Rel).  
  rewrite EmbedMapEq.
  hyperreflexivity.
 clear cond22'.
 apply AppTheoremReverse in cond22.
 rewrite CombMapTheorem in cond22.
 rewrite <- cond12.
 rewrite <- cond22.
 apply Class_to_ERelTheorem.
 apply ClassDividableMapTheorem in InfC.
 put ((proj1 (IsClassDividableMapTheorem _ _ _)) InfC) InfC'.
 apply InfC'. 
 apply Class_to_ERelTheorem.
 apply AppTheoremReverse in cond11.
 apply AppTheoremReverse in cond21.
 rewrite cond11.
 rewrite cond21.
 hyperreflexivity.
Qed.



Definition ClassDivMap {A B} (CA : #(Classifications A)) (CB : #(Classifications B)) : #(Map (%ClassDividableMap [CA ; CB]) (Map CA CB)) :=
%RistMap {_ ! @ClassDivMapInCond A B CA CB}.

Theorem ClassDivMapTheorem : forall {A B} (CA : #(Classifications A)) (CB : #(Classifications B)) (f : #(%ClassDividableMap [CA;CB])) a,
%(%(ClassDivMap _ _) f) (%(EqCannProj CA) a) == %(EqCannProj CB) (%(f{<CDMap_Map}) a).
Proof.
intros A B CA CB fc a.
unfold ClassDivMap.
apply AppTheoremReverse.
set (fc{<CDMap_Map}) as f.
cut (&&(%(%CombineMap' [%CombMap (EqCannProj CB) ; %CombineMap' [EmbedMap Map_Rel ; %CombRelation (%InverseRel ((EqCannProj CA){<Map_Rel}))]]) f) (%(EqCannProj CA) a) (%(EqCannProj CB) (%f a))).
 apply RelRewrite.
 apply SymmetryEq.
 rewrite (USETEq _ Map_Rel).
 apply MapStrong.
  apply StrongRistMapEq.
  hyperreflexivity.
 hyperreflexivity.
apply (RelRewrite' (CombineMap'Theorem _ _ _ _ _ _)).
apply (RelRewrite' (CombineMap'Theorem _ _ _ _ _ _)).
apply CombRelationTheorem.
exists a.
split.
 apply InverseRelTheorem'.
 apply AppTheorem.
cut (&&(%(%CombMap (EqCannProj CB)) f){<Map_Rel} a (%(EqCannProj CB) (%f a))).
 apply RelRewrite.
 rewrite EmbedMapEq.
 hyperreflexivity.
apply AppMapRel.
rewrite CombMapTheorem.
hyperreflexivity.
Qed.



Definition RightClassDivMap {A B} (C : #(Classifications B)) : #(Map (Map A B) (Map A C)) :=
%CombMap (EqCannProj C).

Theorem RightClasssDivMapEqv : forall {A B} (C : #(Classifications B)) (f : #(Map A B)) (a : #A),
%(%(RightClassDivMap C) f) a == %(EqCannProj C) (%f a).
Proof.
intros A B C f a.
unfold RightClassDivMap.
rewrite (CombMapTheorem _ _ _).
hyperreflexivity.
Qed.


(*
Definition LeftClassDividableMap A B (C : #(Classifications A)) :=
SSet' (Map A B) (fun f => forall (a b : #A), &&(%Class_to_ERel C){<ERel_Rel} a b -> %f a == %f b).


Theorem LeftClassDividableMapTheorem : forall A B (C : #(Classifications A)) (f : #(Map A B)),
In f (LeftClassDividableMap A B C) <->
(forall (a b : #A), &&(%Class_to_ERel C){<ERel_Rel} a b -> %f a == %f b).
Proof.
intros A B C f.
split.
 intro InfL.
 apply SSet'Theorem in InfL.
 destruct InfL as [InfAB InfL].
 intros a b relH.
 apply (TransitivityEq (%{f ! InfAB} a)).
  hyperreflexivity.
 apply (TransitivityEq (%{f ! InfAB} b)).
  apply (InfL).
  assumption.
 hyperreflexivity.

 intros cond.
 apply SSet'Theorem.
 split.
 apply SetProp.
 intros InfAB a b relH.
 apply (TransitivityEq (%f a)).
  hyperreflexivity.
 apply (TransitivityEq (%f b)).
  apply (cond).
  assumption.
 hyperreflexivity.
Qed.

Theorem LCDCMap_Map : forall {A B C}, Subset (LeftClassDividableMap A B C) (Map A B).
Proof.
intros A B C.
apply SSet'Subset.
Qed.

Theorem LCDCMap_Rel : forall {A B C}, Subset (LeftClassDividableMap A B C) (Relation A B).
Proof.
intros A B C.
apply (TransitivitySubset (Map A B)).
 apply LCDCMap_Map.
apply Map_Rel.
Qed.



Theorem LeftClassDivMapInCond : forall {A B} (C : #(Classifications A)),
In (%(@CombRelation C A B) (%InverseRel ((EqCannProj C) {<Map_Rel}))) (RistableMap (Relation A B) (Relation C B) (LeftClassDividableMap A B C) (Map C B)).
Proof.
intros A B C.
apply RistableMapTheorem.
split.
 apply (TransitivitySubset (Map A B)).
  apply LCDCMap_Map.
 apply Map_Rel.
split.
 apply Map_Rel.
intros frel InfrelLC.
assert(InfrelM : In frel (Map A B)).
 apply (@LCDCMap_Map _ _ C).
 assumption.
set {frel ! InfrelM} as f.
apply Rel_Map.
intro S.
split.
 assert(NES : NonEmpty S).
  apply (ClassificationTheorem3 _ _ (SetProp C)).
  apply SetProp.
 destruct NES as [a_ NES].
 assert(InaA : In a_ A).
  apply (ClassificationIn A C S a_).
  apply SetProp.
  apply SetProp.
  assumption.
 set {a_ ! InaA} as a.
 exists (%f a).
 apply CombRelationTheorem.
 exists a.
 split.
  apply InverseRelTheorem'.
  apply AppMapRel.
  apply (ClassificationTheorem2 _ _ _ _ (SetProp C)).
  apply SetProp.
  apply SetProp.
  exists a.
  apply SectionTheorem.
  split.
  apply EqCannProjOwnIn.
  apply NES.
 apply AppTheorem.

intros b1 b2 relD.
destruct relD as [relH1 relH2].
apply (CombRelationTheorem _ _ _ _) in relH1.
destruct relH1 as [a1 relH1].
destruct relH1 as [relH1 frelH1].
apply InverseRelTheorem in relH1.
apply AppTheoremReverse in relH1.
apply (CombRelationTheorem _ _ _ _) in relH2.
destruct relH2 as [a2 relH2].
destruct relH2 as [relH2 frelH2].
apply InverseRelTheorem in relH2.
apply AppTheoremReverse in relH2.
assert(Eqf : frel == f).
 hyperreflexivity.
rewrite Eqf in InfrelLC.
clear Eqf.
put ((proj1 (LeftClassDividableMapTheorem A B C f)) InfrelLC) frelc.
assert(fa1 : %f a1 == b1).
 apply AppTheoremReverse.
 generalize frelH1.
 apply RelRewrite.
 hyperreflexivity.
assert(fa2 : %f a2 == b2).
 apply AppTheoremReverse.
 generalize frelH2.
 apply RelRewrite.
 hyperreflexivity.
rewrite <- fa1.
rewrite <- fa2.
apply frelc.
apply Class_to_ERelTheorem.
rewrite relH1.
rewrite relH2.
hyperreflexivity.
Qed.

Definition LeftClassDivMap {A B} (C : #(Classifications A)) : #(Map (LeftClassDividableMap A B C) (Map C B)) :=
%RistMap {_ ! @LeftClassDivMapInCond A B C}.

Theorem LeftClassDivMapTheorem : forall {A B} (C : #(Classifications A)) (f : #(LeftClassDividableMap A B C)) (a : #A),
%(%(LeftClassDivMap _) f) (%(EqCannProj C) a) == %(f{<LCDCMap_Map}) a.
Proof.
intros A B C f a.
unfold LeftClassDivMap.
set (f{<LCDCMap_Rel}) as rel.
set (f{<LCDCMap_Map}) as ff.
apply AppTheoremReverse.
cut (&&(%(%CombRelation (%InverseRel ((EqCannProj C){<Map_Rel}))) rel) (%(EqCannProj C) a) (%ff a)).
 apply RelRewriteAll.
 hyperreflexivity.
 hyperreflexivity.
 apply SymmetryEq.
 rewrite (USETEq _ Map_Rel).
 apply RistMapEq2.
 hyperreflexivity.
apply (CombRelationTheorem).
exists a.
split.
 apply InverseRelTheorem'.
 apply AppTheorem.
cut (&&(ff{<Map_Rel}) a (%ff a)).
 apply RelRewrite.
 hyperreflexivity.
apply AppTheorem.
Qed.
*)




