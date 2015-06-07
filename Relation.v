Require Import logic.
Require Import IZF.
 
Definition Relation A B := PowerSet (Cartesian A B).
Definition BRelation A := Relation A A.
Theorem Rel_BRel : forall {A}, Subset (Relation A A) (BRelation A).
Proof.
intros A.
apply ReflexivitySubset.
Qed.
Theorem BRel_Rel : forall {A}, Subset (BRelation A) (Relation A A).
Proof.
intros A.
apply ReflexivitySubset.
Qed.


Definition If {A B} (rel : (#Relation A B)) (a : #A) (b : #B) :=
  In (Pair a b) rel.
Notation "&& rel" := (If rel) (at level 10).

Theorem ToForm_If : forall A B (rel : #(Relation A B)) (a : #A) (b : #B),
In [a;b] rel -> &&rel a b.
Proof.
tauto.
Qed.

Theorem FoForm_If : forall A B (rel : #(Relation A B)) (a : #A) (b : #B),
&&rel a b -> In [a;b] rel.
tauto.
Qed.


Theorem PairInRelation : forall {A B} (rel : (#Relation A B)),
forall a b, In (Pair a b) rel -> (In a A /\ In b B).
Proof.
intros A B rel a b InPr.
generalize (SetProp rel); intro rel'.
apply PowersetTheorem in rel'.
apply rel' in InPr. 
apply CartesianTheorem in InPr.
auto.
Qed.

Theorem RelationIn : forall {A B} (rel : #(Relation A B)),
forall a b, &&rel a b -> In a A /\ In b B.
Proof.
intros A B rel a b RelH.
unfold If in RelH.
apply PairInRelation in RelH.
assumption.
Qed.


Theorem RelRewriteL : forall {A B},
forall {a1 : #A} {a2 : #A} {b : #B} {rel : #(Relation A B)},
a1 == a2 -> ((&&rel) a1 b -> (&&rel) a2 b).
Proof.
intros A B a1 a2 b rel Eq relH.
unfold If in relH.
rewrite Eq in relH.
apply relH.
Qed.

Theorem RelRewriteR : forall {A B},
forall {a : #A} {b1 : #B} {b2 : #B} {rel : #(Relation A B)},
b1 == b2 -> ((&&rel) a b1 -> (&&rel) a b2).
Proof.
intros A B a b1 b2 rel Eq relH.
unfold If in relH.
rewrite Eq in relH.
apply relH.
Qed.

Theorem RelRewrite : forall {A B},
forall {a : #A} {b : #B} {rel1 rel2 : #(Relation A B)},
rel1 == rel2 -> ((&&rel1) a b -> (&&rel2) a b).
Proof.
intros A B a b rel1 rel2 Eq relH.
unfold If in relH.
rewrite Eq in relH.
apply relH.
Qed.

Theorem RelRewriteAll : forall {A1 A2 B1 B2} {rel1 : #(Relation A1 B1)} {rel2 : #(Relation A2 B2)}
{a1 : #A1} {b1 : #B1} {a2 : #A2} {b2 : #B2},
a1 == a2 -> b1 == b2 -> rel1 == rel2 ->
((&&rel1) a1 b1 -> (&&rel2) a2 b2).
Proof.
intros A1 A2 B1 B2 rel1 rel2 a1 b1 a2 b2 Eqa Eqb Eqrel relH.
unfold If in relH.
rewrite Eqa in relH.
rewrite Eqb in relH.
rewrite Eqrel in relH.
apply relH.
Qed.

Theorem RelRewriteL' : forall {A B},
forall {a1 : #A} {a2 : #A} {b : #B} {rel : #(Relation A B)},
a1 == a2 -> ((&&rel) a2 b -> (&&rel) a1 b).
Proof.
intros A B a1 a2 b rel Eq relH.
generalize relH.
apply (RelRewriteL).
apply SymmetryEq.
apply Eq.
Qed.

Theorem RelRewriteR' : forall {A B},
forall {a : #A} {b1 : #B} {b2 : #B} {rel : #(Relation A B)},
b1 == b2 -> ((&&rel) a b2 -> (&&rel) a b1).
Proof.
intros A B a b1 b2 rel Eq.
apply RelRewriteR.
apply SymmetryEq.
assumption.
Qed.

Theorem RelRewrite' : forall {A B},
forall {a : #A} {b : #B} {rel1 rel2 : #(Relation A B)},
rel1 == rel2 -> ((&&rel2) a b -> (&&rel1) a b).
Proof.
intros A B a b rel1 rel2 Eq.
apply RelRewrite.
rewrite Eq.
apply ReflexivityEq.
Qed.


Theorem SubsetInRelationL : forall A1 A2 B,
Subset A1 A2 ->
Subset (Relation A1 B) (Relation A2 B).
Proof.
intros A1 A2 B sub.
intros c IncR.
apply PowersetTheorem in IncR.
apply PowersetTheorem.
apply (TransitivitySubset (Cartesian A1 B)).
auto.
apply SubsetInCartesianL.
auto.
Qed.


Theorem SubsetInRelationR : forall A B1 B2,
Subset B1 B2 ->
Subset (Relation A B1) (Relation A B2).
Proof.
intros A B1 B2 sub.
intros c IncR.
apply PowersetTheorem in IncR.
apply PowersetTheorem.
apply (TransitivitySubset (Cartesian A B1)).
auto.
apply SubsetInCartesianR.
auto.
Qed.

Theorem SubsetInRelation : forall A1 A2 B1 B2,
Subset A1 A2 -> Subset B1 B2 ->
Subset (Relation A1 B1) (Relation A2 B2).
Proof.
intros A B C D sub1 sub2.
apply (TransitivitySubset (Relation A D)).
 apply SubsetInRelationR.
 assumption.
apply SubsetInRelationL.
assumption.
Qed.


Theorem IsPairRelation : forall {A B} (rel : #(Relation A B)),
forall x, In x rel -> IsPair x.
Proof.
intros A B rel x Inxr.
generalize (SetProp rel); intro relH.
apply PowersetTheorem in relH.
apply relH in Inxr.
apply CartesianIsPair in Inxr.
auto.
Qed.

Theorem IsPair'Relation : forall A B (rel : #(Relation A B)),
forall x , In x rel ->
exists a : #A, exists b : #B,
x == [a;b].
Proof.
intros A B rel x InxR.
put (SetProp rel) Inrel.
apply PowersetTheorem in Inrel.
apply Inrel in InxR.
put (CartesianIsPair' _ _ _ InxR) IsPrel.
apply IsPrel.
Qed.

Theorem Relation_Cartesian : forall A B (rel : #(Relation A B)),
Subset rel (Cartesian A B).
Proof.
intros A B rel.
intros p Inprel.
put (SetProp rel) Inrel.
apply PowersetTheorem in Inrel.
apply Inrel.
apply Inprel.
Qed.



(* Strongeth Relation *)

Definition StrongRel {A B C D}
(rel1 : #(Relation A B)) (rel2 : #(Relation C D)) :=
Subset rel1 rel2.

Theorem ReflexivityStrongRel : forall {A B} (rel : #(Relation A B)),
StrongRel rel rel.
Proof.
intros A B rel.
apply ReflexivitySubset.
Qed.

Theorem ReflexivityStrongRel2 : forall {A1 B1 A2 B2} (rel1 : #(Relation A1 B1)) (rel2 : #(Relation A2 B2)),
rel1 == rel2 -> StrongRel rel1 rel2.
Proof.
intros A1 B1 A2 B2 rel1 rel2 Eqrel.
unfold StrongRel.
rewrite Eqrel.
apply ReflexivitySubset.
Qed.

Theorem AntisymmetryStrongRel : forall {A1 B1 A2 B2} (rel1 : #(Relation A1 B1)) (rel2 : #(Relation A2 B2)),
StrongRel rel1 rel2 -> StrongRel rel2 rel1 -> rel1 == rel2.
Proof.
intros A1 B1 A2 B2 rel1 rel2.
apply AntisymmetrySubset.
Qed.

Theorem TransitivityStrongRel : forall {A1 B1 A2 B2 A3 B3} {rel1 : #(Relation A1 B1)} {rel3 : #(Relation A3 B3)} (rel2 : #(Relation A2 B2)),
StrongRel rel1 rel2 -> StrongRel rel2 rel3 -> StrongRel rel1 rel3.
Proof.
intros.
apply (TransitivitySubset (rel2)).
assumption.
assumption.
Qed.

Theorem StrongRelRewrite : forall {A1 B1 A2 B2} (rel1 : #(Relation A1 B1)) (rel2 : #(Relation A2 B2)),
rel1 == rel2 -> StrongRel rel1 rel2.
Proof.
intros A1 B1 A2 B2 rel1 rel2 Eqrel.
unfold StrongRel.
rewrite Eqrel.
apply ReflexivitySubset.
Qed.

Theorem StrongRelRewriteL : forall {A1 B1 A2 B2 C D} {rel1 : #(Relation A1 B1)} {rel2 : #(Relation A2 B2)} {rel : #(Relation C D)},
rel1 == rel2 -> (StrongRel rel1 rel) -> (StrongRel rel2 rel).
Proof.
intros A1 B1 A2 B2 C D rel1 rel2 rel Eqrel SH.
apply (TransitivityStrongRel rel1).
apply ReflexivityStrongRel2.
rewrite Eqrel.
apply ReflexivityEq.
apply SH.
Qed.

Theorem StrongRelRewriteL' : forall {A1 B1 A2 B2 C D} {rel1 : #(Relation A1 B1)} {rel2 : #(Relation A2 B2)} {rel : #(Relation C D)},
rel1 == rel2 -> (StrongRel rel2 rel) -> (StrongRel rel1 rel).
Proof.
intros A1 B1 A2 B2 C D rel1 rel2 rel Eqrel SH.
apply SymmetryEq in Eqrel.
apply (StrongRelRewriteL Eqrel).
apply SH.
Qed.

Theorem StrongRelRewriteR : forall {A1 B1 A2 B2 C D} {rel1 : #(Relation A1 B1)} {rel2 : #(Relation A2 B2)} {rel : #(Relation C D)},
rel1 == rel2 -> (StrongRel rel rel1) -> (StrongRel rel rel2).
Proof.
intros A1 B1 A2 B2 C D rel1 rel2 rel Eqrel SH.
apply (TransitivityStrongRel rel1).
apply SH.
apply ReflexivityStrongRel2.
rewrite Eqrel.
apply ReflexivityEq.
Qed.

Theorem StrongRelRewriteR' : forall {A1 B1 A2 B2 C D} {rel1 : #(Relation A1 B1)} {rel2 : #(Relation A2 B2)} {rel : #(Relation C D)},
rel1 == rel2 -> (StrongRel rel rel2) -> (StrongRel rel rel1).
Proof.
intros A1 B1 A2 B2 C D rel1 rel2 rel Eqrel SH.
apply SymmetryEq in Eqrel.
apply (StrongRelRewriteR Eqrel).
apply SH.
Qed.


Theorem ToStrongRel : forall {A B C D}
(rel1 : #(Relation A B)) (rel2 : #(Relation C D)),
(forall (a : #A) (b : #B),
(&&rel1) a b -> exists c : #C, exists d : #D, a == c /\ b == d /\ (&&rel2 c d)) ->
StrongRel rel1 rel2.
Proof.
intros A B C D rel1 rel2 Cond.
intros p Inprel1.
put (IsPairRelation _ _ Inprel1) IsPrel1.
destruct IsPrel1 as [a IsPrel1].
destruct IsPrel1 as [b Isprel1].
rewrite Isprel1 in Inprel1.
rewrite Isprel1.
clear Isprel1.
assert(InD : In a A /\ In b B).
 apply (PairInRelation rel1).
 assumption.
destruct InD as [InaA InbB].
assert(CondCond : (&&rel1) {a ! InaA} {b ! InbB}).
 unfold If.
 apply Inprel1.
put (Cond _ _ CondCond) Cond'.
clear Cond.
destruct Cond' as [c Cond].
destruct Cond as [d Cond].
destruct Cond as [Eqac Cond].
destruct Cond as [Eqbd Cond].
unfold If in Cond.
rewrite <- Eqac in Cond.
rewrite <- Eqbd in Cond.
apply Cond.
Qed.



Theorem StrongRelationRelExists : forall {A B C D}
(rel1 : #(Relation A B)) (rel2 : #(Relation C D))
(a : #A) (b : #B),
StrongRel rel1 rel2 -> (&&rel1) a b -> 
exists p1 : In a C, exists p2 : In b D,
(&&rel2) {a!p1} {b!p2}.
Proof.
intros A B C D.
intros rel1 rel2 a b SH relH1.
assert (InP : In (Pair a b) rel2).
 apply SH.
 auto.
assert (sub2 : In rel2 (Relation C D)).
 auto.
assert (InE : In a C /\ In b D).
 apply PowersetTheorem in sub2.
 apply sub2 in InP.
 apply CartesianTheorem in InP.
 auto.
destruct InE as [c d].
exists c.
exists d.
apply InP.
Qed.

Theorem StrongRelationRel : forall {A B C D}
{rel1 : #(Relation A B)} {rel2 : #(Relation C D)}
{a : #A} {b : #B} {c : #C} {d : #D},
a == c -> b == d ->
StrongRel rel1 rel2 -> (&&rel1) a b -> (&&rel2) c d.
Proof.
intros A B C D rel1 rel2 a b c d Eq1 Eq2 SH Hr1.
apply (StrongRelationRelExists _ _ _ _ SH) in Hr1.
destruct Hr1 as [c' Hr1].
destruct Hr1 as [d' Hr1].
assert(Eqr : {a ! c'} == c).
 rewrite <- Eq1.
 apply ReflexivityEq.
apply (RelRewriteL Eqr).
assert(Eql : {b ! d'} == d).
 rewrite <- Eq2.
 apply ReflexivityEq.
apply (RelRewriteR Eql).
auto.
Qed.

Theorem StrongRelationRelSameD : forall {A B}
{rel1 : #(Relation A B)} {rel2 : #(Relation A B)}
{a : #A} {b : #B},
StrongRel rel1 rel2 -> (&&rel1) a b -> (&&rel2) a b.
Proof.
intros A B rel1 rel2 a b SR.
apply StrongRelationRel.
apply ReflexivityEq.
apply ReflexivityEq.
apply SR.
Qed.


Theorem RelEquality : forall {A B C D}
(rel1 : #(Relation A B)) (rel2 : #(Relation C D)),
rel1 == rel2 <-> (StrongRel rel1 rel2 /\ StrongRel rel2 rel1).
Proof.
intros A B C D rel1 rel2.
split.

intro Eqrel.
split.
 cut (Subset rel1 rel2).
 intro sub.
 apply sub.
 rewrite Eqrel.
 apply ReflexivitySubset.

 cut (Subset rel2 rel1).
 intro sub.
 apply sub.
 rewrite Eqrel.
 apply ReflexivitySubset.


intro DS.
destruct DS as [S1 S2].
apply AntisymmetrySubset.
apply S1.
apply S2.
Qed.


Notation "c {< sub ! cond }" := {c ! ((proj1 (sub c)) cond)} (at level 2).
Notation "[ c1 ; c2 ]{<2 sub ! cond }" := {[c1;c2] ! ((proj1 (sub c1 c2)) cond)} (at level 7).

(** RightUnique **)
Definition RightUnique A B := SSet' (Relation A B)
(fun r => forall (a : #A) ,
Atmost' (fun (b : (#B)) => ((&&r) a b))
).

Theorem RUnq_Rel : forall {A B}, (Subset (RightUnique A B) (Relation A B)).
Proof.
intros A B.
apply SSetSubset.
Qed.
Hint Immediate @RUnq_Rel.

Definition Rel_RUnqCond {A B} (rel : #(Relation A B)) :=
forall (a : #A), Atmost'(fun b : (#B) => (&&rel) a b).

Theorem Rel_RUnq : forall {A B} (rel : #(Relation A B)),
Rel_RUnqCond rel <-> In rel (RightUnique A B).
Proof.
intros A B rel.
split.
intro Cond.
apply SSet'Theorem.
split.
apply SetProp.
intros relR a.
unfold Rel_RUnqCond in Cond.
apply (Cond a).

intro InR.
intros a b1 b2 H1 H2.
apply SSet'Theorem in InR.
destruct InR as [InR RCon].
apply (RCon InR a).
generalize H1.
apply RelRewrite.
apply ReflexivityEq.
generalize H2.
apply RelRewrite.
apply ReflexivityEq.
Qed.


Theorem Rel_RUnqCond_StrongCons : forall {A1 B1 A2 B2} (rel1 : #(Relation A1 B1)) (rel2 : #(Relation A2 B2)),
StrongRel rel1 rel2 -> Rel_RUnqCond rel2 -> Rel_RUnqCond rel1.
Proof.
intros A1 B1 A2 B2 rel1 rel2 SR InrR2.
intro a.
intros b1 b2 relH1 relH2.
put (StrongRelationRelExists _ _ _ _ SR relH1) relH1'.
destruct relH1' as [InaA2 relH1'].
destruct relH1' as [InbB2 relH1'].
set {a ! InaA2} as a'.
set {b1 ! InbB2} as b1'.
put (StrongRelationRelExists _ _ _ _ SR relH2) relH2'.
destruct relH2' as [InaA2' relH2'].
destruct relH2' as [InbB2' relH2'].
set {b2 ! InbB2'} as b2'.
apply (TransitivityEq b1').
 apply ReflexivityEq.
apply (TransitivityEq b2').
 apply (Atmost'EqApply _ (InrR2 a')).
 split.
 apply relH1'.
 apply relH2'.
apply ReflexivityEq.
Qed.

Theorem RightUniqueEq : forall {A B} (rel : #(Relation A B)) a b c,
Rel_RUnqCond rel ->
&&rel a b -> &&rel a c -> b == c.
Proof.
intros A B rel a b c RC relH1 relH2.
apply (Atmost'EqApply _ (RC a)).
split; assumption.
Qed.


(* LeftUnique *)
Definition LeftUnique A B := SSet' (Relation A B)
(fun r => forall (b : #B) ,
Atmost' (fun a : #A => ((&&r) a b))
).

Theorem LUnq_Rel : forall {A B}, (Subset (LeftUnique A B) (Relation A B)).
Proof.
intros A B.
apply SSetSubset.
Qed.

Definition Rel_LUnqCond {A B} (rel : #(Relation A B)) :=
forall (b : #B), Atmost'(fun a : (#A) => (&&rel) a b).

Theorem Rel_LUnq : forall {A B} (rel : #(Relation A B)),
Rel_LUnqCond rel <-> In rel (LeftUnique A B).
Proof.
intros A B rel.
split.
intro Cond.
apply SSet'Theorem.
split.
apply SetProp.
intros relR a.
unfold Rel_LUnqCond in Cond.
apply (Cond a).

intro InR.
intros a b1 b2 H1 H2.
apply SSet'Theorem in InR.
destruct InR as [InR RCon].
apply (RCon InR a).
generalize H1.
apply RelRewrite.
apply ReflexivityEq.
generalize H2.
apply RelRewrite.
apply ReflexivityEq.
Qed.

(* Right Total *)
Definition RightTotal A B := SSet' (Relation A B)
(fun r => forall (b : #B) , exists a : #A, (&&r) a b).

Theorem RTtl_Rel : forall {A B}, (Subset (RightTotal A B) (Relation A B)).
Proof.
intros A B.
apply SSet'Subset.
Qed.
(*Hint Immediate @LTtl_Rel.*)

Definition Rel_RTtlCond {A B} (rel : #(Relation A B)) := 
forall (b : #B), exists a : #A,
(&&rel) a b.


Definition Rel_RTtl : forall {A B} (rel : #(Relation A B)),
Rel_RTtlCond rel <-> In rel (RightTotal A B).
Proof.
intros A B rel.
split.
intro RCon.
apply SSet'Theorem.
split; auto.

intro InL.
apply SSet'Theorem in InL.
destruct InL as [InR InL].
intro a.
destruct (InL InR a) as [b InL'].
exists b.
generalize InL'.
apply RelRewrite.
apply ReflexivityEq.
Qed.


(* LeftTotal *)
Definition LeftTotal A B := SSet' (Relation A B)
(fun r => forall (a : #A) , exists b : #B, (&&r) a b).

Theorem LTtl_Rel : forall {A B}, (Subset (LeftTotal A B) (Relation A B)).
Proof.
intros A B.
apply SSet'Subset.
Qed.
(*Hint Immediate @LTtl_Rel.*)

Definition Rel_LTtlCond {A B} (rel : #(Relation A B)) := 
forall (a : #A), exists b : #B,
(&&rel) a b.


Definition Rel_LTtl : forall {A B} (rel : #(Relation A B)),
Rel_LTtlCond rel <-> In rel (LeftTotal A B).
Proof.
intros A B rel.
split.
intro RCon.
apply SSet'Theorem.
split; auto.

intro InL.
apply SSet'Theorem in InL.
destruct InL as [InR InL].
intro a.
destruct (InL InR a) as [b InL'].
exists b.
generalize InL'.
apply RelRewrite.
apply ReflexivityEq.
Qed.

Theorem LeftTotalHasSameDomain : forall {A1 B1 A2 B2}
(rel1 : #(LeftTotal A1 B1)) (rel2 : #(LeftTotal A2 B2)), rel1 == rel2 -> A1 == A2.
Proof.
intros A1 B1 A2 B2 rel1 rel2 Eqrel.
assert(rel1' : Rel_LTtlCond (rel1{<LTtl_Rel})).
 apply Rel_LTtl.
 apply (SetProp rel1).
assert(rel2' : Rel_LTtlCond (rel2{<LTtl_Rel})).
 apply Rel_LTtl.
 apply (SetProp rel2).
apply EA.
 intro c.
 split.

 intro IncA1.
 destruct (rel1' {c ! IncA1}) as [b relH].
 assert(InPR : In (Pair c b) rel2).
  rewrite <- Eqrel.
  auto.
 apply (PairInRelation (rel2{<LTtl_Rel})) in InPR.
 tauto.

 intro IncA2.
 destruct (rel2' {c ! IncA2}) as [b relH].
 assert(InPR : In (Pair c b) rel1).
  rewrite Eqrel.
  auto.
 apply (PairInRelation (rel1{<LTtl_Rel})) in InPR.
 tauto.
Qed.

Theorem StrongLeftTotalSubset : forall {A1 B1 A2 B2}
(rel1 : #(LeftTotal A1 B1)) (rel2 : #(LeftTotal A2 B2)), 
StrongRel rel1{<LTtl_Rel} rel2{<LTtl_Rel} -> Subset A1 A2.
Proof.
intros A1 B1 A2 B2 rel1 rel2 SH.
intros a InaA1.
put (SetProp rel1) Inrel1.
rewrite (USETEq' _ LTtl_Rel) in Inrel1.
apply Rel_LTtl in Inrel1.
put (Inrel1 {a ! InaA1}) Inrel1'.
destruct Inrel1' as [b relH].
put (StrongRelationRelExists _ _ _ _ SH relH) relH'.
destruct relH' as [InaA2 relH'].
apply InaA2.
Qed.


  


(* Map *)
Definition Map D R := Section (LeftTotal D R) (RightUnique D R).

Theorem Map_RUnq : forall {D R} , Subset (Map D R) (RightUnique D R).
Proof.
intros D R.
apply SectionSubsetR.
Qed.
Hint Immediate @Map_RUnq.

Theorem Map_LTtl : forall {D R} , Subset (Map D R) (LeftTotal D R).
Proof.
intros D R.
apply SectionSubsetL.
Qed.
Hint Immediate @Map_LTtl.



Theorem Map_Rel : forall {D R}, Subset (Map D R) (Relation D R).
Proof.
intros D R.
apply (TransitivitySubset (RightUnique D R)); auto.
Qed.
Hint Immediate @Map_Rel.

Definition Rel_MapCond2 {A B} (rel : #(Relation A B)) :=
(Rel_LTtlCond rel) /\ (Rel_RUnqCond rel).

Theorem Rel_Map2 : forall {A B} (rel : #(Relation A B)),
Rel_MapCond2 rel <-> In rel (Map A B).
Proof.
intros A B rel.
split.
intro Cond.
destruct Cond as [LCond RCond].
apply SectionTheorem.
split.
apply Rel_LTtl.
assumption.
apply Rel_RUnq.
assumption.

intro InM.
apply SectionTheorem in InM.
destruct InM as [InL InR].
split.
apply Rel_LTtl.
assumption.
apply Rel_RUnq.
assumption.
Qed.


Definition Rel_MapCond {A B} (rel : #(Relation A B)) :=
forall (a : #A), Unique'(fun b : #B => (&&rel) a b).

Theorem Rel_Map : forall {A B} (rel : #(Relation A B)),
Rel_MapCond rel <-> In rel (Map A B).
Proof.
intros A B rel.
split.
intro cond.
apply SectionTheorem.
split.

 apply Rel_LTtl.
 intro a.
 destruct (cond a) as [Exs Unq].
 destruct Exs as [b Exs].
 exists b.
 assumption.

 apply Rel_RUnq.
 intros a b1 b2 H1 H2.
 destruct (cond a) as [Exs Unq].
 apply Unq.
 split; assumption.

intro InM.
intro a.
apply Rel_Map2 in InM.
destruct InM as [LCond RCond].
split.
destruct (LCond a) as [b LCond'].
exists b.
assumption.

intros b1 b2 HD.
destruct HD as [H1 H2].
apply (RCond a).
assumption.
assumption.
Qed.




Definition RUnq_MapCond {A B} (rel : #(RightUnique A B)) :=
Rel_LTtlCond (rel{<RUnq_Rel}).


Definition RUnq_Map : forall {A B} (rel : #(RightUnique A B)),
RUnq_MapCond rel <-> In rel (Map A B).
Proof.
intros A B rel.
split.

intro Cond.
apply SectionTheorem.
split.
apply SSet'Theorem.
split.
apply RUnq_Rel.
apply SetProp.
intros InrR.
apply Cond.
apply (SetProp).

intro InrM.
unfold RUnq_MapCond.
apply Rel_LTtl.
apply (Map_LTtl) in InrM.
assumption.
Qed.

Definition StrongMap {A1 A2 B1 B2} (f1 : #(Map A1 B1)) (f2 : #(Map A2 B2)) :=
StrongRel (f1{<Map_Rel}) (f2{<Map_Rel}).


Theorem MapHasSameDomain : forall {A1 B1 A2 B2}
(rel1 : #(Map A1 B1)) (rel2 : #(Map A2 B2)), rel1 == rel2 -> A1 == A2.
Proof.
intros A1 B1 A2 B2 rel1 rel2 Eqrel.
apply (LeftTotalHasSameDomain (rel1{<Map_LTtl}) (rel2{<Map_LTtl})).
apply Eqrel.
Qed.

Theorem AppUnique : forall D R (F : (#Map D R)) (d : #D),
Unique' (fun r => &&(F{<Map_Rel}) d r).
Proof.
intros D R F.
apply Rel_Map.
apply (SetProp F).
Qed.

Definition App {D R} (F : #(Map D R)) (d : #D) :=
Unique'Out (fun r => &&(F{<Map_Rel}) d r) (AppUnique D R F d).

Notation "% F" := (App F) (at level 10, x at next level).


Theorem AppTheorem : forall {D R} (F : #(Map D R)) (d : #D),
(&&F{<Map_Rel}) d (%F d).
Proof.
intros D R F d.
apply (HUnique'Out _ (AppUnique D R F d)).
intros x y Eqxy.
split; apply RelRewriteR.
assumption.
apply SymmetryEq.
assumption.
Qed.

Theorem AppMapRel : forall {D R} (F : #(Map D R)) (d : #D) (r : #R),
(%F d) == r -> (&&(F{<Map_Rel}) d r).
Proof.
intros D R F d r Eqr.
cut (&&(F{<Map_Rel}) d (%F d)).
 apply RelRewriteR.
 rewrite Eqr.
 apply ReflexivityEq.
apply AppTheorem.
Qed.




(* Map Charactor *)
Theorem MapEquality : forall {D1 R1 D2 R2} (f1 : #(Map D1 R1)) (f2 : #(Map D2 R2)), 
D1 == D2 -> 
(forall (d1 : #D1) (d2 : #D2), d1 == d2 -> ((% f1) d1) == ((% f2) d2)) ->
(f1) == (f2).
Proof.
intros D1 R1 D2 R2 f1 f2 EqE EqHH.
apply EA.
intro p.
split.
 intro Inpf.
 assert (IsPairp : IsPair p).
  apply (IsPairRelation (f1{<Map_Rel})).
  assumption.
 destruct IsPairp as [d IsPairp].
 destruct IsPairp as [r IsPairp].
 rewrite IsPairp.
 rewrite IsPairp in Inpf.
 assert(InD : In d D1 /\ In r R1).
  apply (PairInRelation (f1{<Map_Rel})).
  assumption.
 destruct InD as [IndD1 InrR1].
 assert(IndD2 : In d D2).
  rewrite <- EqE.
  assumption.
 assert(AppT : (&&f2{<Map_Rel}) {d ! IndD2} (%f2 {d ! IndD2})).
  apply AppTheorem.
 assert(Eqf : (%f1 {d ! IndD1}) == (%f2 {d ! IndD2})).
  apply EqHH.
  apply ReflexivityEq.
 assert (EqR : r == (%f2 {d ! IndD2})).
  apply (TransitivityEq {r ! InrR1}).
  apply ReflexivityEq.
  apply (TransitivityEq (%f1 {d ! IndD1})).
  assert(runq1 : Rel_RUnqCond (f1{<Map_Rel})).
   apply Rel_RUnq.
   apply Map_RUnq.
   apply (SetProp f1).
  apply (runq1 {d ! IndD1}).
  apply Inpf.
  assert(AppT1 : &&(f1{<Map_Rel}) {d ! IndD1} (%f1 {d ! IndD1})).
   apply AppTheorem.
  apply AppT1.
  apply Eqf.
 rewrite EqR.
 apply AppT.

 intros Inpf2.
 assert(IsP : IsPair p).
  apply (IsPairRelation (f2{<Map_Rel})).
  apply Inpf2.
 destruct IsP as [d IsP].
 destruct IsP as [r IsP].
 rewrite IsP in Inpf2.
 rewrite IsP.
 assert(InD : In d D2 /\ In r R2).
  apply (PairInRelation (f2{<Map_Rel})).
  apply Inpf2.
 destruct InD as [IndD2 InrR2].
 assert(IndD1 : In d D1).
  rewrite EqE.
  assumption.
 assert(AppT : (&&f1{<Map_Rel}) {d ! IndD1} (%f1 {d!IndD1})).
  apply AppTheorem.
 assert(EqR : r == (%f1 {d!IndD1})).
  apply (TransitivityEq {r ! InrR2}).
  apply ReflexivityEq.
  apply (TransitivityEq (%f2 {d!IndD2})).
  assert(runq : Rel_RUnqCond (f2{<Map_Rel})).
   apply Rel_RUnq.
   apply Map_RUnq.
   apply (SetProp f2).
  apply (runq {d ! IndD2}).
  apply Inpf2.
  assert(AppT2 : (&&f2{<Map_Rel}) {d!IndD2} (%f2 {d!IndD2})).
   apply AppTheorem.
  apply AppT2.
  symmetry.
  apply EqHH.
  apply (ReflexivityEq).
 rewrite EqR.
 apply AppT.
Qed.


Theorem AppTheoremReverse : forall {A B} (f : #(Map A B))
(a : #A) (b : #B),
(&&f{<Map_Rel}) a b -> ((%f) a) == b.
Proof.
intros A B f a b MapRel.
assert(fR : Rel_MapCond (f{<Map_Rel})).
 apply Rel_Map.
 apply (SetProp f).
unfold Rel_MapCond in fR.
apply (Unique'EqApply _ (fR a)).
split.
apply AppTheorem.
assumption.
Qed.

 


Theorem MapEqAll : forall {A1 B1 A2 B2}
{f1 : #(Map A1 B1)} {f2 : #(Map A2 B2)}
{x1 : #A1} {x2 : #A2},
x1 == x2 -> f1 == f2 ->
((% f1) x1) == ((% f2) x2).
Proof.
intros A1 B1 A2 B2 f1 f2 x1 x2 Eqx EqF.
assert (Inf2B1 : In ((% f2) x2) B1).
 assert(InP : In (Pair x2 ((% f2) x2)) f1).
  rewrite EqF.
  assert(AppT : (&&f2{<Map_Rel}) x2 ((%f2) x2)).
   apply AppTheorem.
  apply AppT.
 apply (PairInRelation (f1{<Map_Rel})) in InP.
 tauto.
apply (TransitivityEq {((% f2) x2) ! Inf2B1}).
apply AppTheoremReverse.
assert(InP : In (Pair x1 {((% f2) x2) ! Inf2B1}) f1).
 rewrite Eqx.
 rewrite EqF.
 assert(AppT : (&&f2{<Map_Rel}) x2 ((% f2) x2)).
  apply AppTheorem.
 apply AppT.
apply InP.
apply ReflexivityEq.
Qed.

Theorem MapEqAll' : forall {A1 B1 A2 B2}
{f1 : #(Map A1 B1)} {f2 : #(Map A2 B2)}
{x1 : #A1} {x2 : #A2},
x1 == x2 -> f1 == f2 ->
((% f2) x2) == ((% f1) x1).
Proof.
intros A1 B1 A2 B2 f1 f2 x1 x2 Eqx Eqf.
symmetry.
apply (MapEqAll Eqx Eqf).
Qed.

Theorem MapArgEq : forall {A B} {d1 : #A} {d2 : #A}
(f : #(Map A B)),
d1 == d2 -> ((% f) d1) == ((% f) d2).
Proof.
intros A B d1 d2 f EqH.
apply MapEqAll.
apply EqH.
apply ReflexivityEq.
Qed.

Theorem MapArgEq' : forall {A B} {d1 : #A} {d2 : #A}
(f : #(Map A B)),
d1 == d2 -> ((% f) d2) == ((% f) d1).
Proof.
intros A B d1 d2 f Eqd.
apply SymmetryEq.
apply (MapArgEq f Eqd).
Qed.

Theorem MapEq : forall {A B1 B2} {f1 : #(Map A B1)} {f2 : #(Map A B2)} {a : #A},
f1 == f2 -> (%f1 a) == (%f2 a).
Proof.
intros A B1 B2 f1 f2 a Eqf.
apply MapEqAll.
apply ReflexivityEq.
apply Eqf.
Qed.

Theorem MapEq' : forall {A B1 B2} {f1 : #(Map A B1)} {f2 : #(Map A B2)} {a : #A},
f2 == f1 -> (%f1 a) == (%f2 a).
Proof.
intros A B1 B2 f1 f2 a Eqf.
apply SymmetryEq.
apply MapEq.
apply Eqf.
Qed.


Theorem MapIn : forall {A B} (f : #(Map A B)),
forall a, In (%f a) B.
Proof.
intros A B f a.
assert(AppT : &&(f{<Map_Rel}) a (%f a)).
 apply AppTheorem.
 apply RelationIn in AppT.
 destruct AppT as [InaA InfaB].
 assumption.
Qed.

Theorem MapStrong : forall {A1 B1 A2 B2} {f : #(Map A1 B1)} {g : #(Map A2 B2)} {x : #A1} {y : #A2},
StrongMap f g ->
x == y -> (%f x) == (%g y).
Proof.
intros A1 B1 A2 B2 f g x y SRel Eqxy.
assert(AppT : &&(f{<Map_Rel}) x (%f x)).
 apply AppTheorem.
apply (StrongRelationRelExists _ _ _ _ SRel) in AppT.
destruct AppT as [InxA2 AppT].
destruct AppT as [IngxB2 AppT].
apply (TransitivityEq {(%f x) ! IngxB2}).
 apply ReflexivityEq.
apply SymmetryEq.
apply AppTheoremReverse.
generalize AppT.
apply RelRewriteL.
apply (TransitivityEq x).
apply ReflexivityEq.
assumption.
Qed.

Theorem MapStrongEq : forall {A1 B1 A2 B2} {f : #(Map A1 B1)} {g : #(Map A2 B2)} {x : #A1} (sub : Subset A1 A2),
StrongMap f g ->
(%f x) == (%g (x{<sub})).
Proof.
intros A1 B1 A2 B2 f g x sub SR.
apply (MapStrong SR).
apply ReflexivityEq.
Qed.

Theorem MapStrongEq' : forall {A1 B1 A2 B2} {f : #(Map A1 B1)} {g : #(Map A2 B2)} {x : #A1} (sub : Subset A1 A2),
StrongRel (f{<Map_Rel}) (g{<Map_Rel}) ->
(%g (x{<sub})) == (%f x).
Proof.
intros A1 B1 A2 B2 f g x sub SR.
apply SymmetryEq.
apply MapStrongEq.
apply SR.
Qed.



Theorem MapStrongSameDomain : forall {A B1 B2} (f : #(Map A B1)) (g : #(Map A B2)),
StrongRel (f{<Map_Rel}) (g{<Map_Rel}) -> f == g.
Proof.
intros A B1 B2 f g SR.
apply MapEquality.
apply ReflexivityEq.
intros a1 a2 Eqa.
apply (MapStrong SR Eqa).
Qed.

Theorem ToMapStrong : forall {A1 B1 A2 B2} {f : #(Map A1 B1)} {g : #(Map A2 B2)},
Subset A1 A2 ->
(forall (a1 : #A1) (a2 : #A2), a1 == a2 -> %f a1 == %g a2) ->
StrongMap f g.
Proof.
intros A1 B1 A2 B2 f g sub cond.
apply ToStrongRel.
intros a b relH.
exists (a{<sub}).
exists (%g (a{<sub})).
split.
apply ReflexivityEq.
split.
apply (TransitivityEq (%f a)).
 apply SymmetryEq.
 apply AppTheoremReverse.
 apply relH.
apply cond.
apply ReflexivityEq.
apply AppTheorem.
Qed.

Theorem MapStrongSubset : forall {A1 B1 A2 B2} (f : #(Map A1 B1)) (g : #(Map A2 B2)),
StrongRel (f{<Map_Rel}) (g{<Map_Rel}) -> Subset A1 A2.
Proof.
intros A1 B1 A2 B2 f g SH.
apply (StrongLeftTotalSubset (f{<Map_LTtl}) (g{<Map_LTtl})).
apply (TransitivityStrongRel (f{<Map_Rel})).
 apply ReflexivityStrongRel2.
 apply ReflexivityEq.
apply (TransitivityStrongRel _ SH).
apply ReflexivityStrongRel2.
apply ReflexivityEq.
Qed.


(** Bijection **)
Definition Injection A B := Section (Map A B) (LeftUnique A B).
Definition Surjection A B := Section (Map A B) (RightTotal A B).
Definition Bijection A B := Section (Injection A B) (Surjection A B).

Theorem Inj_Map : forall {A B}, Subset (Injection A B) (Map A B).
Proof.
intros A B.
apply SectionSubsetL.
Qed.

Theorem Inj_LUnq : forall {A B}, Subset (Injection A B) (LeftUnique A B).
Proof.
intros A B.
apply SectionSubsetR.
Qed.

Theorem Sur_Map : forall {A B}, Subset (Surjection A B) (Map A B).
Proof.
intros A B.
apply SectionSubsetL.
Qed.

Theorem Sur_RTtl : forall {A B}, Subset (Surjection A B) (RightTotal A B).
Proof.
intros A B.
apply SectionSubsetR.
Qed.

Theorem Bij_Inj : forall {A B}, Subset (Bijection A B) (Injection A B).
Proof.
intros A B.
apply SectionSubsetL.
Qed.

Theorem Bij_Sur : forall {A B}, Subset (Bijection A B) (Surjection A B).
Proof.
intros A B.
apply SectionSubsetR.
Qed.

Theorem Bij_Map : forall {A B}, Subset (Bijection A B) (Map A B).
Proof.
intros A B.
apply (TransitivitySubset (Injection A B)).
apply Bij_Inj.
apply Inj_Map.
Qed.




Definition Map_InjCond {A B} (f : #(Map A B)) :=
forall a1 a2, (%f a1) == (%f a2) -> a1 == a2.

Theorem Map_Inj : forall {A B} (f : #(Map A B)),
Map_InjCond f <-> In f (Injection A B).
Proof.
intros A B f.
split.

intro Cond.
apply SectionTheorem.
split.
apply SetProp.
assert(InfR : In f (Relation A B)).
 apply Map_Rel.
 apply SetProp.
rewrite <- (DSETEq _ InfR).
apply Rel_LUnq.
intros b.
intros a1 a2 relH1 relH2.
put (Cond a1 a2) Cond'.
apply Cond'.
apply (TransitivityEq b).
 apply AppTheoremReverse.
 apply relH1.
apply SymmetryEq.
apply AppTheoremReverse.
apply relH2.

intro InfInj.
intros a1 a2 Eqfa.
apply SectionTheorem in InfInj.
destruct InfInj as [InfM InfL].
assert(InfR : In f (Relation A B)).
 apply LUnq_Rel.
 assumption.
rewrite <- (DSETEq _ InfR) in InfL.
apply Rel_LUnq in InfL.
apply (Atmost'EqApply _ (InfL (%f a1))).
split.
cut (&&(f{<Map_Rel}) a1 (%f a1)).
 apply RelRewrite.
 apply ReflexivityEq.
apply AppTheorem.

cut (&&(f{<Map_Rel}) a2 (%f a2)).
 apply RelRewriteAll.
 apply ReflexivityEq.
 apply SymmetryEq.
 apply Eqfa.
 apply ReflexivityEq.
apply AppTheorem.
Qed.

Definition Map_SurCond {A B} (f : #(Map A B)) :=
forall b : #B, exists a: #A, %f a == b.

Theorem Map_Sur : forall {A B} (f : #(Map A B)),
Map_SurCond f <-> In f (Surjection A B).
Proof.
intros A B f.
assert(InfR : In f (Relation A B)).
 apply Map_Rel.
 apply (SetProp).
split.

intro Cond.
apply SectionTheorem.
split.
apply (SetProp).
rewrite <- (DSETEq _ InfR).
apply Rel_RTtl.
intro b.
destruct (Cond b) as [a Cond'].
exists a.
cut (&&(f{<Map_Rel}) a (%f a)).
 apply RelRewriteAll.
 apply ReflexivityEq.
 apply Cond'.
 apply ReflexivityEq.
apply AppTheorem.

intro InfS.
intro b.
apply SectionTheorem in InfS.
destruct InfS as [InfM InfRU].
rewrite <- (DSETEq _ InfR) in InfRU.
apply Rel_RTtl in InfRU.
unfold Rel_RTtlCond in InfRU.
destruct (InfRU b) as [a InfRU'].
exists a.
apply AppTheoremReverse.
apply InfRU'.
Qed.


Definition Map_BijCond {A B} (f : #(Map A B)) :=
Map_InjCond f /\ Map_SurCond f.

Theorem Map_Bij : forall {A B} (f : #(Map A B)),
Map_BijCond f <-> In f (Bijection A B).
Proof.
intros A B f.
split.

intro Cond.
destruct Cond as [CondI CondS].
apply SectionTheorem.
split.
 apply Map_Inj.
 apply CondI.

 apply Map_Sur.
 apply CondS.

intro InfB.
apply SectionTheorem in InfB.
destruct InfB as [InfI InfS].
apply Map_Inj in InfI.
apply Map_Sur in InfS.
split.
apply InfI.
apply InfS.
Qed.

Definition Map_BijCond2 {A B} (f : #(Map A B)) :=
forall (b : #B), Unique' (fun a : #A => (%f a) == b).

Theorem Map_Bij2 : forall  {A B} (f : #(Map A B)),
Map_BijCond2 f <-> In f (Bijection A B).
Proof.
intros A B f.
split.

intro Cond.
apply Map_Bij.
split.
 intros a1 a2 Eqfa.
 destruct (Cond (%f a2)) as [Exs Unq].
 destruct Exs as [a Exs].
 apply Unq.
 split.
 apply Eqfa.
 apply ReflexivityEq.

 intros b.
 destruct (Cond b) as [Exs Unq].
 apply Exs.

intro InfB.
intro b.
apply Map_Bij in InfB.
destruct InfB as [InjC SurC].
split.
 destruct (SurC b) as [a SurC'].
 exists a.
 apply SurC'.

 intros a1 a2 EqfD.
 destruct EqfD as [Eqf1 Eqf2].
 apply InjC.
 apply (TransitivityEq b).
 rewrite Eqf1.
 apply ReflexivityEq.
 rewrite Eqf2.
 apply ReflexivityEq.
Qed.

Definition Rel_InjCond {A B} (rel : #(Relation A B)) :=
Rel_MapCond rel /\ Rel_LUnqCond rel.

Theorem Rel_Inj : forall {A B} (rel : #(Relation A B)),
Rel_InjCond rel <-> In rel (Injection A B).
Proof.
intros A B rel.
split.

intro Cond.
destruct Cond as [CondM CondL].
apply SectionTheorem.
split.
apply Rel_Map.
apply CondM.
apply Rel_LUnq.
apply CondL.

intro InrelI.
apply SectionTheorem in InrelI.
destruct InrelI as [InrM InrL].
apply Rel_Map in InrM.
apply Rel_LUnq in InrL.
split; assumption.
Qed.

Definition Rel_SurCond {A B} (rel : #(Relation A B)) :=
Rel_MapCond rel /\ Rel_RTtlCond rel.

Theorem Rel_Sur : forall {A B} (rel : #(Relation A B)),
Rel_SurCond rel <-> In rel (Surjection A B).
Proof.
intros A B rel.
split.

intro Cond.
destruct Cond as [CondM CondS].
apply SectionTheorem.
split.
apply Rel_Map.
assumption.
apply Rel_RTtl.
assumption.

intro InrS.
apply SectionTheorem in InrS.
destruct InrS as [InrM InrR].
apply Rel_Map in InrM.
apply Rel_RTtl in InrR.
split; assumption.
Qed.

Definition Rel_BijCond {A B} (rel : #(Relation A B)) :=
Rel_MapCond rel /\ Rel_LUnqCond rel /\ Rel_RTtlCond rel.

Theorem Rel_Bij : forall {A B} (rel : #(Relation A B)),
Rel_BijCond rel <-> In rel (Bijection A B).
Proof.
intros A B rel.
split.

intro Cond.
destruct Cond as [ComdM Cond].
destruct Cond as [CondL CondR].
apply SectionTheorem.
split.
 apply Rel_Inj.
 split; assumption.

 apply Rel_Sur.
 split; assumption.

intro InrelB.
apply SectionTheorem in InrelB.
destruct InrelB as [InrelI InrelS].
split.
 apply Rel_Map.
 apply Inj_Map.
 assumption.
split.
 apply Rel_LUnq.
 apply Inj_LUnq.
 assumption.
apply Rel_RTtl.
apply Sur_RTtl.
assumption.
Qed.

(** Reflexive **)
Definition Reflexive A := SSet'
(BRelation A)
(fun r => forall x : #A, &&r x x).

Theorem Ref_Rel : forall {A} , Subset (Reflexive A) (BRelation A).
Proof.
intro A.
apply SSetSubset.
Qed.
Hint Immediate @Ref_Rel.

Definition Rel_RefCond {A} (rel : #(BRelation A)) :=
forall (a : #A), &&rel a a.

Theorem Rel_Ref : forall {A} (rel : #(BRelation A)),
Rel_RefCond rel <-> In rel (Reflexive A).
Proof.
intros A rel.
split.
 intro Cond.
 apply SSet'Theorem.
 split.
 apply (SetProp).
 intros rel' a.
 apply Cond.
intro InR.
intro a.
apply SSet'Theorem in InR.
destruct InR as [InrB InR].
cut ((&&{rel ! InrB}) a a).
apply RelRewrite.
apply ReflexivityEq.
apply InR.
Qed.

Definition Rel_RefCond2 {A} (rel : #(BRelation A)) :=
forall (a b : #A), a == b -> &&rel a b.

Theorem Rel_Ref2 : forall {A} (rel : #(BRelation A)),
Rel_RefCond2 rel <-> In rel (Reflexive A).
Proof.
intros A rel.
split.
 intro Cond.
 apply SSet'Theorem.
 split.
 apply (SetProp).
 intros rel' a.
 apply Cond.
 apply ReflexivityEq.
intro InR.
intros a b Eqab.
apply SSet'Theorem in InR.
destruct InR as [InrB InR].
cut ((&&{rel ! InrB}) a a).
apply RelRewriteAll.
apply ReflexivityEq.
apply Eqab.
apply ReflexivityEq.
apply InR.
Qed.





(** Irreflexive **)
Definition Irreflexive A := SSet'
(BRelation A)
(fun r => forall (x : #A), ~(&&r) x x).

Theorem Irref_Rel : forall {A} , Subset (Irreflexive A) (BRelation A).
Proof.
intro A.
apply SSetSubset.
Qed.
Hint Immediate @Irref_Rel.



Definition Rel_IrrefCond {A} (rel : #(BRelation A)) := 
forall (a : #A), ~(&&rel) a a.

Definition Rel_Irref : forall {A} (rel : #(BRelation A)),
Rel_IrrefCond rel <-> In rel (Irreflexive A).
Proof.
intros A rel.
split.
 intro Cond.
 apply SSet'Theorem.
 split.
 apply SetProp.
 intros InrB x relHxx.
 apply (Cond x).
 apply relHxx.

 intro InrI.
 intros x relHxx.
 apply SSet'Theorem in InrI.
 destruct InrI as [InrB InrI].
 apply (InrI InrB x).
 apply relHxx.
Qed.



(** Symmetric **)
 
Definition Symmetric A := SSet'
(BRelation A)
(fun r => forall (x : #A) (y : #A), &&r x y -> &&r y x).

Theorem Sym_Rel : forall {A}, Subset (Symmetric A) (BRelation A).
Proof.
intro A.
apply SSet'Subset.
Qed.

Definition Rel_SymCond {A} (rel : #(BRelation A)) :=
forall x y, &&rel x y -> &&rel y x.

Theorem Rel_Sym : forall {A} (rel : #(BRelation A)),
Rel_SymCond rel <-> In rel (Symmetric A).
Proof.
intros A rel.
split.
 intro Cond.
 apply SSet'Theorem.
 split.
 apply SetProp.
 intros InrB x y relH.
 apply (Cond x y).
 generalize (relH).
 apply RelRewrite.
 apply ReflexivityEq.

 intro InrS.
 intros x y relH.
 apply SSet'Theorem in InrS.
 destruct InrS as [InrB InrS].
 cut (&&{rel!InrB} y x).
  apply RelRewrite.
  apply ReflexivityEq.
 apply InrS.
 generalize (relH).
 apply RelRewrite.
 apply ReflexivityEq.
Qed.




(** Antisymmetric **)
Definition Antisymmetric A := SSet'
(BRelation A)
(fun r => forall (x : #A) (y : #A), &&r x y -> &&r y x -> x == y).

Theorem ASym_Rel : forall {A} , Subset (Antisymmetric A) (BRelation A).
Proof.
intro A.
apply SSetSubset.
Qed.
Hint Immediate @ASym_Rel.


Theorem AntisymmetricR : forall {A}
(rel : #(Antisymmetric A)) (x : #A) (y : #A),
(&&rel{<ASym_Rel}) x y -> (&&rel{<ASym_Rel}) y x -> x==y.
Proof.
intros A rel x y H1 H2.
generalize (SetProp rel); intro rel'.
apply SSet'Theorem in rel'.
destruct rel' as [InB rel'].
apply (rel' InB).
apply H1.
apply H2.
Qed.

Definition Rel_ASymCond {A} (rel : #(BRelation A)) :=
forall x y, &&rel x y -> &&rel y x -> x == y.

Theorem Rel_ASym : forall {A} (rel : #(BRelation A)),
Rel_ASymCond rel <-> In rel (Antisymmetric A).
Proof.
  intros A rel.
  split.
  {
    intro cond.
    apply SSet'Theorem.
    split.
    apply SetProp.
    intros prf x y Relxy Relyx.
    apply cond.
    {
      generalize Relxy.
      apply RelRewrite.
      reflexivity.
    } {
      generalize Relyx.
      apply RelRewrite.
      reflexivity.
    }
  } {
    intro relA.
    intros x y relHxy relHyx.
    apply SSet'Theorem in relA.
    destruct relA as [prf HH].
    apply (HH prf).
    {
      generalize relHxy.
      apply RelRewrite.
      reflexivity.
    } {
      generalize relHyx.
      apply RelRewrite.
      reflexivity.
    }
  }
Qed.


(** Irsymmetric **)

Definition Irsymmetric A := SSet'
(BRelation A)
(fun r => forall (x : #A) (y : #A), &&r x y -> ~(&&r) y x).
Theorem Irsym_Rel : forall {A} , Subset (Irsymmetric A) (BRelation A).
Proof.
intro A.
apply SSetSubset.
Qed.
Hint Immediate @Irsym_Rel.

Theorem IrsymmetricR : forall {A}
(rel : #(Irsymmetric A)) (x : #A) (y : #A),
(&&rel{<Irsym_Rel}) x y -> ~(&&rel{<Irsym_Rel}) y x.
Proof.
intros A rel x y H1 H2.
generalize (SetProp rel); intro rel'.
apply SSet'Theorem in rel'.
destruct rel' as [InrB rel'].
apply (rel' InrB x y).
apply H1.
apply H2.
Qed.

Definition Rel_IrsymCond {A} (rel : #(BRelation A)) := 
forall (a : #A) (b : #A), (&&rel) a b -> ~(&&rel) b a.

Definition Rel_Irsym : forall {A} (rel : #(BRelation A)),
Rel_IrsymCond rel -> In rel (Irsymmetric A).
Proof.
intros A rel HH.
apply SSet'Theorem.
split; auto.
Qed.








(** Transitive **)
Definition Transitive A := SSet'
(BRelation A)
(fun r => forall (x : #A) (y : #A) (z : #A), 
&&r x y -> &&r y z -> &&r x z).

Theorem Trans_Rel : forall {A} , Subset (Transitive A) (BRelation A).
Proof.
intros A c IncT.
apply SSet'Theorem in IncT.
tauto.
Qed.
(*Hint Immediate @Trans_Rel.*)

Definition Rel_TransCond {A} (rel : #(BRelation A)) :=
forall a b c,
&&rel a b -> &&rel b c -> &&rel a c.

Theorem Rel_Trans : forall {A} (rel : #(BRelation A)),
Rel_TransCond rel <-> In rel (Transitive A).
Proof.
intros A rel.
split.
 intro Cond.
 apply SSet'Theorem.
 split.
 apply SetProp.
 intros InrB x y z H1 H2.
 apply (Cond x y z).
 apply H1.
 apply H2.

 intro InrT.
 intros x y z H1 H2.
 apply SSet'Theorem in InrT.
 destruct InrT as [InrB InrT].
 cut (&&{rel!InrB} x z).
  intro AA; apply AA.
 apply (InrT _ _ y).
 apply H1.
 apply H2.
Qed.
 

(*
Theorem TransitiveR : forall {A}
(rel : #(Transitive A)) (x : #A) (y : #A) (z : #A),
(&&rel{<Trans_Rel}) x y -> (&&rel{<Trans_Rel}) y z -> (&&rel{<Trans_Rel}) x z.
Proof.
intros A rel x y z H1 H2.
generalize (SetProp rel); intro rel'.
apply SSet'Theorem in rel'.
destruct rel' as [InrelB rel'].
apply (rel' InrelB _ y _).
apply H1.
apply H2.
Qed.
*)








(** Complement **)
Definition Complement A := SSet'
(BRelation A)
(fun r => forall (x : #A) (y : #A), 
~&&r x y -> &&r y x).



(** EquivalentRelation **)
Definition ERelation A :=
Section (Section (Reflexive A) (Symmetric A)) (Transitive A).

Theorem ERel_Ref : forall {A}, Subset (ERelation A) (Reflexive A).
Proof.
intro A.
apply (TransitivitySubset (Section (Reflexive A) (Symmetric A))).
apply SectionSubsetL.
apply SectionSubsetL.
Qed.

Theorem ERel_Sym : forall {A}, Subset (ERelation A) (Symmetric A).
Proof.
intro A.
apply (TransitivitySubset (Section (Reflexive A) (Symmetric A))).
apply SectionSubsetL.
apply SectionSubsetR.
Qed.

Theorem ERel_Trans : forall {A}, Subset (ERelation A) (Transitive A).
Proof.
intros A.
apply SectionSubsetR.
Qed.

Theorem ERel_Rel : forall {A}, Subset (ERelation A) (BRelation A).
Proof.
intros A.
apply (TransitivitySubset (Reflexive A)).
apply ERel_Ref.
apply Ref_Rel.
Qed.

Definition Rel_ERelCond {A} (rel : #(BRelation A)) :=
Rel_RefCond rel /\ Rel_SymCond rel /\ Rel_TransCond rel.

Theorem Rel_ERel : forall {A} (rel : #(BRelation A)),
Rel_ERelCond rel <-> In rel (ERelation A).
Proof.
intros A rel.
split.
 intro Cond.
 destruct Cond as [Ref Cond].
 destruct Cond as [Sym Trans].
 apply SectionTheorem.
 split.
 apply SectionTheorem.
 split.
 apply Rel_Ref.
 apply Ref.
 apply Rel_Sym.
 apply Sym.
 apply Rel_Trans.
 apply Trans.

 intro InrE.
 apply SectionTheorem in InrE.
 destruct InrE as [Cond InrT].
 apply SectionTheorem in Cond.
 destruct Cond as [InrR InrS].
 split.
 apply Rel_Ref.
 apply InrR.
 split.
 apply Rel_Sym.
 apply InrS.
 apply Rel_Trans.
 apply InrT.
Qed.



(** PreOrderRelation **)
Definition Poset A := Section (Reflexive A) (Transitive A).

Theorem Poset_Ref : forall {A}, Subset (Poset A) (Reflexive A).
Proof.
  intro A.
  apply SectionSubsetL.
Qed.

Theorem Poset_Trans : forall {A}, Subset (Poset A) (Transitive A).
Proof.
  intro A.
  apply SectionSubsetR.
Qed.  
  
Theorem Poset_Rel : forall {A}, Subset (Poset A) (BRelation A).
Proof.
  intro A.
  generalize (@Ref_Rel A).
  apply TransitivitySubset.
  apply Poset_Ref.
Qed.

Definition Rel_PosetCond {A} (rel : #(BRelation A)) := Rel_RefCond rel /\ Rel_TransCond rel.

Theorem Rel_Poset : forall {A} (rel : #(BRelation A)),
Rel_PosetCond rel <-> In rel (Poset A).
Proof.
  intros A rel.
  split.
  {
    intro relH.
    destruct relH as [refH tranH].
    apply SectionTheorem.
    split.
    {
      apply Rel_Ref.
      apply refH.
    } {
      apply Rel_Trans.
      apply tranH.
    }
  } {
    intro InreP.
    apply SectionTheorem in InreP.
    destruct InreP as [InreR InreT].
    split.
    {
      apply Rel_Ref.
      apply InreR.
    } {
      apply Rel_Trans.
      apply InreT.
    }
  }
Qed.
  
(** PartialOrderRelation **)
Definition ORelation A :=
  Section (Poset A) (Antisymmetric A).

Theorem ORel_Poset : forall {A}, Subset (ORelation A) (Poset A).
Proof.
  intro A.
  apply SectionSubsetL.
Qed.

Theorem ORel_Ref : forall {A} , Subset (ORelation A) (Reflexive A).
Proof.
  intros A.
  generalize (@Poset_Ref A).
  apply TransitivitySubset.
  apply ORel_Poset.
Qed.

Theorem ORel_ASym : forall {A} , Subset (ORelation A) (Antisymmetric A).
Proof.
intros A.
apply SectionSubsetR.
Qed.

Theorem ORel_Rel : forall {A} , Subset (ORelation A) (BRelation A).
Proof.
  intro A.
  generalize (@ASym_Rel A).
  apply TransitivitySubset.
  apply ORel_ASym.
Qed.  

Definition Rel_ORelCond {A} (rel : #(BRelation A)) :=
  Rel_PosetCond rel /\ Rel_ASymCond rel.


Theorem Rel_ORel : forall {A} (rel : #(BRelation A)),
Rel_ORelCond rel <-> In rel (ORelation A).
Proof.
  intros A rel.
  split.
  {
    intro relH.
    destruct relH as [poH asymH].
    apply SectionTheorem.
    split.
    {
      apply Rel_Poset.
      apply poH.
    } {
      apply Rel_ASym.
      apply asymH.
    }
  } {
    intro InreP.
    apply SectionTheorem in InreP.
    destruct InreP as [InreR InreA].
    split.
    {
      apply Rel_Poset.
      apply InreR.
    } {
      apply Rel_ASym.
      apply InreA.
    }
  }
Qed.





(** StrictOrderRelation **)
Definition SORelation A :=
Section (Irreflexive A) (Transitive A).

Theorem SORel_Irref : forall {A} , Subset (SORelation A) (Irreflexive A).
Proof.
intros A.
apply SectionSubsetL.
Qed.
Hint Immediate @SORel_Irref.


Theorem SORel_Rel : forall {A} , Subset (SORelation A) (BRelation A).
Proof.
intro A.
apply (TransitivitySubset (Irreflexive A)); auto.
Qed.
Hint Immediate @SORel_Rel.

Theorem SORel_Irsym : forall {A} , Subset (SORelation A) (Irsymmetric A).
Proof.
intros A.
intros c IncSP.
apply SectionTheorem in IncSP.
destruct IncSP as [IncIr IncTr].
apply SSet'Theorem.
split.
apply SORel_Rel.
apply SectionTheorem.
split; auto.
intros IncB x y Rxy Ryx.
assert(R1 : Rel_IrrefCond {c!IncB}).
 apply Rel_Irref.
 apply IncIr.
assert(R2 : Rel_TransCond {c!IncB}).
 apply Rel_Trans.
 apply IncTr.
apply (R1 x).
apply (R2 x y x).
apply Rxy.
apply Ryx.
Qed.


Definition Rel_SORelCond {A} (rel : #(BRelation A)) := 
Rel_IrrefCond rel /\ Rel_TransCond rel.


Definition Rel_SORel : forall {A} (rel : #(BRelation A)),
Rel_SORelCond rel -> In rel (SORelation A).
Proof.
intros A rel HH.
apply SectionTheorem.
destruct HH as [HH1 HH2].
split.
 apply SSet'Theorem.
 split.
 apply (SetProp rel).
 intros rel2 x Rxx.
 apply (HH1 x).
 apply Rxx.

 apply SSet'Theorem.
 split.
 apply (SetProp rel).
 intros rel2 x y z Rxy Ryz.
 assert(Eqr : rel == {rel ! rel2}).
  auto.
 apply (RelRewrite Eqr).
 apply (HH2 x y z).
 apply Rxy.
 apply Ryz.
Qed.



(** Well Founded **)

Definition WRelation A :=
SSet' (BRelation A) (fun rel => forall X , Subset X A -> 
  (forall (u : (#A)), (forall (v : (#A)), &&rel v u -> In v X) -> In u X) -> X = A
).

Theorem WRel_Rel : forall {A} , Subset (WRelation A) (BRelation A).
Proof.
intro A.
apply SSetSubset.
Qed.
Hint Immediate @WRel_Rel.

Definition Rel_WRelCond {A} (rel : #(BRelation A)) := forall X, Subset X A ->
 (forall (u : (#A)), (forall (v : (#A)), &&rel v u -> In v X) -> In u X) -> X = A.

Theorem Rel_WRel {A} (rel : #(BRelation A)) :
Rel_WRelCond rel <-> In rel (WRelation A).
Proof.
split.
 intro cond.
 apply SSet'Theorem.
 split.
 apply SetProp.
 intros relB.
 apply cond.

 intro InrW.
 apply SSet'Theorem in InrW.
 destruct InrW as [InrB Cond].
 intros X sub HH.
 apply (Cond InrB _ sub).
 apply HH.
Qed.



Theorem WRInduction : forall {A} (rel : #(WRelation A)) (P : (#A) -> Prop),
RPred P ->
(forall (u : #A), (forall (v : #A), (&&rel{<WRel_Rel}) v u -> P v) -> P u) -> 
forall (u : #A), P u.
Proof.
intros A rel P RP IndH u.
generalize (SetProp rel); intro rel'.
apply SSet'Theorem in rel'.
destruct rel' as [InrB RelR].
assert(EqSA : (SSet' A (fun a => P a)) == A).
 apply (RelR InrB).
 apply SSetSubset.
 intros a HH.
 apply SSet'Theorem.
 split.
 apply SetProp.
 intros InaA.
 apply IndH.
 intros v relH.
 assert(relva : (&&{rel ! InrB}) v {a ! InaA}).
  assert(Eqrel : {rel ! InrB} == (rel{<WRel_Rel})).
   apply ReflexivityEq.
  apply (RelRewrite Eqrel).
  assumption.
 apply HH in relva.
 apply SSet'Theorem in relva.
 destruct relva as [InvA Pv].
 assert(Eqv : v == {v ! InvA}).
  apply ReflexivityEq.
 apply (RP _ _ Eqv).
 apply Pv.
assert(InuS : In u A).
 apply SetProp.
rewrite <- EqSA in InuS.
apply SSet'Theorem in InuS.
destruct InuS as [InuA Pu].
assert(Equ : u == {u ! InuA}).
 apply ReflexivityEq.
apply (RP _ _ Equ).
apply Pu.
Qed.



Theorem WRel_Irref : forall {A}, Subset (WRelation A) (Irreflexive A).
Proof.
intros A rel relP.
apply SSet'Theorem.
split.
apply WRel_Rel.
assumption.
intros relP'.
apply (WRInduction {rel ! relP}).
 apply RPredSimplify.
 intros x y Eqxy Px Py.
 apply (RelRewriteL' Eqxy) in Py.
 apply (RelRewriteR' Eqxy) in Py.
 contradiction.
intros u IndH reluu.
apply (IndH _ reluu).
assumption.
Qed.


Theorem WRel_Irsym : forall {A}, Subset (WRelation A) (Irsymmetric A).
intros A rel relW.
apply SSet'Theorem.
split.
apply WRel_Rel.
assumption.
intros relB.
apply (WRInduction {rel ! relW} (fun x : #A => forall (y : #A), (&&{rel ! relB}) x y -> ~(&&{rel ! relB}) y x)).
apply RPredSimplify.
intros x1 x2 Eq RH y Rxy Ryx.
apply (RelRewriteL (SymmetryEq _ _ Eq)) in Rxy.
apply (RH _ Rxy).
apply (RelRewriteR' Eq).
assumption.
intros u IndH v Rxu Rux.
assert(NRuv : ~(&&{rel ! relB}) u v).
 apply (IndH).
 apply Rux.
 apply Rux.
contradiction.
Qed.



(** WORelation *)
Definition WSORelation A := 
Section (WRelation A) (Transitive A).

Theorem WSORel_WRel : forall {A} , Subset (WSORelation A) (WRelation A).
Proof.
intro A.
apply SectionSubsetL.
Qed.
Hint Immediate @WSORel_WRel.

Theorem WSORel_Tran : forall {A} , Subset (WSORelation A) (Transitive A).
Proof.
intro A.
apply SectionSubsetR.
Qed.
Hint Immediate @WSORel_Tran.


Theorem WSORel_SORel : forall {A} , Subset (WSORelation A) (SORelation A).
Proof.
intros A rel relWSO.
apply SectionTheorem.
split.
apply WRel_Irref.
apply WSORel_WRel.
assumption.
apply WSORel_Tran.
assumption.
Qed.
Hint Immediate @WSORel_SORel.


Definition WRel_WSORelCond {A} (rel : #(WRelation A)) := 
Rel_TransCond rel{<WRel_Rel}.


Definition WRel_WSORel : forall {A} (rel : #(WRelation A)),
WRel_WSORelCond rel -> In rel (WSORelation A).
Proof.
intros A rel Cond.
apply SectionTheorem.
split.
apply SetProp.
apply SSet'Theorem.
split.
apply WRel_Rel.
apply SetProp.
unfold WRel_WSORelCond in Cond.
unfold Rel_TransCond in Cond.
intros relB x y z Rxy Ryz.
assert(Relxz : (&&rel{<WRel_Rel}) x z).
 apply (Cond x y z).
 apply Rxy.
 apply Ryz.
apply Relxz.
Qed.


(* Dividable *)
(*
Definition LeftDividable A B (erel : #(ERelation A)) :=
SSet' (Relation A B) (fun rel =>
  forall (a1 a2 : #A), &&(erel{<ERel_Rel}) a1 a2 -> (forall b, &&rel a1 b <-> &&rel a2 b)
).

Definition RightDividable A B (erel : #(ERelation B)) :=
SSet' (Relation A B) (fun rel =>
  forall (b1 b2 : #B), &&(erel{<ERel_Rel}) b1 b2 -> (forall a, &&rel a b1 <-> &&rel a b2)
).

Theorem LDvb_Rel : forall {A B erel}, Subset (LeftDividable A B erel) (Relation A B).
Proof.
intros A B erel.
apply SSet'Subset.
Qed.

Theorem RDvb_Rel : forall {A B erel}, Subset (RightDividable A B erel) (Relation A B).
Proof.
intros A B erel.
apply SSet'Subset.
Qed.

Definition Rel_LDvbCond {A B} (erel : #(ERelation A)) (rel : #(Relation A B)) := 
forall (a1 a2 : #A), &&(erel{<ERel_Rel}) a1 a2 -> (forall b, &&rel a1 b <-> &&rel a2 b).

Definition Rel_RDvbCond {A B} (erel : #(ERelation B)) (rel : #(Relation A B)) := 
forall (b1 b2 : #B), &&(erel{<ERel_Rel}) b1 b2 -> (forall a, &&rel a b1 <-> &&rel a b2).

Theorem Rel_LDvb {A B erel} : forall (rel : #(Relation A B)),
(Rel_LDvbCond erel rel) <-> In rel (LeftDividable A B erel).
Proof.
intros rel.
split.
 intro Cond.
 apply SSet'Theorem.
 split.
 apply SetProp.
 intros InrR a1 a2 relH b.
 put (Cond a1 a2 relH b) Cond'.
 apply Cond'.

 intro InrL.
 intros a1 a2 relH b.
 apply SSet'Theorem in InrL.
 destruct InrL as [InrR HH].
 apply (HH InrR _ _ relH).
Qed.

Theorem Rel_RDvb {A B erel} : forall (rel : #(Relation A B)),
(Rel_RDvbCond erel rel) <-> In rel (RightDividable A B erel).
Proof.
intros rel.
split.
 intro Cond.
 apply SSet'Theorem.
 split.
 apply SetProp.
 intros InrR b1 b2 relH a.
 put (Cond b1 b2 relH a) Cond'.
 apply Cond'.

 intro InrL.
 intros b1 b2 relH a.
 apply SSet'Theorem in InrL.
 destruct InrL as [InrR HH].
 apply (HH InrR _ _ relH).
Qed.
 

Theorem Map_RDvb : forall {A B erel}, Subset (Map A B) (RightDividable A B erel).
Proof.
intros A B erel.
intros p InpM.
assert(InpR : In p (Relation A B)).
 apply (Map_Rel).
 apply InpM.
rewrite <- (DSETEq _ InpR).
apply Rel_RDvb.
intros b1 b2 relH a.
rewrite <- (DSETEq _ InpR) in InpM.
apply Rel_Map in InpM.
destruct (InpM a) as [Exs Unq].
destruct Exs as [b Exs].
split.
 intro relH1.
 
 apply (@RDvb_Rel _ _ erel).
 apply InpRD.
rewrite <- (DSETEq _ InpR).
apply Rel_LTtl.
intro a.
*)
