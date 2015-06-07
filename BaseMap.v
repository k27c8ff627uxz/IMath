Require Import logic.
Require Import IZF.
Require Import Relation.


(* Make Relation *)
Definition MakeRelationSet {A B} (P : (#A) -> (#B) -> Prop) :=
SSet (Cartesian A B) (fun r => forall (a : (#A)) (b : (#B)), r == (Pair a b) -> P a b).

Theorem MakeRelationIn : forall A B (P : (#A) -> (#B) -> Prop),
In (MakeRelationSet P) (Relation A B).
Proof.
intros A B P.
apply PowersetTheorem.
apply SSetSubset.
Qed.

Definition MakeRelation {A B} (P : (#A) -> (#B) -> Prop) := 
{MakeRelationSet P ! MakeRelationIn A B P}.
 
Theorem MakeRelationTheorem : forall A B (P : (#A) -> (#B) -> Prop),
forall (a : (#A)) (b : (#B)),
  (&&(MakeRelation P) a b) <-> (forall (a' : (#A)) (b' : (#B)), a == a' -> b == b' -> P a' b').
Proof.
intros A B P a b.
split.
 intros MPH a' b' Eqa Eqb.
 unfold If in MPH.
 rewrite Eqa in MPH.
 rewrite Eqb in MPH.
 unfold MakeRelation in MPH.
 rewrite DSETEq in MPH.
 apply SSetTheorem in MPH.
 destruct MPH as [InPC HP].
 apply HP.
 apply ReflexivityEq.

 intros HH.
 unfold MakeRelation.
 unfold If.
 rewrite (DSETEq).
 apply SSetTheorem.
 split.
  apply CartesianTheorem.
  split; apply SetProp.

  intros a' b' EqP.
  apply EqualInPair in EqP.
  destruct EqP as [Eqa Eqb].
  apply HH.
  assumption.
  assumption.
Qed.




Theorem MakeMapCond : forall A B (F : (#A) -> (#B)),
RFun F ->
Rel_MapCond (MakeRelation (fun (a : #A) (b : #B) => (F a) == b)).
Proof.
intros A B F RF.
intro a.
split.
 exists (F a).
 apply MakeRelationTheorem.
 intros a' fb' Eqa Eqfb.
 apply (TransitivityEq (F a)).
 rewrite (RF _ _ Eqa).
 apply ReflexivityEq.
 assumption.

 intros b1 b2 MD.
 destruct MD as [MR1 MR2].
 put ((proj1 (MakeRelationTheorem _ _ _ _ _)) MR1) MR1'.
 put ((proj1 (MakeRelationTheorem _ _ _ _ _)) MR2) MR2'.
 apply (TransitivityEq (F a)).
  apply SymmetryEq.
  apply MR1'.
  apply ReflexivityEq.
  apply ReflexivityEq.
 apply MR2'.
 apply ReflexivityEq.
 apply ReflexivityEq.
Qed.

Definition MakeMap A B F (RF : RFun F):=
_{<Rel_Map ! (MakeMapCond A B F RF)}.

Theorem MakeMapTheorem : forall A B F (RF : RFun F),
forall (a : #A), %(MakeMap A B F RF) a == (F a).
Proof.
intros A B F RF a.
apply AppTheoremReverse.
unfold MakeMap.
apply (RelRewrite' (DSETEq (MakeRelation (fun (a0 : #A) (b : #B) => F a0 == b)) _)).
apply MakeRelationTheorem.
intros a' b' Eqa Eqfb.
apply (TransitivityEq (F a)).
apply RF.
apply SymmetryEq.
assumption.
assumption.
Qed.


Ltac proofRFun :=
intros __proofRFunX_ __proofRFunY_ __EqproofRFun;
repeat (
apply ReflexivityEq ||
apply FunRewrite ||
apply FunRewrite2 ||
(apply EqualInPair; split) ||
(apply EqualInPair'; split) ||
apply MapEq ||
apply MapArgEq ||
apply MapEqAll ||
rewrite DSETEq ||
rewrite USETEq ||
rewrite __EqproofRFun ||
fail 1 " 'proofRFun' is failed"

).


(* Left Pair *)
Theorem LeftPairRMapCond : forall L R,
Rel_MapCond (MakeRelation (fun (p : #(Cartesian L R)) (l : #L) => exists r, p == (Pair l r))).
Proof.
intros L R.
split.

assert (IsP : IsPair a).
 apply (CartesianIsPair _ _ _ (SetProp a)).
destruct IsP as [l IsP].
destruct IsP as [r IsP].
assert(InD : In l L /\ In r R).
 apply CartesianTheorem.
 rewrite <- IsP.
 apply SetProp.
destruct InD as [InlL InrR].
exists {l ! InlL}.
apply MakeRelationTheorem.
intros a' l' Eqa Eql.
exists r.
rewrite <- Eqa.
rewrite IsP.
apply EqualInPair.
split.
assumption.
apply ReflexivityEq.


intros l1 l2 MD.
destruct MD as [MR1 MR2].
put ((proj1 (MakeRelationTheorem _ _ _ _ _)) MR1) MR1'.
put ((proj1 (MakeRelationTheorem _ _ _ _ _)) MR2) MR2'.
clear MR1.
clear MR2.
put (MR1' _ _ (ReflexivityEq a) (ReflexivityEq l1)) MR1.
put (MR2' _ _ (ReflexivityEq a) (ReflexivityEq l2)) MR2.
clear MR1'.
clear MR2'.
destruct MR1 as [r1 MR1].
destruct MR2 as [r2 MR2].
assert(EqP : (Pair l1 r1) == (Pair l2 r2)).
 apply (TransitivityEq a).
 apply SymmetryEq.
 assumption.
 assumption.
apply EqualInPair in EqP.
destruct EqP as [Eql Eqr].
assumption.
Qed.

Definition LeftPair L R := _ {<Rel_Map ! (LeftPairRMapCond L R)}.
Definition MLeft {L R} := LeftPair L R.

Theorem LeftPairTheorem : forall {L R} (l : (#L)) (r : (#R)),
%(LeftPair L R) (Pair' l r) == l.
Proof.
intros L R l r.
apply AppTheoremReverse.
unfold LeftPair.
apply (RelRewrite' (DSETEq (MakeRelation (fun (p : #(Cartesian L R)) (l0 : #L) => exists r0, p == Pair l0 r0)) _)).
apply MakeRelationTheorem.
intros p' l' EDqp Eql.
exists r.
apply SymmetryEq.
apply (TransitivityEq [l; r]).
 apply EqualInPairPair'.
 split.
 apply SymmetryEq.
 assumption.
 apply ReflexivityEq.
assumption.
Qed.

Theorem LeftPairTheorem' : forall {L R} l r (InP : In (Pair l r) (Cartesian L R)),
%(LeftPair L R) {Pair l r ! InP} == l.
Proof.
intros L R l r InP.
assert(InD : In l L /\ In r R).
 apply CartesianTheorem.
 assumption.
destruct InD as [InlL InrR].
apply (TransitivityEq (%(LeftPair _ _) (Pair' {l ! InlL} {r ! InrR}))).
apply MapArgEq.
apply (TransitivityEq (Pair l r)).
apply ReflexivityEq.
apply EqualInPairPair'.
split; apply ReflexivityEq.
apply LeftPairTheorem.
Qed.




(* Right Pair *)
Theorem RightPairRMapCond : forall L R,
Rel_MapCond (MakeRelation (fun (p : #(Cartesian L R)) (r : #R) => exists l, p == (Pair l r))).
Proof.
intros L R.
split.

assert (IsP : IsPair a).
 apply (CartesianIsPair _ _ _ (SetProp a)).
destruct IsP as [l IsP].
destruct IsP as [r IsP].
assert(InD : In l L /\ In r R).
 apply CartesianTheorem.
 rewrite <- IsP.
 apply SetProp.
destruct InD as [InlL InrR].
exists {r ! InrR}.
apply MakeRelationTheorem.
intros a' r' Eqa Eql.
exists l.
rewrite <- Eqa.
rewrite IsP.
apply EqualInPair.
split.
apply ReflexivityEq.
assumption.


intros r1 r2 MD.
destruct MD as [MR1 MR2].
put ((proj1 (MakeRelationTheorem _ _ _ _ _)) MR1) MR1'.
put ((proj1 (MakeRelationTheorem _ _ _ _ _)) MR2) MR2'.
clear MR1.
clear MR2.
put (MR1' _ _ (ReflexivityEq a) (ReflexivityEq r1)) MR1.
put (MR2' _ _ (ReflexivityEq a) (ReflexivityEq r2)) MR2.
clear MR1'.
clear MR2'.
destruct MR1 as [l1 MR1].
destruct MR2 as [l2 MR2].
assert(EqP : (Pair l1 r1) == (Pair l2 r2)).
 apply (TransitivityEq a).
 apply SymmetryEq.
 assumption.
 assumption.
apply EqualInPair in EqP.
destruct EqP as [Eql Eqr].
assumption.
Qed.

Definition RightPair L R := _ {<Rel_Map ! (RightPairRMapCond L R)}.
Definition MRight {L R} := RightPair L R.

Theorem RightPairTheorem : forall {L R} (l : (#L)) (r : (#R)),
%(RightPair L R) (Pair' l r) == r.
Proof.
intros L R l r.
apply AppTheoremReverse.
unfold LeftPair.
apply (RelRewrite' (DSETEq (MakeRelation (fun (p : #(Cartesian L R)) (r0 : #R) => exists l0, p == Pair l0 r0)) _)).
apply MakeRelationTheorem.
intros p' r' EDqp Eql.
exists l.
apply SymmetryEq.
apply (TransitivityEq [l; r]).
 apply EqualInPairPair'.
 split.
 apply ReflexivityEq.
 apply SymmetryEq.
 assumption.
assumption.
Qed.

Theorem RightPairTheorem' : forall {L R} l r (InP : In (Pair l r) (Cartesian L R)),
%(RightPair L R) {Pair l r ! InP} == r.
Proof.
intros L R l r InP.
assert(InD : In l L /\ In r R).
 apply CartesianTheorem.
 assumption.
destruct InD as [InlL InrR].
apply (TransitivityEq (%(RightPair _ _) (Pair' {l ! InlL} {r ! InrR}))).
apply MapArgEq.
apply (TransitivityEq (Pair l r)).
apply ReflexivityEq.
apply EqualInPairPair'.
split; apply ReflexivityEq.
apply RightPairTheorem.
Qed.




Theorem CreatePairEq : forall {A B}
(p : #(Cartesian A B)), [(%MLeft) p; (%MRight) p] == p.
Proof.
intros A B p.
assert(IsPp : IsPair p).
 apply (CartesianIsPair _ _ _ (SetProp p)).
destruct IsPp as [a IsPp].
destruct IsPp as [b IsPp].
assert(InD : In a A /\ In b B).
 apply CartesianTheorem.
 rewrite <- IsPp.
 apply SetProp.
destruct InD as [InaA InbB].
assert(EqP : p == [{a ! InaA} ; {b ! InbB}]).
 apply (TransitivityEq (Pair a b)).
  assumption.
 apply EqualInPairPair'.
 split; apply ReflexivityEq.
apply (TransitivityEq (Pair ((%MLeft) p) ((%MRight p)))).
 apply EqPairPair'.
apply (TransitivityEq (Pair ((%MLeft) [{a ! InaA}; {b ! InbB}]) ((%MRight)[{a ! InaA}; {b ! InbB}]))).
 apply EqualInPair.
 split.
  apply MapArgEq.
  assumption.

  apply MapArgEq.
  assumption.
apply (TransitivityEq (Pair {a ! InaA} {b ! InbB})).
 apply EqualInPair.
 split.
 apply LeftPairTheorem.
 apply RightPairTheorem.
apply (TransitivityEq (Pair a b)).
 apply EqualInPair.
 split; apply ReflexivityEq.
apply SymmetryEq.
assumption.
Qed.

Ltac hyperreflexivity :=
apply ReflexivityEq ||
(apply FunRewrite; hyperreflexivity) ||
(apply FunRewrite2; hyperreflexivity) ||
(apply EqualInPair; split; hyperreflexivity) ||
(apply EqualInPair'; split; hyperreflexivity) ||
(apply MapEq; hyperreflexivity) ||
(apply MapArgEq; hyperreflexivity) ||
(apply MapEqAll; hyperreflexivity) ||
(rewrite USETEq; hyperreflexivity) ||
(rewrite DSETEq; hyperreflexivity) ||
fail 1 "reflexivity fail"
.





(* Combine Map *)
Theorem CombineRelationMapCond : forall A B C, Rel_MapCond (MakeRelation 
  (fun (relD : #(Cartesian (Relation A B) (Relation B C))) (rel : #(Relation A C)) =>
  forall a c, &&rel a c <->
    exists b, (&&(%MLeft relD) a b) /\ (&&(%MRight relD) b c))
).
Proof.
intros A B C.
intro relD.
split.

exists (MakeRelation (fun (a : #A) (c : #C) => exists b , &&(%MLeft relD) a b /\ &&(%MRight relD) b c)).
apply MakeRelationTheorem.
intros relD' rel EqrelD Eqrel a c.
split.
 intro relH.
 apply  (RelRewrite' Eqrel) in relH.
 put ((proj1 (MakeRelationTheorem _ _ _ _ _)) relH) relH'.
 clear relH.
 put (relH' _ _ (ReflexivityEq a) (ReflexivityEq c)) relH.
 clear relH'.
 destruct relH as [b relH].
 destruct relH as [relHL relHR].
 exists b.
 split.
  generalize relHL.
  apply RelRewrite.
  apply MapArgEq.
  apply EqrelD.

  generalize relHR.
  apply RelRewrite.
  apply MapArgEq.
  apply EqrelD.

 intro DD.
 destruct DD as [b DD].
 destruct DD as [relHL relHR].
 apply (RelRewrite Eqrel).
 apply MakeRelationTheorem.
 intros a' c' Eqa Eqc.
 exists b.
 split.
  generalize relHL.
  apply RelRewriteAll.
  apply Eqa.
  apply ReflexivityEq.
  apply MapArgEq.
  apply SymmetryEq.
  apply EqrelD.

  generalize relHR.
  apply RelRewriteAll.
  apply ReflexivityEq.
  apply Eqc.
  apply MapArgEq.
  apply SymmetryEq.
  apply EqrelD.


intros rel1 rel2 relHD.
destruct relHD as [relH1 relH2].
put ((proj1 (MakeRelationTheorem _ _ _ _ _)) relH1) relH1'.
put ((proj1 (MakeRelationTheorem _ _ _ _ _)) relH2) relH2'.
clear relH1.
clear relH2.
put (relH1' _ _ (ReflexivityEq relD) (ReflexivityEq rel1)) relH1.
put (relH2' _ _ (ReflexivityEq relD) (ReflexivityEq rel2)) relH2.
clear relH1'.
clear relH2'.
apply RelEquality.
split.
 apply ToStrongRel.
 intros a c relH.
 apply relH1 in relH.
 apply relH2 in relH.
 exists a.
 exists c.
 split.
 apply ReflexivityEq.
 split.
 apply ReflexivityEq.
 apply relH.

 apply ToStrongRel.
 intros a c relH.
 apply relH2 in relH.
 apply relH1 in relH.
 exists a.
 exists c.
 split.
 apply ReflexivityEq.
 split.
 apply ReflexivityEq.
 apply relH.
Qed.


Definition CombineRelation {A B C} := _ {<Rel_Map ! (CombineRelationMapCond A B C)}.

Theorem CombineRelationTheorem : forall {A B C} (rel1 : #(Relation A B)) (rel2 : #(Relation B C)),
forall (a : #A) (c : #C),
&&(%CombineRelation [rel1; rel2]) a c <->
(exists b : #B, (&&rel1 a b) /\ (&&rel2 b c)).
Proof.
intros A B C rel1 rel2 a c.
assert(AppT : &&(CombineRelation{<Map_Rel}) [rel1;rel2] (%CombineRelation [rel1;rel2])).
 apply AppTheorem.
put ((proj1 (MakeRelationTheorem _ _ _ _ _)) AppT) AppT'.
clear AppT.
put (AppT' _ _ (ReflexivityEq [rel1;rel2]) (ReflexivityEq _)) AppT.
clear AppT'.
split.
 intro relH.
 apply AppT in relH.
 destruct relH as [b relH].
 destruct relH as [relH1 relH2].
 exists b.
 split.
  generalize relH1.
  apply RelRewrite.
  apply LeftPairTheorem.

  generalize relH2.
  apply RelRewrite.
  apply RightPairTheorem.

 intro DD.
 destruct DD as [b DD].
 destruct DD as [relH1 relH2].
 apply AppT.
 exists b.
 split.
  generalize relH1.
  apply RelRewrite.
  apply SymmetryEq.
  apply LeftPairTheorem.

  generalize relH2.
  apply RelRewrite.
  apply SymmetryEq.
  apply RightPairTheorem.
Qed.

Theorem SingletonMap_FunctionIn_ : forall {A} (a : #A), In (Singleton a) (PowerSet A).
Proof.
intros A a.
apply PowersetTheorem.
intros x eqxa.
apply SingletonTheorem in eqxa.
rewrite eqxa.
apply SetProp.
Qed.

Definition SingletonMap_Function__ A := fun a : #A => {Singleton a ! SingletonMap_FunctionIn_ a}.

Theorem SingletonMap_RFF_ {A} : RFun (SingletonMap_Function__ A).
Proof.
unfold SingletonMap_Function__.
proofRFun.
Qed.

Definition SingletonMap {A} : #(Map A (PowerSet A)) :=
MakeMap _ _ (SingletonMap_Function__ A) SingletonMap_RFF_.

Theorem SingletonMapTheorem : forall {A} (a : #A),
%SingletonMap a == (Singleton a).
Proof.
intros A a.
unfold SingletonMap.
rewrite (MakeMapTheorem _ _ _ _ _).
hyperreflexivity.
Qed.


(*
Theorem CombineRelationMapCond : forall A B C, Rel_MapCond (MakeRelation 
  (fun (rel1 : #(Relation A B)) (f : #(Map (Relation B C) (Relation A C))) =>
    forall (rel2 : #(Relation B C)) a c, (&&(%f rel2) a c) <->
      (exists b : #B, &&rel1 a b /\ &&rel2 b c)
  )
).
Proof.
intros A B C.
intro rel1.
split.
 set (MakeRelation (fun (rel2 : #(Relation B C)) (rel3 : #(Relation A C)) => forall a c, &&rel3 a c <-> (exists b, &&rel1 a b /\ &&rel2 b c))) as f.
 assert(MapCondf : Rel_MapCond f).
  intro rel2.
  split.
   exists (MakeRelation (fun (a : #A) (c : #C) => exists b, &&rel1 a b /\ &&rel2 b c)).
   apply MakeRelationTheorem.
   intros rel2' rel3 Eqrel2 Eqrel3 a c.
   split.
    intro relH3.
    apply (RelRewrite' Eqrel3) in relH3.
    put ((proj1 (MakeRelationTheorem _ _ _ _ _)) relH3) relH3'.
    clear relH3.
    put (relH3' _ _ (ReflexivityEq a) (ReflexivityEq c)) relH3.
    clear relH3'.
    destruct relH3 as [b relH3].
    destruct relH3 as [relH1 relH2].
    exists b.
    split.
    assumption.
    generalize relH2.
    apply RelRewrite.
    assumption.

    intro HH.
    destruct HH as [b HH].
    destruct HH as [relH1 relH2].
    apply (RelRewrite Eqrel3).
    apply MakeRelationTheorem.
    intros a' c' Eqa Eqb.
    exists b.
    split.
     generalize relH1.
     apply RelRewriteL.
     assumption.

     generalize relH2.
     apply RelRewriteAll.
     apply ReflexivityEq.
     apply Eqb.
     apply SymmetryEq.
     apply Eqrel2.

   intros rel3 rel3' relDD.
   destruct relDD as [relHf1 relHf2].
   put ((proj1 (MakeRelationTheorem _ _ _ _ _)) relHf1) relHf1'.
   put ((proj1 (MakeRelationTheorem _ _ _ _ _)) relHf2) relHf2'.
   clear relHf1.
   clear relHf2.
   put (relHf1' _ _ (ReflexivityEq rel2) (ReflexivityEq rel3)) relHf1.
   put (relHf2' _ _ (ReflexivityEq rel2) (ReflexivityEq rel3')) relHf2.
   clear relHf1'.
   clear relHf2'.
   apply EA.
   intro p.
   split.
    intro Inprel3.
    assert(IsPp : IsPair p).
     apply (IsPairRelation _ _ Inprel3).
    destruct IsPp as [a IsPp].
    destruct IsPp as [c Eqp].
    assert(InD : In a A /\ In c C).
     rewrite Eqp in Inprel3.
     apply (PairInRelation _ _ _ Inprel3).
    destruct InD as [InaA IncC].
    cut (&&rel3' {a ! InaA} {c ! IncC}).
     intro HH.
     rewrite Eqp.
     unfold If in HH.
     apply HH.
    apply relHf2.
    apply relHf1.
    unfold If.
    rewrite Eqp in Inprel3.
    apply Inprel3.

    intro Inprel3.
    assert(IsPp : IsPair p).
     apply (IsPairRelation _ _ Inprel3).
    destruct IsPp as [a IsPp].
    destruct IsPp as [c Eqp].
    assert(InD : In a A /\ In c C).
     rewrite Eqp in Inprel3.
     apply (PairInRelation _ _ _ Inprel3).
    destruct InD as [InaA IncC].
    cut (&&rel3 {a ! InaA} {c ! IncC}).
     intro HH.
     rewrite Eqp.
     unfold If in HH.
     apply HH.
    apply relHf1.
    apply relHf2.
    unfold If.
    rewrite Eqp in Inprel3.
    apply Inprel3.


 exists (f{<Rel_Map ! MapCondf}).
 apply MakeRelationTheorem.
 intros rel1' f' Eqrel Eqf rel2 a c.
 assert(AppT : &&f rel2 (%f' rel2)).
  cut (&&(f'{<Map_Rel}) rel2 (%f' rel2)).
   apply RelRewrite.
   apply (TransitivityEq (f{<Rel_Map ! MapCondf})).
  apply SymmetryEq.
  apply Eqf.
  apply ReflexivityEq.
  apply AppTheorem.
  put ((proj1 (MakeRelationTheorem _ _ _ _ _)) AppT) AppT'.
  clear AppT.
  put (AppT' _ _ (ReflexivityEq rel2) (ReflexivityEq (%f' rel2)) a c) AppT.
  clear AppT'.
 split.
  intro relH2.
  apply AppT in relH2.
  destruct relH2 as [b relH2].
  destruct relH2 as [relH1 relH2].
  exists b.
  split.
  generalize relH1.
  apply RelRewrite.
  apply Eqrel.
  apply relH2.

  intro HH.
  destruct HH as [b HH].
  destruct HH as [relH1 relH2].
  apply AppT.
  exists b.
  split.
  generalize relH1.
  apply RelRewrite.
  apply SymmetryEq.
  apply Eqrel.
  apply relH2.


 intros f1 f2 HD.
 destruct HD as [H1 H2].
 put ((proj1 (MakeRelationTheorem _ _ _ _ _)) H1) H1'.
 put ((proj1 (MakeRelationTheorem _ _ _ _ _)) H2) H2'.
 clear H1.
 clear H2.
 put (H1' _ _ (ReflexivityEq rel1) (ReflexivityEq f1)) H1.
 put (H2' _ _ (ReflexivityEq rel1) (ReflexivityEq f2)) H2.
 clear H1'.
 clear H2'.
 apply MapEquality.
 apply ReflexivityEq.
 intros rel21 rel22 Eqrel2.
 apply RelEquality.
 split.
  apply ToStrongRel.
  intros a c relH.
  exists a.
  exists c.
  split.
  apply ReflexivityEq.
  split.
  apply ReflexivityEq.
  apply H2.
  apply H1.
  generalize relH.
  apply RelRewrite.
  apply MapArgEq.
  apply Eqrel2.

  apply ToStrongRel.
  intros a c relH.
  exists a.
  exists c.
  split.
  apply ReflexivityEq.
  split.
  apply ReflexivityEq.
  apply H1.
  apply H2.
  generalize relH.
  apply RelRewrite.
  apply MapArgEq.
  apply SymmetryEq.
  apply Eqrel2.
Qed.

Definition CombineRelation {A B C} := _ {<Rel_Map ! (CombineRelationMapCond A B C)}.

Theorem CombineRelationTheorem : forall {A B C} (rel1 : #(Relation A B)) (rel2 : #(Relation B C)),
forall (a : #A) (c : #C),
&&(%(%CombineRelation rel1) rel2) a c <->
(exists b : #B, (&&rel1 a b) /\ (&&rel2 b c)).
Proof.
intros A B C rel1 rel2 a c.
assert(RelH : &&((@CombineRelation A B C){<Map_Rel}) rel1 (%(@CombineRelation A B C) rel1)).
 apply AppTheorem.
put ((proj1 (MakeRelationTheorem _ _ _ _ _)) RelH) RelH'.
clear RelH.
put (RelH' _ _ (ReflexivityEq rel1) (ReflexivityEq _) rel2 a c) RelH.
clear RelH'.
apply RelH.
Qed.

*)

(* CartesianRelationR *)

Theorem CartesianRelationRMapCond : forall A X Y,
Rel_MapCond (MakeRelation 
(fun (rel2 : #(Cartesian (Relation A X) (Relation A Y))) (newrel : #(Relation A (Cartesian X Y))) =>
  forall (a : #A) (x : #X) (y : #Y), (&&(%MLeft rel2) a x) /\ (&&(%MRight rel2) a y) <-> (&&newrel) a [x;y])
).
Proof.
intros A X Y.
intro rel2.
split.


exists (MakeRelation (fun (a : #A) (d : #(Cartesian X Y)) => (&&(%MLeft rel2)) a (%MLeft d) /\ (&&(%MRight rel2)) a (%MRight d))).
apply MakeRelationTheorem.
intros rel2' newrel Eqrel2 Eqnewrel.
intros a x y.
split; intro relH.
 destruct relH as [relH1 relH2].
 apply (RelRewrite Eqnewrel).
 apply MakeRelationTheorem.
 intros a' xy Eqa Eqxy.
 split.
  generalize relH1.
  apply RelRewriteAll.
  assumption.
  apply (TransitivityEq ((%MLeft) [x;y])).
  apply SymmetryEq.
  apply LeftPairTheorem.
  apply MapArgEq.
  assumption.
  apply MapArgEq.
  apply SymmetryEq.
  assumption.

  generalize relH2.
  apply RelRewriteAll.
  assumption.
  apply (TransitivityEq ((%MRight) [x;y])).
  apply SymmetryEq.
  apply RightPairTheorem.
  apply MapArgEq.
  assumption.
  apply MapArgEq.
  apply SymmetryEq.
  assumption.

 apply SymmetryEq in Eqnewrel.
 apply (RelRewrite Eqnewrel) in relH.
 generalize ((proj1 (MakeRelationTheorem _ _ _ _ _)) relH); intro relH'.
 assert (relH'' : (&&((%MLeft) rel2) a ((%MLeft) [x;y])) /\ (&&((%MRight) rel2) a ((%MRight) [x;y]))).
  apply relH'.
  apply ReflexivityEq.
  apply ReflexivityEq.
 destruct relH'' as [relH1 relH2].
 split.
  generalize relH1.
  apply RelRewriteAll.
  apply ReflexivityEq.
  apply LeftPairTheorem.
  apply MapArgEq.
  assumption.
   
  generalize relH2.
  apply RelRewriteAll.
  apply ReflexivityEq.
  apply RightPairTheorem.
  apply MapArgEq.
  assumption.


intros newrel1 newrel2 relD.
destruct relD as [relH1 relH2].
put ((proj1 (MakeRelationTheorem _ _ _ _ _)) relH1) relH1'.
put ((proj1 (MakeRelationTheorem _ _ _ _ _)) relH2) relH2'.
clear relH1.
clear relH2.
put (relH1' _ _ (ReflexivityEq rel2) (ReflexivityEq newrel1)) relH1.
put (relH2' _ _ (ReflexivityEq rel2) (ReflexivityEq newrel2)) relH2.
clear relH1'.
clear relH2'.
apply RelEquality.
split.
 apply ToStrongRel.
 intros a b relab.
 exists a.
 exists b.
 split.
 apply ReflexivityEq.
 split.
 apply ReflexivityEq.
 cut ((&&newrel2) a [(%MLeft) b; (%MRight) b]).
  apply RelRewriteR.
  apply CreatePairEq.
 apply relH2.
 apply relH1.
 generalize relab.
 apply RelRewriteR.
 apply SymmetryEq.
 apply CreatePairEq.

 apply ToStrongRel.
 intros a b relab.
 exists a.
 exists b.
 split.
 apply ReflexivityEq.
 split.
 apply ReflexivityEq.
 cut ((&&newrel1) a [(%MLeft) b; (%MRight) b]).
  apply RelRewriteR.
  apply CreatePairEq.
 apply relH1.
 apply relH2.
 generalize relab.
 apply RelRewriteR.
 apply SymmetryEq.
 apply CreatePairEq.
Qed.

Definition CartesianRelationR {A X Y} := _ {<Rel_Map ! (CartesianRelationRMapCond A X Y)}.

Theorem CartesianRelationRTheorem : forall {A X Y}
(rel1 : #(Relation A X)) (rel2 : #(Relation A Y)),
forall (a : #A) (x : #X) (y : #Y),
(&&rel1 a x /\ &&rel2 a y) <-> &&((%(CartesianRelationR)) [rel1; rel2]) a [x;y].
Proof.
intros A X Y rel1 rel2 a x y.
assert(RelH : &&((CartesianRelationR){<Map_Rel}) [rel1; rel2] (%(CartesianRelationR) [rel1; rel2])).
 apply AppTheorem.
put ((proj1 (MakeRelationTheorem _ _ _ _ _)) RelH) RelH'.
clear RelH.
put (RelH' _ _ (ReflexivityEq [rel1; rel2]) (ReflexivityEq (%(CartesianRelationR) [rel1; rel2]))) RelH.
clear RelH'.
apply (TransitivityEquiv ((&& (%MLeft [rel1; rel2]) a x) /\ (&& (%MRight [rel1; rel2]) a y))).
 split.
  intro relD.
  destruct relD as [relH1 relH2].
  split.
   generalize relH1.
   apply RelRewrite.
   apply SymmetryEq.
   apply LeftPairTheorem.

   generalize relH2.
   apply RelRewrite.
   apply SymmetryEq.
   apply RightPairTheorem.

  intro relD.
  destruct relD as [relH1 relH2].
  split.
   generalize relH1.
   apply RelRewrite.
   apply LeftPairTheorem.

   generalize relH2.
   apply RelRewrite.
   apply RightPairTheorem.
apply RelH.
Qed.


(* RelationImage *)
Theorem RelationImageRMapCond A B : Rel_MapCond (MakeRelation 
(fun (rel : #(Relation A B)) (map : #(Map (PowerSet A) (PowerSet B))) =>
  forall SA : #(PowerSet A), forall b : #B,
    In b (%map SA) <-> exists a : #A, In a SA /\ &&rel a b
)).
Proof.
intro rel.
split.

assert(MC : (Rel_MapCond (MakeRelation (fun (SA : #(PowerSet A)) (SB : #(PowerSet B)) => forall b : #B, In b SB <-> exists a : #A, In a SA /\ &&rel a b)))).
 intro SA.
 split.
  assert (SubSB : In (SSet' B (fun b => exists a : #A, In a SA /\ &&rel a b)) (PowerSet B)).
   apply PowersetTheorem.
   apply SSetSubset.
  exists {_ ! SubSB}.
  apply MakeRelationTheorem.
  intros SA' SB' EqSA EqSB b.
  split.
   intro InbSB'.
   rewrite <- EqSB in InbSB'.
   rewrite (DSETEq _ SubSB) in InbSB'.
   apply SSet'Theorem in InbSB'.
   destruct InbSB' as [InbB InbSB'].
   destruct (InbSB' InbB) as [a HH].
   destruct HH as [InaSA relH].
   exists a.
   split.
   rewrite <- EqSA.
   assumption.
   generalize (relH).
   apply RelRewriteR.
   apply ReflexivityEq.

   intros HH.
   destruct HH as [a HH].
   destruct HH as [InaSA' relH].
   rewrite <- EqSB.
   rewrite (DSETEq _ SubSB).
   apply SSet'Theorem.
   split.
   apply SetProp.
   intros InbB.
   exists a.
   split.
   rewrite EqSA.
   assumption.
   generalize relH.
   apply RelRewriteR.
   apply ReflexivityEq.

 intros SB1 SB2 HD.
 destruct HD as [HM1 HM2].
 put ((proj1 (MakeRelationTheorem _ _ _ _ _)) HM1) HM1'.
 put ((proj1 (MakeRelationTheorem _ _ _ _ _)) HM2) HM2'.
 clear HM1.
 clear HM2.
 put (HM1' _ _ (ReflexivityEq SA) (ReflexivityEq SB1)) HM1.
 put (HM2' _ _ (ReflexivityEq SA) (ReflexivityEq SB2)) HM2.
 clear HM1'.
 clear HM2'.
 apply EA.
 intro b.
 split.
  intro InbSB1.
  assert(Inb : In b B).
   put (SetProp SB1) Po.
   apply PowersetTheorem in Po.
   apply Po.
   assumption.
  rewrite <- (DSETEq _ Inb).
  apply HM2.
  apply HM1.
  apply InbSB1.

  intro InbSB2.
  assert(Inb : In b B).
   put (SetProp SB2) Po.
   apply PowersetTheorem in Po.
   apply Po.
   assumption.
  rewrite <- (DSETEq _ Inb).
  apply HM1.
  apply HM2.
  apply InbSB2.

exists (_{<Rel_Map ! MC}).
apply MakeRelationTheorem.
intros rel' map Eqrel Eqmap SA b.
assert(AppT : &&((_{<Rel_Map ! MC}){<Map_Rel}) SA (%(_{<Rel_Map ! MC}) SA)).
 apply AppTheorem.
put ((proj1 (MakeRelationTheorem _ _ _ _ _)) AppT) AppT'.
clear AppT.
put (AppT' _ _ (ReflexivityEq SA) (ReflexivityEq _) b) AppT.
clear AppT'.
 assert(EqmSA : (%map SA) == (%(_{<Rel_Map ! MC}) SA)).
  apply MapEq.
  apply SymmetryEq.
  apply Eqmap.
rewrite EqmSA.
clear EqmSA.
split.
 intro InbM.
 apply AppT in InbM.
 destruct InbM as [a InbM].
 destruct InbM as [InaSA relH].
 exists a.
 split.
 assumption.
 generalize relH.
 apply RelRewrite.
 apply Eqrel.

 intro HH.
 apply AppT.
 destruct HH as [a HH].
 destruct HH as [InaSA relH].
 exists a.
 split.
 assumption.
 generalize relH.
 apply RelRewrite.
 apply SymmetryEq.
 apply Eqrel.


intros m1 m2 HD.
destruct HD as [MH1 MH2].
put ((proj1 (MakeRelationTheorem _ _ _ _ _)) MH1) MH1'.
put ((proj1 (MakeRelationTheorem _ _ _ _ _)) MH2) MH2'.
clear MH1.
clear MH2.
put (MH1' _ _ (ReflexivityEq rel) (ReflexivityEq m1)) MH1.
put (MH2' _ _ (ReflexivityEq rel) (ReflexivityEq m2)) MH2.
clear MH1'.
clear MH2'.
apply MapEquality.
apply ReflexivityEq.
intros SA1 SA2 EqSA.
apply EA.
intro b.
split.
 intro Inbm1.
 assert(InbB : In b B).
  assert (InPB : In (%m1 SA1) (PowerSet B)).
   apply MapIn.
  apply PowersetTheorem in InPB.
  apply InPB.
  assumption.
 rewrite <- (DSETEq _ InbB).
 apply MH2.
 apply MH1.
 assert(Eqm1 : (%m1 SA1) == (%m1 SA2)).
  apply MapArgEq.
  assumption.
 rewrite <- Eqm1.
 apply Inbm1.

 intro Inbm2.
 assert(InbB : In b B).
  assert (InPB : In (%m2 SA2) (PowerSet B)).
   apply MapIn.
  apply PowersetTheorem in InPB.
  apply InPB.
  assumption.
 rewrite <- (DSETEq _ InbB).
 apply MH1.
 apply MH2.
 assert(Eqm2 : (%m2 SA1) == (%m2 SA2)).
  apply MapArgEq.
  assumption.
 rewrite Eqm2.
 apply Inbm2.
Qed.

Definition RelationImageR {A B} : #(Map (Relation A B) (Map (PowerSet A) (PowerSet B))) :=
_ {<Rel_Map ! (RelationImageRMapCond A B)}.

Theorem RelationImageRTheorem : forall A B (rel : #(Relation A B)),
forall (SA : #(PowerSet A)),
(forall b : #B, In b (%(%RelationImageR rel) SA) <-> exists a : #A, In a SA /\ &&rel a b).
Proof.
intros A B rel SA b.
assert (relH : &&(RelationImageR{<Map_Rel}) rel (%RelationImageR rel)).
 apply AppTheorem.
put ((proj1 (MakeRelationTheorem _ _ _ _ _)) relH) relH'.
clear relH.
put (relH' _ _ (ReflexivityEq rel) (ReflexivityEq ((%RelationImageR) rel)) SA b) relH.
clear relH'.
apply relH.
Qed.

Theorem RelationImageRSubset : forall {A B} (rel : #(Relation A B)) (sa : #(PowerSet A)),
Subset (%(%RelationImageR rel) sa) B.
Proof.
intros A B rel sa b InbR.
assert(InRPB : In (%(%RelationImageR rel) sa) (PowerSet B)).
 apply MapIn.
apply PowersetTheorem in InRPB.
apply InRPB in InbR.
assumption.
Qed.

(* AndRelation *)
Theorem AndRelationCond A B : Rel_MapCond (
MakeRelation (fun (relD : #(Cartesian (Relation A B) (Relation A B))) (rel : #(Relation A B)) => forall a b, &&rel a b <-> (&&(%MLeft relD) a b /\ &&(%MRight relD) a b))
).
Proof.
intro relD.
split.

set (MakeRelation (fun a b => &&(%MLeft relD) a b /\ &&(%MRight relD) a b)) as rel.
exists rel.
apply MakeRelationTheorem.
intros relD' rel' EqrelD Eqrel a b.
split.
 intro relH.
 apply (RelRewrite' Eqrel) in relH.
 put ((proj1 (MakeRelationTheorem _ _ _ _ _)) relH) relH'.
 clear relH.
 put (relH' _ _ (ReflexivityEq a) (ReflexivityEq b)) relH.
 clear relH'.
 destruct relH as [relH1 relH2].
 split.
  generalize relH1.
  apply RelRewrite.
  apply MapArgEq.
  apply EqrelD.

  generalize relH2.
  apply RelRewrite.
  apply MapArgEq.
  apply EqrelD.
 intro relHD.
 destruct relHD as [relH1 relH2].
 apply (RelRewrite Eqrel).
 apply MakeRelationTheorem.
 intros a' b' Eqa Eqb.
 split.
  generalize relH1.
  apply RelRewriteAll.
  apply Eqa.
  apply Eqb.
  apply MapArgEq.
  apply SymmetryEq.
  apply EqrelD.

  generalize relH2.
  apply RelRewriteAll.
  apply Eqa.
  apply Eqb.
  apply MapArgEq.
  apply SymmetryEq.
  apply EqrelD.

intros rel1 rel2 relHD.
destruct relHD as [relH1 relH2].
put ((proj1 (MakeRelationTheorem _ _ _ _ _)) relH1) relH1'.
clear relH1.
put (relH1' _ _ (ReflexivityEq relD) (ReflexivityEq rel1)) relH1.
clear relH1'.
put ((proj1 (MakeRelationTheorem _ _ _ _ _)) relH2) relH2'.
clear relH2.
put (relH2' _ _ (ReflexivityEq relD) (ReflexivityEq rel2)) relH2.
clear relH2'.
apply RelEquality.
split.
 apply ToStrongRel.
 intros a b relH.
 exists a.
 exists b.
 split.
 hyperreflexivity.
 split.
 hyperreflexivity.
 apply relH2.
 apply relH1.
 assumption.

 apply ToStrongRel.
 intros a b relH.
 exists a.
 exists b.
 split.
 hyperreflexivity.
 split.
 hyperreflexivity.
 apply relH1.
 apply relH2.
 assumption.
Qed.

Definition AndRelation {A B} : #(Map (Cartesian (Relation A B) (Relation A B)) (Relation A B)) :=
_{<Rel_Map ! (AndRelationCond A B)}.

Theorem AndRelationTheorem : forall {A B} (rel1 : #(Relation A B)) (rel2 : #(Relation A B)) a b,
&&(%AndRelation [rel1 ; rel2]) a b <-> (&&rel1 a b /\ &&rel2 a b).
Proof.
intros A B rel1 rel2 a b.
assert(AppH : &&(AndRelation{<Map_Rel}) [rel1; rel2] (%AndRelation [rel1;rel2])).
 apply AppTheorem.
put ((proj1 (MakeRelationTheorem _ _ _ _ _)) AppH) AppH'.
clear AppH.
put (AppH' _ _ (ReflexivityEq [rel1; rel2]) (ReflexivityEq _)) AppH.
clear AppH'.
split.
 intro relHD.
 apply AppH in relHD.
 destruct relHD as [relH1 relH2].
 split.
  generalize relH1.
  apply RelRewrite.
  apply LeftPairTheorem.

  generalize relH2.
  apply RelRewrite.
  apply RightPairTheorem.

 intro relH.
 destruct relH as [relH1 relH2].
 apply AppH.
 split.
  generalize relH1.
  apply RelRewrite.
  apply SymmetryEq.
  apply LeftPairTheorem.

  generalize relH2.
  apply RelRewrite.
  apply SymmetryEq.
  apply RightPairTheorem.
Qed.
 

(* UnionRelation *)
Theorem UnionRelationLMCond A1 A2 B : Rel_MapCond (
  MakeRelation (fun (relD : #(Cartesian (Relation A1 B) (Relation A2 B))) (newrel : #(Relation (Union A1 A2) B)) => 
    forall a b, &&newrel a b <-> ((exists a1 : #A1, a == a1 /\ &&(%MLeft relD) a1 b) \/ (exists a2 : #A2, a == a2 /\ &&(%MRight relD) a2 b))
  )
).
Proof.
intro relD.
split.

exists (MakeRelation (fun (a : #(Union A1 A2)) (b : #B) => (exists a1 : #A1, a == a1 /\ &&(%MLeft relD) a1 b) \/ (exists a2 : #A2, a == a2 /\ &&(%MRight relD) a2 b))).
apply MakeRelationTheorem.
intros relD' newrel EqrelD MEq.
intros a b.
split.
 intro newrelH.
 apply (RelRewrite' MEq) in newrelH.
 put ((proj1 (MakeRelationTheorem _ _ _ _ _)) newrelH) newrelH'.
 clear newrelH.
 put (newrelH' _ _ (ReflexivityEq a) (ReflexivityEq b)) newrelH.
 clear newrelH'.
 destruct newrelH as [relH1 | relH2].
  left.
  destruct relH1 as [a1 relH1].
  destruct relH1 as [Eqa Rel1].
  exists a1.
  split.
  assumption.
  generalize Rel1.
  apply RelRewrite.
  apply MapArgEq.
  assumption.

  right.
  destruct relH2 as [a2 relH2].
  destruct relH2 as [Eqa Rel2].
  exists a2.
  split.
  assumption.
  generalize Rel2.
  apply RelRewrite.
  apply MapArgEq.
  assumption.

 intros MD.
 apply (RelRewrite MEq).
 apply MakeRelationTheorem.
 intros a' b' Eqa Eqb.
 destruct MD as [relH1 | relH2].
  destruct relH1 as [a1 relH1].
  destruct relH1 as [Eqa1 relH1].
  left.
  exists a1.
  split.
  rewrite <- Eqa.
  assumption.
  generalize relH1.
  apply RelRewriteAll.
  apply ReflexivityEq.
  auto.
  apply MapArgEq.
  apply SymmetryEq.
  assumption.

  destruct relH2 as [a2 relH2].
  destruct relH2 as [Eqa1 relH2].
  right.
  exists a2.
  split.
  rewrite <- Eqa.
  assumption.
  generalize relH2.
  apply RelRewriteAll.
  apply ReflexivityEq.
  auto.
  apply MapArgEq.
  apply SymmetryEq.
  assumption.

intros rel1 rel2 relHD.
destruct relHD as [relH1 relH2].
put ((proj1 (MakeRelationTheorem _ _ _ _ _)) relH1) relH1'.
put ((proj1 (MakeRelationTheorem _ _ _ _ _)) relH2) relH2'.
clear relH1.
clear relH2.
put (relH1' _ _ (ReflexivityEq relD) (ReflexivityEq rel1)) relH1.
put (relH2' _ _ (ReflexivityEq relD) (ReflexivityEq rel2)) relH2.
clear relH1'.
clear relH2'.
apply RelEquality.
split.
 apply ToStrongRel.
 intros a b relH1'.
 exists a.
 exists b.
 split.
 apply ReflexivityEq.
 split.
 apply ReflexivityEq.
 apply relH2.
 apply relH1.
 assumption.

 apply ToStrongRel.
 intros a b relH2'.
 exists a.
 exists b.
 split.
 apply ReflexivityEq.
 split.
 apply ReflexivityEq.
 apply relH1.
 apply relH2.
 assumption.
Qed.

Definition UnionRelationL {A1 A2 B} := _ {<Rel_Map ! UnionRelationLMCond A1 A2 B}.

Theorem UnionRelationLTheorem : forall {A1 A2 B} (rel1 : #(Relation A1 B)) (rel2 : #(Relation A2 B)),
forall (a : #(Union A1 A2)) (b : #B), &&(%UnionRelationL [rel1; rel2]) a b <->
(exists a1 : #A1, a == a1 /\ &&rel1 a1 b) \/ (exists a2 : #A2, a == a2 /\ &&rel2 a2 b).
Proof.
intros A1 A2 B rel1 rel2 a b.
assert (AppH : &&(UnionRelationL{<Map_Rel}) [rel1; rel2] (%UnionRelationL [rel1; rel2])).
 apply AppTheorem.
put ((proj1 (MakeRelationTheorem _ _ _ _ _)) AppH) AppH'.
clear AppH.
put (AppH' _ _ (ReflexivityEq [rel1; rel2]) (ReflexivityEq _)) AppH.
clear AppH'.
apply (TransitivityEquiv _ (AppH _ _)).
split.

intro RelHH.
destruct RelHH as [RelHH | RelHH].
 destruct RelHH as [a1 RelHH].
 destruct RelHH as [Eqa1 RelHH].
 left.
 exists a1.
 split.
 auto.
 generalize RelHH.
 apply RelRewrite.
 apply LeftPairTheorem.

 destruct RelHH as [a2 RelHH].
 destruct RelHH as [Eqa2 RelHH].
 right.
 exists a2.
 split.
 auto.
 generalize RelHH.
 apply RelRewrite.
 apply RightPairTheorem.

intro RelHH.
destruct RelHH as [RelHH | RelHH].
 destruct RelHH as [a1 RelHH].
 destruct RelHH as [Eqa1 RelHH].
 left.
 exists a1.
 split.
 assumption.
 generalize RelHH.
 apply RelRewrite.
 apply SymmetryEq.
 apply LeftPairTheorem.

 destruct RelHH as [a2 RelHH].
 destruct RelHH as [Eqa2 RelHH].
 right.
 exists a2.
 split.
 assumption.
 generalize RelHH.
 apply RelRewrite.
 apply SymmetryEq.
 apply RightPairTheorem.
Qed.


(* RistrictRelationL *)
Theorem RistrictRelationLMCond A S B (sub : Subset S A) : Rel_MapCond
(MakeRelation (fun (rel : #(Relation A B)) (newrel : #(Relation S B)) =>
  forall (a : #S) (b : #B), &&newrel a b <-> &&rel (a{<sub}) b
)).
Proof.
intro rel.
split.

exists (MakeRelation (fun (a : #S) (b : #B) => &&rel (a{<sub}) b)).
apply MakeRelationTheorem.
intros rel' newrel Eqrel MEq.
intros a b.
split.
 intro relH.
 apply (RelRewrite' MEq) in relH.
 put ((proj1 (MakeRelationTheorem _ _ _ _ _)) relH) relH'.
 clear relH.
 generalize (relH' _ _ (ReflexivityEq a) (ReflexivityEq b)).
 apply RelRewrite.
 assumption.

 intros relH.
 apply (RelRewrite MEq).
 apply MakeRelationTheorem.
 intros a' b' Eqa Eqb.
 generalize (relH).
 apply RelRewriteAll.
 apply Eqa.
 assumption.
 apply SymmetryEq.
 apply Eqrel.

intros nrel1 nrel2 relD.
destruct relD as [relH1 relH2].
put ((proj1 (MakeRelationTheorem _ _ _ _ _)) relH1) relH1'.
put ((proj1 (MakeRelationTheorem _ _ _ _ _)) relH2) relH2'.
clear relH1.
clear relH2.
put (relH1' _ _ (ReflexivityEq rel) (ReflexivityEq nrel1)) relH1.
put (relH2' _ _ (ReflexivityEq rel) (ReflexivityEq nrel2)) relH2.
clear relH1'.
clear relH2'.
apply RelEquality.
split.
 apply ToStrongRel.
 intros a b relH1'.
 exists a.
 exists b.
 split.
 apply ReflexivityEq.
 split.
 apply ReflexivityEq.
 apply relH2.
 apply relH1.
 assumption.

 apply ToStrongRel.
 intros a b relH2'.
 exists a.
 exists b.
 split.
 apply ReflexivityEq.
 split.
 apply ReflexivityEq.
 apply relH1.
 apply relH2.
 assumption.
Qed.

Definition RistrictRelationL {A S B} (sub : Subset S A) := _ {<Rel_Map ! RistrictRelationLMCond A S B sub}.

Theorem ToRistrictRelationL : forall {A S B} (sub : Subset S A) (rel : #(Relation A B)),
forall (a : #S) (b : #B),
&&rel (a{<sub}) b -> &&(%(RistrictRelationL sub) rel) a b.
Proof.
intros A S B sub rel a b relH.
assert(AppT : &&((RistrictRelationL sub){<Map_Rel}) rel (%(RistrictRelationL sub) rel)).
 apply AppTheorem.
put ((proj1 (MakeRelationTheorem _ _ _ _ _)) AppT) AppT'.
clear AppT.
put (AppT' _ _ (ReflexivityEq rel) (ReflexivityEq _)) AppT.
clear AppT'.
apply AppT.
assumption.
Qed.


Theorem StrongRelRistrictL : forall A S B (sub : Subset S A),
forall (rel : #(Relation A B)),
StrongRel (%(RistrictRelationL sub) rel) rel.
Proof.
intros A S B sub rel.
apply ToStrongRel.
intros a b relH.
exists (a{<sub}).
exists b.
split.
apply ReflexivityEq.
split.
apply ReflexivityEq.
assert(AppT : &&((RistrictRelationL sub){<Map_Rel}) rel (%(RistrictRelationL sub) rel)).
 apply AppTheorem.
put ((proj1 (MakeRelationTheorem _ _ _ _ _)) AppT) AppT'.
clear AppT.
put (AppT' _ _ (ReflexivityEq rel) (ReflexivityEq _)) AppT.
clear AppT'.
apply AppT.
apply relH.
Qed.

Theorem RistrictRelationLTheorem : forall {A S B} {a : #A} {sa : #S} {b : #B} (rel : #(Relation A B))  (sub : Subset S A),
a == sa ->
(&&(%(RistrictRelationL sub) rel) sa b <-> &&rel a b).
Proof.
intros A S B a sa b rel sub Eqa.
split.
 apply StrongRelationRel.
 rewrite Eqa.
 apply ReflexivityEq.
 apply ReflexivityEq.
 apply StrongRelRistrictL.

 intro relH.
 apply ToRistrictRelationL.
 generalize relH.
 apply RelRewriteL.
 apply Eqa.
Qed.

Theorem RistrictRelationLTheoremSubp : forall {A S B} {a : #S} {b : #B} (rel : #(Relation A B))  (sub : Subset S A),
(&&(%(RistrictRelationL sub) rel) a b <-> &&rel (a{<sub}) b).
Proof.
intros A S B a b rel sub.
apply RistrictRelationLTheorem.
apply ReflexivityEq.
Qed.


(* RistrictRelationR *)
Theorem RistrictRelationRMCond A B S (sub : Subset S B) : Rel_MapCond
(MakeRelation (fun (rel : #(Relation A B)) (newrel : #(Relation A S)) =>
  forall (a : #A) (b : #S), &&newrel a b <-> &&rel a (b{<sub})
)).
Proof.
intro rel.
split.

exists (MakeRelation (fun (a : #A) (b : #S) => &&rel a (b{<sub}))).
apply MakeRelationTheorem.
intros rel' newrel Eqrel MEq.
intros a b.
split.
 intro relH.
 apply (RelRewrite' MEq) in relH.
 put ((proj1 (MakeRelationTheorem _ _ _ _ _)) relH) relH'.
 clear relH.
 generalize (relH' _ _ (ReflexivityEq a) (ReflexivityEq b)).
 apply RelRewrite.
 assumption.

 intros relH.
 apply (RelRewrite MEq).
 apply MakeRelationTheorem.
 intros a' b' Eqa Eqb.
 generalize (relH).
 apply RelRewriteAll.
 apply Eqa.
 assumption.
 apply SymmetryEq.
 apply Eqrel.

intros nrel1 nrel2 relD.
destruct relD as [relH1 relH2].
put ((proj1 (MakeRelationTheorem _ _ _ _ _)) relH1) relH1'.
put ((proj1 (MakeRelationTheorem _ _ _ _ _)) relH2) relH2'.
clear relH1.
clear relH2.
put (relH1' _ _ (ReflexivityEq rel) (ReflexivityEq nrel1)) relH1.
put (relH2' _ _ (ReflexivityEq rel) (ReflexivityEq nrel2)) relH2.
clear relH1'.
clear relH2'.
apply RelEquality.
split.
 apply ToStrongRel.
 intros a b relH1'.
 exists a.
 exists b.
 split.
 apply ReflexivityEq.
 split.
 apply ReflexivityEq.
 apply relH2.
 apply relH1.
 assumption.

 apply ToStrongRel.
 intros a b relH2'.
 exists a.
 exists b.
 split.
 apply ReflexivityEq.
 split.
 apply ReflexivityEq.
 apply relH1.
 apply relH2.
 assumption.
Qed.

Definition RistrictRelationR {A B S} (sub : Subset S B) := _ {<Rel_Map ! RistrictRelationRMCond A B S sub}.



Theorem ToRistrictRelationR : forall {A B S} (sub : Subset S B) (rel : #(Relation A B)),
forall (a : #A) (b : #S),
&&rel a (b{<sub}) -> &&(%(RistrictRelationR sub) rel) a b.
Proof.
intros A B S sub rel a b relH.
assert(AppT : &&((RistrictRelationR sub){<Map_Rel}) rel (%(RistrictRelationR sub) rel)).
 apply AppTheorem.
put ((proj1 (MakeRelationTheorem _ _ _ _ _)) AppT) AppT'.
clear AppT.
put (AppT' _ _ (ReflexivityEq rel) (ReflexivityEq _)) AppT.
clear AppT'.
apply AppT.
assumption.
Qed.

Theorem StrongRelRistrictR : forall A B S (sub : Subset S B),
forall (rel : #(Relation A B)),
StrongRel (%(RistrictRelationR sub) rel) rel.
Proof.
intros A B S sub rel.
apply ToStrongRel.
intros a b relH.
exists a.
exists (b{<sub}).
split.
apply ReflexivityEq.
split.
apply ReflexivityEq.
assert(AppT : &&((RistrictRelationR sub){<Map_Rel}) rel (%(RistrictRelationR sub) rel)).
 apply AppTheorem.
put ((proj1 (MakeRelationTheorem _ _ _ _ _)) AppT) AppT'.
clear AppT.
put (AppT' _ _ (ReflexivityEq rel) (ReflexivityEq _)) AppT.
clear AppT'.
apply AppT.
apply relH.
Qed.

(* Ristrict Map *)
Definition RistableMap A B SA SB :=
SSet' (Map A B) (fun f => Subset SA A /\ Subset SB B /\ forall (a : #A), In a SA -> In (%f a) SB).

Theorem RistableMapTheorem : forall {A B} SA SB (f : #(Map A B)),
In f (RistableMap A B SA SB) <-> 
(Subset SA A /\ Subset SB B) /\ forall (a : #A), In a SA -> In (%f a) SB.
Proof.
intros A B SA SB f.
split.
 intro InfR.
 apply SSet'Theorem in InfR.
 destruct InfR as [InfM HH].
 destruct (HH InfM) as [SubA HH'].
 destruct HH' as [SubB HH'].
 split.
 split; assumption.
 intros a InaSA.
 cut (In (%{f ! InfM} a) SB).
  apply Arrow2Rewrite.
  apply MapEq.
  apply ReflexivityEq.
  apply ReflexivityEq.
 apply HH'.
 assumption.

 intro DD.
 destruct DD as [[SubA SubB] DD].
 apply SSet'Theorem.
 split.
 apply SetProp.
 intros InfM'.
 split.
 assumption.
 split.
 assumption.
 intros a InaSA.
 cut (In (%f a) SB).
  apply Arrow2Rewrite.
  apply MapEq.
  apply ReflexivityEq.
  apply ReflexivityEq.
 apply DD.
 apply InaSA.
Qed.

Theorem RistableMapTheoremSubA : forall A B SA SB,
NonEmpty (RistableMap A B SA SB) -> 
Subset SA A.
Proof.
intros A B SA SB NER.
destruct NER as [f NER].
apply SSet'Theorem in NER.
destruct NER as [InfM NER].
specialize NER with InfM.
destruct NER as [SubA NER].
apply SubA.
Qed.

Theorem RistableMapTheoremSubB : forall A B SA SB,
NonEmpty (RistableMap A B SA SB) -> 
Subset SB B.
Proof.
intros A B SA SB NER.
destruct NER as [f NER].
apply SSet'Theorem in NER.
destruct NER as [InfM NER].
specialize NER with InfM.
destruct NER as [SubA NER].
destruct NER as [SubB NER].
apply SubB.
Qed.

Theorem RistableMapTheoremIn : forall {A B} SA SB (f : #(Map A B)),
In f (RistableMap A B SA SB) -> 
forall (a : #A), In a SA -> In (%f a) SB.
Proof.
intros A B SA SB f InfR a InsA.
apply RistableMapTheorem in InfR.
destruct InfR as [[SubA SubB] InfR].
apply InfR.
assumption.
Qed.

Theorem RistableMap_Map : forall {A B SA SB},
Subset (RistableMap A B SA SB) (Map A B).
Proof.
intros A B SA SB.
apply SSet'Subset.
Qed.


Theorem RistMapRelMapCond : forall {A B} SA SB, Rel_MapCond (
  MakeRelation (fun (of : #(RistableMap A B SA SB)) (nf : #(Map SA SB)) =>
    forall (a : #A) (sa : #SA), a == sa -> (%(of{<RistableMap_Map}) a) == (%nf sa)
  )
).
Proof.
intros A B SA SB.
intro f.
assert(SubA : Subset SA A).
 apply (RistableMapTheoremSubA A B SA SB).
 exists f.
 apply SetProp.
assert(SubB : Subset SB B).
 apply (RistableMapTheoremSubB A B SA SB).
 exists f.
 apply SetProp.
split.


set (%(RistrictRelationR SubB) (%(RistrictRelationL SubA) (f{<RistableMap_Map}{<Map_Rel}))) as nf.
assert (MCond : Rel_MapCond nf).
intro sa.
split.
 assert(AppT : &&(f{<RistableMap_Map}{<Map_Rel}) (sa{<SubA}) (%(f{<RistableMap_Map}) (sa{<SubA}))).
  apply AppTheorem.
 apply (ToRistrictRelationL) in AppT.
 assert(InSB : In (%(f{<RistableMap_Map}) (sa{<SubA})) SB).
  apply (RistableMapTheoremIn SA SB).
  apply (SetProp f).
  apply (SetProp sa).
 assert(fsaEq : (%(f{<RistableMap_Map}) (sa{<SubA})) == {_! InSB}{<SubB}).
  apply ReflexivityEq.
 apply (RelRewriteR fsaEq) in AppT.
 clear fsaEq.
 apply (ToRistrictRelationR) in AppT.
 exists ({_!InSB}).
 apply AppT.

 intros sb1 sb2 D.
 destruct D as [D1 D2].
 assert(Eqb1 : sb1 == (sb1{<SubB})).
  apply ReflexivityEq.
 assert(Eqb2 : sb2 == (sb2{<SubB})).
  apply ReflexivityEq.
 apply (StrongRelationRel (ReflexivityEq sa) Eqb1 (StrongRelRistrictR _ _ _ _ _)) in D1.
 apply (StrongRelationRel (ReflexivityEq sa) Eqb2 (StrongRelRistrictR _ _ _ _ _)) in D2.
 assert(Eqa : sa == (sa{<SubA})).
  apply ReflexivityEq.
 apply (StrongRelationRel Eqa (ReflexivityEq _) (StrongRelRistrictL _ _ _ _ _)) in D1.
 apply (StrongRelationRel Eqa (ReflexivityEq _) (StrongRelRistrictL _ _ _ _ _)) in D2.
 apply AppTheoremReverse in D1.
 apply AppTheoremReverse in D2.
 rewrite Eqb1.
 rewrite Eqb2.
 rewrite <- D1.
 rewrite <- D2.
 apply ReflexivityEq.
exists (_{<Rel_Map ! MCond}).
apply MakeRelationTheorem.
intros f' nf' Eqf Eqnf a sa Eqa.
apply SymmetryEq.
apply MapStrong.
apply (TransitivityStrongRel nf).
 apply ReflexivityStrongRel2.
 apply (TransitivityEq nf').
  apply ReflexivityEq.
 rewrite <-Eqnf.
 apply ReflexivityEq.
apply (TransitivityStrongRel (%(RistrictRelationL SubA) (f{<RistableMap_Map}{<Map_Rel}))).
 apply StrongRelRistrictR.
apply (TransitivityStrongRel (f{<RistableMap_Map}{<Map_Rel})).
 apply StrongRelRistrictL.
apply ReflexivityStrongRel2.
apply (TransitivityEq f').
 rewrite <- Eqf.
 apply ReflexivityEq.
apply ReflexivityEq.
apply SymmetryEq.
apply Eqa.


intros f1 f2 MD.
destruct MD as [MH1 MH2].
put ((proj1 (MakeRelationTheorem _ _ _ _ _)) MH1) MH1'.
put ((proj1 (MakeRelationTheorem _ _ _ _ _)) MH2) MH2'.
clear MH1.
clear MH2.
put (MH1' _ _ (ReflexivityEq f) (ReflexivityEq f1)) MH1.
put (MH2' _ _ (ReflexivityEq f) (ReflexivityEq f2)) MH2.
clear MH1'.
clear MH2'.
apply MapEquality.
apply ReflexivityEq.
intros sa1 sa2 Eqsa.
assert(Eqsa1 : (sa1{<SubA}) == sa1).
 apply ReflexivityEq.
rewrite <- (MH1 _ _ (Eqsa1)).
rewrite (MH2 _ _ Eqsa1).
apply MapArgEq.
apply Eqsa.
Qed.

Definition RistMap {A B SA SB} := _{<Rel_Map ! (@RistMapRelMapCond A B SA SB)}.

(*
Check RistMap.

Theorem StrongRistMap : forall A B SA SB (f : #(RistableMap A B SA SB)),
StrongRel ((%RistMap f){<Map_Rel}) (f{<RistableMap_Map}{<Map_Rel}).
Proof.
intros A B SA SB f.
apply ToStrongRel.
intros sa sb RiH.
assert(SubA : Subset SA A).
 apply (RistableMapTheoremSubA A B SA SB).
 exists f.
 apply SetProp.
assert(SubB : Subset SB B).
 apply (RistableMapTheoremSubB A B SA SB).
 exists f.
 apply SetProp.
exists (sa{<SubA}).
exists (sb{<SubB}).
split.
apply ReflexivityEq.
split.
apply ReflexivityEq.
assert(AppT : &&(RistMap{<Map_Rel}) f (%RistMap f)).
 apply AppTheorem. 
put ((proj1 (MakeRelationTheorem _ _ _ _ _)) AppT) AppT'.
clear AppT.
assert(Eqsa : (sa{<SubA}) == sa).
 apply ReflexivityEq.
put (AppT' _ _ (ReflexivityEq f) (ReflexivityEq _) (sa{<SubA}) sa Eqsa) AppT.
clear AppT'.
clear Eqsa.
apply AppTheoremReverse in RiH.
cut (&&(f{<RistableMap_Map}{<Map_Rel}) (sa{<SubA}) (%(f{<RistableMap_Map}) (sa{<SubA}))).
 apply RelRewriteR.
 apply (TransitivityEq sb).
 rewrite <- RiH.
 rewrite <- AppT.
 apply ReflexivityEq.
 apply ReflexivityEq.
apply AppTheorem.
Qed.

Theorem StrongRistMap2 : forall A B SA SB (f : #(Map A B)) (cond : In f (RistableMap A B SA SB)),
StrongRel ((%RistMap {f ! cond}){<Map_Rel}) (f{<Map_Rel}).
Proof.
intros A B SA SB f cond.
apply (TransitivityStrongRel ({f ! cond}{<RistableMap_Map}{<Map_Rel})).
 apply (StrongRistMap).
apply ReflexivityStrongRel2.
hyperreflexivity.
Qed.
Print StrongMap.
Check @StrongMap.
Check @MapStrong.
*)

Theorem StrongRistMapEq : forall A B SA SB (f : #(RistableMap A B SA SB)) (g : #(Map A B)),
f == g -> StrongMap (%RistMap f) g.
Proof.
intros A B SA SB f g Eqfg.
unfold StrongMap.
apply ToStrongRel.
intros sa sb relH.
assert(subA : Subset SA A).
 apply (RistableMapTheoremSubA A B SA SB).
 exists f.
 apply SetProp.
assert(subB : Subset SB B).
 apply (RistableMapTheoremSubB A B SA SB).
 exists f.
 apply SetProp.
exists (sa{<subA}).
exists (sb{<subB}).
split.
 hyperreflexivity.
split.
 hyperreflexivity.
assert(AppT : &&(RistMap{<Map_Rel}) f (%RistMap f)).
 apply AppTheorem. 
put ((proj1 (MakeRelationTheorem _ _ _ _ _)) AppT) AppT'.
assert(Eqa : (sa{<subA}) == sa).
 hyperreflexivity.
clear AppT.
put (AppT' _ _ (ReflexivityEq f) (ReflexivityEq _) _ _ Eqa) AppT.
clear AppT'.
apply AppTheoremReverse in relH.
rewrite relH in AppT.
rewrite (USETEq' _ subB) in AppT.
apply (RelRewriteR AppT).
rewrite (USETEq' _ Map_Rel) in Eqfg.
rewrite (USETEq' _ RistableMap_Map) in Eqfg.
rewrite (USETEq' _ Map_Rel) in Eqfg.
apply (RelRewrite Eqfg).
set (f{<RistableMap_Map}) as rr.
apply AppTheorem.
Qed.

(*
Theorem RistMapEq2 : forall {A B SA SB} (f : #(Map A B)) (cond : In f (RistableMap A B SA SB)) (sa : #SA) (a : #A),
sa == a -> %(%RistMap {f ! cond}) sa == %f a.
Proof.
intros A B SA SB f cond sa a Eqa.
rewrite (MapStrong (StrongRistMap2 _ _ _ _ f cond) Eqa).
hyperreflexivity.
Qed.

Theorem RistMapEq2Subp : forall {A B SA SB} (f : #(Map A B)) (cond : In f (RistableMap A B SA SB)) (a : #SA) (sub : Subset SA A),
%(%RistMap {f ! cond}) a == %f (a{<sub}).
Proof.
intros A B SA SB f cond a sub.
apply MapStrongEq.
apply StrongRistMap2.
Qed.
*)

(*Expand Relation*)
Definition ExpandRelationL {A B X} (sub : Subset A X) : #(Map (Relation A B) (Relation X B)).
assert (RF : RFun (fun (r : #(Relation A B)) => r{<SubsetInRelationL _ _ B sub})).
 proofRFun.
apply (MakeMap _ _ _ RF).
Defined.

Definition ExpandRelationR {A B X} (sub : Subset B X) : #(Map (Relation A B) (Relation A X)).
assert (RF : RFun (fun (r : #(Relation A B)) => r{<SubsetInRelationR A _ _ sub})).
 proofRFun.
apply (MakeMap _ _ _ RF).
Defined.

Theorem ExpandRelationLEq : forall {A B X} (sub : Subset A X) (rel : #(Relation A B)),
%(ExpandRelationL sub)rel == rel.
Proof.
intros A B X sub rel.
unfold ExpandRelationL.
rewrite (MakeMapTheorem).
hyperreflexivity.
Qed.

Theorem ExpandRelationREq : forall {A B X} (sub : Subset B X) (rel : #(Relation A B)),
%(ExpandRelationR sub)rel == rel.
Proof.
intros A B X sub rel.
unfold ExpandRelationR.
rewrite (MakeMapTheorem).
hyperreflexivity.
Qed.



(* Curry *)
Theorem CurryingMapCond A B C : Rel_MapCond (MakeRelation (fun (f1 : #(Map (Cartesian A B) C)) (f2 : #(Map A (Map B C))) => forall a b, %f1 [a;b] == %(%f2 a) b)).
Proof.
intro f1.
split.

set (MakeRelation (fun (a : #A) (f3 : #(Map B C)) => forall b, %f1 [a;b] == %f3 b)) as f2.
assert(MRCond : Rel_MapCond f2).
 intro a.
 split.
  set (MakeRelation (fun (b : #B) (c : #C) => %f1 [a;b] == c)) as f3.
  assert(MRCond2 : Rel_MapCond f3).
   intro b.
   split.
    exists (%f1 [a;b]).
    apply MakeRelationTheorem.
    intros b' fab Eqb Eqf.
    rewrite <- Eqf.
    apply MapArgEq.
    apply EqualInPair'.
    split.
    apply ReflexivityEq.
    apply SymmetryEq.
    apply Eqb.

    intros c1 c2 fD.
    destruct fD as [fH1 fH2].
    put ((proj1 (MakeRelationTheorem _ _ _ _ _)) fH1) fH1'.
    put ((proj1 (MakeRelationTheorem _ _ _ _ _)) fH2) fH2'.
    clear fH1.
    clear fH2.
    put (fH1' _ _ (ReflexivityEq b) (ReflexivityEq c1)) fH1.
    put (fH2' _ _ (ReflexivityEq b) (ReflexivityEq c2)) fH2.
    clear fH1'.
    clear fH2'.
    rewrite <- fH1.
    rewrite <- fH2.
    apply ReflexivityEq.

  exists (f3{<Rel_Map ! MRCond2}).
  apply MakeRelationTheorem.
  intros a' f3' Eqa Eqf3 b.
  apply SymmetryEq.
  apply AppTheoremReverse.
  cut (&&(f3) b (%f1 [a'; b])).
   apply RelRewrite.
   apply (TransitivityEq (f3')).
   rewrite <- Eqf3.
   apply ReflexivityEq.
   apply ReflexivityEq.
  apply MakeRelationTheorem.
  intros b' c' Eqb Eqc.
  rewrite <- Eqc.
  apply MapArgEq.
  apply EqualInPair'.
  split.
  apply Eqa.
  apply SymmetryEq.
  apply Eqb.

 intros f2a f2b fH.
 destruct fH as [fH1 fH2].
 apply MapEquality.
 apply ReflexivityEq.
 intros b1 b2 Eqb.
 put ((proj1 (MakeRelationTheorem _ _ _ _ _)) fH1) fH1'.
 put ((proj1 (MakeRelationTheorem _ _ _ _ _)) fH2) fH2'.
 clear fH1.
 clear fH2.
 put (fH1' _ _ (ReflexivityEq a) (ReflexivityEq f2a)) fH1.
 put (fH2' _ _ (ReflexivityEq a) (ReflexivityEq f2b)) fH2.
 clear fH1'.
 clear fH2'.
 rewrite <- fH1.
 rewrite fH2.
 apply MapArgEq.
 apply Eqb.
exists (f2{<Rel_Map ! MRCond}).
apply MakeRelationTheorem.
intros f1' f2' Eqf1 Eqf2 a b.
apply SymmetryEq.
apply AppTheoremReverse.
assert(f2App : &&f2 a (%f2' a)).
 cut (&&(f2'{<Map_Rel}) a ((%f2' a))).
  apply RelRewrite.
  apply (TransitivityEq f2').
  apply ReflexivityEq.
  rewrite <- Eqf2.
  apply ReflexivityEq.
 apply AppTheorem.
put ((proj1 (MakeRelationTheorem _ _ _ _ _)) f2App) f2App'.
clear f2App.
put (f2App' _ _ (ReflexivityEq a) (ReflexivityEq _)) f2App.
clear f2App'.
cut ((&& ((%f2') a){<Map_Rel}) b (%(%f2' a) b)).
 apply RelRewriteR.
 rewrite <- f2App.
 apply MapEq.
 apply Eqf1.
apply AppTheorem.


intros F1 F2 FD.
destruct FD as [FH1 FH2].
put ((proj1 (MakeRelationTheorem _ _ _ _ _)) FH1) FH1'.
put ((proj1 (MakeRelationTheorem _ _ _ _ _)) FH2) FH2'.
clear FH1.
clear FH2.
put (FH1' _ _ (ReflexivityEq f1) (ReflexivityEq F1)) FH1.
put (FH2' _ _ (ReflexivityEq f1) (ReflexivityEq F2)) FH2.
clear FH1'.
clear FH2'.
apply MapEquality.
apply ReflexivityEq.
intros a1 a2 Eqa.
apply MapEquality.
apply ReflexivityEq.
intros b1 b2 Eqb.
apply (TransitivityEq (%f1 [a1;b1])).
 apply SymmetryEq.
 apply FH1.
apply (TransitivityEq (%f1 [a2;b2])).
 apply MapArgEq.
 apply EqualInPair'.
 split; assumption.
apply FH2.
Qed.

Definition Currying {A B C} := _ {<Rel_Map ! CurryingMapCond A B C}.

Theorem CurryingTheorem : forall {A B C} (f : #(Map (Cartesian A B) C)),
forall a b,
%(%(%Currying f) a) b == %f [a;b].
Proof.
intros A B C f a b.
assert(AppT : &&(Currying{<Map_Rel}) f (%Currying f)).
 apply AppTheorem.
put ((proj1 (MakeRelationTheorem _ _ _ _ _)) AppT) AppT'.
clear AppT.
put (AppT' _ _ (ReflexivityEq f) (ReflexivityEq _)) AppT.
clear AppT'.
apply SymmetryEq.
apply AppT.
Qed.

(* True False Relation *)
Definition TrueRel {A B} : #(Relation A B) :=
{Cartesian A B ! PowersetHasOwn _}.

Theorem TrueRelTheorem : forall {A B} (a : #A) (b : #B),
&&TrueRel a b.
Proof.
intros A B a b.
unfold If.
unfold TrueRel.
rewrite (DSETEq _ _).
apply CartesianTheorem.
split; apply SetProp.
Qed.

Definition FalseRel {A B} : #(Relation A B) :=
{Empty ! PowersetHasEmpty _}.

Theorem FalseRelTheorem : forall {A B} (a : #A) (b : #B),
~&&FalseRel a b.
Proof.
intros A B a b FR.
unfold If in FR.
unfold FalseRel in FR.
rewrite (DSETEq _ _) in FR.
apply EmptyTheorem in FR.
apply FR.
Qed.

Theorem StrongTrueRel : forall {A B} (rel : #(Relation A B)),
StrongRel rel (@TrueRel A B).
Proof.
intros A B rel.
unfold StrongRel.
intros p Inprel.
put (IsPair'Relation _ _ _ _ Inprel) Eqp.
destruct Eqp as [a Eqp].
destruct Eqp as [b Eqp].
rewrite Eqp.
apply SetProp.
Qed.

Theorem StrongFalseRel : forall {A B} (rel : #(Relation A B)),
StrongRel (@FalseRel A B) rel.
Proof.
intros A B rel.
apply AllSetHasEmpty.
Qed.


(* Set WellFoundedical *)
Definition InRelation A B := MakeRelation (fun (a : #A) (b : #B) => In a b).


Theorem InRelationTheorem : forall A B x y,
&&(InRelation A B) x y <-> In x y.
Proof.
intros A B x y.
split.
 intro Rxy.
 generalize ((proj1 (MakeRelationTheorem _ _ _ _ _)) Rxy); intro Rxy'.
 apply (Rxy' x y).
 apply ReflexivityEq.
 apply ReflexivityEq.

 intro Inxy.
 apply MakeRelationTheorem.
 intros x' y' Eqx Eqy.
 rewrite <- Eqx.
 rewrite <- Eqy.
 assumption.
Qed.

Theorem InRelationWCond : forall A, Rel_WRelCond (InRelation A A).
Proof.
unfold Rel_WRelCond.
intros A X sub HInd.
apply EA.
apply (SetInductionAxiom).
intros a HInda.
split.
 intro InaX.
 apply sub.
 assumption.

 intro InaA.
 apply (HInd {a ! InaA}).
 intros b Inba'.
 assert(Inba : In b a).
  apply InRelationTheorem in Inba'.
  apply Inba'.
 apply (HInda _ Inba).
 apply SetProp.
Qed.

Definition InRelationW A := (InRelation A A){<Rel_WRel ! InRelationWCond A}.

(* Eq Relation *)
(*
Definition EqRelation {A B} : #(Relation A B) := MakeRelation (fun a b => a == b).

Theorem EqRelationTheorem : forall {A B} (a : #A) (b : #B),
&&EqRelation a b <-> a == b.
Proof.
intros A B a b.
split.
 intro ER.
 put ((proj1 (MakeRelationTheorem _ _ _ _ _)) ER) ER'.
 apply ER'; hyperreflexivity.

 intro Eqab.
 apply MakeRelationTheorem.
 intros a' b' Eqa Eqb.
 rewrite <- Eqa.
 rewrite <- Eqb.
 apply Eqab.
Qed.

Theorem EqRelation_Rel_RefCond : forall {A},
Rel_RefCond (@EqRelation A A).
Proof.
intros A.
intro a.
apply EqRelationTheorem.
hyperreflexivity.
Qed.

Theorem EqRelation_Rel_SymCond : forall {A},
Rel_SymCond (@EqRelation A A).
Proof.
intros A.
intros a b EH.
apply EqRelationTheorem.
apply EqRelationTheorem in EH.
apply SymmetryEq.
apply EH.
Qed.

Theorem EqRelation_Rel_TransCond : forall {A},
Rel_TransCond (@EqRelation A A).
Proof.
intros A.
intros a b c RH1 RH2.
apply EqRelationTheorem.
apply EqRelationTheorem in RH1.
apply EqRelationTheorem in RH2.
rewrite RH1.
rewrite RH2.
hyperreflexivity.
Qed.
*)

(* Subset Relation *)
Definition SubsetRelation A B := MakeRelation (fun (a : #A) (b : #B) => Subset a b).


Theorem SubsetRelationTheorem : forall A B x y,
&&(SubsetRelation A B) x y <-> Subset x y.
Proof.
intros A B x y.
split.
 intro SR.
 put ((proj1 (MakeRelationTheorem _ _ _ _ _)) SR) SR'.
 apply SR'; hyperreflexivity.

 intros SS.
 apply MakeRelationTheorem.
 intros x' y' Eqx Eqy.
 rewrite <- Eqx.
 rewrite <- Eqy.
 apply SS.
Qed.


(* Equal Relation *)
Definition EqRelaion {A B} := MakeRelation (fun (a : #A) (b : #B) => a == b).


(* FunMap *)
Definition FunMapCond A B f := forall a, In a A -> In (f a) B.

Theorem FunMapRMapCond {A B} (f : SET -> SET) (prf : FunMapCond A B f) :
Rel_MapCond (MakeRelation (fun (a : #A) (b : #B) => f a == b)).
Proof.
intros a.
split.

exists {_!(prf _ (SetProp a))}.
apply MakeRelationTheorem.
intros a' b' Eqa Eqb.
rewrite <- Eqa.
apply Eqb.

intros b1 b2 fD.
destruct fD as [fH1 fH2].
put ((proj1 (MakeRelationTheorem _ _ _ _ _)) fH1) fH1'.
put ((proj1 (MakeRelationTheorem _ _ _ _ _)) fH2) fH2'.
clear fH1.
clear fH2.
put (fH1' _ _ (ReflexivityEq a) (ReflexivityEq b1)) fH1.
put (fH2' _ _ (ReflexivityEq a) (ReflexivityEq b2)) fH2.
clear fH1'.
clear fH2'.
rewrite <- fH1.
rewrite <- fH2.
apply ReflexivityEq.
Qed.

Definition FunMap {A B} (f : SET -> SET) (prf : FunMapCond A B f) := 
_{<Rel_Map ! (FunMapRMapCond f prf)}.

Theorem FunMapTheorem {A B} : forall f (prf : FunMapCond A B f),
forall a,
%(FunMap f prf) a == f a.
Proof.
intros f prf a.
assert(AppT : &&((FunMap f prf){<Map_Rel}) a (%(FunMap f prf) a)).
 apply AppTheorem.
put ((proj1 (MakeRelationTheorem _ _ _ _ _)) AppT) AppT'.
clear AppT.
put (AppT' _ _ (ReflexivityEq a) (ReflexivityEq _)) AppT.
clear AppT'.
apply SymmetryEq.
apply AppT.
Qed.

Definition Fun2MapCond A B X (f : SET -> SET -> SET) :=
forall a b, In a A -> In b B -> In (f a b) X.


Theorem Fun2MapRMapCond {A B X} (f : SET -> SET -> SET) (prf : Fun2MapCond A B X f) :
Rel_MapCond (MakeRelation (fun (p : #(Cartesian A B)) (x : #X) => f (%MLeft p) (%MRight p) == x)).
Proof.
intros p.
assert(IsPp : IsPair p).
 apply (CartesianIsPair _ _ _ (SetProp p)).
destruct IsPp as [a IsPp].
destruct IsPp as [b IsPp].
assert(InD : In a A /\ In b B).
 apply CartesianTheorem.
 rewrite <- IsPp.
 apply (SetProp p).
destruct InD as [InaA InbB].
split.

assert(InfX : In (f a b) X).
 apply prf.
 assumption.
 assumption. 
exists {_!InfX}.
apply MakeRelationTheorem.
intros a' b' Eqa Eqb.
rewrite <- Eqb.
apply (TransitivityEq (f a b)).
apply FunRewrite2.
 apply (TransitivityEq (%MLeft [{a!InaA};{b!InbB}])).
 apply MapArgEq.
 rewrite <- Eqa.
 rewrite IsPp.
 hyperreflexivity.
 apply LeftPairTheorem.

 apply (TransitivityEq (%MRight [{a!InaA};{b!InbB}])).
 apply MapArgEq.
 rewrite <- Eqa.
 rewrite IsPp.
 hyperreflexivity.
 apply RightPairTheorem.
hyperreflexivity.

intros x1 x2 MD.
destruct MD as [MH1 MH2].
put ((proj1 (MakeRelationTheorem _ _ _ _ _)) MH1) MH1'.
put ((proj1 (MakeRelationTheorem _ _ _ _ _)) MH2) MH2'.
clear MH1.
clear MH2.
put (MH1' _ _ (ReflexivityEq p) (ReflexivityEq x1)) MH1.
put (MH2' _ _ (ReflexivityEq p) (ReflexivityEq x2)) MH2.
clear MH1'.
clear MH2'.
rewrite <- MH1.
rewrite <- MH2.
hyperreflexivity.
Qed.

Definition Fun2Map {A B X} (f : SET -> SET -> SET) (prf : Fun2MapCond A B X f) := 
_{<Rel_Map ! (Fun2MapRMapCond f prf)}.

Theorem Fun2MapTheorem {A B X} : forall f (prf : Fun2MapCond A B X f),
forall p, %(Fun2Map f prf) p == f (%MLeft p) (%MRight p).
Proof.
intros f prf p.
assert(AppT : &&((Fun2Map f prf){<Map_Rel}) p (%(Fun2Map f prf) p)).
 apply AppTheorem.
put ((proj1 (MakeRelationTheorem _ _ _ _ _)) AppT) AppT'.
clear AppT.
put (AppT' _ _ (ReflexivityEq p) (ReflexivityEq _)) AppT.
clear AppT'.
apply SymmetryEq.
apply AppT.
Qed.

Theorem Fun2MapTheoremP {A B X} : forall f (prf : Fun2MapCond A B X f),
forall a b,
%(Fun2Map f prf) [a;b] == f a b.
Proof.
intros f prf a b.
rewrite Fun2MapTheorem.
apply FunRewrite2.
apply LeftPairTheorem.
apply RightPairTheorem.
Qed.


(* MCartesian *)
Definition MCartesian {A B} : #(Map (Cartesian (PowerSet A) (PowerSet B)) (PowerSet (Cartesian A B))).
assert(Cond : Fun2MapCond (PowerSet A) (PowerSet B) (PowerSet (Cartesian A B)) Cartesian).
 intros SA SB InSAP InSBP.
 apply PowersetTheorem in InSAP.
 apply PowersetTheorem in InSBP.
 apply PowersetTheorem.
 apply SubsetInCartesian.
 assumption.
 assumption.
apply (Fun2Map Cartesian Cond).
Defined.

Theorem MCartesianEq : forall {A B} (SA : #(PowerSet A)) (SB : #(PowerSet B)),
(%MCartesian [SA;SB]) == (Cartesian SA SB).
Proof.
intros A B SA SB.
unfold MCartesian.
rewrite (Fun2MapTheoremP _ _ _ _).
hyperreflexivity.
Qed.

(* Classification *)
Definition Classifications A :=
SSet (PowerSet (PowerSet A)) (fun X => (forall S, In S X -> NonEmpty S) /\ (Unions X) == A /\ forall a b, In a X -> In b X -> NonEmpty (Section a b) -> a == b).

Theorem ClassificationTheorem : forall A A', 
((forall S, In S A' -> NonEmpty S) /\ (Unions A') == A /\ forall a b, In a A' -> In b A' -> NonEmpty (Section a b) -> a == b) -> In A' (Classifications A).
Proof.
intros A A' Cond.
apply SSetTheorem.
split.
 destruct Cond as [Cond1 Cond].
 destruct Cond as [Cond2 Cond3].
 apply PowersetTheorem.
 intros a InaA'.
 apply PowersetTheorem.
 rewrite <- Cond2.
 intros b Inba.
 apply UnionsTheorem.
 exists a.
 split; assumption.
apply Cond.
Qed.

Theorem ClassificationTheorem1 : forall A A', In A' (Classifications A) -> (Unions A') == A.
Proof.
intros A A' InA'C.
apply SSetTheorem in InA'C.
destruct InA'C as [InA'P InA'C].
destruct InA'C as [NE InA'C].
destruct InA'C as [EqUA InA'C].
assumption.
Qed.

Theorem ClassificationTheorem2 : forall A A' a b, In A' (Classifications A) ->
In a A' -> In b A' -> NonEmpty (Section a b) -> a == b.
Proof.
intros A A' a b InA'C InaA1 InaA2.
apply SSetTheorem in InA'C.
destruct InA'C as [InA'P InA'C].
destruct InA'C as [NE InA'C].
destruct InA'C as [EqUA InA'C].
apply InA'C.
assumption.
assumption.
Qed.

Theorem ClassificationTheorem3 : forall A A', In A' (Classifications A) ->
  forall S, In S A' -> NonEmpty S.
Proof.
intros A A' InA'C.
apply SSetTheorem in InA'C.
destruct InA'C as [InA'P InA'C].
destruct InA'C as [NE InA'C].
apply NE.
Qed.

Theorem ClassificationIn : forall A C S a, In C (Classifications A) ->
   In S C -> In a S -> In a A.
Proof.
intros A C S a CA InSA' InaS.
assert(EqU : Unions C == A).
 apply ClassificationTheorem1.
 apply CA.
rewrite <- EqU.
apply UnionsTheorem.
exists S.
split.
apply InSA'.
apply InaS.
Qed.
 
Theorem ClassificationTheorem3' : forall A A', In A' (Classifications A) ->
  ~In Empty A'.
Proof.
intros A A' InA'C InE.
put (ClassificationTheorem3 _ _ InA'C _ InE) NES.
destruct NES as [E NES].
apply EmptyTheorem in NES.
contradiction.
Qed.


 
Theorem ClassificationElementIn : forall A (C : #(Classifications A)) (a : #A),
exists S : #C, In a S.
Proof.
intros A C a.
assert(InCU : In a (Unions C)).
 assert(EqU : Unions C == A).
  apply ClassificationTheorem1.
  apply SetProp.
 rewrite EqU.
 apply SetProp.
apply UnionsTheorem in InCU.
destruct InCU as [S InCU].
destruct InCU as [InSC InaS].
exists {S ! InSC}.
apply InaS.
Qed.


Theorem ClassificationElementEq : forall A C, In C (Classifications A) ->
forall a S1 S2, In S1 C -> In S2 C -> 
In a S1 -> In a S2 -> S1 == S2.
Proof.
intros A C InCS a S1 S2 InS1 InS2 Ina1 Ina2.
put (ClassificationTheorem2 _ _ _ _ InCS InS1 InS2) CT2.
apply CT2.
exists a.
apply SectionTheorem.
split; assumption.
Qed.

Theorem ClassificationSubset : forall {A} (C : #(Classifications A)) S,
In S C -> Subset S A.
Proof.
intros A C S InSC a InaS.
apply (ClassificationIn _ _ _ _ (SetProp C) InSC InaS).
Qed.

Theorem ClassificationPPSubset : forall A, Subset (Classifications A) (PowerSet (PowerSet A)).
Proof.
intros A.
apply SSetSubset.
Qed.

Theorem ClassificationPSubset : forall A (C : #(Classifications A)), Subset C (PowerSet A).
Proof.
intros A C S InSC.
apply PowersetTheorem.
intros a InaS.
apply (ClassificationIn _ _ _ _ (SetProp C) InSC InaS).
Qed.

Theorem EqCannProjMapCond A (C : #(Classifications A)) : Rel_MapCond (MakeRelation
  (fun (a : #A) (S : #C) => In a S)
).
Proof.
intro a.
split.

 put (ClassificationElementIn A C a) CI.
 destruct CI as [S CI].
 exists S.
 apply MakeRelationTheorem.
 intros a' S' Eqa EqS.
 rewrite <- Eqa.
 rewrite <- EqS.
 apply CI. 

 intros S1 S2 HD.
 destruct HD as [H1 H2].
 put ((proj1 (MakeRelationTheorem _ _ _ _ _)) H1) H1'.
 put ((proj1 (MakeRelationTheorem _ _ _ _ _)) H2) H2'.
 clear H1.
 clear H2.
 put (H1' _ _ (ReflexivityEq a) (ReflexivityEq S1)) H1.
 put (H2' _ _ (ReflexivityEq a) (ReflexivityEq S2)) H2.
 clear H1'.
 clear H2'.
 put (ClassificationTheorem2 _ _ _ _ (SetProp C) (SetProp S1) (SetProp S2)) CT2.
 apply CT2.
 exists a.
 apply SectionTheorem.
 split; assumption.
Qed.


Definition EqCannProj {A} (C : #(Classifications A)) : #(Map A C) :=
_{<Rel_Map ! EqCannProjMapCond A C}.



Theorem EqCannProjOwnIn : forall {A} (C : #(Classifications A)),
forall (a : #A),
In a (%(EqCannProj C) a).
Proof.
intros A C a.
assert(AppT : &&((@EqCannProj A C){<Map_Rel}) a (%(EqCannProj C) a)).
 apply AppTheorem.
put ((proj1 (MakeRelationTheorem _ _ _ _ _)) AppT) AppT'.
clear AppT.
put (AppT' _ _ (ReflexivityEq a) (ReflexivityEq _)) AppT.
clear AppT'.
apply AppT.
Qed.

Theorem EqCannProjInA : forall {A} (C : #(Classifications A)) (a : #A) (b : SET),
In b (%(EqCannProj C) a) -> In b A.
intros A C a b InbE.
assert(EqCIn : In (%(EqCannProj C) a) C).
 apply MapIn.
apply (ClassificationIn _ _ _ _ (SetProp C) EqCIn).
apply InbE.
Qed.

Theorem EqCannProjIn : forall {A} (C : #(Classifications A)) S,
In S C <-> exists a : #A, (%(EqCannProj C) a) == S.
Proof.
intros A C S.
split.
 intro InSC.
 put InSC InSC'.
 apply (ClassificationTheorem3 _ _ (SetProp C)) in InSC'.
 destruct InSC' as [a' InaS].
 assert(InaA : In a' A).
  apply (ClassificationIn _ _ _ _ (SetProp C) InSC InaS).
 set {a' ! InaA} as a.
 exists a.
 apply (ClassificationTheorem2 _ _ _ _ (SetProp C)).
 apply MapIn.
 assumption.
 exists a.
 apply SectionTheorem.
 split.
 apply EqCannProjOwnIn.
 apply InaS.

 intros Cond.
 destruct Cond as [a EqES].
 rewrite <- EqES.
 apply MapIn.
Qed.

(*
Theorem ClassificationInC : forall {A} (C : #(Classifications A)) a,
In a C <-> (exists S, In a S /\ In S C).
Proof.
intros A C a.
split.
 intro InaC.
 assert(InaA : In a A).
 
 put (ClassificationTheorem1 _ _ (SetProp C)) UEq.
 assert(
 
Check @ClassificationIn.
intros A C a.
*)

Theorem RewriteEqCannProj : forall {A} (C1 C2 : #(Classifications A)),
C1 == C2 -> EqCannProj C1 == EqCannProj C2.
Proof.
intros A C1 C2 EqC.

apply MapEquality.
hyperreflexivity.
intros a1 a2 Eqa.
apply (ClassificationTheorem2 _ _ _ _ (SetProp C1)).
 apply MapIn.
 rewrite EqC.
 apply MapIn.
exists a1.
apply SectionTheorem.
split.
apply EqCannProjOwnIn.
rewrite Eqa.
apply EqCannProjOwnIn.
Qed.

Theorem Rewrite'EqCannProj : forall {A} (C1 C2 : #(Classifications A)),
C2 == C1 -> EqCannProj C1 == EqCannProj C2.
Proof.
intros A C1 C2 Eq.
apply RewriteEqCannProj.
apply SymmetryEq.
apply Eq.
Qed.

Theorem EqCannProjSurjection : forall A (C : #(Classifications A)), Map_SurCond (EqCannProj C).
Proof.
intros A C.
intros c.
assert (NEc : NonEmpty c).
 apply (ClassificationTheorem3 A C).
 apply SetProp.
 apply SetProp.
destruct NEc as [a cNEc].
assert(InaA : In a A).
 apply (ClassificationIn A C c a).
 apply SetProp.
 apply SetProp.
 assumption.
exists {a ! InaA}.
apply (ClassificationElementEq _ _ (SetProp C) a).
apply MapIn.
apply SetProp.
cut (In {a ! InaA} (%(@EqCannProj _ C) {a ! InaA})).
 intro; assumption.
apply EqCannProjOwnIn.
assumption.
Qed.

