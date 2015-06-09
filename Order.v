Require Import logic IZF Relation BaseMap Maps BOperation1.

Theorem Rel_RefCond_Inverse :
  forall A (rel : #(BRelation A)),
    Rel_RefCond rel -> Rel_RefCond (%InverseRel rel).
Proof.
  intros A rel cond a.
  generalize (cond a).
  apply (InverseRelTheorem rel).
Qed.

Theorem Rel_SymCond_Inverse :
  forall A (rel : #(BRelation A)),
    Rel_SymCond rel -> Rel_SymCond (%InverseRel rel).
Proof.
  intros A rel cond a b relab.
  cut (&&rel a b).
  {
    apply (InverseRelTheorem rel).
  }
  apply cond.
  generalize relab.
  apply (InverseRelTheorem rel).
Qed.

Theorem Rel_ASymCond_Inverse :
  forall A (rel : #(BRelation A)),
    Rel_ASymCond rel -> Rel_ASymCond (%InverseRel rel).
Proof.
  intros A rel cond a b  relab relba.
  apply cond.
  {
    generalize relba.
    apply (InverseRelTheorem rel).
  } {
    generalize relab.
    apply (InverseRelTheorem rel).
  }
Qed.

Theorem Rel_TransCond_Inverse :
  forall A (rel : #(BRelation A)),
    Rel_TransCond rel -> Rel_TransCond (%InverseRel rel).
Proof.
  intros A rel cond a b c Rab Rbc.
  cut (&&rel c a).
  {
    apply (InverseRelTheorem rel).
  }
  apply (cond c b a).
  {
    generalize Rbc.
    apply (InverseRelTheorem rel).
  } {
    generalize Rab.
    apply (InverseRelTheorem rel).
  }
Qed.

Theorem Rel_PosetCond_Inverse :
  forall A (rel : #(BRelation A)),
    Rel_PosetCond rel -> Rel_PosetCond (%InverseRel rel).
Proof.
  intros A rel cond.
  split.
  apply Rel_RefCond_Inverse.
  apply cond.
  apply Rel_TransCond_Inverse.
  apply cond.
Qed.

Theorem Rel_ORelCond_Inverse :
  forall A (rel : #(BRelation A)),
    Rel_ORelCond rel -> Rel_ORelCond (%InverseRel rel).
Proof.
  intros A rel cond.
  split.
  apply Rel_PosetCond_Inverse.
  apply cond.
  apply Rel_ASymCond_Inverse.
  apply cond.
Qed.

Theorem InverseRel_RistMapORel :
  forall A,
    In (@InverseRel A A) (RistableMap (BRelation A) (BRelation A) (ORelation A) (ORelation A)).
Proof.
  intros A.
  apply RistableMapTheorem.
  split.
  {
    split; apply ORel_Rel.
  }
  intros rel InrelO.
  apply Rel_ORel.
  apply Rel_ORelCond_Inverse.
  apply Rel_ORel.
  apply InrelO.
Qed.


Definition InverseORel {A} :=
  %RistMap {_ ! InverseRel_RistMapORel A}.

Theorem InverseORelTheorem : forall {A} (rel : #(ORelation A)),
forall a b,
&&(rel{<ORel_Rel}) a b <-> &&((%InverseORel rel){<ORel_Rel}) b a.
Proof.
  intros A rel.
  assert(EqH : %InverseORel rel == %InverseRel (rel{<ORel_Rel})).
  {
    unfold InverseORel.
    apply (RistMapEq _ _ rel (rel{<ORel_Rel})).
    hyperreflexivity.
  }
  intros a b.
  split.
  {
    intro relab.
    cut (&&(%InverseRel (rel{<ORel_Rel})) b a).
    {
      apply RelRewrite.
      apply (SymmetryEq _ _ EqH).
    }
    generalize relab.
    apply (InverseRelTheorem (rel{<ORel_Rel})).
  }
  {
    intro InverseRelH.
    cut (&& (%InverseRel (rel{<ORel_Rel})) b a).
    {
      apply InverseRelTheorem.
    }
    generalize InverseRelH.
    apply RelRewrite.
    apply EqH.
  }
Qed.



(* Sup Inf *)


Theorem Upper_RFun {A} :
  RFun (fun (arg : #(Cartesian (ORelation A) (PowerSet A))) => SSet'P A (fun (a : #A) => forall (s : #A), In s (%MRight arg) -> &&((%MLeft arg){<ORel_Rel}) s a)).
Proof.
  intros c1 c2 Eqrel.
  apply EqualInSSet'Set.
  hyperreflexivity.
  intros a1 a2 EqH.
  split; intros HH.
  {
    intros s InsS.
    cut (&&(%MLeft c1){<ORel_Rel} s a1).
    {
      apply RelRewriteAll.
      reflexivity.
      exact EqH.
      apply MapArgEq.
      exact Eqrel.
    }
    apply HH.
    rewrite (MapArgEq _ Eqrel).
    exact InsS.
  } {
    intros s InsS.
    cut (&&(%MLeft c2){<ORel_Rel} s a2).
    {
      apply RelRewriteAll.
      reflexivity.
      exact (SymmetryEq _ _ EqH).
      apply MapArgEq.
      exact (SymmetryEq _ _ Eqrel).
    }
    apply HH.
    rewrite (MapArgEq' _ Eqrel).
    exact InsS.
  }
Qed.

Definition Upper {A} := %Currying (MakeMap _ _ _ (@Upper_RFun A)).
Definition Lower {A} := %CombineMap [@Upper A ; InverseORel]. 

Theorem UpperTheorem1 :
  forall {A} (rel : #(ORelation A)) (S : #(PowerSet A)) (m : #A),
    In m (%(%Upper rel) S) -> (forall (a : #A), In a S -> &&(rel{<ORel_Rel}) a m).
Proof.
  intros A rel S m InmU a InaS.
  unfold Upper in InmU.
  rewrite CurryingTheorem in InmU.
  rewrite MakeMapTheorem in InmU.
  unfold SSet'P in InmU.
  rewrite DSETEq in InmU.
  apply SSet'Theorem in InmU.
  destruct InmU as [InmA cond].
  cut (&& ((%MLeft [rel ; S]){<ORel_Rel}) a {m ! (SetProp m)}).
  {
    apply RelRewriteAll.
    hyperreflexivity.
    hyperreflexivity.
    apply (LeftPairTheorem rel S).
  }
  apply cond.
  rewrite (RightPairTheorem).
  exact InaS.
Qed.

Theorem UpperTheorem2 :
  forall {A} (rel : #(ORelation A)) (S : #(PowerSet A)) (m : #A),
    (forall (a : #A), In a S -> &&(rel{<ORel_Rel}) a m) -> In m (%(%Upper rel) S).
Proof.
  intros A rel S m cond.
  unfold Upper.
  rewrite CurryingTheorem.
  rewrite MakeMapTheorem.
  unfold SSet'P.
  apply SSet'Theorem.
  split.
  exact (SetProp m).
  intros InmA a InaS.
  cut (&&(rel{<ORel_Rel}) a {m ! InmA}).
  {
    apply RelRewrite.
    apply SymmetryEq.
    apply (LeftPairTheorem rel S).
  }
  apply cond.
  rewrite RightPairTheorem in InaS.
  exact InaS.
Qed.






(* Max Min *)
Theorem RFun_Max {A} :
  RFun (fun (rel : #(ORelation A)) => 
          MakeRelation (fun (S : #(PowerSet A)) (a : #A) => In a (Section S (%(%Upper rel) S)))
       ).
Proof.
intros rel1 rel2 Eqxy.
unfold MakeRelation.
rewrite DSETEq.
rewrite DSETEq.
unfold MakeRelationSet.
apply EqualInSSetSet.
reflexivity.
intros p InpC.
cut (forall a, %(%Upper rel1) a == %(%Upper rel2) a).
{
  intros HH.
  split; intros S a.
  {
    rewrite <- (HH a).
    auto.
  } {
    rewrite (HH a).
    auto.
  } 
}
intro S.
apply MapEq.
apply MapArgEq.
exact Eqxy.
Qed.

Definition Max {A} := (MakeMap _ _ _ (@RFun_Max A)).
Definition Min {A} := %CombineMap [@Max A ; InverseORel].

Theorem RFun_Sup {A} : 
  RFun (fun (rel : #(ORelation A)) => 
          MakeRelation
            (fun (S : #(PowerSet A)) (a : #A) => &&(%Min rel) (%(%Upper rel) S) a)
       ).
Proof.
intros rel1 rel2 Eqrel.
unfold MakeRelation.
rewrite DSETEq.
rewrite DSETEq.
unfold MakeRelationSet.
apply EqualInSSetSet.
reflexivity.
intros p InpC.
split; intros cond S a Eqp.
{
  generalize (cond _ _ Eqp).
  apply RelRewriteAll.
  apply MapEq.
  apply MapArgEq.
  exact Eqrel.
  reflexivity.
  apply MapArgEq.
  apply Eqrel.
} {
  apply SymmetryEq in Eqrel.
  generalize (cond _ _ Eqp).
  apply RelRewriteAll.
  apply MapEq.
  apply MapArgEq.
  exact Eqrel.
  reflexivity.
  apply MapArgEq.
  exact Eqrel.
}
Qed.

Definition Sup {A} := MakeMap _ _ _ (@RFun_Sup A).
Definition Inf {A} := %CombineMap [@Sup A ; InverseORel].

Theorem MaxTheorem1 :
  forall {A} (rel : #(ORelation A)),
  forall (S : #(PowerSet A)) (m : #A),
    &&(%Max rel) S m ->
    forall (a : #A), In a S -> &&(rel{<ORel_Rel}) a m.
Proof.
  intros A rel S m MaxH a InaS.
  unfold If in MaxH.
  unfold Max in MaxH.
  rewrite MakeMapTheorem in MaxH.
  put ((proj1 (MakeRelationTheorem _ _ _ _ _)) MaxH) MaxH'.
  clear MaxH.
  put (MaxH' _ _ (ReflexivityEq S) (ReflexivityEq m)) MaxH.
  clear MaxH'.
  apply SectionTheorem in MaxH.
  destruct MaxH as [InmS InmU].
  apply (UpperTheorem1 _ S).
  apply InmU.
  apply InaS.
Qed.    

Theorem MaxTheorem2 :
  forall {A} (rel : #(ORelation A)),
  forall (S : #(PowerSet A)) (m : #A),
    &&(%Max rel) S m -> In m S.
Proof.
  intros A rel S m MaxH.
  unfold If in MaxH.
  unfold Max in MaxH.
  rewrite MakeMapTheorem in MaxH.
  put ((proj1 (MakeRelationTheorem _ _ _ _ _)) MaxH) MaxH'.
  clear MaxH.
  put (MaxH' _ _ (ReflexivityEq S) (ReflexivityEq m)) MaxH.
  clear MaxH'.
  apply SectionTheorem in MaxH.
  apply (proj1 MaxH).
Qed.

Theorem MinTheorem1 :
  forall {A} (rel : #(ORelation A)),
  forall (S : #(PowerSet A)) (m : #A),
    &&(%Min rel) S m ->
    forall (a : #A), In a S -> &&(rel{<ORel_Rel}) m a.
Proof.
  intros A rel S m MinH a InaS.
  apply <- (InverseORelTheorem rel).
  apply (MaxTheorem1 _ S).
  {
    generalize MinH.
    apply RelRewrite.
    unfold Min.
    apply CombineMapTheorem.
  }
  apply InaS.
Qed.

Theorem MinTheorem2 :
  forall {A} (rel : #(ORelation A)),
  forall (S : #(PowerSet A)) (m : #A),
    &&(%Min rel) S m -> In m S.
Proof.
  intros A rel S m MinH.
  apply (MaxTheorem2 (%InverseORel rel)).
  generalize MinH.
  apply RelRewrite.
  unfold Min.
  apply CombineMapTheorem.
Qed.

Theorem SupTheorem1 :
  forall {A} (rel : #(ORelation A)),
  forall (S : #(PowerSet A)) (m : #A),
    &&(%Sup rel) S m ->
    forall (a : #A), In a S -> &&(rel{<ORel_Rel}) a m.
Proof.
  intros A rel S m SupH a InaS.
  unfold If in SupH.
  unfold Sup in SupH.
  rewrite MakeMapTheorem in SupH.
  put ((proj1 (MakeRelationTheorem _ _ _ _ _)) SupH) SupH'.
  clear SupH.
  put (SupH' _ _ (ReflexivityEq S) (ReflexivityEq m)) SupH.
  clear SupH'.
  apply MinTheorem2 in SupH.
  apply (UpperTheorem1 _ _ _ SupH).
  apply InaS.
Qed.

Theorem SupTheorem2 :
  forall {A} (rel : #(ORelation A)),
  forall (S : #(PowerSet A)) (m : #A),
    &&(%Sup rel) S m ->
    forall (a : #A), (forall (s : #A), In s S -> &&(rel{<ORel_Rel}) s a) -> &&(rel{<ORel_Rel}) m a.
Proof.
  intros A rel S m SupH a cond.
  unfold If in SupH.
  unfold Sup in SupH.
  rewrite MakeMapTheorem in SupH.
  put ((proj1 (MakeRelationTheorem _ _ _ _ _)) SupH) SupH'.
  clear SupH.
  put (SupH' _ _ (ReflexivityEq S) (ReflexivityEq m)) SupH.
  clear SupH'.
  apply (MinTheorem1 _ _ _ SupH).
  apply UpperTheorem2.
  apply cond.
Qed.
  
Theorem Rel_RUnqCond_Max :
  forall {A} (rel : #(ORelation A)),
    Rel_RUnqCond (%Max rel).
Proof.
  intros A rel.
  intros S x y relSx relSy.
  assert(InrelA : In (rel{<ORel_Rel}) (Antisymmetric A)).
  {
    apply ORel_ASym.
    apply (SetProp rel).
  }
  apply Rel_ASym in InrelA.
  apply InrelA.
  {
    apply (MaxTheorem1 _ S).
    apply relSy.
    apply (MaxTheorem2 rel).
    apply relSx.
  } {
    apply (MaxTheorem1 _ S).
    apply relSx.
    apply (MaxTheorem2 rel).
    apply relSy.
  }
Qed.
  
Theorem Max_Sup :
  forall {A} (rel : #(ORelation A)),
  forall (S : #(PowerSet A)) (m1 m2 : #A),
    &&(%Max rel) S m1 /\ &&(%Sup rel) S m2 -> m1 == m2.
Proof.
  intros A rel S m1 m2 [MaxH SupH].
  assert(InrelA : In (rel{<ORel_Rel}) (Antisymmetric A)).
  {
    apply ORel_ASym.
    apply (SetProp rel).
  }
  apply Rel_ASym in InrelA.
  apply InrelA.
  {
    apply (SupTheorem1 _ _ _ SupH).
    apply (MaxTheorem2 _ _ _ MaxH).
  } {
    apply (SupTheorem2 _ _ _ SupH).
    intros a InsS.
    apply (MaxTheorem1 _ _ _ MaxH).
    apply InsS.
  }
Qed.

Theorem Rel_RUnqCond_Sup :
  forall {A} (rel : #(ORelation A)), Rel_RUnqCond (%Sup rel).
Proof.
  intros A rel.
  intro S.
  assert(Lem : forall (x y : #A), &&(%Sup rel) S x -> &&(%Sup rel) S y -> &&(rel{<ORel_Rel}) x y).
  {
    intros x y Sx Sy.
    apply (SupTheorem2 _ _ _ Sx).
    intros s InsS.
    apply (SupTheorem1 _ _ _ Sy).
    apply InsS.
  }    
  intros x y RSx RSy.
  assert(RelCond : Rel_ASymCond (rel{<ORel_Rel})).
  {
    apply Rel_ASym.
    apply ORel_ASym.
    apply (SetProp rel).
  }
  apply RelCond.
  {
    apply (Lem _ _ RSx).
    apply RSy.
  }
  {
    apply (Lem _ _ RSy).
    apply RSx.
  }
Qed.

Theorem Rel_RUnqCond_Inf :
  forall {A} (rel : #(ORelation A)), Rel_RUnqCond (%Inf rel).
Proof.
  intros A rel.
  unfold Inf.
  unfold Rel_RUnqCond.
  intros S.
  intros x y Sx Sy.
  apply (Rel_RUnqCond_Sup (%InverseORel rel) S).
  {
    generalize Sx.
    apply RelRewrite.
    apply CombineMapTheorem.
  } {
    generalize Sy.
    apply RelRewrite.
    apply CombineMapTheorem.
  }
Qed.



(* Up Closure *)
Theorem UpClosure_RFun {A} :
  RFun (fun (arg : #(Cartesian (ORelation A) (PowerSet A))) => SSet'P A (fun (a : #A) => exists (s : #A), In s (%MRight arg) /\ &&((%MLeft arg){<ORel_Rel}) s a)).
Proof.
intros arg1 arg2 Eqarg.
unfold SSet'P.
apply EqualInSSet'Set.
reflexivity.
intros a1 a2 Eqa.
split; intro HH; destruct HH as [s [Ins HH]]; exists s.
{
  split.
  rewrite (MapArgEq' _ Eqarg).
  exact Ins.
  generalize HH.
  apply RelRewriteAll.
  reflexivity.
  exact Eqa.
  apply MapArgEq.
  exact Eqarg.
} {
  split.
  rewrite (MapArgEq _ Eqarg).
  exact Ins.
  generalize HH.
  apply RelRewriteAll.
  reflexivity.
  exact (SymmetryEq _ _ Eqa).
  apply MapArgEq.
  exact (SymmetryEq _ _ Eqarg).
}
Qed.

Definition UpClosure {A} := %Currying (MakeMap _ _ _ (@UpClosure_RFun A)).
Definition DownClosure {A} := %CombineMap [@UpClosure A ; InverseORel].


