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

Definition Upper_Rel {A} (rel : #(ORelation A)) :=
  MakeRelation
    (fun (S1 : #(PowerSet A)) (S2 : #(PowerSet A)) =>
       forall (b : #A), (forall (a : #A), In a S1 -> &&(rel{<ORel_Rel}) a b) <-> In b S2
    ).

Theorem Upper_Rel_Theorem :
  forall {A} (rel : #(ORelation A)),
  forall S1 S2,
    &&(Upper_Rel rel) S1 S2 <->
    (forall (b : #A), (forall (a : #A), In a S1 -> &&(rel{<ORel_Rel}) a b) <-> In b S2).
Proof.
  intros A rel S1 S2.
  split.
  {
    intros relH b.
    put ((proj1 (MakeRelationTheorem _ _ _ _ _)) relH) HH.
    clear relH.
    put (HH _ _ (ReflexivityEq S1) (ReflexivityEq S2)) HHH.
    clear HH.
    apply HHH.
  } {
    intro cond.
    apply MakeRelationTheorem.
    intros S1' S2' EqS1 EqS2 b.
    split.
    {
      intro condH.
      rewrite <- EqS2.
      apply cond.
      intros a InaS1.
      apply condH.
      rewrite <- EqS1.
      apply InaS1.
    } {
      intros InbS2 a InaS1.
      rewrite <- EqS2 in InbS2.
      put ((proj2 (cond _)) InbS2) HH.
      apply HH.
      rewrite EqS1.
      apply InaS1.
    }
  }
Qed.

Theorem Upper_Rel_MapCond :
  forall {A} (rel : #(ORelation A)),
    Rel_MapCond (Upper_Rel rel).
Proof.
  intros A rel.
  intros S1.
  split.
  {
    set (SSet' A (fun a => forall (m : #A), In m S1 -> &&(rel{<ORel_Rel}) m a)) as S2_.
    assert(InS2A : In S2_ (PowerSet A)).
    {
      apply PowersetTheorem.      
      apply SSet'Subset.
    }
    set {S2_ ! InS2A} as S2.
    exists S2.
    apply Upper_Rel_Theorem.
    intro b.
    split.
    {
      intros cond.
      apply SSet'Theorem.
      split.
      apply SetProp.
      intros InbA m InmS1.
      cut (&&(rel{<ORel_Rel}) m b).
      {
        apply RelRewriteR.
        hyperreflexivity.
      }
      apply cond.
      assumption.
    } {
      intros InbS2' a cond.
      put ((proj1 (SSet'Theorem _ _ _)) InbS2') HH.
      destruct HH as [InbA condH].
      cut (&&(rel{<ORel_Rel}) a {b ! InbA}).
      {
        apply RelRewriteR.
        hyperreflexivity.
      }
      apply condH.
      apply cond.
    }
  } {
    intros SA SB [RelH1 RelH2].
    put ((proj1 (Upper_Rel_Theorem _ _ _)) RelH1) HH1.
    put ((proj1 (Upper_Rel_Theorem _ _ _)) RelH2) HH2.
    clear RelH1.
    clear RelH2.
    apply EA.
    intros b'.
    split.
    {
      intro InbSA.
      assert(InbA : In b' A).
      {
        cut (In SA (PowerSet A)).
        {
          intro SubH.
          apply PowersetTheorem in SubH.
          apply SubH.
          assumption.
        }
        apply SetProp.
      }
      set {b' ! InbA} as b.
      cut (In b SB).
      auto.
      apply HH2.
      apply HH1.
      apply InbSA.
    } {
      intro InbSB.
      assert(InbA : In b' A).
      {
        cut (In SB (PowerSet A)).
        {
          intro SubH.
          apply PowersetTheorem in SubH.
          apply SubH.
          assumption.
        }
        apply SetProp.
      }
      set {b' ! InbA} as b.
      cut (In b SA).
      auto.
      apply HH1.
      apply HH2.
      apply InbSB.
    }
  }
Qed.

Definition Upper {A} (rel : #(ORelation A)) :=
  (Upper_Rel rel){<Rel_Map ! Upper_Rel_MapCond rel}.

Theorem UpperTheorem1 :
  forall {A} (rel : #(ORelation A)) (S : #(PowerSet A)) (m : #A),
    In m (%(Upper rel) S) -> (forall (a : #A), In a S -> &&(rel{<ORel_Rel}) a m).
Proof.
  intros A rel S m InmU a InaS.
  assert(relH : &&(Upper_Rel rel) S (%(Upper rel) S)).
  {
    generalize (AppTheorem (Upper rel) S).
    apply RelRewrite.
    hyperreflexivity.
  }
  put ((proj1 (Upper_Rel_Theorem _ _ _)) relH) HH.
  clear relH.
  put ((proj2 (HH _)) InmU) HHH.
  apply HHH.
  apply InaS.
Qed.

Theorem UpperTheorem2 :
  forall {A} (rel : #(ORelation A)) (S : #(PowerSet A)) (m : #A),
    (forall (a : #A), In a S -> &&(rel{<ORel_Rel}) a m) -> In m (%(Upper rel) S).
Proof.
  intros A rel S m cond.
  assert(relH : &&(Upper_Rel rel) S (%(Upper rel) S)).
  {
    generalize (AppTheorem (Upper rel) S).
    apply RelRewrite.
    hyperreflexivity.
  }
  put ((proj1 (Upper_Rel_Theorem _ _ _)) relH) HH.
  clear relH.
  apply HH.
  apply cond.
Qed.

Definition Lower {A} (rel : #(ORelation A)) := Upper (%InverseORel rel). 
           
Definition Max {A} (rel : #(ORelation A)) :=
  MakeRelation
    (fun (S : #(PowerSet A)) (a : #A) => In a (Section S (%(Upper rel) S))).

Definition Min {A} (rel : #ORelation A) := Max (%InverseORel rel).

Definition Sup {A} (rel : #ORelation A) :=
  MakeRelation
    (fun (S : #(PowerSet A)) (a : #A) => &&(Min rel) (%(Upper rel) S) a).

Definition Inf {A} (rel : #ORelation A) := Sup (%InverseORel rel).

Theorem MaxTheorem1 :
  forall {A} (rel : #(ORelation A)),
  forall (S : #(PowerSet A)) (m : #A),
    &&(Max rel) S m ->
    forall (a : #A), In a S -> &&(rel{<ORel_Rel}) a m.
Proof.
  intros A rel S m MaxH a InaS.
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
    &&(Max rel) S m -> In m S.
Proof.
  intros A rel S m MaxH.
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
    &&(Min rel) S m ->
    forall (a : #A), In a S -> &&(rel{<ORel_Rel}) m a.
Proof.
  intros A rel S m MinH a InaS.
  apply <- (InverseORelTheorem rel).
  apply (MaxTheorem1 _ S).
  apply MinH.
  apply InaS.
Qed.

Theorem MinTheorem2 :
  forall {A} (rel : #(ORelation A)),
  forall (S : #(PowerSet A)) (m : #A),
    &&(Min rel) S m -> In m S.
Proof.
  intros A rel S m MinH.
  apply (MaxTheorem2 (%InverseORel rel)).
  apply MinH.
Qed.

Theorem SupTheorem1 :
  forall {A} (rel : #(ORelation A)),
  forall (S : #(PowerSet A)) (m : #A),
    &&(Sup rel) S m ->
    forall (a : #A), In a S -> &&(rel{<ORel_Rel}) a m.
Proof.
  intros A rel S m SupH a InaS.
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
    &&(Sup rel) S m ->
    forall (a : #A), (forall (s : #A), In s S -> &&(rel{<ORel_Rel}) s a) -> &&(rel{<ORel_Rel}) m a.
Proof.
  intros A rel S m SupH a cond.
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
    Rel_RUnqCond (Max rel).
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
    &&(Max rel) S m1 /\ &&(Sup rel) S m2 -> m1 == m2.
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
  forall {A} (rel : #(ORelation A)), Rel_RUnqCond (Sup rel).
Proof.
  intros A rel.
  intro S.
  assert(Lem : forall (x y : #A), &&(Sup rel) S x -> &&(Sup rel) S y -> &&(rel{<ORel_Rel}) x y).
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
  forall {A} (rel : #(ORelation A)), Rel_RUnqCond (Inf rel).
Proof.
  intros A rel.
  apply Rel_RUnqCond_Sup.
Qed.


