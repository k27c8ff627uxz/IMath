Require Import logic IZF Relation BaseMap.

Definition OpenSets A :=
  SSet
    (PowerSet (PowerSet A))
    (fun O =>
       (In Empty O /\ In A O) /\ (
         (forall S, Subset S O -> In (Unions S) O) /\
         (forall X1 X2, In X1 O -> In X2 O -> In (Section X1 X2) O)
       )
    ).

Theorem OUnions_In :
  forall {A} (X : #(OpenSets A)) (S : #(PowerSet X)),
    In (Unions S) X.
Proof.
  intros A X S.
  put (SetProp X) InXO.
  apply SSetTheorem in InXO.
  apply (proj1 (proj2 (proj2 InXO))).
  apply PowersetTheorem.
  apply SetProp.
Qed.

Definition OSection_In :
  forall {A} (X : #(OpenSets A)) (O1 O2 : #X),
    In (Section O1 O2) X.
Proof.
  intros A X O1 O2.
  put (SetProp X) InXO.
  apply SSetTheorem in InXO.
  apply (proj2 (proj2 (proj2 InXO))); apply SetProp.
Qed.

  




        
    
Definition OpenBases A :=
  SSet
    (PowerSet (PowerSet A))
    (fun O =>
       (Unions O) == A /\ forall X1 X2, In X1 O -> In X2 O -> forall x, In x (Section X1 X2) -> exists X3, In X3 O /\ (In x X3 /\ Subset X3 (Section X1 X2))
    ).

Definition OpenBases_to_OpenSets_Fun {A} (B : #(OpenBases A)) := FunctionImageRistriction Unions (PowerSet B).

Theorem OpenBases_to_OpenSets_Fun_In :
  forall A (B : #(OpenBases A)),
    In (OpenBases_to_OpenSets_Fun B) (OpenSets A).
Proof.
  intros A B.
  put (SetProp B) InBBase.
  apply SSetTheorem in InBBase.
  destruct InBBase as [InBP [BaseCond1 BaseCond2]].
  apply SSetTheorem.
  split.  
  {
    apply PowersetTheorem.
    intros S InSF.
    apply FunctionImageRistrictionTheorem in InSF.
    destruct InSF as [X' [InX'PB UEq]].
    apply PowersetTheorem.
    intros a InaS.
    rewrite <- UEq in InaS.
    apply UnionsTheorem in InaS.
    destruct InaS as [X [InXX' InaX]].
    apply PowersetTheorem in InX'PB.
    apply InX'PB in InXX'.
    apply PowersetTheorem in InBP.
    apply InBP in InXX'.
    apply PowersetTheorem in InXX'.
    apply InXX'.
    apply InaX.
  }
  split.
  {
    split.
    {
      (* Include Empty Set *)
      apply FunctionImageRistrictionTheorem.
      exists Empty.
      split.
      {
        apply PowersetTheorem.
        apply AllSetHasEmpty.
      } {
        apply EA.
        intro x.
        split.
        {
          intro InxUE.
          apply UnionsTheorem in InxUE.
          destruct InxUE as [a [InaE _]].
          apply EmptyTheorem in InaE.
          destruct InaE.
        } {
          intro InxE.
          apply EmptyTheorem in InxE.
          destruct InxE.
        }
      }
    } {
      (* Include Whole Set *)
      apply FunctionImageRistrictionTheorem.
      exists B.
      split.
      {
        apply PowersetTheorem.
        apply ReflexivitySubset.
      } {
        apply BaseCond1.
      }
    }
  }
  split.
  {
    (* Close Under Union *)
    intros S SubSF.
    apply FunctionImageRistrictionTheorem.
    exists (SSet B (fun O' => Subset O' (Unions S))).
    split.
    {
      apply PowersetTheorem.
      intros O InOS.
      apply SSetSubset in InOS.
      apply InOS.
    } {
      apply EA.
      intro a.
      split.
      {
        intro InaU.
        apply UnionsTheorem in InaU.
        destruct InaU as [O [InOS InaO]].
        apply SSetTheorem in InOS.
        destruct InOS as [InOB SubOS].
        apply SubOS.
        apply InaO.
      } {
        intros InaU.
        apply UnionsTheorem in InaU.
        destruct InaU as [O [InOS InaO]].
        put InOS InOS'.
        apply SubSF in InOS'.
        apply FunctionImageRistrictionTheorem in InOS'.
        destruct InOS' as [B' [InB'B UEq]].
        rewrite <- UEq in InOS.
        apply PowersetTheorem in InB'B.
        apply UnionsTheorem.
        rewrite <- UEq in InaO.
        apply UnionsTheorem in InaO.
        destruct InaO as [O' [InO'B' InaO']].
        exists O'.
        split.
        {
          apply SSetTheorem.
          split.
          {
            apply InB'B.
            apply InO'B'.
          }
          intros a' Ina'O'.
          apply UnionsTheorem.
          exists (Unions B').
          split.
          {
            apply InOS.
          }
          apply UnionsTheorem.
          exists O'.
          split; assumption.
        }
        apply InaO'.
      }
    }
  }
  {
    (* Close Under Intersection *)
    intros O1 O2 InOF1 InOF2.
    apply FunctionImageRistrictionTheorem in InOF1.
    apply FunctionImageRistrictionTheorem in InOF2.
    destruct InOF1 as [B1 [SubBB1 EqB1]].
    destruct InOF2 as [B2 [SubBB2 EqB2]].
    apply PowersetTheorem in SubBB1.
    apply PowersetTheorem in SubBB2.
    apply FunctionImageRistrictionTheorem.
    exists (SSet B (fun O => Subset O (Section O1 O2))).
    split.
    {
      apply PowersetTheorem.
      apply SSetSubset.
    }
    apply EA.
    intro a.
    split.
    {
      intros InaU.
      apply UnionsTheorem in InaU.
      destruct InaU as [O [InOS InaO]].
      apply SSetTheorem in InOS.
      destruct InOS as [InOB SOS].
      apply SOS.
      apply InaO.
    } {
      intros InaS.
      apply SectionTheorem in InaS.
      destruct InaS as [InaO1 InaO2].
      rewrite <- EqB1 in InaO1.
      rewrite <- EqB2 in InaO2.
      apply UnionsTheorem in InaO1.
      apply UnionsTheorem in InaO2.
      destruct InaO1 as [O1' [InOB1' InaO1']].
      destruct InaO2 as [O2' [InOB2' InaO2']].
      assert(ExsO3 : exists O3', In O3' B /\ (In a O3' /\ Subset O3' (Section O1' O2'))).
      {
        apply BaseCond2.
        {
          apply SubBB1.
          assumption.
        }
        {
          apply SubBB2.
          assumption.
        }
        {
          apply SectionTheorem.
          split; assumption.
        }
      }
      destruct ExsO3 as [O3' [InO3'B [InaO3' SubO3']]].
      apply UnionsTheorem.
      exists O3'.
      split.
      {
        apply SSetTheorem.
        split.
        exact InO3'B.
        apply (TransitivitySubset _ SubO3').
        cut (Subset O1' O1 /\ Subset O2' O2).
        {
          intros [Sub1 Sub2].
          apply (TransitivitySubset (Section O1 O2')).
          exact (SubsetInSectionL _ _ _ Sub1).
          exact (SubsetInSectionR _ _ _ Sub2).
        }
        split.
        {
          intros x Inx1.
          rewrite <- EqB1.
          apply UnionsTheorem.
          exists O1'.
          split; assumption.
        } {
          intros x Inx2.
          rewrite <- EqB2.
          apply UnionsTheorem.
          exists O2'.
          split; assumption.
        }
      }
      exact InaO3'.
    }
  }
Qed.

Definition OpenBases_to_OpenSets {A} (B : #(OpenBases A)) := { _ ! OpenBases_to_OpenSets_Fun_In _ B}.

Theorem OpenBases_to_OpenSetsTheorem1 :
  forall {A} (B : #(OpenBases A)),
    Subset B (OpenBases_to_OpenSets B).
Proof.
  intros A B.
  intros O InOB.
  apply FunctionImageRistrictionTheorem.
  exists (Singleton O).
  split.
  {
    apply PowersetTheorem.
    intros O' EqO.
    apply SingletonTheorem in EqO.
    rewrite EqO.
    exact InOB.
  }
  apply EA.
  intro x.
  split.
  {
    intro InxU.
    apply UnionsTheorem in InxU.
    destruct InxU as [O' [EqO InxO']].
    apply SingletonTheorem in EqO.
    rewrite <- EqO.
    exact InxO'.
  } {
    intro InxO.
    apply UnionsTheorem.
    exists O.
    split.
    {
      apply SingletonTheorem.
      reflexivity.
    }
    exact InxO.
  }
Qed.


Theorem OpenBases_to_OpenSetsTheorem2 :
  forall {A} (B : #(OpenBases A)) (X : #(OpenSets A)),
    Subset B X -> Subset (OpenBases_to_OpenSets B) X.
Proof.
  intros A B X SubH.
  intros O InOB'.
  unfold OpenBases_to_OpenSets in InOB'.
  rewrite DSETEq in InOB'.
  apply FunctionImageRistrictionTheorem in InOB'.
  destruct InOB' as [B' [InB'B EqB]].
  rewrite <- EqB.
  put (SetProp X) InXO.
  apply SSetTheorem in InXO.
  apply (proj1 (proj2 (proj2 InXO))).
  generalize SubH.
  apply TransitivitySubset.
  apply PowersetTheorem in InB'B.
  exact InB'B.
Qed.
