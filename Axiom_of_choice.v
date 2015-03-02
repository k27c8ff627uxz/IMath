Require Import logic.
Require Import IZF.
Require Import Relation.
Require Import BaseMap.
Require Import Maps.

Definition RAC := forall (A B : Type), 
  forall (P : A -> B -> Prop),
    (forall a, exists b, P a b) ->
    (exists f : A -> B, forall a, P a (f a)).

Definition AC := forall A B,
  forall R : #(Relation A B),
    (forall a, exists b, &&R a b) ->
    (exists f, forall a, &&R a (%f a)).

Theorem RAC_AC : ProofEquiv -> RAC -> AC.
Proof.
intros pe rac.
intros A B R cond.
apply (rac (#A) (#B) (fun a b => &&R a b)) in cond.
destruct cond as [f cond].
assert(RF : RFun f).
now apply ProofEquiv_RFun.
set (MakeMap _ _ f RF) as F.
exists F.
intro a.
generalize (cond a).
apply RelRewriteR.
apply SymmetryEq.
apply MakeMapTheorem.
Qed.
  

Theorem AC_PEM : AC -> REM.
Proof.
intros ac P.
set Empty as f.
set (Next f) as t.
set (UnorderdPair f t) as ft.
set (SSet ft (fun n => n == f \/ (n == t /\ P))) as A.
set (SSet ft (fun n => n == t \/ (n == f /\ P))) as B.
set (UnorderdPair A B) as AB.
set (%InverseRel (InRelation ft AB)) as nI.
assert (base_lem : forall x : #AB, exists y : #ft, &&nI x y).
{
  assert(Infft : In f ft).
  {
    apply UnorderdPairTheorem.
    auto.
  }
  assert(Intft : In t ft).
  {
    apply UnorderdPairTheorem.
    auto.
  }
  intros x.
  put (SetProp x) InxAB.
  apply UnorderdPairTheorem in InxAB.
  destruct InxAB as [EqxA | EqxB].
  {
    exists {f ! Infft}.
    apply (InverseRelTheorem (InRelation ft AB)).
    apply InRelationTheorem.
    rewrite EqxA.
    apply SSetTheorem.
    split.
    now apply Infft.
    left.
    now auto.
  } {
    exists {t ! Intft}.
    apply (InverseRelTheorem (InRelation ft AB)).
    apply InRelationTheorem.
    rewrite EqxB.
    apply SSetTheorem.
    split.
    now apply Intft.
    left.
    now auto.
  }
}
apply ac in base_lem.
destruct base_lem as [F base_lem].
assert(NEqft : ~f == t).
{
  intro Eqft.
  apply (EmptyTheorem f).
  cut (In f t).
  {
    rewrite <- Eqft.
    auto.
  }
  apply UnionTheorem.
  right.
  apply SingletonTheorem.
  auto.
}
assert(A_in_AB : In A AB).
{
  apply UnorderdPairTheorem.
  auto.
}
assert(B_in_AB : In B AB).
{
  apply UnorderdPairTheorem.
  auto.
}
assert(Eq_or_NEq : (%F {A ! A_in_AB} == %F {B ! B_in_AB}) \/ ~(%F {A ! A_in_AB} == %F {B ! B_in_AB})).
{
  assert(FA_in_A : In (%F {A ! A_in_AB}) A).
  {
    put (base_lem {A ! A_in_AB}) base_lem'.
    apply (InverseRelTheorem (InRelation ft AB)) in base_lem'.
    apply InRelationTheorem in base_lem'.
    apply base_lem'.
  }
  assert(FB_in_B : In (%F {B ! B_in_AB}) B).
  {
    put (base_lem {B ! B_in_AB}) base_lem'.
    apply (InverseRelTheorem (InRelation ft AB)) in base_lem'.
    apply InRelationTheorem in base_lem'.
    apply base_lem'.
  }
  apply SSetSubset in FA_in_A.
  apply SSetSubset in FB_in_B.
  apply UnorderdPairTheorem in FA_in_A.
  apply UnorderdPairTheorem in FB_in_B.
  destruct FA_in_A as [Af | At] ; destruct FB_in_B as [Bf | Bt].
  {
    left.
    apply (TransitivityEq f); auto.
  } {
    right.
    intro EqH.
    rewrite Af in EqH.
    rewrite Bt in EqH.
    tauto.
  } {
    right.
    intro EqH.
    rewrite At in EqH.
    rewrite Bf in EqH.
    apply NEqft.
    apply SymmetryEq.
    auto.
  } {
    left.
    rewrite At.
    rewrite Bt.
    auto.
  }
}
destruct Eq_or_NEq as [EqH | NEqH].
{
  assert(InF : forall a : #AB, In (%F a) a).
  {
    intros a.
    put (base_lem a) InH.
    apply (InverseRelTheorem (InRelation ft AB)) in InH.
    apply InRelationTheorem in InH.
    apply InH.
  }
  assert(InFAA : In (%F {A ! A_in_AB}) A).
  now apply InF.
  assert(InFBB : In (%F {B ! B_in_AB}) B).
  now apply InF.
  apply SSetTheorem in InFAA.
  destruct InFAA as [InFAft [EqFAf | [EqFFAt PH]]].
  {
    rewrite EqH in EqFAf.
    rewrite EqFAf in InFBB.
    apply SSetTheorem in InFBB.
    destruct InFBB as [Infft [Eqft | [Eqff PH]]].
    now tauto.
    auto.
  } {
    left.
    apply PH.
  }
} {
  right.
  intro PH.
  cut (A == B).
  {
    intro EqAB.
    apply NEqH.
    apply MapArgEq.
    apply EqAB.
  }
  assert(InftAB : (In f A /\ In t A) /\ (In f B /\ In t B)).
  {
    split; split.
    {
      apply SSetTheorem.
      split.
      {
        apply UnorderdPairTheorem.
        auto.
      } {
        left.
        auto.
      }
    } {
      apply SSetTheorem.
      split.
      {
        apply UnorderdPairTheorem.
        auto.
      } {
        right.
        split; auto.
      }
    } {
      apply SSetTheorem.
      split.
      {
        apply UnorderdPairTheorem.
        auto.
      } {
        right.
        split; auto.
      } 
    } {
      apply SSetTheorem.
      split.
      {
        apply UnorderdPairTheorem.
        auto.
      }
      now auto.
    }
  }
  destruct InftAB as [[InfA IntA] [InfB IntB]].
  apply EA.
  intro x.
  split; intro Inx.
  {
    apply SSetSubset in Inx.
    apply UnorderdPairTheorem in Inx.
    destruct Inx as [Eqx | Eqx]; rewrite Eqx; auto.
  } {
    apply SSetSubset in Inx.
    apply UnorderdPairTheorem in Inx.
    destruct Inx as [Eqx | Eqx]; rewrite Eqx; auto.
  }
}
Qed.








