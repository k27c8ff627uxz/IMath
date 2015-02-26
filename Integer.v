Require Import logic.
Require Import IZF.
Require Import Relation.
Require Import BaseMap.
Require Import Maps.
Require Import BOperation1.
Require Import BOperation2.
Require Import AddMultPower.

(*Preparation*)
Theorem NNIsSubCMonoid : In NN (SubCMonoid NNAdd_CMonoid).
Proof.
cut (In {NN ! PowersetHasOwn NN} (SubCMonoid NNAdd_CMonoid)).
 apply Arrow2Rewrite; hyperreflexivity.
unfold SubCMonoid.
apply SubIdenticalTheorem.
apply IsSubIdenticalTheorem.
split.
 apply IsSubBOperationTheorem.
 intros a b Ina Inb.
 cut (In (%NNAdd [a;b]) NN).
  apply Arrow2Rewrite.
  hyperreflexivity.
  hyperreflexivity.
 apply SetProp.
intros e IsIe'.
assert(IsIe : &&IsIdent NNAdd e).
 generalize IsIe'.
 apply RelRewriteL.
 hyperreflexivity.
assert(Eqe0 : e == (nat_to_NN 0)).
 apply (IsIdentEq NNAdd).
 apply IsIe.
 apply NN0IsIdent.
rewrite Eqe0.
rewrite (DSETEq NN _).
apply (SetProp).
Qed.

Definition NNSubCMonoid := {NN ! NNIsSubCMonoid}.


Theorem NN_NNSubCMonoid : Subset NN NNSubCMonoid.
Proof.
apply ReflexivitySubset2.
hyperreflexivity.
Qed.

Theorem NNSubCMonoid_NN : Subset NN NNSubCMonoid.
Proof.
apply ReflexivitySubset2.
hyperreflexivity.
Qed.

Definition ZZ := FractionCMonoidSet NNAdd_CMonoid NNSubCMonoid.

Definition NNNN_to_ZZ : #(Map (Cartesian NN NN) ZZ) :=
%CombineMap' [%DoubleMap [IdMap ; EmbedMap NN_NNSubCMonoid] ; to_FractionCMonoidSet NNAdd_CMonoid NNSubCMonoid].

Definition NN_to_ZZ : #(Map NN ZZ) := (FractionCMonoidCannProj _ _).

Definition ZZAdd : #(BOperation ZZ) := (FractionCMonoid _ _).

Definition NZ := %Image NN_to_ZZ.

Definition nat_to_ZZ (n : nat) : #ZZ := %NN_to_ZZ (nat_to_NN n).



(* Algebraic Structure of Add *)

Theorem ZZAdd_SGrpCond : Ope_SGrpCond ZZAdd.
Proof.
unfold ZZAdd.
apply FractionCMonoid_Ope_SGrpCond.
Qed.

Theorem ZZAdd_CommCond : Ope_CommCond ZZAdd.
Proof.
unfold ZZAdd.
apply FractionCMonoid_Ope_CommCond.
Qed.

Theorem ZZ0IsIdent : &&IsIdent ZZAdd (nat_to_ZZ 0).
Proof.
unfold ZZAdd.
unfold NN_to_ZZ.
apply FractionCMonoidCannProj_IsIdent.
generalize NN0IsIdent.
apply RelRewriteL.
hyperreflexivity.
Qed.

Theorem ZZAdd_IdentCond : Ope_IdentCond ZZAdd.
Proof.
exists (%NN_to_ZZ (nat_to_NN 0)).
apply ZZ0IsIdent.
Qed.

Theorem ZZAdd_MonoidCond : Ope_MonoidCond ZZAdd.
Proof.
split.
apply ZZAdd_SGrpCond.
apply ZZAdd_IdentCond.
Qed.


(* NNNN_to_ZZ *)
Theorem NNNN_to_ZZ_is_Fraction : forall m n,
%NNNN_to_ZZ [m;n] ==
%(to_FractionCMonoidSet NNAdd_CMonoid NNSubCMonoid) [m ; %(EmbedMap NN_NNSubCMonoid) n].
Proof.
intros m n.
unfold NNNN_to_ZZ.
rewrite CombineMap'Theorem.
apply MapArgEq.
rewrite DoubleMapTheorem.
apply EqualInPair'L.
apply IdMapTheorem.
Qed.

Theorem NN_to_ZZ_is_NNNN_to_ZZ : forall n,
%NN_to_ZZ n ==
%NNNN_to_ZZ [n ; nat_to_NN 0].
Proof.
intro n.
unfold NN_to_ZZ.
rewrite (FractionCMonoidCannProjTheorem NNAdd_CMonoid NNSubCMonoid).
rewrite NNNN_to_ZZ_is_Fraction.
apply MapArgEq.
apply EqualInPair'R.
apply MIdentEq.
generalize NN0IsIdent.
apply IsIdent_StrongCons.
 rewrite EmbedMapEq.
 hyperreflexivity.
apply (TransitivityStrongRel ((SubCMonoid_to_CMonoid NNSubCMonoid){<CMonoid_Ope}){<Map_Rel}).
 apply ReflexivityStrongRel2.
 hyperreflexivity.
apply (StrongSubBOpe _ (NNSubCMonoid){<SubCMonoid_SubOpe}).
Qed.

Theorem ZZIsNNNN : forall (a : #ZZ),
exists m, exists n,
a == %NNNN_to_ZZ [m;n].
Proof.
intro a.
put (FractionCMonoidSetIn _ _ a) Eqa.
destruct Eqa as [m Eqa].
destruct Eqa as [n Eqa].
exists m.
exists n.
rewrite NNNN_to_ZZ_is_Fraction.
apply (TransitivityEq (%(to_FractionCMonoidSet NNAdd_CMonoid NNSubCMonoid) [m;n])).
 apply Eqa.
apply MapArgEq.
apply EqualInPair'R.
rewrite EmbedMapEq.
hyperreflexivity.
Qed.

Theorem NNNN_to_ZZEq : forall a b c d,
%NNNN_to_ZZ [a;b] == %NNNN_to_ZZ [c;d] <->
%NNAdd [a;d] == %NNAdd [c;b].
Proof.
intros a b c d.
split.
 intro HH.
 rewrite NNNN_to_ZZ_is_Fraction in HH.
 rewrite NNNN_to_ZZ_is_Fraction in HH.
 apply (to_FractionCMonoidSetEq NNAdd_CMonoid NNSubCMonoid) in HH.
 destruct HH as [s HH].
 cut (%NNAdd [%NNAdd [a;d] ; s{<SubCMonoid_S}] == %NNAdd [%NNAdd[c;b] ; s{<SubCMonoid_S}]).
  intro EqH.
  apply NNAddRightCancell in EqH.
  apply EqH.
 apply (TransitivityEq (%(NNAdd_CMonoid{<CMonoid_Ope}) [%(NNAdd_CMonoid{<CMonoid_Ope}) [a; (%(EmbedMap NN_NNSubCMonoid) d){<SubCMonoid_S}] ; s{<SubCMonoid_S}])).
  apply MapEqAll.
   apply EqualInPair'L.
   apply MapEqAll.
    apply EqualInPair'R.
    rewrite USETEq.
    rewrite EmbedMapEq.
    hyperreflexivity.
   hyperreflexivity.
  hyperreflexivity.
 rewrite HH.
 apply MapEqAll.
  apply EqualInPair'L.
  apply MapEqAll.
   apply EqualInPair'R.
   rewrite USETEq.
   rewrite EmbedMapEq.
   hyperreflexivity.
  hyperreflexivity.
 hyperreflexivity.


 intro EqN.
 rewrite NNNN_to_ZZ_is_Fraction.
 rewrite NNNN_to_ZZ_is_Fraction.
 apply (to_FractionCMonoidSetEq NNAdd_CMonoid NNSubCMonoid).
 exists (nat_to_NN 0).
 apply (TransitivityEq (%NNAdd [%NNAdd [a;d] ; nat_to_NN 0])).
  apply MapEqAll.
   apply EqualInPair'.
   split.
    apply MapEqAll.
     apply EqualInPair'R.
     rewrite USETEq.
     rewrite EmbedMapEq.
     hyperreflexivity.
    hyperreflexivity.
   hyperreflexivity.
  hyperreflexivity.
 rewrite NNAddTheorem1.
 rewrite EqN.
 apply (TransitivityEq (%NNAdd [%NNAdd [c;b] ; nat_to_NN 0])).
  rewrite NNAddTheorem1.
  hyperreflexivity.
 apply MapEqAll.
  apply EqualInPair'.
  split.
   apply MapEqAll.
    apply EqualInPair'R.
    rewrite USETEq.
    rewrite EmbedMapEq.
    hyperreflexivity.
   hyperreflexivity.
  hyperreflexivity.
 hyperreflexivity.
Qed.


Theorem ZZAddTheorem_NNNN : forall a b c d,
%ZZAdd [%NNNN_to_ZZ [a;b] ; %NNNN_to_ZZ [c;d]] ==
%NNNN_to_ZZ [%NNAdd [a;c] ; %NNAdd [b;d]].
Proof.
intros a b c d.
rewrite (MapArgEq _ (EqualInPair'L _ _ _ _ _ (NNNN_to_ZZ_is_Fraction _ _))).
rewrite (MapArgEq _ (EqualInPair'R _ _ _ _ _ (NNNN_to_ZZ_is_Fraction _ _))).
rewrite (FractionCMonoidTheorem NNAdd_CMonoid NNSubCMonoid).
rewrite NNNN_to_ZZ_is_Fraction.
apply MapArgEq.
apply EqualInPair'.
split.
 hyperreflexivity.
rewrite EmbedMapEq.
apply MapStrong.
 apply (StrongSubBOpe _ (NNSubCMonoid{<SubCMonoid_SubOpe})).
apply EqualInPair'.
split; apply EmbedMapEq.
Qed.

Theorem NNNN_to_ZZ_IsIdent2 : forall (m n : #NN),
m == n -> 
&&IsIdent ZZAdd (%NNNN_to_ZZ [m;n]).
Proof.
intros m n Eqmn.
unfold ZZAdd.
apply (RelRewriteR' (NNNN_to_ZZ_is_Fraction _ _)).
apply to_FractionCMonoidSet_Ident2.
rewrite Eqmn.
rewrite EmbedMapEq.
hyperreflexivity.
Qed.

Theorem ZZAdd_IsInverseE_NNNN : forall m n,
&&(%IsInverseE ZZAdd) (%NNNN_to_ZZ [m;n]) (%NNNN_to_ZZ [n;m]).
Proof.
intros m n.
apply IsInverseETheoremL.
 apply ZZAdd_CommCond.
apply (RelRewriteR' (ZZAddTheorem_NNNN _ _ _ _)).
apply NNNN_to_ZZ_IsIdent2.
apply NNAdd_Ope_CommCond.
Qed.
 

Theorem ZZAdd_InvertCond : Ope_InvertCond ZZAdd.
Proof.
intro x.
put (ZZIsNNNN x) Eqx.
destruct Eqx as [m Eqx].
destruct Eqx as [n Eqx].
apply IsInvertibleTheorem.
exists (%NNNN_to_ZZ [n;m]).
apply (RelRewriteL' Eqx).
apply ZZAdd_IsInverseE_NNNN.
Qed.

Theorem ZZAdd_GrpCond : Ope_GrpCond ZZAdd.
Proof.
split.
apply ZZAdd_MonoidCond.
apply ZZAdd_InvertCond.
Qed.

Theorem ZZAdd_CGrpCond : Ope_CGrpCond ZZAdd.
Proof.
split.
apply ZZAdd_GrpCond.
apply ZZAdd_CommCond.
Qed.

Definition ZZAdd_CGrp := ZZAdd{<Ope_CGrp ! ZZAdd_CGrpCond}.

(* Addition of Integer *)
Definition Minus_of_ZZ : #(Map ZZ ZZ) :=
(MInvert_of_CGrp ZZAdd_CGrp).

Theorem Minus_of_ZZTheorem : forall n,
&&(%IsInverseE ZZAdd) n (%Minus_of_ZZ n).
Proof.
intro n.
generalize (MInvert_of_CGrpTheorem ZZAdd_CGrp n).
apply RelRewriteAll; hyperreflexivity.
Qed.

Theorem DoubleMinus_of_ZZ : forall n,
%Minus_of_ZZ (%Minus_of_ZZ n) == n.
Proof.
intro n.
apply (IsInverseEq_SGrp (ZZAdd_CGrp{<CGrp_SGrp}) (%Minus_of_ZZ n)).
 generalize (Minus_of_ZZTheorem (%Minus_of_ZZ n)).
 apply RelRewriteAll; hyperreflexivity.
apply IsInverseESymCond.
generalize (Minus_of_ZZTheorem n).
apply RelRewriteAll; hyperreflexivity.
Qed.

Theorem Minus_of_ZZDist : forall n m,
%Minus_of_ZZ (%ZZAdd [n;m]) == %ZZAdd [%Minus_of_ZZ n;%Minus_of_ZZ m].
Proof.
intros n m.
apply (TransitivityEq (%Minus_of_ZZ (%(ZZAdd_CGrp{<CGrp_Ope}) [n;m]))).
 hyperreflexivity.
unfold Minus_of_ZZ at 1.
rewrite MInvert_of_CGrpMultTheorem.
hyperreflexivity.
Qed.

Theorem NNNN_to_ZZTheorem : forall n m,
%NNNN_to_ZZ [n;m] ==
%ZZAdd [%NN_to_ZZ n ; %Minus_of_ZZ (%NN_to_ZZ m)].
Proof.
intros n m.
apply (TransitivityEq (%ZZAdd [%NNNN_to_ZZ [n ; nat_to_NN 0] ; %NNNN_to_ZZ [nat_to_NN 0 ; m]])).
 apply SymmetryEq.
 rewrite ZZAddTheorem_NNNN.
 apply MapArgEq.
 apply EqualInPair'.
 split.
 apply NNAddTheorem1.
 rewrite NNAdd_Ope_CommCond.
 apply NNAddTheorem1.
apply MapArgEq.
apply EqualInPair'.
split.
 apply SymmetryEq.
 apply NN_to_ZZ_is_NNNN_to_ZZ.
cut (&&IsIdent ZZAdd (%ZZAdd [%NN_to_ZZ m ; %NNNN_to_ZZ [nat_to_NN 0 ; m] ])).
 intro IsIH.
 apply SymmetryEq.
 apply (TransitivityEq (%ZZAdd [%Minus_of_ZZ (%NN_to_ZZ m) ; %ZZAdd [%NN_to_ZZ m ; %NNNN_to_ZZ [nat_to_NN 0 ; m]]])).
  apply SymmetryEq.
  apply IsRightIdentTheorem.
  apply IsIdent_RightIdent.
  apply IsIH.
 rewrite <- ZZAdd_SGrpCond.
 apply IsLeftIdentTheorem.
 apply IsIdent_LeftIdent.
 apply IsInverseE_IsIdent'.
 apply Minus_of_ZZTheorem.
cut (&&IsIdent ZZAdd (%ZZAdd [%NNNN_to_ZZ [m;nat_to_NN 0] ; %NNNN_to_ZZ [nat_to_NN 0 ; m]])).
 apply RelRewriteR.
 apply MapArgEq.
 apply EqualInPair'L.
 rewrite NN_to_ZZ_is_NNNN_to_ZZ.
 hyperreflexivity.
apply IsInverseE_IsIdent.
apply ZZAdd_IsInverseE_NNNN.
Qed.

Theorem NNAdd_to_ZZAdd_Hom :
&&IsHomomorphism_of_BOpe [NNAdd;ZZAdd] NN_to_ZZ.
Proof.
apply (FractionCMonoidCannProj_Hom NNAdd_CMonoid NNSubCMonoid).
Qed.

Theorem ZZAdd_comm_NNAdd : forall n1 n2,
%NN_to_ZZ (%NNAdd [n1;n2]) ==
%ZZAdd [%NN_to_ZZ n1 ; %NN_to_ZZ n2].
Proof.
put NNAdd_to_ZZAdd_Hom HomH.
put ((proj1 (IsHomomorphism_of_BOpeTheorem _ _ _)) HomH) comm.
apply comm.
Qed.



Definition ZZNext : #(Map ZZ ZZ) :=
%(%Currying ZZAdd) (nat_to_ZZ 1).

Definition ZZPrev : #(Map ZZ ZZ) :=
%(%Currying ZZAdd) (%Minus_of_ZZ (nat_to_ZZ 1)).

Theorem ZZNextTheorem : forall n,
%ZZNext n == %ZZAdd [n ; nat_to_ZZ 1].
Proof.
intro n.
unfold ZZNext.
rewrite CurryingTheorem.
apply ZZAdd_CommCond.
Qed.

Theorem ZZPrevTheorem : forall n,
%ZZPrev n == %ZZAdd [n ; %Minus_of_ZZ (nat_to_ZZ 1)].
Proof.
intro n.
unfold ZZPrev.
rewrite CurryingTheorem.
apply ZZAdd_CommCond.
Qed.

Theorem ZZPrevTheorem2 : forall n,
%ZZPrev n == %Minus_of_ZZ (%ZZNext (%Minus_of_ZZ n)).
Proof.
intro n.
apply SymmetryEq.
rewrite (MapArgEq _ (ZZNextTheorem _)).
rewrite Minus_of_ZZDist.
rewrite (MapArgEq _ (EqualInPair'L _ _ _ _ _ (DoubleMinus_of_ZZ _))).
apply SymmetryEq.
rewrite ZZPrevTheorem.
hyperreflexivity.
Qed.



Theorem ZZNext_comm_NNNext_arg : forall n,
%ZZNext (%NN_to_ZZ n) ==
%NN_to_ZZ (%NNNext n).
Proof.
intros n.
unfold ZZNext.
rewrite CurryingTheorem.
rewrite ZZAdd_CommCond.
unfold nat_to_ZZ.
rewrite <- ZZAdd_comm_NNAdd.
apply MapArgEq.
unfold nat_to_NN.
rewrite NNAddTheorem2.
apply MapArgEq.
rewrite NNAddTheorem1.
hyperreflexivity.
Qed.

Theorem ZZNext_comm_NNNext :
%CombineMap' [NN_to_ZZ ; ZZNext] ==
%CombineMap' [NNNext ; NN_to_ZZ].
Proof.
apply MapEquality.
hyperreflexivity.
intros n1 n2 Eqn.
rewrite CombineMap'Theorem.
rewrite CombineMap'Theorem.
rewrite ZZNext_comm_NNNext_arg.
apply MapArgEq.
apply MapArgEq.
apply Eqn.
Qed.

Theorem ZZNext_comb_ZZPrev : forall n,
%ZZNext (%ZZPrev n) == n.
Proof.
intros n.
unfold ZZNext.
rewrite CurryingTheorem.
rewrite ZZAdd_CommCond.
unfold ZZPrev.
rewrite (MapArgEq _ (EqualInPair'L _ _ _ _ _ (CurryingTheorem _ _ _))).
rewrite ZZAdd_CommCond.
rewrite <- ZZAdd_SGrpCond.
apply IsLeftIdentTheorem.
apply IsIdent_LeftIdent.
put (Minus_of_ZZTheorem (nat_to_ZZ 1)) InvH.
apply IsInverseETheorem in InvH.
apply (proj1 InvH).
Qed.

Theorem ZZPrev_comb_ZZNext : forall n,
%ZZPrev (%ZZNext n) == n.
Proof.
intros n.
unfold ZZPrev.
rewrite CurryingTheorem.
unfold ZZNext.
rewrite (MapArgEq _ (EqualInPair'R _ _ _ _ _ (CurryingTheorem _ _ _))).
rewrite <- ZZAdd_SGrpCond.
apply IsLeftIdentTheorem.
apply IsIdent_LeftIdent.
put (Minus_of_ZZTheorem (nat_to_ZZ 1)) InvH.
apply IsInverseETheorem in InvH.
apply (proj2 InvH).
Qed.



Theorem ZZAddTheorem0 : forall z,
%ZZAdd [z ; nat_to_ZZ 0] == z.
Proof.
intro z.
apply IsRightIdentTheorem.
apply IsIdent_RightIdent.
apply ZZ0IsIdent.
Qed.

Theorem ZZAddTheorem1 : forall m n,
%ZZAdd [m ; %ZZNext n] == %ZZNext (%ZZAdd [m;n]).
Proof.
intros m n.
unfold ZZNext at 1.
rewrite (MapArgEq _ (EqualInPair'R _ _ _ _ _ (CurryingTheorem _ _ _))).
rewrite <- ZZAdd_SGrpCond.
rewrite (MapArgEq _ (EqualInPair'L _ _ _ _ _ (ZZAdd_CommCond _ _))).
rewrite ZZAdd_SGrpCond.
unfold ZZNext.
rewrite CurryingTheorem.
hyperreflexivity.
Qed.

Theorem ZZAddTheorem2 : forall m n,
%ZZAdd [m ; %ZZPrev n] == %ZZPrev (%ZZAdd [m;n]).
Proof.
intros m n.
unfold ZZPrev at 1.
rewrite (MapArgEq _ (EqualInPair'R _ _ _ _ _ (CurryingTheorem _ _ _))).
rewrite <- ZZAdd_SGrpCond.
rewrite (MapArgEq _ (EqualInPair'L _ _ _ _ _ (ZZAdd_CommCond _ _))).
rewrite ZZAdd_SGrpCond.
unfold ZZPrev.
rewrite CurryingTheorem.
hyperreflexivity.
Qed.


Theorem ZZNextInjection : Map_InjCond ZZNext.
Proof.
intros n m EqH.
apply (TransitivityEq (%ZZPrev (%ZZNext n))).
 apply SymmetryEq.
 apply ZZPrev_comb_ZZNext.
rewrite (MapArgEq _ EqH).
rewrite ZZPrev_comb_ZZNext.
hyperreflexivity.
Qed.

Theorem ZZNextSurjection : Map_SurCond ZZNext.
Proof.
intros n.
exists (%ZZPrev n).
apply ZZNext_comb_ZZPrev.
Qed.

Theorem ZZPrevInjection : Map_InjCond ZZPrev.
Proof.
intros n m EqH.
apply (TransitivityEq (%ZZNext (%ZZPrev n))).
 apply SymmetryEq.
 apply ZZNext_comb_ZZPrev.
rewrite (MapArgEq _ EqH).
rewrite ZZNext_comb_ZZPrev.
hyperreflexivity.
Qed.

Theorem ZZPrevSurjection : Map_SurCond ZZPrev.
Proof.
intros n.
exists (%ZZNext n).
apply ZZPrev_comb_ZZNext.
Qed.


(************************)
(* Representation of ZZ *)
(************************)

Theorem HomNN_RepresentOfFractionCMonoidableSet :
Subset (%Homomorphism_of_BOpe [NNAdd;ZZAdd]) (RepresentOfFractionCMonoidableSet NNAdd_CMonoid (ZZAdd_CGrp{<CGrp_Monoid}) NNSubCMonoid).
Proof.
intros f InfH.
assert(InfM : In f (Map NN ZZ)).
 apply HomBOpe_Map in InfH.
 apply InfH.
rewrite (DSETEq' _ InfM).
apply RepresentOfFractionCMonoidableSetTheorem.
split.
 apply Homomorphism_of_BOpeTheorem.
 generalize InfH.
 apply Arrow2Rewrite.
 hyperreflexivity.
 hyperreflexivity.
intros s InsNNS.
cut (&&IsInvertible ZZAdd (%{f ! InfM} s)).
 apply RelRewriteL.
 hyperreflexivity.
apply ZZAdd_InvertCond.
Qed.

Definition NZMap_to_ZZMap : #(Map (%Homomorphism_of_BOpe [NNAdd;ZZAdd]) (Map ZZ ZZ)) :=
%CombineMap' [EmbedMap HomNN_RepresentOfFractionCMonoidableSet ; RepresentOfFractionCMonoid _ _ _].

Theorem NZMap_to_ZZMapTheorem : forall (f : #(%Homomorphism_of_BOpe [NNAdd;ZZAdd])) m n,
%(%NZMap_to_ZZMap f) (%NNNN_to_ZZ [m;n]) ==
%ZZAdd [%(f{<HomBOpe_Map}) m ; %Minus_of_ZZ (%(f{<HomBOpe_Map}) n)].
Proof.
intros f m n.
unfold NZMap_to_ZZMap.
rewrite (MapEq (CombineMap'Theorem _ _ _ _ _ _)).
rewrite (MapArgEq _ (NNNN_to_ZZ_is_Fraction _ _)).
apply (TransitivityEq (%(ZZAdd_CGrp{<CGrp_Monoid}{<Monoid_Ope}) [%(%(EmbedMap HomNN_RepresentOfFractionCMonoidableSet) f){<RepresentOfFCM_Map} m ; (%Minus_of_ZZ (%(f{<HomBOpe_Map}) n))])).
 apply RepresentOfFractionCMonoidTheorem.
 cut (&&(%IsInverseE ZZAdd) (%(f{<HomBOpe_Map}) n) (%Minus_of_ZZ (%(f{<HomBOpe_Map}) n))).
  apply RelRewriteAll.
    apply MapEqAll.
     rewrite USETEq.
     rewrite EmbedMapEq.
     hyperreflexivity.
    rewrite USETEq.
    rewrite USETEq.
    rewrite EmbedMapEq.
    hyperreflexivity.
   hyperreflexivity.
  apply MapArgEq.
  hyperreflexivity.
 apply Minus_of_ZZTheorem.
apply MapEqAll.
 apply EqualInPair'L.
 apply MapEq.
 rewrite USETEq.
 rewrite USETEq.
 rewrite EmbedMapEq.
 hyperreflexivity.
hyperreflexivity.
Qed. 

Theorem NZMap_to_ZZMapEq : forall (f : #(%Homomorphism_of_BOpe [NNAdd;ZZAdd])),
f == %CombineMap' [NN_to_ZZ ; %NZMap_to_ZZMap f].
Proof.
intro f.
unfold NN_to_ZZ.
unfold NZMap_to_ZZMap.
rewrite (USETEq' f HomNN_RepresentOfFractionCMonoidableSet).
rewrite (RepresentOfFractionCMonoidEq _ _ _).
apply MapArgEq.
apply EqualInPair'R.
rewrite CombineMap'Theorem.
apply MapArgEq.
rewrite EmbedMapEq.
hyperreflexivity.
Qed.

(*
Theorem NZMap_to_ZZMapEqWP : forall (f : #(Map NN ZZ)) (cond : In f (%Homomorphism_of_BOpe [NNAdd;ZZAdd])),
f == %CombineMap' [NN_to_ZZ ; %NZMap_to_ZZMap {f ! cond}].
Proof.
intros f cond.
apply (TransitivityEq {f ! cond}).
 hyperreflexivity.
rewrite NZMap_to_ZZMapEq.
hyperreflexivity.
Qed.

Theorem NZMap_to_ZZMapEq_Arg : forall (f : #(%Homomorphism_of_BOpe [NNAdd;ZZAdd])) a,
%(f{<HomBOpe_Map}) a == %(%NZMap_to_ZZMap f) (%NN_to_ZZ a).
Proof.
intros f a.
apply (TransitivityEq (%(%CombineMap' [NN_to_ZZ ; %NZMap_to_ZZMap f]) a)).
 apply MapEq.
 apply (TransitivityEq f).
  hyperreflexivity.
 apply NZMap_to_ZZMapEq.
rewrite CombineMap'Theorem.
hyperreflexivity.
Qed.

Theorem NZMap_to_ZZMapEqWP_Arg : forall (f : #(Map NN ZZ)) (cond : In f (%Homomorphism_of_BOpe [NNAdd;ZZAdd])) a,
%f a == %(%NZMap_to_ZZMap {f ! cond}) (%NN_to_ZZ a).
Proof.
intros f cond a.
apply (TransitivityEq (%(%CombineMap' [NN_to_ZZ ; %NZMap_to_ZZMap {f ! cond}]) a)).
 apply MapEq.
 apply NZMap_to_ZZMapEqWP.
rewrite CombineMap'Theorem.
hyperreflexivity.
Qed.
*)

(*
Theorem NZMap_to_ZZMapEq : forall (f : #(Map NN ZZ)) (g1 g2 : #(Map ZZ ZZ)),
&&IsHomomorphism_of_BOpe [NNAdd;ZZAdd] f ->
&&IsHomomorphism_of_BOpe [ZZAdd;ZZAdd] g1 ->
&&IsHomomorphism_of_BOpe [ZZAdd;ZZAdd] g2 ->
f == %CombineMap' [NN_to_ZZ ; g1] ->
f == %CombineMap' [NN_to_ZZ ; g2] ->
g1 == g2.
Proof.
intros f g1 g2.
intros conf cong1 cong2.
apply (RepresentOfFractionCMonoid_Eq NNAdd_CMonoid (ZZAdd_CGrp{<CGrp_Monoid}) NNSubCMonoid).
 apply HomNN_RepresentOfFractionCMonoidableSet.
 apply Homomorphism_of_BOpeTheorem.
 apply conf.
apply cong1.
apply cong2.
Qed.
*)

Theorem NZMap_to_ZZMapHom : forall (f : #(%Homomorphism_of_BOpe [NNAdd;ZZAdd])),
&&IsHomomorphism_of_BOpe [ZZAdd;ZZAdd] (%NZMap_to_ZZMap f).
Proof.
intros f.
unfold NZMap_to_ZZMap.
apply (RelRewriteR' (CombineMap'Theorem _ _ _ _ _ _)).
generalize (RepresentOfFractionCMonoid_HomBOpe NNAdd_CMonoid (ZZAdd_CGrp{<CGrp_Monoid}) NNSubCMonoid (%(EmbedMap HomNN_RepresentOfFractionCMonoidableSet) f)).
apply RelRewriteAll; hyperreflexivity.
Qed.

Theorem NNNNHomomorphism_to_NNZZHomomorphism:forall (f : #(%Homomorphism_of_BOpe [NNAdd;NNAdd])),
In (%CombineMap' [f{<HomBOpe_Map};NN_to_ZZ]) (%Homomorphism_of_BOpe [NNAdd;ZZAdd]).
Proof.
intros f.
apply Homomorphism_of_BOpeTheorem.
apply (CombIsHomomorphis_of_BOpe NNAdd NNAdd ZZAdd).
apply Homomorphism_of_BOpeTheorem.
apply (SetProp f).
apply NNAdd_to_ZZAdd_Hom.
Qed.

Definition NNMap_to_ZZMap_Cls (f : #(%Homomorphism_of_BOpe [NNAdd;NNAdd])) : #(Map ZZ ZZ) :=
%NZMap_to_ZZMap {_!NNNNHomomorphism_to_NNZZHomomorphism f}.

Theorem NNMap_to_ZZMap_ClsRFun : RFun NNMap_to_ZZMap_Cls.
Proof.
intros f1 f2 Eqf.
unfold NNMap_to_ZZMap_Cls.
apply MapArgEq.
rewrite DSETEq.
rewrite DSETEq.
apply MapArgEq.
apply EqualInPair'L.
apply Eqf.
Qed.

Definition NNMap_to_ZZMap : #(Map (%Homomorphism_of_BOpe [NNAdd;NNAdd]) (Map ZZ ZZ)) :=
MakeMap _ _ _ NNMap_to_ZZMap_ClsRFun.

Theorem NNMap_to_ZZMapEq : forall (f : #(%Homomorphism_of_BOpe [NNAdd;NNAdd])),
%CombineMap' [f{<HomBOpe_Map} ; NN_to_ZZ] == %CombineMap' [NN_to_ZZ ; %NNMap_to_ZZMap f].
Proof.
intro f.
rewrite (MapArgEq _ (EqualInPair'R _ _ _ _ _(MakeMapTheorem _ _ NNMap_to_ZZMap_Cls NNMap_to_ZZMap_ClsRFun _))).
unfold NNMap_to_ZZMap_Cls.
rewrite <- NZMap_to_ZZMapEq.
rewrite DSETEq.
hyperreflexivity.
Qed.

(*
Theorem NNMap_to_ZZMapEqWP : forall (f : #(Map NN NN)) (cond : In f (%Homomorphism_of_BOpe [NNAdd;NNAdd])),
%CombineMap' [f ; NN_to_ZZ] == %CombineMap' [NN_to_ZZ ; %NNMap_to_ZZMap {f ! cond}].
Proof.
intros f cond.
rewrite <- NNMap_to_ZZMapEq.
hyperreflexivity.
Qed.

Theorem NNMap_to_ZZMapEq_Arg : forall (f : #(%Homomorphism_of_BOpe [NNAdd;NNAdd])) n,
%NN_to_ZZ (%(f{<HomBOpe_Map}) n) ==
%(%NNMap_to_ZZMap f) (%NN_to_ZZ n).
Proof.
intros f n.
apply (TransitivityEq (%(%CombineMap' [f{<HomBOpe_Map} ; NN_to_ZZ]) n)).
 rewrite CombineMap'Theorem.
 hyperreflexivity.
rewrite (MapEq (NNMap_to_ZZMapEq _)).
rewrite CombineMap'Theorem.
hyperreflexivity.
Qed.

Theorem NNMap_to_ZZMapEqWP_Arg : forall (f : #(Map NN NN)) (cond : In f (%Homomorphism_of_BOpe [NNAdd;NNAdd])) a,
%NN_to_ZZ (%f a) ==
%(%NNMap_to_ZZMap {f ! cond}) (%NN_to_ZZ a).
Proof.
intros f cond a.
apply (TransitivityEq (%(%CombineMap' [f ; NN_to_ZZ]) a)).
 rewrite CombineMap'Theorem.
 hyperreflexivity.
rewrite (MapEq (NNMap_to_ZZMapEqWP f cond)).
rewrite CombineMap'Theorem.
hyperreflexivity.
Qed.
*)

Theorem NNMap_to_ZZMapTheorem : forall m n (f : #(%Homomorphism_of_BOpe [NNAdd;NNAdd])),
%(%NNMap_to_ZZMap f) (%NNNN_to_ZZ [m;n]) ==
%ZZAdd [%NN_to_ZZ (%(f{<HomBOpe_Map}) m) ; %Minus_of_ZZ (%NN_to_ZZ (%(f{<HomBOpe_Map}) n))].
Proof.
intros m n f.
unfold NNMap_to_ZZMap.
rewrite (MapEq (MakeMapTheorem _ _ _ _ _)).
unfold NNMap_to_ZZMap_Cls.
rewrite NZMap_to_ZZMapTheorem.
apply (TransitivityEq (%ZZAdd [%(%CombineMap' [f{<HomBOpe_Map} ; NN_to_ZZ]) m ; %Minus_of_ZZ (%(%CombineMap' [f{<HomBOpe_Map} ; NN_to_ZZ]) n)])).
 hyperreflexivity.
apply MapArgEq.
apply EqualInPair'.
split.
rewrite CombineMap'Theorem.
hyperreflexivity.
apply MapArgEq.
rewrite CombineMap'Theorem.
hyperreflexivity.
Qed.

(*
Theorem NNMap_to_ZZMapEq : forall (f : #(Map NN NN)) (g1 g2 : #(Map ZZ ZZ)),
&&IsHomomorphism_of_BOpe [NNAdd;NNAdd] f ->
&&IsHomomorphism_of_BOpe [ZZAdd;ZZAdd] g1 ->
&&IsHomomorphism_of_BOpe [ZZAdd;ZZAdd] g2 ->
%CombineMap' [f ; NN_to_ZZ] == %CombineMap' [NN_to_ZZ ; g1] ->
%CombineMap' [f ; NN_to_ZZ] == %CombineMap' [NN_to_ZZ ; g2] ->
g1 == g2.
Proof.
intros f g1 g2.
intros conf cong1 cong2.
set (%CombineMap' [f;NN_to_ZZ]) as f'.
apply (NZMap_to_ZZMapEq f' g1 g2).
 apply (CombIsHomomorphis_of_BOpe NNAdd NNAdd ZZAdd).
 apply conf.
apply NNAdd_to_ZZAdd_Hom.
apply cong1.
apply cong2.
Qed.
*)

Theorem NNMap_to_ZZMapHom : forall (f : #(%Homomorphism_of_BOpe [NNAdd;NNAdd])),
&&IsHomomorphism_of_BOpe [ZZAdd;ZZAdd] (%NNMap_to_ZZMap f).
Proof.
intro f.
cut (&&IsHomomorphism_of_BOpe [ZZAdd;ZZAdd] (%NZMap_to_ZZMap {_!NNNNHomomorphism_to_NNZZHomomorphism f})).
 apply RelRewriteR.
 unfold NNMap_to_ZZMap.
 rewrite MakeMapTheorem.
 unfold NNMap_to_ZZMap_Cls.
 hyperreflexivity.
apply NZMap_to_ZZMapHom.
Qed.

(*************)
(* PreZZMult *)
(*************)
(*
   PreZZMult1 : #(Map NN (Map NN NN))
   PreZZMult2 : #(Map NN (Map ZZ ZZ))
   PreZZMult3 : #(Map ZZ (Map NN ZZ))
   PreZZMult4 : #(Map ZZ (Map ZZ ZZ))
*)

Definition PreZZMult1 : #(Map NN (Map NN NN)) := %Currying NNMult.

Theorem PreZZMult1Theorem : forall n m,
%(%PreZZMult1 n) m == %NNMult [n;m].
Proof.
intros n m.
unfold PreZZMult1.
rewrite CurryingTheorem.
hyperreflexivity.
Qed.

Theorem PreZZMult1HomCond :
In PreZZMult1 (RistableRMap NN (Map NN NN) (%Homomorphism_of_BOpe [NNAdd;NNAdd])).
Proof.
apply RistableRMapTheorem.
split.
 apply HomBOpe_Map.
intros n.
apply Homomorphism_of_BOpeTheorem.
apply IsHomomorphism_of_BOpeTheorem.
intros a b.
unfold PreZZMult1.
rewrite CurryingTheorem.
rewrite (proj1 (NNAdd_NNMultDistDond _ _ _)).
apply MapArgEq.
apply EqualInPair'.
split.
 rewrite CurryingTheorem.
 hyperreflexivity.

 rewrite CurryingTheorem.
 hyperreflexivity.
Qed.

Definition PreZZMult1Hom : #(Map NN (%Homomorphism_of_BOpe [NNAdd;NNAdd])) :=
%RistrictMapR {_!PreZZMult1HomCond}.

Definition PreZZMult2 : #(Map NN (Map ZZ ZZ)) :=
%CombineMap' [PreZZMult1Hom ; NNMap_to_ZZMap].

Theorem PreZZMult2Theorem : forall n a b,
%(%PreZZMult2 n) (%NNNN_to_ZZ [a;b]) ==
%ZZAdd [%NN_to_ZZ (%(%PreZZMult1 n) a) ; %Minus_of_ZZ (%NN_to_ZZ (%(%PreZZMult1 n) b))].
Proof.
intros n a b.
unfold PreZZMult2.
rewrite (MapEq (CombineMap'Theorem _ _ _ _ _ _)).
rewrite NNMap_to_ZZMapTheorem.
apply MapArgEq.
apply EqualInPair'.
unfold PreZZMult1Hom.
split.
 apply MapArgEq.
 apply MapEq.
 rewrite USETEq.
 apply MapEq.
 apply RistrictMapREq2.
apply MapArgEq.
apply MapArgEq.
apply MapEq.
rewrite USETEq.
apply MapEq.
apply RistrictMapREq2.
Qed.

(*
Theorem PreZZMult2Eq : forall (g1 g2 : #(Map ZZ ZZ)) n,
&&IsHomomorphism_of_BOpe [ZZAdd;ZZAdd] g1 ->
&&IsHomomorphism_of_BOpe [ZZAdd;ZZAdd] g2 ->
%CombineMap' [%PreZZMult1 n ; NN_to_ZZ] == %CombineMap' [NN_to_ZZ ; g1] ->
%CombineMap' [%PreZZMult1 n ; NN_to_ZZ] == %CombineMap' [NN_to_ZZ ; g2] ->
g1 == g2.
Proof.
intros g1 g2 n.
apply NNMap_to_ZZMapEq.
apply Homomorphism_of_BOpeTheorem.
apply RistableRMapTheoremIn.
apply PreZZMult1HomCond.
Qed.
*)
(*
Theorem PreZZMult2_Hom : forall n,
&&IsHomomorphism_of_BOpe [ZZAdd;ZZAdd] (%PreZZMult2 n).
Proof.
intro n.
apply Homomorphism_of_BOpeTheorem.
unfold PreZZMult2.
rewrite CombineMap'Theorem.
put (NNMap_to_ZZMapHom (%PreZZMult1Hom n)) HomH.
apply Homomorphism_of_BOpeTheorem.
apply HomH.
Qed.

Theorem PreZZMult2LeftDist : forall a b c,
%(%PreZZMult2 a) (%ZZAdd [b;c]) ==
%ZZAdd [%(%PreZZMult2 a) b ; %(%PreZZMult2 a) c].
Proof.
intros a b c.
put (PreZZMult2_Hom a) HomH.
put ((proj1 (IsHomomorphism_of_BOpeTheorem _ _ _)) HomH) HomH'.
apply HomH'.
Qed.

Theorem PreZZMult2z1 : forall n,
%(%PreZZMult2 n) (nat_to_ZZ 1) == %NN_to_ZZ n.
Proof.
intro n.
unfold nat_to_ZZ.
rewrite PreZZMult2Theorem.
apply MapArgEq.
unfold nat_to_NN.
rewrite NNMultTheorem1.
hyperreflexivity.
Qed.

Theorem PreZZMult2z0 : forall n,
%(%PreZZMult2 n) (nat_to_ZZ 0) == (nat_to_ZZ 0).
Proof.
intro n.
cut (%ZZAdd [%NN_to_ZZ n ; %(%PreZZMult2 n) (nat_to_ZZ 0)] == %NN_to_ZZ n).
 intro EqH.
 apply (TransitivityEq (%ZZAdd [%ZZAdd[%Minus_of_ZZ (%NN_to_ZZ n) ; %NN_to_ZZ n] ; %(%PreZZMult2 n) (nat_to_ZZ 0)])).
  apply SymmetryEq.
  apply IsLeftIdentTheorem.
  apply IsIdent_LeftIdent.
  generalize (Minus_of_ZZTheorem (%NN_to_ZZ n)).
  intro InvH.
  apply IsInverseETheorem in InvH.
  apply (proj2 InvH).
 rewrite ZZAdd_SGrpCond.
 rewrite (MapArgEq _ (EqualInPair'R _ _ _ _ _ EqH)).
 apply (TransitivityEq (MIdent_of_CGrp (ZZAdd_CGrp))).
  apply SymmetryEq.
  apply MIdentEq.
  put (Minus_of_ZZTheorem (%NN_to_ZZ n)) InvH.
  apply IsInverseETheorem in InvH.
  apply (proj2 InvH).
 apply MIdentEq.
 generalize ZZ0IsIdent.
 apply RelRewriteAll; hyperreflexivity.
rewrite <- (MapArgEq _ (EqualInPair'L _ _ _ _ _ (PreZZMult2z1 _))).
rewrite <- PreZZMult2LeftDist.
rewrite <- PreZZMult2z1.
apply MapArgEq.
apply IsRightIdentTheorem.
apply IsIdent_RightIdent.
apply ZZ0IsIdent.
Qed.

Theorem PreZZMult2n0 : forall a,
%(%PreZZMult2 (nat_to_NN 0)) a == (nat_to_ZZ 0).
Proof.
intro a.
set (%(@ConstMap ZZ ZZ) (nat_to_ZZ 0)) as Const0.
assert(Map_Eq : (%PreZZMult2 (nat_to_NN 0)) == Const0).
 apply (PreZZMult2Eq _ _ (nat_to_NN 0)).

 apply PreZZMult2_Hom.

 apply IsHomomorphism_of_BOpeTheorem.
 intros n m.
 unfold Const0.
 rewrite ConstMapTheorem.
 rewrite (MapArgEq _ (EqualInPair'L _ _ _ _ _ (ConstMapTheorem _ _))).
 rewrite (MapArgEq _ (EqualInPair'R _ _ _ _ _ (ConstMapTheorem _ _))).
 apply SymmetryEq.
 apply IsLeftIdentTheorem.
 apply IsIdent_LeftIdent.
 apply ZZ0IsIdent.

 apply MapEquality.
  hyperreflexivity.
 intros n m Eqnm.
 rewrite CombineMap'Theorem.
 rewrite CombineMap'Theorem.
 rewrite PreZZMult2Theorem.
 apply MapArgEq.
 unfold PreZZMult1.
 rewrite CurryingTheorem.
 apply MapArgEq.
 apply EqualInPair'R.
 apply Eqnm.

 unfold Const0.
 apply MapEquality.
  hyperreflexivity.
 intros n m Eqnm.
 rewrite CombineMap'Theorem.
 rewrite CombineMap'Theorem.
 rewrite ConstMapTheorem.
 unfold PreZZMult1.
 rewrite (MapArgEq _ (CurryingTheorem _ _ _)).
 apply MapArgEq.
 rewrite NNMult_Ope_CommCond.
 rewrite NNMultTheorem0.
 hyperreflexivity.
rewrite (MapEq Map_Eq).
unfold Const0.
rewrite ConstMapTheorem.
hyperreflexivity.
Qed.

Theorem PreZZMult2Next : forall n m,
%(%PreZZMult2 (%NNNext n)) m == %ZZAdd [%(%PreZZMult2 n) m ; m].
Proof.
intros n m.
set (%CombineMap' [%CartesianDMap [IdMap ; %PreZZMult2 n] ; ZZAdd]) as F.
assert(Eq_Map : %PreZZMult2 (%NNNext n) == F).
 apply (PreZZMult2Eq _ _ (%NNNext n)).

 apply PreZZMult2_Hom.

 apply IsHomomorphism_of_BOpeTheorem.
 intros x y.
 unfold F.
 rewrite CombineMap'Theorem.
 rewrite (MapArgEq _ (CartesianDMapTheorem _ _ _)).
 rewrite (MapArgEq _ (EqualInPair'L _ _ _ _ _ (IdMapTheorem _ _))).
 apply SymmetryEq.
 apply (TransitivityEq (%ZZAdd [%ZZAdd [x;%(%PreZZMult2 n) x] ; %ZZAdd [y;%(%PreZZMult2 n) y]])).
  apply MapArgEq.
  apply EqualInPair'.
  split.
   rewrite CombineMap'Theorem.
   apply MapArgEq.
   rewrite CartesianDMapTheorem.
   apply EqualInPair'L.
   rewrite IdMapTheorem.
   hyperreflexivity.

   rewrite CombineMap'Theorem.
   apply MapArgEq.
   rewrite CartesianDMapTheorem.
   apply EqualInPair'L.
   rewrite IdMapTheorem.
   hyperreflexivity.
 apply (TransitivityEq (%ZZAdd [%ZZAdd [x;y] ; %ZZAdd [%(%PreZZMult2 n) x ; %(%PreZZMult2 n) y]])).
  rewrite ZZAdd_SGrpCond.
  apply SymmetryEq.
  rewrite ZZAdd_SGrpCond.
  apply MapArgEq.
  apply EqualInPair'R.
  rewrite <- ZZAdd_SGrpCond.
  apply SymmetryEq.
  rewrite <- ZZAdd_SGrpCond.
  apply MapArgEq.
  apply EqualInPair'L.
  apply ZZAdd_CommCond.
 apply MapArgEq.
 apply EqualInPair'R.
 apply SymmetryEq.
 apply PreZZMult2LeftDist.

 apply MapEquality.
  hyperreflexivity.
 intros a b Eqab.
 rewrite CombineMap'Theorem.
 rewrite CombineMap'Theorem.
 rewrite PreZZMult2Theorem.
 apply MapArgEq.
 unfold NNMult.
 unfold PreZZMult1.
 rewrite CurryingTheorem.
 apply MapArgEq.
 apply EqualInPair'R.
 apply Eqab.

 unfold F.
 apply MapEquality.
  hyperreflexivity.
 intros a b Eqab.
 rewrite CombineMap'Theorem.
 apply SymmetryEq.
 rewrite CombineMap'Theorem.
 rewrite CombineMap'Theorem.
 rewrite (MapArgEq _ (CartesianDMapTheorem _ _ _)).
 rewrite (MapArgEq _ (EqualInPair'L _ _ _ _ _ (IdMapTheorem _ _))).
 rewrite (MapArgEq _ (EqualInPair'R _ _ _ _ _ (PreZZMult2Theorem _ _))).
 unfold PreZZMult1.
 rewrite (MapArgEq _ (CurryingTheorem _ _ _)).
 apply SymmetryEq.
 rewrite (MapArgEq _ (MapArgEq _ (EqualInPair'R _ _ _ _ _ Eqab))).
 rewrite (MapArgEq _ (NNMult_Ope_CommCond _ _)).
 rewrite (MapArgEq _ (NNMultTheorem2 _ _)).
 put NNAdd_to_ZZAdd_Hom Hom.
 put ((proj1 (IsHomomorphism_of_BOpeTheorem _ _ _)) Hom) Hom'.
 rewrite Hom'.
 rewrite ZZAdd_CommCond.
 apply MapArgEq.
 apply EqualInPair'R.
 apply MapArgEq.
 apply NNMult_Ope_CommCond.
rewrite (MapEq Eq_Map).
unfold F.
rewrite CombineMap'Theorem.
rewrite (MapArgEq _ (CartesianDMapTheorem _ _ _)).
rewrite ZZAdd_CommCond.
rewrite (MapArgEq _ (EqualInPair'R _ _ _ _ _ (IdMapTheorem _ _))).
hyperreflexivity.
Qed.
*)

Theorem PreZZMult2RightDist : forall a b c,
%(%PreZZMult2 (%NNAdd [a;b])) c ==
%ZZAdd [%(%PreZZMult2 a) c ; %(%PreZZMult2 b) c].
Proof.
intros a b c.
put (ZZIsNNNN c) Eqc.
destruct Eqc as [m Eqc].
destruct Eqc as [n Eqc].
rewrite (MapArgEq _ Eqc).
rewrite PreZZMult2Theorem.
rewrite (MapArgEq _ (EqualInPair'L _ _ _ _ _ (MapArgEq _ (PreZZMult1Theorem _ _)))).
rewrite (MapArgEq _ (EqualInPair'L _ _ _ _ _ (MapArgEq _ (NNAdd_NNMultRDistDond _ _ _)))).
rewrite (MapArgEq _ (EqualInPair'L _ _ _ _ _ (ZZAdd_comm_NNAdd _ _))).
rewrite (MapArgEq _ (EqualInPair'R _ _ _ _ _ (MapArgEq _ (MapArgEq _ (PreZZMult1Theorem _ _))))).
rewrite (MapArgEq _ (EqualInPair'R _ _ _ _ _ (MapArgEq _ (MapArgEq _ (NNAdd_NNMultRDistDond _ _ _))))).
rewrite (MapArgEq _ (EqualInPair'R _ _ _ _ _ (MapArgEq _ (ZZAdd_comm_NNAdd _ _)))).
rewrite (MapArgEq _ (EqualInPair'R _ _ _ _ _ (Minus_of_ZZDist _ _))).
apply SymmetryEq.
rewrite (MapArgEq _ (EqualInPair'L _ _ _ _ _ (MapArgEq _ Eqc))).
rewrite (MapArgEq _ (EqualInPair'L _ _ _ _ _ (PreZZMult2Theorem _ _ _))).
rewrite (MapArgEq _ (EqualInPair'L _ _ _ _ _ (MapArgEq _ (EqualInPair'L _ _ _ _ _ (MapArgEq _ (PreZZMult1Theorem _ _)))))).
rewrite (MapArgEq _ (EqualInPair'L _ _ _ _ _ (MapArgEq _ (EqualInPair'R _ _ _ _ _ (MapArgEq _ (MapArgEq _ (PreZZMult1Theorem _ _))))))).
rewrite (MapArgEq _ (EqualInPair'R _ _ _ _ _ (MapArgEq _ Eqc))).
rewrite (MapArgEq _ (EqualInPair'R _ _ _ _ _ (PreZZMult2Theorem _ _ _))).
rewrite (MapArgEq _ (EqualInPair'R _ _ _ _ _ (MapArgEq _ (EqualInPair'L _ _ _ _ _ (MapArgEq _ (PreZZMult1Theorem _ _)))))).
rewrite (MapArgEq _ (EqualInPair'R _ _ _ _ _ (MapArgEq _ (EqualInPair'R _ _ _ _ _ (MapArgEq _ (MapArgEq _ (PreZZMult1Theorem _ _))))))).
rewrite ZZAdd_SGrpCond.
apply SymmetryEq.
rewrite ZZAdd_SGrpCond.
apply MapArgEq.
apply EqualInPair'R.
rewrite <- ZZAdd_SGrpCond.
apply SymmetryEq.
rewrite <- ZZAdd_SGrpCond.
apply MapArgEq.
apply EqualInPair'L.
apply ZZAdd_CommCond.
Qed.

(*
Theorem PreZZMult2Assoc : forall n m,
%CombineMap' [%PreZZMult2 n ; %PreZZMult2 m] == %PreZZMult2 (%NNMult [n;m]).
Proof.
intros n m.
apply (PreZZMult2Eq _ _ (%NNMult [n;m])).

apply (CombIsHomomorphis_of_BOpe ZZAdd ZZAdd ZZAdd);
 apply PreZZMult2_Hom.

apply PreZZMult2_Hom.

apply MapEquality.
 hyperreflexivity.
intros a b Eqab.
rewrite CombineMap'Theorem.
apply SymmetryEq.
rewrite CombineMap'Theorem.
rewrite CombineMap'Theorem.
rewrite (MapArgEq _ (PreZZMult2Theorem _ _)).
rewrite PreZZMult2Theorem.
apply MapArgEq.
apply SymmetryEq.
unfold PreZZMult1.
rewrite CurryingTheorem.
rewrite (MapArgEq _ (EqualInPair'L _ _ _ _ _ (NNMult_Ope_CommCond _ _))).
rewrite NNMult_Ope_SGrpCond.
apply MapArgEq.
apply EqualInPair'R.
apply MapArgEq.
apply EqualInPair'R.
apply Eqab.

apply MapEquality.
 hyperreflexivity.
intros a b Eqab.
rewrite CombineMap'Theorem.
apply SymmetryEq.
rewrite CombineMap'Theorem.
rewrite PreZZMult2Theorem.
apply MapArgEq.
apply SymmetryEq.
unfold PreZZMult1.
rewrite CurryingTheorem.
apply MapArgEq.
apply EqualInPair'R.
apply Eqab.
Qed.
*)

Definition PreZZMult3 : #(Map ZZ (Map NN ZZ)) :=
%Currying (%InverseBinaryMap (%Uncurrying PreZZMult2)).

Theorem PreZZMult3Theorem : forall n z,
%(%PreZZMult3 n) z == %(%PreZZMult2 z) n.
Proof.
intros n z.
unfold PreZZMult3.
rewrite CurryingTheorem.
rewrite InverseBinaryMapTheorem.
rewrite UncurryingTheorem.
hyperreflexivity.
Qed.

Theorem PreZZMult3HomCond :
In PreZZMult3 (RistableRMap ZZ (Map NN ZZ) (%Homomorphism_of_BOpe [NNAdd;ZZAdd])).
Proof.
apply RistableRMapTheorem.
split.
 apply HomBOpe_Map.
intros z.
apply Homomorphism_of_BOpeTheorem.
apply IsHomomorphism_of_BOpeTheorem.
intros n m.
rewrite PreZZMult3Theorem.
rewrite (MapArgEq _ (EqualInPair'L _ _ _ _ _ (PreZZMult3Theorem _ _))).
rewrite (MapArgEq _ (EqualInPair'R _ _ _ _ _ (PreZZMult3Theorem _ _))).
apply PreZZMult2RightDist.
Qed.

Definition PreZZMult3Hom : #(Map ZZ (%Homomorphism_of_BOpe [NNAdd;ZZAdd])) :=
%RistrictMapR {_ ! PreZZMult3HomCond}.

Definition PreZZMult4 : #(Map ZZ (Map ZZ ZZ)) :=
%CombineMap' [PreZZMult3Hom ; NZMap_to_ZZMap].

Theorem PreZZMult4Theorem : forall a m n,
%(%PreZZMult4 a) (%NNNN_to_ZZ [m;n]) ==
%ZZAdd [%(%PreZZMult3 a) m ; %Minus_of_ZZ (%(%PreZZMult3 a) n)].
Proof.
intros a m n.
unfold PreZZMult4.
rewrite (MapEq (CombineMap'Theorem _ _ _ _ _ _)).
unfold PreZZMult3Hom.
rewrite NZMap_to_ZZMapTheorem.
apply MapArgEq.
apply EqualInPair'.
split.
 apply MapEq.
 rewrite USETEq.
 apply MapEq.
 apply RistrictMapREq2.
apply MapArgEq.
apply MapEq.
rewrite USETEq.
apply MapEq.
apply RistrictMapREq2.
Qed.

(*
Theorem PreZZMult4Eq : forall (g1 g2 : #(Map ZZ ZZ)) a,
&&IsHomomorphism_of_BOpe [ZZAdd;ZZAdd] g1 ->
&&IsHomomorphism_of_BOpe [ZZAdd;ZZAdd] g2 ->
%PreZZMult3 a == %CombineMap' [NN_to_ZZ ; g1] ->
%PreZZMult3 a == %CombineMap' [NN_to_ZZ ; g2] ->
g1 == g2.
Proof.
intros g1 g2 a.
apply NZMap_to_ZZMapEq.
apply Homomorphism_of_BOpeTheorem.
apply RistableRMapTheoremIn.
apply PreZZMult3HomCond.
Qed.

Theorem PreZZMult4_Hom : forall n,
&&IsHomomorphism_of_BOpe [ZZAdd;ZZAdd] (%PreZZMult4 n).
Proof.
intro n.
apply Homomorphism_of_BOpeTheorem.
unfold PreZZMult4.
rewrite CombineMap'Theorem.
put (NZMap_to_ZZMapHom (%PreZZMult3Hom n)) HomH.
apply Homomorphism_of_BOpeTheorem.
apply HomH.
Qed.

Theorem PreZZMult4LeftDist : forall a b c,
%(%PreZZMult4 a) (%ZZAdd [b;c]) ==
%ZZAdd [%(%PreZZMult4 a) b ; %(%PreZZMult4 a) c].
Proof.
intros a b c.
put (PreZZMult4_Hom a) HomH.
put ((proj1 (IsHomomorphism_of_BOpeTheorem _ _ _)) HomH) HomH'.
apply HomH'.
Qed.

Theorem PreZZMult4_z1 : forall a,
%(%PreZZMult4 a) (nat_to_ZZ 1) == a.
Proof.
intro a.
apply (TransitivityEq (%(%PreZZMult4 a) (%NN_to_ZZ (nat_to_NN 1)))).
 apply MapArgEq.
 hyperreflexivity.
rewrite PreZZMult4Theorem.
rewrite PreZZMult3Theorem.
unfold nat_to_NN.
rewrite PreZZMult2Next.
rewrite (MapArgEq _ (EqualInPair'L _ _ _ _ _ (PreZZMult2n0 _))).
apply IsLeftIdentTheorem.
apply IsIdent_LeftIdent.
apply ZZ0IsIdent.
Qed.

Theorem PreZZMult4_z0 : forall a,
%(%PreZZMult4 a) (nat_to_ZZ 0) == (nat_to_ZZ 0).
Proof.
intro a.
apply (TransitivityEq (%(%PreZZMult4 a) (%NN_to_ZZ (nat_to_NN 0)))).
 apply MapArgEq.
 hyperreflexivity.
rewrite PreZZMult4Theorem.
rewrite PreZZMult3Theorem.
rewrite PreZZMult2n0.
hyperreflexivity.
Qed.

Theorem PreZZMult4z1 : forall a,
%(%PreZZMult4 (nat_to_ZZ 1)) a == a.
Proof.
intro a.
assert(Map_Eq : (%PreZZMult4 (nat_to_ZZ 1)) == (@IdMap ZZ)).
 apply (PreZZMult4Eq _ _ (nat_to_ZZ 1)).

 apply PreZZMult4_Hom.

 apply IsHomomorphism_of_BOpeTheorem.
 intros x y.
 rewrite IdMapTheorem.
 apply SymmetryEq.
 rewrite (MapArgEq _ (EqualInPair'L _ _ _ _ _ (IdMapTheorem _ _))).
 rewrite (MapArgEq _ (EqualInPair'R _ _ _ _ _ (IdMapTheorem _ _))).
 hyperreflexivity.

 apply MapEquality.
  hyperreflexivity.
 intros n m Eqnm.
 apply SymmetryEq.
 rewrite CombineMap'Theorem.
 rewrite PreZZMult4Theorem.
 apply MapArgEq.
 apply SymmetryEq.
 apply Eqnm.

 apply MapEquality.
  hyperreflexivity.
 intros n m Eqnm.
 apply SymmetryEq.
 rewrite CombineMap'Theorem.
 rewrite IdMapTheorem.
 apply SymmetryEq.
 rewrite PreZZMult3Theorem.
 rewrite PreZZMult2z1.
 apply MapArgEq.
 apply Eqnm.

rewrite (MapEq Map_Eq).
rewrite IdMapTheorem.
hyperreflexivity.
Qed.

(*
Theorem PreZZMult4z0 : forall a,
%(%PreZZMult4 (nat_to_ZZ 0)) a == (nat_to_ZZ 0).
Proof.
intro a.
apply (TransitivityEq (%(%PreZZMult4 (%NN_to_ZZ (nat_to_NN 0))) a)).
 apply MapArgEq.
 hyperreflexivity.
rewrite PreZZMult4Theorem.
rewrite PreZZMult3Theorem.
rewrite PreZZMult2n0.
hyperreflexivity.
Qed.
*)

Theorem PreZZMult4RightDist : forall a b c,
%(%PreZZMult4 (%ZZAdd [a;b])) c ==
%ZZAdd [%(%PreZZMult4 a) c ; %(%PreZZMult4 b) c].
Proof.
intros a b c.
assert(EqP : %PreZZMult4 (%ZZAdd[a;b]) == %CombineMap' [%CartesianDMap [%PreZZMult4 a ; %PreZZMult4 b] ; ZZAdd]).
 apply (PreZZMult4Eq _ _ (%ZZAdd[a;b])).

 apply PreZZMult4_Hom.

 apply IsHomomorphism_of_BOpeTheorem.
 intros x y.
 rewrite CombineMap'Theorem.
 rewrite (MapArgEq _ (CartesianDMapTheorem _ _ _)).
 apply SymmetryEq.
 apply (TransitivityEq (%ZZAdd [%ZZAdd [%(%PreZZMult4 a) x ; %(%PreZZMult4 b) x] ; %ZZAdd [%(%PreZZMult4 a) y ; %(%PreZZMult4 b) y]])).
  apply MapArgEq.
  apply EqualInPair'.
  split.
   rewrite CombineMap'Theorem.
   rewrite (MapArgEq _ (CartesianDMapTheorem _ _ _)).
   hyperreflexivity.

   rewrite CombineMap'Theorem.
   rewrite (MapArgEq _ (CartesianDMapTheorem _ _ _)).
   hyperreflexivity.
 apply SymmetryEq.
 rewrite (MapArgEq _ (EqualInPair'L _ _ _ _ _ (PreZZMult4LeftDist _ _ _))).
 rewrite (MapArgEq _ (EqualInPair'R _ _ _ _ _ (PreZZMult4LeftDist _ _ _))).
 rewrite ZZAdd_SGrpCond.
 apply SymmetryEq.
 rewrite ZZAdd_SGrpCond.
 apply MapArgEq.
 apply EqualInPair'R.
 rewrite <- ZZAdd_SGrpCond.
 apply SymmetryEq.
 rewrite <- ZZAdd_SGrpCond.
 apply MapArgEq.
 apply EqualInPair'L.
 apply ZZAdd_CommCond.

 apply MapEquality.
  hyperreflexivity.
 intros x y Eqxy.
 apply SymmetryEq.
 rewrite CombineMap'Theorem.
 rewrite PreZZMult4Theorem.
 apply MapArgEq.
 apply SymmetryEq.
 apply Eqxy.

 apply MapEquality.
  hyperreflexivity.
 intros n m Eqnm.
 apply SymmetryEq.
 rewrite CombineMap'Theorem.
 rewrite CombineMap'Theorem.
 rewrite (MapArgEq _ (CartesianDMapTheorem _ _ _)).
 rewrite (MapArgEq _ (EqualInPair'L _ _ _ _ _ (PreZZMult4Theorem _ _))).
 rewrite (MapArgEq _ (EqualInPair'R _ _ _ _ _ (PreZZMult4Theorem _ _))).
 rewrite (MapArgEq _ (EqualInPair'L _ _ _ _ _ (PreZZMult3Theorem _ _))).
 rewrite (MapArgEq _ (EqualInPair'R _ _ _ _ _ (PreZZMult3Theorem _ _))).
 apply SymmetryEq.
 rewrite PreZZMult3Theorem.
 apply (TransitivityEq (%(%PreZZMult2 m) (%ZZAdd [a;b]))).
  apply MapEq.
  apply MapArgEq.
  apply Eqnm.
 apply PreZZMult2LeftDist.

rewrite (MapEq EqP).
rewrite CombineMap'Theorem.
rewrite (MapArgEq _ (CartesianDMapTheorem _ _ _)).
hyperreflexivity.
Qed.
*)
(************)
(** ZZMult **)
(************)

Definition ZZMultInv : #(BOperation ZZ) :=
%Uncurrying PreZZMult4.

Theorem ZZMultInv_is_PreZZMult4 : forall a b,
%ZZMultInv [a;b] == %(%PreZZMult4 a) b.
Proof.
intros a b.
unfold ZZMultInv.
rewrite UncurryingTheorem.
hyperreflexivity.
Qed.

Definition ZZMult : #(BOperation ZZ) :=
%InverseBinaryMap ZZMultInv.

Theorem ZZMult_is_ZZMultInv : forall a b,
%ZZMult [a;b] == %ZZMultInv [b;a].
Proof.
intros a b.
unfold ZZMult.
apply InverseBinaryMapTheorem.
Qed.

Theorem ZZMultTheorem_NNNN : forall a b c d,
%ZZMult [%NNNN_to_ZZ [a;b] ; %NNNN_to_ZZ [c;d]] ==
%NNNN_to_ZZ [%NNAdd [%NNMult [a;c] ; %NNMult [b;d]] ; %NNAdd [%NNMult [a;d] ; %NNMult [b;c]]].
Proof.
intros a b c d.
rewrite ZZMult_is_ZZMultInv.
rewrite ZZMultInv_is_PreZZMult4.
rewrite PreZZMult4Theorem.
rewrite (MapArgEq _ (EqualInPair'L _ _ _ _ _ (PreZZMult3Theorem _ _))).
rewrite (MapArgEq _ (EqualInPair'R _ _ _ _ _ (MapArgEq _ (PreZZMult3Theorem _ _)))).
rewrite (MapArgEq _ (EqualInPair'L _ _ _ _ _ (PreZZMult2Theorem _ _ _))).
rewrite (MapArgEq _ (EqualInPair'R _ _ _ _ _ (MapArgEq _ (PreZZMult2Theorem _ _ _)))).
rewrite (MapArgEq _ (EqualInPair'L _ _ _ _ _ (MapArgEq _ (EqualInPair'L _ _ _ _ _ (MapArgEq _ (PreZZMult1Theorem _ _)))))).
rewrite (MapArgEq _ (EqualInPair'L _ _ _ _ _ (MapArgEq _ (EqualInPair'R _ _ _ _ _ (MapArgEq _ (MapArgEq _ (PreZZMult1Theorem _ _))))))).
rewrite (MapArgEq _ (EqualInPair'R _ _ _ _ _ (MapArgEq _ (MapArgEq _ (EqualInPair'L _ _ _ _ _ (MapArgEq _ (PreZZMult1Theorem _ _))))))).
rewrite (MapArgEq _ (EqualInPair'R _ _ _ _ _ (MapArgEq _ (MapArgEq _ (EqualInPair'R _ _ _ _ _ (MapArgEq _ (MapArgEq _ (PreZZMult1Theorem _ _)))))))).
apply SymmetryEq.
rewrite NNNN_to_ZZTheorem.
rewrite (MapArgEq _ (EqualInPair'L _ _ _ _ _ (ZZAdd_comm_NNAdd _ _))).
rewrite (MapArgEq _ (EqualInPair'R _ _ _ _ _ (MapArgEq _ (ZZAdd_comm_NNAdd _ _)))).
rewrite ZZAdd_SGrpCond.
apply SymmetryEq.
rewrite ZZAdd_SGrpCond.
apply MapArgEq.
apply EqualInPair'R.
rewrite (MapArgEq _ (EqualInPair'R _ _ _ _ _ (Minus_of_ZZDist _ _))).
rewrite <- ZZAdd_SGrpCond.
rewrite ZZAdd_CommCond.
rewrite (MapArgEq _ (EqualInPair'L _ _ _ _ _ (DoubleMinus_of_ZZ _))).
apply MapArgEq.
apply EqualInPair'R.
apply SymmetryEq.
rewrite Minus_of_ZZDist.
hyperreflexivity.
Qed.


Theorem NNMult_to_ZZMult_Hom :
&&IsHomomorphism_of_BOpe [NNMult;ZZMult] NN_to_ZZ.
Proof.
apply IsHomomorphism_of_BOpeTheorem.
intros n m.
apply SymmetryEq.
rewrite (MapArgEq _ (EqualInPair'L _ _ _ _ _ (NN_to_ZZ_is_NNNN_to_ZZ _))).
rewrite (MapArgEq _ (EqualInPair'R _ _ _ _ _ (NN_to_ZZ_is_NNNN_to_ZZ _))).
rewrite ZZMultTheorem_NNNN.
apply (TransitivityEq (%NNNN_to_ZZ [%NNMult[n;m] ; nat_to_NN 0])).
 apply MapArgEq.
 apply EqualInPair'.
 split.
  apply IsRightIdentTheorem.
  apply IsIdent_RightIdent.
  generalize NN0IsIdent.
  apply RelRewriteR.
  rewrite NNMultTheorem0.
  hyperreflexivity.
 apply (TransitivityEq (%NNAdd [nat_to_NN 0 ; nat_to_NN 0])).
  apply MapArgEq.
  apply EqualInPair'.
  split.
  apply NNMultTheorem0.
  rewrite NNMult_Ope_CommCond.
  apply NNMultTheorem0.
 apply IsLeftIdentTheorem.
 apply IsIdent_LeftIdent.
 apply NN0IsIdent.
rewrite <- NN_to_ZZ_is_NNNN_to_ZZ.
hyperreflexivity.
Qed.

Theorem ZZMult_comm_NNMult : forall n1 n2,
%NN_to_ZZ (%NNMult [n1;n2]) ==
%ZZMult [%NN_to_ZZ n1 ; %NN_to_ZZ n2].
Proof.
put NNMult_to_ZZMult_Hom HomH.
put ((proj1 (IsHomomorphism_of_BOpeTheorem _ _ _)) HomH) comm.
apply comm.
Qed.

Theorem ZZMult_CommCond : Ope_CommCond ZZMult.
Proof.
intros a b.
put (ZZIsNNNN a) Eqa.
destruct Eqa as [s Eqa].
destruct Eqa as [t Eqa].
put (ZZIsNNNN b) Eqb.
destruct Eqb as [m Eqb].
destruct Eqb as [n Eqb].
rewrite (MapArgEq _ (EqualInPair'L _ _ _ _ _ Eqa)).
rewrite (MapArgEq _ (EqualInPair'R _ _ _ _ _ Eqb)).
rewrite (MapArgEq _ (EqualInPair'R _ _ _ _ _ Eqa)).
rewrite (MapArgEq _ (EqualInPair'L _ _ _ _ _ Eqb)).
rewrite ZZMultTheorem_NNNN.
rewrite ZZMultTheorem_NNNN.
rewrite (MapArgEq _ (EqualInPair'L _ _ _ _ _ (MapArgEq _ (EqualInPair'L _ _ _ _ _ (NNMult_Ope_CommCond _ _))))).
rewrite (MapArgEq _ (EqualInPair'L _ _ _ _ _ (MapArgEq _ (EqualInPair'R _ _ _ _ _ (NNMult_Ope_CommCond _ _))))).
rewrite (MapArgEq _ (EqualInPair'R _ _ _ _ _ (MapArgEq _ (EqualInPair'L _ _ _ _ _ (NNMult_Ope_CommCond _ _))))).
rewrite (MapArgEq _ (EqualInPair'R _ _ _ _ _ (MapArgEq _ (EqualInPair'R _ _ _ _ _ (NNMult_Ope_CommCond _ _))))).
apply MapArgEq.
apply EqualInPair'R.
apply NNAdd_Ope_CommCond.
Qed.

Theorem ZZMult_SGrpCond : Ope_SGrpCond ZZMult.
Proof.
intros x y z.
put (ZZIsNNNN x) Eqx.
destruct Eqx as [a Eqx].
destruct Eqx as [b Eqx].
put (ZZIsNNNN y) Eqy.
destruct Eqy as [c Eqy].
destruct Eqy as [d Eqy].
put (ZZIsNNNN z) Eqz.
destruct Eqz as [e Eqz].
destruct Eqz as [f Eqz].
rewrite (MapArgEq _ (EqualInPair'L _ _ _ _ _ (MapArgEq _ (EqualInPair'L _ _ _ _ _ Eqx)))).
rewrite (MapArgEq _ (EqualInPair'L _ _ _ _ _ (MapArgEq _ (EqualInPair'R _ _ _ _ _ Eqy)))).
rewrite (MapArgEq _ (EqualInPair'R _ _ _ _ _ Eqz)).
rewrite (MapArgEq _ (EqualInPair'L _ _ _ _ _ Eqx)).
rewrite (MapArgEq _ (EqualInPair'R _ _ _ _ _ (MapArgEq _ (EqualInPair'L _ _ _ _ _ Eqy)))).
rewrite (MapArgEq _ (EqualInPair'R _ _ _ _ _ (MapArgEq _ (EqualInPair'R _ _ _ _ _ Eqz)))).
rewrite (MapArgEq _ (EqualInPair'L _ _ _ _ _ (ZZMultTheorem_NNNN _ _ _ _))).
rewrite ZZMultTheorem_NNNN.
apply SymmetryEq.
rewrite (MapArgEq _ (EqualInPair'R _ _ _ _ _ (ZZMultTheorem_NNNN _ _ _ _))).
rewrite ZZMultTheorem_NNNN.

apply MapArgEq.
apply EqualInPair'.
split.
 rewrite (MapArgEq _ (EqualInPair'L _ _ _ _ _ (NNAdd_NNMultLDistDond _ _ _))).
 rewrite (MapArgEq _ (EqualInPair'R _ _ _ _ _ (NNAdd_NNMultLDistDond _ _ _))).
 apply SymmetryEq.
 rewrite (MapArgEq _ (EqualInPair'L _ _ _ _ _ (NNAdd_NNMultRDistDond _ _ _))).
 rewrite (MapArgEq _ (EqualInPair'R _ _ _ _ _ (NNAdd_NNMultRDistDond _ _ _))).
 rewrite NNAdd_Ope_SGrpCond.
 rewrite (MapArgEq _ (EqualInPair'R _ _ _ _ _ (NNAdd_Ope_CommCond _ _))).
 rewrite (MapArgEq _ (EqualInPair'R _ _ _ _ _ (NNAdd_Ope_SGrpCond _ _ _))).
 rewrite <- NNAdd_Ope_SGrpCond.
 apply MapArgEq.
 apply EqualInPair'.
 split;
 apply MapArgEq;
 apply EqualInPair';
 split;
 apply NNMult_Ope_SGrpCond.

 rewrite (MapArgEq _ (EqualInPair'L _ _ _ _ _ (NNAdd_NNMultLDistDond _ _ _))).
 rewrite (MapArgEq _ (EqualInPair'R _ _ _ _ _ (NNAdd_NNMultLDistDond _ _ _))).
 apply SymmetryEq.
 rewrite (MapArgEq _ (EqualInPair'L _ _ _ _ _ (NNAdd_NNMultRDistDond _ _ _))).
 rewrite (MapArgEq _ (EqualInPair'R _ _ _ _ _ (NNAdd_NNMultRDistDond _ _ _))).
 rewrite NNAdd_Ope_SGrpCond.
 rewrite (MapArgEq _ (EqualInPair'R _ _ _ _ _ (NNAdd_Ope_CommCond _ _))).
 rewrite (MapArgEq _ (EqualInPair'R _ _ _ _ _ (NNAdd_Ope_SGrpCond _ _ _))).
 rewrite <- NNAdd_Ope_SGrpCond.
 apply MapArgEq.
 apply EqualInPair'.
 split;
 apply MapArgEq;
 apply EqualInPair';
 split;
 apply NNMult_Ope_SGrpCond.
Qed.

Theorem ZZAddMult_DistDond :
Ope2_DistDond ZZAdd ZZMult.
Proof.
apply Dist_LDistCommCond.
 apply ZZMult_CommCond.
intros x y z.
put (ZZIsNNNN x) Eqx.
destruct Eqx as [a Eqx].
destruct Eqx as [b Eqx].
put (ZZIsNNNN y) Eqy.
destruct Eqy as [c Eqy].
destruct Eqy as [d Eqy].
put (ZZIsNNNN z) Eqz.
destruct Eqz as [e Eqz].
destruct Eqz as [f Eqz].
rewrite (MapArgEq _ (EqualInPair'L _ _ _ _ _ Eqx)).
rewrite (MapArgEq _ (EqualInPair'R _ _ _ _ _ (MapArgEq _ (EqualInPair'L _ _ _ _ _ Eqy)))).
rewrite (MapArgEq _ (EqualInPair'R _ _ _ _ _ (MapArgEq _ (EqualInPair'R _ _ _ _ _ Eqz)))).
rewrite (MapArgEq _ (EqualInPair'L _ _ _ _ _ (MapArgEq _ (EqualInPair'L _ _ _ _ _ Eqx)))).
rewrite (MapArgEq _ (EqualInPair'L _ _ _ _ _ (MapArgEq _ (EqualInPair'R _ _ _ _ _ Eqy)))).
rewrite (MapArgEq _ (EqualInPair'R _ _ _ _ _ (MapArgEq _ (EqualInPair'L _ _ _ _ _ Eqx)))).
rewrite (MapArgEq _ (EqualInPair'R _ _ _ _ _ (MapArgEq _ (EqualInPair'R _ _ _ _ _ Eqz)))).
rewrite (MapArgEq _ (EqualInPair'R _ _ _ _ _ (ZZAddTheorem_NNNN _ _ _ _))).
rewrite ZZMultTheorem_NNNN.
rewrite (MapArgEq _ (EqualInPair'L _ _ _ _ _ (MapArgEq _ (EqualInPair'L _ _ _ _ _ (NNAdd_NNMultLDistDond _ _ _))))).
rewrite (MapArgEq _ (EqualInPair'L _ _ _ _ _ (MapArgEq _ (EqualInPair'R _ _ _ _ _ (NNAdd_NNMultLDistDond _ _ _))))).
rewrite (MapArgEq _ (EqualInPair'R _ _ _ _ _ (MapArgEq _ (EqualInPair'L _ _ _ _ _ (NNAdd_NNMultLDistDond _ _ _))))).
rewrite (MapArgEq _ (EqualInPair'R _ _ _ _ _ (MapArgEq _ (EqualInPair'R _ _ _ _ _ (NNAdd_NNMultLDistDond _ _ _))))).
apply SymmetryEq.
rewrite (MapArgEq _ (EqualInPair'L _ _ _ _ _ (ZZMultTheorem_NNNN _ _ _ _))).
rewrite (MapArgEq _ (EqualInPair'R _ _ _ _ _ (ZZMultTheorem_NNNN _ _ _ _))).
rewrite ZZAddTheorem_NNNN.

apply MapArgEq.
apply EqualInPair'.
split.
 rewrite NNAdd_Ope_SGrpCond.
 apply SymmetryEq.
 rewrite NNAdd_Ope_SGrpCond.
 apply MapArgEq.
 apply EqualInPair'R.
 rewrite <- NNAdd_Ope_SGrpCond.
 apply SymmetryEq.
 rewrite <- NNAdd_Ope_SGrpCond.
 apply MapArgEq.
 apply EqualInPair'L.
 apply NNAdd_Ope_CommCond.

 rewrite NNAdd_Ope_SGrpCond.
 apply SymmetryEq.
 rewrite NNAdd_Ope_SGrpCond.
 apply MapArgEq.
 apply EqualInPair'R.
 rewrite <- NNAdd_Ope_SGrpCond.
 apply SymmetryEq.
 rewrite <- NNAdd_Ope_SGrpCond.
 apply MapArgEq.
 apply EqualInPair'L.
 apply NNAdd_Ope_CommCond.
Qed.

Theorem ZZAddMult_LDistDond : Ope2_LDistDond ZZAdd ZZMult.
Proof.
apply Ope2_LDist.
apply Dist_LDist.
apply Ope2_Dist.
apply ZZAddMult_DistDond.
Qed.

Theorem ZZAddMult_RDistDond : Ope2_RDistDond ZZAdd ZZMult.
Proof.
apply Ope2_RDist.
apply Dist_RDist.
apply Ope2_Dist.
apply ZZAddMult_DistDond.
Qed.

Theorem NNAdd_NNMultRDistDond : Ope2_RDistDond NNAdd NNMult.
Proof.
apply Ope2_RDist.
apply Dist_RDist.
apply Ope2_Dist.
apply NNAdd_NNMultDistDond.
Qed.

Theorem ZZMultTheorem1 : forall n,
%ZZMult [n;nat_to_ZZ 1] == n.
Proof.
intro n.
put (ZZIsNNNN n) Eqn.
destruct Eqn as [a Eqn].
destruct Eqn as [b Eqn].
apply (TransitivityEq (%ZZMult [%NNNN_to_ZZ [a;b] ; %NNNN_to_ZZ [nat_to_NN 1 ; nat_to_NN 0]])).
 apply MapArgEq.
 apply EqualInPair'.
 split.
 apply Eqn.
 rewrite <- NN_to_ZZ_is_NNNN_to_ZZ.
 hyperreflexivity.
rewrite ZZMultTheorem_NNNN.
rewrite Eqn.
apply MapArgEq.
apply EqualInPair'.
split.
 apply (TransitivityEq (%NNAdd [a;nat_to_NN 0])).
  apply MapArgEq.
  apply EqualInPair'.
  split.
  apply NNMultTheorem1.
  apply NNMultTheorem0.
 apply IsRightIdentTheorem.
 apply IsIdent_RightIdent.
 apply NN0IsIdent.

 apply (TransitivityEq (%NNAdd [nat_to_NN 0 ; b])).
  apply MapArgEq.
  apply EqualInPair'.
  split.
  apply NNMultTheorem0.
  apply NNMultTheorem1.
 rewrite NNAdd_Ope_CommCond.
 apply NNAddTheorem1.
Qed.

Theorem ZZ1IsIdent : &&IsIdent ZZMult (nat_to_ZZ 1).
Proof.
apply IsIdentTheoremR.
apply ZZMult_CommCond.
apply ZZMultTheorem1.
Qed.

Theorem ZZMultTheorem0 : forall n,
%ZZMult [n ; nat_to_ZZ 0] == nat_to_ZZ 0.
Proof.
intro n.
cut (%ZZAdd [n ; %ZZMult [n;nat_to_ZZ 0]] == n).
 intro EqH.
 apply (TransitivityEq (%ZZAdd [%Minus_of_ZZ n ; %ZZAdd [n ;%ZZMult [n;nat_to_ZZ 0]]])).
  apply SymmetryEq.
  rewrite <- ZZAdd_SGrpCond.
  apply IsLeftIdentTheorem.
  apply IsIdent_LeftIdent.
  apply IsInverseE_IsIdent'.
  apply Minus_of_ZZTheorem.
 rewrite (MapArgEq _ (EqualInPair'R _ _ _ _ _ EqH)).
 apply (IsIdentEq ZZAdd).
  apply IsInverseE_IsIdent'.
  apply Minus_of_ZZTheorem.
 apply ZZ0IsIdent.
apply (TransitivityEq (%ZZAdd [%ZZMult [n ; nat_to_ZZ 1] ; %ZZMult [n ; nat_to_ZZ 0]])).
 apply MapArgEq.
 apply EqualInPair'L.
 apply SymmetryEq.
 apply ZZMultTheorem1.
rewrite <- ZZAddMult_LDistDond.
apply IsRightIdentTheorem.
apply IsIdent_RightIdent.
generalize ZZ1IsIdent.
apply RelRewriteR.
apply SymmetryEq.
apply ZZAddTheorem0.
Qed.

Theorem ZZMultTheoremNext : forall n m,
%ZZMult [n;%ZZNext m] == %ZZAdd [%ZZMult [n;m] ; n].
Proof.
intros n m.
rewrite (MapArgEq _ (EqualInPair'R _ _ _ _ _ (ZZNextTheorem _))).
rewrite ZZAddMult_LDistDond.
apply MapArgEq.
apply EqualInPair'R.
apply ZZMultTheorem1.
Qed.

Theorem ZZMultTheoremMinus : forall n m,
%ZZMult [n ; %Minus_of_ZZ m] ==
%Minus_of_ZZ (%ZZMult [n;m]).
Proof.
intros n m.
cut (%ZZAdd [%ZZMult [n;%Minus_of_ZZ m] ; %ZZMult[n;m]] == nat_to_ZZ 0).
 intro EqH.
 apply (TransitivityEq (%ZZAdd [%ZZAdd [%ZZMult [n;%Minus_of_ZZ m] ; %ZZMult [n;m]] ; %Minus_of_ZZ (%ZZMult [n;m])])).
  apply SymmetryEq.
  rewrite ZZAdd_SGrpCond.
  apply IsRightIdentTheorem.
  apply IsIdent_RightIdent.
  apply IsInverseE_IsIdent.
  apply Minus_of_ZZTheorem.
 rewrite (MapArgEq _ (EqualInPair'L _ _ _ _ _ EqH)).
 apply IsLeftIdentTheorem.
 apply IsIdent_LeftIdent.
 apply ZZ0IsIdent.
rewrite <- ZZAddMult_LDistDond.
apply (TransitivityEq (%ZZMult [n ; nat_to_ZZ 0])).
 apply MapArgEq.
 apply EqualInPair'R.
 apply (IsIdentEq ZZAdd).
  apply IsInverseE_IsIdent'.
  apply Minus_of_ZZTheorem.
 apply ZZ0IsIdent.
apply ZZMultTheorem0.
Qed.

Theorem ZZMult_IdentCond : Ope_IdentCond ZZMult.
Proof.
exists (nat_to_ZZ 1).
apply ZZ1IsIdent.
Qed.

Theorem ZZMult_MonoidCond : Ope_MonoidCond ZZMult.
Proof.
split.
apply ZZMult_SGrpCond.
apply ZZMult_IdentCond.
Qed.

Theorem ZZMult_CMonoidCond : Ope_CMonoidCond ZZMult.
Proof.
split.
apply ZZMult_MonoidCond.
apply ZZMult_CommCond.
Qed.

Theorem ZZAddMult_CRingDond : Ope2_CRingDond ZZAdd ZZMult.
Proof.
split.
apply ZZAdd_CGrpCond.
split.
apply ZZMult_CMonoidCond.
apply ZZAddMult_DistDond.
Qed.

Theorem ZZAddMult_RingDond : Ope2_RingDond ZZAdd ZZMult.
Proof.
apply Ope2_Ring.
apply CRing_Ring.
apply Ope2_CRing.
apply ZZAddMult_CRingDond.
Qed.
 