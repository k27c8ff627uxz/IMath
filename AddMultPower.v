
Require Import logic.
Require Import IZF.
Require Import Relation.
Require Import BaseMap.
Require Import Maps.
Require Import TransitiveRecursion.
Require Import BOperation1.
Require Import BOperation2.





(* AddSet *)
Definition AddSet a b :=  TransitiveRecursiveFunction (fun x => Union a x) b.

Theorem AddSetOrderSemigroupCondition : forall a b c,
In b c -> In (AddSet a b) (AddSet a c).
Proof.
intros a b c Inbc.
assert(EqAD : (AddSet a c) == (TransitiveRecursiveFunction (fun x => Union a x) c)).
 apply ReflexivityEq.
rewrite EqAD.
rewrite (TransitiveRecursiveFunctionTheorem).
apply UnionTheorem.
right.
apply FunctionImageRistrictionTheorem.
exists b.
split.
assumption.
apply ReflexivityEq.
Qed.

Theorem AddSetTheoremEmpty : forall x,
AddSet x Empty == x.
Proof.
intro x.
unfold AddSet.
rewrite (TransitiveRecursiveFunctionTheorem).
apply EA.
intro c.
split.
 intro IncU.
 apply UnionTheorem in IncU.
 destruct IncU as [IncU | IncF].
 apply IncU.
 apply FunctionImageRistrictionTheorem in IncF.
 destruct IncF as [a IncF].
 destruct IncF as [InaE IncF].
 apply EmptyTheorem in InaE.
 contradiction.

 intro Incx.
 apply UnionTheorem.
 left.
 assumption.
Qed.

Theorem AddSetTheoremEmpty' : forall x,
AddSet Empty x == x.
Proof.
apply SetInductionAxiom.
intros x HHx.
apply EA.
intro a.
split.
 intros InaA.
 unfold AddSet in InaA.
 rewrite (TransitiveRecursiveFunctionTheorem) in InaA.
 apply UnionTheorem in InaA.
 destruct InaA as [InaE | InaF].
 apply EmptyTheorem in InaE.
 contradiction.
 apply FunctionImageRistrictionTheorem in InaF.
 destruct InaF as [b InaF].
 destruct InaF as [Inbx TEa].
 assert(Eqab : a == b).
  apply (TransitivityEq (AddSet Empty b)).
  apply SymmetryEq.
  apply TEa.
  apply HHx.
  assumption.
 rewrite Eqab.
 assumption.

 intro Inax.
 unfold AddSet.
 rewrite (TransitiveRecursiveFunctionTheorem).
 apply UnionTheorem.
 right.
 apply FunctionImageRistrictionTheorem.
 exists a.
 split.
 assumption.
 apply (TransitivityEq (AddSet Empty a)).
 apply ReflexivityEq.
 apply HHx.
 assumption.
Qed.



Theorem AddSetTheoremNext : forall x y,
AddSet x (Next y) == Next (AddSet x y).
Proof.
intros x y.
apply EA.
intro a.
split.
 intro InaA.
 unfold AddSet in InaA.
 rewrite TransitiveRecursiveFunctionTheorem in InaA.
 apply UnionTheorem in InaA.
 destruct InaA as [Inax | InaF].
  (* a < x *)
  apply UnionTheorem.
  left.
  unfold AddSet.
  rewrite TransitiveRecursiveFunctionTheorem.
  apply UnionTheorem.
  left.
  assumption.

  (* x <= a < Sy *) 
  apply FunctionImageRistrictionTheorem in InaF.
  destruct InaF as [b InaF].
  destruct InaF as [Inbny Eqxba'].
  assert(Eqxba : (AddSet x b) == a).
   apply Eqxba'.
  clear Eqxba'.
  apply UnionTheorem in Inbny.
  destruct Inbny as [Inby | Eqby].
   (* b < y *)
   apply UnionTheorem.
   left.
   rewrite <- Eqxba.
   apply AddSetOrderSemigroupCondition.
   assumption.

   (* b = y *)
   apply SingletonTheorem in Eqby.
   apply UnionTheorem.
   right.
   apply SingletonTheorem.
   rewrite <- Eqxba.
   rewrite Eqby.
   hyperreflexivity.


 intro InaN.
 apply UnionTheorem in InaN.
 destruct InaN as [Inaxy | Eqaxy].
  (* a < x+y *)
  unfold AddSet in Inaxy.
  rewrite (TransitiveRecursiveFunctionTheorem) in Inaxy.
  apply UnionTheorem in Inaxy.
  destruct Inaxy as [Inax | InaF].
   (* a < x *)
   unfold AddSet.
   rewrite (TransitiveRecursiveFunctionTheorem).
   apply UnionTheorem.
   left.
   assumption.

   (* x <= a < x+y *)
   apply FunctionImageRistrictionTheorem in InaF.
   destruct InaF as [b InaF].
   destruct InaF as [Inby Eqxba'].
   assert(Eqxba : (AddSet x b) == a).
    apply Eqxba'.
   clear Eqxba'.
   rewrite <- Eqxba.
   apply AddSetOrderSemigroupCondition.
   apply UnionTheorem.
   left.
   assumption.

  (* a = x+y *)
  apply SingletonTheorem in Eqaxy.
  rewrite Eqaxy.
  apply AddSetOrderSemigroupCondition.
  apply UnionTheorem.
  right.
  apply SingletonTheorem.
  hyperreflexivity.
Qed.
  

Theorem AddSetAssociativity : forall a b c,
AddSet (AddSet a b) c == AddSet a (AddSet b c).
Proof.
intros X Y.
apply SetInductionAxiom.
intros Z ZInd.
apply EA.
intro a.
split.


intro InaT.
unfold AddSet in InaT at 1.
rewrite (TransitiveRecursiveFunctionTheorem) in InaT.
apply UnionTheorem in InaT.
destruct InaT as [InaA | InaF].
 (* a<X+Y *)
 unfold AddSet in InaA.
 rewrite (TransitiveRecursiveFunctionTheorem) in InaA.
 apply UnionTheorem in InaA.
 destruct InaA as [InaX | InaF].

  (* a<X *)
  unfold AddSet at 1.
  rewrite TransitiveRecursiveFunctionTheorem .
  apply UnionTheorem.
  left.
  assumption.

  (* X <= a < X+Y *)
  apply FunctionImageRistrictionTheorem in InaF.
  destruct InaF as [b InaF].
  destruct InaF as [InbY EqT'].
  assert(EqT : AddSet X b == a).
   apply EqT'.
  clear EqT'.
  rewrite <- EqT.
  apply AddSetOrderSemigroupCondition.
  unfold AddSet.
  rewrite TransitiveRecursiveFunctionTheorem.
  apply UnionTheorem.
  left.
  assumption.

 (* X+Y <= a < (X+Y)+Z *)
 apply FunctionImageRistrictionTheorem in InaF.
 destruct InaF as [b InaF].
 destruct InaF as [InbZ EqXYba'].
 assert(EqXYba : (AddSet (AddSet X Y) b) == a).
  apply EqXYba'.
 clear EqXYba'.
 rewrite (ZInd _ InbZ) in EqXYba.
 rewrite <- EqXYba.
 apply AddSetOrderSemigroupCondition.
 apply AddSetOrderSemigroupCondition.
 assumption.


intro InaXYZ.
unfold AddSet at 1 in InaXYZ.
rewrite TransitiveRecursiveFunctionTheorem in InaXYZ.
apply UnionTheorem in InaXYZ.
destruct InaXYZ as [InaX | InaYZ].
 (* a < X *)
  unfold AddSet at 1.
 rewrite (TransitiveRecursiveFunctionTheorem).
 apply UnionTheorem.
 left.
 unfold AddSet.
 rewrite TransitiveRecursiveFunctionTheorem.
 apply UnionTheorem.
 left.
 assumption.

 (* X <= a < X+(Y+Z) *)
 apply FunctionImageRistrictionTheorem in InaYZ.
 destruct InaYZ as [b InaYZ].
 destruct InaYZ as [InbAXY EqXba'].
 assert(EqXba : (AddSet X b) == a).
  apply EqXba'.
 clear EqXba'.
 unfold AddSet in InbAXY.
 rewrite TransitiveRecursiveFunctionTheorem in InbAXY.
 apply UnionTheorem in InbAXY.
 destruct InbAXY as [InbY | InbF].
  (* b < Y *)
  unfold AddSet at 1.
  rewrite TransitiveRecursiveFunctionTheorem.
  apply UnionTheorem.
  left.
  rewrite <- EqXba.
  apply AddSetOrderSemigroupCondition.
  assumption.

  (* Y <= b < Y+Z *)
  apply FunctionImageRistrictionTheorem in InbF.
  destruct InbF as [c InbF].
  destruct InbF as [IncZ EqYcb'].
  assert(EqYcb : AddSet Y c == b).
   apply EqYcb'.
  clear EqYcb'.
  rewrite <- EqXba.
  rewrite <- EqYcb.
  rewrite <- (ZInd _ IncZ).
  apply AddSetOrderSemigroupCondition.
  assumption.
Qed.

 
Theorem AddSetSup : forall X Y,
(In Empty Y /\ (forall y, In y Y -> In (Next y) Y) /\ TransitivitySet Y) ->
AddSet X Y == (Unions (FunctionImageRistriction (fun v => AddSet X v) Y)).
Proof.
intros X Y YCond.
destruct YCond as [InEY YCond].
destruct YCond as [YN TY].
apply EA.
intro a.
split.
 intro InaA.
 unfold AddSet in InaA.
 rewrite (TransitiveRecursiveFunctionTheorem) in InaA.
 apply UnionTheorem in InaA.
 destruct InaA as [InaX | InaF].
 (* a < X *)
  apply UnionsTheorem.
  exists X.
  split.
   apply FunctionImageRistrictionTheorem.
   exists Empty.
   split.
   assumption.
   apply AddSetTheoremEmpty.

   assumption.

 (* X <= a < X+Y *)
 apply FunctionImageRistrictionTheorem in InaF.
 destruct InaF as [b InaF].
 destruct InaF as [InbY TeTa].
 assert(EqXba : AddSet X b == a).
  apply TeTa.
 clear TeTa.
 apply UnionsTheorem.
 exists (AddSet X (Next b)).
 split.
  apply FunctionImageRistrictionTheorem.
  exists (Next b).
  split.
   apply YN.
   assumption.

   apply ReflexivityEq.

  unfold AddSet.
  rewrite (TransitiveRecursiveFunctionTheorem).
  apply UnionTheorem.
  right.
  apply FunctionImageRistrictionTheorem.
  exists b.
  split.
   apply UnionTheorem.
   right.
   apply SingletonTheorem.
   apply ReflexivityEq.

   apply EqXba.


 intro InaU.
 apply UnionsTheorem in InaU.
 destruct InaU as [b InaU].
 destruct InaU as [InbF Inab].
 apply FunctionImageRistrictionTheorem in InbF.
 destruct InbF as [c InbF].
 destruct InbF as [IncY EqXcb].
 rewrite <- EqXcb in Inab.
 clear EqXcb.
 clear b.
 unfold AddSet in Inab.
 rewrite (TransitiveRecursiveFunctionTheorem) in Inab.
 apply UnionTheorem in Inab.
 destruct Inab as [InaX | InaF].
  (* a < X *)
  unfold AddSet.
  rewrite (TransitiveRecursiveFunctionTheorem).
  apply UnionTheorem.
  left.
  assumption.

  (* X <= a < X+Y *)
  apply FunctionImageRistrictionTheorem in InaF.
  destruct InaF as [b InaF].
  destruct InaF as [Inbc EqTba].
  assert(EqXba : (AddSet X b) == a).
   apply EqTba.
  clear EqTba.
  unfold AddSet.
  rewrite (TransitiveRecursiveFunctionTheorem).
  apply UnionTheorem.
  right.
  apply FunctionImageRistrictionTheorem.
  exists b.
  split.
  apply TY in IncY.
  apply IncY.
  assumption.

  apply EqXba.
Qed.






  

(* Mult *)
Definition MultSet A B := TransitiveRecursiveFunction (fun v => Unions (
  FunctionImageRistriction (fun p => FunctionImageRistriction (fun q => AddSet p q) A) v
)) B.

Theorem MultSetTheoremEmpty : forall A,
MultSet A Empty == Empty.
Proof.
intro A.
apply EA.
intro a.
split.
 intro InaM.
 unfold MultSet in InaM.
 rewrite (TransitiveRecursiveFunctionTheorem) in InaM.
 apply UnionsTheorem in InaM.
 destruct InaM as [b InaM].
 destruct InaM as [InbF Inab].
 apply FunctionImageRistrictionTheorem in InbF.
 destruct InbF as [c InbF].
 destruct InbF as [IncF EqT].
 apply FunctionImageRistrictionTheorem in IncF.
 destruct IncF as [d IncF].
 destruct IncF as [IndE EqTT].
 apply EmptyTheorem in IndE.
 contradiction.

 intro InaE.
 apply EmptyTheorem in InaE.
 contradiction.
Qed.

Theorem MultSetTheoremEmpty' : forall A,
MultSet Empty A == Empty.
Proof.
intro A.
apply EA.
intro a.
split.



intro InaM.
unfold MultSet in InaM.
rewrite (TransitiveRecursiveFunctionTheorem) in InaM.
apply UnionsTheorem in InaM.
destruct InaM as [b InaM].
destruct InaM as [InbF Inab].
apply FunctionImageRistrictionTheorem in InbF.
destruct InbF as [c InbF].
destruct InbF as [IncF EqFb].
rewrite <- EqFb in Inab.
clear EqFb.
clear b.
apply FunctionImageRistrictionTheorem in Inab.
destruct Inab as [b Inab].
destruct Inab as [InbE Eqcba].
apply EmptyTheorem in InbE.
contradiction.



intro InaE.
apply EmptyTheorem in InaE.
contradiction.
Qed.


Theorem MultSetTheoremOne : forall A,
MultSet A (Next Empty) == A.
Proof.
intro A.
apply EA.
intro a.
split.

intro InaM.
unfold MultSet in InaM.
rewrite (TransitiveRecursiveFunctionTheorem) in InaM.
apply UnionsTheorem in InaM.
destruct InaM as [b InaM].
destruct InaM as [InbF Inab].
apply FunctionImageRistrictionTheorem in InbF.
destruct InbF as [c InbF].
destruct InbF as [IncF EqFb].
rewrite <- EqFb in Inab.
clear EqFb.
clear b.
apply FunctionImageRistrictionTheorem in Inab.
destruct Inab as [b Inab].
destruct Inab as [InbA EqAa].
apply FunctionImageRistrictionTheorem in IncF.
destruct IncF as [d IncF].
destruct IncF as [IndNE TEqc].
apply UnionTheorem in IndNE.
destruct IndNE as [IndE | EqdE].
apply EmptyTheorem in IndE.
contradiction.
apply SingletonTheorem in EqdE.
assert(Eqc : (MultSet A d) == c).
 apply TEqc.
clear TEqc.
rewrite EqdE in Eqc.
assert(Eqab : a == b).
 apply (TransitivityEq (AddSet c b)).
 apply SymmetryEq.
 assumption.
 assert(Eqc0 : c == Empty).
  apply (TransitivityEq (MultSet A Empty)).
  apply SymmetryEq.
  assumption.
  apply MultSetTheoremEmpty.
 rewrite Eqc0.
 apply AddSetTheoremEmpty'.
rewrite Eqab.
assumption.


intro InaA.
unfold MultSet.
rewrite (TransitiveRecursiveFunctionTheorem).
apply UnionsTheorem.
exists (FunctionImageRistriction (fun q => AddSet (MultSet A Empty) q) A).
split.
 apply FunctionImageRistrictionTheorem.
 exists Empty.
 split.
  apply FunctionImageRistrictionTheorem.
  exists Empty.
  split.
   apply UnionTheorem.
   right.
   apply SingletonTheorem.
   apply ReflexivityEq.

   apply (TransitivityEq (MultSet A Empty)).
   apply ReflexivityEq.
   apply MultSetTheoremEmpty.

  apply EA.
  intro b.
  split.
   intro InbF.
   apply FunctionImageRistrictionTheorem in InbF.
   destruct InbF as [c InbF].
   destruct InbF as [IncA AEqb].
   apply FunctionImageRistrictionTheorem.
   exists c.
   split.
   assumption.
   assert(EqME : (MultSet A Empty) == Empty).
    apply MultSetTheoremEmpty.
   rewrite EqME.
   assumption.

   intro Inbf.
   apply FunctionImageRistrictionTheorem in Inbf.
   destruct Inbf as [c Inbf].
   destruct Inbf as [IncA EqAb].
   apply FunctionImageRistrictionTheorem.
   exists b.
   split.
   assert(Eqbc : b == c).
    apply (TransitivityEq (AddSet (MultSet A Empty) c)).
    apply SymmetryEq.
    assumption.
    assert(EqM : MultSet A Empty == Empty).
     apply MultSetTheoremEmpty.
    rewrite EqM.
    apply AddSetTheoremEmpty'.
   rewrite Eqbc.
   assumption.
   apply AddSetTheoremEmpty'.
   
 apply FunctionImageRistrictionTheorem.
 exists a.
 split.
 assumption.
 assert(EqM : (MultSet A Empty) == Empty).
  apply MultSetTheoremEmpty.
 rewrite EqM.
 apply AddSetTheoremEmpty'.
Qed.

Theorem MultSetTheoremOne' : forall A,
MultSet (Next Empty) A == A.
Proof.
apply (SetInductionAxiom).
intros A InductionA.

apply EA.
intro a.
split.


intro InaM.
unfold MultSet in InaM.
rewrite (TransitiveRecursiveFunctionTheorem) in InaM.
apply UnionsTheorem in InaM.
destruct InaM as [b InaM].
destruct InaM as [InbF Inab].
apply FunctionImageRistrictionTheorem in InbF.
destruct InbF as [c InbF].
destruct InbF as [IncF EqFb].
rewrite <- EqFb in Inab.
clear EqFb.
clear b.
apply FunctionImageRistrictionTheorem in Inab.
destruct Inab as [b Inab].
destruct Inab as [Inb1 Eqcba].
apply FunctionImageRistrictionTheorem in IncF.
destruct IncF as [d IncF].
destruct IncF as [IndA EqTc].
assert(Eq1dc : (MultSet (Next Empty) d) == c).
 apply EqTc.
clear EqTc.
assert (Eqa : a == d).
 rewrite <- Eqcba.
 rewrite <- Eq1dc.
 rewrite (InductionA _ IndA).
 apply UnionTheorem in Inb1.
 destruct Inb1 as [Cont | Eqb0].
 apply EmptyTheorem in Cont.
 contradiction.
 apply SingletonTheorem in Eqb0.
 rewrite Eqb0.
 apply AddSetTheoremEmpty.
rewrite Eqa.
assumption.


intro InaA.
unfold MultSet.
rewrite (TransitiveRecursiveFunctionTheorem).
apply UnionsTheorem.
exists (FunctionImageRistriction (fun q => AddSet (MultSet (Next Empty) a) q) (Next Empty)).
split.
 apply FunctionImageRistrictionTheorem.
 exists (MultSet (Next Empty) a).
 split.
  apply FunctionImageRistrictionTheorem.
  exists a.
  split.
  assumption.
  apply ReflexivityEq.

  apply ReflexivityEq.

 apply FunctionImageRistrictionTheorem.
 exists Empty.
 split.
  apply UnionTheorem.
  right.
  apply SingletonTheorem.
  apply ReflexivityEq.

  apply (TransitivityEq (MultSet (Next Empty) a)).
  apply AddSetTheoremEmpty.
  apply InductionA.
  assumption.
Qed.

Theorem MultSetSmall : forall X Y a b, (In a Y /\ In b X) -> In (AddSet (MultSet X a) b) (MultSet X Y).
Proof.
intros X Y a b InD.
destruct InD as [InaY InbX].
unfold MultSet at 2.
rewrite (TransitiveRecursiveFunctionTheorem).
apply UnionsTheorem.
exists (FunctionImageRistriction (fun q => AddSet (MultSet X a) q) X).
split.
 apply FunctionImageRistrictionTheorem.
 exists (MultSet X a).
 split.
  apply FunctionImageRistrictionTheorem.
  exists a.
  split.
  assumption.
  apply ReflexivityEq.

  apply ReflexivityEq.

 apply FunctionImageRistrictionTheorem.
 exists b.
 split.
 assumption.
 apply ReflexivityEq.
Qed.




Theorem MultSetLeftDistributivity : forall X Y Z,
MultSet X (AddSet Y Z) == AddSet (MultSet X Y) (MultSet X Z).
Proof.
intros X Y.
apply (SetInductionAxiom).
intros Z IndZ.
apply EA.
intro a.
split.


intro InaM.
unfold MultSet in InaM at 1.
rewrite (TransitiveRecursiveFunctionTheorem) in InaM.
apply UnionsTheorem in InaM.
destruct InaM as [b InbF].
destruct InbF as [InbF Inab].
apply FunctionImageRistrictionTheorem in InbF.
destruct InbF as [c InbF].
destruct InbF as [IncF EqFb].
rewrite <- EqFb in Inab.
clear EqFb.
clear b.
apply FunctionImageRistrictionTheorem in Inab.
destruct Inab as [b Inab].
destruct Inab as [InbX AEa].
apply FunctionImageRistrictionTheorem in IncF.
destruct IncF as [d IncF].
destruct IncF as [IndA EqTd].
assert(EqMc : (MultSet X d) == c).
 apply EqTd.
clear EqTd.
unfold AddSet in IndA.
rewrite (TransitiveRecursiveFunctionTheorem) in IndA.
apply UnionTheorem in IndA.
destruct IndA as [IndY | IndF].
 (* d < Y *)
 rewrite <- AEa.
 rewrite <- EqMc.
 unfold AddSet at 2.
 rewrite (TransitiveRecursiveFunctionTheorem).
 apply UnionTheorem.
 left.
 apply MultSetSmall.
 split; assumption.

 (* Y <= d < Y+Z *)
 apply FunctionImageRistrictionTheorem in IndF.
 destruct IndF as [e IndF].
 destruct IndF as [IneZ EqTd].
 assert(AdEqd : AddSet Y e == d).
  apply EqTd.
 clear EqTd.
 assert(Eqa : a == (AddSet (MultSet X Y) (AddSet (MultSet X e) b))).
  rewrite <- AEa.
  rewrite <- EqMc.
  rewrite <- AdEqd.
  apply (TransitivityEq (AddSet (AddSet (MultSet X Y) (MultSet X e)) b)).
   apply FunRewrite2.
   apply IndZ.
   assumption.
   apply ReflexivityEq.
  apply AddSetAssociativity.
 rewrite Eqa.
 apply AddSetOrderSemigroupCondition.
 apply MultSetSmall.
 split; assumption.


intro InaA.
unfold AddSet in InaA.
rewrite (TransitiveRecursiveFunctionTheorem) in InaA.
apply UnionTheorem in InaA.
destruct InaA as [InaM | InaF].
 (* a < X*Y *)
 unfold MultSet in InaM.
 rewrite (TransitiveRecursiveFunctionTheorem) in InaM.
 apply UnionsTheorem in InaM.
 destruct InaM as [b InaM].
 destruct InaM as [InbF Inab].
 apply FunctionImageRistrictionTheorem in InbF.
 destruct InbF as [c InbF].
 destruct InbF as [IncF EqFXb].
 rewrite <- EqFXb in Inab.
 clear EqFXb.
 clear b.
 apply FunctionImageRistrictionTheorem in IncF.
 destruct IncF as [b IncF].
 destruct IncF as [InbY EqTc].
 assert(EqMc : (MultSet X b) == c).
  apply EqTc.
 clear EqTc.
 apply FunctionImageRistrictionTheorem in Inab.
 destruct Inab as [d Inab].
 destruct Inab as [IndX EaAa].
 rewrite <- EaAa.
 rewrite <- EqMc.
 apply MultSetSmall.
 split; try apply IndX.
 unfold AddSet.
 rewrite (TransitiveRecursiveFunctionTheorem).
 apply UnionTheorem.
 left.
 assumption.

 (* X*Y <= a < X*Y+XZ *)
 apply FunctionImageRistrictionTheorem in InaF.
 destruct InaF as [b InaF].
 destruct InaF as [InbM EqTa].
 assert(EqAxba : (AddSet (MultSet X Y) b) == a).
  apply EqTa.
 clear EqTa.
 unfold MultSet in InbM.
 rewrite (TransitiveRecursiveFunctionTheorem) in InbM.
 apply UnionsTheorem in InbM.
 destruct InbM as [c InbM].
 destruct InbM as [IncF Inbc].
 apply FunctionImageRistrictionTheorem in IncF.
 destruct IncF as [d IncF].
 destruct IncF as [IndF FEqc].
 rewrite <- FEqc in Inbc.
 clear FEqc.
 clear c.
 apply FunctionImageRistrictionTheorem in Inbc.
 destruct Inbc as [c Inbc].
 destruct Inbc as [IncX Eqacb].
 apply FunctionImageRistrictionTheorem in IndF.
 destruct IndF as [e IndF].
 destruct IndF as [IneZ IndF].
 assert(EqXed : (MultSet X e) == d).
  apply IndF.
 clear IndF.
 assert(Eqa : a == (AddSet (MultSet X (AddSet Y e)) c)).
  rewrite <- EqAxba.
  rewrite <- Eqacb.
  rewrite <- EqXed.
  apply (TransitivityEq (AddSet (AddSet (MultSet X Y) (MultSet X e)) c)).
   apply SymmetryEq.
   apply AddSetAssociativity.
  apply FunRewrite2; try apply (ReflexivityEq c).
  apply SymmetryEq.
  apply IndZ.
  assumption.
 rewrite Eqa.
 apply MultSetSmall.
 split; try apply IncX.
 apply AddSetOrderSemigroupCondition.
 assumption.
Qed.

Theorem MultSetTheoremNext : forall X Y,
MultSet X (Next Y) == (AddSet (MultSet X Y) X).
Proof.
intros X Y.
apply (TransitivityEq (MultSet X (AddSet Y (Next Empty)))).
assert(EqN : (Next Y) == (AddSet Y (Next Empty))).
 apply SymmetryEq.
 apply (TransitivityEq (Next (AddSet Y Empty))).
 apply AddSetTheoremNext.
 rewrite (AddSetTheoremEmpty).
 apply ReflexivityEq.
rewrite EqN.
apply ReflexivityEq.

apply (TransitivityEq (AddSet (MultSet X Y) (MultSet X (Next Empty)))).
apply (MultSetLeftDistributivity).

assert (EqM : (MultSet X (Next Empty)) == X).
 apply MultSetTheoremOne.
rewrite EqM.
apply ReflexivityEq.
Qed.


Theorem MultSetAssociativity : forall X Y Z,
MultSet (MultSet X Y) Z == MultSet X (MultSet Y Z).
Proof.
intros X Y.
apply SetInductionAxiom.
intros Z InductionZ.
apply EA.
intro a.
split.

intro InaM.
unfold MultSet in InaM at 1.
rewrite (TransitiveRecursiveFunctionTheorem) in InaM.
apply UnionsTheorem in InaM.
destruct InaM as [b InaM].
destruct InaM as [InbF Inab].
apply FunctionImageRistrictionTheorem in InbF.
destruct InbF as [c InbF].
destruct InbF as [IncF Eqfb].
rewrite <- Eqfb in Inab.
clear Eqfb.
clear b.
apply FunctionImageRistrictionTheorem in Inab.
destruct Inab as [b Inab].
destruct Inab as [InbT Eqcba].
apply FunctionImageRistrictionTheorem in IncF.
destruct IncF as [d IncF].
destruct IncF as [IndZ Eqdc].
assert(InbXY : In b (MultSet X Y)).
 apply InbT.
clear InbT.
assert(EqXYdc : (MultSet (MultSet X Y) d) == c).
 apply Eqdc.
clear Eqdc.
unfold MultSet in InbXY.
rewrite (TransitiveRecursiveFunctionTheorem) in InbXY.
apply UnionsTheorem in InbXY.
destruct InbXY as [e InbXY].
destruct InbXY as [IneF Inbe].
apply FunctionImageRistrictionTheorem in IneF.
destruct IneF as [f IneF].
destruct IneF as [InfF EqXe].
rewrite <- EqXe in Inbe.
clear EqXe.
clear e.
apply FunctionImageRistrictionTheorem in Inbe.
destruct Inbe as [e Inbe].
destruct Inbe as [IneX Eqfeb].
apply FunctionImageRistrictionTheorem in InfF.
destruct InfF as [g InfF].
destruct InfF as [IngY Eqgf].
assert(EqXgf : (MultSet X g) == f).
 apply Eqgf.
clear Eqgf.
assert(Eqa : a == (AddSet (MultSet X (AddSet (MultSet Y d) g)) e)).
 rewrite <- Eqcba.
 rewrite <- EqXYdc.
 rewrite <- Eqfeb.
 rewrite <- EqXgf.
 apply (TransitivityEq (AddSet (AddSet (MultSet (MultSet X Y) d) (MultSet X g)) e)).
  apply SymmetryEq.
  apply AddSetAssociativity.
 apply FunRewrite2; try apply ReflexivityEq.
 apply (TransitivityEq (AddSet (MultSet X (MultSet Y d)) (MultSet X g))).
  apply FunRewrite2; try apply ReflexivityEq.
  apply (InductionZ).
  assumption.
 apply SymmetryEq.
 apply MultSetLeftDistributivity.
rewrite Eqa.
apply MultSetSmall.
split.
 apply MultSetSmall.
 split; assumption.
assumption.



intros InaM.
unfold MultSet in InaM at 1.
rewrite (TransitiveRecursiveFunctionTheorem) in InaM.
apply UnionsTheorem in InaM.
destruct InaM as [b InaM].
destruct InaM as [InbF Inab].
apply FunctionImageRistrictionTheorem in InbF.
destruct InbF as [c InbF].
destruct InbF as [IncF EqFXb].
rewrite <- EqFXb in Inab.
clear EqFXb.
clear b.
apply FunctionImageRistrictionTheorem in Inab.
destruct Inab as [b Inab].
destruct Inab as [InBX Eqcba].
apply FunctionImageRistrictionTheorem in IncF.
destruct IncF as [d IncF].
destruct IncF as [IndM EqTc].
assert(EqXdc : (MultSet X d) == c).
 apply EqTc.
clear EqTc.
unfold MultSet in IndM.
rewrite (TransitiveRecursiveFunctionTheorem) in IndM.
apply UnionsTheorem in IndM.
destruct IndM as [e IndM].
destruct IndM as [IneF Inde].
apply FunctionImageRistrictionTheorem in IneF.
destruct IneF as [f IneF].
destruct IneF as [InfF EqFYe].
rewrite <- EqFYe in Inde.
clear EqFYe.
clear e.
apply FunctionImageRistrictionTheorem in Inde.
destruct Inde as [e Inde].
destruct Inde as [IneY Eqfed].
apply FunctionImageRistrictionTheorem in InfF.
destruct InfF as [g InfF].
destruct InfF as [IngZ EqYgf].
assert(EqMYgf : (MultSet Y g) == f).
 apply EqYgf.
clear EqYgf.
assert(Eqa : a == (AddSet (MultSet (MultSet X Y) g) (AddSet (MultSet X e) b))).
 rewrite <- Eqcba.
 rewrite <- EqXdc.
 rewrite <- Eqfed.
 rewrite <- EqMYgf.
 apply (TransitivityEq (AddSet (AddSet (MultSet X (MultSet Y g)) (MultSet X e)) b)).
  apply FunRewrite2.
  apply MultSetLeftDistributivity.
  hyperreflexivity.
 apply (TransitivityEq (AddSet (MultSet X (MultSet Y g)) (AddSet (MultSet X e) b))).
  apply AddSetAssociativity.
 apply FunRewrite2; try apply ReflexivityEq.
 apply SymmetryEq.
 apply InductionZ.
 assumption.
rewrite Eqa.
apply MultSetSmall.
split.
assumption.
apply MultSetSmall.
split.
assumption.
assumption.
Qed.




Theorem MultSetSup : forall X Y,
((forall y, In y Y -> In (Next y) Y) /\ TransitivitySet Y) ->
MultSet X Y == (Unions (FunctionImageRistriction (fun v => MultSet X v) Y)).
Proof.
intros X Y YCond.
destruct YCond as [YN TY].
apply EA.
intro a.
split.


intro InaM.
unfold MultSet in InaM.
rewrite (TransitiveRecursiveFunctionTheorem) in InaM.
apply UnionsTheorem in InaM.
destruct InaM as [b InaM].
destruct InaM as [InbF Inab].
apply FunctionImageRistrictionTheorem in InbF.
destruct InbF as [c InbF].
destruct InbF as [IncF EqFXb].
rewrite <- EqFXb in Inab.
clear EqFXb.
clear b.
apply FunctionImageRistrictionTheorem in Inab.
destruct Inab as [b Inab].
destruct Inab as [InbC Eqcba].
apply FunctionImageRistrictionTheorem in IncF.
destruct IncF as [d IncF].
destruct IncF as [IndY EqTc].
assert(EqXdc : MultSet X d == c).
 apply EqTc.
clear EqTc.
apply UnionsTheorem.
exists (MultSet X (Next d)).
split.
 apply FunctionImageRistrictionTheorem.
 exists (Next d).
 split.
  apply YN.
  assumption.

  apply ReflexivityEq.

 unfold MultSet.
 rewrite (TransitiveRecursiveFunctionTheorem).
 apply UnionsTheorem.
 exists (FunctionImageRistriction (fun q => AddSet (MultSet X d) q) X).
 split.
  apply FunctionImageRistrictionTheorem.
  exists (MultSet X d).
  split.
   apply FunctionImageRistrictionTheorem.
   exists d.
   split.
    apply UnionTheorem.
    right.
    apply SingletonTheorem.
    apply ReflexivityEq.

    apply ReflexivityEq.

   apply ReflexivityEq.

  apply FunctionImageRistrictionTheorem.
  exists b.
  split.
  assumption.
  rewrite <- Eqcba.
  rewrite <- EqXdc.
  apply ReflexivityEq.




intro InaU.
apply UnionsTheorem in InaU.
destruct InaU as [b InaU].
destruct InaU as [InbF Inab].
apply FunctionImageRistrictionTheorem in InbF.
destruct InbF as [c InbF].
destruct InbF as [IncY EqXcb].
rewrite <- EqXcb in Inab.
clear EqXcb.
clear b.
unfold MultSet in Inab.
rewrite (TransitiveRecursiveFunctionTheorem) in Inab.
apply UnionsTheorem in Inab.
destruct Inab as [b Inab].
destruct Inab as [InbF Inab].
apply FunctionImageRistrictionTheorem in InbF.
destruct InbF as [d InbF].
destruct InbF as [IndF EqXb].
rewrite <- EqXb in Inab.
clear EqXb.
clear b.
apply FunctionImageRistrictionTheorem in Inab.
destruct Inab as [b Inab].
destruct Inab as [InbX Eqdba].
apply FunctionImageRistrictionTheorem in IndF.
destruct IndF as [e IndF].
destruct IndF as [Inec Eqed].
assert(EqXed : MultSet X e == d).
 apply Eqed.
clear Eqed.

unfold MultSet.
rewrite (TransitiveRecursiveFunctionTheorem).
apply UnionsTheorem.
exists (FunctionImageRistriction (fun q => AddSet (MultSet X e) q) X).
split.
 apply FunctionImageRistrictionTheorem.
 exists (MultSet X e).
 split.
  apply FunctionImageRistrictionTheorem.
  exists e.
  split.
   apply TY in IncY.
   apply IncY.
   assumption.

   apply ReflexivityEq.

  apply ReflexivityEq.

 apply FunctionImageRistrictionTheorem.
 exists b.
 split.
 assumption.
 rewrite <- Eqdba.
 rewrite <- EqXed.
 apply ReflexivityEq.
Qed.



(* Power *)
Definition PowSet X Y := TransitiveRecursiveFunction (fun v => Union (Next Empty) (Unions (FunctionImageRistriction (fun p => FunctionImageRistriction'Dom (fun d : #(Cartesian X p) => AddSet (MultSet p (%(LeftPair _ _) d)) (%(RightPair _ _) d))) v))) Y.

Theorem PowSetTheoremEmpty : forall X , (PowSet X Empty) == (Next Empty).
Proof.
intro X.
apply EA.
intro a.
split.



intro InaP.
unfold PowSet in InaP.
rewrite (TransitiveRecursiveFunctionTheorem) in InaP.
apply UnionTheorem in InaP.
destruct InaP as [InaN | InaU].
assumption.
apply UnionsTheorem in InaU.
destruct InaU as [b InaU].
destruct InaU as [InbF Inab].
apply FunctionImageRistrictionTheorem in InbF.
destruct InbF as [c InbF].
destruct InbF as [IncF EqFb].
rewrite <- EqFb in Inab.
clear EqFb.
clear b.
apply FunctionImageRistriction'DomTheorem in Inab.
destruct Inab as [b Inab].
destruct Inab as [InbC HHE'].
apply FunctionImageRistrictionTheorem in IncF.
destruct IncF as [d IncF].
destruct IncF as [IndF EqTc].
apply EmptyTheorem in IndF.
contradiction.



intro InaN.
apply UnionTheorem in InaN.
destruct InaN as [InaE | EqaE].
apply EmptyTheorem in InaE.
contradiction.
apply SingletonTheorem in EqaE.
rewrite EqaE.
clear EqaE.
clear a.
unfold PowSet.
rewrite (TransitiveRecursiveFunctionTheorem).
apply UnionTheorem.
left.
apply UnionTheorem.
right.
apply SingletonTheorem.
apply ReflexivityEq.
Qed.


Theorem PowSetTheoremOne : forall X , In Empty X -> (PowSet X (Next Empty)) == X.
Proof.
intros X InEX.
apply EA.
intro a.
split.



intro InaP.
unfold PowSet in InaP.
rewrite (TransitiveRecursiveFunctionTheorem) in InaP.
apply UnionTheorem in InaP.
destruct InaP as [InaP | InaP].
 apply UnionTheorem in InaP.
 destruct InaP as [InaE | EqaE].
 apply EmptyTheorem in InaE.
 contradiction.
 apply SingletonTheorem in EqaE.
 rewrite EqaE.
 assumption.
apply UnionsTheorem in InaP.
destruct InaP as [b InaP].
destruct InaP as [InbF Inab].
apply FunctionImageRistrictionTheorem in InbF.
destruct InbF as [c InbF].
destruct InbF as [InbF Eqb].
rewrite <- Eqb in Inab.
clear Eqb.
clear b.
apply FunctionImageRistriction'DomTheorem in Inab.
destruct Inab as [b Inab].
destruct Inab as [InbC InbCond].
apply FunctionImageRistrictionTheorem in InbF.
destruct InbF as [d InbF].
destruct InbF as [IndN InbF].
assert(EqXdc : PowSet X d == c).
 apply InbF.
clear InbF.
apply UnionTheorem in IndN.
destruct IndN as [IndE | EqdE].
apply EmptyTheorem in IndE.
contradiction.
apply SingletonTheorem in EqdE.
rewrite EqdE in EqXdc.
clear EqdE.
clear d.
assert(IsPb : IsPair b).
 apply (CartesianIsPair _ _ _ InbC).
destruct IsPb as [l IsPb].
destruct IsPb as [r IsPb].
assert(InD : In l X /\ In r c).
 apply InPCartesian.
 rewrite <- IsPb.
 assumption.
destruct InD as [InlX Inrc].
assert(Eqclra : (AddSet (MultSet c l) r) == a).
 apply (TransitivityEq (AddSet (MultSet c (%(LeftPair _ _) {b ! InbC})) (%(RightPair _ _) {b ! InbC}))).
 assert(EqL : (%(LeftPair _ _) {b ! InbC}) == l).
  apply (TransitivityEq (%(LeftPair _ _) (Pair' {l ! InlX} {r ! Inrc}))).
  apply MapArgEq.
  apply (TransitivityEq b).
  apply ReflexivityEq.
  apply (TransitivityEq (Pair l r)).
  apply IsPb.
  apply EqualInPairPair'.
  split; apply ReflexivityEq.
  apply LeftPairTheorem.
 rewrite EqL.
 assert(EqR : (%(RightPair _ _) {b ! InbC}) == r).
  apply (TransitivityEq (%(RightPair _ _)(Pair' {l ! InlX} {r ! Inrc}))).
  apply MapArgEq.
  apply (TransitivityEq b).
  apply ReflexivityEq.
  apply (TransitivityEq (Pair l r)).
  apply IsPb.
  apply EqualInPairPair'.
  split; apply ReflexivityEq.
  apply RightPairTheorem.
 rewrite EqR.
 apply ReflexivityEq.
 apply InbCond.
 rewrite (PowSetTheoremEmpty) in EqXdc.
 rewrite <- EqXdc in Inrc.
 apply UnionTheorem in Inrc.
 destruct Inrc as [Cond | EqrE].
 apply EmptyTheorem in Cond.
 contradiction.
 apply SingletonTheorem in EqrE.
 rewrite EqrE in Eqclra.
 assert(Eqcla : (MultSet c l) == a).
  apply (TransitivityEq (AddSet (MultSet c l) Empty)).
  apply SymmetryEq.
  apply AddSetTheoremEmpty.
  apply Eqclra.
 assert(Eqal : a == l).
  apply (TransitivityEq (MultSet c l)).
  apply SymmetryEq.
  apply Eqcla.
  rewrite <- EqXdc.
  apply MultSetTheoremOne'.
 rewrite Eqal.
 assumption.



intro InaX.
unfold PowSet.
rewrite (TransitiveRecursiveFunctionTheorem).
apply UnionTheorem.
right.
apply UnionsTheorem.
exists (FunctionImageRistriction'Dom (fun d : #(Cartesian X (PowSet X Empty)) => AddSet (MultSet (PowSet X Empty) (%(LeftPair _ _) d)) (%(RightPair _ _) d))).
split.
 apply FunctionImageRistrictionTheorem.
 exists (PowSet X Empty).
 split.
 apply FunctionImageRistrictionTheorem.
  exists Empty.
  split.
   apply UnionTheorem.
   right.
   apply SingletonTheorem.
   apply ReflexivityEq.

   apply ReflexivityEq.

  apply ReflexivityEq.

 apply FunctionImageRistriction'DomTheorem.
 exists (Pair a Empty).
 split.
  apply CartesianTheorem.
  split.
  assumption.
  rewrite (PowSetTheoremEmpty).
  apply UnionTheorem.
  right.
  apply SingletonTheorem.
  apply ReflexivityEq.

  intros InPC.
  assert (InEN : In Empty (PowSet X Empty)).
   rewrite (PowSetTheoremEmpty).
   apply UnionTheorem.
   right.
   apply SingletonTheorem.
   apply ReflexivityEq.
  assert(EqL : (%(LeftPair _ _) {Pair a Empty ! InPC}) == a).
   apply (TransitivityEq (%(LeftPair _ _) (Pair' {a ! InaX} {Empty ! InEN}))).
   apply MapArgEq.
   apply (TransitivityEq (Pair a Empty)).
   apply ReflexivityEq.
   apply EqualInPairPair'.
   split; apply ReflexivityEq.
   apply LeftPairTheorem.
  rewrite EqL.
  assert(EqR : (%(RightPair _ _) {Pair a Empty ! InPC}) == Empty).
   apply (TransitivityEq (%(RightPair _ _) (Pair' {a ! InaX} {Empty ! InEN}))).
   apply MapArgEq.
   apply (TransitivityEq (Pair a Empty)).
   apply ReflexivityEq.
   apply EqualInPairPair'.
   split; apply ReflexivityEq.
   apply RightPairTheorem.
  rewrite EqR.
  apply (TransitivityEq (MultSet (PowSet X Empty) a)).
  apply AddSetTheoremEmpty.
  apply (TransitivityEq (MultSet (Next Empty) a)).
  assert(EqP : (PowSet X Empty) == (Next Empty)).
  apply PowSetTheoremEmpty.
  rewrite EqP.
  apply ReflexivityEq.
  apply MultSetTheoremOne'.
Qed.


Theorem PowSetLeftOrder : forall X A B, In (Next Empty) X -> In A B -> In (PowSet X A) (PowSet X B).
Proof.
intros X A B In1X InAB.
unfold PowSet at 2.
rewrite (TransitiveRecursiveFunctionTheorem).
apply UnionTheorem.
right.
apply UnionsTheorem.
exists (FunctionImageRistriction'Dom (fun dd : #(Cartesian X (PowSet X A)) => AddSet (MultSet (PowSet X A) (%(LeftPair _ _) dd)) (%(RightPair _ _) dd))).
split.
 apply FunctionImageRistrictionTheorem.
 exists (PowSet X A).
 split.
  apply FunctionImageRistrictionTheorem.
  exists A.
  split.
  assumption.
  apply ReflexivityEq.

  apply ReflexivityEq.

 apply FunctionImageRistriction'DomTheorem.
 exists (Pair (Next Empty) Empty).
 split.
  apply CartesianTheorem.
  split.
  assumption.
  unfold PowSet.
  rewrite (TransitiveRecursiveFunctionTheorem).
  apply UnionTheorem.
  left.
  apply UnionTheorem.
  right.
  apply SingletonTheorem.
  apply ReflexivityEq.

  intros InPC.
  assert(EqL : (%(LeftPair _ _) ({Pair (Next Empty) Empty ! InPC})) == (Next Empty)).
   apply LeftPairTheorem'.
  assert(EqR : (%(RightPair _ _) ({Pair (Next Empty) Empty ! InPC})) == Empty).
   apply RightPairTheorem'.
  rewrite EqL.
  rewrite EqR.
  rewrite AddSetTheoremEmpty.
  rewrite MultSetTheoremOne.
  apply ReflexivityEq.
Qed.

Theorem PowSetInEmpty : forall X Y, In Empty (PowSet X Y).
Proof.
intros X Y.
unfold PowSet.
rewrite (TransitiveRecursiveFunctionTheorem).
apply UnionTheorem.
left.
apply UnionTheorem.
right.
apply SingletonTheorem.
apply ReflexivityEq.
Qed.

Theorem PowSetSmall : forall X Y a b c, (In a Y /\ In b X /\ In c (PowSet X a)) -> In (AddSet (MultSet (PowSet X a) b) c) (PowSet X Y).
Proof.
intros X.
apply (SetInductionAxiom (fun Y => forall a b c, (In a Y /\ In b X /\ In c (PowSet X a)) -> In (AddSet (MultSet (PowSet X a) b) c) (PowSet X Y))).
intros Y InductionY a b c InD.
destruct InD as [InaY InD].
destruct InD as [InbX IncP].
unfold PowSet in IncP.
rewrite (TransitiveRecursiveFunctionTheorem) in IncP.
apply UnionTheorem in IncP.
destruct IncP as [IncN | IncU].
 (* destruct IncP1 *)
 apply UnionTheorem in IncN.
 destruct IncN as [cond | EqcE].
 apply EmptyTheorem in cond.
 contradiction.
 apply SingletonTheorem in EqcE.
 rewrite EqcE.
 rewrite (AddSetTheoremEmpty).
 clear EqcE.
 unfold PowSet at 2.
 rewrite (TransitiveRecursiveFunctionTheorem).
 apply UnionTheorem.
 right.
 apply UnionsTheorem.
 exists (FunctionImageRistriction'Dom (fun dd : #(Cartesian X (PowSet X a)) => AddSet (MultSet (PowSet X a) (%(LeftPair _ _) dd)) (%(RightPair _ _) dd ))).
 split.
  apply FunctionImageRistrictionTheorem.
  exists (PowSet X a).
  split.
   apply FunctionImageRistrictionTheorem.
   exists a.
   split.
   assumption.
   apply ReflexivityEq.

   apply ReflexivityEq.

  apply FunctionImageRistriction'DomTheorem.
  exists (Pair b Empty).
  split.
   apply CartesianTheorem.
   split.
   assumption.
   apply PowSetInEmpty.

   intro InPC.
   assert(EqL : (%(LeftPair _ _) {Pair b Empty ! InPC}) == b).
    apply LeftPairTheorem'.
   assert(EqR : (%(RightPair _ _) {Pair b Empty ! InPC}) == Empty).
    apply RightPairTheorem'.
   rewrite EqL.
   rewrite EqR.
   apply AddSetTheoremEmpty.

 (* destruct IncP2 *)
 apply UnionsTheorem in IncU.
 destruct IncU as [d IncU].
 destruct IncU as [IndF Incd].
 apply FunctionImageRistrictionTheorem in IndF.
 destruct IndF as [e IndF].
 destruct IndF as [IneF Eqd].
 rewrite <- Eqd in Incd.
 clear Eqd.
 clear d.
 apply FunctionImageRistriction'DomTheorem in Incd.
 destruct Incd as [d Incd].
 destruct Incd as [IndC EqP].
 assert(IsPd : IsPair d).
  apply (CartesianIsPair _ _ _ IndC).
 destruct IsPd as [f IsPd].
 destruct IsPd as [g IsPd].
 assert(InD : In f X /\ In g e).
  apply CartesianTheorem.
  rewrite IsPd in IndC.
  assumption.
 destruct InD as [InfX Inge].
 assert(Eqefgc : (AddSet (MultSet e f) g) == c).
  apply (TransitivityEq (AddSet (MultSet e (%(LeftPair _ _) {d ! IndC})) (%(RightPair _ _) {d ! IndC}))).
  assert(InPC : In (Pair f g) (Cartesian X e)).
   rewrite IsPd in IndC.
   assumption.
  assert(EqL : (%(LeftPair _ _) {d ! IndC}) == f).
   apply (TransitivityEq (%(LeftPair _ _) {Pair f g ! InPC})).
   apply MapArgEq.
   apply (TransitivityEq d).
   apply ReflexivityEq.
   apply (TransitivityEq (Pair f g)).
   apply IsPd.
   apply ReflexivityEq.
   apply LeftPairTheorem'.
  assert(EqR : (%(RightPair _ _) {d ! IndC}) == g).
   apply (TransitivityEq (%(RightPair _ _) {Pair f g ! InPC})).
   apply MapArgEq.
   apply (TransitivityEq d).
   apply ReflexivityEq.
   apply (TransitivityEq (Pair f g)).
   apply IsPd.
   apply ReflexivityEq.
   apply RightPairTheorem'.
  rewrite EqL.
  rewrite EqR.
  apply ReflexivityEq.
  apply EqP.
 clear EqP.
 clear IndC.
 clear IsPd.
 clear d.
 apply FunctionImageRistrictionTheorem in IneF.
 destruct IneF as [d IneF].
 destruct IneF as [Inda EqTe].
 assert(EqXde : PowSet X d == e).
  apply EqTe.
 clear EqTe.
 unfold PowSet at 2.
 rewrite (TransitiveRecursiveFunctionTheorem).
 apply UnionTheorem.
 right.
 apply UnionsTheorem.
 exists (FunctionImageRistriction'Dom (fun dd : #(Cartesian X (PowSet X a)) => AddSet (MultSet (PowSet X a) (%(LeftPair _ _) dd)) (%(RightPair _ _) dd))).
 split.
  apply FunctionImageRistrictionTheorem.
  exists (PowSet X a).
  split.
   apply FunctionImageRistrictionTheorem.
   exists a.
   split.
   assumption.
   apply ReflexivityEq.

   apply ReflexivityEq.

  apply FunctionImageRistriction'DomTheorem.
  exists (Pair b c).
  split.
   apply CartesianTheorem.
   split.
   assumption.
   rewrite <- Eqefgc.
   rewrite <- EqXde.
   apply (InductionY _ InaY).
   split.
   assumption.
   split.
   assumption.
   rewrite EqXde.
   assumption.

   intros InPC.
   assert(EqL : (%(LeftPair _ _) {Pair b c ! InPC}) == b).
    apply LeftPairTheorem'.
   assert(EqR : (%(RightPair _ _) {Pair b c ! InPC}) == c).
    apply RightPairTheorem'.
   rewrite EqL.
   rewrite EqR.
   apply ReflexivityEq.
Qed.

Theorem PowSetSmall' : forall X Y a b, (In a Y /\ In b X) -> In (MultSet (PowSet X a) b) (PowSet X Y).
Proof.
intros X Y a b InD.
destruct InD as [InaY InbX].
rewrite <- (AddSetTheoremEmpty (MultSet (PowSet X a) b)).
apply PowSetSmall.
split.
assumption.
split.
assumption.
apply PowSetInEmpty.
Qed.




Theorem PowSetTheoremAdd : forall X A B, (PowSet X (AddSet A B)) == (MultSet (PowSet X A) (PowSet X B)).
Proof.
intros X A.
apply (SetInductionAxiom (fun B => (PowSet X (AddSet A B)) == MultSet (PowSet X A) (PowSet X B))).
intros B InductionB.
apply EA.
intro a.
split.



intro InaP.
unfold PowSet in InaP.
rewrite (TransitiveRecursiveFunctionTheorem) in InaP.
apply UnionTheorem in InaP.
destruct InaP as [Ina1 | InaUU].

 apply UnionTheorem in Ina1.
 destruct Ina1 as [cond | Eqa0].
 apply EmptyTheorem in cond.
 contradiction.
 apply SingletonTheorem in Eqa0.
 rewrite Eqa0.
 clear Eqa0.
 clear a.
 assert(EqE : (AddSet (MultSet (PowSet X A) Empty) Empty) == Empty).
  apply (TransitivityEq (MultSet (PowSet X A) Empty)).
  apply AddSetTheoremEmpty.
  apply MultSetTheoremEmpty.
 rewrite <- EqE.
 apply MultSetSmall.
 split; apply PowSetInEmpty.

 apply UnionsTheorem in InaUU.
 destruct InaUU as [b InaUU].
 destruct InaUU as [InbF Inab].
 apply FunctionImageRistrictionTheorem in InbF.
 destruct InbF as [c InbF].
 destruct InbF as [IncF EqFb].
 rewrite <- EqFb in Inab.
 clear EqFb.
 clear b.
 apply FunctionImageRistriction'DomTheorem in Inab.
 destruct Inab as [b Inab].
 destruct Inab as [InbC EqP].
 assert(IsPb : IsPair b).
  apply (CartesianIsPair _ _ _ InbC).
 destruct IsPb as [d IsPb].
 destruct IsPb as [e IsPb].
 assert(InPC : In (Pair d e) (Cartesian X c)).
  rewrite IsPb in InbC.
  assumption.
 assert(Eqcde : (AddSet (MultSet c d) e) == a).
  apply (TransitivityEq (AddSet (MultSet c (%(LeftPair _ _) {b ! InbC})) (%(RightPair _ _) {b ! InbC}))).
  apply FunRewrite2.
  apply FunRewrite2.
  apply ReflexivityEq.
  apply (TransitivityEq (%(LeftPair _ _) {(Pair d e) ! InPC})).
  apply SymmetryEq.
  apply LeftPairTheorem'.
  apply MapArgEq.
  apply (TransitivityEq (Pair d e)).
  apply ReflexivityEq.
  apply (TransitivityEq b).
  apply SymmetryEq.
  apply IsPb.
  apply ReflexivityEq.
  apply (TransitivityEq (%(RightPair _ _) {(Pair d e) ! InPC})).
  apply SymmetryEq.
  apply RightPairTheorem'.
  apply MapArgEq.
  apply (TransitivityEq (Pair d e)).
  apply ReflexivityEq.
  apply (TransitivityEq b).
  apply SymmetryEq.
  apply IsPb.
  apply ReflexivityEq.
  apply EqP.
 clear EqP.
 clear IsPb.
 clear InbC.
 clear b.
 apply CartesianTheorem in InPC.
 destruct InPC as [IndX Inec].
 apply FunctionImageRistrictionTheorem in IncF.
 destruct IncF as [b IncF].
 destruct IncF as [InbA Eqbc].
 assert(EqXbc : (PowSet X b) == c).
  apply Eqbc.
 clear Eqbc.
 unfold AddSet in InbA.
 rewrite (TransitiveRecursiveFunctionTheorem) in InbA.
 apply UnionTheorem in InbA.
 destruct InbA as [InbA | InbF].
 (* b < A *)
  rewrite <- Eqcde.
  rewrite <- EqXbc.
  assert(EqInL : (AddSet (MultSet (PowSet X b) d) e) == (AddSet (MultSet (PowSet X A) Empty) (AddSet (MultSet (PowSet X b) d) e))).
   apply (TransitivityEq (AddSet Empty (AddSet (MultSet (PowSet X b) d) e))).
   apply SymmetryEq.
   apply AddSetTheoremEmpty'.
   assert(EqE : (MultSet (PowSet X A) Empty) == Empty).
    apply MultSetTheoremEmpty.
   rewrite EqE.
   apply ReflexivityEq.
  rewrite EqInL.
  clear EqInL.
  apply MultSetSmall.
  split.
  apply PowSetInEmpty.
  apply PowSetSmall.
  split.
  assumption.
  split.
  assumption.
  rewrite EqXbc.
  assumption.

 (* A <= b < A+B *)
  apply FunctionImageRistrictionTheorem in InbF.
  destruct InbF as [f InbF].
  destruct InbF as [InfB Eqb].
  assert(EqAfb : (AddSet A f) == b).
   apply Eqb.
  clear Eqb. 
  assert(EqXb : c == (MultSet (PowSet X A) (PowSet X f))).
   rewrite <- EqXbc.
   rewrite <- EqAfb.
   apply InductionB.
   assumption.
  rewrite EqXb in Inec.
  unfold MultSet in Inec.
  rewrite (TransitiveRecursiveFunctionTheorem) in Inec.
  apply UnionsTheorem in Inec.
  destruct Inec as [g Inec].
  destruct Inec as [IngF Ineg].
  apply FunctionImageRistrictionTheorem in IngF.
  destruct IngF as [h IngF].
  destruct IngF as [InhF Eqg].
  rewrite <- Eqg in Ineg.
  clear Eqg.
  clear g.
  apply FunctionImageRistrictionTheorem in Ineg.
  destruct Ineg as [g Ineg].
  destruct Ineg as [IngP Eqhge].
  apply FunctionImageRistrictionTheorem in InhF.
  destruct InhF as [i InhF].
  destruct InhF as [IniP EqTh].
  assert(EqXih : (MultSet (PowSet X A) i) == h).
   apply EqTh.
  clear EqTh.
  assert(Eqa : a == (AddSet (MultSet (PowSet X A) (AddSet (MultSet (PowSet X f) d) i)) g)).
   rewrite <- Eqcde.
   rewrite <- EqXbc.
   rewrite <- EqAfb.
   rewrite <- Eqhge.
   rewrite <- EqXih.
   apply (TransitivityEq (AddSet (AddSet (MultSet (PowSet X (AddSet A f)) d) (MultSet (PowSet X A) i)) g)).
   apply SymmetryEq.
   apply AddSetAssociativity.
   assert(EqAL : (AddSet (MultSet (PowSet X (AddSet A f)) d) (MultSet (PowSet X A) i)) == (MultSet (PowSet X A) (AddSet (MultSet (PowSet X f) d) i))).
    assert(EqP : (PowSet X (AddSet A f)) == (MultSet (PowSet X A) (PowSet X f))).
     apply InductionB.
     assumption.
    rewrite EqP.
    assert(EqPA : (MultSet (MultSet (PowSet X A) (PowSet X f)) d) == (MultSet (PowSet X A) (MultSet (PowSet X f) d))).
     apply MultSetAssociativity.
    rewrite EqPA.
    apply SymmetryEq.
    apply MultSetLeftDistributivity.
   rewrite EqAL.
   apply ReflexivityEq.
  rewrite Eqa.
  apply MultSetSmall.
  split.
   apply PowSetSmall.
   split.
   assumption.
   split.
   assumption.
   assumption.

   assumption.






intro InaM.
unfold MultSet in InaM.
rewrite (TransitiveRecursiveFunctionTheorem) in InaM.
apply UnionsTheorem in InaM.
destruct InaM as [b InaM].
destruct InaM as [InbF Inab].
apply FunctionImageRistrictionTheorem in InbF.
destruct InbF as [c InbF].
destruct InbF as [IncF Eqb].
rewrite <- Eqb in Inab.
clear Eqb.
clear b.
apply FunctionImageRistrictionTheorem in Inab.
destruct Inab as [b Inab].
destruct Inab as [InbP Eqcba].
apply FunctionImageRistrictionTheorem in IncF.
destruct IncF as [d IncF].
destruct IncF as [IndP EqTc].
assert(EqXdc : (MultSet (PowSet X A) d) == c).
 apply EqTc.
clear EqTc.
rewrite <- Eqcba.
rewrite <- EqXdc.
unfold PowSet in IndP.
rewrite (TransitiveRecursiveFunctionTheorem) in IndP.
apply UnionTheorem in IndP.
destruct IndP as [IndN | IndU].
 apply UnionTheorem in IndN.
 destruct IndN as [cont | EqdE].
 apply EmptyTheorem in cont.
 contradiction.
 apply SingletonTheorem in EqdE.
 rewrite EqdE.
 rewrite MultSetTheoremEmpty.
 rewrite AddSetTheoremEmpty'.
 clear Eqcba.
 clear EqXdc.
 clear EqdE.
 clear a.
 clear d.
 clear c.
 unfold PowSet in InbP.
 rewrite (TransitiveRecursiveFunctionTheorem) in InbP.
 apply UnionTheorem in InbP.
 destruct InbP as [InbN | InbU].
  apply UnionTheorem in InbN as [cond | EqbE].
  apply EmptyTheorem in cond.
  contradiction.
  apply SingletonTheorem in EqbE.
  rewrite EqbE.
  apply PowSetInEmpty.
 apply UnionsTheorem in InbU.
 destruct InbU as [a InbU].
 destruct InbU as [InaF Inba].
 apply FunctionImageRistrictionTheorem in InaF.
 destruct InaF as [c InaF].
 destruct InaF as [IncF Eqa].
 rewrite <- Eqa in Inba.
 clear Eqa.
 clear a.
 apply FunctionImageRistriction'DomTheorem in Inba.
 destruct Inba as [a Inba].
 destruct Inba as [InaC EqP].
 apply FunctionImageRistrictionTheorem in IncF.
 destruct IncF as [d IncF].
 destruct IncF as [IndA EqTc].
 assert(EqXdc : (PowSet X d) == c).
  apply EqTc.
 clear EqTc.
 assert (IsPa : IsPair a).
  apply (CartesianIsPair _ _ _ InaC).
 destruct IsPa as [e IsPa].
 destruct IsPa as [f IsPa].
 assert(IsPC : In (Pair e f) (Cartesian X c)).
  rewrite IsPa in InaC.
  assumption.
 assert(EqXef : (AddSet (MultSet c e) f) == b).
  apply (TransitivityEq (AddSet (MultSet c (%(LeftPair _ _) {a ! InaC})) (%(RightPair _ _) {a ! InaC}))).
  apply FunRewrite2.
  apply FunRewrite2.
  apply ReflexivityEq.
  apply (TransitivityEq (%(LeftPair _ _) {(Pair e f) ! IsPC})).
  apply SymmetryEq.
  apply LeftPairTheorem'.
  apply MapArgEq.
  apply (TransitivityEq (Pair e f)).
  apply ReflexivityEq.
  apply (TransitivityEq a).
  apply SymmetryEq.
  apply IsPa.
  apply ReflexivityEq.
  apply (TransitivityEq (%(RightPair _ _) {(Pair e f) ! IsPC})).
  apply SymmetryEq.
  apply RightPairTheorem'.
  apply MapArgEq.
  apply (TransitivityEq (Pair e f)).
  apply ReflexivityEq.
  apply (TransitivityEq a).
  apply SymmetryEq.
  apply IsPa.
  apply ReflexivityEq.
  apply EqP.
 apply CartesianTheorem in IsPC.
 destruct IsPC as [IneX Infc].
 clear EqP.
 clear InaC.
 clear IsPa.
 clear a.
 rewrite <- EqXef.
 rewrite <- EqXdc.
 apply PowSetSmall.
 split.
 unfold AddSet.
 rewrite (TransitiveRecursiveFunctionTheorem).
 apply UnionTheorem.
 left.
 assumption.
 split.
 assumption.
 rewrite <- EqXdc in Infc.
 assumption.
apply UnionsTheorem in IndU.
destruct IndU as [e IndU].
destruct IndU as [IneF Inde].
apply FunctionImageRistrictionTheorem in IneF.
destruct IneF as [f IneF].
destruct IneF as [InfF Eqe].
rewrite <- Eqe in Inde.
clear Eqe.
clear e.
apply FunctionImageRistriction'DomTheorem in Inde.
destruct Inde as [e Inde].
destruct Inde as [IneC EqP].
apply FunctionImageRistrictionTheorem in InfF.
destruct InfF as [g InfF].
destruct InfF as [IngB Eqf].
assert(EqXvg : (PowSet X g) == f).
 apply Eqf.
clear Eqf.
assert(IsPe : IsPair e).
 apply (CartesianIsPair _ _ _ IneC).
destruct IsPe as [h IsPe].
destruct IsPe as [i IsPe].
assert(InPC : In (Pair h i) (Cartesian X f)).
 rewrite IsPe in IneC.
 assumption.
assert(Eqfhi : (AddSet (MultSet f h) i) == d).
 apply (TransitivityEq (AddSet (MultSet f (%(LeftPair _ _) {e ! IneC})) (%(RightPair _ _) {e ! IneC}))).
 apply FunRewrite2.
 apply FunRewrite2.
 apply ReflexivityEq.
 apply (TransitivityEq (%(LeftPair _ _) {(Pair h i) ! InPC})).
 apply SymmetryEq.
 apply LeftPairTheorem'.
 apply MapArgEq.
 apply (TransitivityEq (Pair h i)).
 apply ReflexivityEq.
 apply (TransitivityEq e).
 apply SymmetryEq.
 apply IsPe.
 apply ReflexivityEq.
 apply (TransitivityEq (%(RightPair _ _) {(Pair h i) ! InPC})).
 apply SymmetryEq.
 apply RightPairTheorem'.
 apply MapArgEq.
 apply (TransitivityEq (Pair h i)).
 apply ReflexivityEq.
 apply (TransitivityEq e).
 apply SymmetryEq.
 apply IsPe.
 apply ReflexivityEq.
 apply EqP.
clear EqP.
apply CartesianTheorem in InPC.
destruct InPC as [InhX Inif].
clear IsPe.
clear IneC.
clear e.
rewrite <- Eqfhi.
rewrite <- EqXvg.
assert(EqR : (AddSet (MultSet (PowSet X A) (AddSet (MultSet (PowSet X g) h) i)) b) == (AddSet (MultSet (PowSet X (AddSet A g)) h) (AddSet (MultSet (PowSet X A) i) b))).
 apply (TransitivityEq (AddSet (AddSet (MultSet (PowSet X A) (MultSet (PowSet X g) h) ) (MultSet (PowSet X A) i)) b)).
 apply FunRewrite2.
 apply MultSetLeftDistributivity.
 apply ReflexivityEq.
 rewrite (AddSetAssociativity).
 apply FunRewrite2.
 apply (TransitivityEq (MultSet (MultSet (PowSet X A) (PowSet X g)) h)).
 apply SymmetryEq.
 apply MultSetAssociativity.
 apply FunRewrite2.
 apply SymmetryEq.
 apply InductionB.
 assumption.
 apply ReflexivityEq.
 apply ReflexivityEq.
rewrite EqR.
apply PowSetSmall.
split.
apply AddSetOrderSemigroupCondition.
assumption.
split.
assumption.
rewrite (InductionB _ IngB).
apply MultSetSmall.
split.
rewrite <- EqXvg in Inif.
assumption.
assumption.
Qed.
  










(**************)
(* Closed Set *)
(**************)

(* Definition *)
Definition NextClosedSet A := FunMapCond A A Next.
Definition AddSetClosedSet A := Fun2MapCond A A A AddSet.
Definition MultSetClosedSet A := Fun2MapCond A A A MultSet.
Definition PowSetClosedSet A := Fun2MapCond A A A PowSet.

Definition AddSetCommutativeSet A := forall x y, In x A -> In y A -> (AddSet x y) == (AddSet y x).
Definition MultSetCommutativeSet A := forall x y, In x A -> In y A -> (MultSet x y) == (MultSet y x).
Definition AddSetLeftCancellabilitySet A := forall a x y, In a A -> In x A -> In y A -> (AddSet a x) == (AddSet a y) -> x == y.
Definition AddSetRightCancellabilitySet A := forall a x y, In a A -> In x A -> In y A -> (AddSet x a) == (AddSet y a) -> x == y.


(* Map *)
Definition MNext A (CA : NextClosedSet A) : #(Map A A) := FunMap Next (CA).
Definition MAdd A (CA : AddSetClosedSet A) := Fun2Map AddSet CA.
Definition MMult A (CA : MultSetClosedSet A) := Fun2Map MultSet CA.
Definition MPow A (CA : PowSetClosedSet A) := Fun2Map PowSet CA.

(* MapTheorem *)
Theorem MNextTheorem : forall A (CA : NextClosedSet A) (a : #A),
%(MNext A CA) a == (Next a).
Proof.
intros A CA a.
unfold MNext.
apply FunMapTheorem.
Qed.

Theorem MAddTheorem : forall A (CA : AddSetClosedSet A) (x : #A) (y : #A),
%(MAdd A CA) [x;y] == (AddSet x y).
Proof.
intros A CA x y.
unfold MAdd.
rewrite (Fun2MapTheorem _ _ _).
apply FunRewrite2.
apply LeftPairTheorem.
apply RightPairTheorem.
Qed.

Theorem MMultTheorem : forall A (CA : MultSetClosedSet A) (x : #A) (y : #A),
%(MMult A CA) [x;y] == (MultSet x y).
Proof.
intros A CA x y.
unfold MMult.
rewrite (Fun2MapTheorem _ _ _).
apply FunRewrite2.
apply LeftPairTheorem.
apply RightPairTheorem.
Qed.

Theorem MPowTheorem : forall A (CA : PowSetClosedSet A) (x : #A) (y : #A),
%(MPow A CA) [x;y] == (PowSet x y).
Proof.
intros A CA x y.
unfold MPow.
rewrite (Fun2MapTheorem _ _ _).
apply FunRewrite2.
apply LeftPairTheorem.
apply RightPairTheorem.
Qed.


(* Algebras *)


(* Nature Number Closed*)
Theorem NextClosedSetNN : NextClosedSet NN.
Proof.
intros n InnNN.
apply PeanoAxiom2.
assumption.
Qed.


Theorem AddSetClosedSetNN : AddSetClosedSet NN.
Proof.
intros x y InxNN InyNN. 
assert(EqSN : (SSet NN (fun n => In (AddSet x n) NN)) == NN).
 apply PeanoAxiom5.
 apply SSetSubset.
 split.
  apply SSetTheorem.
  split.
  apply PeanoAxiom1.
  rewrite (AddSetTheoremEmpty).
  assumption.

  intros n InnS.
  apply SSetTheorem in InnS.
  destruct InnS as [InnNN NH].
  apply SSetTheorem.
  split.
  apply PeanoAxiom2.
  assumption.
  rewrite (AddSetTheoremNext).
  apply PeanoAxiom2.
  assumption.

rewrite <- EqSN in InyNN.
apply SSetTheorem in InyNN.
destruct InyNN as [InyNN InANN].
assumption.
Qed.
  

Theorem MultSetClosedSetNN : MultSetClosedSet NN.
Proof.
intros x y InxA InyA.
assert(EqS : (SSet NN (fun n => In (MultSet x n) NN)) == NN).
 apply PeanoAxiom5.
 apply SSetSubset.
 split.
  apply SSetTheorem.
  split.
  apply PeanoAxiom1.
  rewrite (MultSetTheoremEmpty).
  apply PeanoAxiom1.

  intros n InnS.
  apply SSetTheorem in InnS.
  destruct InnS as [InnN InMN].
  apply SSetTheorem.
  split.
  apply PeanoAxiom2.
  assumption.
  rewrite (MultSetTheoremNext).
  apply AddSetClosedSetNN.
  assumption.
  assumption.
rewrite <- EqS in InyA.
apply SSetTheorem in InyA.
destruct InyA as [InyA InMA].
assumption.
Qed.

Theorem AddSetCommutativeSetNN : AddSetCommutativeSet NN.
Proof.
intros x y InxNN InyNN.
assert(AddSetTheoremNextNN : forall x y, In y NN -> (AddSet (Next x) y) == (Next (AddSet x y))).
 intros a.
 apply (MathematicalInductionNN').
 split.
  apply (TransitivityEq (Next a)).  
  rewrite (AddSetTheoremEmpty).
  apply ReflexivityEq.
  rewrite (AddSetTheoremEmpty).
  apply ReflexivityEq.

  intros n InnNN EqH.
  apply (TransitivityEq (Next (AddSet (Next a) n))).
  apply (AddSetTheoremNext).
  rewrite EqH.
  rewrite AddSetTheoremNext.
  apply ReflexivityEq.

assert(Eq1 : forall n, In n NN -> (AddSet x n) == (AddSet n x)).
 apply MathematicalInductionNN'.
 split.
 rewrite (AddSetTheoremEmpty).
 rewrite (AddSetTheoremEmpty').
 apply ReflexivityEq.

 intros n InnNN EqA.
 apply (TransitivityEq (Next (AddSet x n))).
 apply (AddSetTheoremNext).
 rewrite EqA.
 rewrite <- (AddSetTheoremNextNN _ _ InxNN).
 apply ReflexivityEq.
apply Eq1.
assumption.
Qed.

Theorem MultSetCommutativeSetNN : MultSetCommutativeSet NN.
Proof.
intros a b InaNN InbNN.
assert(MultSetTheoremNextNN' : forall x, In x NN -> forall y, In y NN -> (MultSet (Next x) y) == (AddSet (MultSet x y) y)).
 intros x InxNN.
 apply MathematicalInductionNN'.
 split.
  apply (TransitivityEq Empty).
  apply MultSetTheoremEmpty.
  rewrite MultSetTheoremEmpty.
  apply SymmetryEq.
  apply AddSetTheoremEmpty.

  intros n InnNN HH.
  apply (TransitivityEq (AddSet (MultSet (Next x) n) (Next x))).
   apply MultSetTheoremNext.
  rewrite HH.
  apply (TransitivityEq (AddSet (AddSet (MultSet x n) n) (AddSet x (Next Empty)))).
   apply FunRewrite2.
   apply ReflexivityEq.
   apply SymmetryEq.
   apply (TransitivityEq (Next (AddSet x Empty))).
   apply AddSetTheoremNext.
   apply FunRewrite.
   apply AddSetTheoremEmpty.
  rewrite (AddSetAssociativity).
  apply (TransitivityEq (AddSet (MultSet x n) (AddSet (AddSet n x) (Next Empty)))).
   apply FunRewrite2.
   apply ReflexivityEq.
   apply SymmetryEq.
   apply AddSetAssociativity.
  apply (TransitivityEq (AddSet (MultSet x n) (AddSet (AddSet x n) (Next Empty)))).
   apply FunRewrite2.
   apply ReflexivityEq.
   apply FunRewrite2.
    apply AddSetCommutativeSetNN.
    assumption.
    assumption.
    apply ReflexivityEq.
  apply (TransitivityEq (AddSet (MultSet x n) (AddSet x (AddSet n (Next Empty))))).
   apply FunRewrite2.
   apply ReflexivityEq.
   apply AddSetAssociativity.
  apply (TransitivityEq (AddSet (AddSet (MultSet x n) x) (AddSet n (Next Empty)))).
   apply SymmetryEq.
   apply AddSetAssociativity.
  apply FunRewrite2.
   apply (TransitivityEq (AddSet (MultSet x n) (MultSet x (Next Empty)))).
    apply FunRewrite2.
    apply ReflexivityEq.
    apply SymmetryEq.
    apply MultSetTheoremOne.
   apply (TransitivityEq (MultSet x (AddSet n (Next Empty)))).
    apply SymmetryEq.
    apply MultSetLeftDistributivity.
   apply FunRewrite2.
    apply ReflexivityEq.
     apply (TransitivityEq (Next (AddSet n Empty))).
     apply AddSetTheoremNext.
     apply FunRewrite.
     apply AddSetTheoremEmpty.
    apply (TransitivityEq (Next (AddSet n Empty))).
    apply AddSetTheoremNext.
    apply FunRewrite.
    apply AddSetTheoremEmpty.

assert(Eq : forall n, In n NN -> MultSet a n == MultSet n a).
 apply MathematicalInductionNN'.
 split.
 apply (TransitivityEq Empty).
 apply MultSetTheoremEmpty.
 apply SymmetryEq.
 apply MultSetTheoremEmpty'.

 intros n InnNN Eqan.
 apply (TransitivityEq (MultSet a (AddSet n (Next Empty)))).
  apply FunRewrite2.
  apply ReflexivityEq.
  apply SymmetryEq.
  apply (TransitivityEq (Next (AddSet n Empty))).
   apply AddSetTheoremNext.
  apply FunRewrite.
  apply AddSetTheoremEmpty.
 apply (TransitivityEq (AddSet (MultSet a n) (MultSet a (Next Empty)))).
  apply MultSetLeftDistributivity.
 apply (TransitivityEq (AddSet (MultSet a n) a)).
  apply FunRewrite2.
  apply ReflexivityEq.
  apply MultSetTheoremOne.
 apply SymmetryEq.
 rewrite Eqan.
 apply MultSetTheoremNextNN'.
 assumption.
 assumption.
apply Eq.
assumption.
Qed.



Theorem AddSetLeftCancellabilitySetNN : AddSetLeftCancellabilitySet NN.
Proof.
assert(MainLemma : forall A, In A NN -> forall X, In X NN -> forall Y, In Y NN -> (AddSet A X) == (AddSet A Y) -> X == Y).
apply (MathematicalInductionNN' (fun A => forall X, In X NN -> forall Y, In Y NN -> (AddSet A X) == (AddSet A Y) -> X == Y)).
split.
 intros X InXNN Y InYNN AEq.
 apply (TransitivityEq (AddSet Empty X)).
  apply SymmetryEq.
  apply AddSetTheoremEmpty'.
 apply (TransitivityEq (AddSet Empty Y)).
  apply AEq.
 apply AddSetTheoremEmpty'.
intros A InANN InductionA.

intros X InXNN Y InYNN EqAA.
apply InductionA.
assumption.
assumption.
apply PeanoAxiom4.
apply (TransitivityEq (Next (AddSet X A))).
 apply FunRewrite.
 apply AddSetCommutativeSetNN.
 assumption.
 assumption.
apply (TransitivityEq (AddSet X (Next A))).
 apply SymmetryEq.
 apply AddSetTheoremNext.
apply (TransitivityEq (AddSet (Next A) X)).
 apply AddSetCommutativeSetNN.
 assumption.
 apply PeanoAxiom2.
 assumption.
apply (TransitivityEq (AddSet (Next A) Y)).
 apply EqAA.
apply (TransitivityEq (AddSet Y (Next A))).
 apply AddSetCommutativeSetNN.
 apply PeanoAxiom2.
 assumption.
 assumption.
apply (TransitivityEq (Next (AddSet Y A))).
 apply AddSetTheoremNext.
apply FunRewrite.
apply AddSetCommutativeSetNN.
assumption.
assumption.

intros A X Y InANN InXNN InYNN EqAd.
apply (MainLemma A InANN X InXNN Y InYNN EqAd).
Qed.

Theorem AddSetRightCancellabilitySetNN : AddSetRightCancellabilitySet NN.
Proof.
intros x a b InxNN InaNN InbNN EqA.
apply (AddSetLeftCancellabilitySetNN x).
assumption.
assumption.
assumption.
rewrite AddSetCommutativeSetNN.
rewrite EqA.
apply AddSetCommutativeSetNN.
assumption.
assumption.
assumption.
assumption.
Qed.







(**********************)
(* Nature Calculation *)
(**********************)
Definition NNNext : #(Map NN NN) := MNext NN NextClosedSetNN. 
Definition NNAdd : #(BOperation NN) := MAdd NN AddSetClosedSetNN.
Definition NNMult : #(BOperation NN) := MMult NN MultSetClosedSetNN.

Fixpoint nat_to_NN (n : nat) : #NN :=
match n with
| O => {Empty ! PeanoAxiom1}
| S n => %NNNext (nat_to_NN n)
end.

Notation " x {<<nat_NN }" := (nat_to_NN x)(at level 2).

Theorem Next_nat_NN : forall n : nat, %NNNext n{<<nat_NN} == (S n){<<nat_NN}.
Proof.
intro n.
induction n.
hyperreflexivity.
apply (TransitivityEq (%NNNext (%NNNext (n{<<nat_NN})))).
 apply MapArgEq.
 rewrite IHn.
 hyperreflexivity.
hyperreflexivity.
Qed.

(* next *)
Theorem NNNextTheorem : forall n : #NN, (%NNNext n) == Next n.
Proof.
intro n.
unfold NNNext.
rewrite MNextTheorem.
hyperreflexivity.
Qed.

Theorem MathematicalInductionNN : forall (P : (#NN) -> Prop),
RPred P ->
P (nat_to_NN 0) -> (forall n, P n -> P (%NNNext n)) ->
forall n, P n.
Proof.
intros P' RP P0 Pn n.
put MathematicalInductionNN' ind.
assert (RP' : RPred' P').
 apply RPredSimplify.
 apply RP.
unfold RPred' in RP'.
set (fun (x : SET) => exists prf : In x NN, P' {x ! prf}) as P.
assert (IndH1 : P Empty).
 unfold P.
 exists PeanoAxiom1.
 generalize P0.
 apply RP'.
 hyperreflexivity.
assert(IndH2 : (forall n, In n NN -> P n -> P (Next n))).
 intros n' InnNN Pnn.
 unfold P in Pnn.
 destruct Pnn as [Inn'N PH].
 unfold P.
 assert(InNn : In (Next n') NN).
  apply PeanoAxiom2.
  apply InnNN.
 exists InNn.
 cut (P' (%NNNext {n' ! Inn'N})).
  apply RP'.
  rewrite NNNextTheorem.
  hyperreflexivity.
 apply Pn.
 apply PH.
put (ind _ (conj IndH1 IndH2)) Ind.
assert(InnNN : In n NN).
 apply SetProp.
put (Ind _ InnNN) Ind'.
destruct Ind' as [InH PH].
generalize PH.
apply RP'.
hyperreflexivity.
Qed.



(* add *)
Theorem NNAddTheorem1 : forall n : #NN, %NNAdd [n ; 0{<<nat_NN}] == n.
Proof.
intros n.
unfold NNAdd.
rewrite MAddTheorem.
rewrite AddSetTheoremEmpty.
hyperreflexivity.
Qed.


Theorem NNAddTheorem2 : forall n m : #NN, %NNAdd [n ; (%NNNext m)] == %NNNext (%NNAdd [n ; m]).
Proof.
intros n m.
unfold NNAdd at 1.
rewrite MAddTheorem.
rewrite NNNextTheorem.
rewrite AddSetTheoremNext.
rewrite NNNextTheorem.
unfold NNAdd.
rewrite MAddTheorem.
hyperreflexivity.
Qed.

Theorem NNAdd_Ope_CommCond :
Ope_CommCond NNAdd.
Proof.
intros a b.
unfold NNAdd at 1.
rewrite MAddTheorem.
apply (TransitivityEq (AddSet b a)).
 apply AddSetCommutativeSetNN.
 apply SetProp.
 apply SetProp.
unfold NNAdd.
rewrite MAddTheorem.
hyperreflexivity.
Qed.

Theorem NNAdd_Ope_SGrpCond :
Ope_SGrpCond NNAdd.
Proof.
intros a b c.
apply (TransitivityEq (AddSet (AddSet a b) c)).
 unfold NNAdd.
 rewrite MAddTheorem.
 rewrite MAddTheorem.
 hyperreflexivity.
rewrite AddSetAssociativity.
unfold NNAdd.
rewrite MAddTheorem.
rewrite MAddTheorem.
hyperreflexivity.
Qed.

Theorem NN0IsIdent : &&IsIdent NNAdd (nat_to_NN 0).
Proof.
apply IsIdentTheoremR.
apply NNAdd_Ope_CommCond.
intros a.
apply NNAddTheorem1.
Qed.

Theorem NNAdd_Ope_IdentCond :
Ope_IdentCond NNAdd.
Proof.
exists (nat_to_NN 0).
apply NN0IsIdent.
Qed.

Theorem NNAdd_Ope_MonoidCond :
Ope_MonoidCond NNAdd.
Proof.
split.
apply NNAdd_Ope_SGrpCond.
apply NNAdd_Ope_IdentCond.
Qed.

Theorem NNAdd_Ope_CMonoidCond :
Ope_CMonoidCond NNAdd.
Proof.
split.
apply NNAdd_Ope_MonoidCond.
apply NNAdd_Ope_CommCond.
Qed.

Definition NNAdd_CMonoid :=
_{<Ope_CMonoid ! NNAdd_Ope_CMonoidCond}.

Theorem NNAdd_comm_plus : forall n m,
%NNAdd [nat_to_NN n; nat_to_NN m] == nat_to_NN (n+m).
Proof.
induction n.
 intro m.
 apply (TransitivityEq (%NNAdd [nat_to_NN m ; nat_to_NN 0])).
  apply NNAdd_Ope_CommCond.
 rewrite NNAddTheorem1.
 simpl.
 hyperreflexivity.

intro m.
rewrite NNAdd_Ope_CommCond.
apply (TransitivityEq (%NNAdd [nat_to_NN m; %NNNext (nat_to_NN n)])).
 apply MapArgEq.
 apply EqualInPair'R.
 rewrite Next_nat_NN.
 hyperreflexivity.
rewrite NNAddTheorem2.
apply (TransitivityEq (nat_to_NN (S (n+m)))).
 rewrite (MapArgEq _ (NNAdd_Ope_CommCond _ _)).
 rewrite (MapArgEq _ (IHn _)).
 rewrite Next_nat_NN.
 hyperreflexivity.
assert(Eqn : S(n+m) = (S n + m)).
 simpl.
 reflexivity.
rewrite Eqn.
hyperreflexivity.
Qed.

Theorem NNAddLeftCancell : forall a x y,
%NNAdd [a;x] == %NNAdd[a;y] -> x == y.
Proof.
intros a x y NNAddEq.
apply (AddSetLeftCancellabilitySetNN a).
apply SetProp.
apply SetProp.
apply SetProp.
apply (TransitivityEq (%NNAdd [a;x])).
 unfold NNAdd.
 rewrite MAddTheorem.
 hyperreflexivity.
rewrite NNAddEq.
unfold NNAdd.
rewrite MAddTheorem.
hyperreflexivity.
Qed.

Theorem NNAddRightCancell : forall a x y,
%NNAdd [x;a] == %NNAdd[y;a] -> x == y.
Proof.
intros a x y NNAddEq.
apply (AddSetRightCancellabilitySetNN a).
apply SetProp.
apply SetProp.
apply SetProp.
apply (TransitivityEq (%NNAdd [x;a])).
 unfold NNAdd.
 rewrite MAddTheorem.
 hyperreflexivity.
rewrite NNAddEq.
unfold NNAdd.
rewrite MAddTheorem.
hyperreflexivity.
Qed.



(* mult *)
Theorem NNMultTheorem0 : forall n,
%NNMult [n;nat_to_NN 0] == nat_to_NN 0.
Proof.
intros n.
unfold NNMult.
rewrite MMultTheorem.
rewrite MultSetTheoremEmpty.
hyperreflexivity.
Qed.

Theorem NNMultTheorem1 : forall n,
%NNMult [n;nat_to_NN 1] == n.
Proof.
intro n.
unfold NNMult.
rewrite MMultTheorem.
apply (TransitivityEq (MultSet n (Next Empty))).
 apply FunRewrite2.
 hyperreflexivity.
 apply (TransitivityEq (%NNNext (nat_to_NN 0))).
  hyperreflexivity.
 rewrite NNNextTheorem.
 hyperreflexivity.
rewrite MultSetTheoremOne.
hyperreflexivity.
Qed.

Theorem NNMultTheorem2 : forall n m,
%NNMult [n;%NNNext m] == %NNAdd [%NNMult [n;m];n].
Proof.
intros n m.
unfold NNMult at 1.
rewrite MMultTheorem.
unfold NNNext at 1.
rewrite MNextTheorem.
rewrite MultSetTheoremNext.
unfold NNAdd.
rewrite MAddTheorem.
unfold NNMult.
rewrite MMultTheorem.
hyperreflexivity.
Qed.

Theorem NNMult_Ope_SGrpCond : Ope_SGrpCond NNMult.
Proof.
intros a b c.
unfold NNMult at 1.
rewrite MMultTheorem.
unfold NNMult at 1.
rewrite MMultTheorem.
rewrite MultSetAssociativity.
unfold NNMult at 1.
rewrite MMultTheorem.
unfold NNMult.
rewrite MMultTheorem.
hyperreflexivity.
Qed.

Theorem NNMult_Ope_CommCond : Ope_CommCond NNMult.
Proof.
intros a b.
unfold NNMult at 1.
rewrite MMultTheorem.
unfold NNMult.
rewrite MMultTheorem.
apply MultSetCommutativeSetNN.
apply SetProp.
apply SetProp.
Qed.

Theorem NN1IsIdent : &&IsIdent NNMult (nat_to_NN 1).
Proof.
apply IsIdentTheoremR.
apply NNMult_Ope_CommCond.
intros a.
apply NNMultTheorem1.
Qed.

Theorem NNMult_Ope_IdentCond : Ope_IdentCond NNMult.
Proof.
exists (nat_to_NN 1).
apply NN1IsIdent.
Qed.

Theorem NNMult_Ope_MonoidCond : Ope_MonoidCond NNMult.
Proof.
split.
apply NNMult_Ope_SGrpCond.
apply NNMult_Ope_IdentCond.
Qed.

Theorem NNMult_Ope_CMonoidCond : Ope_CMonoidCond NNMult.
Proof.
split.
apply NNMult_Ope_MonoidCond.
apply NNMult_Ope_CommCond.
Qed.

Theorem NNAdd_NNMultDistDond : Ope2_DistDond NNAdd NNMult.
apply Dist_LDistCommCond.
apply NNMult_Ope_CommCond.
intros a b c.
unfold NNMult at 1.
rewrite MMultTheorem.
unfold NNAdd at 1.
rewrite MAddTheorem.
rewrite MultSetLeftDistributivity.
unfold NNAdd.
rewrite MAddTheorem.
apply FunRewrite2.
unfold NNMult.
rewrite MMultTheorem.
hyperreflexivity.
unfold NNMult.
rewrite MMultTheorem.
hyperreflexivity.
Qed.

Theorem NNAdd_NNMultLDistDond : Ope2_LDistDond NNAdd NNMult.
Proof.
apply Ope2_LDist.
apply Dist_LDist.
apply Ope2_Dist.
apply NNAdd_NNMultDistDond.
Qed.

Theorem NNAdd_NNMultRDistDond : Ope2_RDistDond NNAdd NNMult.
Proof.
apply Ope2_RDist.
apply Dist_RDist.
apply Ope2_Dist.
apply NNAdd_NNMultDistDond.
Qed.
  




