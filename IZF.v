

Require Import logic.

Axiom EA : forall A B ,
(forall x , In x A <-> In x B)
-> (A == B).

Definition Subset A B := forall c , In c A -> In c B.
(*
Notation "a <== b" := (Subset a b) (at level 1).
Notation "a ==> b" := (Subset b a) (at level 1).
*)

(* Up Cast *)
Definition UpCast A B (sub : Subset A B) : (#A) -> (#B).
intro a.
apply {a ! (sub _ (SetProp a))}.
Defined.
Notation " x {< sub }" := (UpCast _ _ sub x)(at level 2).

Theorem USETEq : forall {A B} (a : #A) (sub : Subset A B), (a{<sub}) == a.
Proof.
intros A B a sub.
apply ReflexivityEq.
Qed.

Theorem USETEq' : forall {A B} (a : #A) (sub : Subset A B), a == (a{<sub}).
Proof.
intros A B a sub.
apply SymmetryEq.
apply USETEq.
Qed.


Theorem ReflexivitySubset : forall A , Subset A A.
Proof.
intro A.
intro c.
auto.
Qed.

Theorem ReflexivitySubset2 : forall A B, A == B -> Subset A B.
Proof.
intros A B eq.
rewrite eq.
apply ReflexivitySubset.
Qed.


Theorem AntisymmetrySubset : forall A B ,
Subset A B -> Subset B A -> (A == B).
Proof.
intros A B S1 S2.
apply EA.
intro x.
split.

 apply S1.
 apply S2.
Qed.

Theorem TransitivitySubset : forall {A C} B,
Subset A B -> Subset B C -> Subset A C.
Proof.
intros A C B S1 S2.
intro x.
intro InxA.
apply S2.
apply S1.
auto.
Qed.

Theorem SubsetEq : forall A B , 
(Subset A B /\ Subset B A) -> A == B.
Proof.
intros A B SD.
destruct SD as [S1 S2].
apply (AntisymmetrySubset _ _ S1 S2).
Qed.

(*Empty Set*)

Definition NonEmpty A :=
exists a , In a A.

Definition IsEmpty A := 
forall x , ~In x A.

Axiom EmptyAxiom : exists x , IsEmpty x.

Theorem UniqueEmpty : Unique IsEmpty.
Proof.
split.
apply EmptyAxiom.
intros x y Ex Ey.
apply EA.
intros c.
split; intro HH.
apply Ex in HH.
tauto.
apply Ey in HH.
tauto.
Qed.

Theorem NNEmpty : forall x , ~NonEmpty x -> IsEmpty x.
Proof.
intros x NNx.
generalize (DeMorganNEF _ NNx); intro NNx'.
tauto.
Qed.


Definition Empty := UniqueOut IsEmpty UniqueEmpty.

Theorem EmptyTheorem : IsEmpty Empty.
Proof.
apply (HUniqueOut IsEmpty).
Qed.

Theorem AllSetHasEmpty : forall A , Subset Empty A.
Proof.
intro A.
intros c IncE.
apply EmptyTheorem in IncE.
tauto.
Qed.

(*UnorderdPair*)
Definition IsUnorderdPair a b X := forall c ,
In c X <->
(c==a \/ c==b).

Axiom UnorderdPairAxiom : forall a b ,
exists X , IsUnorderdPair a b X.

Theorem UniqueUnorderdPair : forall a b,
Unique (IsUnorderdPair a b).
Proof.
intros a b.
split.
apply UnorderdPairAxiom.
intros x y Ux Uy.
apply EA.
intro c.
split; intro Inc.

 apply Uy.
 apply Ux in Inc.
 auto.

 apply Ux.
 apply Uy in Inc.
 auto.
Qed.

Definition UnorderdPair a b :=
UniqueOut (IsUnorderdPair a b) (UniqueUnorderdPair a b).

Theorem UnorderdPairTheorem : forall a b, 
forall c , In c (UnorderdPair a b) <->
(c==a \/ c==b).
Proof.
intros a b.
apply (HUniqueOut (IsUnorderdPair a b)).
Qed.



Definition Singleton a := UnorderdPair a a.

Theorem SingletonTheorem : forall a b,
In a (Singleton b) <-> a==b.
Proof.
intros a b.
split.
intro S.
apply UnorderdPairTheorem in S.
tauto.
intro Eqab.
rewrite Eqab.
apply UnorderdPairTheorem.
auto.
Qed.

Theorem SingletonInEq : forall a (x y : #(Singleton a)),
x == y.
Proof.
intros a x y.
put (SetProp x) Eqxa.
put (SetProp y) Eqya.
apply SingletonTheorem in Eqxa.
apply SingletonTheorem in Eqya.
rewrite Eqxa.
rewrite Eqya.
apply ReflexivityEq.
Qed.


(*Unions*)
Definition IsUnions A U :=
forall c , 
In c U <-> (exists a , In a A /\ In c a).

Axiom UnionsAxiom : forall A , exists U,
IsUnions A U.

Theorem UniqueUnions : forall A , Unique (IsUnions A).
Proof.
intro A.
split.
apply UnionsAxiom.
intros x y Ux Uy.
apply EA.
intro c.
split; intro Inc.
 apply Uy.
 apply Ux.
 auto.

 apply Ux.
 apply Uy.
 auto.
Qed.

Definition Unions A := UniqueOut (IsUnions A) (UniqueUnions A).

Theorem UnionsTheorem : forall A ,
forall c , 
In c (Unions A) <-> (exists a , In a A /\ In c a).
Proof.
intro A.
apply (HUniqueOut (IsUnions A)).
Qed.



(* Separation *)
Definition IsSeparation A P S :=
forall c, In c S <-> (In c A /\ P c).



Definition Separation := forall A P , exists S, IsSeparation A P S.


 (* Reference : Replacement and Collection in Intuitionistic Set Theory *)
Definition Collection := forall (P : SET -> SET -> Prop) A,
(forall x,In x A -> exists y, P x y) ->
exists B, forall x , In x A ->
exists y, In y B /\ P x y.

Definition Replacement := forall (P : SET -> SET -> Prop) A,
(forall a , In a A -> Unique(fun b => P a b)) ->
exists B, forall a, In a A -> exists b, In b B /\ P a b.

Definition Replacement' := forall (P : SET -> SET -> Prop) A,
(forall a , In a A -> Unique (fun b => P a b)) ->
exists B, forall b, (In b B <-> exists a, In a A /\ P a b).

Definition Replacement'' := forall (P : SET -> SET -> Prop),
(forall a b c, P a b /\ P a c -> b == c) ->
forall D, exists R, forall x, (In x R <-> exists d, In d D /\ P d x).


Theorem Collection_Replacement : Collection -> Replacement.
Proof.
intro col.
intros P A HH.
generalize (col P A); intro col'.
clear col.
assert (collem : forall x , In x A -> exists y , P x y).
 intros x InxA.
 destruct (HH _ InxA) as [Exs Unq].
 apply Exs.
generalize (col' collem); intro col.
destruct col as [B col].
exists B.
apply col.
Qed.


Theorem Replacement'_Replacement : Replacement' -> Replacement.
Proof.
intro rep.
intros P A HH.
generalize (rep P A HH); intro rep'.
destruct rep' as [B rep'].
exists B.
intros a InaA.
destruct (HH _ InaA) as [Exs Unq].
destruct Exs as [b Exs].
exists b.
split.
 apply rep'.
 exists a.
 split; auto.

 auto.
Qed.

Theorem Separation_Replacement_Replacement' : Separation /\ Replacement -> Replacement'.
Proof.
intros HH P.
destruct HH as [sep rep].
intros A HH.
generalize (rep P A HH); intro rep'.
destruct rep' as [B rep'].
destruct (sep B (fun b => exists a, In a A /\ P a b)) as [B' rep''].
exists B'.
intro c.
split.
 intro IncB.
 apply rep'' in IncB.
 destruct IncB as [IncB DD].
 auto.

 intro DD.
 apply rep''.
 split.
  destruct DD as [a DD].
  destruct DD as [InaA Pac].
  destruct (HH _ InaA) as [Exs Unq].
  destruct (rep' _ InaA) as [b rep''''].
  destruct rep'''' as [InbB Pab].
  assert (eqbc : b == c).
  apply (Unq _ _ Pab Pac).
  rewrite <- eqbc.
  auto.

 auto.
Qed.


Theorem Replacement''_Replacement' : Replacement'' -> Replacement'.
Proof.
intro rep.
intros P A HH.
generalize (rep (fun a b => P a b /\ In a A)); intro rep'.
assert(repHH : forall a b c, (P a b /\ In a A) /\ (P a c /\ In a A) -> b == c).
 intros a b c HD.
 destruct HD as [P1 P2].
 destruct P1 as [P1 InaA1].
 destruct P2 as [P2 InaA2].
 generalize (HH _ InaA1); intro HH'.
 apply (UniqueEqApply (fun x => P a x)).
 auto.
 split; auto.
generalize (rep' repHH A); intro rep''.
destruct rep'' as [R rep''].
exists R.
intros b.
destruct (rep'' b) as [rep1 rep2].
split.
 intro InbR.
 apply rep1 in InbR.
 destruct InbR as [a InbR].
 exists a.
 split; tauto.

 intro HHH.
 apply rep2.
 destruct HHH as [a HHH].
 exists a.
 split.
 tauto.
 split.
 tauto.
 tauto.
Qed.

Theorem Replacement''_Separation : Replacement'' -> Separation.
Proof.
intros rep.
intros A P.
generalize (rep (fun a b => P a /\ a==b)); intro rep'.
assert(repInd : forall a b c, (P a /\ a==b) /\ (P a /\ a==c) -> b==c).
 intros a b c PH.
 destruct PH as [Pa Pb].
 destruct Pa as [Pa Eqab].
 destruct Pb as [Pb Eqac].
 apply (TransitivityEq a).
 rewrite Eqab.
 auto.
 auto.
generalize (rep' repInd A); intro rep''.
destruct rep'' as [S rep''].
exists S.
intro c.
specialize rep'' with c.
split; intro HH.
 apply rep'' in HH.
 destruct HH as [d HH].
 destruct HH as [IndA HH].
 destruct HH as [Pd Eqdc].
 split.
 rewrite <- Eqdc.
 auto.
 rewrite <- Eqdc.
 auto.

 apply rep''.
 exists c.
 split.
 tauto.
 split.
 tauto.
 
 split; tauto.
Qed.
 

Theorem Separation_Replacement'_Replacement'' : Separation /\ Replacement' -> Replacement''.
Proof.
intros HH P.
destruct HH as [sep rep].
intros repHH D.
generalize (sep D (fun d => exists r, P d r)); intro sep'.
clear sep.
destruct sep' as [S sep].
generalize (rep P S); intro rep'.
assert (repInd : forall a , In a S -> Unique (fun b => P a b)).
 intros a InaS.
 split.
  generalize (sep a); intro sep'.
  apply sep' in InaS.
  destruct InaS as [InaD SepHH].
  auto.

  intros b c Pb Pc.  
  apply (repHH a); auto.
generalize (rep' repInd); intro rep''.
destruct rep'' as [R rep''].
exists R.
intro b.
specialize rep'' with b.
split; intro HH.
 apply rep'' in HH.
 destruct HH as [d HH].
 destruct HH as [IndS Pdb].
 exists d.
 split; auto.
 apply (sep d) in IndS.
 tauto.

 apply rep''.
 destruct HH as [d HH].
 destruct HH as [IndD Pdb].
 exists d.
 split; auto.
 apply sep.
 split.
 auto.
 exists b.
 auto.
Qed.







Axiom CollectionAxiom : Collection.
Axiom SeparationAxiom : Separation.



Theorem ReplacementAxiom : Replacement.
Proof.
apply Collection_Replacement.
apply CollectionAxiom.
Qed.

Theorem Replacement'Axiom : Replacement'.
Proof.
apply Separation_Replacement_Replacement'.
split.
apply SeparationAxiom.
apply ReplacementAxiom.
Qed.

Theorem Replacement''Axiom : Replacement''.
Proof.
apply Separation_Replacement'_Replacement''.
split.
apply SeparationAxiom.
apply Replacement'Axiom.
Qed.


Theorem UniqueSeparation : forall P A ,
Unique (IsSeparation P A).
Proof.
intros P A.
split.
apply SeparationAxiom.
intros x y Sx Sy.
apply EA.
intro c.
split; intro Inc.

 apply Sy.
 apply Sx.
 auto.

 apply Sx.
 apply Sy.
 auto.
Qed.



Definition SSet A P :=
UniqueOut (IsSeparation A P) (UniqueSeparation A P).

Definition SSet' A (P : (#A) -> Prop) :=
UniqueOut (IsSeparation A (fun v => In v A /\ forall prf : In v A, P {v!prf})) (UniqueSeparation A (fun v => In v A /\ forall prf : In v A, P {v!prf})).

Theorem SSetTheorem : forall A P ,
forall c, In c (SSet A P) <-> 
(In c A /\ P c).
Proof.
intros A P c.
apply (HUniqueOut (IsSeparation A P)).
Qed.


Theorem SSet'Theorem : forall A P , 
forall c , In c (SSet' A P) <->
(In c A /\ forall prf : In c A, P {c ! prf}).
Proof.
intros A P c.
split.
 intro IncS.
 apply SSetTheorem in IncS.
 destruct IncS as [IncA IncS].
 auto.

 intro HH.
 destruct HH as [IncA PH].
 apply SSetTheorem.
 split.
 auto.
 split.
 auto.
 auto.
Qed.

Theorem SSetSubset : forall A P , Subset (SSet A P) A.
Proof.
intros A P c IncS.
apply SSetTheorem in IncS.
destruct IncS as [IncA Pc].
auto.
Qed.

Theorem SSet'Subset : forall A P, Subset (SSet' A P) A.
Proof.
intros A P.
apply (SSetSubset).
Qed.

Theorem SubsetInSSetSet : forall A1 A2 (P1 : SET -> Prop) (P2 : SET -> Prop),
Subset A1 A2 -> (forall x, In x A1 -> P1 x -> P2 x) -> Subset (SSet A1 P1) (SSet A2 P2).
Proof.
intros A1 A2 P1 P2 sub HH.
intros s Ins1.
apply SSetTheorem in Ins1.
destruct Ins1 as [InsA PH1].
apply SSetTheorem.
split.
apply sub.
auto.
apply HH.
auto.
auto.
Qed.


Theorem SubsetInSSet'Set : forall A1 A2 (P1 : (#A1) -> Prop) (P2 : (#A2) -> Prop),
Subset A1 A2 ->
(forall (a1 : #A1) (a2 : #A2), a1 == a2 -> P1 a1 -> P2 a2) ->
Subset (SSet' A1 P1) (SSet' A2 P2).
Proof.
intros A1 A2 P1 P2 sub EquivH.
apply SubsetInSSetSet.
auto.
intros x InxA2 H1.
apply sub in InxA2.
split.
auto.
destruct H1 as [InxA1 PH1].
intro InxA2'.
specialize PH1 with InxA1.
assert(EqH : {x!InxA1} == {x!InxA2'}).
 apply ReflexivityEq.
apply (EquivH _ _ EqH).
auto.
Qed.

Theorem EqualInSSetSet : forall A1 A2 P1 P2, A1 == A2 ->
(forall x, In x A1 -> (P1 x <-> P2 x)) ->
(SSet A1 P1) == (SSet A2 P2).
Proof.
intros A1 A2 P1 P2 EqH HH.
apply (AntisymmetrySubset).
 apply SubsetInSSetSet.
 rewrite EqH.
 apply ReflexivitySubset.
 intros x InxA1 PH1.
 apply (HH _ InxA1).
 auto.

 apply SubsetInSSetSet.
 rewrite EqH.
 apply ReflexivitySubset.
 intros x InxA2 PH2.
 rewrite <- EqH in InxA2.
 apply (HH _ InxA2).
 auto.
Qed.

Theorem EqualInSSet'Set : forall A1 A2 P1 P2, A1 == A2 ->
(forall (a1 : #A1) (a2 : #A2), a1 == a2 -> (P1 a1 <-> P2 a2)) ->
(SSet' A1 P1) == (SSet' A2 P2).
Proof.
intros A1 A2 P1 P2 Eql EquivH.
apply EqualInSSetSet.
auto.
intros x InxA1.
split; intro HH.
 destruct HH as [InxA HH].
 rewrite Eql in InxA1.
 split.
 auto.
 intro InxA1'.
 apply (EquivH {x!InxA} {x!InxA1'}).
 apply ReflexivityEq.
 auto.

 split.
 auto.
 intro InxA1'.
 destruct HH as [InxA HH].
 specialize HH with InxA.
 apply (EquivH {x!InxA1'} {x!InxA}).
 apply ReflexivityEq.
 auto.
Qed.





Theorem UniqueFunctionImageRistriction : forall (F : SET -> SET) A,
Unique (fun B => forall b , In b B <-> (exists a, In a A /\ (F a) == b)).
Proof.
intros F A.
split.
generalize (Replacement'Axiom (fun a b => (F a) == b) A); intro HH.
assert (HInd : forall a, In a A -> Unique (fun b => (F a) == b)).
 intros a InaA.
 split.
 exists (F a).
 auto.
 intros x y Hx Hy.
 transitivity (F a).
 rewrite Hx.
 auto.
 auto.
destruct (HH HInd) as [B HH'].
exists B.
auto.

intros x y Hx Hy.
apply EA.
intro c.
split.
 intro Incx.
 apply Hy.
 apply Hx.
 auto.

 intro Incy.
 apply Hx.
 apply Hy.
 auto.
Qed.

Definition FunctionImageRistriction F A := 
UniqueOut _ (UniqueFunctionImageRistriction F A).

Theorem FunctionImageRistrictionTheorem : forall F A,
forall c , In c (FunctionImageRistriction F A) <->
(exists a, In a A /\ (F a) == c).
Proof.
intros F A.
apply (HUniqueOut _ (UniqueFunctionImageRistriction F A)).
Qed.


Theorem UniqueFunctionImageRistriction' : forall {A} (F : (#A) -> SET) S,
Unique (fun R => forall c, In c R <-> (exists a, In a S /\ In a A /\ forall prf : In a A, (F {a ! prf}) == c)).
Proof.
intros A F S.
put (Replacement'Axiom (fun a b => forall InaA : In a A, F {a ! InaA} == b) (SSet' A (fun a => In a S /\ forall b : #A, a == b -> F a == F b))) rep.
assert(RepHH : forall a, In a (SSet' A (fun a => In a S /\ forall b : #A, a == b -> F a == F b)) -> Unique (fun b => forall InaA : In a A, F {a ! InaA} == b)).
 intros a InaS.
 apply SSet'Theorem in InaS.
 destruct InaS as [InaA InaS].
 split.
  exists (F {a ! InaA}).
  intros prf.
  destruct (InaS prf) as [InaS' EqF].
  apply EqF.
  auto.
 intros x y HHx HHy.
 rewrite <- (HHx InaA).
 rewrite <- (HHy InaA).
 auto.
apply rep in RepHH.
clear rep.
destruct RepHH as [B RepHH].
split.
 exists B.
 intros b.
 split.
  intro InbB.
  apply RepHH in InbB.
  destruct InbB as [a [InaS EqF]].
  apply SSet'Theorem in InaS.
  destruct InaS as [InaA InaS].
  exists a.
  split.
   destruct (InaS InaA) as [InaS' EqF'].
   apply InaS'.
  split.
   destruct (InaS InaA) as [InaS' FH].
   auto.
  apply EqF.
 intros [a [InaS [InaA EqF]]].
 apply RepHH.
 exists a.
 split.
  apply SSet'Theorem.
  split.
   auto.
  intro prf.
  split.
   apply InaS.
  intros c Eqab.
  generalize (RFunRewrite F a); intro rew.
  assert (relH : exists y, forall prf : In a A, F {a ! prf} == y).
   exists b.
   apply EqF.
  generalize (rew relH); intro Rew.
  apply Rew.
  auto.
  apply Eqab.
 apply EqF.

intros x y Hx Hy.
apply EA.
intro c.
split.
 intro Incx.
 apply Hy.
 apply Hx.
 auto.

 intro Incy.
 apply Hx.
 apply Hy.
 auto.
Qed.

Definition FunctionImageRistriction' {A} (F : (#A) -> SET) S := 
UniqueOut _ (UniqueFunctionImageRistriction' F S).

Theorem FunctionImageRistriction'Theorem : forall {A} (F : (#A) -> SET) S,
forall c, In c (FunctionImageRistriction' F S ) <-> (exists a, In a S /\ In a A /\ forall prf : In a A, (F {a ! prf}) == c).
Proof.
intros A F S.
unfold FunctionImageRistriction'.
apply HUniqueOut.
Qed.

Definition FunctionImageRistriction'Dom {A} (F : (#A) -> SET) := FunctionImageRistriction' F A.

Theorem FunctionImageRistriction'DomTheorem : forall {A} (F : (#A) -> SET),
forall c, In c (FunctionImageRistriction'Dom F) <-> (exists a, In a A /\ forall prf : In a A, (F {a ! prf}) == c).
Proof.
intros A F c.
 unfold FunctionImageRistriction'Dom.
split.
 intro IncF.
 apply FunctionImageRistriction'Theorem in IncF.
 destruct IncF as [a [InaA [_ FH]]].
 exists a.
 split.
  auto.
 apply FH.

 intros [a [InaA FH]].
 apply FunctionImageRistriction'Theorem.
 exists a.
 split.
 auto.
 split.
 auto.
 apply FH.
Qed.

(*PowerAxiom*)
Definition IsPower A P :=
forall c , In c P <->
Subset c A.

Axiom PowerAxiom : forall A , exists P,
IsPower A P.

Theorem UniquePower : forall A ,
Unique (IsPower A).
Proof.
intro A.
split.
apply PowerAxiom.
intros x y Px Py.
apply EA.
intro c.
split; intro Inc.

 apply Py.
 apply Px.
 auto.

 apply Px.
 apply Py.
 auto.
Qed.

Definition PowerSet P :=
UniqueOut (IsPower P) (UniquePower P).

Theorem PowersetTheorem : forall A ,
forall c , In c (PowerSet A) <->
Subset c A.
Proof.
intro A.
apply (HUniqueOut (IsPower A)).
Qed.

Notation " x {<<SP sub }" := ({x ! ((proj2 (PowersetTheorem _ x)) sub)}) (at level 2).



Theorem PowersetHasEmpty : forall A , In Empty (PowerSet A).
Proof.
intro A.
apply PowersetTheorem.
apply AllSetHasEmpty.
Qed.

Theorem PowersetHasOwn : forall A , In A (PowerSet A).
Proof.
intro A.
apply PowersetTheorem.
apply ReflexivitySubset.
Qed.

(*union section*)
Definition Union A B := Unions (UnorderdPair A B).

Theorem UnionTheorem : forall A B,
forall c , In c (Union A B) <->
(In c A \/ In c B).
Proof.
intros A B c.
split.

 intro IncU.
 apply UnionsTheorem in IncU.
 destruct IncU as [a IncU].
 destruct IncU as [InU Inca].
 apply UnorderdPairTheorem in InU.
 destruct InU as [EqaA | EqaB].
  left.
  symmetry in EqaA.
  rewrite EqaA.
  auto.

  right.
  symmetry in EqaB.
  rewrite EqaB.
  auto.

 intro InD.
 apply UnionsTheorem.
 destruct InD as [IncA | IncB].

  exists A.
  split.
  apply UnorderdPairTheorem.
  auto.
  auto.

  exists B.
  split.
  apply UnorderdPairTheorem.
  auto.
  auto.
Qed.

Theorem UnionSubsetL : forall A B,
Subset A (Union A B).
Proof.
intros A B.
intros c IncA.
apply UnionTheorem.
tauto.
Qed.

Theorem UnionSubsetR : forall A B,
Subset B (Union A B).
Proof.
intros A B.
intros c IncB.
apply UnionTheorem.
tauto.
Qed.

Theorem UnionEmptyEqualityL : forall A,
Union Empty A == A.
Proof.
intro A.
apply EA.
intro c.
split; intro HH.
apply UnionTheorem in HH.
destruct HH as [IncE | IncA].
apply EmptyTheorem in IncE.
contradiction.
assumption.

apply UnionTheorem.
right.
assumption.
Qed.

Theorem UnionEmptyEqualityR : forall A,
Union A Empty == A.
Proof.
intro A.
apply EA.
intro c.
split; intro HH.
apply UnionTheorem in HH.
destruct HH as [IncA | IncE].
assumption.
apply EmptyTheorem in IncE.
contradiction.

apply UnionTheorem.
left.
assumption.
Qed.



Definition Sections A :=
SSet
(Unions A)
(fun v => forall c , In c A -> In v c).

Theorem SectionsTheorem : forall A , NonEmpty A ->
forall c , In c (Sections A) <->
(forall a , In a A -> In c a).
Proof.
intros A NEA c.
split.
 intros IncS a InaA.
 apply SSetTheorem in IncS.
 destruct IncS as [IncU SS].
 apply SS.
 auto.

 intro SS.
 apply SSetTheorem.
 split.
 apply UnionsTheorem.
 destruct NEA as [a NEA].
 exists a.
 split.
 auto.
 apply SS.
 auto.

 intros a InaA.
 apply SS.
 auto.
Qed.

Definition Section A B :=
Sections (UnorderdPair A B).

Theorem SectionTheorem : forall A B ,
forall c , In c (Section A B) <->
(In c A /\ In c B).
Proof.
intros A B c.
split.
 intro IncS.
 apply SSetTheorem in IncS.
 destruct IncS as [IncU SS].
 split; apply SS; apply UnorderdPairTheorem; auto.

 intro InD.
 destruct InD as [IncA IncB].
 apply SSetTheorem.
 split.

  apply UnionsTheorem.
  exists A.
  split.
  apply UnorderdPairTheorem.
  auto.
  auto.

  intros a InaU.
  apply UnorderdPairTheorem in InaU.
  destruct InaU as [E1 | E2].
  rewrite E1.
  auto.
  rewrite E2.
  auto.
Qed.

Theorem SectionTheoremS : forall A B,
forall S , (Subset S (Section A B)) <->
(Subset S A /\ Subset S B).
Proof.
intros.
split; intro HH.
 split; 
  intros c IncS;
  apply HH in IncS;
  apply SectionTheorem in IncS;
  tauto.

 intros c IncS.  
 destruct HH as [SA SB].
 apply SectionTheorem.
 split.
  apply SA; auto.
  apply SB; auto.
Qed.

Theorem SectionSubsetL : forall A B,
Subset (Section A B) A.
Proof.
intros A B.
intros c IncS.
apply SectionTheorem in IncS.
tauto.
Qed.

Theorem SectionSubsetR : forall A B,
Subset (Section A B) B.
Proof.
intros A B.
intros c IncS.
apply SectionTheorem in IncS.
tauto.
Qed.

Theorem SubsetInSectionL : forall A1 A2 B,
Subset A1 A2 -> Subset (Section A1 B) (Section A2 B).
Proof.
intros A1 A2 B sub.
intros c IncS.
apply SectionTheorem.
apply SectionTheorem in IncS.
split.
apply sub.
tauto.
tauto.
Qed.


Theorem SubsetInSectionR : forall A B1 B2,
Subset B1 B2 -> Subset (Section A B1) (Section A B2).
Proof.
intros A B1 B2.
intros sub c IncS.
apply SectionTheorem.
apply SectionTheorem in IncS.
split.
tauto.
apply sub.
tauto.
Qed.



Definition Diffset A B :=
SSet A (fun x => ~In x B).

Theorem DiffsetTheorem : forall A B x , 
In x (Diffset A B) <->
(In x A /\ ~In x B).
Proof.
intros A B x.
split.
 intro InxD.
 apply SSetTheorem in InxD.
 tauto.

 intro InD.
 apply SSetTheorem.
 tauto.
Qed.

Theorem DiffSubset : forall A B, Subset (Diffset A B) A.
Proof.
intros A B.
apply SSetSubset.
Qed.
Notation " x {<Diff}" := (x{<DiffSubset _ _}) (at level 1).


(*Set Induction*)

Definition Foundation :=
forall A, NonEmpty A ->
(exists x , In x A /\ (forall y , In y A -> ~In y x)).

Definition Foundation' := forall P : SET -> Prop,
(exists x, P x) ->
(exists x, P x /\ (forall y, P y -> ~In y x)).


Definition SetInduction := forall P : SET -> Prop ,
(forall A, (forall x , In x A -> P x) -> P A) ->
forall a , P a.


Theorem Foundation'_Foundation : Foundation' -> Foundation.
Proof.
intros found.
intros A NEA.
generalize (found (fun x => In x A) NEA); intro found'.
auto.
Qed.


(*
Theorem Foundation_Foundation' : Foundation -> Foundation'.
Proof.
intros found.
intros P ExP.
destruct ExP as [A ExP].
assert (NE : NonEmpty (SSet (PowerSet A) (fun x => P x))).
 exists A.
 apply SSetTheorem.
 split.
 apply PowersetTheorem.
 apply ReflexivitySubset.
 auto. 
apply found in NE.
destruct NE as [a NE].
destruct NE as [InaS NE].
apply SSetTheorem in InaS.
destruct InaS as [InaP Pa].
exists a.
split.
auto.
intros y Py.
apply NE.
apply SSetTheorem.
Admitted.
*)


Theorem Foundation_REM : Foundation -> REM.
Proof.
intro em.
intro P.
assert(NES : NonEmpty (SSet (PowerSet (PowerSet Empty)) (fun x => x == (Singleton Empty) \/ (x == Empty /\ P)))).
 exists (Singleton Empty).
 apply SSetTheorem.
 split.
  apply PowersetTheorem.
  intro c.
  intro IncS.
  apply SingletonTheorem in IncS.
  apply PowersetTheorem.
  rewrite IncS.
  apply ReflexivitySubset.

  auto.

generalize(em _ NES); intro em'.
clear em.
clear NES.
destruct em' as [x em].
destruct em as [em1 em2].
apply SSetTheorem in em1.
destruct em1 as [em11 em12].
destruct em12 as [EqxS | em12].
 rewrite EqxS in em2.
 right.
 intro PP.
 assert(em2E : In Empty (SSet (PowerSet (PowerSet Empty)) (fun x => x == Singleton Empty \/ x == Empty /\ P))).
 apply SSetTheorem.
 split.
 apply PowersetTheorem.
 intro c.
 intro IncS.
 apply EmptyTheorem in IncS.
 tauto.
 right.
 split;
  auto.
 apply em2 in em2E.
 apply em2E.
 apply SingletonTheorem.
 auto.

 left.
 tauto.
Qed.

(*
Theorem Foundation_SetInduction : Foundation -> SetInduction.
Proof.
intro found.
unfold Foundation in found.
unfold SetInduction.
intros P PInd.
apply dde.
intro NEPa.
apply (DeMorganNFE rem) in NEPa.
destruct NEPa as [x NPa].

fsdafdsafdsa
apply Foundation_Foundation' in found.
assert (dd : DD).
 apply REM_DD.
 auto.
intros P HH.
apply dd.
intro NF.
apply (DeMorganNFE rem) in NF.
destruct NF as [x NPx].
apply NPx.
apply HH.
intros c Incx.
assert (fH : exists x , ~P x).
 exists x.
 auto.
apply found in fH.
destruct fH as [a fH].
destruct fH as [NPa fH].
assert (T : forall y , In y a -> P y).
 intros y Inya.
 specialize fH with y.
 apply dd.
 intro NPy.
 apply fH in NPy.
 tauto.
apply (HH a) in T.
tauto.
Qed.
*)


Theorem SetInduction_Foundation : REM -> SetInduction -> Foundation.
Proof.
intros rem seti.
unfold SetInduction in seti.
assert(cont_seti : forall P : SET -> Prop, (exists a, ~P a) -> (exists A, (forall x, In x A -> P x) /\ ~P A)).
 intros P [a NPa].
 generalize (ContraPosition _ _ (seti P)); intro seti'.
 assert(seti'1 : ~(forall a, P a)).
  intro HH.
  apply NPa.
  apply HH.
 apply seti' in seti'1.
 apply (DeMorganNFE rem) in seti'1.
 destruct seti'1 as [x seti'1].
 exists x.
 apply (NArrowDest rem) in seti'1.
 apply seti'1.
clear seti.
assert(seti2 : forall A, NonEmpty A -> exists x, (IsEmpty (Section A x)) /\ In x A).
 assert(dde : DDE).
 now apply (REM_DDE rem).
 intros A [a InaA]. 
 set (fun a => ~In a A) as P.
 assert(LemH : exists a, ~P a).
  exists a.
  unfold P.
  auto.
 apply cont_seti in LemH.
 destruct LemH as [B [LemH NPB]].
 unfold P in LemH.
 unfold P in NPB. 
 exists B.
 split.
  intros s InsAB.
  apply SectionTheorem in InsAB.
  apply (LemH _ (proj2 InsAB)).
  apply (proj1 InsAB).
 apply dde in NPB.
 now auto.
intros A NEA.
destruct (seti2 _ NEA) as [x [HH1 HH2]].
exists x.
split.
now assumption.
intros y InyA Inyx.
apply (HH1 y).
apply SectionTheorem.
split; assumption.
Qed.

Axiom SetInductionAxiom : SetInduction.



Theorem NotIncludeOwn : forall x , ~In x x.
Proof.
intros x.
assert (MH : forall A , (forall x , In x A -> ~In x x) -> ~In A A).
 intros A HH InAA.
 generalize (HH _ InAA); intro NInAA.
 tauto.
apply (SetInductionAxiom _ MH).
Qed.

Theorem NotInclude2Set : forall x y,
In x y -> ~In y x.
Proof.
apply (SetInductionAxiom (fun x => forall y, In x y -> ~In y x)).
intros x ind_x y Inxy Inyx.
generalize (ind_x _ Inyx); intro ind_x'.
generalize (ind_x' _ Inyx); intro ind_x''.
apply ind_x''.
assumption.
Qed.

(*Pair*)

Definition Pair l r := UnorderdPair (Singleton l) (UnorderdPair l r).


Definition IsPair X := exists l , exists r , X == Pair l r.

Theorem EqualInPair : forall A B C D , 
(Pair A B)==(Pair C D) <-> (A == C /\ B == D).
Proof.
intros A B C D.
apply SymmetryEquiv.
split.
intro Eq2.
destruct Eq2 as [E1 E2].
rewrite E1.
rewrite E2.
auto.

intro EqP.

assert (EqAC : A == C).
 assert (PAP : In (Singleton A) (Pair A B)).
  apply UnorderdPairTheorem.
  auto.
 rewrite EqP in PAP.
 apply UnorderdPairTheorem in PAP.
 destruct PAP as [EqAC | EqACD].

  assert (InAS : In A (Singleton A)).
   apply SingletonTheorem.
   auto.
  rewrite EqAC in InAS.
  apply SingletonTheorem in InAS.
  auto.

  assert(InCU : In C (UnorderdPair C D)).
   apply UnorderdPairTheorem.
   auto.
  symmetry in EqACD.
  rewrite EqACD in InCU.
  apply SingletonTheorem in InCU.
  symmetry.
  auto.

split.
auto.
assert (InUP : In (UnorderdPair A B) (Pair A B)).
 apply UnorderdPairTheorem.
 auto.
rewrite EqP in InUP.
apply UnorderdPairTheorem in InUP.
assert (EqO : B==C \/ B==D).
 destruct InUP as [US | UU].

  assert(InBU : In B (UnorderdPair A B)).
   apply UnorderdPairTheorem.
   auto.
  rewrite US in InBU.
  apply SingletonTheorem in InBU.
  auto.

 assert (InBU : In B (UnorderdPair A B)).
   apply UnorderdPairTheorem.
   auto.
  rewrite UU in InBU.
  apply UnorderdPairTheorem in InBU.
  auto.

destruct EqO as [EqBC | EqBD].
assert (EqPSS : (Pair A B) == (Singleton (Singleton C))).
 apply EA.
 intro c.
 split.
  intro IncP.
  apply SingletonTheorem.
  apply UnorderdPairTheorem in IncP.
  destruct IncP as [EqS | EqU].
   rewrite EqS.
   rewrite EqAC.
   auto.

   rewrite EqU.
   rewrite EqAC.
   rewrite EqBC.
   auto.

  intro IncSS.
  apply SingletonTheorem in IncSS.
  rewrite IncSS.
  apply UnorderdPairTheorem.
  left.
  rewrite EqAC.
  auto.

rewrite EqPSS in EqP.
assert(EqCCD : (Singleton C) == (UnorderdPair C D)).
 assert (InUPCD : In (UnorderdPair C D) (Pair C D)).
  apply UnorderdPairTheorem.
  auto.
 symmetry in EqP.
 rewrite EqP in InUPCD.
 apply SingletonTheorem in InUPCD.
 auto.

assert (InDU : In D (UnorderdPair C D)).
 apply UnorderdPairTheorem.
 auto.
symmetry in EqCCD.
rewrite EqCCD in InDU.
apply SingletonTheorem in InDU.
apply (TransitivityEq C).
auto.
apply (SymmetryEq).
auto.

auto.
Qed.

Theorem EqualInPairL : forall A1 A2 B , 
A1 == A2 -> (Pair A1 B)==(Pair A2 B).
Proof.
intros A1 A2 B Eq.
rewrite Eq.
apply ReflexivityEq.
Qed.

Theorem EqualInPairR : forall A B1 B2 , 
B1 == B2 -> (Pair A B1)==(Pair A B2).
Proof.
intros A B1 B2 Eq.
rewrite Eq.
apply ReflexivityEq.
Qed.

Definition Cartesian A B := SSet
 (PowerSet (PowerSet (Union A B)))
 (fun v => exists l , exists r , In l A /\ In r B /\ v == (Pair l r)).

Theorem CartesianTheorem : forall a b A B ,
In (Pair a b) (Cartesian A B) <-> (In a A /\ In b B).
Proof.
intros a b A B.
split.

 intro InPC.
 apply SSetTheorem in InPC.
 destruct InPC as [InPP PP].
 destruct PP as [l PP].
 destruct PP as [r PP].
 destruct PP as [InlA PP].
 destruct PP as [InrB PP].
 apply EqualInPair in PP.
 destruct PP as [Eqal Eqbr].
 rewrite Eqal.
 rewrite Eqbr.
 tauto.

 intro InD.
 destruct InD as [InaA InbB].
 apply SSetTheorem.
 split.
  apply PowersetTheorem.
  intro c.
  intro IncP.
  apply PowersetTheorem.
  intro d.
  intro Indc.
  apply UnorderdPairTheorem in IncP.
  destruct IncP as [Eqca | EqcU].
   rewrite Eqca in Indc.
   apply SingletonTheorem in Indc.
   rewrite Indc.
   apply UnionTheorem.
   auto.

   rewrite EqcU in Indc.
   apply UnorderdPairTheorem in Indc.
   destruct Indc as [Eqda | Eqdb].
   rewrite Eqda.
   apply UnionTheorem.
   auto.
   rewrite Eqdb.
   apply UnionTheorem.
   auto.

 exists a.
 exists b.
 split.
 auto.
 split.
 auto.
 auto.
Qed.

Theorem PairInCartesian : forall {A B} (a : #A) (b : #B),
In (Pair a b) (Cartesian A B).
Proof.
intros A B a b.
generalize (SetProp a); intro InaA.
generalize (SetProp b); intro InbB.
apply CartesianTheorem.
split; assumption.
Qed.


Definition Pair' {A B} (a : #A) (b : #B) := {(Pair a b) ! (PairInCartesian a b)}.
Notation "[ a ; b ]" := (Pair' a b) (at level 7).

Theorem EqPairPair' : forall {A B} (a : #A) (b : #B),
(Pair' a b) == (Pair a b).
Proof.
intros A B a b.
apply ReflexivityEq.
Qed.


Theorem EqualInPair' : forall A B C D (a : (#A)) (b : (#B)) (c : (#C)) (d : (#D)),
(Pair' a b) == (Pair' c d) <-> a == c /\ b == d.
Proof.
intros A B C D a b c d.
split.
 intro EqP'.
 assert(EqP : (Pair a b) == (Pair c d)).
  apply (TransitivityEq (Pair' a b)).
  apply ReflexivityEq.
  apply (TransitivityEq (Pair' c d)).
  apply EqP'.
  apply ReflexivityEq.
 apply EqualInPair in EqP.
 assumption.

 intro EqD.
 apply (TransitivityEq (Pair a b)).
 apply ReflexivityEq.
 apply (TransitivityEq (Pair c d)).
 apply EqualInPair.
 apply EqD.
 apply ReflexivityEq.
Qed.

Theorem EqualInPairPair' : forall a b X Y (c : (#X)) (d : (#Y)),
(Pair a b)==(Pair' c d) <-> a == c /\ b == d.
Proof.
intros a b X Y c d.
split.
 intro EqP'.
 assert(EqP : (Pair a b) == (Pair c d)).
  apply (TransitivityEq (Pair' c d)).
  apply EqP'.
  apply ReflexivityEq.
 apply EqualInPair in EqP.
 apply EqP.

 intro EqD.
 apply (TransitivityEq (Pair c d)).
 apply EqualInPair.
 apply EqD.
 apply ReflexivityEq.
Qed.

Theorem EqualInPair'L : forall A B (a1 a2 : #A) (b : #B),
a1 == a2 -> [a1 ; b] == [a2; b].
Proof.
intros A B a1 a2 b Eq.
apply EqualInPair'.
split.
apply Eq.
apply ReflexivityEq.
Qed.

Theorem EqualInPair'R : forall A B (a : #A) (b1 b2 : #B),
b1 == b2 -> [a ; b1] == [a; b2].
Proof.
intros A B a b1 b2 Eq.
apply EqualInPair'.
split.
apply ReflexivityEq.
apply Eq.
Qed.



Theorem CartesianIsPair : forall A B ,
forall x , In x (Cartesian A B) ->
IsPair x.
Proof.
intros A B x InxC.
apply SSetTheorem in InxC.
destruct InxC as [InP InxC].
destruct InxC as [l InxC].
destruct InxC as [r InxC].
exists l.
exists r.
tauto.
Qed.

Theorem CartesianIsPair' : forall A B ,
forall x , In x (Cartesian A B) ->
exists a : #A, exists b : #B,
x == [a;b].
Proof.
intros A B x InxC.
assert(IsPx : IsPair x).
 apply (CartesianIsPair _ _ _ InxC).
destruct IsPx as [a IsPx].
destruct IsPx as [b IsPx].
assert(InD : In a A /\ In b B).
 apply CartesianTheorem.
 rewrite <- IsPx.
 apply InxC.
destruct InD as [InaA InbB].
exists {a!InaA}.
exists {b!InbB}.
rewrite IsPx.
apply EqualInPairPair'.
split; apply ReflexivityEq.
Qed.


Theorem PairInCartesian' : forall {A B} (a : #A) (b : #B),
In [a;b] (Cartesian A B).
Proof.
intros A B a b.
rewrite (EqPairPair' _ _).
apply PairInCartesian.
Qed.

Theorem CartesianTheorem' : forall {A B} (a : #A) (b : #B) X Y,
In [a;b] (Cartesian X Y) <-> (In a X /\ In b Y).
Proof.
intros A B a b X Y.
rewrite (EqPairPair' _ _).
apply CartesianTheorem.
Qed.



Theorem InPCartesian : forall a b X Y, In (Pair a b) (Cartesian X Y) ->
In a X /\ In b Y.
Proof.
intros a b X Y InPC.
apply CartesianTheorem in InPC.
assumption.
Qed.



Theorem SubsetInCartesianL : forall A1 A2 B, Subset A1 A2 ->
Subset (Cartesian A1 B) (Cartesian A2 B).
Proof.
intros A1 A2 B Sub p InpC.
assert (IsPp : IsPair p).
 apply (CartesianIsPair _ _ _ InpC).
destruct IsPp as [l IsPp].
destruct IsPp as [r IsPp].
rewrite IsPp in InpC.
rewrite IsPp.
apply CartesianTheorem in InpC.
apply CartesianTheorem.
split.
apply Sub.
tauto.
tauto.
Qed.

Theorem SubsetInCartesianR : forall A B1 B2, Subset B1 B2 ->
Subset (Cartesian A B1) (Cartesian A B2).
Proof.
intros A B1 B2 Sub p InpC.
assert (IsPp : IsPair p).
 apply (CartesianIsPair _ _ _ InpC).
destruct IsPp as [l IsPp].
destruct IsPp as [r IsPp].
rewrite IsPp in InpC.
rewrite IsPp.
apply CartesianTheorem in InpC.
apply CartesianTheorem.
split.
tauto.
apply Sub.
tauto.
Qed.

Theorem SubsetInCartesian : forall A1 A2 B1 B2, Subset A1 A2 -> Subset B1 B2 ->
Subset (Cartesian A1 B1) (Cartesian A2 B2).
Proof.
intros A1 A2 B1 B2 sub1 sub2.
apply (TransitivitySubset (Cartesian A1 B2)).
apply SubsetInCartesianR.
assumption.
apply SubsetInCartesianL.
assumption.
Qed.

Theorem CartesianInjection : forall A1 A2 B1 B2, NonEmpty A1 -> NonEmpty A2 -> NonEmpty B1 -> NonEmpty B2 -> (Cartesian A1 B1) == (Cartesian A2 B2) -> (A1 == A2 /\ B1 == B2).
Proof.
intros A1 A2 B1 B2 NA1 NA2 NB1 NB2 EqC.
destruct NA1 as [a1 NA1].
destruct NA2 as [a2 NA2].
destruct NB1 as [b1 NB1].
destruct NB2 as [b2 NB2].
split.
apply EA.
 intros a.
 split.
  intro InA1.
  assert(InP : In (Pair a b1) (Cartesian A2 B2)).
   rewrite <- EqC.
   apply CartesianTheorem.
   split; assumption.
  apply CartesianTheorem in InP.
  destruct InP as [InaA2].
  apply InaA2.

  intro InA2.
  assert(InP : In (Pair a b2) (Cartesian A1 B1)).
   rewrite EqC.
   apply CartesianTheorem.
   split; assumption.
  apply CartesianTheorem in InP.
  destruct InP as [InaA1].
  apply InaA1.

apply EA.
 intros b.
 split.
  intro InB1.
  assert(InP : In (Pair a1 b) (Cartesian A2 B2)).
   rewrite <- EqC.
   apply CartesianTheorem.
   split; assumption.
  apply CartesianTheorem in InP.
  destruct InP.
  assumption.

  intro InB2.
  assert(InP : In (Pair a2 b) (Cartesian A1 B1)).
   rewrite EqC.
   apply CartesianTheorem.
   split; assumption.
  apply CartesianTheorem in InP.
  destruct InP.
  assumption.
Qed.


Theorem PairLSet : forall PS, (forall p, In p PS -> IsPair p) ->
exists L, forall l, In l L <-> (exists p, In p PS /\ exists r, p == (Pair l r)).
Proof.
intros PS PairH.
generalize (Replacement'Axiom (fun p l => (exists r, p == (Pair l r)))); intro repH.
assert (repInd : forall p, In p PS -> Unique (fun l => exists r, p == (Pair l r))).
 intros p InpPS.
 split.
  apply PairH in InpPS.
  auto.

  intros l1 l2 H1 H2.
  destruct H1 as [r1 H1].
  destruct H2 as [r2 H2].
  assert(EqP : (Pair l1 r1) == (Pair l2 r2)).
   transitivity p.
   rewrite H1.
   auto.
   auto.
  apply EqualInPair in EqP.
  tauto.
apply repH in repInd.
auto.
Qed.

Theorem PairRSet : forall PS, (forall p, In p PS -> IsPair p) ->
exists R, forall r, In r R <-> (exists p, In p PS /\ exists l, p == (Pair l r)).
Proof.
intros PS PairH.
generalize (Replacement'Axiom (fun p r => (exists l, p == (Pair l r)))); intro repH.
assert (repInd : forall p, In p PS -> Unique (fun r => exists l, p == (Pair l r))).
 intros p InpPS.
 split.
  apply PairH in InpPS.
  destruct InpPS as [l InpPS].
  destruct InpPS as [r InpPS].
  exists r.
  exists l.
  auto.

  intros r1 r2 H1 H2.
  destruct H1 as [l1 H1].
  destruct H2 as [l2 H2].
  assert(EqP : (Pair l1 r1) == (Pair l2 r2)).
   transitivity p.
   rewrite H1.
   auto.
   auto.
  apply EqualInPair in EqP.
  tauto.
apply repH in repInd.
auto.
Qed.

(* Map Set *)
Definition IsMapSet x := (forall p, In p x -> IsPair p) /\ (forall a b1 b2, In (Pair a b1) x -> In (Pair a b2) x -> b1 == b2).

Theorem MapSet_UniqueValue : forall x, IsMapSet x -> forall A, (forall a, In a A -> exists b, In (Pair a b) x) -> forall (a : #A), Unique (fun b => In (Pair a b) x).
Proof.
intros x [IsP Unq] A cond a.
split.
 apply cond.
 apply SetProp.

 apply Unq.
Qed.
 

Definition MapSetFunction (F : SET -> SET) A :=
FunctionImageRistriction (fun x => Pair x (F x)) A.

Theorem IsMapSet_MapSetFunction : forall F A, IsMapSet (MapSetFunction F A).
Proof.
intros F A.
unfold MapSetFunction.
split.
 intros p InpM.
 apply FunctionImageRistrictionTheorem in InpM.
 destruct InpM as [a [InaA Eqp]].
 rewrite <- Eqp.
 exists a.
 exists (F a).
 apply ReflexivityEq.

 intros a b1 b2 InpF1 InpF2.
 apply FunctionImageRistrictionTheorem in InpF1.
 destruct InpF1 as [a1 [InaA1 Eqp1]].
 apply EqualInPair in Eqp1.
 destruct Eqp1 as [Eqa1 Eqfb1].
 apply FunctionImageRistrictionTheorem in InpF2.
 destruct InpF2 as [a2 [InaA2 Eqp2]].
 apply EqualInPair in Eqp2.
 destruct Eqp2 as [Eqa2 Eqfb2].
 rewrite <- Eqfb2.
 rewrite <- Eqfb1.
 rewrite Eqa1.
 rewrite Eqa2.
 apply ReflexivityEq.
Qed.

Theorem MapSetFunction_UniqueValue : forall F A (a : #A), Unique (fun b => In (Pair a b) (MapSetFunction F A)).
Proof.
intros F A.
apply MapSet_UniqueValue.
 apply IsMapSet_MapSetFunction.
intros a InaA.
exists (F a).
unfold MapSetFunction.
apply FunctionImageRistrictionTheorem.
exists a.
split.
 apply InaA.
apply ReflexivityEq.
Qed.

Definition MapSetFunction' {A} (F : (#A) -> SET) S :=
FunctionImageRistriction' (fun a => Pair a (F a)) S.


Theorem IsMapSet_MapSetFunction' : forall {A} (F : (#A) -> SET) S, IsMapSet (MapSetFunction' F S).
Proof.
intros A F S.
unfold MapSetFunction'.
split.
 intros p InpM.
 apply FunctionImageRistriction'Theorem in InpM.
 destruct InpM as [a [InaS [InaA Eqp]]].
 rewrite <- (Eqp InaA).
 exists {a ! InaA}.
 exists (F {a ! InaA}).
 apply ReflexivityEq.

 intros a b1 b2 InpF1 InpF2.
 apply FunctionImageRistriction'Theorem in InpF1.
 destruct InpF1 as [a1 [InaS1 [InaA1 Eqp1]]].
 assert(EqFa1 : forall prf : In a1 A, F {a1 ! prf} == b1).
  intro prf.
  specialize Eqp1 with prf.
  apply EqualInPair in Eqp1.
  apply (proj2 Eqp1).
 assert(Eqa1 : a == a1).
  specialize Eqp1 with InaA1.
  apply EqualInPair in Eqp1.
  destruct Eqp1 as [Eqa _].
  rewrite <- Eqa.
  apply ReflexivityEq.
 clear Eqp1.
 apply FunctionImageRistriction'Theorem in InpF2.
 destruct InpF2 as [a2 [InaS2 [InaA2 Eqp2]]].
 assert(EqFa2 : forall prf : In a2 A, F {a2 ! prf} == b2).
  intro prf.
  specialize Eqp2 with prf.
  apply EqualInPair in Eqp2.
  apply (proj2 Eqp2).
 assert(Eqa2 : a == a2).
  specialize Eqp2 with InaA2.
  apply EqualInPair in Eqp2.
  destruct Eqp2 as [Eqa _].
  rewrite <- Eqa.
  apply ReflexivityEq.
 clear Eqp2.
 rewrite <- Eqa1 in EqFa1.
 rewrite <- Eqa2 in EqFa2.
 assert(InaA : In a A).
  rewrite Eqa1.
  apply InaA1.
 rewrite <- (EqFa1 InaA).
 rewrite <- (EqFa2 InaA).
 apply ReflexivityEq.
Qed.

(*
Theorem MapSetFunction'_UniqueValue : forall {A} (F : (#A) -> SET) S (a : #S), Unique (fun b => In (Pair a b) (MapSetFunction' F A)).
Proof.
intros A F S.
apply MapSet_UniqueValue.
 apply IsMapSet_MapSetFunction'.
intros a InaS.
exists (F {a ! InaS}).
unfold MapSetFunction.
apply FunctionImageRistrictionTheorem.
exists a.
split.
 apply InaA.
apply ReflexivityEq.
Qed.
*)




(* Infinity Axiom *)
Definition Next x := Union x (Singleton x).


Axiom InfinityAxiom : 
exists N , In Empty N /\ (forall x , In x N -> In (Next x) N).


(* Peano Axiom *)
Definition IsPeano N := 
In Empty N /\
(forall x , In x N -> In (Next x) N) /\
(forall S , Subset S N -> 
  (In Empty S /\ (forall x , In x S -> In (Next x) S)) -> S = N
).

Theorem ExistPeano : exists N , IsPeano N.
Proof.
destruct InfinityAxiom as [N inf].
destruct inf as [InEN P2].
exists (Sections (SSet (PowerSet N) (fun N => In Empty N /\ (forall x , In x N -> In (Next x) N)))).
assert (NES : NonEmpty (SSet (PowerSet N) (fun N => In Empty N /\ (forall x , In x N -> In (Next x) N)))).
 exists N.
 apply SSetTheorem.
 split.
 apply PowersetHasOwn.
 split; auto.

split.

apply (SectionsTheorem _ NES).
intros a InaS.
apply SSetTheorem in InaS.
tauto.

split.
intros x InxS.
apply (SectionsTheorem _ NES).
intros a InaS.
apply SSetTheorem in InaS.
destruct InaS as [InaP InaS].
destruct InaS as [InEa Pa].
apply Pa.
generalize ((proj1 (SectionsTheorem _ NES _)) InxS); intro InxS'.
apply InxS'.
apply SSetTheorem.
split.
auto.
split.
auto.
auto.

intros S SSS DH.
apply SubsetEq.
split.

auto.
intros c IncS.
generalize ((proj1 (SectionsTheorem _ NES _)) IncS); intro IncS'.
apply IncS'.
apply SSetTheorem.
split.
 apply PowersetTheorem.
 intros s InsS.
 apply SSS in InsS.
 generalize ((proj1 (SectionsTheorem _ NES _)) InsS); intro InsS'.
 apply InsS'.
 apply SSetTheorem.
 split.
 auto.
 apply PowersetHasOwn.
 auto.
auto.
Qed.

Theorem UniquePeano : Unique IsPeano.
Proof.
split.
apply ExistPeano.
intros X Y PX PY.
destruct PX as [EX PX].
destruct PX as [PX SX].
destruct PY as [EY PY].
destruct PY as [PY SY].
assert (SubX : Subset (Section X Y) X).
 intros c IncX.
 apply SectionTheorem in IncX.
 tauto.
assert (SubY : Subset (Section X Y) Y).
 intros c IncY.
 apply SectionTheorem in IncY.
 tauto.
assert (EP : In Empty (Section X Y) /\ (forall x , In x (Section X Y) -> In (Next x) (Section X Y))).
 split.
  apply SectionTheorem.
  split; tauto.

  intros x InxS.
  apply SectionTheorem in InxS.
  apply SectionTheorem.
  split.
  apply PX.
  tauto.
  apply PY.
  tauto.
generalize (SX _ SubX EP); intro SX'.
generalize (SY _ SubY EP); intro SY'.
transitivity (Section X Y).
auto.
auto.
Qed.

Definition NN := UniqueOut IsPeano UniquePeano.


Theorem NNPeano : IsPeano NN.
Proof.
apply (HUniqueOut IsPeano).
Qed.

Theorem PeanoAxiom1 : In Empty NN.
Proof.
destruct NNPeano as [P1 PP].
assumption.
Qed.

Theorem PeanoAxiom2 : forall n, In n NN -> In (Next n) NN.
Proof.
destruct NNPeano as [P1 PP].
destruct PP as [P2 PP].
apply P2.
Qed.

Theorem PeanoAxiom3 : ~exists n, (Next n) == Empty.
Proof.
intro Exs.
destruct Exs as [n Exs].
assert(InnE : In n Empty).
 rewrite <- Exs.
 apply UnionTheorem.
 right.
 apply SingletonTheorem.
 apply ReflexivityEq.
apply EmptyTheorem in InnE.
contradiction.
Qed.

Theorem PeanoAxiom4 : forall x y, (Next x) == (Next y) -> x == y.
Proof.
intros x y EqN.
apply EA.
intro a.
split; intro Ina.
 assert (InaN : In a (Next x)).
  apply UnionTheorem.
  left.
  assumption.
 rewrite EqN in InaN.
 apply UnionTheorem in InaN.
 destruct InaN as [Inay | Eqay].
 assumption.
 apply SingletonTheorem in Eqay.
 rewrite Eqay in Ina.
 assert (Inxy : In x y).
 assert(InxN : In x (Next x)).
  apply UnionTheorem.
  right.
  apply SingletonTheorem.
  apply ReflexivityEq.
 rewrite EqN in InxN.
 apply UnionTheorem in InxN.
 destruct InxN as [Inxy | Eqxy].
 assumption.
 apply SingletonTheorem in Eqxy.
 rewrite Eqxy.
 rewrite Eqxy in Ina.
 assumption.
 generalize (NotInclude2Set _ _ Inxy); intro cont'.
 contradiction.

 assert (InaN : In a (Next y)).
  apply UnionTheorem.
  left.
  assumption.
 rewrite <- EqN in InaN.
 apply UnionTheorem in InaN.
 destruct InaN as [Inax | Eqax].
 assumption.
 apply SingletonTheorem in Eqax.
 rewrite Eqax in Ina.
 assert (Inyx : In y x).
 assert(InyN : In y (Next y)).
  apply UnionTheorem.
  right.
  apply SingletonTheorem.
  apply ReflexivityEq.
 rewrite <- EqN in InyN.
 apply UnionTheorem in InyN.
 destruct InyN as [Inyx | Eqyx].
 assumption.
 apply SingletonTheorem in Eqyx.
 rewrite Eqyx.
 rewrite Eqyx in Ina.
 assumption.
 generalize (NotInclude2Set _ _ Inyx); intro cont'.
 contradiction.
Qed.

Theorem PeanoAxiom5 : forall S, Subset S NN -> (In Empty S /\ (forall n, In n S -> In (Next n) S)) -> S == NN.
Proof.
destruct NNPeano as [P1 PP].
destruct PP as [P2 PP].
apply PP.
Qed.

Theorem MathematicalInductionNN' : forall (P : SET -> Prop), (P Empty /\ (forall n, In n NN -> P n -> P (Next n))) -> forall n, In n NN -> P n.
Proof.
intros P HD n InnNN.
destruct HD as [P0 PN].
assert(EqS : (SSet NN (fun n => P n)) == NN).
 apply PeanoAxiom5.
 apply SSetSubset.
 split.
  apply SSetTheorem.
  split.
  apply PeanoAxiom1.
  assumption.

  intros nn Innn.
  apply SSetTheorem in Innn.
  destruct Innn as [Inn Pnn].
  apply SSetTheorem.
  split.
  apply PeanoAxiom2.
  assumption.
  apply PN.
  assumption.
  assumption.
rewrite <- EqS in InnNN.
apply SSetTheorem in InnNN.
destruct InnNN as [InnNN Pn].
assumption.
Qed.
