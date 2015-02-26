Axiom SET : Type.
Axiom In : SET -> SET -> Prop.

Ltac put H name :=
generalize H; intro name.



(* Sub Typeing *)

Definition Cls (P : SET -> Prop) := sig P.
Notation "## P" := (Cls P) (at level 100).
Definition Cls_to_SET {A} (p : Cls A) : SET := (proj1_sig p).
Coercion Cls_to_SET : Cls >-> SET.
Definition partial_SET A := Cls (fun v => In v A).
Notation "# A" := (partial_SET A) (at level 100).
Definition partialSET_to_SET {A} (p : partial_SET A) : SET := (Cls_to_SET p).
Coercion partialSET_to_SET : partial_SET >-> SET.

Theorem ClsProp : forall {P} (a : (##P)), P a.
intros P a.
compute.
generalize (proj2_sig a); intro HH.
apply HH.
Qed.

Theorem SetProp : forall {A} (a : (#A)), In a A.
Proof.
intros A a.
apply (@ClsProp (fun v => In v A)).
Qed.
Hint Immediate @SetProp.

(*DownCast*)
Definition DCast_Cls {P : SET -> Prop} x (prf : P x) : (##P) := exist P _ prf.
Notation "{ x !! prf }" := (DCast_Cls x prf) (at level 1).
Definition DCast_SET {A} x (prf : In x A) : (#A) := exist (fun x => In x A) x prf.
Notation "{ x ! prf }" := (DCast_SET x prf) (at level 1).




Definition ZFCEq (a : SET) (b : SET) := a = b.
Notation "a == b" := (ZFCEq a b) (at level 70).



Theorem ReflexivityEq : forall a , a == a.
Proof.
intros.
reflexivity.
Qed.
Hint Immediate ReflexivityEq.
Theorem SymmetryEq : forall a b, a == b -> b == a.
Proof.
intros a b ab.
rewrite ab.
auto.
Qed.
Hint Immediate SymmetryEq.
Theorem TransitivityEq : forall {a c} b, a == b -> b == c -> a == c.
Proof.
intros a c b ab bc.
transitivity b.
auto.
auto.
Qed.
Hint Immediate @TransitivityEq.

Theorem DSETEq : forall {A} x (prf : In x A), {x ! prf} == x.
Proof.
intros x A prf.
apply ReflexivityEq.
Qed.

Theorem DSETEq' : forall {A} x (prf : In x A), x == {x ! prf}.
Proof.
intros A x prf.
apply ReflexivityEq.
Qed.


Theorem PropRewrite : forall (P : SET -> Prop),
forall x y, x == y -> P x -> P y.
Proof.
intros P x y Eqxy Px.
rewrite Eqxy in Px.
assumption.
Qed.
Theorem PropRewrite' : forall (P : SET -> Prop),
forall x y, x == y -> P y -> P x.
Proof.
intros P x y Eqxy.
apply PropRewrite.
apply SymmetryEq.
assumption.
Qed.


Definition RPred {A} (P : (#A) -> Prop) :=
forall (x : (#A)) (y : (#A)),
x == y -> (P x <-> P y).
Definition RPred' {A} (P : (#A) -> Prop) :=
forall (x : (#A)) (y : (#A)),
x == y -> (P x -> P y).
Definition RFunS {A} (F : (#A) -> SET) := 
forall (x y : (#A)),
x == y -> F x == F y.
Definition RFun {A B} (F : (#A) -> (#B)) := 
forall (x y : (#A)),
x == y -> F x == F y.

Definition EquivPred (P1 P2 : SET -> Prop) := forall a, (P1 a <-> P2 a).
Definition EquivPred' {A} (P1 P2 : (#A) -> Prop) := forall a, (P1 a <-> P2 a).

Theorem RPredSimplify : forall {A} (P : (#A) -> Prop),
RPred P <-> RPred' P.
Proof.
intros A P.
split.
 intro RP.
 intros x y Eqxy Px.
 apply (RP _ _ Eqxy).
 assumption.

 intro RP'.
 intros x y Eqxy.
 split.
  intro Px.
  apply (RP' _ _ Eqxy).
  assumption.

  intro Py.
  apply SymmetryEq in Eqxy.
  apply (RP' _ _ Eqxy).
  assumption.
Qed.

 
Theorem RFunRewrite' : forall {P : SET -> Prop} (F : (##P) -> SET) x,
(exists y, forall prf : P x, F {x !! prf} == y) -> 
forall (a b : ##P), x == a -> x == b ->  F a == F b.
Proof.
intros P F x Cond a b Eqa Eqb.
destruct a as [a prfa].
destruct b as [b prfb].
destruct Cond as [y Cond].
assert(Eqxa : x = a).
 apply Eqa.
assert(Eqxb : x = b).
 apply Eqb.
apply (TransitivityEq y).
rewrite Eqxa in Cond.
apply Cond.
apply SymmetryEq.
rewrite Eqxb in Cond.
apply Cond.
Qed.

Theorem RFunRewrite : forall {A} (F : (#A) -> SET) x,
(exists y, forall prf : In x A, F {x ! prf} == y) -> 
forall (a b : #A), x == a -> x == b ->  F a == F b.
Proof.
intros A F x Cond a b Eqa Eqb.
destruct a as [a prfa].
destruct b as [b prfb].
destruct Cond as [y Cond].
assert(Eqxa : x = a).
 apply Eqa.
assert(Eqxb : x = b).
 apply Eqb.
apply (TransitivityEq y).
rewrite Eqxa in Cond.
apply Cond.
apply SymmetryEq.
rewrite Eqxb in Cond.
apply Cond.
Qed.

Theorem FunRewrite : forall (F : SET -> SET), forall x y,
x == y -> F x == F y.
Proof.
intros F x y Eqxy.
rewrite Eqxy.
apply ReflexivityEq.
Qed.

Theorem FunRewrite2 : forall (F : SET -> SET -> SET), forall a b x y,
a == b -> x == y -> F a x == F b y.
Proof.
intros F a b x y Eqab Eqxy.
rewrite Eqab.
rewrite Eqxy.
apply ReflexivityEq.
Qed.

Theorem ArrowRewrite : forall (P : SET -> Prop), forall x y,
x == y -> (P x -> P y).
Proof.
intros P x y Eqxy Px.
rewrite Eqxy in Px.
apply Px.
Qed.

Theorem Arrow2Rewrite : forall (P : SET -> SET -> Prop), forall a b x y,
a == b -> x == y -> (P a x -> P b y).
Proof.
intros P a b x y Eqab Eqxy Pax.
rewrite <- Eqab.
rewrite <- Eqxy.
apply Pax.
Qed.



Definition ProofEquiv := forall (P : Prop) (prf1 : P) (prf2 : P), prf1
= prf2.

Theorem ProofEquiv_RPred : ProofEquiv -> (forall A (P : (#A) -> Prop), RPred P).
Proof.
intros pe A P.
intros x y Eqxy.
destruct x as [xs px].
destruct y as [ys py].
assert(EqP : (exist (fun v => In v A) xs px) = (exist (fun v => In v A) ys py)).
 assert(EqxyS : xs = ys).
  auto.
 generalize px.
 rewrite EqxyS.
 intro py'.
 assert(Eqp : py' = py).
  apply (pe (In ys A)).
 rewrite Eqp.
 reflexivity.
rewrite EqP.
tauto.
Qed.


(* Unique *)
Definition Unique (P : SET -> Prop) :=
(exists x , P x) /\
(forall x y , P x -> P y -> x==y).
Axiom UniqueOut :
  forall (P : SET -> Prop) , Unique P -> SET.
Axiom HUniqueOut : 
  forall (P : SET -> Prop) (prf : Unique P),
  P (UniqueOut P prf).

Definition Unique' {A} (P : (#A) -> Prop) :=
(exists a, P a) /\ (forall x y, P x /\ P y -> x == y).
Definition Unique'OutProof : forall {A} (P : (#A) -> Prop),
Unique' P -> Unique (fun x => exists prf : In x A, P ({x ! prf})).
Proof.
intros A P unqp.
destruct unqp as [Exs Unq].
split.
 destruct Exs as [a Exs].
 destruct a as [sa pa].
 exists sa.
 exists pa.
 apply Exs.

 intros x y Hx Hy.
 destruct Hx as [px Hx].
 destruct Hy as [py Hy].
 assert(Eqxy : {x ! px} == {y ! py}).
  apply Unq.
  split; assumption.
 apply Eqxy.
Qed.
Definition Unique'OutSet {A} (P : (#A) -> Prop) (unq : Unique' P) :=
UniqueOut (fun x => exists prf : In x A, P {x ! prf}) (Unique'OutProof _ unq).
Theorem Unique'OutSetIn : forall {A} (P : (#A) -> Prop) (unq : Unique' P),
In (Unique'OutSet P unq) A.
Proof.
intros A P unq.
unfold Unique'OutSet.
assert (UH : (fun x => exists prf : In x A, P {x ! prf}) (UniqueOut (fun x => exists prf : In x A, P {x ! prf}) (Unique'OutProof P unq))).
 apply (HUniqueOut (fun x => exists prf : In x A, P {x ! prf})).
simpl in UH.
destruct UH as [InA UH].
assumption.
Qed.
Definition Unique'Out {A} (P : (#A) -> Prop) (unq : Unique' P) :=
{(Unique'OutSet P unq) ! (Unique'OutSetIn P unq)}.
Theorem HUnique'Out : forall {A} (P : (#A) -> Prop) (unq : Unique' P),
RPred P -> P (Unique'Out P unq).
Proof.
intros A P unq rpp.
assert (UH : (fun x => exists prf : In x A, P {x ! prf}) (UniqueOut (fun x => exists prf : In x A, P {x ! prf}) (Unique'OutProof P unq))).
 apply (HUniqueOut (fun x => exists prf : In x A, P {x ! prf})).
simpl in UH.
destruct UH as [InUA PH].
assert(EqP : (Unique'Out P unq) == {(UniqueOut (fun x => exists prf : In x A, P {x ! prf}) (Unique'OutProof P unq)) ! InUA}).
 apply ReflexivityEq.
apply (rpp _ _ EqP).
assumption.
Qed.

Theorem UniqueOutEquiv : forall P (Unq : Unique P) x,
UniqueOut P Unq == x <-> P x.
Proof.
intros P Unq x.
split; intro HH.
 symmetry in HH.
 rewrite HH.
 apply (HUniqueOut P).

 destruct Unq as [Exs Unq].
 apply (Unq).
 apply (HUniqueOut P).
 auto.
Qed.

Theorem Unique'OutEquiv : forall {A} (P : (#A) -> Prop) (Unq : Unique' P) (x : (#A)),
RPred P -> (Unique'Out P Unq == x <-> P x).
Proof.
intros A P Unq x rpp.
split.
 intro UPEq.
 apply (rpp _ _ UPEq).
 apply (HUnique'Out _ _ rpp).

 intro Px.
 inversion Unq as [exs unq].
 apply unq.
 split.
 apply (HUnique'Out _ _ rpp).
 assumption.
Qed.

Theorem UniqueRewrite : forall P1 P2,
EquivPred P1 P2 -> 
(Unique P1 <-> Unique P2).
Proof.
intros P1 P2 cond. 
split.
 intro UP1.
 destruct UP1 as [Exs Unq].
 destruct Exs as [a Exs].
 split.
  exists a.
  apply cond.
  assumption.
 intros a1 a2 H1 H2.
 apply Unq.
  apply cond.
  assumption.
 apply cond.
 assumption.

 intro UP2.
 destruct UP2 as [Exs Unq].
 destruct Exs as [a Exs].
 split.
  exists a.
  apply cond.
  assumption.
 intros a1 a2 H1 H2.
 apply Unq.
  apply cond.
  assumption.
 apply cond.
 assumption.
Qed.

Theorem Unique'Rewrite : forall {A} (P1 : (#A) -> Prop) (P2 : (#A) -> Prop),
EquivPred' P1 P2 -> 
(Unique' P1 <-> Unique' P2).
Proof.
intros A P1 P2 cond. 
split.
 intro UP1.
 destruct UP1 as [Exs Unq].
 destruct Exs as [a Exs].
 split.
  exists a.
  apply cond.
  assumption.
 intros a1 a2 HD.
 destruct HD as [H1 H2].
 apply Unq.
 split.
  apply cond.
  assumption.
 apply cond.
 assumption.

 intro UP2.
 destruct UP2 as [Exs Unq].
 destruct Exs as [a Exs].
 split.
  exists a.
  apply cond.
  assumption.
 intros a1 a2 HD.
 destruct HD as [H1 H2].
 apply Unq.
 split.
  apply cond.
  assumption.
 apply cond.
 assumption.
Qed.


Definition Atmost (P : SET -> Prop) :=
(forall x y , P x -> P y -> x==y).

Definition Atmost' {A} (P : (#A) -> Prop) :=
(forall x y , P x -> P y -> x==y).


Theorem AtmostEqApply :
forall (P : SET -> Prop) (prf : Atmost P) x y ,
P x /\ P y -> x==y.
Proof.
intros P prf x y DP.
apply prf; tauto.
Qed.

Theorem Atmost'EqApply : 
forall {A} (P : (#A) -> Prop) (prf : Atmost' P) x y,
P x /\ P y -> x == y.
Proof.
intros A P prf x y PD.
destruct PD as [Px Py].
apply prf.
auto.
auto.
Qed.



Theorem Unique_Atmost : forall P , 
Unique P -> Atmost P.
Proof.
intros P UnqP.
destruct UnqP as [Exs Unq].
intros x y Px Py.
apply Unq; auto.
Qed.

Theorem Unique'_Atmost' : forall {A} (P : (#A) -> Prop),
Unique' P -> Atmost' P.
Proof.
intros A P Unq.
destruct Unq as [Exs Unq].
intros x y Px Py.
apply (Unq _ _).
split; assumption.
Qed.


Theorem UniqueEqApply :
forall (P : SET -> Prop) (prf : Unique P) x y ,
P x /\ P y -> x==y.
Proof.
intros P prf.
apply Unique_Atmost in prf.
apply AtmostEqApply.
auto.
Qed.

Theorem Unique'EqApply :
forall {A} (P : (#A) -> Prop) (prf : Unique' P) x y,
P x /\ P y -> x == y.
intros A P prf.
apply Unique'_Atmost' in prf.
apply Atmost'EqApply.
auto.
Qed.


Theorem Atmost_Unique : forall P : SET -> Prop,
Atmost P -> (exists x , P x) -> Unique P.
Proof.
intros P AP EP.
split; auto.
Qed.

Definition AtmostOut
(P : SET -> Prop) (atm : Atmost P) (exs : exists x , P x) :=
UniqueOut P (Atmost_Unique _ atm exs).

Theorem HAtmostOut : forall
(P : SET -> Prop) (atm : Atmost P) (exs : exists x , P x),
P (AtmostOut P atm exs).
Proof.
intros P atm exs.
apply (HUniqueOut P).
Qed.


(*Theorems*)
Theorem DeMorganANO : forall P Q : Prop ,
(~P /\ ~Q) -> ~(P \/ Q).
Proof.
intros P Q HH NH.
destruct HH as [NP NQ].
destruct NH as [PP | QQ]; tauto.
Qed.

Theorem DeMorganONA : forall P Q : Prop ,
(~P \/ ~Q) -> ~(P /\ Q).
Proof.
intros P Q HH NH.
destruct NH as [PP QQ].
destruct HH as [NP | NQ]; tauto.
Qed.

Theorem DeMorganNOA : forall P Q : Prop ,
~(P \/ Q) -> (~P /\ ~Q).
Proof.
intros P Q HH.
split; intro TT; apply HH; tauto.
Qed.

Theorem DoubleDeny : forall P : Prop, P -> ~~P.
Proof.
auto.
Qed.


Theorem DeMorganFNE : forall P : SET -> Prop,
(forall x , ~P x) -> ~(exists x , P x).
Proof.
intros P NP NN.
destruct NN as [x NN].
apply (NP x).
auto.
Qed.

Theorem DeMorganENF : forall P : SET -> Prop,
(exists x , ~P x) -> ~(forall x , P x).
Proof.
intros P NP NN.
destruct NP as [x NP].
apply NP.
auto.
Qed.

Theorem DeMorganNEF : forall P : SET -> Prop,
~(exists x , P x) -> (forall x , ~P x).
Proof.
intros P NE x NN.
apply NE.
exists x.
auto.
Qed.


Theorem ChangeInForall : forall P Q : SET -> Prop,
(forall x , P x -> Q x) ->
(forall x , P x) -> (forall x , Q x).
Proof.
intros P Q HH F1 x.
apply HH.
auto.
Qed.

Theorem ChangeInExists : forall P Q : SET -> Prop,
(forall x , P x -> Q x) ->
(exists x , P x) -> (exists x , Q x).
Proof.
intros P Q HH F1.
destruct F1 as [x F1].
exists x.
apply HH.
auto.
Qed.


Theorem ReflexivityArrow : forall P Q : Prop,
P -> P.
Proof.
tauto.
Qed.

Theorem TransitivityArrow : forall P Q R : Prop,
(P -> Q) -> (Q -> R) -> (P -> R).
Proof.
tauto.
Qed.

Theorem ReflexivityEquiv : forall P : Prop,
P <-> P.
Proof.
tauto.
Qed.

Theorem SymmetryEquiv : forall P Q : Prop ,
(P <-> Q) -> (Q <-> P).
Proof.
intros P Q PQ.
tauto.
Qed.

Theorem TransitivityEquiv : forall {P R : Prop} (Q : Prop),
(P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
tauto.
Qed.

(*
Theorem DistributeEquivAndL : forall A B C : Prop,
(A /\ (B <-> C)) <-> ((A /\ B) <-> (A /\ C)).
Proof.
intros A B C.
split.
 intro HH.
 destruct HH as [a bc].
 split.
  intro ab.
  destruct ab as [a' b].
  split.
  assumption.
  apply bc.
  assumption.

  intro ac.
  destruct ac as [a' c].
  
 split.
 split.
  intro a.
  cut (B /\ C).
  tauto.
  apply HH.
  auto.

  intro b.
  apply HH.
  
  assum
(A /\ B <-> C /\ D) <-> ((A <-> C) /\ (B <-> D)).
Proof.
intros A B C D.
split.
 intro AndH.
 split.
 split.
  intro a.
  cut (C /\ D).
  tauto.
  apply AndH.
  
  cut D.
  apply AndH.

 destruct AndH as [H1 H2].
 
(P /\ Q <-> R) <-> (P -> 
*)


Theorem SymmetryAnd : forall P Q : Prop,
P /\ Q -> Q /\ P.
Proof.
intros P Q PQ.
split; tauto.
Qed.

Theorem LeftAnd : forall {R} L,
L /\ R -> R.
Proof.
tauto.
Qed.

Theorem RightAnd : forall {L} R,
L /\ R -> L.
Proof.
tauto.
Qed.

Theorem DoubleAnd : forall P,
P /\ P <-> P.
Proof.
tauto.
Qed.




Theorem SymmetryOr : forall P Q : Prop,
P \/ Q -> Q \/ P.
Proof.
intros P Q PQ.
destruct PQ; auto.
Qed.

Theorem LeftOr : forall {R : Prop} (L : Prop),
R -> R \/ L.
Proof.
tauto.
Qed.

Theorem RightOr : forall {L : Prop} (R : Prop),
L -> R \/ L.
Proof.
tauto.
Qed.


(*Classical Theorems*)
Definition REM := forall P : Prop , P \/ ~P.
Definition DDE := forall P : Prop , ~~P -> P.


(*Definition ContraPosition := forall P Q : Prop, (P -> Q) -> (~Q -> ~P).*)

Theorem ContraPosition : forall P Q : Prop, (P -> Q) -> (~Q -> ~P).
Proof.
intros P Q HH NQH NP.
apply NQH.
apply HH.
auto.
Qed.


Theorem DDE_REM : DDE -> REM.
Proof.
intros dd P.
apply (dd (P \/ ~P)).
intro NN.
apply DeMorganNOA in NN.
tauto.
Qed.

Theorem REM_DDE : REM -> DDE.
Proof.
intros em P NNP.
generalize (em P); intro em'.
destruct em' as [PP | NP].
auto.
elimtype False.
apply NNP.
auto.
Qed.

Theorem DeMorganNAO : REM -> forall P Q : Prop ,
~(P /\ Q) -> (~P \/ ~Q).
Proof.
intros rem P Q HH.
destruct (rem P) as [PH | NPH].
 right.
 intro QH.
 apply HH.
 split; auto.

 left.
 auto.
Qed.

Theorem DeMorganNFE : REM -> forall P : SET -> Prop,
~(forall x , P x) -> (exists x , ~P x).
Proof.
intros dd P NP.
apply REM_DDE in dd.
apply dd.
intro NN.
apply NP.
generalize (DeMorganNEF _ NN); intro NN'.
intro x.
apply dd.
auto.
Qed.

Theorem ArrowDestruct1 : REM ->
forall P Q : Prop, (P -> Q) -> (~P \/ Q).
Proof.
intros rem P Q Arr.
destruct (rem Q) as [QH | NQH].
 auto.

 left.
 intro PH.
 apply NQH.
 auto.
Qed.

Theorem ArrowDestruct2 :
forall P Q, (~P \/ Q) -> (P -> Q).
Proof.
intros P Q destarr HP.
destruct destarr as [NPH | QH].
tauto.
auto.
Qed.

Theorem ArrowDestructRem : 
(forall P Q : Prop, (P -> Q) -> (~P \/ Q)) -> REM.
Proof.
intros Arrd M.
assert(c : M -> M).
 auto.
destruct (Arrd _ _ c); auto.
Qed.

Theorem NArrowDest : REM -> forall P Q : Prop, ~(P -> Q) -> (P /\ ~Q).
Proof.
intros REM P Q NPQ.
apply (REM_DDE REM).
intro PNQ.
apply (DeMorganNAO REM) in PNQ.
apply NPQ.
intro PH.
destruct PNQ as [NPH | QH].
tauto.
apply (REM_DDE REM).
auto.
Qed.


(*
Theorem REMInForall : REM -> forall P : SET -> Prop ,
(forall x , ~~P x) -> (forall x , P x).
Proof.
intros dd P HH x.
apply dd.
auto.
Qed.


Theorem REMInExists : DDE -> forall P : SET -> Prop ,
(exists x , ~~P x) -> (exists x , P x).
Proof.
intros dd P HH.
destruct HH as [x HH].
exists x.
apply dd.
auto.
Qed.
*)


