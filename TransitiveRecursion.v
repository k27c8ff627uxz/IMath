
Require Import logic.
Require Import IZF.
Require Import Relation.
Require Import BaseMap.
Require Import Maps.

(* TransitivitySet *)
Definition TransitivitySet A := forall x , In x A -> Subset x A.

Theorem UnionsTransitivitySet : forall A,
(forall x , In x A -> TransitivitySet x) -> TransitivitySet (Unions A).
Proof.
intros A TH.
intros c IncU.
apply UnionsTheorem in IncU.
destruct IncU as [a IncU].
destruct IncU as [InaA Inca].
assert (Ta : TransitivitySet a).
 apply TH.
 auto.
apply Ta in Inca.
apply (TransitivitySubset a).
auto.
intros x Inxa.
apply UnionsTheorem.
exists a.
split.
auto.
auto.
Qed.

Theorem TransitivitySetPowerIn : forall {A a}, In a A -> TransitivitySet A -> In a (PowerSet A).
Proof.
intros A a InaA TA.
apply PowersetTheorem.
apply TA.
assumption.
Qed.


(* Transfinite Recursion *)
Definition ConditionInTransitiveRecursiveMapUnique (F : SET -> SET) y g :=
  exists D, exists R, exists gMap : In g (Map D R), exists TTD : TransitivitySet D,
    In y D /\ (forall D', In y D' -> TransitivitySet D' -> Subset D D') /\
forall (u : #D), (%{g!gMap} u) == F (%(%MapImage {g!gMap}) {u ! TransitivitySetPowerIn (SetProp u) TTD}).

Theorem TransitiveRecursiveMapUnique : 
forall (F : SET -> SET) y, Unique (fun _g => ConditionInTransitiveRecursiveMapUnique F y _g).
Proof.
intros F.
apply (SetInductionAxiom (fun y => Unique (fun _g => ConditionInTransitiveRecursiveMapUnique F y _g))).
intros A IndH.
assert(Rep : exists MS, (forall u, In u A -> exists _g, In _g MS /\ ConditionInTransitiveRecursiveMapUnique F u _g) /\ (forall _g, In _g MS -> exists u, In u A /\ ConditionInTransitiveRecursiveMapUnique F u _g) /\ (forall _g, (exists u, In u A /\ ConditionInTransitiveRecursiveMapUnique F u _g) -> In _g MS)).
 generalize (Replacement'Axiom (fun x _g => ConditionInTransitiveRecursiveMapUnique F x _g) _ IndH); intro IndH'.
 destruct IndH' as [MS IndH'].
 exists MS.
 split.
  intros _g In_gMS.
  destruct (IndH _ In_gMS) as [Exs Unq].
  destruct Exs as [b Exs].
  exists b.
  split.
   apply IndH'.
   exists _g.
   split.
   auto.
   auto.
   auto.

  split.
  intros _g In_gMS.
  apply IndH' in In_gMS.
  destruct In_gMS as [u In_gMS].
  exists u.
  auto.

  intros _g HH.
  apply IndH'.
  auto.

destruct Rep as [MS Rep].
destruct Rep as [Rep1 Rep2].
destruct Rep2 as [Rep2 Rep3].
assert(MSisMapSet : forall _g, In _g MS -> exists D, exists R, In _g (Map D R)).
 intros _g IngMS.
 destruct (Rep2 _ IngMS) as [u RepH].
 destruct RepH as [InuA RepH].
 destruct RepH as [D RepH].
 destruct RepH as [R RepH].
 exists D.
 exists R.
 destruct RepH as [g RepH].
 auto.
assert (UMisMap : exists D, exists R, TransitivitySet D /\ In (Unions MS) (Map D R) /\ (forall r, In r R -> exists d, In d D /\ In (Pair d r) (Unions MS)) /\ Subset A D /\ (forall l, In l D <-> (exists p, In p (Unions MS) /\ (exists r, p = (Pair l r)))) /\ (forall D', Subset A D' -> TransitivitySet D' -> Subset D D')).
 assert(UMSisPairSet : forall p, In p (Unions MS) -> IsPair p).
  intros p InpMS.
  apply UnionsTheorem in InpMS.
  destruct InpMS as [_g InpMS].
  destruct InpMS as [IngMS Inpg]. 
  apply (MSisMapSet) in IngMS.
  destruct IngMS as [D IngMS].
  destruct IngMS as [R IngMS].
  apply Map_Rel in IngMS.
  apply (IsPairRelation {_g ! IngMS}).
  auto.
 assert(DomainLemma : exists ND, forall l, In l ND <-> (exists p, In p (Unions MS) /\ (exists r, p = (Pair l r)))).
  apply (PairLSet _ UMSisPairSet).
 assert(RangeLemma : exists NR, forall r, In r NR <-> (exists p, In p (Unions MS) /\ (exists l, p = (Pair l r)))).
  apply (PairRSet _ UMSisPairSet).
 destruct DomainLemma as [ND DomainLemma].
 destruct RangeLemma as [NR RangeLemma].
 exists ND.
 exists NR.
 assert (InuMR : In (Unions MS) (Relation ND NR)).
  apply PowersetTheorem.
  intros p InpU.
  generalize InpU; intro InpU'.
  apply UMSisPairSet in InpU.
  destruct InpU as [l InpU].
  destruct InpU as [r InpU].
  rewrite InpU.
  apply CartesianTheorem.
  split.
   apply DomainLemma.
   exists p.
   split.
   auto.
   exists r.
   auto.

   apply RangeLemma.
   exists p.
   split.
   auto.
   exists l.
   auto.

 assert (cond : Rel_MapCond {(Unions MS) ! InuMR}).
  intros x.
  split.
   generalize (SetProp x); intro In_dND.
   apply DomainLemma in In_dND.
   destruct In_dND as [p In_dND].
   destruct In_dND as [InpU In_dND].
   destruct In_dND as [_r In_dND].
   rewrite In_dND in InpU.
   assert (b : In _r NR).
    apply RangeLemma.
    exists (Pair x _r).
    split.
    auto.
    exists x.
    auto.
   exists {_r ! b}.
   auto.

   intros y1 y2 HD.
   destruct HD as [H1 H2].
   assert (InpU1 : In (Pair x y1) (Unions MS)); auto.
   assert (InpU2 : In (Pair x y2) (Unions MS)); auto.
   clear H1.
   clear H2.
   apply UnionsTheorem in InpU1.
   apply UnionsTheorem in InpU2.
   destruct InpU1 as [G1 InpU1].
   destruct InpU2 as [G2 InpU2].
   destruct InpU1 as [Ing1MS InpG1].
   destruct InpU2 as [Ing2MS InpG2].
 assert(MapSetUnionLemma : forall _g1 _g2, In _g1 MS -> In _g2 MS ->
 exists D1, exists D2, exists R1, exists R2,
 exists g1 : In _g1 (Map D1 R1), exists g2 : In _g2 (Map D2 R2), 
   forall x (x1 : In x D1) (x2 : In x D2), (%{_g1!g1} {x!x1}) == (%{_g2!g2} {x!x2} )).
   intros _g1 _g2 IngMS1 IngMS2.
   destruct (Rep2 _ IngMS1) as [u1 repH1].
   destruct (Rep2 _ IngMS2) as [u2 repH2].
   clear Rep2.
   clear MSisMapSet.
   destruct repH1 as [InuA1 repH1].
   destruct repH2 as [InuA2 repH2].
   destruct repH1 as [D1 repH1].
   destruct repH2 as [D2 repH2].
   destruct repH1 as [R1 repH1].
   destruct repH2 as [R2 repH2].
   destruct repH1 as [g1 repH1].
   destruct repH2 as [g2 repH2].
   exists D1.
   exists D2.
   exists R1.
   exists R2.
   exists g1.
   exists g2.
   destruct repH1 as [T1 repH1].
   destruct repH2 as [T2 repH2].
   destruct repH1 as [repH1 InuD1].
   destruct repH2 as [repH2 InuD2].
   apply (SetInductionAxiom (fun x => forall (x1 : In x D1) (x2 : In x D2), (%{_g1!g1} {x!x1} ) == (%{_g2!g2} {x!x2}))).
   intros xx SIH x1 x2.
   assert (RistEq : (%(%MapImage {_g1 ! g1}) {xx ! TransitivitySetPowerIn x1 T1}) == (%(%MapImage {_g2 ! g2}) {xx ! TransitivitySetPowerIn x2 T2})).
    apply EA.
    intro c; split; intro IncM; apply MapImageTheorem in IncM; apply MapImageTheorem; destruct IncM as [_a IncM]; destruct IncM as [In_axx' IncM]; destruct IncM as [In_aD Eqgc].
     assert(In_aD2 : In _a D2).
      apply T2 in x2.
      apply x2.
      apply In_axx'.
     exists {_a ! In_aD2}.
     split.
     apply In_axx'.
     assert (Inxxx : In _a xx).
      apply In_axx'.
     assert(In_aD1 : In _a D1).
      apply (SetProp _a).
     generalize (SIH _ Inxxx In_aD1 In_aD2); intro SIH'.
     apply SymmetryEq.
     apply (TransitivityEq (%{_g1!g1} {_a!In_aD1})).
     assert(Eqa : _a == {_a ! In_aD1}).
      apply ReflexivityEq.
     apply (MapArgEq {_g1 ! g1} Eqa).
     apply SIH'.

     assert(In_aD1 : In _a D1).
      apply T1 in x1.
      apply x1.
      apply In_axx'.
     exists {_a ! In_aD1}.
     split.
     apply In_axx'.
     assert(In_aD2 : In _a D2).
      generalize (x2); intro x2'.
      apply T2 in x2'.
      apply x2'.
      apply In_axx'.
     apply (TransitivityEq (%{_g2 ! g2} {_a ! In_aD2} )).
     apply SIH.
     apply In_axx'.
     assert(Eqa : {_a ! In_aD2} == _a).
      apply ReflexivityEq.
     apply (MapArgEq _ Eqa).

   apply (TransitivityEq (F ((%((%MapImage {_g1 ! g1})) {{xx ! x1} ! TransitivitySetPowerIn (SetProp {xx ! x1}) T1})))).
    apply InuD1.
   apply (TransitivityEq (F (%(%MapImage {_g1 ! g1}) {xx ! TransitivitySetPowerIn x1 T1}))).
    hyperreflexivity.
   apply (TransitivityEq (F (%(%MapImage {_g2 ! g2}) {xx ! TransitivitySetPowerIn x2 T2}))).
    apply FunRewrite.
    apply RistEq.
   apply (TransitivityEq (F ((%((%MapImage {_g2 ! g2})) {{xx ! x2} ! TransitivitySetPowerIn (SetProp {xx ! x2}) T2})))).
    hyperreflexivity.
   apply SymmetryEq.
   apply InuD2.
  generalize (MapSetUnionLemma _ _ Ing1MS Ing2MS); intro MapSetUnionLemma'.
  clear MapSetUnionLemma.
  rename MapSetUnionLemma' into MapSetUnionLemma.
  destruct MapSetUnionLemma as [D1 MapSetUnionLemma].
  destruct MapSetUnionLemma as [D2 MapSetUnionLemma].
  destruct MapSetUnionLemma as [R1 MapSetUnionLemma].
  destruct MapSetUnionLemma as [R2 MapSetUnionLemma].
  destruct MapSetUnionLemma as [g1 MapSetUnionLemma].
  destruct MapSetUnionLemma as [g2 MapSetUnionLemma].
  assert (InxD1 : In x D1 /\ In y1 R1).
   assert(InGM : In G1 (Map D1 R1)); auto.
   apply Map_Rel in InGM.
   apply PowersetTheorem in InGM.
   apply InGM in InpG1.
   apply CartesianTheorem in InpG1.
   tauto.
  assert (InxD2 : In x D2 /\ In y2 R2).
   assert(InGM : In G2 (Map D2 R2)); auto.
   apply Map_Rel in InGM.
   apply PowersetTheorem in InGM.
   apply InGM in InpG2.
   apply CartesianTheorem in InpG2.
   tauto.
  destruct InxD1 as [InxD1 InyR1].
  destruct InxD2 as [InxD2 InyR2].
  specialize MapSetUnionLemma with x InxD1 InxD2.
  assert (G1y : (%{G1 ! g1} {x!InxD1}) == {y1 ! InyR1}).
   apply AppTheoremReverse.
   auto.
  assert (F2y : (%{G2 ! g2} {x!InxD2}) == {y2 ! InyR2}).
   apply AppTheoremReverse.
   auto.
  transitivity ({y1 ! InyR1}).
  auto.
  transitivity (%{G1 ! g1} {x ! InxD1}).
  auto.
  transitivity (%{G2 ! g2} {x ! InxD2}).
  auto.
  transitivity ({y2 ! InyR2}).
  auto.
  auto.

 assert (DomainSet : exists DSet, forall D , In D DSet <-> (exists g, In g MS /\ exists R, In g (Map D R))).
  assert (DSL : forall g, In g MS -> Unique(fun D => exists R, In g (Map D R))).
   intros g IngMS.
   destruct (Rep2 _ IngMS) as [u Rep2'].
   destruct Rep2' as [InuA Rep2'].
   destruct Rep2' as [D Rep2'].
   destruct Rep2' as [R Rep2'].
   destruct Rep2' as [gf Rep2'].
   split.
    exists D.
    exists R.
    auto.

    intros D1 D2 H1 H2.
    destruct H1 as [R1 H1].
    destruct H2 as [R2 H2].
    apply (MapHasSameDomain {g ! H1} {g ! H2}).
    apply ReflexivityEq.
    generalize (Replacement'Axiom _ _ DSL); intro rep.
    destruct rep as [DSet rep].
    exists DSet.
    intros D.
    auto.
   destruct DomainSet as [DSet DomainSet].
   assert(UDEqD : ND = (Unions DSet)).
    apply EA.
    intro d.
    split.
     intro IndND.
     apply UnionsTheorem.
     apply DomainLemma in IndND.
     destruct IndND as [p IndND].
     destruct IndND as [InpU IndND].
     apply UnionsTheorem in InpU.
     destruct InpU as [g InpU].
     destruct InpU as [IngMS Inpg].
     destruct (Rep2 _ IngMS) as [u Rep2'].
     destruct Rep2' as [InuA Rep2'].
     destruct Rep2' as [D Rep2'].
     destruct Rep2' as [R Rep2'].
     destruct Rep2' as [gf Rep2'].
     exists D.
     split.
     apply DomainSet.
     exists g.
     split.
     auto.
     exists R.
     auto.

     destruct IndND as [r IndND].
     assert (IngR : In g (Relation D R)).
      apply Map_Rel.
      auto.
     rewrite IndND in Inpg.
     apply (PairInRelation {g ! IngR}) in Inpg.
     tauto.

    intro IndU.
    apply UnionsTheorem in IndU.
    destruct IndU as [D IndU].
    destruct IndU as [InDDSet IndD].
    apply DomainLemma.
    assert (DLem : In D DSet); auto.
    apply DomainSet in DLem.
    destruct DLem as [g DLem].
    destruct DLem as [IngMS DLem].
    destruct DLem as [R DLem].
    exists (Pair d (%{g ! DLem} {d ! IndD})).
    split.
    apply UnionsTheorem.
    exists g.
    split.
    auto.
    assert (gApp : (&&{g ! DLem}{<Map_Rel}) {d ! IndD} (%{g ! DLem} {d ! IndD})).
     apply AppTheorem.
    auto.
    exists (%{g ! DLem} {d ! IndD}).
    auto.   

  split.
  rewrite UDEqD.
  apply (UnionsTransitivitySet).
  intros D InDDSet.
  apply DomainSet in InDDSet.
  destruct InDDSet as [_g InDDSet].
  destruct InDDSet as [In_gMS InDDSet].
  destruct InDDSet as [R g].
  generalize (Rep2 _ In_gMS); intro Rep2'.
  destruct Rep2' as [u Rep2'].
  destruct Rep2' as [InuA Rep2'].
  destruct Rep2' as [D' Rep2'].
  destruct Rep2' as [R' Rep2'].
  destruct Rep2' as [g' Rep2'].
  destruct Rep2' as [TD' Rep2'].
  assert (EqD : D = D').
   apply (MapHasSameDomain {_g ! g} {_g ! g'}).
   apply (ReflexivityEq).
  rewrite EqD.
  auto.


  split.
  apply ((proj1 (Rel_Map _)) cond).

  split.
  intros r InrNR.
  apply RangeLemma in InrNR.
  destruct InrNR as [p InrNR].
  destruct InrNR as [InpU EqP].
  destruct EqP as [l EqP].
  rewrite EqP in InpU.
  clear EqP.
  clear p.
  exists l.
  split.
  apply DomainLemma.
  exists (Pair l r).
  split.
  auto.
  exists r.
  auto.
  auto.

  split.
  intros c IncA.
  apply DomainLemma.
  destruct (Rep1 _ IncA) as [_g Rep1'].
  destruct Rep1' as [In_gMS Pg].
  destruct Pg as [PD Pg].
  destruct Pg as [PR Pg].
  destruct Pg as [PG Pg].
  destruct Pg as [TPD Pg].
  destruct Pg as [InaPD PgH].
  assert (Inpg : exists b, In (Pair c b) _g).
   assert(AppT : &&({_g ! PG}{<Map_Rel}) {c ! InaPD} (%{_g ! PG} {c ! InaPD})).
    apply AppTheorem.
   exists (%{_g ! PG} {c ! InaPD}).
   auto.
  destruct Inpg as [b Inpg].
  exists (Pair c b).
  split.
  apply UnionsTheorem.
  exists _g.
  split.
  auto.
  auto.
  exists b.
  auto.

  split.
  auto.

  intros D' SubAD' TD'.
  intros n InND.
  rewrite UDEqD in InND.
  apply UnionsTheorem in InND.
  destruct InND as [DD InND].
  destruct InND as [InDDDSet InDD].
  apply DomainSet in InDDDSet.
  destruct InDDDSet as [g InDDDSet].
  destruct InDDDSet as [IngMS InDDR].
  destruct InDDR as [RR IngM].
  destruct (Rep2 _ IngMS) as [u Rep2'].
  destruct Rep2' as [InuA Rep2'].
  destruct Rep2' as [DD' Rep2'].
  destruct Rep2' as [RR' Rep2'].
  destruct Rep2' as [IngM' Rep2'].
  destruct Rep2' as [TDD' Rep2'].
  destruct Rep2' as [InuDD' Rep2'].
  destruct Rep2' as [MST Rep2'].
  assert(InuD' : In u D').
   apply SubAD'.
   auto.
  apply (MST _ InuD' TD').
  assert(EqDD : DD = DD').
   apply (MapHasSameDomain {g ! IngM} {g ! IngM'}).
   apply ReflexivityEq.
  rewrite <- EqDD.
  auto.




destruct UMisMap as [OD UMisMap].
destruct UMisMap as [OR UMisMap].
destruct UMisMap as [TOD UMisMap].
destruct UMisMap as [UMisMap SurjUM].
destruct SurjUM as [SurjUM SubAOD].
destruct SubAOD as [SubAOD ODomainLemma].
destruct ODomainLemma as [ODomainLemma OTD].


assert(NMSIsMap : exists D, exists R, TransitivitySet D /\ In (Union (Unions MS) (Singleton (Pair A (F (%(%MapImage {Unions MS ! UMisMap}) (A{<<SP SubAOD})))))) (Map D R) /\ In A D /\ D = (Union OD (Singleton A))).
 assert(UMSisPairSet : forall p, In p (Union (Unions MS) (Singleton (Pair A (F (%(%MapImage {Unions MS ! UMisMap}) (A{<<SP SubAOD})))))) -> IsPair p).
  intros p InpMS.
  apply UnionTheorem in InpMS.
  destruct InpMS as [InpMS | InpMS].
   apply UnionsTheorem in InpMS.
   destruct InpMS as [_g InpMS].
   destruct InpMS as [IngMS Inpg]. 
   apply (MSisMapSet) in IngMS.
   destruct IngMS as [D IngMS].
   destruct IngMS as [R IngMS].
   apply Map_Rel in IngMS.
   apply (IsPairRelation {_g ! IngMS}).
   auto.

   apply SingletonTheorem in InpMS.
   rewrite InpMS.
   exists A.
   exists (F (%(%MapImage {Unions MS ! UMisMap}) (A{<<SP SubAOD}))).
   auto.

  assert(DomainLemma : exists ND, forall l, In l ND <-> (exists p, In p (Union (Unions MS) (Singleton (Pair A (F (%(%MapImage {Unions MS ! UMisMap}) (A{<<SP SubAOD})))))) /\ (exists r, p = (Pair l r)))).
  apply (PairLSet _ UMSisPairSet).
 assert(RangeLemma : exists NR, forall r, In r NR <-> (exists p, In p (Union (Unions MS) (Singleton (Pair A (F (%(%MapImage {Unions MS ! UMisMap}) (A{<<SP SubAOD})))))) /\ (exists l, p = (Pair l r)))).
  apply (PairRSet _ UMSisPairSet).
 destruct DomainLemma as [ND DomainLemma].
 destruct RangeLemma as [NR RangeLemma].
 exists ND.
 exists NR.
 assert (InuMR : In (Union (Unions MS) (Singleton (Pair A (F (%(%MapImage {Unions MS ! UMisMap}) (A{<<SP SubAOD})))))) (Relation ND NR)).
  apply PowersetTheorem.
  intros p InpU.
  generalize InpU; intro InpU'.
  apply UMSisPairSet in InpU.
  destruct InpU as [l InpU].
  destruct InpU as [r InpU].
  rewrite InpU.
  apply CartesianTheorem.
  split.
   apply DomainLemma.
   exists p.
   split.
   auto.
   exists r.
   auto.

   apply RangeLemma.
   exists p.
   split.
   auto.
   exists l.
   auto.
  assert(NDIs_ : ND = (Union OD (Singleton A))).
   apply EA.
   intros d.
   split.
    intro IndND.
    apply UnionTheorem.
    apply DomainLemma in IndND.
    destruct IndND as [p IndND].
    destruct IndND as [InpU IndND].
    destruct IndND as [r IndND].
    rewrite IndND in InpU.
    apply UnionTheorem in InpU.
    assert(InUMSR : In (Unions MS) (Relation OD OR)).
     apply Map_Rel.
     auto.
    destruct InpU as [InpU | InpU].
     apply (PairInRelation {Unions MS ! InUMSR}) in InpU.
     left.
     tauto.

     apply SingletonTheorem in InpU.
     apply EqualInPair in InpU.
     right.
     apply SingletonTheorem.
     tauto.
    
    intro IndU.
    apply UnionTheorem in IndU.
    apply DomainLemma.
    destruct IndU as [IndOD | EqdA].
     exists (Pair d (%{Unions MS ! UMisMap} {d ! IndOD})).
     split.
      apply UnionTheorem.
      left.
      assert(AppT : &&({Unions MS ! UMisMap}{<Map_Rel}) {d ! IndOD}  (%{Unions MS ! UMisMap} {d ! IndOD})).
       apply AppTheorem.
      auto.
     
      exists (%{Unions MS ! UMisMap} {d ! IndOD}).
      auto.

     exists (Pair A (F (%(%MapImage {Unions MS ! UMisMap}) (A{<<SP SubAOD})))).
     split.
      apply UnionTheorem.
      right.
      apply SingletonTheorem.
      auto.

      exists (F (%(%MapImage {Unions MS ! UMisMap}) (A{<<SP SubAOD}))).
      apply SingletonTheorem in EqdA.
      rewrite EqdA.
      auto.
  assert(NRIs_ : NR = (Union OR (Singleton (F (%(%MapImage {Unions MS ! UMisMap}) (A{<<SP SubAOD})))))).
   apply EA.
   intros c.
   split.
    intro IncNR.
    apply RangeLemma in IncNR.
    destruct IncNR as [p IncNR].
    destruct IncNR as [InpU IncNR].
    destruct IncNR as [l EqP].
    rewrite EqP in InpU.
    clear EqP.
    clear p.
    apply UnionTheorem in InpU.
    apply UnionTheorem.
    destruct InpU as [InpU | EqPS].
     assert (InR : In (Unions MS) (Relation OD OR)).
      apply Map_Rel.
      auto.
     apply (PairInRelation {Unions MS ! InR}) in InpU.
     left.
     tauto.

     apply SingletonTheorem in EqPS.
     apply EqualInPair in EqPS.
     destruct EqPS as [EqlA EqcF].
     right.
     rewrite EqcF.
     apply SingletonTheorem.
     auto.

    intro IncU.
    apply RangeLemma.
    apply UnionTheorem in IncU.
    destruct IncU as [IncOR | EqcF].
     destruct (SurjUM _ IncOR) as [d SJ].
     destruct SJ as [IndOD InPU].
     exists (Pair d c).
     split.
      apply UnionTheorem.
      left.
      auto.

      exists d.
      auto.

     apply SingletonTheorem in EqcF.
     exists (Pair A c).
     split.
      apply UnionTheorem.
      right.
      apply SingletonTheorem.
      rewrite EqcF.
      auto.

      exists A.
      auto.
  assert(UMSRel : In (Unions MS) (Relation OD OR)).
   apply Map_Rel.
   auto.
  assert(cond : Rel_MapCond {_ ! InuMR}).
   intros a.
   split.
    assert(InaND : In a ND); auto.
    rewrite NDIs_ in InaND.
    apply UnionTheorem in InaND.
    destruct InaND as [InaOD | EqaA].
     assert(b : In (%{Unions MS ! UMisMap} {a ! InaOD}) NR).
      rewrite NRIs_.
      apply UnionTheorem.
      left.
      auto.
     exists {_ ! b}.
     assert(InP : In (Pair a (%{Unions MS ! UMisMap} {a ! InaOD})) (Union (Unions MS) (Singleton (Pair A (F (%(%MapImage {Unions MS ! UMisMap}) (A{<<SP SubAOD}))))))).
      assert(InP : In (Pair a (%{Unions MS ! UMisMap} {a ! InaOD})) (Unions MS)).
       assert(AppT : (&&{Unions MS ! UMisMap}{<Map_Rel}) {a ! InaOD} (%{Unions MS ! UMisMap} {a ! InaOD})).
        apply AppTheorem.
       auto.
      apply UnionTheorem.
      left.
      auto.
     auto.

     apply SingletonTheorem in EqaA.
     assert (b : In (F (%(%MapImage {Unions MS ! UMisMap}) (A{<<SP SubAOD}))) NR).
      rewrite NRIs_.
      apply UnionTheorem.
      right.
      apply SingletonTheorem.
      auto.
     assert (InP : In (Pair a (F (%(%MapImage {Unions MS ! UMisMap}) (A{<<SP SubAOD})))) (Union (Unions MS) (Singleton (Pair A (F (%(%MapImage {Unions MS ! UMisMap}) (A{<<SP SubAOD}))))))).
      assert(InP : In (Pair a (F (%(%MapImage {Unions MS ! UMisMap}) (A{<<SP SubAOD})))) (Singleton (Pair A (F (%(%MapImage {Unions MS ! UMisMap}) (A{<<SP SubAOD})))))).
       apply SingletonTheorem.
       rewrite EqaA.
       auto.
      apply UnionTheorem.
      right.
      auto.
     exists {_ ! b}.
     apply InP.


   intros y1 y2 HD.
   destruct HD as [H1 H2].
   assert(InP1 : In (Pair a y1) (Union (Unions MS) (Singleton (Pair A (F (%(%MapImage {Unions MS ! UMisMap}) (A{<<SP SubAOD}))))))); auto.
   assert(InP2 : In (Pair a y2) (Union (Unions MS) (Singleton (Pair A (F (%(%MapImage {Unions MS ! UMisMap}) (A{<<SP SubAOD}))))))); auto.
   apply UnionTheorem in InP1.
   apply UnionTheorem in InP2.
   destruct InP1 as [InP1 | InP1]; destruct InP2 as [InP2 | InP2].
    assert(UMMapR : Rel_MapCond ({Unions MS ! UMisMap}{<Map_Rel})).
     apply Rel_Map.
     assumption.
    assert (InaOD : In a OD).
     apply (PairInRelation {Unions MS ! UMSRel}) in InP1.
     tauto.
    assert(Iny1OR : In y1 OR).
     apply (PairInRelation {Unions MS ! UMSRel}) in InP1.
     tauto.
    assert(Iny2OR : In y2 OR).
     apply (PairInRelation {Unions MS ! UMSRel}) in InP2.
     tauto.
    apply (SymmetryEq).
    apply (TransitivityEq {y2 ! Iny2OR}).
     apply ReflexivityEq.
    apply SymmetryEq.
    apply (TransitivityEq {y1 ! Iny1OR}).
     apply ReflexivityEq.
    apply (Unique'EqApply _ (UMMapR {a!InaOD})).
    split.
    generalize (PairInRelation {_ ! UMSRel} _ _ InP1); intro InP1'.
    destruct InP1' as [InaOD' InyOR].
    auto.
    generalize (PairInRelation {_ ! UMSRel} _ _ InP2); intro InP2'.
    destruct InP2' as [InaOD' InyOR].
    auto.

    apply SingletonTheorem in InP2.
    apply EqualInPair in InP2.
    destruct InP2 as [EqaA EqyF].
    apply UnionsTheorem in InP1.
    destruct InP1 as [f InP1].
    destruct InP1 as [InfMS InPf].
    destruct (Rep2 _ InfMS) as [u Rep2'].
    destruct Rep2' as [InuA Rep2'].
    destruct Rep2' as [D Rep2'].
    destruct Rep2' as [R Rep2'].
    destruct Rep2' as [fM Rep2'].
    destruct Rep2' as [TD Rep2'].
    destruct Rep2' as [InuD Rep2'].
    destruct Rep2' as [MST fH'].
    assert(InaD : In a D /\ In y1 R).
     assert(InfRel : In f (Relation D R)).
      apply Map_Rel.
      auto.
     apply (PairInRelation {f ! InfRel}) in InPf.
     auto.
    destruct InaD as [InaD InyR1].
    apply (TransitivityEq {y1 ! InyR1}).
    auto.
    apply (TransitivityEq (%{f ! fM} {a ! InaD})).
    apply (SymmetryEq).
    apply AppTheoremReverse.
    auto.
    apply (TransitivityEq (F (%(%MapImage {f ! fM}) {a ! (TransitivitySetPowerIn (SetProp {a ! InaD}) TD)}))).
    apply fH'.
    apply (TransitivityEq (F (%(%MapImage {Unions MS ! UMisMap}) (A{<<SP SubAOD})))).
     apply FunRewrite.
     apply EA.
     intro c.
     split; intro IncM; apply MapImageTheorem; apply MapImageTheorem in IncM.
      destruct IncM as [x IncM].
      destruct IncM as [Inxa' IncM].
      assert(InxOD : In x OD).
       assert (InaOD : In a OD).
        assert (InPUMS : In (Pair a y1) (Unions MS)).
         apply UnionsTheorem.
         exists f.
         split; auto.
        assert(URel : In (Unions MS) (Relation OD OR)).
         apply Map_Rel.
         auto.
        apply (PairInRelation {Unions MS ! URel}) in InPUMS.
        tauto.
       apply TOD in InaOD.
       apply InaOD in Inxa'.
       auto.
      exists {x ! InxOD}.
      split.
      rewrite <- EqaA.
      apply Inxa'.
      apply SymmetryEq.
      apply (TransitivityEq (%{f ! fM} x)).
      auto.
      assert(InPMS : In (Pair x (%{f ! fM} x)) (Unions MS)).
       apply UnionsTheorem.
       exists f.
       split. 
       auto.
       assert(AppT : (&&{f ! fM}{<Map_Rel}) x (%{f ! fM} x)).
        apply AppTheorem.
       auto.
      apply (PairInRelation {_ ! UMSRel}) in InPMS.
      destruct InPMS as [InxOD' InrOR].
      apply (TransitivityEq ({_ ! InrOR})).
      auto.
      apply SymmetryEq.
      apply AppTheoremReverse.
      assert (InPUMS : In (Pair {x ! InxOD} {%{f ! fM} x ! InrOR}) (Unions MS)).
       apply UnionsTheorem.
       exists f.
       split.
       auto.
       assert(EqP : (Pair {x ! InxOD} {%{f ! fM} x ! InrOR}) == (Pair x (%{f!fM} x))).
        apply ReflexivityEq.
       rewrite EqP.
       assert(AppT : (&&{f ! fM}{<Map_Rel}) x (%{f!fM} x)).
        apply AppTheorem.
       auto.
      auto.

      destruct IncM as [x IncM].
      destruct IncM as [InxA IncM].
      assert (InxD : In x D).
       apply TD in InaD.
       rewrite <- EqaA in InxA.
       apply InaD.
       auto.
      exists {x ! InxD}.
      split.
      rewrite <- EqaA in InxA.
      apply InxA.
      apply SymmetryEq.
      apply (TransitivityEq (%{Unions MS ! UMisMap} x)).
      auto.
      assert(InPUMS : In (Pair x (%{f!fM} {x!InxD})) (Unions MS)).
       apply UnionsTheorem.
       exists f.
       split.
       auto.
       assert(AppT : (&&{f!fM}{<Map_Rel}) {x!InxD} (%{f!fM} {x!InxD})).
        apply AppTheorem.
       auto.
      generalize (PairInRelation {_!UMSRel} _ _ InPUMS); intro InPUMS'.
      destruct InPUMS' as [InxOD' InrOR].
      apply (TransitivityEq ({_!InrOR})).
      apply AppTheoremReverse.
      auto.
      auto.
 
    apply SymmetryEq.
    apply EqyF.



    apply SingletonTheorem in InP1.
    apply EqualInPair in InP1.
    destruct InP1 as [EqaA EqyF1].
    apply UnionsTheorem in InP2.
    destruct InP2 as [f InP2].
    destruct InP2 as [InfMS InPf].
    destruct (Rep2 _ InfMS) as [u Rep2'].
    destruct Rep2' as [InuA Rep2'].
    destruct Rep2' as [D Rep2'].
    destruct Rep2' as [R Rep2'].
    destruct Rep2' as [fM Rep2'].
    destruct Rep2' as [TD Rep2'].
    destruct Rep2' as [InuD Rep2'].
    destruct Rep2' as [SMT fH].
    assert(InaD : In a D /\ In y2 R).
     assert(InfRel : In f (Relation D R)).
      apply Map_Rel.
      auto.
     apply (PairInRelation {f!InfRel}) in InPf.
     auto.
    destruct InaD as [InaD InyR2].
    apply (TransitivityEq (F (%(%MapImage {Unions MS ! UMisMap}) (A{<<SP SubAOD})))).
    apply EqyF1.
    apply (TransitivityEq (F (%(%MapImage {f!fM}) {a ! (TransitivitySetPowerIn InaD TD)}))).
     apply FunRewrite.
(*    assert(EqF : (MapImage {Unions MS ! UMisMap} A) = (MapImage {f ! fM} {a ! InaD})).*)
     apply EA.
     intro c.
     split; intro IncM; apply MapImageTheorem; apply MapImageTheorem in IncM.
      destruct IncM as [x IncM].
      destruct IncM as [InxA IncM].
      assert(InxD : In x D).
       rewrite EqaA in InaD.
       apply TD in InaD.
       apply InaD.
       auto.
      exists {x!InxD}.
      split.
      rewrite <- EqaA in InxA.
      apply InxA.
      apply SymmetryEq.
      apply (TransitivityEq (%{Unions MS ! UMisMap} x)).
      auto.
      assert(InPUMS : In (Pair {x!InxD} (%{f!fM} {x!InxD})) (Unions MS)).
       apply UnionsTheorem.
       exists f.
       split.
       auto.
       assert(AppT : (&&{f!fM}{<Map_Rel}) {x!InxD} (%{f!fM} {x!InxD})).
        apply AppTheorem.
       auto.
      generalize (PairInRelation {Unions MS ! UMSRel} _ _ InPUMS); intro InPUMS'.
      destruct InPUMS' as [InxOD' InrOR].
      apply (TransitivityEq {_!InrOR}).
      apply AppTheoremReverse.
      apply InPUMS.
      apply ReflexivityEq.


      destruct IncM as [x IncM].
      destruct IncM as [Inx_a' IncM].
      assert(InxOD : In x OD).
       assert (InaOD : In a OD).
        assert (InPUMS : In (Pair a y2) (Unions MS)).
         apply UnionsTheorem.
         exists f.
         split; auto.
        assert(URel : In (Unions MS) (Relation OD OR)).
         apply Map_Rel.
         auto.
        apply (PairInRelation {Unions MS ! URel}) in InPUMS.
        tauto.
       apply TOD in InaOD.
       apply InaOD.
       auto.
      exists {x ! InxOD}.
      split.
      rewrite <- EqaA.
      apply Inx_a'.
      apply SymmetryEq.
      apply (TransitivityEq (%{f!fM} x)).
      rewrite IncM.
      apply ReflexivityEq.
      apply SymmetryEq.
      assert(InPUMS : In (Pair x (%{f!fM} x)) (Unions MS)).
       apply UnionsTheorem.
       exists f.
       split.
       auto.
       assert(AppT : (&&{f!fM}{<Map_Rel}) x (%{f!fM} x)).
        apply AppTheorem.
       auto.
      generalize (PairInRelation {Unions MS ! UMSRel} _ _ InPUMS); intro InPUMS'.
      destruct InPUMS' as [InxOD' InrOR].
      apply (TransitivityEq {_ ! InrOR}).
      apply AppTheoremReverse.
      apply InPUMS.
      apply ReflexivityEq.
(*    rewrite EqF.
    apply ReflexivityEq.*)
    apply (TransitivityEq (F (%(%MapImage {f ! fM}) {{a ! InaD} ! TransitivitySetPowerIn (SetProp {a ! InaD}) TD}))).
     hyperreflexivity.
    apply (TransitivityEq (%{f!fM} {a!InaD})).
    apply SymmetryEq.
    apply fH.
    apply (TransitivityEq {y2 ! InyR2}).
    apply AppTheoremReverse.
    apply InPf.
    apply ReflexivityEq.



    apply SingletonTheorem in InP1.
    apply SingletonTheorem in InP2.
    assert (EqP : (Pair a y1) = (Pair a y2)).
     apply (TransitivityEq (Pair A (F (%(%MapImage {Unions MS ! UMisMap}) (A{<<SP SubAOD}))))).
     apply InP1.
     rewrite InP2.
     apply ReflexivityEq.
    apply EqualInPair in EqP.
    tauto.

  split.
  rewrite NDIs_.
  intros c IncU.
  apply UnionTheorem in IncU.
  destruct IncU as [IncOD | EqcA].
   intros d Indc.
   apply UnionTheorem.
   left.
   apply TOD in IncOD.
   apply IncOD.
   auto.

   apply SingletonTheorem in EqcA.
   rewrite EqcA.
   intros d IndA.
   apply UnionTheorem.
   destruct (Rep1 _ IndA) as [g Rep1'].
   destruct Rep1' as [IngMS Rep1'].
   destruct Rep1' as [D Rep1'].
   destruct Rep1' as [R Rep1'].
   destruct Rep1' as [IngM Rep1'].
   destruct Rep1' as [TD Rep1'].
   destruct Rep1' as [IndD FEq].
   assert(SubD : Subset D OD).
    intros x InxD.
    assert(InP : In (Pair x (%{g!IngM} {x!InxD})) (Unions MS)).
     apply UnionsTheorem.
     exists g.
     split.
     auto.
     assert (AppT : (&&{g!IngM}{<Map_Rel}) {x!InxD} (%{g!IngM} {x!InxD})).
      apply AppTheorem.
     apply AppT.
    apply (PairInRelation {Unions MS ! UMSRel}) in InP.
    tauto.
   left.
   apply SubD.
   auto.

  split.
  apply (Rel_Map {_!InuMR}).
  apply cond.

  split.
  rewrite NDIs_.
  apply UnionTheorem.
  right.
  apply SingletonTheorem.
  auto.

  auto.



destruct NMSIsMap as [ND NMSIsMap].
destruct NMSIsMap as [NR NMSIsMap].
destruct NMSIsMap as [TND NMSIsMap].
destruct NMSIsMap as [NMSIsMap InAAD].
destruct InAAD as [InAAD NDIs_].
split.

exists (Union (Unions MS) (Singleton (Pair A (F (%(%MapImage {Unions MS ! UMisMap}) (A{<<SP SubAOD})))))).
exists ND.
exists NR.
exists (NMSIsMap).
exists TND.
split.
auto.
split.
intros D' InAD' TD'.
intros n InND.
rewrite NDIs_ in InND.
apply UnionTheorem in InND.
destruct InND as [InnOD | EqnA].
 assert (SubAD' : Subset A D').
  apply TD'.
  auto.
 apply (OTD _ SubAD' TD').
 auto.

 apply SingletonTheorem in EqnA.
 rewrite EqnA.
 auto.


intros u.
assert(NMSRel : In (Union (Unions MS) (Singleton (Pair A (F (%(%MapImage {Unions MS ! UMisMap}) (A{<<SP SubAOD})))))) (Relation ND NR)).
 apply Map_Rel.
 auto.
assert(InP : In (Pair u (%{_!NMSIsMap} u)) (Union (Unions MS) (Singleton (Pair A (F (%(%MapImage {Unions MS ! UMisMap}) (A{<<SP SubAOD}))))))).
 assert(AppT : (&&{_!NMSIsMap}{<Map_Rel}) u (%{_!NMSIsMap} u)).
  apply AppTheorem.
 apply AppT.
apply UnionTheorem in InP.
destruct InP as [InP | InP].
 apply UnionsTheorem in InP.
 destruct InP as [f InP].
 destruct InP as [InfMS InPf].
 destruct (Rep2 _ InfMS) as [v Rep2'].
 destruct Rep2' as [InvA Rep2'].
 destruct Rep2' as [D Rep2'].
 destruct Rep2' as [R Rep2'].
 destruct Rep2' as [gM Rep2'].
 destruct Rep2' as [TD Rep2'].
 destruct Rep2' as [InvD Rep2'].
 destruct Rep2' as [MTD Rep2'].
 assert (InuD : In u D /\ In (%{_!NMSIsMap} u) R).
  assert (gR : In f (Relation D R)).
   apply Map_Rel.
  assumption.
  apply (PairInRelation {f!gR}) in InPf.
  auto.
 destruct InuD as [InuD InrR].
 apply (TransitivityEq (%{f!gM} {u!InuD})).
 apply (TransitivityEq {_!InrR}).
 apply ReflexivityEq.
 apply SymmetryEq.
 apply AppTheoremReverse.
 apply InPf.
 apply (TransitivityEq (F (%(%MapImage {f!gM}) {{u ! InuD}!(TransitivitySetPowerIn (SetProp {u ! InuD}) TD)}))).
 apply Rep2'.
  apply FunRewrite.
  apply EA.
  intro c.
  split; intro IncM; apply MapImageTheorem; apply MapImageTheorem in IncM.
   destruct IncM as [x IncM].
   destruct IncM as [Inxu' IncM].
   assert(InxND : In x ND).
    assert (subu : Subset u ND).
     apply TND.
     auto.
    apply subu.
    auto.
   exists {x!InxND}.
   split.
   apply Inxu'.
   apply SymmetryEq.
   apply (TransitivityEq (%{f!gM} x)).
   rewrite IncM.
   apply ReflexivityEq.
   assert(InPf2 : In (Pair x (%{f!gM} x)) (Union (Unions MS) (Singleton (Pair A (F (%(%MapImage {Unions MS ! UMisMap}) (A{<<SP SubAOD}))))))).
    apply UnionTheorem.
    left.
    apply UnionsTheorem.
    exists f.
    split.
    auto.
    assert(AppT : (&&{f!gM}{<Map_Rel}) x (%{f!gM} x)).
     apply AppTheorem.
    apply AppT.
   
   generalize (PairInRelation {_!NMSRel} _ _ InPf2); intro InPf2'.
   destruct InPf2' as [InxND' InrNR].
   apply (TransitivityEq {_!InrNR}).
   apply ReflexivityEq.
   apply SymmetryEq.
   apply AppTheoremReverse.
   apply InPf2.



   destruct IncM as [x IncM].
   destruct IncM as [Inxu IncM].
   assert(InxD : In x D).
    assert(subu : Subset u D).
     apply TD.
     auto.
    apply subu.
    auto.
   exists {x!InxD}.
   split.
   apply Inxu.
   apply (TransitivityEq (%{_!NMSIsMap} x)).
   assert(InPf2 : In (Pair x (%{f!gM} {x!InxD})) (Union (Unions MS) (Singleton (Pair A (F (%(%MapImage {Unions MS ! UMisMap}) (A{<<SP SubAOD}))))))).
    apply UnionTheorem.
    left.
    apply UnionsTheorem.
    exists f.
    split.
    auto.
    assert(AppT : (&&{f!gM}{<Map_Rel}) {x!InxD} (%{f!gM} {x!InxD})).
     apply AppTheorem.
    apply AppT.
   generalize (PairInRelation {_!NMSRel} _ _ InPf2); intro InPf2'.
   destruct InPf2' as [InxND' InrNR].
   apply (TransitivityEq {_!InrNR}).
   apply ReflexivityEq.
   apply SymmetryEq.
   apply AppTheoremReverse.
   apply InPf2.
   apply IncM.


 apply SingletonTheorem in InP.
 apply EqualInPair in InP.
 destruct InP as [EquA NFE].
 
 apply (TransitivityEq (F (%(%MapImage {Unions MS ! UMisMap}) (A{<<SP SubAOD})))).
 assumption.
 apply FunRewrite.
 assert(InNPND : In A (PowerSet ND)).
  apply TND in InAAD.
  apply PowersetTheorem.
  assumption.
 apply (TransitivityEq (%(%MapImage {_ ! NMSIsMap}) {A ! InNPND})).
  apply EA.
  intro c.
  split; intro IncM; apply MapImageTheorem; apply MapImageTheorem in IncM.
   destruct IncM as [x IncM].
   destruct IncM as [Inxu IncM].
   assert(InxND : In x ND).
    rewrite NDIs_.
    apply UnionTheorem.
    auto.
   exists {x!InxND}.
   split.
   apply Inxu.
   apply SymmetryEq.
   transitivity (%{Unions MS ! UMisMap} x).
   rewrite IncM.
   apply ReflexivityEq.
   assert(InP : In (Pair x (%{Unions MS ! UMisMap} x)) (Union (Unions MS) (Singleton (Pair A (F (%(%MapImage {Unions MS ! UMisMap}) (A{<<SP SubAOD}))))))).
    apply UnionTheorem.
    left.
    assert(AppT : (&&{Unions MS ! UMisMap}{<Map_Rel}) x (%{Unions MS ! UMisMap} x)).
     apply AppTheorem.
    apply AppT.
   generalize (PairInRelation {_ ! NMSRel} _ _ InP); intro InP'.
   destruct InP' as [InxND' InrNR].
   apply (TransitivityEq {_!InrNR}).
   apply ReflexivityEq.
   apply SymmetryEq.
   apply AppTheoremReverse.
   apply InP.

   destruct IncM as [x IncM].
   destruct IncM as [Inxu IncM].
   assert(InxOD : In x OD).
    assert(InxA : In x A).
     rewrite <- EquA.
     auto.
    assert(InxUOA : In x (Union OD (Singleton A))).
     rewrite <- NDIs_.
     auto.
    apply UnionTheorem in InxUOA.
    destruct InxUOA as [InxOD | EqxA].
    rewrite EquA.
    apply Inxu.
    apply SingletonTheorem in EqxA.
    rewrite EqxA in Inxu.
    assert(cond : In A A).
     apply Inxu.
    apply NotIncludeOwn in cond.
    contradiction.
   apply SubAOD.
   assumption.
   exists {x!InxOD}.
   split.
   apply Inxu.
   apply SymmetryEq.
   apply (TransitivityEq (%{_!NMSIsMap} x)).
   rewrite IncM.
   apply ReflexivityEq.
   assert(InP : In (Pair x (%{Unions MS ! UMisMap} {x!InxOD})) (Union (Unions MS) (Singleton (Pair A (F (%(%MapImage {Unions MS ! UMisMap}) (A{<<SP SubAOD}))))))).
    apply UnionTheorem.
    left.
    assert(AppT : (&&{Unions MS ! UMisMap}{<Map_Rel}) {x!InxOD} (%{Unions MS ! UMisMap} {x!InxOD})).
     apply AppTheorem.
    apply AppT.
   generalize (PairInRelation {_!NMSRel} _ _ InP); intro InP'.
   destruct InP' as [InxND' InrNR].
   transitivity {_!InrNR}.
   apply AppTheoremReverse.
   apply InP.
   apply ReflexivityEq.
 apply MapArgEq.
 apply (TransitivityEq A).
 hyperreflexivity.
 apply (TransitivityEq u).
 apply SymmetryEq.
 assumption.
 hyperreflexivity.


intros g1 g2 H1 H2.
destruct H1 as [D1 H1].
destruct H1 as [R1 H1].
destruct H1 as [gM1 H1].
destruct H1 as [TD1 H1].
destruct H1 as [InAD1 H1].
destruct H1 as [TMD1 H1].
destruct H2 as [D2 H2].
destruct H2 as [R2 H2].
destruct H2 as [gM2 H2].
destruct H2 as [TD2 H2].
destruct H2 as [InAD2 H2].
destruct H2 as [TMD2 H2].
assert(EqD : D1 = D2).
 apply (AntisymmetrySubset).
  apply TMD1.
  auto.
  auto.

  apply TMD2.
  auto.
  auto.
apply (MapEquality {g1!gM1} {g2!gM2} EqD).
assert(LastStep : forall d (d1 : In d D1) (d2 : In d D2), (%{g1!gM1} {d!d1}) == (%{g2!gM2} {d!d2})).
apply (SetInductionAxiom (fun d => forall (d1 : In d D1) (d2 : In d D2), (%{g1!gM1} {d!d1}) == (%{g2!gM2} {d!d2}))).
 intros d HH d1 d2.
 apply (TransitivityEq (F (%(%MapImage {g1!gM1}) ({{d ! d1} ! TransitivitySetPowerIn (SetProp {d ! d1}) TD1})))).
 apply H1.
 apply SymmetryEq.
 apply (TransitivityEq (F (%(%MapImage {g2!gM2}) ({{d ! d2} ! TransitivitySetPowerIn (SetProp {d ! d2}) TD2})))).
 apply H2.
 apply FunRewrite.
  apply EA.
  intros c.
  split; intro IncM; apply MapImageTheorem; apply MapImageTheorem in IncM; destruct IncM as [x IncM]; destruct IncM as [Inxd IncM].
   assert(InxD1 : In x D1).
    rewrite EqD.
    apply SetProp.
   exists {x!InxD1}.
   split.
   apply Inxd.
   apply SymmetryEq.
   apply (TransitivityEq (%{g2!gM2} x)).
   rewrite IncM.
   apply ReflexivityEq.
   assert(InxD2 : In x D2).
    apply SetProp.
   apply (TransitivityEq (%{g2!gM2} {x ! InxD2})).
   hyperreflexivity.
   apply SymmetryEq.
   apply HH.
   apply Inxd.

   assert(InxD2 : In x D2).
    rewrite <- EqD.
    apply SetProp.
   exists {x!InxD2}.
   split.
   apply Inxd.
   apply SymmetryEq.
   apply (TransitivityEq (%{g1!gM1} x)).
   apply SymmetryEq.
   apply IncM.
   apply (TransitivityEq (%{g1!gM1} {x!(SetProp x)})).
   hyperreflexivity.
   apply HH.
   apply Inxd.


intros d1 d2 Eqd.
assert(Ind1 : In d1 D1).
 apply SetProp.
assert(Ind2 : In d1 D2).
 rewrite EqD in Ind1.
 assumption.
apply (TransitivityEq (%{g1!gM1} {d1!Ind1})).
apply (MapArgEq).
apply ReflexivityEq.
apply SymmetryEq.
apply (TransitivityEq (%{g2!gM2} {d1!Ind2})).
apply (MapArgEq).
rewrite <- Eqd.
apply ReflexivityEq.
apply SymmetryEq.
apply LastStep.
Qed.




Definition TransitiveRecursiveMap F y :=
UniqueOut _ (TransitiveRecursiveMapUnique F y).

Theorem TransitiveRecursiveMapUniqueOutTheorem : forall F y,
  exists D, exists R, exists gMap : In (TransitiveRecursiveMap F y) (Map D R), exists TTD : TransitivitySet D,
    In y D /\ (forall D', In y D' -> TransitivitySet D' -> Subset D D') /\
forall (u : #D), (%{_!gMap} u) == F (%(%MapImage {_!gMap}) {u ! TransitivitySetPowerIn (SetProp u) TTD}).
Proof.
intros F y.
apply (HUniqueOut _ (TransitiveRecursiveMapUnique F y)).
Qed.

Theorem TransitiveRecursiveMapIsAllEqual : forall F y1 y2,
forall D1 R1 D2 R2 
(g1 : In (TransitiveRecursiveMap F y1) (Map D1 R1))
(g2 : In (TransitiveRecursiveMap F y2) (Map D2 R2)),
forall u (u1 : In u D1) (u2 : In u D2),
(%{_!g1} {u!u1}) == (%{_!g2} {u!u2}).
Proof.
intros F y1 y2 D1 R1 D2 R2 g1 g2.
assert (IndH : forall A,
  (forall u, In u A -> forall (u1 : In u D1) (u2 : In u D2), (%{_!g1} {u!u1}) == (%{_!g2} {u!u2})) ->
  forall (A1 : In A D1) (A2 : In A D2), (%{_!g1} {A!A1}) == (%{_!g2} {A!A2})).
 intros A IndH A1 A2.
 destruct (TransitiveRecursiveMapUniqueOutTheorem F y1) as [D1' TFT1].
 destruct TFT1 as [R1' TFT1].
 destruct TFT1 as [g1' TFT1].
 destruct TFT1 as [TT1 TFT1].
 destruct TFT1 as [Iny1D TFT1].
 destruct (TransitiveRecursiveMapUniqueOutTheorem F y2) as [D2' TFT2].
 destruct TFT2 as [R2' TFT2].
 destruct TFT2 as [g2' TFT2].
 destruct TFT2 as [TT2 TFT2].
 destruct TFT2 as [Iny2D TFT2].
 assert (EqD1 : D1 = D1').
  apply (MapHasSameDomain {_!g1} {_!g1'}).
  apply ReflexivityEq.
 assert (EqD2 : D2 = D2').
  apply (MapHasSameDomain {_!g2} {_!g2'}).
  apply ReflexivityEq.
 assert (A1' : In A D1').
  rewrite <- EqD1.
  auto.
 assert (A2' : In A D2').
  rewrite <- EqD2.
  auto.
 assert (Eqg1 : (%{_!g1} {A!A1}) == (%{_!g1'} {A!A1'})).
  apply (MapEqAll).
  apply ReflexivityEq.
  apply ReflexivityEq. 
 assert (Eqg2 : (%{_!g2} {A!A2}) == (%{_!g2'} {A!A2'})).
  apply (MapEqAll).
  apply ReflexivityEq.
  apply ReflexivityEq.
 apply (TransitivityEq (%{_!g1'} {A!A1'})).
  hyperreflexivity.
 apply (TransitivityEq (F (%(%MapImage {_!g1'}) {{A!A1'} ! TransitivitySetPowerIn (SetProp {A!A1'}) TT1}))).
  apply TFT1.
 apply SymmetryEq.
 apply (TransitivityEq (%{_!g2'} {A!A2'})).
  hyperreflexivity.
 apply (TransitivityEq (F (%(%MapImage {_!g2'}) {{A!A2'} ! TransitivitySetPowerIn (SetProp {A!A2'}) TT2}))).
  apply TFT2.
 apply SymmetryEq.
 apply FunRewrite.
   apply EA.
   intro c.
   split; intro IncM; apply MapImageTheorem in IncM; apply MapImageTheorem; destruct IncM as [a IncM]; destruct IncM as [Ina Eqgc].
    assert (InaD2 : In a D2').
     assert(A2'' : In A D2'); auto.
     apply TT2 in A2''.
     apply A2''.
     auto.
    exists {a!InaD2}.
    split.
    apply Ina.
    apply SymmetryEq.
    apply (TransitivityEq (%{_!g1'} a)).
    rewrite Eqgc.
    apply ReflexivityEq.
    assert(In_aD1 : In a D1).
     rewrite EqD1.
     auto.
    assert(In_aD2 : In a D2).
     rewrite EqD2.
     auto.
    assert(Eqg1' : (%{_!g1'} a) == (%{_!g1} {a!In_aD1})).
     apply (MapEqAll).
     apply ReflexivityEq.
     apply ReflexivityEq.
    assert(Eqg2' : (%{_!g2'} {a!InaD2}) == (%{_!g2} {a!In_aD2})).
     apply (MapEqAll).
     apply ReflexivityEq.
     apply ReflexivityEq.
    apply (TransitivityEq (%{_!g1} {a!In_aD1})).
    apply Eqg1'.
    apply (TransitivityEq (%{_!g2} {a!In_aD2})).
    assert(InaA : In a A).
     apply Ina.
    apply (IndH _ InaA).
    apply MapEqAll.
    apply ReflexivityEq.
    apply ReflexivityEq.

    assert (InaD1 : In a D1').
     assert(A1'' : In A D1'); auto.
     apply TT1 in A1''.
     apply A1''.
     auto.
    exists {a!InaD1}.
    split.
    apply Ina.
    apply SymmetryEq.
    apply (TransitivityEq (%{_!g2'} a)).
    rewrite Eqgc.
    apply ReflexivityEq.
    assert(In_aD1 : In a D1).
     rewrite EqD1.
     auto.
    assert(In_aD2 : In a D2).
     rewrite EqD2.
     auto.
    assert(Eqg2' : (%{_!g2'} a) == (%{_!g2} {a!In_aD2})).
     apply (MapEqAll).
     apply ReflexivityEq.
     apply ReflexivityEq.
    assert(Eqg1' : (%{_!g1'} {a!InaD1}) == (%{_!g1} {a!In_aD1})).
     apply (MapEqAll).
     apply ReflexivityEq.
     apply ReflexivityEq.
    apply (TransitivityEq (%{_!g2} {a!In_aD2})).
    apply Eqg2'.
    apply (TransitivityEq (%{_!g1} {a!In_aD1})).
    assert(InaA : In a A).
     apply Ina.
    apply SymmetryEq.
    apply (IndH _ InaA).
    apply MapEqAll.
    apply ReflexivityEq.
    apply ReflexivityEq.

apply (SetInductionAxiom _ IndH).
Qed.


Theorem TransitiveRecursiveFunctionUnique : forall F y,
Unique (fun w =>
  exists D, exists R, exists g : In (TransitiveRecursiveMap F y) (Map D R),
    exists InyD : In y D, exists TDD : TransitivitySet D, (%{_!g} {y!InyD}) == w /\ forall _u (u : In _u D), (%{_!g} {_!u}) == F (%(%MapImage {_!g}) {_u!(TransitivitySetPowerIn u TDD)})
).
Proof.
intros F y.
split.

destruct (TransitiveRecursiveMapUniqueOutTheorem F y) as [D TRT].
destruct TRT as [R TRT].
destruct TRT as [g TRT].
destruct TRT as [TD TRT].
destruct TRT as [InyD TRT].
destruct TRT as [MST TRT].
exists (%{_!g} {y!InyD}).
exists D.
exists R.
exists g.
exists InyD.
exists TD.
split.
hyperreflexivity.
intros _u u.
apply (TransitivityEq (F (%(%MapImage {TransitiveRecursiveMap F y! g}) {{_u!u} ! TransitivitySetPowerIn (SetProp {_u!u}) TD}))).
 apply TRT.
hyperreflexivity.


intros w1 w2 H1 H2.
destruct H1 as [D1 H1].
destruct H1 as [R1 H1].
destruct H1 as [g1 H1].
destruct H1 as [InyD1 H1].
destruct H1 as [TDD1 H1].
destruct H1 as [Eqwg1 H1].
destruct H2 as [D2 H2].
destruct H2 as [R2 H2].
destruct H2 as [g2 H2].
destruct H2 as [InyD2 H2].
destruct H2 as [TDD2 H2].
destruct H2 as [Eqwg2 H2].
assert (Eqg : (%{_!g1} {y!InyD1}) == (%{_!g2} {y!InyD2})).
 apply (MapEqAll).
 apply ReflexivityEq.
 apply ReflexivityEq.
apply (TransitivityEq (%{_!g1} {y!InyD1})).
rewrite Eqwg1.
apply ReflexivityEq.
apply (TransitivityEq (%{_!g2} {y!InyD2})).
apply Eqg.
apply Eqwg2.
Qed.

Definition TransitiveRecursiveFunction F := fun y =>
UniqueOut _ (TransitiveRecursiveFunctionUnique F y).

Theorem TransitiveRecursiveFunctionUniqueOutTheorem : forall F y,
  exists D, exists R, exists g : In (TransitiveRecursiveMap F y) (Map D R),
    exists InyD : In y D, exists TDD : TransitivitySet D, (%{_!g} {y!InyD}) == (TransitiveRecursiveFunction F y) /\ forall _u (u : In _u D), (%{_!g} {_!u}) == F (%(%MapImage {_!g}) {_u!(TransitivitySetPowerIn u TDD)}).
Proof.
intros F y.
apply (HUniqueOut _ (TransitiveRecursiveFunctionUnique F y)).
Qed.

Theorem TransitiveRecursiveFunctionTheorem : forall F y,
((TransitiveRecursiveFunction F) y) == (F (FunctionImageRistriction (TransitiveRecursiveFunction F) y)).
Proof.
intros F y.
destruct (TransitiveRecursiveFunctionUniqueOutTheorem F y) as [D TFF].
destruct TFF as [R TFF].
destruct TFF as [g TFF].
destruct TFF as [InyD TFF].
destruct TFF as [TD TFF].
destruct TFF as [EqgT TFF].
apply (TransitivityEq (%{_!g} {y!InyD})).
auto.
apply (TransitivityEq (F (%(%MapImage {_!g}) {y ! TransitivitySetPowerIn InyD TD}))).
apply TFF.
apply FunRewrite.
 apply EA.
 intro c.
 split.
  intro IncM.
  apply MapImageTheorem in IncM.
  destruct IncM as [_a IncM].
  destruct IncM as [In_ay' IncM].
  apply FunctionImageRistrictionTheorem.
  exists _a.
  split.
  auto.
  apply SymmetryEq.
  apply (TransitivityEq (%{_!g} _a)).
  rewrite IncM.
  apply ReflexivityEq.
  destruct (TransitiveRecursiveFunctionUniqueOutTheorem F _a) as [Da TFFa].
  destruct TFFa as [Ra TFFa].
  destruct TFFa as [ga TFFa].
  destruct TFFa as [InyDa TFFa].
  destruct TFFa as [EqgTa TFFa].
  destruct TFFa as [TDa FEqa].
  transitivity (%{_!ga} {_a!InyDa}).
  assert(InaD : In _a D).
   apply SetProp.
  apply (TransitivityEq (%{_!g} {_a!InaD})).
  apply MapEqAll.
  apply ReflexivityEq.
  apply ReflexivityEq.
  apply (TransitiveRecursiveMapIsAllEqual).
  auto.

  intros IncF.
  apply FunctionImageRistrictionTheorem in IncF.
  destruct IncF as [_a IncF].
  destruct IncF as [Inay EqTc].
  apply MapImageTheorem.
  assert (InaD : In _a D).
   assert (InyD' : In y D); auto.
   apply TD in InyD'.
   apply InyD'.
   auto.
  exists {_a!InaD}.
  split.
  apply Inay.
  apply SymmetryEq.
  apply (TransitivityEq (TransitiveRecursiveFunction F _a)).
  auto.
  destruct (TransitiveRecursiveFunctionUniqueOutTheorem F _a) as [Da TFFa].
  destruct TFFa as [Ra TFFa].
  destruct TFFa as [ga TFFa].
  destruct TFFa as [InyDa TFFa].
  destruct TFFa as [TDa TFFa].
  destruct TFFa as [EqTFFa TFFa].
  apply (TransitivityEq (%{_!ga} {_!InyDa})).
  auto.
  apply (TransitiveRecursiveMapIsAllEqual).
Qed.


 
(* TransitivitySet Lemmas *)
Theorem TransitivitySet0 : TransitivitySet Empty.
intros c IncE cc InccE.
apply EmptyTheorem in IncE.
tauto.
Qed.

Theorem TransitivitySetNext : forall A , 
TransitivitySet A -> TransitivitySet (Next A).
intros A TA.
intros c IncN.
apply UnionTheorem in IncN.
destruct IncN as [IncA | EqcA].
 apply TA in IncA.
 apply (TransitivitySubset A); auto.
 apply UnionSubsetL.

 apply SingletonTheorem in EqcA.
 rewrite EqcA.
 apply UnionSubsetL.
Qed.

Theorem TransitivitySetNat : forall n, In n NN -> TransitivitySet n.
Proof.
intros n InnNN.
assert(EqTn : (SSet NN (fun n => TransitivitySet n)) == NN).
 apply (PeanoAxiom5).
 apply SSetSubset.
 split.
  apply SSetTheorem.
  split.
  apply PeanoAxiom1.
  apply TransitivitySet0.
  intros a InaS.
  apply SSetTheorem in InaS.
  destruct InaS as [InaNN Ta].
  apply SSetTheorem.
  split.
  apply PeanoAxiom2.
  assumption.
  apply TransitivitySetNext.
  assumption.
 rewrite <- EqTn in InnNN.
 apply SSetTheorem in InnNN.
 destruct InnNN as [InnNN Tn].
 assumption.
Qed.


Theorem TransitivitySetNN : TransitivitySet NN.
Proof.
assert(EqS : (SSet NN (fun a => Subset a NN)) == NN).
 apply PeanoAxiom5.
 apply SSetSubset.
 split.
  apply SSetTheorem.
  split.
  apply PeanoAxiom1.
  apply AllSetHasEmpty.

  intros n InnS.
  apply SSetTheorem in InnS.
  destruct InnS as [InnNN Sub].
  apply SSetTheorem.
  split.
  apply PeanoAxiom2.
  assumption.
  intros a InaN.
  apply UnionTheorem in InaN.
  destruct InaN as [Inan | Eqan].
   apply Sub.
   assumption.

   apply SingletonTheorem in Eqan.
   rewrite Eqan.
   assumption.

intros a InaNN.
rewrite <- EqS in InaNN.
apply SSetTheorem in InaNN.
destruct InaNN as [InaNN Sub].
assumption.
Qed.












