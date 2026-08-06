/-
# The shared-circuit-pair law at corank-2 ties, uniformly in the rank

**Headline** (`sharedCircuitPairAtCorankTwoTie_holds`): for every rank ≥ 2,
every primitive tie at the corank-2 cell `(rank + 2, rank)` carries two
dependent rank-subsets overlapping in a `(rank − 2)`-core and jointly covering
all `rank + 2` atoms — the two-triangles-glued-along-an-edge shape of the
graphic matroid `M(K4 − e)`, generalized.

**Route** (the `(5,3)` endgame of
`EndpointSpike.sharedLinePairAtEveryTie_holds`, generalized):

1. the tie locks its rank-two Naimark dual (`exists_tieLockedNaimarkDual`):
   no strictly dominating dual pair, hence — through the rank-two hinge — a
   bracket-zero pair inside EVERY dual quadruple;
2. a symmetric relation on `rank + 2 ≥ 5` vertices covering every quadruple
   contains a two-edge matching or a triangle (the Gallai dichotomy of
   `EndpointSpike.matching_or_triangle_of_coveringEdges`, re-proved at every
   vertex count ≥ 5);
3. MATCHING: the two dictionary dependences complement the two edges — core =
   the four matched labels' complement (card `rank − 2`), each dependent
   rank-subset = core plus one edge;
4. TRIANGLE: the triple dictionary yields ONE dependence supported on the
   `rank − 1` labels OFF the triangle (`exists_dependentRest_of_dualTriangle`,
   the triangle branch's forcing STATED GENERALLY).  At rank 3 the rest is a
   PAIR, so a primitive design kills the branch outright (same endpoint as
   the five-coplanar/Parseval argument, by a shorter mechanism — see the
   killer's docstring).  At rank ≥ 4 the branch is already combinatorially
   dead: a covering edge set with a triangle but no two disjoint edges would
   leave an edge-free quadruple (one triangle vertex plus three outsiders).

**Cross-checks**, all kernel theorems below:
* the rank = 3 instance REPROVES
  `EndpointSpike.SharedLinePairAtEveryTieFiveThree` on the same hypotheses
  (`sharedLinePairAtEveryTieFiveThree_rederived`);
* rank = 2 degenerate reading: the law holds because no primitive `(4,2)` tie
  exists (`not_isTie_of_isPrimitive_fourTwo`), and its conclusion is
  UNSATISFIABLE for primitive designs
  (`sharedCircuitPair_conclusion_impossible_rankTwo`) — so at rank 2 the law
  IS the no-tie statement;
* the diamond, the kernel-checked primitive `(5,3)` tie, realizes the law
  (`diamond_realizes_sharedCircuitPair`) — the general statement predicts a
  1-core with two dependent triples, exactly the pair `{0,1,3}`/`{0,2,4}`
  through atom `0`.

**The corank-1 analogue** (`corankOneTie_isUniformCircuit`): at corank 1 the
analogous law says the tie's direction matroid is the uniform circuit
`U(rank, rank+1)` — every rank-subset independent, the full ground set the
unique circuit, and the design primitive — assembled from
`Gtz.corankOne_isTie_det_ne_zero` / `Gtz.corankOne_isTie_not_parallel` plus
rank-nullity for the full dependence.
-/
import Mathlib
import Gtz.Ties.SpikeMatroidObstruction
import Gtz.Ties.TotalTieCorankOne
import Gtz.Design.DiamondPrimitive
import Gtz.Design.StratumEmptinessLedger
import Gtz.Uniform.CorankTwoTransfer

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace CorankTwo

open Matrix Finset Gtz

/-! ## The rank-generic dependency vocabulary and the target Prop -/

/-- A selection of atom labels is DEPENDENT: some coefficient vector supported
inside the selection, not identically zero, kills the atoms.  Width-specific
determinant forms the tree already speaks: `Gtz.pairBracket` at rank 2,
`Gtz.atomBracket` at rank 3. -/
def IsDependentSelection {size rank : ℕ} (design : WeightedDesign size rank)
    (chosen : Finset (Fin size)) : Prop :=
  ∃ dependence : Fin size → ℝ,
    (∃ witnessLabel, dependence witnessLabel ≠ 0)
      ∧ (∀ label, label ∉ chosen → dependence label = 0)
      ∧ (∑ label, dependence label • design.atom label) = 0

/-- **The shared-circuit-pair law at corank-2 ties, rank-generic.**  Every
primitive tie at `(rank + 2, rank)` carries two dependent rank-subsets
overlapping in a `(rank − 2)`-core and jointly covering all atoms. -/
def SharedCircuitPairAtCorankTwoTie (rank : ℕ) : Prop :=
  2 ≤ rank →
    ∀ design : WeightedDesign (rank + 2) rank,
      IsPrimitiveDesign design → IsTie design →
      ∃ core pairOne pairTwo : Finset (Fin (rank + 2)),
        core.card = rank - 2 ∧ pairOne.card = 2 ∧ pairTwo.card = 2
          ∧ Disjoint core pairOne ∧ Disjoint core pairTwo
          ∧ Disjoint pairOne pairTwo
          ∧ IsDependentSelection design (core ∪ pairOne)
          ∧ IsDependentSelection design (core ∪ pairTwo)

/-! ## Plane-dimension kit -/

/-- Two vectors of any coordinate dimension carry no nontrivial vanishing
combination unless parallel — the width-generic form of
`EndpointSpike.coeffPair_eq_zero_of_smul_add_smul_eq_zero`, which is
`Fin 3`-typed. -/
theorem coeffPair_eq_zero_of_smul_add_smul_eq_zero {dim : ℕ}
    (leftVector rightVector : Fin dim → ℝ) (leftScalar rightScalar : ℝ)
    (hfree : ∀ ratio : ℝ, rightVector ≠ ratio • leftVector)
    (hleftNonzero : leftVector ≠ 0)
    (hvanish : leftScalar • leftVector + rightScalar • rightVector = 0) :
    leftScalar = 0 ∧ rightScalar = 0 := by
  by_cases hright : rightScalar = 0
  · refine ⟨?_, hright⟩
    rw [hright, zero_smul, add_zero] at hvanish
    rcases smul_eq_zero.mp hvanish with hscalar | hvector
    · exact hscalar
    · exact absurd hvector hleftNonzero
  · exfalso
    refine hfree ((-leftScalar) / rightScalar) ?_
    have hsolve : rightScalar • rightVector = (-leftScalar) • leftVector := by
      rw [neg_smul]
      exact eq_neg_of_add_eq_zero_left (by rw [add_comm]; exact hvanish)
    calc rightVector = rightScalar⁻¹ • (rightScalar • rightVector) := by
          rw [smul_smul, inv_mul_cancel₀ hright, one_smul]
      _ = rightScalar⁻¹ • ((-leftScalar) • leftVector) := by rw [hsolve]
      _ = ((-leftScalar) / rightScalar) • leftVector := by
          rw [smul_smul, div_eq_inv_mul]

/-- A vanishing plane determinant against a nonzero base exhibits the ratio:
the other vector is a multiple of the base. -/
theorem eq_smul_of_planeDet_eq_zero (baseVector otherVector : Fin 2 → ℝ)
    (hbaseNonzero : baseVector ≠ 0)
    (hdet : baseVector 0 * otherVector 1 - baseVector 1 * otherVector 0 = 0) :
    ∃ ratio : ℝ, otherVector = ratio • baseVector := by
  by_cases hbaseFst : baseVector 0 = 0
  · have hbaseSnd : baseVector 1 ≠ 0 := by
      intro hsnd
      refine hbaseNonzero (funext ?_)
      rw [Fin.forall_fin_two]
      exact ⟨hbaseFst, hsnd⟩
    have hotherFst : otherVector 0 = 0 := by
      rw [hbaseFst, zero_mul, zero_sub, neg_eq_zero] at hdet
      rcases mul_eq_zero.mp hdet with hdead | hzero
      · exact absurd hdead hbaseSnd
      · exact hzero
    refine ⟨otherVector 1 / baseVector 1, funext ?_⟩
    rw [Fin.forall_fin_two]
    constructor
    · show otherVector 0 = otherVector 1 / baseVector 1 * baseVector 0
      rw [hotherFst, hbaseFst, mul_zero]
    · show otherVector 1 = otherVector 1 / baseVector 1 * baseVector 1
      field_simp
  · refine ⟨otherVector 0 / baseVector 0, funext ?_⟩
    rw [Fin.forall_fin_two]
    constructor
    · show otherVector 0 = otherVector 0 / baseVector 0 * baseVector 0
      field_simp
    · show otherVector 1 = otherVector 0 / baseVector 0 * baseVector 1
      rw [div_mul_eq_mul_div, eq_div_iff hbaseFst]
      linear_combination hdet

/-- **A dependent pair is impossible in a primitive design.**  A nontrivial
dependence supported on two labels is a parallel pair or a zero atom. -/
theorem dependentPair_impossible_of_isPrimitive {size rank : ℕ} (hsize : 2 ≤ size)
    (design : WeightedDesign size rank) (hprimitive : IsPrimitiveDesign design)
    (pairSet : Finset (Fin size)) (hpairCard : pairSet.card = 2) :
    ¬ IsDependentSelection design pairSet := by
  rintro ⟨dependence, ⟨witnessLabel, hwitnessNe⟩, hsupport, hsum⟩
  obtain ⟨labelFst, labelSnd, hlabelNe, hpairEq⟩ := Finset.card_eq_two.mp hpairCard
  have hoffSupport : ∀ label ∈ (Finset.univ : Finset (Fin size)), label ∉ pairSet →
      dependence label • design.atom label = 0 := fun label _ hnot => by
    rw [hsupport label hnot, zero_smul]
  have hcollapsed := Finset.sum_subset (Finset.subset_univ pairSet) hoffSupport
  rw [hsum, hpairEq, Finset.sum_pair hlabelNe] at hcollapsed
  obtain ⟨hfstZero, hsndZero⟩ :=
    coeffPair_eq_zero_of_smul_add_smul_eq_zero (design.atom labelFst) (design.atom labelSnd)
      (dependence labelFst) (dependence labelSnd)
      (fun ratio => hprimitive labelFst labelSnd ratio hlabelNe)
      (atom_ne_zero_of_isPrimitiveDesign hsize design hprimitive labelFst)
      hcollapsed
  have hwitnessMem : witnessLabel ∈ pairSet := by
    by_contra hnot
    exact hwitnessNe (hsupport witnessLabel hnot)
  rw [hpairEq] at hwitnessMem
  rcases Finset.mem_insert.mp hwitnessMem with rfl | hmem
  · exact hwitnessNe hfstZero
  · rw [Finset.mem_singleton] at hmem
    subst hmem
    exact hwitnessNe hsndZero

/-! ## The rank-2 floor: no primitive `(4,2)` tie -/

/-- **No primitive `(4,2)` tie exists** — the degenerate floor of the law.
Primitivity makes all six pair brackets nonzero, and the rank-two hinge
(through `Gtz.not_isTie_of_fourDirections`) then forbids the tie. -/
theorem not_isTie_of_isPrimitive_fourTwo (design : WeightedDesign 4 2)
    (hprimitive : IsPrimitiveDesign design) : ¬ IsTie design := by
  have hbracketNe : ∀ leftLabel rightLabel : Fin 4, leftLabel ≠ rightLabel →
      pairBracket design leftLabel rightLabel ≠ 0 := by
    intro leftLabel rightLabel hlabelNe hzero
    obtain ⟨ratio, hratio⟩ := eq_smul_of_planeDet_eq_zero
      (design.atom leftLabel) (design.atom rightLabel)
      (atom_ne_zero_of_isPrimitiveDesign (by norm_num) design hprimitive leftLabel) hzero
    exact hprimitive leftLabel rightLabel ratio hlabelNe hratio
  exact not_isTie_of_fourDirections rankTwoFourDirectionHinge_holds design 0 1 2 3
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (hbracketNe 0 1 (by decide)) (hbracketNe 0 2 (by decide))
    (hbracketNe 0 3 (by decide)) (hbracketNe 1 2 (by decide))
    (hbracketNe 1 3 (by decide)) (hbracketNe 2 3 (by decide))

/-! ## The covering-edge combinatorics at every vertex count

`EndpointSpike.matching_or_triangle_of_coveringEdges` is `Fin 5`-typed
through its translate trick; the general form below replaces translates by a
four-element subset avoiding the excluded vertex, and adds the `≥ 6`-vertex
refinement that kills the matching-free triangle outright. -/

/-- A covering edge relation admits an edge avoiding any prescribed vertex —
there are at least four other vertices to draw the quadruple from. -/
theorem exists_edge_avoiding {vertexCount : ℕ} (hcount : 5 ≤ vertexCount)
    (edge : Fin vertexCount → Fin vertexCount → Prop)
    (hcover : ∀ quadA quadB quadC quadD : Fin vertexCount,
      quadA ≠ quadB → quadA ≠ quadC → quadA ≠ quadD →
      quadB ≠ quadC → quadB ≠ quadD → quadC ≠ quadD →
      edge quadA quadB ∨ edge quadA quadC ∨ edge quadA quadD
        ∨ edge quadB quadC ∨ edge quadB quadD ∨ edge quadC quadD) :
    ∀ excluded : Fin vertexCount, ∃ endFst endSnd : Fin vertexCount,
      endFst ≠ endSnd ∧ endFst ≠ excluded ∧ endSnd ≠ excluded ∧ edge endFst endSnd := by
  classical
  intro excluded
  have havoidCard : 4 ≤ (Finset.univ.erase excluded).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ excluded), Finset.card_univ,
      Fintype.card_fin]
    omega
  obtain ⟨avoidQuad, hquadSubset, hquadCard⟩ := Finset.exists_subset_card_eq havoidCard
  set pick : Fin 4 → Fin vertexCount :=
    fun slot => ((avoidQuad.orderIsoOfFin hquadCard) slot).val with hpickDef
  have hpickMem : ∀ slot, pick slot ∈ avoidQuad := fun slot =>
    ((avoidQuad.orderIsoOfFin hquadCard) slot).2
  have hpickNeExcluded : ∀ slot, pick slot ≠ excluded := fun slot =>
    (Finset.mem_erase.mp (hquadSubset (hpickMem slot))).1
  have hpickNe : ∀ slotLeft slotRight : Fin 4, slotLeft ≠ slotRight →
      pick slotLeft ≠ pick slotRight := fun slotLeft slotRight hslotNe hpickEq =>
    hslotNe ((avoidQuad.orderIsoOfFin hquadCard).toEquiv.injective
      (Subtype.val_injective hpickEq))
  rcases hcover (pick 0) (pick 1) (pick 2) (pick 3)
      (hpickNe 0 1 (by decide)) (hpickNe 0 2 (by decide)) (hpickNe 0 3 (by decide))
      (hpickNe 1 2 (by decide)) (hpickNe 1 3 (by decide)) (hpickNe 2 3 (by decide)) with
    hedge | hedge | hedge | hedge | hedge | hedge
  · exact ⟨pick 0, pick 1, hpickNe 0 1 (by decide), hpickNeExcluded 0,
      hpickNeExcluded 1, hedge⟩
  · exact ⟨pick 0, pick 2, hpickNe 0 2 (by decide), hpickNeExcluded 0,
      hpickNeExcluded 2, hedge⟩
  · exact ⟨pick 0, pick 3, hpickNe 0 3 (by decide), hpickNeExcluded 0,
      hpickNeExcluded 3, hedge⟩
  · exact ⟨pick 1, pick 2, hpickNe 1 2 (by decide), hpickNeExcluded 1,
      hpickNeExcluded 2, hedge⟩
  · exact ⟨pick 1, pick 3, hpickNe 1 3 (by decide), hpickNeExcluded 1,
      hpickNeExcluded 3, hedge⟩
  · exact ⟨pick 2, pick 3, hpickNe 2 3 (by decide), hpickNeExcluded 2,
      hpickNeExcluded 3, hedge⟩

/-- **Matching or triangle at every vertex count ≥ 5.**  A symmetric relation
covering every quadruple contains two disjoint edges or a full triangle — the
Gallai step at every vertex count. -/
theorem matching_or_triangle_of_coveringEdges_general {vertexCount : ℕ}
    (hcount : 5 ≤ vertexCount) (edge : Fin vertexCount → Fin vertexCount → Prop)
    (hsymm : ∀ leftIdx rightIdx, edge leftIdx rightIdx → edge rightIdx leftIdx)
    (hcover : ∀ quadA quadB quadC quadD : Fin vertexCount,
      quadA ≠ quadB → quadA ≠ quadC → quadA ≠ quadD →
      quadB ≠ quadC → quadB ≠ quadD → quadC ≠ quadD →
      edge quadA quadB ∨ edge quadA quadC ∨ edge quadA quadD
        ∨ edge quadB quadC ∨ edge quadB quadD ∨ edge quadC quadD) :
    (∃ matchAFst matchASnd matchBFst matchBSnd : Fin vertexCount,
        matchAFst ≠ matchASnd ∧ matchBFst ≠ matchBSnd
          ∧ matchAFst ≠ matchBFst ∧ matchAFst ≠ matchBSnd
          ∧ matchASnd ≠ matchBFst ∧ matchASnd ≠ matchBSnd
          ∧ edge matchAFst matchASnd ∧ edge matchBFst matchBSnd)
      ∨ (∃ triA triB triC : Fin vertexCount, triA ≠ triB ∧ triA ≠ triC ∧ triB ≠ triC
          ∧ edge triA triB ∧ edge triA triC ∧ edge triB triC) := by
  classical
  have havoiding := exists_edge_avoiding hcount edge hcover
  obtain ⟨seedFst, seedSnd, hseedNe, -, -, hseedEdge⟩ := havoiding ⟨0, by omega⟩
  by_cases hmatch : ∃ matchAFst matchASnd matchBFst matchBSnd : Fin vertexCount,
      matchAFst ≠ matchASnd ∧ matchBFst ≠ matchBSnd
        ∧ matchAFst ≠ matchBFst ∧ matchAFst ≠ matchBSnd
        ∧ matchASnd ≠ matchBFst ∧ matchASnd ≠ matchBSnd
        ∧ edge matchAFst matchASnd ∧ edge matchBFst matchBSnd
  · exact Or.inl hmatch
  -- no two disjoint edges: every edge meets the seed edge
  have hmeets : ∀ endFst endSnd : Fin vertexCount, endFst ≠ endSnd → edge endFst endSnd →
      endFst = seedFst ∨ endFst = seedSnd ∨ endSnd = seedFst ∨ endSnd = seedSnd := by
    intro endFst endSnd hendNe hendEdge
    by_contra hnone
    push Not at hnone
    obtain ⟨hfs1, hfs2, hss1, hss2⟩ := hnone
    exact hmatch ⟨seedFst, seedSnd, endFst, endSnd, hseedNe, hendNe, Ne.symm hfs1,
      Ne.symm hss1, Ne.symm hfs2, Ne.symm hss2, hseedEdge, hendEdge⟩
  -- the edge avoiding seedFst passes through seedSnd
  obtain ⟨avoidFst, avoidSnd, hane, hafs, hasf, haedge⟩ := havoiding seedFst
  have hthroughSnd : ∃ spoke : Fin vertexCount, spoke ≠ seedFst ∧ spoke ≠ seedSnd
      ∧ edge spoke seedSnd := by
    rcases hmeets avoidFst avoidSnd hane haedge with hfs | hfs | hss | hss
    · exact absurd hfs hafs
    · refine ⟨avoidSnd, hasf, ?_, ?_⟩
      · rw [← hfs]; exact (Ne.symm hane)
      · rw [← hfs]; exact hsymm _ _ haedge
    · exact absurd hss hasf
    · refine ⟨avoidFst, hafs, ?_, ?_⟩
      · rw [← hss]; exact hane
      · rw [← hss]; exact haedge
  -- the edge avoiding seedSnd passes through seedFst
  obtain ⟨avoidFst', avoidSnd', hane', hafs', hasf', haedge'⟩ := havoiding seedSnd
  have hthroughFst : ∃ spoke : Fin vertexCount, spoke ≠ seedFst ∧ spoke ≠ seedSnd
      ∧ edge spoke seedFst := by
    rcases hmeets avoidFst' avoidSnd' hane' haedge' with hfs | hfs | hss | hss
    · refine ⟨avoidSnd', ?_, hasf', ?_⟩
      · rw [← hfs]; exact (Ne.symm hane')
      · rw [← hfs]; exact hsymm _ _ haedge'
    · exact absurd hfs hafs'
    · refine ⟨avoidFst', ?_, hafs', ?_⟩
      · rw [← hss]; exact hane'
      · rw [← hss]; exact haedge'
    · exact absurd hss hasf'
  obtain ⟨spokeSnd, hspokeSndFst, hspokeSndSnd, hspokeSndEdge⟩ := hthroughSnd
  obtain ⟨spokeFst, hspokeFstFst, hspokeFstSnd, hspokeFstEdge⟩ := hthroughFst
  -- the two spokes coincide, closing the triangle
  have hspokesEq : spokeSnd = spokeFst := by
    by_contra hspokes
    exact hmatch ⟨spokeSnd, seedSnd, spokeFst, seedFst, hspokeSndSnd, hspokeFstFst,
      hspokes, hspokeSndFst, Ne.symm hspokeFstSnd, Ne.symm hseedNe,
      hspokeSndEdge, hspokeFstEdge⟩
  refine Or.inr ⟨seedFst, seedSnd, spokeSnd, hseedNe, Ne.symm hspokeSndFst,
    Ne.symm hspokeSndSnd, hseedEdge, ?_, hsymm _ _ hspokeSndEdge⟩
  rw [hspokesEq]
  exact hsymm _ _ hspokeFstEdge

/-- **At six or more vertices, a covering edge set with a triangle but no
two-edge matching is absurd**: a quadruple made of one triangle vertex and
three outsiders can carry no edge — each of its six pairs is disjoint from
some triangle edge, so any edge on it would complete a matching. -/
theorem false_of_coveringEdges_triangle_without_matching {vertexCount : ℕ}
    (hcount : 6 ≤ vertexCount) (edge : Fin vertexCount → Fin vertexCount → Prop)
    (hcover : ∀ quadA quadB quadC quadD : Fin vertexCount,
      quadA ≠ quadB → quadA ≠ quadC → quadA ≠ quadD →
      quadB ≠ quadC → quadB ≠ quadD → quadC ≠ quadD →
      edge quadA quadB ∨ edge quadA quadC ∨ edge quadA quadD
        ∨ edge quadB quadC ∨ edge quadB quadD ∨ edge quadC quadD)
    (hnoMatching : ¬ ∃ matchAFst matchASnd matchBFst matchBSnd : Fin vertexCount,
        matchAFst ≠ matchASnd ∧ matchBFst ≠ matchBSnd
          ∧ matchAFst ≠ matchBFst ∧ matchAFst ≠ matchBSnd
          ∧ matchASnd ≠ matchBFst ∧ matchASnd ≠ matchBSnd
          ∧ edge matchAFst matchASnd ∧ edge matchBFst matchBSnd)
    (triA triB triC : Fin vertexCount)
    (htriAB : triA ≠ triB) (htriAC : triA ≠ triC) (htriBC : triB ≠ triC)
    (hedgeAB : edge triA triB) (_hedgeAC : edge triA triC) (hedgeBC : edge triB triC) :
    False := by
  classical
  have htriNotFst : triA ∉ ({triB, triC} : Finset (Fin vertexCount)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro (heq | heq)
    exacts [htriAB heq, htriAC heq]
  have htriNotSnd : triB ∉ ({triC} : Finset (Fin vertexCount)) :=
    Finset.notMem_singleton.mpr htriBC
  have htriCard : ({triA, triB, triC} : Finset (Fin vertexCount)).card = 3 := by
    rw [Finset.card_insert_of_notMem htriNotFst, Finset.card_insert_of_notMem htriNotSnd,
      Finset.card_singleton]
  have houtCard : 3 ≤ (({triA, triB, triC} : Finset (Fin vertexCount))ᶜ).card := by
    rw [Finset.card_compl, Fintype.card_fin, htriCard]
    omega
  obtain ⟨outTriple, houtSubset, houtTripleCard⟩ := Finset.exists_subset_card_eq houtCard
  set pick : Fin 3 → Fin vertexCount :=
    fun slot => ((outTriple.orderIsoOfFin houtTripleCard) slot).val with hpickDef
  have hpickMem : ∀ slot, pick slot ∈ outTriple := fun slot =>
    ((outTriple.orderIsoOfFin houtTripleCard) slot).2
  have hpickNe : ∀ slotLeft slotRight : Fin 3, slotLeft ≠ slotRight →
      pick slotLeft ≠ pick slotRight := fun slotLeft slotRight hslotNe hpickEq =>
    hslotNe ((outTriple.orderIsoOfFin houtTripleCard).toEquiv.injective
      (Subtype.val_injective hpickEq))
  have hpickNeTri : ∀ slot, pick slot ≠ triA ∧ pick slot ≠ triB ∧ pick slot ≠ triC := by
    intro slot
    have hnot := Finset.mem_compl.mp (houtSubset (hpickMem slot))
    simp only [Finset.mem_insert, Finset.mem_singleton] at hnot
    push Not at hnot
    exact hnot
  rcases hcover triA (pick 0) (pick 1) (pick 2)
      (Ne.symm (hpickNeTri 0).1) (Ne.symm (hpickNeTri 1).1) (Ne.symm (hpickNeTri 2).1)
      (hpickNe 0 1 (by decide)) (hpickNe 0 2 (by decide)) (hpickNe 1 2 (by decide)) with
    hedge | hedge | hedge | hedge | hedge | hedge
  · exact hnoMatching ⟨triA, pick 0, triB, triC, Ne.symm (hpickNeTri 0).1, htriBC,
      htriAB, htriAC, (hpickNeTri 0).2.1, (hpickNeTri 0).2.2, hedge, hedgeBC⟩
  · exact hnoMatching ⟨triA, pick 1, triB, triC, Ne.symm (hpickNeTri 1).1, htriBC,
      htriAB, htriAC, (hpickNeTri 1).2.1, (hpickNeTri 1).2.2, hedge, hedgeBC⟩
  · exact hnoMatching ⟨triA, pick 2, triB, triC, Ne.symm (hpickNeTri 2).1, htriBC,
      htriAB, htriAC, (hpickNeTri 2).2.1, (hpickNeTri 2).2.2, hedge, hedgeBC⟩
  · exact hnoMatching ⟨pick 0, pick 1, triA, triB, hpickNe 0 1 (by decide), htriAB,
      (hpickNeTri 0).1, (hpickNeTri 0).2.1, (hpickNeTri 1).1, (hpickNeTri 1).2.1,
      hedge, hedgeAB⟩
  · exact hnoMatching ⟨pick 0, pick 2, triA, triB, hpickNe 0 2 (by decide), htriAB,
      (hpickNeTri 0).1, (hpickNeTri 0).2.1, (hpickNeTri 2).1, (hpickNeTri 2).2.1,
      hedge, hedgeAB⟩
  · exact hnoMatching ⟨pick 1, pick 2, triA, triB, hpickNe 1 2 (by decide), htriAB,
      (hpickNeTri 1).1, (hpickNeTri 1).2.1, (hpickNeTri 2).1, (hpickNeTri 2).2.1,
      hedge, hedgeAB⟩

/-! ## The triangle branch's forcing, stated generally, and its rank-3 killer -/

/-- **The general triangle forcing.**  A bracket-zero triangle in the dual
yields ONE dependence supported on the `rank − 1` labels OFF the triangle —
the triangle's complement is a dependent selection.  This is the general form
of what the five-coplanar argument extracted at `(5,3)`; there the rest has
TWO labels and primitivity kills it (next theorem), reaching the same
endpoint as the Parseval route by a shorter mechanism. -/
theorem exists_dependentRest_of_dualTriangle {rank : ℕ}
    (design : WeightedDesign (rank + 2) rank)
    (dualDesign : WeightedDesign (rank + 2) 2)
    (htripleDictionary : ∀ triFst triSnd triThd : Fin (rank + 2),
      pairBracket dualDesign triFst triSnd = 0 →
      pairBracket dualDesign triFst triThd = 0 →
      pairBracket dualDesign triSnd triThd = 0 →
      ∃ dependence : Fin (rank + 2) → ℝ,
        (∃ witnessLabel, dependence witnessLabel ≠ 0)
          ∧ dependence triFst = 0 ∧ dependence triSnd = 0 ∧ dependence triThd = 0
          ∧ (∑ label, dependence label • design.atom label) = 0)
    (triFst triSnd triThd : Fin (rank + 2))
    (htriNeFstSnd : triFst ≠ triSnd) (htriNeFstThd : triFst ≠ triThd)
    (htriNeSndThd : triSnd ≠ triThd)
    (hbracketFstSnd : pairBracket dualDesign triFst triSnd = 0)
    (hbracketFstThd : pairBracket dualDesign triFst triThd = 0)
    (hbracketSndThd : pairBracket dualDesign triSnd triThd = 0) :
    ∃ restSet : Finset (Fin (rank + 2)),
      restSet.card = rank - 1
        ∧ restSet = ({triFst, triSnd, triThd} : Finset (Fin (rank + 2)))ᶜ
        ∧ IsDependentSelection design restSet := by
  obtain ⟨dependence, hwitness, hdepFst, hdepSnd, hdepThd, hsum⟩ :=
    htripleDictionary triFst triSnd triThd hbracketFstSnd hbracketFstThd hbracketSndThd
  have htriNotFst : triFst ∉ ({triSnd, triThd} : Finset (Fin (rank + 2))) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro (heq | heq)
    exacts [htriNeFstSnd heq, htriNeFstThd heq]
  have htriNotSnd : triSnd ∉ ({triThd} : Finset (Fin (rank + 2))) :=
    Finset.notMem_singleton.mpr htriNeSndThd
  have htriCard : ({triFst, triSnd, triThd} : Finset (Fin (rank + 2))).card = 3 := by
    rw [Finset.card_insert_of_notMem htriNotFst, Finset.card_insert_of_notMem htriNotSnd,
      Finset.card_singleton]
  refine ⟨({triFst, triSnd, triThd} : Finset (Fin (rank + 2)))ᶜ, ?_, rfl,
    dependence, hwitness, ?_, hsum⟩
  · rw [Finset.card_compl, Fintype.card_fin, htriCard]
    omega
  · intro label hnotRest
    have hmemTriple : label ∈ ({triFst, triSnd, triThd} : Finset (Fin (rank + 2))) := by
      by_contra hnotTriple
      exact hnotRest (Finset.mem_compl.mpr hnotTriple)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmemTriple
    rcases hmemTriple with rfl | rfl | rfl
    exacts [hdepFst, hdepSnd, hdepThd]

/-- **The rank-3 triangle killer.**  At `(5,3)` the rest of a dual triangle is
a PAIR, and a dependent pair is impossible in a primitive design.  Same
endpoint as the five-coplanar/Parseval branch of
`Gtz/Ties/SpikeMatroidObstruction.lean`: a dual bracket-zero triangle cannot
exist over a primitive `(5,3)` design at all. -/
theorem no_dualTriangle_of_isPrimitive_fiveThree
    (design : WeightedDesign (3 + 2) 3) (hprimitive : IsPrimitiveDesign design)
    (dualDesign : WeightedDesign (3 + 2) 2)
    (htripleDictionary : ∀ triFst triSnd triThd : Fin (3 + 2),
      pairBracket dualDesign triFst triSnd = 0 →
      pairBracket dualDesign triFst triThd = 0 →
      pairBracket dualDesign triSnd triThd = 0 →
      ∃ dependence : Fin (3 + 2) → ℝ,
        (∃ witnessLabel, dependence witnessLabel ≠ 0)
          ∧ dependence triFst = 0 ∧ dependence triSnd = 0 ∧ dependence triThd = 0
          ∧ (∑ label, dependence label • design.atom label) = 0)
    (triFst triSnd triThd : Fin (3 + 2))
    (htriNeFstSnd : triFst ≠ triSnd) (htriNeFstThd : triFst ≠ triThd)
    (htriNeSndThd : triSnd ≠ triThd)
    (hbracketFstSnd : pairBracket dualDesign triFst triSnd = 0)
    (hbracketFstThd : pairBracket dualDesign triFst triThd = 0)
    (hbracketSndThd : pairBracket dualDesign triSnd triThd = 0) :
    False := by
  obtain ⟨restSet, hrestCard, _hrestEq, hrestDependent⟩ :=
    exists_dependentRest_of_dualTriangle design dualDesign htripleDictionary
      triFst triSnd triThd htriNeFstSnd htriNeFstThd htriNeSndThd
      hbracketFstSnd hbracketFstThd hbracketSndThd
  have hrestCardTwo : restSet.card = 2 := by omega
  exact dependentPair_impossible_of_isPrimitive (by norm_num) design hprimitive
    restSet hrestCardTwo hrestDependent

/-! ## THE HEADLINE: the shared-circuit-pair law, every rank ≥ 2 -/

/-- **THE SHARED-CIRCUIT-PAIR LAW AT CORANK-2 TIES, UNIFORMLY IN THE RANK.**
Every primitive tie at `(rank + 2, rank)`, `rank ≥ 2`, carries two dependent
rank-subsets through a `(rank − 2)`-core, jointly covering all atoms. -/
theorem sharedCircuitPairAtCorankTwoTie_holds :
    ∀ rank : ℕ, 2 ≤ rank → SharedCircuitPairAtCorankTwoTie rank := by
  intro rank hrankTwo _hrankGuard design hprimitive htie
  classical
  rcases eq_or_lt_of_le hrankTwo with hrankEqTwo | hrankGtTwo
  · -- rank = 2: no primitive (4,2) tie exists at all
    exfalso
    subst hrankEqTwo
    exact not_isTie_of_isPrimitive_fourTwo design hprimitive htie
  · -- rank ≥ 3: the tie-locked dual, then matching-or-triangle
    obtain ⟨dualDesign, hpairDictionary, htripleDictionary, hquadCover⟩ :=
      exists_tieLockedNaimarkDual rank design htie
    by_cases hmatching : ∃ matchAFst matchASnd matchBFst matchBSnd : Fin (rank + 2),
        matchAFst ≠ matchASnd ∧ matchBFst ≠ matchBSnd
          ∧ matchAFst ≠ matchBFst ∧ matchAFst ≠ matchBSnd
          ∧ matchASnd ≠ matchBFst ∧ matchASnd ≠ matchBSnd
          ∧ pairBracket dualDesign matchAFst matchASnd = 0
          ∧ pairBracket dualDesign matchBFst matchBSnd = 0
    · -- MATCHING: the shared circuit pair, by construction
      obtain ⟨matchAFst, matchASnd, matchBFst, matchBSnd, hmatchA, hmatchB, hcrossOne,
        hcrossTwo, hcrossThree, hcrossFour, hedgeA, hedgeB⟩ := hmatching
      obtain ⟨depA, hwitA, hdepAFst, hdepASnd, hsumA⟩ :=
        hpairDictionary matchAFst matchASnd hedgeA
      obtain ⟨depB, hwitB, hdepBFst, hdepBSnd, hsumB⟩ :=
        hpairDictionary matchBFst matchBSnd hedgeB
      set quadSet : Finset (Fin (rank + 2)) :=
        {matchAFst, matchASnd, matchBFst, matchBSnd} with hquadSetDef
      have hquadNotFst : matchAFst ∉ ({matchASnd, matchBFst, matchBSnd}
          : Finset (Fin (rank + 2))) := by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        rintro (heq | heq | heq)
        exacts [hmatchA heq, hcrossOne heq, hcrossTwo heq]
      have hquadNotSnd : matchASnd ∉ ({matchBFst, matchBSnd}
          : Finset (Fin (rank + 2))) := by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        rintro (heq | heq)
        exacts [hcrossThree heq, hcrossFour heq]
      have hquadNotThd : matchBFst ∉ ({matchBSnd} : Finset (Fin (rank + 2))) :=
        Finset.notMem_singleton.mpr hmatchB
      have hquadCard : quadSet.card = 4 := by
        rw [hquadSetDef, Finset.card_insert_of_notMem hquadNotFst,
          Finset.card_insert_of_notMem hquadNotSnd,
          Finset.card_insert_of_notMem hquadNotThd, Finset.card_singleton]
      have hpairOneSubQuad : ({matchAFst, matchASnd} : Finset (Fin (rank + 2)))
          ⊆ quadSet := by
        intro label hlabel
        rw [hquadSetDef]
        rcases Finset.mem_insert.mp hlabel with rfl | hmem
        · exact Finset.mem_insert_self _ _
        · rw [Finset.mem_singleton] at hmem
          subst hmem
          exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
      have hpairTwoSubQuad : ({matchBFst, matchBSnd} : Finset (Fin (rank + 2)))
          ⊆ quadSet := by
        intro label hlabel
        rw [hquadSetDef]
        rcases Finset.mem_insert.mp hlabel with rfl | hmem
        · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
            (Finset.mem_insert_self _ _))
        · rw [Finset.mem_singleton] at hmem
          subst hmem
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
            (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))
      -- the two chosen-set identities
      have hunionOne : quadSetᶜ ∪ ({matchAFst, matchASnd} : Finset (Fin (rank + 2)))
          = ({matchBFst, matchBSnd} : Finset (Fin (rank + 2)))ᶜ := by
        ext label
        simp only [Finset.mem_union, Finset.mem_compl, hquadSetDef, Finset.mem_insert,
          Finset.mem_singleton]
        constructor
        · rintro (hnotQuad | hpairMem)
          · rintro (heq | heq)
            · exact hnotQuad (Or.inr (Or.inr (Or.inl heq)))
            · exact hnotQuad (Or.inr (Or.inr (Or.inr heq)))
          · rcases hpairMem with rfl | rfl
            · rintro (heq | heq)
              · exact hcrossOne heq
              · exact hcrossTwo heq
            · rintro (heq | heq)
              · exact hcrossThree heq
              · exact hcrossFour heq
        · intro hnotPairTwo
          by_cases hinPairOne : label = matchAFst ∨ label = matchASnd
          · exact Or.inr hinPairOne
          · push Not at hinPairOne hnotPairTwo
            refine Or.inl ?_
            rintro (heq | heq | heq | heq)
            exacts [hinPairOne.1 heq, hinPairOne.2 heq, hnotPairTwo.1 heq,
              hnotPairTwo.2 heq]
      have hunionTwo : quadSetᶜ ∪ ({matchBFst, matchBSnd} : Finset (Fin (rank + 2)))
          = ({matchAFst, matchASnd} : Finset (Fin (rank + 2)))ᶜ := by
        ext label
        simp only [Finset.mem_union, Finset.mem_compl, hquadSetDef, Finset.mem_insert,
          Finset.mem_singleton]
        constructor
        · rintro (hnotQuad | hpairMem)
          · rintro (heq | heq)
            · exact hnotQuad (Or.inl heq)
            · exact hnotQuad (Or.inr (Or.inl heq))
          · rcases hpairMem with rfl | rfl
            · rintro (heq | heq)
              · exact hcrossOne heq.symm
              · exact hcrossThree heq.symm
            · rintro (heq | heq)
              · exact hcrossTwo heq.symm
              · exact hcrossFour heq.symm
        · intro hnotPairOne
          by_cases hinPairTwo : label = matchBFst ∨ label = matchBSnd
          · exact Or.inr hinPairTwo
          · push Not at hinPairTwo hnotPairOne
            refine Or.inl ?_
            rintro (heq | heq | heq | heq)
            exacts [hnotPairOne.1 heq, hnotPairOne.2 heq, hinPairTwo.1 heq,
              hinPairTwo.2 heq]
      refine ⟨quadSetᶜ, {matchAFst, matchASnd}, {matchBFst, matchBSnd},
        ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [Finset.card_compl, Fintype.card_fin, hquadCard]
        omega
      · rw [Finset.card_insert_of_notMem (Finset.notMem_singleton.mpr hmatchA),
          Finset.card_singleton]
      · rw [Finset.card_insert_of_notMem (Finset.notMem_singleton.mpr hmatchB),
          Finset.card_singleton]
      · rw [Finset.disjoint_left]
        intro label hlabelCompl hlabelPair
        exact (Finset.mem_compl.mp hlabelCompl) (hpairOneSubQuad hlabelPair)
      · rw [Finset.disjoint_left]
        intro label hlabelCompl hlabelPair
        exact (Finset.mem_compl.mp hlabelCompl) (hpairTwoSubQuad hlabelPair)
      · rw [Finset.disjoint_left]
        intro label hlabelOne hlabelTwo
        simp only [Finset.mem_insert, Finset.mem_singleton] at hlabelOne hlabelTwo
        rcases hlabelOne with rfl | rfl
        · rcases hlabelTwo with heq | heq
          · exact hcrossOne heq
          · exact hcrossTwo heq
        · rcases hlabelTwo with heq | heq
          · exact hcrossThree heq
          · exact hcrossFour heq
      · -- core ∪ pairOne dependent, through the OTHER edge's dependence
        refine ⟨depB, hwitB, ?_, hsumB⟩
        intro label hnotChosen
        rw [hunionOne] at hnotChosen
        have hmemPairTwo : label ∈ ({matchBFst, matchBSnd} : Finset (Fin (rank + 2))) := by
          by_contra hnot
          exact hnotChosen (Finset.mem_compl.mpr hnot)
        rcases Finset.mem_insert.mp hmemPairTwo with rfl | hmem
        · exact hdepBFst
        · rw [Finset.mem_singleton] at hmem
          subst hmem
          exact hdepBSnd
      · -- core ∪ pairTwo dependent, through the first edge's dependence
        refine ⟨depA, hwitA, ?_, hsumA⟩
        intro label hnotChosen
        rw [hunionTwo] at hnotChosen
        have hmemPairOne : label ∈ ({matchAFst, matchASnd} : Finset (Fin (rank + 2))) := by
          by_contra hnot
          exact hnotChosen (Finset.mem_compl.mpr hnot)
        rcases Finset.mem_insert.mp hmemPairOne with rfl | hmem
        · exact hdepAFst
        · rw [Finset.mem_singleton] at hmem
          subst hmem
          exact hdepASnd
    · -- NO MATCHING: a triangle exists, and both rank regimes refute it
      exfalso
      have htriangle := (matching_or_triangle_of_coveringEdges_general
          (by omega : 5 ≤ rank + 2)
          (fun leftIdx rightIdx => pairBracket dualDesign leftIdx rightIdx = 0)
          (fun leftIdx rightIdx => pairBracket_eq_zero_symm dualDesign leftIdx rightIdx)
          hquadCover).resolve_left hmatching
      obtain ⟨triA, triB, triC, htriAB, htriAC, htriBC,
        hedgeTriAB, hedgeTriAC, hedgeTriBC⟩ := htriangle
      rcases Nat.lt_or_ge rank 4 with hrankLtFour | hrankGeFour
      · -- rank = 3: the geometric killer on the rest pair
        have hrankEqThree : rank = 3 := by omega
        subst hrankEqThree
        exact no_dualTriangle_of_isPrimitive_fiveThree design hprimitive dualDesign
          htripleDictionary triA triB triC htriAB htriAC htriBC
          hedgeTriAB hedgeTriAC hedgeTriBC
      · -- rank ≥ 4: the matching-free triangle is combinatorially impossible
        exact false_of_coveringEdges_triangle_without_matching
          (by omega : 6 ≤ rank + 2)
          (fun leftIdx rightIdx => pairBracket dualDesign leftIdx rightIdx = 0)
          hquadCover hmatching triA triB triC htriAB htriAC htriBC
          hedgeTriAB hedgeTriAC hedgeTriBC

/-! ## Cross-check 1: the rank-3 instance reproves the `(5,3)` theorem -/

/-- From a dependent triple selection to the vanishing atom bracket — the
determinant form the `(5,3)` Prop speaks. -/
theorem atomBracket_eq_zero_of_dependentTriple (design : WeightedDesign 5 3)
    (sharedLabel offFst offSnd : Fin 5)
    (hsharedNotPair : sharedLabel ∉ ({offFst, offSnd} : Finset (Fin 5)))
    (hoffNe : offFst ≠ offSnd)
    (hdependent : IsDependentSelection design
      ({sharedLabel, offFst, offSnd} : Finset (Fin 5))) :
    atomBracket design sharedLabel offFst offSnd = 0 := by
  obtain ⟨dependence, ⟨witnessLabel, hwitnessNe⟩, hsupport, hsum⟩ := hdependent
  have hoffSupport : ∀ label ∈ (Finset.univ : Finset (Fin 5)),
      label ∉ ({sharedLabel, offFst, offSnd} : Finset (Fin 5)) →
      dependence label • design.atom label = 0 := fun label _ hnot => by
    rw [hsupport label hnot, zero_smul]
  have hcollapsed := Finset.sum_subset
    (Finset.subset_univ ({sharedLabel, offFst, offSnd} : Finset (Fin 5))) hoffSupport
  rw [hsum, Finset.sum_insert hsharedNotPair, Finset.sum_pair hoffNe] at hcollapsed
  have hvanish : dependence sharedLabel • design.atom sharedLabel
      + dependence offFst • design.atom offFst
      + dependence offSnd • design.atom offSnd = 0 := by
    rw [add_assoc]
    exact hcollapsed
  have hwitnessMem : witnessLabel ∈ ({sharedLabel, offFst, offSnd} : Finset (Fin 5)) := by
    by_contra hnot
    exact hwitnessNe (hsupport witnessLabel hnot)
  have hnontrivial : dependence sharedLabel ≠ 0 ∨ dependence offFst ≠ 0
      ∨ dependence offSnd ≠ 0 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hwitnessMem
    rcases hwitnessMem with rfl | rfl | rfl
    · exact Or.inl hwitnessNe
    · exact Or.inr (Or.inl hwitnessNe)
    · exact Or.inr (Or.inr hwitnessNe)
  show tripleBracket (design.atom sharedLabel) (design.atom offFst)
      (design.atom offSnd) = 0
  exact EndpointSpike.tripleBracket_eq_zero_of_dependence _ _ _ _ _ _
    hnontrivial hvanish

/-- **Cross-check: the `(5,3)` shared-line-pair theorem, rederived from the
uniform law** — same conclusion on the same hypotheses as
`EndpointSpike.sharedLinePairAtEveryTie_holds`. -/
theorem sharedLinePairAtEveryTieFiveThree_rederived :
    EndpointSpike.SharedLinePairAtEveryTieFiveThree := by
  intro bottomDesign hprimitive htie
  classical
  obtain ⟨core, pairOne, pairTwo, hcoreCard, hpairOneCard, hpairTwoCard,
    hdisjCoreOne, hdisjCoreTwo, hdisjPairs, hdependentOne, hdependentTwo⟩ :=
    sharedCircuitPairAtCorankTwoTie_holds 3 (by norm_num) (by norm_num)
      bottomDesign hprimitive htie
  have hcoreCardOne : core.card = 1 := by omega
  obtain ⟨sharedLabel, hcoreEq⟩ := Finset.card_eq_one.mp hcoreCardOne
  obtain ⟨oneFst, oneSnd, honeNe, hpairOneEq⟩ := Finset.card_eq_two.mp hpairOneCard
  obtain ⟨twoFst, twoSnd, htwoNe, hpairTwoEq⟩ := Finset.card_eq_two.mp hpairTwoCard
  subst hcoreEq hpairOneEq hpairTwoEq
  -- the ten distinctness facts
  have hsharedNotPairOne : sharedLabel ∉ ({oneFst, oneSnd} : Finset (Fin 5)) :=
    Finset.disjoint_left.mp hdisjCoreOne (Finset.mem_singleton_self sharedLabel)
  have hsharedNotPairTwo : sharedLabel ∉ ({twoFst, twoSnd} : Finset (Fin 5)) :=
    Finset.disjoint_left.mp hdisjCoreTwo (Finset.mem_singleton_self sharedLabel)
  have hsharedNeOne : sharedLabel ≠ oneFst ∧ sharedLabel ≠ oneSnd := by
    have hcopy := hsharedNotPairOne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hcopy
    push Not at hcopy
    exact hcopy
  have hsharedNeTwo : sharedLabel ≠ twoFst ∧ sharedLabel ≠ twoSnd := by
    have hcopy := hsharedNotPairTwo
    simp only [Finset.mem_insert, Finset.mem_singleton] at hcopy
    push Not at hcopy
    exact hcopy
  have honeFstNotPairTwo : oneFst ∉ ({twoFst, twoSnd} : Finset (Fin 5)) :=
    Finset.disjoint_left.mp hdisjPairs (Finset.mem_insert_self _ _)
  have honeSndNotPairTwo : oneSnd ∉ ({twoFst, twoSnd} : Finset (Fin 5)) :=
    Finset.disjoint_left.mp hdisjPairs
      (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  have honeFstNeTwo : oneFst ≠ twoFst ∧ oneFst ≠ twoSnd := by
    have hcopy := honeFstNotPairTwo
    simp only [Finset.mem_insert, Finset.mem_singleton] at hcopy
    push Not at hcopy
    exact hcopy
  have honeSndNeTwo : oneSnd ≠ twoFst ∧ oneSnd ≠ twoSnd := by
    have hcopy := honeSndNotPairTwo
    simp only [Finset.mem_insert, Finset.mem_singleton] at hcopy
    push Not at hcopy
    exact hcopy
  -- the two vanishing atom brackets
  have hchosenOne : ({sharedLabel} : Finset (Fin 5)) ∪ {oneFst, oneSnd}
      = ({sharedLabel, oneFst, oneSnd} : Finset (Fin 5)) :=
    Finset.singleton_union sharedLabel {oneFst, oneSnd}
  have hchosenTwo : ({sharedLabel} : Finset (Fin 5)) ∪ {twoFst, twoSnd}
      = ({sharedLabel, twoFst, twoSnd} : Finset (Fin 5)) :=
    Finset.singleton_union sharedLabel {twoFst, twoSnd}
  rw [hchosenOne] at hdependentOne
  rw [hchosenTwo] at hdependentTwo
  have hbracketOne : atomBracket bottomDesign sharedLabel oneFst oneSnd = 0 :=
    atomBracket_eq_zero_of_dependentTriple bottomDesign sharedLabel oneFst oneSnd
      hsharedNotPairOne honeNe hdependentOne
  have hbracketTwo : atomBracket bottomDesign sharedLabel twoFst twoSnd = 0 :=
    atomBracket_eq_zero_of_dependentTriple bottomDesign sharedLabel twoFst twoSnd
      hsharedNotPairTwo htwoNe hdependentTwo
  -- the relabeling permutation
  obtain ⟨hsharedNeOneFst, hsharedNeOneSnd⟩ := hsharedNeOne
  obtain ⟨hsharedNeTwoFst, hsharedNeTwoSnd⟩ := hsharedNeTwo
  obtain ⟨honeFstNeTwoFst, honeFstNeTwoSnd⟩ := honeFstNeTwo
  obtain ⟨honeSndNeTwoFst, honeSndNeTwoSnd⟩ := honeSndNeTwo
  have hsymOne := Ne.symm hsharedNeOneFst
  have hsymTwo := Ne.symm hsharedNeOneSnd
  have hsymThree := Ne.symm hsharedNeTwoFst
  have hsymFour := Ne.symm hsharedNeTwoSnd
  have hsymFive := Ne.symm honeFstNeTwoFst
  have hsymSix := Ne.symm honeFstNeTwoSnd
  have hsymSeven := Ne.symm honeSndNeTwoFst
  have hsymEight := Ne.symm honeSndNeTwoSnd
  have hsymNine := Ne.symm honeNe
  have hsymTen := Ne.symm htwoNe
  set relabelFun : Fin 5 → Fin 5 :=
    ![sharedLabel, oneFst, oneSnd, twoFst, twoSnd] with hrelabelDef
  have hrelabelInj : Function.Injective relabelFun := by
    intro relabelLeft relabelRight hvalueEq
    fin_cases relabelLeft <;> fin_cases relabelRight <;> simp_all
  refine ⟨Equiv.ofBijective relabelFun (Finite.injective_iff_bijective.mp hrelabelInj),
    ?_, ?_⟩
  · exact hbracketOne
  · exact hbracketTwo

/-! ## Cross-check 2: the rank-2 degenerate reading -/

/-- The law holds at rank 2 — vacuously, because no primitive `(4,2)` tie
exists. -/
theorem sharedCircuitPair_rankTwo_holds : SharedCircuitPairAtCorankTwoTie 2 :=
  sharedCircuitPairAtCorankTwoTie_holds 2 (by norm_num)

/-- **The degenerate reading is exact**: at rank 2 the law's conclusion (an
empty core and two disjoint dependent PAIRS) is unsatisfiable over a primitive
design — a dependent pair is a parallel pair or a zero atom.  So
`SharedCircuitPairAtCorankTwoTie 2` says precisely "no primitive `(4,2)` tie
exists", the size-four tie form of the four-direction hinge. -/
theorem sharedCircuitPair_conclusion_impossible_rankTwo
    (design : WeightedDesign 4 2) (hprimitive : IsPrimitiveDesign design) :
    ¬ ∃ core pairOne pairTwo : Finset (Fin 4),
        core.card = 0 ∧ pairOne.card = 2 ∧ pairTwo.card = 2
          ∧ Disjoint core pairOne ∧ Disjoint core pairTwo
          ∧ Disjoint pairOne pairTwo
          ∧ IsDependentSelection design (core ∪ pairOne)
          ∧ IsDependentSelection design (core ∪ pairTwo) := by
  rintro ⟨core, pairOne, pairTwo, hcoreCard, hpairOneCard, _, _, _, _,
    hdependentOne, _⟩
  have hcoreEmpty : core = ∅ := Finset.card_eq_zero.mp hcoreCard
  rw [hcoreEmpty, Finset.empty_union] at hdependentOne
  exact dependentPair_impossible_of_isPrimitive (by norm_num) design hprimitive
    pairOne hpairOneCard hdependentOne

/-! ## Cross-check 3: the diamond realizes the law -/

/-- **The diamond satisfies the law it must satisfy.**  The kernel-checked
primitive `(5,3)` tie (`Gtz.diamondDesign_isTie`; primitive via
`Gtz.not_hasParallelPair_diamondDesign`) carries a 1-core shared circuit
pair — the general statement's `rank = 3` prediction, matching the dependent
triples `{0,1,3}` and `{0,2,4}` through atom `0`. -/
theorem diamond_realizes_sharedCircuitPair :
    ∃ core pairOne pairTwo : Finset (Fin 5),
      core.card = 1 ∧ pairOne.card = 2 ∧ pairTwo.card = 2
        ∧ Disjoint core pairOne ∧ Disjoint core pairTwo
        ∧ Disjoint pairOne pairTwo
        ∧ IsDependentSelection diamondDesign (core ∪ pairOne)
        ∧ IsDependentSelection diamondDesign (core ∪ pairTwo) :=
  sharedCircuitPairAtCorankTwoTie_holds 3 (by norm_num) (by norm_num) diamondDesign
    ((isPrimitiveDesign_iff_not_hasParallelPair diamondDesign).mpr
      not_hasParallelPair_diamondDesign)
    diamondDesign_isTie

/-! ## BONUS: the corank-1 analogue — the tie matroid is the uniform circuit -/

/-- **The corank-1 law.**  Every tie at `(rank + 1, rank)`, `rank ≥ 2`, is
primitive and its direction matroid is the uniform matroid
`U(rank, rank + 1)`: every rank-subset is independent and the full ground set
is dependent — the single circuit `C_{rank+1}`, the graphic matroid of the
`(rank + 1)`-cycle.  Assembled from `Gtz.corankOne_isTie_not_parallel` and
`Gtz.corankOne_isTie_det_ne_zero` plus rank-nullity for the full
dependence. -/
theorem corankOneTie_isUniformCircuit (rank : ℕ) (hrankTwo : 2 ≤ rank)
    (design : WeightedDesign (rank + 1) rank) (htie : IsTie design) :
    IsPrimitiveDesign design
      ∧ (∀ chosen : Finset (Fin (rank + 1)), chosen.card = rank →
          ¬ IsDependentSelection design chosen)
      ∧ IsDependentSelection design Finset.univ := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro keptLabel dropLabel ratio hlabelNe
    exact corankOne_isTie_not_parallel hrankTwo design htie hlabelNe ratio
  · rintro chosen hchosenCard ⟨dependence, ⟨witnessLabel, hwitnessNe⟩, hsupport, hsum⟩
    have hdet := corankOne_isTie_det_ne_zero (by omega) design htie hchosenCard
    have hwitnessMem : witnessLabel ∈ chosen := by
      by_contra hnot
      exact hwitnessNe (hsupport witnessLabel hnot)
    obtain ⟨witnessSlot, hwitnessSlot⟩ := subsetPick_surjOn chosen hchosenCard hwitnessMem
    have hcoeffNe : (fun slot => dependence (subsetPick chosen hchosenCard slot)) ≠ 0 := by
      intro hzero
      have hslotEntry := congrFun hzero witnessSlot
      simp only [Pi.zero_apply] at hslotEntry
      rw [hwitnessSlot] at hslotEntry
      exact hwitnessNe hslotEntry
    have hvecMul : Matrix.vecMul (fun slot => dependence (subsetPick chosen hchosenCard slot))
        (subsetRowMatrix design chosen hchosenCard) = 0 := by
      funext coordIdx
      simp only [Matrix.vecMul, dotProduct, Pi.zero_apply, subsetRowMatrix,
        Matrix.of_apply]
      have hreindex : ∑ slot, dependence (subsetPick chosen hchosenCard slot)
            * design.atom (subsetPick chosen hchosenCard slot) coordIdx
          = ∑ label ∈ chosen, dependence label * design.atom label coordIdx :=
        sum_orderIsoOfFin chosen hchosenCard
          (fun label => dependence label * design.atom label coordIdx)
      have hextend : ∑ label ∈ chosen, dependence label * design.atom label coordIdx
          = ∑ label, dependence label * design.atom label coordIdx :=
        Finset.sum_subset (Finset.subset_univ chosen) (fun label _ hnot => by
          rw [hsupport label hnot, zero_mul])
      have hfromSum : ∑ label, dependence label * design.atom label coordIdx = 0 := by
        have happlied := congrFun hsum coordIdx
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
          Pi.zero_apply] at happlied
        exact happlied
      rw [hreindex, hextend, hfromSum]
    exact hdet (Matrix.exists_vecMul_eq_zero_iff.mp
      ⟨fun slot => dependence (subsetPick chosen hchosenCard slot), hcoeffNe, hvecMul⟩)
  · have hnotLin : ¬ LinearIndependent ℝ design.atom := by
      intro hlin
      have hcardLe := hlin.fintype_card_le_finrank
      rw [Fintype.card_fin] at hcardLe
      have hfinrank : Module.finrank ℝ (Fin rank → ℝ) = rank := by simp
      rw [hfinrank] at hcardLe
      omega
    obtain ⟨coeffs, hcoeffSum, ⟨liveIndex, hliveNe⟩⟩ :=
      Fintype.not_linearIndependent_iff.mp hnotLin
    exact ⟨coeffs, ⟨liveIndex, hliveNe⟩,
      fun label hnotMem => absurd (Finset.mem_univ label) hnotMem, hcoeffSum⟩

end CorankTwo
