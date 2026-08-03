/-
# The erase system in value form: the T-form edge law, rigidity, and capacity

The edge law `Gtz.sum_erasePair_weight_mul_atomPairing` reads the Parseval
identity at an off-diagonal entry.  Multiplying it by the edge pairing turns
every summand into the ORIENTED TRIPLE PRODUCT of the triple `{c, d, e}` —
the tree already exploits this in two vocabularies: the SIGN form
(`Gtz.SolvesSignedEraseSystem`, unknowns `±1` against the nonnegative
`Gtz.tripleRadius`) and the MAGNITUDE form (`Gtz.edgeStarMass`).  This module
lands the third, VALUE form: the unknown of each star slot is the signed real
`Gtz.edgeTripleValue` itself, the erase equations constrain those values, and
realness enters as torsion — at a real design every candidate value lies in
the two-point set `{T, −T}` because `|t_C| = r_C` exactly
(`Gtz.edgeTripleValue_eq_tripleParity_mul_tripleRadius`).  Over `ℂ` the
Bargmann phase is free, candidate values fill a disc, and every uniqueness
statement below fails at the shared-axis trine; the `±` clauses in the
hypotheses are exactly where the field enters.

## Contents

* the value-form edge law `Gtz.sum_erasePair_weight_mul_edgeTripleValue`
  (general size, rank three) and the torsion bridges back to the shipped
  sign-form vocabulary;
* the diagonal capacity identity `Gtz.sum_erase_weight_mul_sq_dotProduct`
  (general size AND rank): the weighted squared pairings through one atom
  resolve its leverage times one minus its share;
* OWN-ANCHORED RIGIDITY: `Gtz.eq_of_sum_eq_of_flipSubsetSums_ne_zero` — a
  competing `±`-reading of one equation differs from the reference reading on
  a set whose PLAIN subset-sum must vanish, so nonvanishing of all plain
  subset-sums pins the reading.  This strengthens the shipped difference
  principle `Gtz.sum_disagreement_eq_zero_of_solvesSame`, which cancels the
  disagreement set but kills it only when it is a singleton
  (`Gtz.disagreement_ne_singleton_of_pos`); here EVERY nonempty flip set is
  excluded at once.  The two-sided variant
  `Gtz.eq_of_sum_eq_of_signedSubsetSums_ne_zero` needs SIGNED subset-sums and
  pins any two readings to each other;
* per-edge and global design rigidity (`Gtz.eraseConsistent_edge_eq_own`,
  `Gtz.eraseConsistentAssignment_eq_own`): at a design with nonvanishing flip
  subset-sums the design's own triple values are the ONLY erase-consistent
  reading.  Global rigidity is pointwise from per-edge because every triple
  lies inside an edge star.  Compare `Gtz.HasRigidSignedEraseSystem`, the
  sign-form rigidity predicate: the icosahedron refutes rigidity globally
  (`Gtz.solvesSignedEraseSystem_neg_tripleParity_icosaDesign`), and indeed
  every icosahedral erase right-hand side vanishes, so its FULL stars are
  vanishing flip sets and no icosahedral edge is flip-clean;
* SHARPNESS (`Gtz.exists_flipped_edge_reading`): a vanishing flip subset-sum
  hands back a second reading solving the same edge with the flip set read
  negated — so the flip-clean hypothesis of rigidity is exact, not merely
  sufficient.  Existence of a solving `±1` sign pattern at every edge is the
  shipped `Gtz.solvesSignedEraseSystem_tripleParity` and is not restated;
* THE CAPACITY LEMMA `Gtz.exists_nonneg_edgeTripleValue_of_boxDeficit`: a
  box-deficit at an edge — the free star slots cannot absorb the requirement
  plus the forced mass — forbids the all-negative reading of the forced
  slots.  Nothing but the value-form law, weight positivity, and one triangle
  bound; no genericity, no heaviness, no failure hypothesis;
* UNIFORM-STAR SIGN LEMMAS: a strictly light edge with nonzero pairing has a
  strictly positive star value (`Gtz.exists_pos_edgeTripleValue_of_lightEdge`)
  and a strictly heavy one has a strictly negative star value
  (`Gtz.exists_neg_edgeTripleValue_of_heavyEdge`).  These sharpen the shipped
  saturated-edge lemmas `Gtz.atomShare_add_atomShare_lt_one_of_coherentEdge`
  and `Gtz.one_lt_atomShare_add_atomShare_of_incoherentEdge`: the hypothesis
  shrinks from all pairings nonzero at size six to the ONE edge pairing
  nonzero at every size, and the conclusion is a value, not a parity;
* THE MATCHING BOTH-SIGNS THEOREM
  (`Gtz.exists_pos_and_neg_edgeTripleValue_of_matching`): the shares of three
  disjoint covering parts sum to the rank
  (`Gtz.sum_atomShare_of_three_part_cover`), so at `(6,3)` a perfect matching
  with strict edges carries a strictly light AND a strictly heavy edge, hence
  a positive AND a negative star value through matching edges.  The cell
  `(6,3)` is exactly critical here: `rank = size/2` blocks the all-light and
  the all-heavy matching simultaneously.  Link-vocabulary twins at size six:
  `Gtz.coherentMatching_eq_false`, `Gtz.incoherentMatching_eq_false`;
* THE PARITY NO-GO `Gtz.isEdgeCoboundary_const_one`: the all-plus triple
  pattern is an edge coboundary, i.e. a genuine two-graph.  Any GF(2)-parity
  functional vanishing on all two-graphs therefore vanishes on the all-plus
  pattern, so no parity invariant separates candidate minus-sets — the
  formal kill of the parity route (its census twin: the two-graph code
  contains the zero word, hence its dual code is even);
* THE FLIP DEGENERACY POLYNOMIAL (`Gtz.edgeFlipDegeneracyPoly`,
  `Gtz.flipDegeneracyPoly`) with exact evaluation brackets
  (`Gtz.eval_edgeFlipDegeneracyPoly_ne_zero_iff`,
  `Gtz.eval_flipDegeneracyPoly_ne_zero_iff`): flip-cleanliness is the
  nonvanishing of one polynomial in the packed design parameters, so the
  flip-dirty locus dissolves through the genericity template at the price of
  one witness evaluation.  The template application
  `Gtz.gtzWeighted_of_forall_generic_flipClean_dominates` carries that
  witness evaluation as an EXPLICIT HYPOTHESIS: it is a finite rational
  computation, measured true externally (all `15 × 15` plain flip
  subset-sums nonzero at `Gtz.genericWitnessDesign`, gtz-p3 exact-arithmetic
  run over `619` designs with zero generic violations), and NOT yet
  kernel-checked.  No margin is manufactured anywhere: genericity narrows
  quantifiers only.

Provenance: gtz-p3 land-substrate; the rigidity chain and the capacity lemma
were compiled first as free-standing probes by the derive-rigidity and
derive-farkas lanes and are transcribed here against the same anchors.
-/
import Mathlib
import Gtz.Quantitative.TwoGraphRepresentability
import Gtz.Reduction.ShareBudgetLifting
import Gtz.Reduction.GenericityReduction

namespace Gtz

open Matrix

variable {sizeIndex rank : ℕ}

/-! ## The value-form vocabulary and the torsion bridges -/

/-- The **edge-relative triple value** `T_abx = p_ab · p_ax · p_xb`: the signed
real each star slot of the erase system carries.  Its magnitude is the shipped
`Gtz.tripleRadius` and its sign the shipped `Gtz.tripleParity` — realness IS
the statement that only the two values `±r` occur, which is the torsion bridge
`Gtz.edgeTripleValue_eq_tripleParity_mul_tripleRadius`. -/
noncomputable def edgeTripleValue (D : WeightedDesign sizeIndex 3)
    (edgeFirst edgeSecond other : Fin sizeIndex) : ℝ :=
  atomPairing D edgeFirst edgeSecond * atomPairing D edgeFirst other
    * atomPairing D other edgeSecond

/-- **The torsion bridge**: the value is the parity times the radius.  This is
`Gtz.tripleParity_mul_tripleRadius` read in the edge orientation, and it is
where realness enters every statement of this module: over `ℂ` the left side
would carry a free Bargmann phase and only satisfy `|t| ≤ r`. -/
theorem edgeTripleValue_eq_tripleParity_mul_tripleRadius
    (D : WeightedDesign sizeIndex 3) (edgeFirst edgeSecond other : Fin sizeIndex) :
    edgeTripleValue D edgeFirst edgeSecond other
      = tripleParity D edgeFirst edgeSecond other
        * tripleRadius D edgeFirst edgeSecond other := by
  rw [tripleParity_mul_tripleRadius]
  simp only [edgeTripleValue, atomPairing_comm D other edgeSecond]

/-- The radius bridge: the absolute value of the edge triple value is the
shipped `Gtz.tripleRadius`. -/
theorem abs_edgeTripleValue (D : WeightedDesign sizeIndex 3)
    (edgeFirst edgeSecond other : Fin sizeIndex) :
    |edgeTripleValue D edgeFirst edgeSecond other|
      = tripleRadius D edgeFirst edgeSecond other := by
  simp only [edgeTripleValue, tripleRadius]
  congr 1
  rw [atomPairing_comm D other edgeSecond]

/-! ## The value-form edge law -/

/-- **THE T-FORM ERASE LAW** (general size, rank three): the shipped edge law
`Gtz.sum_erasePair_weight_mul_atomPairing` times the edge pairing.  Every
summand becomes the oriented triple value of `{a, b, x}`, and the right-hand
side becomes the squared edge pairing times the share gap `1 − s_a − s_b`.
The sign-form twin is `Gtz.solvesSignedEraseSystem_tripleParity`. -/
theorem sum_erasePair_weight_mul_edgeTripleValue (D : WeightedDesign sizeIndex 3)
    {edgeFirst edgeSecond : Fin sizeIndex} (hedge : edgeFirst ≠ edgeSecond) :
    ∑ other ∈ (Finset.univ.erase edgeFirst).erase edgeSecond,
        D.weight other * edgeTripleValue D edgeFirst edgeSecond other
      = atomPairing D edgeFirst edgeSecond ^ 2
        * (1 - atomShare D edgeFirst - atomShare D edgeSecond) := by
  have hterm : ∀ other : Fin sizeIndex,
      D.weight other * edgeTripleValue D edgeFirst edgeSecond other
        = atomPairing D edgeFirst edgeSecond
          * (D.weight other * (atomPairing D edgeFirst other
            * atomPairing D other edgeSecond)) := by
    intro other
    simp only [edgeTripleValue]
    ring
  rw [Finset.sum_congr rfl fun other _ => hterm other, ← Finset.mul_sum,
    sum_erasePair_weight_mul_atomPairing D hedge]
  ring

/-! ## The diagonal capacity identity -/

/-- **THE DIAGONAL BUDGET** (general size and rank): the weighted squared
pairings of the other atoms through one atom resolve its leverage times one
minus its share.  This is the shipped Parseval row law
`Gtz.sum_weight_mul_sq_dotProduct` probed at the atom itself, with the
diagonal term peeled off — the per-atom capacity every erase-magnitude
argument prices against. -/
theorem sum_erase_weight_mul_sq_dotProduct (D : WeightedDesign sizeIndex rank)
    (atomIndex : Fin sizeIndex) :
    ∑ other ∈ Finset.univ.erase atomIndex,
        D.weight other * (D.atom other ⬝ᵥ D.atom atomIndex) ^ 2
      = leverageOf (D.atom atomIndex) * (1 - atomShare D atomIndex) := by
  have hfull := sum_weight_mul_sq_dotProduct D (D.atom atomIndex)
  have hself : D.atom atomIndex ⬝ᵥ D.atom atomIndex
      = leverageOf (D.atom atomIndex) := dotProduct_self_eq_sum_sq _
  have hsplit := Finset.add_sum_erase (Finset.univ : Finset (Fin sizeIndex))
    (fun other => D.weight other * (D.atom other ⬝ᵥ D.atom atomIndex) ^ 2)
    (Finset.mem_univ atomIndex)
  rw [hfull, hself] at hsplit
  have herase : ∑ other ∈ Finset.univ.erase atomIndex,
      D.weight other * (D.atom other ⬝ᵥ D.atom atomIndex) ^ 2
      = leverageOf (D.atom atomIndex)
        - D.weight atomIndex * leverageOf (D.atom atomIndex) ^ 2 := by
    linarith [hsplit]
  rw [herase, atomShare]
  ring

/-- The rank-three reading of the diagonal budget, in pairing vocabulary:
`∑_{x ≠ a} t_x · p_ax² = ℓ_a (1 − s_a)`. -/
theorem sum_erase_weight_mul_atomPairing_sq (D : WeightedDesign sizeIndex 3)
    (atomIndex : Fin sizeIndex) :
    ∑ other ∈ Finset.univ.erase atomIndex,
        D.weight other * atomPairing D other atomIndex ^ 2
      = leverageOf (D.atom atomIndex) * (1 - atomShare D atomIndex) :=
  sum_erase_weight_mul_sq_dotProduct D atomIndex

/-! ## Own-anchored uniqueness: the abstract rigidity lemmas

The KEY simplification of the value form: uniqueness AGAINST THE CANONICAL
SOLUTION needs only PLAIN subset-sums of the signed coefficients to be
nonvanishing — no sign symmetrization and no square roots, because the
reference solution comes free from the edge law and a competing reading
differs from it exactly on a flip set whose plain sum must cancel. -/

/-- **OWN-ANCHORED UNIQUENESS.**  If no nonempty subset of the star has
vanishing plain coefficient sum, then any `±`-valued reading matching the
reference sum IS the reference reading.  The flip set of a competing reading
carries `∑ 2·coefficient = 0`, and one member witnesses nonemptiness. -/
theorem eq_of_sum_eq_of_flipSubsetSums_ne_zero {indexType : Type*}
    [DecidableEq indexType] (star : Finset indexType)
    (coefficient candidate : indexType → ℝ)
    (hclean : ∀ flipSet ⊆ star, flipSet.Nonempty →
      ∑ member ∈ flipSet, coefficient member ≠ 0)
    (hplusminus : ∀ member ∈ star,
      candidate member = coefficient member
        ∨ candidate member = -coefficient member)
    (hsum : ∑ member ∈ star, candidate member
      = ∑ member ∈ star, coefficient member) :
    ∀ member ∈ star, candidate member = coefficient member := by
  classical
  set flipSet := star.filter fun member => candidate member ≠ coefficient member
    with hflipSetDef
  have hflipSubset : flipSet ⊆ star := Finset.filter_subset _ _
  have hdiffZero : ∑ member ∈ star, (coefficient member - candidate member) = 0 := by
    rw [Finset.sum_sub_distrib, hsum, sub_self]
  have hsplit := Finset.sum_filter_add_sum_filter_not star
    (fun member => candidate member ≠ coefficient member)
    (fun member => coefficient member - candidate member)
  have hrestZero : ∑ member ∈ star.filter
      (fun member => ¬ candidate member ≠ coefficient member),
      (coefficient member - candidate member) = 0 :=
    Finset.sum_eq_zero fun member hmember => by
      rw [not_not.mp (Finset.mem_filter.mp hmember).2, sub_self]
  have hflipDiff : ∑ member ∈ flipSet, (coefficient member - candidate member) = 0 := by
    rw [← hflipSetDef] at hsplit
    rw [hrestZero, add_zero] at hsplit
    rw [hsplit, hdiffZero]
  have hflipDouble : ∑ member ∈ flipSet, (coefficient member - candidate member)
      = 2 * ∑ member ∈ flipSet, coefficient member := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun member hmember => ?_
    rcases hplusminus member (hflipSubset hmember) with heq | hneg
    · exact absurd heq (Finset.mem_filter.mp hmember).2
    · rw [hneg]; ring
  have hflipSumZero : ∑ member ∈ flipSet, coefficient member = 0 := by
    have htwo : 2 * ∑ member ∈ flipSet, coefficient member = 0 := by
      rw [← hflipDouble, hflipDiff]
    linarith
  intro member hmember
  by_contra hne
  exact hclean flipSet hflipSubset
    ⟨member, Finset.mem_filter.mpr ⟨hmember, hne⟩⟩ hflipSumZero

/-- **TWO-SIDED UNIQUENESS** (the measured `|V_e| = 1` statement): if no
nonempty subset of the star carries a vanishing SIGNED subset-sum, then any
two `±`-valued readings with equal sums agree.  The signed hypothesis is
strictly stronger than the plain one; the plain form suffices for the
pipeline because the design's own reading anchors one side. -/
theorem eq_of_sum_eq_of_signedSubsetSums_ne_zero {indexType : Type*}
    [DecidableEq indexType] (star : Finset indexType)
    (coefficient candidateFirst candidateSecond : indexType → ℝ)
    (hclean : ∀ flipSet ⊆ star, flipSet.Nonempty →
      ∀ signVector : indexType → ℝ,
        (∀ member ∈ flipSet, signVector member = 1 ∨ signVector member = -1) →
        ∑ member ∈ flipSet, signVector member * coefficient member ≠ 0)
    (hfirst : ∀ member ∈ star,
      candidateFirst member = coefficient member
        ∨ candidateFirst member = -coefficient member)
    (hsecond : ∀ member ∈ star,
      candidateSecond member = coefficient member
        ∨ candidateSecond member = -coefficient member)
    (hsum : ∑ member ∈ star, candidateFirst member
      = ∑ member ∈ star, candidateSecond member) :
    ∀ member ∈ star, candidateFirst member = candidateSecond member := by
  classical
  set flipSet := star.filter
    fun member => candidateFirst member ≠ candidateSecond member
    with hflipSetDef
  have hflipSubset : flipSet ⊆ star := Finset.filter_subset _ _
  set signVector : indexType → ℝ := fun member =>
    if candidateFirst member = coefficient member then (1 : ℝ) else -1
    with hsignDef
  have hdiffZero : ∑ member ∈ star,
      (candidateFirst member - candidateSecond member) = 0 := by
    rw [Finset.sum_sub_distrib, hsum, sub_self]
  have hsplit := Finset.sum_filter_add_sum_filter_not star
    (fun member => candidateFirst member ≠ candidateSecond member)
    (fun member => candidateFirst member - candidateSecond member)
  have hrestZero : ∑ member ∈ star.filter
      (fun member => ¬ candidateFirst member ≠ candidateSecond member),
      (candidateFirst member - candidateSecond member) = 0 :=
    Finset.sum_eq_zero fun member hmember => by
      rw [not_not.mp (Finset.mem_filter.mp hmember).2, sub_self]
  have hflipDiff : ∑ member ∈ flipSet,
      (candidateFirst member - candidateSecond member) = 0 := by
    rw [← hflipSetDef] at hsplit
    rw [hrestZero, add_zero] at hsplit
    rw [hsplit, hdiffZero]
  have hflipDouble : ∑ member ∈ flipSet,
      (candidateFirst member - candidateSecond member)
      = 2 * ∑ member ∈ flipSet, signVector member * coefficient member := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun member hmember => ?_
    have hne := (Finset.mem_filter.mp hmember).2
    have hmemberStar := hflipSubset hmember
    rcases hfirst member hmemberStar with hfirstEq | hfirstNeg
    · have hsecondNeg : candidateSecond member = -coefficient member := by
        rcases hsecond member hmemberStar with hsecondEq | hsecondNeg
        · exact absurd (hfirstEq.trans hsecondEq.symm) hne
        · exact hsecondNeg
      rw [hfirstEq, hsecondNeg, hsignDef]
      simp only [if_pos hfirstEq]
      ring
    · have hsecondEq : candidateSecond member = coefficient member := by
        rcases hsecond member hmemberStar with hsecondEq | hsecondNeg
        · exact hsecondEq
        · exact absurd (hfirstNeg.trans hsecondNeg.symm) hne
      have hcoeffNe : coefficient member ≠ 0 := fun hzero => hne (by
        rw [hfirstNeg, hsecondEq, hzero, neg_zero])
      have hfirstNe : candidateFirst member ≠ coefficient member := fun heq =>
        hcoeffNe (by
          have := heq.symm.trans hfirstNeg
          linarith [this])
      rw [hfirstNeg, hsecondEq, hsignDef]
      simp only [if_neg hfirstNe]
      ring
  intro member hmember
  by_contra hne
  refine hclean flipSet hflipSubset
    ⟨member, Finset.mem_filter.mpr ⟨hmember, hne⟩⟩ signVector
    (fun other _ => ?_) ?_
  · rw [hsignDef]
    by_cases hcase : candidateFirst other = coefficient other
    · exact Or.inl (if_pos hcase)
    · exact Or.inr (if_neg hcase)
  · have htwo : 2 * ∑ other ∈ flipSet, signVector other * coefficient other = 0 := by
      rw [← hflipDouble, hflipDiff]
    linarith

/-! ## Flip-cleanliness and design-level rigidity -/

/-- The per-edge flip-cleanliness hypothesis: no nonempty subset of the edge
star has vanishing plain sum of erase coefficients `t_x · T_abx`.  Sufficient
for own-anchored rigidity (`Gtz.eraseConsistent_edge_eq_own`) and exact:
`Gtz.exists_flipped_edge_reading` builds a second solving reading from any
vanishing flip subset-sum. -/
def EdgeFlipClean (D : WeightedDesign sizeIndex 3)
    (edgeFirst edgeSecond : Fin sizeIndex) : Prop :=
  ∀ flipSet ⊆ (Finset.univ.erase edgeFirst).erase edgeSecond, flipSet.Nonempty →
    ∑ other ∈ flipSet,
      D.weight other * edgeTripleValue D edgeFirst edgeSecond other ≠ 0

/-- Every edge flip-clean.  Measured externally (gtz-p3): zero violations at
`619` exact generic designs; every violation found sits on a special shipped
design — the icosahedron, whose erase right-hand sides all vanish, violates
it at every edge through the FULL star. -/
def AllEdgesFlipClean (D : WeightedDesign sizeIndex 3) : Prop :=
  ∀ edgeFirst edgeSecond : Fin sizeIndex, edgeFirst ≠ edgeSecond →
    EdgeFlipClean D edgeFirst edgeSecond

/-- **PER-EDGE RIGIDITY**: at a flip-clean edge, any `±`-valued reading of the
star triple values satisfying the edge's erase equation IS the design's own
reading.  Weight positivity cancels the coefficients pointwise. -/
theorem eraseConsistent_edge_eq_own (D : WeightedDesign sizeIndex 3)
    {edgeFirst edgeSecond : Fin sizeIndex} (hedge : edgeFirst ≠ edgeSecond)
    (hclean : EdgeFlipClean D edgeFirst edgeSecond)
    (tripleValue : Fin sizeIndex → ℝ)
    (hplusminus : ∀ other ∈ (Finset.univ.erase edgeFirst).erase edgeSecond,
      tripleValue other = edgeTripleValue D edgeFirst edgeSecond other
        ∨ tripleValue other = -edgeTripleValue D edgeFirst edgeSecond other)
    (hsolve : ∑ other ∈ (Finset.univ.erase edgeFirst).erase edgeSecond,
        D.weight other * tripleValue other
      = atomPairing D edgeFirst edgeSecond ^ 2
        * (1 - atomShare D edgeFirst - atomShare D edgeSecond)) :
    ∀ other ∈ (Finset.univ.erase edgeFirst).erase edgeSecond,
      tripleValue other = edgeTripleValue D edgeFirst edgeSecond other := by
  intro other hother
  have hpointwise := eq_of_sum_eq_of_flipSubsetSums_ne_zero
    ((Finset.univ.erase edgeFirst).erase edgeSecond)
    (fun member => D.weight member * edgeTripleValue D edgeFirst edgeSecond member)
    (fun member => D.weight member * tripleValue member)
    hclean
    (fun member hmember => by
      rcases hplusminus member hmember with heq | hneg
      · exact Or.inl (by rw [heq])
      · exact Or.inr (by rw [hneg]; ring))
    (by rw [hsolve, sum_erasePair_weight_mul_edgeTripleValue D hedge])
    other hother
  exact mul_left_cancel₀ (D.weight_pos other).ne' hpointwise

/-- An **erase-consistent assignment**: a `±edgeTripleValue`-valued reading of
every (edge, star-member) slot satisfying every erase equation.  This is the
UNSYMMETRIZED (finer) CSP object: the true sign CSP assigns one sign per
unordered triple and factors through the symmetric special case, so
uniqueness here covers it.  The sign-form twin quantified over `±1` patterns
is `Gtz.SolvesSignedEraseSystem` together with `Gtz.IsParityFlip`. -/
def IsEraseConsistentAssignment (D : WeightedDesign sizeIndex 3)
    (assignment : Fin sizeIndex → Fin sizeIndex → Fin sizeIndex → ℝ) : Prop :=
  (∀ edgeFirst edgeSecond other : Fin sizeIndex,
      assignment edgeFirst edgeSecond other
          = edgeTripleValue D edgeFirst edgeSecond other
        ∨ assignment edgeFirst edgeSecond other
          = -edgeTripleValue D edgeFirst edgeSecond other)
    ∧ ∀ edgeFirst edgeSecond : Fin sizeIndex, edgeFirst ≠ edgeSecond →
        ∑ other ∈ (Finset.univ.erase edgeFirst).erase edgeSecond,
          D.weight other * assignment edgeFirst edgeSecond other
        = atomPairing D edgeFirst edgeSecond ^ 2
          * (1 - atomShare D edgeFirst - atomShare D edgeSecond)

/-- The design's own triple values form an erase-consistent assignment: the
`±` clause is the left disjunct, the equations are the value-form edge law. -/
theorem own_isEraseConsistentAssignment (D : WeightedDesign sizeIndex 3) :
    IsEraseConsistentAssignment D (fun edgeFirst edgeSecond other =>
      edgeTripleValue D edgeFirst edgeSecond other) :=
  ⟨fun _ _ _ => Or.inl rfl,
   fun _ _ hedge => sum_erasePair_weight_mul_edgeTripleValue D hedge⟩

/-- **GLOBAL RIGIDITY**: at a design with every edge flip-clean, the design's
own triple values are the ONLY erase-consistent assignment.  Pointwise from
per-edge rigidity — every slot lies inside an edge star, so no connectivity
argument over star overlaps is needed. -/
theorem eraseConsistentAssignment_eq_own (D : WeightedDesign sizeIndex 3)
    (hclean : AllEdgesFlipClean D)
    (assignment : Fin sizeIndex → Fin sizeIndex → Fin sizeIndex → ℝ)
    (hconsistent : IsEraseConsistentAssignment D assignment) :
    ∀ edgeFirst edgeSecond other : Fin sizeIndex, edgeFirst ≠ edgeSecond →
      other ∈ (Finset.univ.erase edgeFirst).erase edgeSecond →
      assignment edgeFirst edgeSecond other
        = edgeTripleValue D edgeFirst edgeSecond other := by
  intro edgeFirst edgeSecond other hedge hother
  exact eraseConsistent_edge_eq_own D hedge (hclean edgeFirst edgeSecond hedge)
    (assignment edgeFirst edgeSecond)
    (fun member _ => hconsistent.1 edgeFirst edgeSecond member)
    (hconsistent.2 edgeFirst edgeSecond hedge) other hother

/-! ## Sharpness: a vanishing flip subset-sum builds a second reading -/

/-- **SHARPNESS OF FLIP-CLEANLINESS.**  A vanishing plain flip subset-sum
hands back a reading that solves the same edge equation with the flip set
read NEGATED.  Whenever some flip member has nonzero triple value, this
reading differs from the design's own — so the hypothesis of
`Gtz.eraseConsistent_edge_eq_own` is exact.  (When every flip member's value
vanishes, the negated reading coincides with the own reading pointwise and
uniqueness is untouched; the singleton subset-sum already forced those
values to zero.) -/
theorem exists_flipped_edge_reading (D : WeightedDesign sizeIndex 3)
    {edgeFirst edgeSecond : Fin sizeIndex} (hedge : edgeFirst ≠ edgeSecond)
    {flipSet : Finset (Fin sizeIndex)}
    (hsubset : flipSet ⊆ (Finset.univ.erase edgeFirst).erase edgeSecond)
    (hvanish : ∑ other ∈ flipSet,
      D.weight other * edgeTripleValue D edgeFirst edgeSecond other = 0) :
    ∃ tripleValue : Fin sizeIndex → ℝ,
      (∀ other ∈ (Finset.univ.erase edgeFirst).erase edgeSecond,
        tripleValue other = edgeTripleValue D edgeFirst edgeSecond other
          ∨ tripleValue other = -edgeTripleValue D edgeFirst edgeSecond other)
      ∧ ∑ other ∈ (Finset.univ.erase edgeFirst).erase edgeSecond,
            D.weight other * tripleValue other
          = atomPairing D edgeFirst edgeSecond ^ 2
            * (1 - atomShare D edgeFirst - atomShare D edgeSecond)
      ∧ ∀ other ∈ flipSet,
          tripleValue other = -edgeTripleValue D edgeFirst edgeSecond other := by
  classical
  refine ⟨fun other => if other ∈ flipSet
      then -edgeTripleValue D edgeFirst edgeSecond other
      else edgeTripleValue D edgeFirst edgeSecond other, ?_, ?_, ?_⟩
  · intro other _
    by_cases hmember : other ∈ flipSet
    · refine Or.inr ?_
      show (if other ∈ flipSet then -edgeTripleValue D edgeFirst edgeSecond other
          else edgeTripleValue D edgeFirst edgeSecond other)
        = -edgeTripleValue D edgeFirst edgeSecond other
      rw [if_pos hmember]
    · refine Or.inl ?_
      show (if other ∈ flipSet then -edgeTripleValue D edgeFirst edgeSecond other
          else edgeTripleValue D edgeFirst edgeSecond other)
        = edgeTripleValue D edgeFirst edgeSecond other
      rw [if_neg hmember]
  · show ∑ other ∈ (Finset.univ.erase edgeFirst).erase edgeSecond,
        D.weight other * (if other ∈ flipSet
          then -edgeTripleValue D edgeFirst edgeSecond other
          else edgeTripleValue D edgeFirst edgeSecond other)
      = atomPairing D edgeFirst edgeSecond ^ 2
        * (1 - atomShare D edgeFirst - atomShare D edgeSecond)
    have hsplitFlipped : ∑ other ∈ ((Finset.univ.erase edgeFirst).erase edgeSecond)
          \ flipSet,
          D.weight other * (if other ∈ flipSet
            then -edgeTripleValue D edgeFirst edgeSecond other
            else edgeTripleValue D edgeFirst edgeSecond other)
        + ∑ other ∈ flipSet,
            D.weight other * (if other ∈ flipSet
              then -edgeTripleValue D edgeFirst edgeSecond other
              else edgeTripleValue D edgeFirst edgeSecond other)
        = ∑ other ∈ (Finset.univ.erase edgeFirst).erase edgeSecond,
            D.weight other * (if other ∈ flipSet
              then -edgeTripleValue D edgeFirst edgeSecond other
              else edgeTripleValue D edgeFirst edgeSecond other) :=
      Finset.sum_sdiff hsubset
    have hsplitOwn : ∑ other ∈ ((Finset.univ.erase edgeFirst).erase edgeSecond)
          \ flipSet,
          D.weight other * edgeTripleValue D edgeFirst edgeSecond other
        + ∑ other ∈ flipSet,
            D.weight other * edgeTripleValue D edgeFirst edgeSecond other
        = ∑ other ∈ (Finset.univ.erase edgeFirst).erase edgeSecond,
            D.weight other * edgeTripleValue D edgeFirst edgeSecond other :=
      Finset.sum_sdiff hsubset
    have hflipPart : ∑ other ∈ flipSet,
        D.weight other * (if other ∈ flipSet
          then -edgeTripleValue D edgeFirst edgeSecond other
          else edgeTripleValue D edgeFirst edgeSecond other) = 0 := by
      have hcongr : ∀ other ∈ flipSet,
          D.weight other * (if other ∈ flipSet
            then -edgeTripleValue D edgeFirst edgeSecond other
            else edgeTripleValue D edgeFirst edgeSecond other)
          = -(D.weight other * edgeTripleValue D edgeFirst edgeSecond other) :=
        fun other hother => by rw [if_pos hother]; ring
      rw [Finset.sum_congr rfl hcongr, Finset.sum_neg_distrib, hvanish, neg_zero]
    have hrestPart : ∑ other ∈ ((Finset.univ.erase edgeFirst).erase edgeSecond)
          \ flipSet,
          D.weight other * (if other ∈ flipSet
            then -edgeTripleValue D edgeFirst edgeSecond other
            else edgeTripleValue D edgeFirst edgeSecond other)
        = ∑ other ∈ ((Finset.univ.erase edgeFirst).erase edgeSecond) \ flipSet,
            D.weight other * edgeTripleValue D edgeFirst edgeSecond other :=
      Finset.sum_congr rfl fun other hother => by
        rw [if_neg (Finset.mem_sdiff.mp hother).2]
    rw [← hsplitFlipped, hflipPart, add_zero, hrestPart,
      ← sum_erasePair_weight_mul_edgeTripleValue D hedge, ← hsplitOwn, hvanish,
      add_zero]
  · intro other hother
    show (if other ∈ flipSet then -edgeTripleValue D edgeFirst edgeSecond other
        else edgeTripleValue D edgeFirst edgeSecond other)
      = -edgeTripleValue D edgeFirst edgeSecond other
    rw [if_pos hother]

/-! ## The capacity lemma -/

/-- **THE CAPACITY LEMMA.**  A box-deficit at an edge — the free star slots'
total mass is strictly less than the erase requirement plus the forced
slots' mass — forbids the all-negative reading of the forced slots: some
forced slot carries a nonnegative triple value.  Nothing but the value-form
edge law, weight positivity, and one triangle bound; the forced subset is
abstract, and there is no genericity, heaviness, exceptionality, or failure
hypothesis.  Realness enters through the law itself: the design's own values
solve it, which pins the equation value inside the box `±∑ t·r` — over `ℂ`
there is no such pinning and the trine sits strictly inside the box. -/
theorem exists_nonneg_edgeTripleValue_of_boxDeficit (D : WeightedDesign sizeIndex 3)
    {edgeFirst edgeSecond : Fin sizeIndex} (hedge : edgeFirst ≠ edgeSecond)
    (forcedStar : Finset (Fin sizeIndex))
    (hsubset : forcedStar ⊆ (Finset.univ.erase edgeFirst).erase edgeSecond)
    (hdeficit :
      ∑ other ∈ ((Finset.univ.erase edgeFirst).erase edgeSecond) \ forcedStar,
          D.weight other * |edgeTripleValue D edgeFirst edgeSecond other|
        < atomPairing D edgeFirst edgeSecond ^ 2
              * (1 - atomShare D edgeFirst - atomShare D edgeSecond)
          + ∑ other ∈ forcedStar,
              D.weight other * |edgeTripleValue D edgeFirst edgeSecond other|) :
    ∃ other ∈ forcedStar,
      0 ≤ edgeTripleValue D edgeFirst edgeSecond other := by
  by_contra hall
  push Not at hall
  have hsplit :
      ∑ other ∈ ((Finset.univ.erase edgeFirst).erase edgeSecond) \ forcedStar,
          D.weight other * edgeTripleValue D edgeFirst edgeSecond other
        + ∑ other ∈ forcedStar,
            D.weight other * edgeTripleValue D edgeFirst edgeSecond other
      = ∑ other ∈ (Finset.univ.erase edgeFirst).erase edgeSecond,
          D.weight other * edgeTripleValue D edgeFirst edgeSecond other :=
    Finset.sum_sdiff hsubset
  have hlaw := sum_erasePair_weight_mul_edgeTripleValue D hedge
  have hfreeBound :
      ∑ other ∈ ((Finset.univ.erase edgeFirst).erase edgeSecond) \ forcedStar,
          D.weight other * edgeTripleValue D edgeFirst edgeSecond other
        ≤ ∑ other ∈ ((Finset.univ.erase edgeFirst).erase edgeSecond)
              \ forcedStar,
            D.weight other * |edgeTripleValue D edgeFirst edgeSecond other| :=
    Finset.sum_le_sum fun other _ =>
      mul_le_mul_of_nonneg_left (le_abs_self _) (D.weight_pos other).le
  have hforcedPairZero :
      ∑ other ∈ forcedStar,
          (D.weight other * edgeTripleValue D edgeFirst edgeSecond other
            + D.weight other
                * |edgeTripleValue D edgeFirst edgeSecond other|) = 0 :=
    Finset.sum_eq_zero fun other hother => by
      rw [abs_of_neg (hall other hother)]
      ring
  have hforcedSum :
      ∑ other ∈ forcedStar,
          D.weight other * edgeTripleValue D edgeFirst edgeSecond other
        + ∑ other ∈ forcedStar,
            D.weight other * |edgeTripleValue D edgeFirst edgeSecond other|
      = 0 := by
    rw [← Finset.sum_add_distrib]
    exact hforcedPairZero
  linarith

/-! ## Uniform-star sign lemmas and the matching both-signs theorem -/

/-- **THE LIGHT-EDGE SIGN LEMMA**: a strictly light edge with nonzero pairing
has a strictly positive triple value in its star — the erase right-hand side
is strictly positive and some summand must carry it.  Sharpens the shipped
`Gtz.one_lt_atomShare_add_atomShare_of_incoherentEdge` contrapositive: the
hypothesis is the ONE edge pairing at every size, not all pairings at size
six, and the conclusion is a value, not a parity.  The strictness and the
nonzero pairing are both necessary: the icosahedron has every edge share-sum
exactly one and refutes the conclusion at every edge. -/
theorem exists_pos_edgeTripleValue_of_lightEdge (D : WeightedDesign sizeIndex 3)
    {edgeFirst edgeSecond : Fin sizeIndex} (hedge : edgeFirst ≠ edgeSecond)
    (hpairing : atomPairing D edgeFirst edgeSecond ≠ 0)
    (hlight : atomShare D edgeFirst + atomShare D edgeSecond < 1) :
    ∃ other ∈ (Finset.univ.erase edgeFirst).erase edgeSecond,
      0 < edgeTripleValue D edgeFirst edgeSecond other := by
  by_contra hall
  push Not at hall
  have hsumNonpos : ∑ other ∈ (Finset.univ.erase edgeFirst).erase edgeSecond,
      D.weight other * edgeTripleValue D edgeFirst edgeSecond other ≤ 0 :=
    Finset.sum_nonpos fun other hother =>
      mul_nonpos_of_nonneg_of_nonpos (D.weight_pos other).le (hall other hother)
  have hrhsPos : 0 < atomPairing D edgeFirst edgeSecond ^ 2
      * (1 - atomShare D edgeFirst - atomShare D edgeSecond) := by
    have hsq : 0 < atomPairing D edgeFirst edgeSecond ^ 2 := by positivity
    have hgap : 0 < 1 - atomShare D edgeFirst - atomShare D edgeSecond := by
      linarith
    exact mul_pos hsq hgap
  rw [sum_erasePair_weight_mul_edgeTripleValue D hedge] at hsumNonpos
  linarith

/-- **THE HEAVY-EDGE SIGN LEMMA**: a strictly heavy edge with nonzero pairing
has a strictly negative triple value in its star.  Mirror of
`Gtz.exists_pos_edgeTripleValue_of_lightEdge`; sharpens the shipped
`Gtz.atomShare_add_atomShare_lt_one_of_coherentEdge` contrapositive the same
way. -/
theorem exists_neg_edgeTripleValue_of_heavyEdge (D : WeightedDesign sizeIndex 3)
    {edgeFirst edgeSecond : Fin sizeIndex} (hedge : edgeFirst ≠ edgeSecond)
    (hpairing : atomPairing D edgeFirst edgeSecond ≠ 0)
    (hheavy : 1 < atomShare D edgeFirst + atomShare D edgeSecond) :
    ∃ other ∈ (Finset.univ.erase edgeFirst).erase edgeSecond,
      edgeTripleValue D edgeFirst edgeSecond other < 0 := by
  by_contra hall
  push Not at hall
  have hsumNonneg : 0 ≤ ∑ other ∈ (Finset.univ.erase edgeFirst).erase edgeSecond,
      D.weight other * edgeTripleValue D edgeFirst edgeSecond other :=
    Finset.sum_nonneg fun other hother =>
      mul_nonneg (D.weight_pos other).le (hall other hother)
  have hrhsNeg : atomPairing D edgeFirst edgeSecond ^ 2
      * (1 - atomShare D edgeFirst - atomShare D edgeSecond) < 0 := by
    have hsq : 0 < atomPairing D edgeFirst edgeSecond ^ 2 := by positivity
    have hgap : 1 - atomShare D edgeFirst - atomShare D edgeSecond < 0 := by
      linarith
    exact mul_neg_of_pos_of_neg hsq hgap
  rw [sum_erasePair_weight_mul_edgeTripleValue D hedge] at hsumNonneg
  linarith

/-- The shares of three pairwise-disjoint covering parts sum to the rank —
the shipped trace normalization `Gtz.sum_atomShare_eq_rank` split along a
three-part cover.  General size and rank. -/
theorem sum_atomShare_of_three_part_cover (D : WeightedDesign sizeIndex rank)
    {partOne partTwo partThree : Finset (Fin sizeIndex)}
    (hdisjointOneTwo : Disjoint partOne partTwo)
    (hdisjointOneThree : Disjoint partOne partThree)
    (hdisjointTwoThree : Disjoint partTwo partThree)
    (hcover : partOne ∪ partTwo ∪ partThree = Finset.univ) :
    (∑ atomIndex ∈ partOne, atomShare D atomIndex)
      + (∑ atomIndex ∈ partTwo, atomShare D atomIndex)
      + (∑ atomIndex ∈ partThree, atomShare D atomIndex) = (rank : ℝ) := by
  have hdisjointUnion : Disjoint (partOne ∪ partTwo) partThree :=
    Finset.disjoint_union_left.mpr ⟨hdisjointOneThree, hdisjointTwoThree⟩
  calc (∑ atomIndex ∈ partOne, atomShare D atomIndex)
        + (∑ atomIndex ∈ partTwo, atomShare D atomIndex)
        + (∑ atomIndex ∈ partThree, atomShare D atomIndex)
      = ∑ atomIndex ∈ partOne ∪ partTwo ∪ partThree, atomShare D atomIndex := by
        rw [Finset.sum_union hdisjointUnion, Finset.sum_union hdisjointOneTwo]
    _ = ∑ atomIndex, atomShare D atomIndex := by rw [hcover]
    _ = (rank : ℝ) := sum_atomShare_eq_rank D

/-- **THE MATCHING BOTH-SIGNS THEOREM** at `(6,3)`.  A perfect matching whose
three edges carry nonzero pairings and strict share-sums has a strictly
positive triple value through some matching edge AND a strictly negative one
through some matching edge: the three share-sums total exactly the rank
`3 = 6/2`, so they cannot all sit strictly below `1` nor all strictly above
`1`, and the uniform-star sign lemmas fire on a light and on a heavy edge.
The cell `(6,3)` is exactly critical — `rank = size/2` blocks the all-light
and the all-heavy matching SIMULTANEOUSLY; at any other ratio one side would
survive.  Link-vocabulary twins killing the two uniform matchings at size
six: `Gtz.coherentMatching_eq_false`, `Gtz.incoherentMatching_eq_false`.
Strictness comes free on generic designs (`Gtz.IsGenericDesign` clauses one
and three supply both hypothesis families). -/
theorem exists_pos_and_neg_edgeTripleValue_of_matching (D : WeightedDesign 6 3)
    {matchAtomOne matchAtomTwo matchAtomThree matchAtomFour
      matchAtomFive matchAtomSix : Fin 6}
    (hpairOne : matchAtomOne ≠ matchAtomTwo)
    (hpairTwo : matchAtomThree ≠ matchAtomFour)
    (hpairThree : matchAtomFive ≠ matchAtomSix)
    (hdisjointOneTwo : Disjoint ({matchAtomOne, matchAtomTwo} : Finset (Fin 6))
      {matchAtomThree, matchAtomFour})
    (hdisjointOneThree : Disjoint ({matchAtomOne, matchAtomTwo} : Finset (Fin 6))
      {matchAtomFive, matchAtomSix})
    (hdisjointTwoThree : Disjoint ({matchAtomThree, matchAtomFour} : Finset (Fin 6))
      {matchAtomFive, matchAtomSix})
    (hcover : ({matchAtomOne, matchAtomTwo} ∪ {matchAtomThree, matchAtomFour}
      ∪ {matchAtomFive, matchAtomSix} : Finset (Fin 6)) = Finset.univ)
    (hpairingOne : atomPairing D matchAtomOne matchAtomTwo ≠ 0)
    (hpairingTwo : atomPairing D matchAtomThree matchAtomFour ≠ 0)
    (hpairingThree : atomPairing D matchAtomFive matchAtomSix ≠ 0)
    (hstrictOne : atomShare D matchAtomOne + atomShare D matchAtomTwo ≠ 1)
    (hstrictTwo : atomShare D matchAtomThree + atomShare D matchAtomFour ≠ 1)
    (hstrictThree : atomShare D matchAtomFive + atomShare D matchAtomSix ≠ 1) :
    ((∃ other ∈ (Finset.univ.erase matchAtomOne).erase matchAtomTwo,
        0 < edgeTripleValue D matchAtomOne matchAtomTwo other)
      ∨ (∃ other ∈ (Finset.univ.erase matchAtomThree).erase matchAtomFour,
          0 < edgeTripleValue D matchAtomThree matchAtomFour other)
      ∨ (∃ other ∈ (Finset.univ.erase matchAtomFive).erase matchAtomSix,
          0 < edgeTripleValue D matchAtomFive matchAtomSix other))
    ∧ ((∃ other ∈ (Finset.univ.erase matchAtomOne).erase matchAtomTwo,
        edgeTripleValue D matchAtomOne matchAtomTwo other < 0)
      ∨ (∃ other ∈ (Finset.univ.erase matchAtomThree).erase matchAtomFour,
          edgeTripleValue D matchAtomThree matchAtomFour other < 0)
      ∨ (∃ other ∈ (Finset.univ.erase matchAtomFive).erase matchAtomSix,
          edgeTripleValue D matchAtomFive matchAtomSix other < 0)) := by
  have hshareSum : (atomShare D matchAtomOne + atomShare D matchAtomTwo)
      + (atomShare D matchAtomThree + atomShare D matchAtomFour)
      + (atomShare D matchAtomFive + atomShare D matchAtomSix) = 3 := by
    have hpartOne : ∑ atomIndex ∈ ({matchAtomOne, matchAtomTwo} : Finset (Fin 6)),
        atomShare D atomIndex = atomShare D matchAtomOne + atomShare D matchAtomTwo :=
      Finset.sum_pair hpairOne
    have hpartTwo : ∑ atomIndex ∈ ({matchAtomThree, matchAtomFour} : Finset (Fin 6)),
        atomShare D atomIndex
          = atomShare D matchAtomThree + atomShare D matchAtomFour :=
      Finset.sum_pair hpairTwo
    have hpartThree : ∑ atomIndex ∈ ({matchAtomFive, matchAtomSix} : Finset (Fin 6)),
        atomShare D atomIndex
          = atomShare D matchAtomFive + atomShare D matchAtomSix :=
      Finset.sum_pair hpairThree
    have hcoverSum := sum_atomShare_of_three_part_cover D hdisjointOneTwo
      hdisjointOneThree hdisjointTwoThree hcover
    rw [hpartOne, hpartTwo, hpartThree] at hcoverSum
    rw [hcoverSum]
    norm_num
  constructor
  · -- some matching edge is strictly light
    have hlight : atomShare D matchAtomOne + atomShare D matchAtomTwo < 1
        ∨ atomShare D matchAtomThree + atomShare D matchAtomFour < 1
        ∨ atomShare D matchAtomFive + atomShare D matchAtomSix < 1 := by
      by_contra hnone
      push Not at hnone
      obtain ⟨honeGe, htwoGe, hthreeGe⟩ := hnone
      have honeGt := lt_of_le_of_ne honeGe (Ne.symm hstrictOne)
      have htwoGt := lt_of_le_of_ne htwoGe (Ne.symm hstrictTwo)
      have hthreeGt := lt_of_le_of_ne hthreeGe (Ne.symm hstrictThree)
      linarith
    rcases hlight with hlightEdge | hlightEdge | hlightEdge
    · exact Or.inl (exists_pos_edgeTripleValue_of_lightEdge D hpairOne
        hpairingOne hlightEdge)
    · exact Or.inr (Or.inl (exists_pos_edgeTripleValue_of_lightEdge D hpairTwo
        hpairingTwo hlightEdge))
    · exact Or.inr (Or.inr (exists_pos_edgeTripleValue_of_lightEdge D hpairThree
        hpairingThree hlightEdge))
  · -- some matching edge is strictly heavy
    have hheavy : 1 < atomShare D matchAtomOne + atomShare D matchAtomTwo
        ∨ 1 < atomShare D matchAtomThree + atomShare D matchAtomFour
        ∨ 1 < atomShare D matchAtomFive + atomShare D matchAtomSix := by
      by_contra hnone
      push Not at hnone
      obtain ⟨honeLe, htwoLe, hthreeLe⟩ := hnone
      have honeLt := lt_of_le_of_ne honeLe hstrictOne
      have htwoLt := lt_of_le_of_ne htwoLe hstrictTwo
      have hthreeLt := lt_of_le_of_ne hthreeLe hstrictThree
      linarith
    rcases hheavy with hheavyEdge | hheavyEdge | hheavyEdge
    · exact Or.inl (exists_neg_edgeTripleValue_of_heavyEdge D hpairOne
        hpairingOne hheavyEdge)
    · exact Or.inr (Or.inl (exists_neg_edgeTripleValue_of_heavyEdge D hpairTwo
        hpairingTwo hheavyEdge))
    · exact Or.inr (Or.inr (exists_neg_edgeTripleValue_of_heavyEdge D hpairThree
        hpairingThree hheavyEdge))

/-! ## The parity no-go -/

/-- **THE PARITY NO-GO.**  The all-plus triple pattern is an edge coboundary
— the two-graph of the all-plus edge signing.  Consequence: the realized
two-graph patterns contain the pattern with EMPTY minus set, so no GF(2)
parity functional that vanishes on all two-graphs can obstruct a candidate
minus-set; the parity route to excluding forced-minus patterns is dead.
This is the design-free half; the design side is the shipped
`Gtz.isEdgeCoboundary_tripleParity`. -/
theorem isEdgeCoboundary_const_one :
    IsEdgeCoboundary (fun _ _ _ => (1 : ℝ) :
      Fin sizeIndex → Fin sizeIndex → Fin sizeIndex → ℝ) := by
  refine ⟨fun _ _ => 1, fun _ _ => rfl, fun _ _ => Or.inl rfl, fun _ => rfl,
    fun _ _ _ => ?_⟩
  norm_num

/-! ## The flip degeneracy polynomial -/

/-- The per-edge flip degeneracy polynomial: the product of the plain flip
subset-sums of the cleared triple-product polynomials over all nonempty
subsets of the edge star.  At a design it evaluates to
`(t_a t_b)^(2^|star| − 1) · ∏_S (∑_{x ∈ S} t_x T_abx)`, so its nonvanishing
is EXACTLY flip-cleanliness (`Gtz.eval_edgeFlipDegeneracyPoly_ne_zero_iff`).
No symmetrization is needed: own-anchored rigidity consumes SIGNED
coefficients, and the weight prefactor is positive. -/
noncomputable def edgeFlipDegeneracyPoly (edgeFirst edgeSecond : Fin sizeIndex) :
    MvPolynomial (FrameParamIndex sizeIndex 3) ℝ :=
  ∏ flipSet ∈ ((Finset.univ.erase edgeFirst).erase edgeSecond).powerset.erase ∅,
    ∑ other ∈ flipSet, clearedTripleProductPoly 3 edgeFirst edgeSecond other

/-- The per-flip-set evaluation bridge: the cleared subset-sum evaluates to
the true flip subset-sum times the positive prefactor `t_a t_b`. -/
theorem eval_flipSubsetSum_designParamsOf (D : WeightedDesign sizeIndex 3)
    (edgeFirst edgeSecond : Fin sizeIndex) (flipSet : Finset (Fin sizeIndex)) :
    MvPolynomial.eval (designParamsOf D)
        (∑ other ∈ flipSet, clearedTripleProductPoly 3 edgeFirst edgeSecond other)
      = D.weight edgeFirst * D.weight edgeSecond
        * ∑ other ∈ flipSet,
            D.weight other * edgeTripleValue D edgeFirst edgeSecond other := by
  rw [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun other _ => ?_
  rw [eval_clearedTripleProductPoly_designParamsOf]
  simp only [edgeTripleValue, atomPairing_comm D other edgeSecond]
  ring

/-- The per-edge evaluation bracket: the flip degeneracy polynomial is
nonzero at a design's packed parameters exactly when the edge is
flip-clean. -/
theorem eval_edgeFlipDegeneracyPoly_ne_zero_iff (D : WeightedDesign sizeIndex 3)
    (edgeFirst edgeSecond : Fin sizeIndex) :
    MvPolynomial.eval (designParamsOf D)
        (edgeFlipDegeneracyPoly edgeFirst edgeSecond) ≠ 0
      ↔ EdgeFlipClean D edgeFirst edgeSecond := by
  rw [edgeFlipDegeneracyPoly, map_prod, Finset.prod_ne_zero_iff]
  constructor
  · intro hall flipSet hsubset hnonempty
    have hmember : flipSet
        ∈ ((Finset.univ.erase edgeFirst).erase edgeSecond).powerset.erase ∅ :=
      Finset.mem_erase.mpr ⟨Finset.nonempty_iff_ne_empty.mp hnonempty,
        Finset.mem_powerset.mpr hsubset⟩
    have hfactor := hall flipSet hmember
    rw [eval_flipSubsetSum_designParamsOf] at hfactor
    intro hzero
    rw [hzero, mul_zero] at hfactor
    exact hfactor rfl
  · intro hclean flipSet hmember
    obtain ⟨hnonemptyNe, hpowerset⟩ := Finset.mem_erase.mp hmember
    rw [eval_flipSubsetSum_designParamsOf]
    exact mul_ne_zero
      (mul_ne_zero (D.weight_pos edgeFirst).ne' (D.weight_pos edgeSecond).ne')
      (hclean flipSet (Finset.mem_powerset.mp hpowerset)
        (Finset.nonempty_iff_ne_empty.mpr hnonemptyNe))

/-- The full flip degeneracy polynomial over all ordered edges of the `(6,3)`
cell. -/
noncomputable def flipDegeneracyPoly : MvPolynomial (FrameParamIndex 6 3) ℝ :=
  ∏ orderedPair ∈ (Finset.univ : Finset (Fin 6)).offDiag,
    edgeFlipDegeneracyPoly orderedPair.1 orderedPair.2

/-- The global evaluation bracket: the full flip degeneracy polynomial is
nonzero at a design's packed parameters exactly when every edge is
flip-clean. -/
theorem eval_flipDegeneracyPoly_ne_zero_iff (D : WeightedDesign 6 3) :
    MvPolynomial.eval (designParamsOf D) flipDegeneracyPoly ≠ 0
      ↔ AllEdgesFlipClean D := by
  rw [flipDegeneracyPoly, map_prod, Finset.prod_ne_zero_iff]
  constructor
  · intro hall edgeFirst edgeSecond hedge
    exact (eval_edgeFlipDegeneracyPoly_ne_zero_iff D edgeFirst edgeSecond).mp
      (hall (edgeFirst, edgeSecond) (Finset.mem_offDiag.mpr
        ⟨Finset.mem_univ _, Finset.mem_univ _, hedge⟩))
  · intro hclean orderedPair hmember
    exact (eval_edgeFlipDegeneracyPoly_ne_zero_iff D orderedPair.1 orderedPair.2).mpr
      (hclean orderedPair.1 orderedPair.2 (Finset.mem_offDiag.mp hmember).2.2)

/-- **THE AVOIDANCE-TEMPLATE APPLICATION.**  To prove the open cell it
suffices to dominate the GENERIC FLIP-CLEAN all-heavy designs — the
flip-dirty locus dissolves by one polynomial multiplication through
`Gtz.gtzWeighted_of_forall_avoiding_dominates`, exactly as the zero-pairing
branch did.

The witness evaluation `hwitnessFlip` is carried as an EXPLICIT HYPOTHESIS,
per the residue-reduction precedent for conditional statements: it is a
closed finite rational computation (`30` ordered edges, `15` nonempty flip
subsets each, at the shipped `Gtz.genericWitnessDesign`), measured true by
exact arithmetic externally (gtz-p3), and NOT yet kernel-checked.
Discharging it upgrades this theorem to an unconditional sibling of
`Gtz.gtzWeighted_of_forall_generic_dominates`.  Scope honesty: genericity
and flip-cleanliness narrow quantifiers only; no margin is manufactured. -/
theorem gtzWeighted_of_forall_generic_flipClean_dominates
    (hwitnessFlip : MvPolynomial.eval (designParamsOf genericWitnessDesign)
      flipDegeneracyPoly ≠ 0)
    (hclose : ∀ D : WeightedDesign 6 3, AllHeavy D → IsGenericDesign D →
      AllEdgesFlipClean D →
      ∃ C : Finset (Fin 6), C.card = 3 ∧ Dominates D C) :
    GtzWeighted 6 3 := by
  apply gtzWeighted_of_forall_avoiding_dominates
    (genericBundlePoly 6 * flipDegeneracyPoly) genericWitnessDesign
    ((eval_designParamsOf_mul_ne_zero_iff genericWitnessDesign
        (genericBundlePoly 6) flipDegeneracyPoly).mpr
      ⟨eval_genericBundlePoly_genericWitnessDesign_ne_zero, hwitnessFlip⟩)
  intro D hheavy havoid
  obtain ⟨hbundle, hflip⟩ := (eval_designParamsOf_mul_ne_zero_iff D
    (genericBundlePoly 6) flipDegeneracyPoly).mp havoid
  exact hclose D hheavy ((eval_genericBundlePoly_ne_zero_iff D).mp hbundle)
    ((eval_flipDegeneracyPoly_ne_zero_iff D).mp hflip)

end Gtz
