/-
# Branch B: domination is ONE determinant, and the kill needs NO selection rule

Branch B is the region where every atom is heavy and every pair is admissible.
`Gtz.not_admissiblePair_of_parallel_of_heavy` makes it the region carrying NO
parallel pair, so the branch-B emptiness statement is exactly the case of the
hinge in which the hinge's conclusion has no witness to point at.

This module does two things to that statement, and the second is the point.

## 1. Inside branch B the Sylvester criterion collapses to its top minor

Strict domination of a triple is three polynomial inequalities: the leverage
excess, the pair minor, the gap determinant
(`Gtz.subsetSum_posDef_iff_pairVocabulary`).  **Branch B supplies the first two
by hypothesis, for every atom and every pair at once.**  So on branch B

  **`T` dominates strictly  ⟺  `0 < tripleGapDet T`**

(`Gtz.branchB_posDef_iff_gapDet_pos`).  The general caveat that a positive
determinant is not domination — true, and measured on dead triples — simply
does not apply here: branch B is precisely the hypothesis that removes it.

## 2. The existential loses its selection rule

A branch-B tie says all `C(m,3)` determinants are nonpositive, and the
contradiction needed is existential: SOME triple dominates.  Three separate
campaign fronts have failed to find a scalar rule naming that triple, and the
banked doctrine is that a sum over the family destroys the design — proved, for
the weighted aggregate, by `Gtz.weighted_aggregate_design_blind`.

The landed `Gtz.exists_pos_of_prod_sub_nonpos` exhibits a positive member of a
family while naming none.  Fed with the collapse above it gives, for ANY finite
family of triples and ANY `t > 0`,

  **`∏ (t − tripleGapDet) ≤ 0`  on branch B  ⟹  `¬ IsTie`**

(`Gtz.branchB_not_isTie_of_prod_nonpos`).  One product, no selector, and the
family is arbitrary.

The criterion is LOSSLESS: at a branch-B tie every such product is at least
`t ^ card` (`Gtz.branchB_isTie_prod_ge`), so nothing is given away by asking for
the product instead of the disjunction.  The product is therefore the
aggregation that survives exactly where the sum provably cannot — the weighted
sum of gap determinants is design-blind by `Gtz.weighted_aggregate_design_blind`,
and this product is not.

**The probe is not free, and this is a producer rather than a closing form.**
`∏(t − φ) ≤ 0` holds exactly on `t ∈ (second largest φ, largest φ]`, and those
windows are data-dependent — measured disjoint across instances by three orders
of magnitude, with every scaled probe `t = c·S` tried so far infeasible.  So the
device converts a disjunction over MEMBERS into an existential over PROBES.  Use
it to produce a dominator from any convenient `t`; do not expect one polynomial
inequality to close the branch.

## 3. The same kill in the hinge's own currency

The landed currency bridge `Gtz.sq_tripleBracket_eq_gapDet_add_pairMinors` reads
the squared bracket as the gap determinant plus the three pair minors plus the
three leverage excesses plus one.  Substituting the branch-B collapse turns
domination into a statement with no determinant in it at all:

  **`T` dominates strictly  ⟺  `Σ q_ij + Σ x_i + 1 < [abc]²`**

(`Gtz.branchB_posDef_iff_bracket_sq_gt`), so a branch-B tie forces the reverse
inequality at every one of its `C(m,3)` triples simultaneously
(`Gtz.branchB_isTie_bracket_sq_le`).  Bracket, pair minor and leverage excess
are exactly the three currencies the hinge, admissibility and heaviness are
stated in, so this is the branch-B obstruction written where the hinge can read
it.

## What this does not do

It does not close branch B, and branch B is not the hinge.  A tie with no
parallel pair need not lie in branch B — it may carry a light atom, or an
inadmissible pair that is not parallel — so the step from an inadmissible pair
to a parallel pair remains open and is owned by no lane.

[MEASURED, and recorded because it corrects the lane's own tooling: a descent on
`max_T λmin(S_T)` whitened through an explicit adjugate inverse returns `F ≈
−6·10¹⁴` with NEGATIVE leverages.  A leverage is a sum of squares, so the tool
was wrong, not the mathematics — the optimiser drives the moment matrix singular
and the inverse manufactures the minimum.  Cholesky whitening plus the Parseval
assertion `Σ t_c ℓ_c = 3` rejects those points.  Both fixtures then read
correctly: the primitive diamond at `F = 1` is saturated and lies IN branch B
with `min q = +0.75`, and the split diamond at `F = 1` is saturated, has
`min q = −3` on its two spine copies, and is NOT in branch B.]
-/
import Gtz.Wave.TripleSumSizeLaw
import Gtz.Wave.OppositeHornSelect
import Gtz.Wave.KOneWedgeProducer
import Gtz.Wave.CornerGatewayBudget

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

open Matrix

variable {m : ℕ}

/-! ## 1. On a live triple the criterion is its determinant -/

/-- **A LIVE TRIPLE DOMINATES EXACTLY WHEN ITS DETERMINANT IS POSITIVE.**
Liveness is the first two Sylvester minors, so only the third is left to
decide. -/
theorem liveTriple_posDef_iff_gapDet_pos (D : WeightedDesign m 3)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hlive : LiveTriple D x y z) :
    (subsetSum D ({x, y, z} : Finset (Fin m)) - 1).PosDef
      ↔ 0 < tripleGapDet (D.atom x) (D.atom y) (D.atom z) := by
  rw [subsetSum_posDef_iff_pairVocabulary D x y z hxy hxz hyz]
  obtain ⟨hhx, -, -, hxy', -, -⟩ := hlive
  constructor
  · rintro ⟨-, -, h⟩; exact h
  · intro h
    exact ⟨by rw [HeavyAtom] at hhx; linarith, hxy', h⟩

/-- **THE BRANCH-B COLLAPSE.**  In branch B strict domination of any triple of
distinct labels is the single inequality `0 < tripleGapDet`. -/
theorem branchB_posDef_iff_gapDet_pos (D : WeightedDesign m 3) (hB : BranchB D)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    (subsetSum D ({x, y, z} : Finset (Fin m)) - 1).PosDef
      ↔ 0 < tripleGapDet (D.atom x) (D.atom y) (D.atom z) :=
  liveTriple_posDef_iff_gapDet_pos D hxy hxz hyz (liveTriple_of_branchB hB hxy hxz hyz)

/-- A triple of distinct labels has a three-element index set. -/
theorem card_triple {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ({x, y, z} : Finset (Fin m)).card = 3 := by
  rw [Finset.card_insert_of_notMem (by simp [hxy, hxz]),
    Finset.card_insert_of_notMem (by simp [hyz]), Finset.card_singleton]

/-! ## 2. The collapse in bracket, pair-minor and leverage currency -/

/-- **BRANCH-B DOMINATION WITH NO DETERMINANT IN IT.**  The currency bridge
replaces the gap determinant by the squared bracket less the pair minors, the
leverage excesses and one, so on branch B a triple dominates exactly when its
squared bracket beats that total.

Every quantity here is a currency the hinge already speaks: the bracket is what
a parallel pair kills, the pair minors are admissibility, the leverage excesses
are heaviness. -/
theorem branchB_posDef_iff_bracket_sq_gt (D : WeightedDesign m 3) (hB : BranchB D)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    (subsetSum D ({x, y, z} : Finset (Fin m)) - 1).PosDef
      ↔ (pairGapMinor (D.atom x) (D.atom y) + pairGapMinor (D.atom x) (D.atom z)
            + pairGapMinor (D.atom y) (D.atom z))
          + ((leverageOf (D.atom x) - 1) + (leverageOf (D.atom y) - 1)
            + (leverageOf (D.atom z) - 1)) + 1
        < tripleBracket (D.atom x) (D.atom y) (D.atom z) ^ 2 := by
  rw [branchB_posDef_iff_gapDet_pos D hB hxy hxz hyz,
    sq_tripleBracket_eq_gapDet_add_pairMinors]
  constructor <;> intro h <;> linarith

/-! ## 3. One positive determinant refutes the tie -/

/-- **A POSITIVE DETERMINANT ON BRANCH B REFUTES THE TIE.**  No selection rule
is needed to USE the witness — only to find it, and the next section removes
even that. -/
theorem branchB_not_isTie_of_gapDet_pos (D : WeightedDesign m 3) (hB : BranchB D)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hdet : 0 < tripleGapDet (D.atom x) (D.atom y) (D.atom z)) :
    ¬ IsTie D := by
  intro htie
  exact htie.2 ({x, y, z} : Finset (Fin m)) (card_triple hxy hxz hyz)
    ((branchB_posDef_iff_gapDet_pos D hB hxy hxz hyz).mpr hdet)

/-- **AT A BRANCH-B TIE EVERY DETERMINANT IS NONPOSITIVE.**  The converse
reading, and the source of the losslessness below. -/
theorem branchB_isTie_gapDet_nonpos (D : WeightedDesign m 3) (hB : BranchB D)
    (htie : IsTie D) {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    tripleGapDet (D.atom x) (D.atom y) (D.atom z) ≤ 0 := by
  by_contra hcon
  push_neg at hcon
  exact branchB_not_isTie_of_gapDet_pos D hB hxy hxz hyz hcon htie

/-- **THE BRANCH-B TIE, IN THE HINGE'S CURRENCY.**  Twenty simultaneous
inequalities at size six, each saying that a triple's squared bracket does not
beat its own admissibility and heaviness data. -/
theorem branchB_isTie_bracket_sq_le (D : WeightedDesign m 3) (hB : BranchB D)
    (htie : IsTie D) {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    tripleBracket (D.atom x) (D.atom y) (D.atom z) ^ 2
      ≤ (pairGapMinor (D.atom x) (D.atom y) + pairGapMinor (D.atom x) (D.atom z)
          + pairGapMinor (D.atom y) (D.atom z))
        + ((leverageOf (D.atom x) - 1) + (leverageOf (D.atom y) - 1)
          + (leverageOf (D.atom z) - 1)) + 1 := by
  have hdet := branchB_isTie_gapDet_nonpos D hB htie hxy hxz hyz
  have hbridge := sq_tripleBracket_eq_gapDet_add_pairMinors
    (D.atom x) (D.atom y) (D.atom z)
  linarith

/-! ## 4. The selection-free kill -/

/-- **THE BRANCH-B KILL WITHOUT A SELECTION RULE.**  For an arbitrary finite
family of triples, indexed however is convenient, and an arbitrary strictly
positive probe `t`, a nonpositive product refutes the tie.

The product exhibits a triple with positive determinant without naming one, the
branch-B collapse turns that triple into a strict dominator, and a tie has
none.  The family is arbitrary, so a two-element family gives a degree-six
target rather than the degree-sixty target of the full twenty. -/
theorem branchB_not_isTie_of_prod_nonpos {ι : Type*} {s : Finset ι}
    (D : WeightedDesign m 3) (hB : BranchB D)
    (x y z : ι → Fin m)
    (hne : ∀ i ∈ s, x i ≠ y i ∧ x i ≠ z i ∧ y i ≠ z i)
    {t : ℝ} (ht : 0 < t)
    (hprod : ∏ i ∈ s, (t - tripleGapDet (D.atom (x i)) (D.atom (y i)) (D.atom (z i))) ≤ 0) :
    ¬ IsTie D := by
  obtain ⟨i, hi, hpos⟩ := exists_pos_of_prod_sub_nonpos ht hprod
  obtain ⟨hxy, hxz, hyz⟩ := hne i hi
  exact branchB_not_isTie_of_gapDet_pos D hB hxy hxz hyz hpos

/-- **THE CRITERION IS LOSSLESS.**  At a branch-B tie every such product is at
least `t ^ card`, so demanding the product in place of the disjunction gives
nothing away. -/
theorem branchB_isTie_prod_ge {ι : Type*} {s : Finset ι}
    (D : WeightedDesign m 3) (hB : BranchB D) (htie : IsTie D)
    (x y z : ι → Fin m)
    (hne : ∀ i ∈ s, x i ≠ y i ∧ x i ≠ z i ∧ y i ≠ z i)
    {t : ℝ} (ht : 0 < t) :
    t ^ s.card
      ≤ ∏ i ∈ s, (t - tripleGapDet (D.atom (x i)) (D.atom (y i)) (D.atom (z i))) := by
  rw [← Finset.prod_const]
  refine Finset.prod_le_prod (fun i _ => ht.le) fun i hi => ?_
  obtain ⟨hxy, hxz, hyz⟩ := hne i hi
  have := branchB_isTie_gapDet_nonpos D hB htie hxy hxz hyz
  linarith

/-- **THE TWO-TRIPLE FORM.**  The smallest family that is not a single triple:
one product of two factors, degree six in the atoms, and it still names
neither triple. -/
theorem branchB_not_isTie_of_two_prod_nonpos (D : WeightedDesign m 3) (hB : BranchB D)
    {x₁ y₁ z₁ x₂ y₂ z₂ : Fin m}
    (h₁ : x₁ ≠ y₁ ∧ x₁ ≠ z₁ ∧ y₁ ≠ z₁) (h₂ : x₂ ≠ y₂ ∧ x₂ ≠ z₂ ∧ y₂ ≠ z₂)
    {t : ℝ} (ht : 0 < t)
    (hprod : (t - tripleGapDet (D.atom x₁) (D.atom y₁) (D.atom z₁))
        * (t - tripleGapDet (D.atom x₂) (D.atom y₂) (D.atom z₂)) ≤ 0) :
    ¬ IsTie D := by
  intro htie
  rcases le_or_gt (tripleGapDet (D.atom x₁) (D.atom y₁) (D.atom z₁)) 0 with h1 | h1
  · rcases le_or_gt (tripleGapDet (D.atom x₂) (D.atom y₂) (D.atom z₂)) 0 with h2 | h2
    · nlinarith
    · exact branchB_not_isTie_of_gapDet_pos D hB h₂.1 h₂.2.1 h₂.2.2 h2 htie
  · exact branchB_not_isTie_of_gapDet_pos D hB h₁.1 h₁.2.1 h₁.2.2 h1 htie

/-! ## 5. The strict producer, and what a tie forces at every spanning triple -/

/-- **THE STRICT PRODUCER.**  The landed producer returns weak domination from
`pair area sum ≤ bracket²`.  Making the hypothesis strict makes the conclusion
strict, and that is what a tie can refuse.

The dual-basis expansion turns the bracket times any probe into the wedge probe
at that probe's own atom readings, so `bracket² * ‖ξ‖² ≤ pairAreaSum * (ξᵀ S ξ)`;
under a strict cap the atom sum beats the identity at every nonzero probe. -/
theorem posDef_of_pairAreaSum_lt_bracket_sq (a b c : Fin 3 → ℝ)
    (hbracket : tripleBracket a b c ≠ 0)
    (harea : triplePairAreaSum a b c < tripleBracket a b c ^ 2) :
    (atomMatrix a + atomMatrix b + atomMatrix c - 1).PosDef := by
  have hherm : (atomMatrix a + atomMatrix b + atomMatrix c - 1).IsHermitian := by
    simpa [gapOfDirectionTriple] using gapOfDirectionTriple_isHermitian a b c
  have hbr2 : 0 < tripleBracket a b c ^ 2 := by positivity
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨hherm, fun probe hprobe => ?_⟩
  rw [star_trivial]
  -- the gap's quadratic form is the reading square total less the probe's norm
  have hform : probe ⬝ᵥ ((atomMatrix a + atomMatrix b + atomMatrix c - 1) *ᵥ probe)
      = ((a ⬝ᵥ probe) ^ 2 + (b ⬝ᵥ probe) ^ 2 + (c ⬝ᵥ probe) ^ 2)
        - probe ⬝ᵥ probe := by
    simp only [Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.one_mulVec,
      dotProduct_sub, dotProduct_add, atomMatrix_dotProduct_mulVec]
  -- the dual-basis expansion, read as squared norms
  have hdual := bracket_smul_eq_wedgeProbe_readings a b c probe
  have hcap := wedgeProbe_normSq_le_pairAreaSum_mul a b c
    ![a ⬝ᵥ probe, b ⬝ᵥ probe, c ⬝ᵥ probe]
  have hleft : (tripleBracket a b c • probe) ⬝ᵥ (tripleBracket a b c • probe)
      = tripleBracket a b c ^ 2 * (probe ⬝ᵥ probe) := by
    simp only [smul_dotProduct, dotProduct_smul, smul_eq_mul]; ring
  have hread : (![a ⬝ᵥ probe, b ⬝ᵥ probe, c ⬝ᵥ probe] : Fin 3 → ℝ)
      ⬝ᵥ ![a ⬝ᵥ probe, b ⬝ᵥ probe, c ⬝ᵥ probe]
      = (a ⬝ᵥ probe) ^ 2 + (b ⬝ᵥ probe) ^ 2 + (c ⬝ᵥ probe) ^ 2 := by
    simp only [dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
    ring
  rw [hdual] at hleft
  rw [hread] at hcap
  -- the probe has positive length
  have hpp : 0 < probe ⬝ᵥ probe := by
    rcases (dotProduct_self_nonneg probe).lt_or_eq with h | h
    · exact h
    · exact absurd (dotProduct_self_eq_zero.mp h.symm) hprobe
  -- the reading square total is positive, else the bracket kills the probe
  have hQ : 0 < (a ⬝ᵥ probe) ^ 2 + (b ⬝ᵥ probe) ^ 2 + (c ⬝ᵥ probe) ^ 2 := by
    rcases le_or_gt ((a ⬝ᵥ probe) ^ 2 + (b ⬝ᵥ probe) ^ 2 + (c ⬝ᵥ probe) ^ 2) 0 with h | h
    · exfalso; nlinarith [hleft, hcap]
    · exact h
  rw [hform]
  nlinarith [hleft, hcap, hQ, hpp]

/-- **WHAT A TIE FORCES AT EVERY SPANNING TRIPLE.**  A tie has no strict
dominator, so the strict producer must never fire: every triple with a nonzero
bracket carries a pair area sum at least its squared bracket.

Both sides are wedges and brackets, the statement is tie-necessary and carries
no chart, and it holds at every triple at once rather than at a selected one.

[MEASURED: the identities `Σ_{a<b} w_ab = e₂(S)`, `Σ_T [T]² = det S` and
`Σ_T e₂(K_T) = (m−2)·e₂(S)` for the unweighted atom sum `S` hold to `10⁻¹³` at
the fixtures, so summing this law over all triples gives the unweighted,
size-carrying tie condition `det S ≤ (m−2)·e₂(S)`.  It is true at the primitive
diamond, the split diamond and the tetrahedral foil, and it is NOT vacuous —
between 1.6 and 4.1 percent of random designs violate it.  It is however loose
at ties, the ratio there running `0.46` to `0.67` against the permitted `1`, so
it is recorded and not built upon.] -/
theorem isTie_pairAreaSum_ge_bracket_sq (D : WeightedDesign m 3) (htie : IsTie D)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hbracket : tripleBracket (D.atom x) (D.atom y) (D.atom z) ≠ 0) :
    tripleBracket (D.atom x) (D.atom y) (D.atom z) ^ 2
      ≤ triplePairAreaSum (D.atom x) (D.atom y) (D.atom z) := by
  by_contra hcon
  push_neg at hcon
  refine htie.2 ({x, y, z} : Finset (Fin m)) (card_triple hxy hxz hyz) ?_
  rw [subsetSum_triple_eq_add D hxy hxz hyz]
  exact posDef_of_pairAreaSum_lt_bracket_sq _ _ _ hbracket hcon

end Gtz
