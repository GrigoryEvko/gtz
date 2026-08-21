/-
# The moment ladder of a complement triple, and the ten-refusal collapse of `Z1`

## The ladder

At `(6,3)` the complement of a corner triple is again a triple, so the three
outside atoms are the columns of a SQUARE matrix.  That single fact turns the two
moments the design supplies into a whole ladder.  Write

  `M := ∑_d g_d g_dᵀ`   (the unweighted outside sum, the gap of the complement
                          plus the identity)
  `N := ∑_d w_d g_d g_dᵀ` (any weighted outside sum)

Then, with NO hypothesis at all,

  `N·adj(M)·N = det M · ∑_d w_d² g_d g_dᵀ`      (`Gtz.outside_second_moment_ladder`)
  `M·adj(N)·M = det M · ∑_d (∏_{e≠d} w_e) g_d g_dᵀ` (`Gtz.outside_inverse_moment_ladder`)

so the SECOND weight moment and the INVERSE weight moment of the outside frame
are both computable from the first two.  Iterating, every weight moment is.  The
carrier is `adj(A·B) = adj B · adj A` together with `A·adj A = det A · 1`, applied
to `M = G Gᵀ` and `N = G T Gᵀ` for `G` the column matrix of the three atoms and
`T` the diagonal of the weights.

**The ladder is a size marker.**  It needs the complement to have exactly three
labels in dimension three: at `(5,3)` the complement of a triple is a pair and `G`
is not square, at `(7,3)` it is four atoms and `G` has a kernel.  This is the
sharpest form of "the complement triple is a basis" the campaign has, and it is
the first version that carries the weights.

## What the ladder buys

Every aggregate of the star of an inside atom weighted by a POLYNOMIAL in the
outside weights becomes computable.  The landed aggregate is the unweighted one,
`Gtz.star_ledger_unweighted`; the weighted one is `Gtz.star_ledger_weighted`; the
ladder adds the square, the inverse, and everything above.  Each of them is a
producer, because a positive total forces a positive summand and a positive
downdate determinant promotes to a strictly dominating triple.

[MEASURED on 44628 exact `Z1` cell-H inhabitants in quad precision: the star
fires at every one.  Of the aggregates, the co-weighted total `∑ (1−w_d)·r_d`
fires at 99.9395 percent, the unweighted at 98.9827, the square at 95.5297, the
weighted at 96.7532 and the inverse at 48.4270.  So no single aggregate of this
family covers the cell — the disjunction is irreducible, exactly as the symmetric
trio criterion says it must be — and the ladder is an instrument, not the kill.]

## The collapse

The second half of this module removes the clause families from the `Z1`
coverage residual.  A tie at a corner refuses exactly the ten triples that share
at most one label with the corner (landed census).  At `(6,3)` those are the
complement itself and the nine triples built from one inside atom and two outside
atoms.  Hence

  `Gtz.oneAxisZeroPairCoverage_of_starRefusalSystem`

derives `Gtz.OneAxisZeroPairCoverage` — whose two cells carry, between them, four
universally quantified clause families in matrix inverses, adjugate traces, an
odds parameter and an excluded-trace floor — from TEN positive definiteness
refusals on named triples.  Both cell residuals follow as corollaries, and cell H
gets four of its ten for free from the failed four-set.
-/
import Gtz.Wave.ZeroAxisStarLedger
import Gtz.Wave.OneAxisZeroRefusalBudget
import Gtz.Wave.CellHStarPromotion

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000

namespace Gtz

open Matrix Finset

/-! ## 1. The frame factorisation -/

/-- A weighted triple of atoms is the column matrix conjugating the diagonal of
the weights. -/
theorem weightedTriple_eq_columnMatrix_conj (a b c : Fin 3 → ℝ) (wa wb wc : ℝ) :
    wa • atomMatrix a + wb • atomMatrix b + wc • atomMatrix c
      = columnMatrix a b c * Matrix.diagonal ![wa, wb, wc]
        * (columnMatrix a b c)ᵀ := by
  ext i j
  rw [Matrix.mul_assoc]
  simp [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.transpose_apply,
    columnMatrix, Fin.sum_univ_three, atomMatrix, Matrix.vecMulVec_apply]
  ring

/-- The diagonal of the squared weights is the square of the diagonal. -/
theorem diagonal_weights_sq (wa wb wc : ℝ) :
    Matrix.diagonal ![wa, wb, wc] * Matrix.diagonal ![wa, wb, wc]
      = Matrix.diagonal ![wa ^ 2, wb ^ 2, wc ^ 2] := by
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  fin_cases i <;> simp [sq]

/-- The adjugate of the diagonal of three weights. -/
theorem adjugate_diagonal_three (wa wb wc : ℝ) :
    (Matrix.diagonal ![wa, wb, wc]).adjugate
      = Matrix.diagonal ![wb * wc, wa * wc, wa * wb] := by
  rw [Matrix.adjugate_diagonal]
  congr 1
  funext i
  have h0 : ((univ : Finset (Fin 3)).erase 0) = {1, 2} := by decide
  have h1 : ((univ : Finset (Fin 3)).erase 1) = {0, 2} := by decide
  have h2 : ((univ : Finset (Fin 3)).erase 2) = {0, 1} := by decide
  fin_cases i <;> simp [h0, h1, h2]

/-! ## 2. The moment ladder -/

/-- **THE SECOND MOMENT LADDER.**  For three atoms in dimension three, the
weighted sum conjugated through the adjugate of the unweighted sum returns the
SQUARE-weighted sum, scaled by the unweighted determinant.  No hypothesis. -/
theorem outside_second_moment_ladder (a b c : Fin 3 → ℝ) (wa wb wc : ℝ) :
    (wa • atomMatrix a + wb • atomMatrix b + wc • atomMatrix c)
        * (atomMatrix a + atomMatrix b + atomMatrix c).adjugate
        * (wa • atomMatrix a + wb • atomMatrix b + wc • atomMatrix c)
      = (atomMatrix a + atomMatrix b + atomMatrix c).det
        • (wa ^ 2 • atomMatrix a + wb ^ 2 • atomMatrix b + wc ^ 2 • atomMatrix c) := by
  set G := columnMatrix a b c with hG
  set T := Matrix.diagonal ![wa, wb, wc] with hT
  have hM : atomMatrix a + atomMatrix b + atomMatrix c = G * Gᵀ :=
    atomTriple_eq_mul_transpose a b c
  have hN : wa • atomMatrix a + wb • atomMatrix b + wc • atomMatrix c = G * T * Gᵀ :=
    weightedTriple_eq_columnMatrix_conj a b c wa wb wc
  have hSq : wa ^ 2 • atomMatrix a + wb ^ 2 • atomMatrix b + wc ^ 2 • atomMatrix c
      = G * (T * T) * Gᵀ := by
    rw [diagonal_weights_sq]
    exact weightedTriple_eq_columnMatrix_conj a b c (wa ^ 2) (wb ^ 2) (wc ^ 2)
  have hadjM : (G * Gᵀ).adjugate = (Gᵀ).adjugate * G.adjugate :=
    Matrix.adjugate_mul_distrib G Gᵀ
  have hdetM : (G * Gᵀ).det = G.det * G.det := by
    rw [Matrix.det_mul, Matrix.det_transpose]
  rw [hM, hN, hSq, hadjM, hdetM]
  have hstep : G * T * Gᵀ * ((Gᵀ).adjugate * G.adjugate) * (G * T * Gᵀ)
      = G * T * (Gᵀ * (Gᵀ).adjugate) * (G.adjugate * G) * T * Gᵀ := by
    simp only [Matrix.mul_assoc]
  rw [hstep, Matrix.mul_adjugate, Matrix.adjugate_mul, Matrix.det_transpose]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, smul_smul,
    Matrix.mul_assoc]

/-- **THE INVERSE MOMENT LADDER.**  The unweighted sum conjugated through the
adjugate of the weighted sum returns the sum weighted by the products of the
OTHER two weights, scaled by the unweighted determinant.  No hypothesis. -/
theorem outside_inverse_moment_ladder (a b c : Fin 3 → ℝ) (wa wb wc : ℝ) :
    (atomMatrix a + atomMatrix b + atomMatrix c)
        * (wa • atomMatrix a + wb • atomMatrix b + wc • atomMatrix c).adjugate
        * (atomMatrix a + atomMatrix b + atomMatrix c)
      = (atomMatrix a + atomMatrix b + atomMatrix c).det
        • ((wb * wc) • atomMatrix a + (wa * wc) • atomMatrix b
          + (wa * wb) • atomMatrix c) := by
  set G := columnMatrix a b c with hG
  set T := Matrix.diagonal ![wa, wb, wc] with hT
  have hM : atomMatrix a + atomMatrix b + atomMatrix c = G * Gᵀ :=
    atomTriple_eq_mul_transpose a b c
  have hN : wa • atomMatrix a + wb • atomMatrix b + wc • atomMatrix c = G * T * Gᵀ :=
    weightedTriple_eq_columnMatrix_conj a b c wa wb wc
  have hOther : (wb * wc) • atomMatrix a + (wa * wc) • atomMatrix b
      + (wa * wb) • atomMatrix c = G * T.adjugate * Gᵀ := by
    rw [hT, adjugate_diagonal_three]
    exact weightedTriple_eq_columnMatrix_conj a b c (wb * wc) (wa * wc) (wa * wb)
  have hadjN : (G * T * Gᵀ).adjugate = (Gᵀ).adjugate * (T.adjugate * G.adjugate) := by
    rw [Matrix.adjugate_mul_distrib, Matrix.adjugate_mul_distrib]
  have hdetM : (G * Gᵀ).det = G.det * G.det := by
    rw [Matrix.det_mul, Matrix.det_transpose]
  rw [hM, hN, hOther, hadjN, hdetM]
  have hstep : G * Gᵀ * ((Gᵀ).adjugate * (T.adjugate * G.adjugate)) * (G * Gᵀ)
      = G * (Gᵀ * (Gᵀ).adjugate) * T.adjugate * (G.adjugate * G) * Gᵀ := by
    simp only [Matrix.mul_assoc]
  rw [hstep, Matrix.mul_adjugate, Matrix.adjugate_mul, Matrix.det_transpose]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, smul_smul,
    Matrix.mul_assoc]

/-- **THE LADDER AT A PROBE.**  The square-weighted outside energy at any probe
is one quadratic form of the two moments. -/
theorem outside_second_moment_probe (a b c : Fin 3 → ℝ) (wa wb wc : ℝ)
    (v : Fin 3 → ℝ) :
    v ⬝ᵥ (((wa • atomMatrix a + wb • atomMatrix b + wc • atomMatrix c)
          * (atomMatrix a + atomMatrix b + atomMatrix c).adjugate
          * (wa • atomMatrix a + wb • atomMatrix b + wc • atomMatrix c)) *ᵥ v)
      = (atomMatrix a + atomMatrix b + atomMatrix c).det
        * (wa ^ 2 * (a ⬝ᵥ v) ^ 2 + wb ^ 2 * (b ⬝ᵥ v) ^ 2 + wc ^ 2 * (c ⬝ᵥ v) ^ 2) := by
  rw [outside_second_moment_ladder]
  simp only [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Matrix.add_mulVec,
    dotProduct_add, atomMatrix, vecMulVec_mulVec_eq, dotProduct_smul]
  rw [dotProduct_comm v a, dotProduct_comm v b, dotProduct_comm v c]
  ring

/-- The square-weighted outside energy is nonnegative whenever the unweighted
determinant is. -/
theorem outside_second_moment_probe_nonneg (a b c : Fin 3 → ℝ) (wa wb wc : ℝ)
    (hdet : 0 ≤ (atomMatrix a + atomMatrix b + atomMatrix c).det) (v : Fin 3 → ℝ) :
    0 ≤ v ⬝ᵥ (((wa • atomMatrix a + wb • atomMatrix b + wc • atomMatrix c)
          * (atomMatrix a + atomMatrix b + atomMatrix c).adjugate
          * (wa • atomMatrix a + wb • atomMatrix b + wc • atomMatrix c)) *ᵥ v) := by
  rw [outside_second_moment_probe]
  have h : 0 ≤ wa ^ 2 * (a ⬝ᵥ v) ^ 2 + wb ^ 2 * (b ⬝ᵥ v) ^ 2 + wc ^ 2 * (c ⬝ᵥ v) ^ 2 := by
    positivity
  exact mul_nonneg hdet h

/-! ## 3. The ten refusals of a `Z1` corner -/

/-- The complement of a corner triple meets it in nothing. -/
theorem compl_inter_card_le_one {m : ℕ} (C : Finset (Fin m)) :
    ((Cᶜ : Finset (Fin m)) ∩ C).card ≤ 1 := by
  have hempty : (Cᶜ : Finset (Fin m)) ∩ C = ∅ :=
    Finset.eq_empty_iff_forall_notMem.mpr fun a ha =>
      (Finset.mem_compl.mp (Finset.mem_inter.mp ha).1) (Finset.mem_inter.mp ha).2
  rw [hempty]
  simp

/-- **A TIE REFUSES THE COMPLEMENT OF A CORNER.** -/
theorem isTie_compl_not_posDef {m : ℕ} (D : WeightedDesign m 3) {C : Finset (Fin m)}
    (hC : C.card = 3) (hcompl : (Cᶜ : Finset (Fin m)).card = 3)
    {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ}
    (hgap : subsetSum D C - 1 = lam • atomMatrix u) (htie : IsTie D) :
    ¬ (subsetSum D (Cᶜ : Finset (Fin m)) - 1).PosDef :=
  (isTie_iff_corner_refusals D C hC hlam hgap).mp htie _ hcompl (compl_inter_card_le_one C)

/-- **THE `Z1` STAR REFUSAL SYSTEM.**  Ten positive definiteness refusals at a
`Z1` corner: the complement triple, and the nine triples made of one inside atom
and two outside atoms.  No inverse, no adjugate trace, no odds parameter. -/
def OneAxisZeroStarRefusalSystem : Prop :=
  ∀ (D : WeightedDesign 6 3) (x y z : Fin 6), x ≠ y → x ≠ z → y ≠ z →
    ∀ lam : ℝ, 0 < lam → ∀ u : Fin 3 → ℝ, u ⬝ᵥ u = 1 →
    subsetSum D ({x, y, z} : Finset (Fin 6)) - 1 = lam • atomMatrix u →
    D.atom x ⬝ᵥ u = 0 → D.atom y ⬝ᵥ u ≠ 0 → D.atom z ⬝ᵥ u ≠ 0 →
    ¬ (subsetSum D (({x, y, z} : Finset (Fin 6))ᶜ) - 1).PosDef →
    (∀ e ∈ ({x, y, z} : Finset (Fin 6)), ∀ d ∈ (({x, y, z} : Finset (Fin 6))ᶜ),
      ¬ (subsetSum D
          (insert e ((({x, y, z} : Finset (Fin 6))ᶜ).erase d)) - 1).PosDef) →
    False

/-- **THE TEN-REFUSAL COLLAPSE.**  The whole `Z1` pair coverage — both cells,
their four clause families in matrix inverses, adjugate traces, an odds parameter
and an excluded-trace floor — follows from the ten geometric refusals.  The
corner census supplies the other ten triples of the twenty for free. -/
theorem oneAxisZeroPairCoverage_of_starRefusalSystem :
    OneAxisZeroStarRefusalSystem → OneAxisZeroPairCoverage := by
  intro hsys
  refine oneAxisZeroPairCoverage_iff.mpr ?_
  intro D x y z hxy hxz hyz lam hlam u hunit hgap hax hay haz htie
  have hC : ({x, y, z} : Finset (Fin 6)).card = 3 := cornerTriple_card hxy hxz hyz
  have hcompl : ((({x, y, z} : Finset (Fin 6))ᶜ) : Finset (Fin 6)).card = 3 :=
    cornerTriple_compl_card hxy hxz hyz
  exact hsys D x y z hxy hxz hyz lam hlam u hunit hgap hax hay haz
    (isTie_compl_not_posDef D hC hcompl hlam.le hgap htie)
    (fun e he d hd => isTie_oneInside_not_posDef D hC hcompl hlam.le hgap htie he hd)

/-- **CELL H FOLLOWS.**  The heavy-inside residual is a corollary of the ten
refusals: the star of the failed inside atom and the complement triple are free,
so only six of the ten are ever asked. -/
theorem oneAxisZeroHeavyInsideResidual_of_starRefusalSystem :
    OneAxisZeroStarRefusalSystem → OneAxisZeroHeavyInsideResidual := by
  intro hsys
  exact (oneAxisZeroPairCoverage_iff_cellResiduals.mp
    (oneAxisZeroPairCoverage_of_starRefusalSystem hsys)).1

/-- **CELL B FOLLOWS.**  The both-light residual is the other corollary.  This
discharges the reduction that `Gtz/Wave/BothLightChartReduction.lean` advertises
and does not land. -/
theorem oneAxisZeroBothLightResidual_of_starRefusalSystem :
    OneAxisZeroStarRefusalSystem → OneAxisZeroBothLightResidual := by
  intro hsys
  exact (oneAxisZeroPairCoverage_iff_cellResiduals.mp
    (oneAxisZeroPairCoverage_of_starRefusalSystem hsys)).2

/-- **THE CELL-H BUDGET.**  At a cell-H corner four of the ten refusals hold with
nothing computed, so the star system is asked only for the remaining six. -/
theorem cellH_starRefusalSystem_budget (D : WeightedDesign 6 3) {x y z : Fin 6}
    (hnotz : ¬ (subsetSum D (insert z (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).PosDef) :
    ¬ (subsetSum D (({x, y, z} : Finset (Fin 6))ᶜ) - 1).PosDef
      ∧ ∀ d ∈ (({x, y, z} : Finset (Fin 6))ᶜ),
        ¬ (subsetSum D
            (insert z ((({x, y, z} : Finset (Fin 6))ᶜ).erase d)) - 1).PosDef := by
  have hz : z ∈ ({x, y, z} : Finset (Fin 6)) := by simp
  exact cellH_zSide_refusals_free D hz hnotz

end Gtz
