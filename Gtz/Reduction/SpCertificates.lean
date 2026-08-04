import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The series-parallel certificate kit (Nesterenko 2511.02387v2, Section 4)

Nesterenko proves fixed-graph GTZ for every 2-connected series-parallel graph
at every positive edge weighting: some spanning tree `tau` satisfies the
Dirichlet-energy bound `E_{E \ tau}(u) <= (n-1) * E_tau(u)` for every potential
`u`, where `n` is the edge count -- equivalently `alpha_G(W) >= 1/n`
(his Lemma 4.1), with equality exactly at the graph-induced weighting
(his Theorem 4.1).  The proof is a recursion over the series-parallel
decomposition tree combining per-child tree/forest certificates
(his Proposition 4.1, displays (4.2)-(4.4) and (4.6)-(4.7)).

This module mechanizes the recursion's ALGEBRAIC content -- every lemma here
is a finite-family real inequality with no graph vocabulary -- and then
instantiates the kit on the DIAMOND (K4 minus an edge: four vertices, five
edges, the rank-3 primitive of the campaign's equality locus), proving the
fixed-graph GTZ bound `E_cotree <= 4 * E_tree` for EVERY positive weighting
of the diamond, with the spanning tree produced by the paper's selection
rule.  The graph-induced diamond weighting `(3,3,2,3,3)` (up to scale,
chord = 2) is where all eight trees tie; the tie itself is already in the
tree as `Gtz.diamondDesign_isTie`.

Pre-verified in exact sympy (`verify_sp.py` alongside this file): the
phi-ratio weights of his Definition 2.2, the eight-fold tie at those weights
(every spanning-tree block of the projection has least eigenvalue exactly
1/5), both SOS certificate identities below, and the selection rule on 400
random rational weightings.
-/

namespace Gtz

open Finset

variable {edgeIndex : Type*}

/-! ## The two quadratic engines (his Lemmas 4.2 and 4.3) -/

/-- **Lemma 4.2 of 2511.02387v2, cleared form** (Cauchy-Schwarz in Engel
form): for positive coefficients, `(sum x)^2 <= (sum 1/A) * (sum A x^2)`. -/
theorem sq_sum_le_sum_inv_mul_sum_mul_sq (s : Finset edgeIndex)
    (coeff quantity : edgeIndex → ℝ) (hcoeff : ∀ i ∈ s, 0 < coeff i) :
    (∑ i ∈ s, quantity i) ^ 2
      ≤ (∑ i ∈ s, (coeff i)⁻¹) * ∑ i ∈ s, coeff i * quantity i ^ 2 := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  · have hinv : ∀ i ∈ s, 0 < (coeff i)⁻¹ := fun i hi => inv_pos.2 (hcoeff i hi)
    have hsumInv : 0 < ∑ i ∈ s, (coeff i)⁻¹ := Finset.sum_pos hinv hs
    have hEngel := Finset.sq_sum_div_le_sum_sq_div s quantity hinv
    have hterm : ∑ i ∈ s, quantity i ^ 2 / (coeff i)⁻¹
        = ∑ i ∈ s, coeff i * quantity i ^ 2 :=
      Finset.sum_congr rfl fun i _ => by rw [div_eq_mul_inv, inv_inv, mul_comm]
    rw [hterm, div_le_iff₀ hsumInv] at hEngel
    calc (∑ i ∈ s, quantity i) ^ 2
        ≤ (∑ i ∈ s, coeff i * quantity i ^ 2) * ∑ i ∈ s, (coeff i)⁻¹ := hEngel
      _ = (∑ i ∈ s, (coeff i)⁻¹) * ∑ i ∈ s, coeff i * quantity i ^ 2 := by ring

/-- **Lemma 4.2 of 2511.02387v2** (paper form): the harmonic mean of the
coefficients bounds the quadratic below,
`(sum 1/A)^{-1} * (sum x)^2 <= sum A x^2`. -/
theorem harmonicMean_mul_sq_sum_le (s : Finset edgeIndex)
    (coeff quantity : edgeIndex → ℝ) (hcoeff : ∀ i ∈ s, 0 < coeff i) :
    (∑ i ∈ s, (coeff i)⁻¹)⁻¹ * (∑ i ∈ s, quantity i) ^ 2
      ≤ ∑ i ∈ s, coeff i * quantity i ^ 2 := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  · have hinv : ∀ i ∈ s, 0 < (coeff i)⁻¹ := fun i hi => inv_pos.2 (hcoeff i hi)
    have hsumInv : 0 < ∑ i ∈ s, (coeff i)⁻¹ := Finset.sum_pos hinv hs
    have hcleared := sq_sum_le_sum_inv_mul_sum_mul_sq s coeff quantity hcoeff
    have hmul := mul_le_mul_of_nonneg_left hcleared (inv_nonneg.2 hsumInv.le)
    rwa [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hsumInv), one_mul] at hmul

/-- The two-variable saddle identity behind his Lemma 4.3, in cleared form:
`(A - B) * (B x^2 - A y^2) <= B A (x + y)^2` holds for ALL reals, because the
difference is the perfect square `(B x + A y)^2`. -/
theorem saddle_cleared (bCoeff aCoeff x y : ℝ) :
    (aCoeff - bCoeff) * (bCoeff * x ^ 2 - aCoeff * y ^ 2)
      ≤ bCoeff * aCoeff * (x + y) ^ 2 := by
  nlinarith [sq_nonneg (bCoeff * x + aCoeff * y)]

/-- **Lemma 4.3 of 2511.02387v2**: one positive term against a family of
negative ones.  If `D^{-1} = 1/B - sum 1/A_i > 0`, then
`B x_j^2 - sum A_i x_i^2 <= D (x_j + sum x_i)^2`. -/
theorem seriesForest_saddle_bound (s : Finset edgeIndex) (bCoeff : ℝ)
    (coeff : edgeIndex → ℝ) (xj : ℝ) (x : edgeIndex → ℝ) (hb : 0 < bCoeff)
    (hcoeff : ∀ i ∈ s, 0 < coeff i)
    (hgap : 0 < bCoeff⁻¹ - ∑ i ∈ s, (coeff i)⁻¹) :
    bCoeff * xj ^ 2 - ∑ i ∈ s, coeff i * x i ^ 2
      ≤ (bCoeff⁻¹ - ∑ i ∈ s, (coeff i)⁻¹)⁻¹ * (xj + ∑ i ∈ s, x i) ^ 2 := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp only [Finset.sum_empty, sub_zero, add_zero, inv_inv]
    exact le_of_eq (by ring)
  · have hinv : ∀ i ∈ s, 0 < (coeff i)⁻¹ := fun i hi => inv_pos.2 (hcoeff i hi)
    have hsumInv : 0 < ∑ i ∈ s, (coeff i)⁻¹ := Finset.sum_pos hinv hs
    set sumInv := ∑ i ∈ s, (coeff i)⁻¹ with hsumInvDef
    set harmonic := sumInv⁻¹ with hharmonicDef
    have hharmonicPos : 0 < harmonic := inv_pos.2 hsumInv
    have hbelow : bCoeff < harmonic := by
      have hlt : sumInv < bCoeff⁻¹ := sub_pos.mp hgap
      have hmul := mul_lt_mul_of_pos_left hlt hb
      rw [mul_inv_cancel₀ (ne_of_gt hb)] at hmul
      have hone : bCoeff * sumInv * harmonic < 1 * harmonic :=
        mul_lt_mul_of_pos_right hmul hharmonicPos
      rwa [mul_assoc, mul_inv_cancel₀ (ne_of_gt hsumInv), mul_one, one_mul]
        at hone
    have hdiffPos : 0 < harmonic - bCoeff := sub_pos.2 hbelow
    set total := ∑ i ∈ s, x i with htotalDef
    have hquad : harmonic * total ^ 2 ≤ ∑ i ∈ s, coeff i * x i ^ 2 :=
      harmonicMean_mul_sq_sum_le s coeff x hcoeff
    have hstepOne : bCoeff * xj ^ 2 - ∑ i ∈ s, coeff i * x i ^ 2
        ≤ bCoeff * xj ^ 2 - harmonic * total ^ 2 := by linarith
    have hstepTwo : bCoeff * xj ^ 2 - harmonic * total ^ 2
        ≤ bCoeff * harmonic / (harmonic - bCoeff) * (xj + total) ^ 2 := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hdiffPos]
      calc (bCoeff * xj ^ 2 - harmonic * total ^ 2) * (harmonic - bCoeff)
          = (harmonic - bCoeff) * (bCoeff * xj ^ 2 - harmonic * total ^ 2) := by
            ring
        _ ≤ bCoeff * harmonic * (xj + total) ^ 2 :=
            saddle_cleared bCoeff harmonic xj total
    have hgapEq : (bCoeff⁻¹ - sumInv)⁻¹
        = bCoeff * harmonic / (harmonic - bCoeff) := by
      have hsumInvEq : sumInv = harmonic⁻¹ := by
        rw [hharmonicDef, inv_inv]
      rw [hsumInvEq,
        inv_sub_inv (ne_of_gt hb) (ne_of_gt hharmonicPos), inv_div]
    rw [hgapEq]
    exact hstepOne.trans hstepTwo

/-! ## The combination steps of his Proposition 4.1

Abstract shadows of the recursion over the decomposition tree.  `sizeOf i`
plays `|H_i|` (child edge counts), `constOf i` the child constants `c_{H_i}`,
`total` the ambient edge count `n`, and `drop` the terminal potential drop
`Delta_H(u)`.  The parallel node uses the weighted-mean constant of his (4.6);
the series node uses the harmonic recursion of his (4.4) and (4.7). -/

/-- Parallel node, forest mode (his display (4.3) at a parallel `H`): child
forest certificates just add. -/
theorem parallelForest_combine (s : Finset edgeIndex)
    (forestQ sizeOf constOf : edgeIndex → ℝ) (drop : ℝ)
    (hforest : ∀ i ∈ s, forestQ i ≤ sizeOf i * constOf i * drop ^ 2) :
    ∑ i ∈ s, forestQ i ≤ (∑ i ∈ s, sizeOf i * constOf i) * drop ^ 2 := by
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum fun i hi => hforest i hi

section EraseCombination

variable [DecidableEq edgeIndex]

/-- Parallel node, tree mode, exact form: one child in tree mode, the rest in
forest mode, no division anywhere.  With the choice `c_j` at least the
weighted mean this is his display (4.2) at a parallel `H`. -/
theorem parallelTree_combine (s : Finset edgeIndex) (j : edgeIndex)
    (hj : j ∈ s) (treeQ total drop : ℝ)
    (forestQ sizeOf constOf : edgeIndex → ℝ)
    (htree : treeQ ≤ -((total - sizeOf j) * constOf j * drop ^ 2))
    (hforest : ∀ i ∈ s.erase j, forestQ i ≤ sizeOf i * constOf i * drop ^ 2) :
    treeQ + ∑ i ∈ s.erase j, forestQ i
      ≤ (∑ i ∈ s, sizeOf i * constOf i - total * constOf j) * drop ^ 2 := by
  have hsum : ∑ i ∈ s.erase j, forestQ i
      ≤ (∑ i ∈ s.erase j, sizeOf i * constOf i) * drop ^ 2 :=
    parallelForest_combine (s.erase j) forestQ sizeOf constOf drop hforest
  have hsplit : sizeOf j * constOf j + ∑ i ∈ s.erase j, sizeOf i * constOf i
      = ∑ i ∈ s, sizeOf i * constOf i :=
    Finset.add_sum_erase s (fun i => sizeOf i * constOf i) hj
  have hshape : -((total - sizeOf j) * constOf j * drop ^ 2)
        + (∑ i ∈ s.erase j, sizeOf i * constOf i) * drop ^ 2
      = (∑ i ∈ s, sizeOf i * constOf i - total * constOf j) * drop ^ 2 := by
    rw [← hsplit]; ring
  linarith

/-- The root of the recursion: at the root parallel node `total` equals the
whole edge sum, and the weighted-mean choice makes the combination
nonpositive -- exactly `E_{E \ tau}(u) <= (n-1) E_tau(u)` in `Q`-form. -/
theorem rootParallel_nonpos (s : Finset edgeIndex) (j : edgeIndex)
    (hj : j ∈ s) (treeQ total drop : ℝ)
    (forestQ sizeOf constOf : edgeIndex → ℝ)
    (htree : treeQ ≤ -((total - sizeOf j) * constOf j * drop ^ 2))
    (hforest : ∀ i ∈ s.erase j, forestQ i ≤ sizeOf i * constOf i * drop ^ 2)
    (hchoice : ∑ i ∈ s, sizeOf i * constOf i ≤ total * constOf j) :
    treeQ + ∑ i ∈ s.erase j, forestQ i ≤ 0 := by
  have hcombine := parallelTree_combine s j hj treeQ total drop
    forestQ sizeOf constOf htree hforest
  have hfactor : ∑ i ∈ s, sizeOf i * constOf i - total * constOf j ≤ 0 :=
    sub_nonpos.2 hchoice
  have hprod := mul_le_mul_of_nonneg_right hfactor (sq_nonneg drop)
  rw [zero_mul] at hprod
  exact hcombine.trans hprod

/-- Parallel node, tree mode, mean form (his (4.2) with the constant (4.6)):
dividing the exact form by the positive size sum. -/
theorem parallelTree_combine_mean (s : Finset edgeIndex) (j : edgeIndex)
    (hj : j ∈ s) (treeQ total drop : ℝ)
    (forestQ sizeOf constOf : edgeIndex → ℝ) (htotal : 0 ≤ total)
    (hsizes : 0 < ∑ i ∈ s, sizeOf i)
    (htree : treeQ ≤ -((total - sizeOf j) * constOf j * drop ^ 2))
    (hforest : ∀ i ∈ s.erase j, forestQ i ≤ sizeOf i * constOf i * drop ^ 2)
    (hchoice : (∑ i ∈ s, sizeOf i * constOf i) / (∑ i ∈ s, sizeOf i)
      ≤ constOf j) :
    treeQ + ∑ i ∈ s.erase j, forestQ i
      ≤ -((total - ∑ i ∈ s, sizeOf i)
          * ((∑ i ∈ s, sizeOf i * constOf i) / (∑ i ∈ s, sizeOf i))
          * drop ^ 2) := by
  have hcombine := parallelTree_combine s j hj treeQ total drop
    forestQ sizeOf constOf htree hforest
  set meanConst := (∑ i ∈ s, sizeOf i * constOf i) / (∑ i ∈ s, sizeOf i)
    with hmeanDef
  have hmass : ∑ i ∈ s, sizeOf i * constOf i
      = (∑ i ∈ s, sizeOf i) * meanConst := by
    rw [hmeanDef]
    field_simp
  have hcoeff : ∑ i ∈ s, sizeOf i * constOf i - total * constOf j
      ≤ -((total - ∑ i ∈ s, sizeOf i) * meanConst) := by
    have hmulChoice := mul_le_mul_of_nonneg_left hchoice htotal
    rw [hmass]
    linarith
  have hprod := mul_le_mul_of_nonneg_right hcoeff (sq_nonneg drop)
  calc treeQ + ∑ i ∈ s.erase j, forestQ i
      ≤ (∑ i ∈ s, sizeOf i * constOf i - total * constOf j) * drop ^ 2 :=
        hcombine
    _ ≤ -((total - ∑ i ∈ s, sizeOf i) * meanConst) * drop ^ 2 := hprod
    _ = -((total - ∑ i ∈ s, sizeOf i) * meanConst * drop ^ 2) := by ring

end EraseCombination

/-- Series node, tree mode (his display (4.2) at a series `H`, constant by
the harmonic recursion (4.4)/(4.7)): child tree certificates chain through
Lemma 4.2, the child drops telescoping to the node drop. -/
theorem seriesTree_combine (s : Finset edgeIndex)
    (treeQ coeff delta : edgeIndex → ℝ)
    (hcoeff : ∀ i ∈ s, 0 < coeff i)
    (htree : ∀ i ∈ s, treeQ i ≤ -(coeff i * delta i ^ 2)) :
    ∑ i ∈ s, treeQ i
      ≤ -((∑ i ∈ s, (coeff i)⁻¹)⁻¹ * (∑ i ∈ s, delta i) ^ 2) := by
  have hsum : ∑ i ∈ s, treeQ i ≤ ∑ i ∈ s, -(coeff i * delta i ^ 2) :=
    Finset.sum_le_sum htree
  have hneg : ∑ i ∈ s, -(coeff i * delta i ^ 2)
      = -∑ i ∈ s, coeff i * delta i ^ 2 := by simp
  have hquad := harmonicMean_mul_sq_sum_le s coeff delta hcoeff
  linarith [hsum, hquad]

/-- Series node, forest mode (his display (4.3) at a series `H`): one child
forest certificate against the others' tree certificates, through Lemma 4.3.
The gap hypothesis is exactly what his ratio choice of `j` supplies. -/
theorem seriesForest_combine (s : Finset edgeIndex) (forestQ bCoeff dropj : ℝ)
    (treeQ coeff delta : edgeIndex → ℝ) (hb : 0 < bCoeff)
    (hcoeff : ∀ i ∈ s, 0 < coeff i)
    (hforest : forestQ ≤ bCoeff * dropj ^ 2)
    (htree : ∀ i ∈ s, treeQ i ≤ -(coeff i * delta i ^ 2))
    (hgap : 0 < bCoeff⁻¹ - ∑ i ∈ s, (coeff i)⁻¹) :
    forestQ + ∑ i ∈ s, treeQ i
      ≤ (bCoeff⁻¹ - ∑ i ∈ s, (coeff i)⁻¹)⁻¹
          * (dropj + ∑ i ∈ s, delta i) ^ 2 := by
  have hsum : ∑ i ∈ s, treeQ i ≤ -∑ i ∈ s, coeff i * delta i ^ 2 := by
    have h := Finset.sum_le_sum htree
    have hneg : ∑ i ∈ s, -(coeff i * delta i ^ 2)
        = -∑ i ∈ s, coeff i * delta i ^ 2 := by simp
    linarith [h]
  have hsaddle := seriesForest_saddle_bound s bCoeff coeff dropj delta hb
    hcoeff hgap
  linarith

/-! ## The two selection rules

His Proposition 4.1 chooses, at a parallel node, a child whose constant
reaches the weighted mean, and at a series node a child maximizing
`u_i / |H_i|`.  Both exist by averaging. -/

/-- At a parallel node some child constant reaches the size-weighted mean
(cleared form, no division). -/
theorem exists_child_ge_weightedMean (s : Finset edgeIndex) (hs : s.Nonempty)
    (sizeOf constOf : edgeIndex → ℝ) (hsize : ∀ i ∈ s, 0 < sizeOf i) :
    ∃ j ∈ s, ∑ i ∈ s, sizeOf i * constOf i
      ≤ (∑ i ∈ s, sizeOf i) * constOf j := by
  by_contra hnone
  push Not at hnone
  have hpointwise : ∀ j ∈ s,
      sizeOf j * ((∑ i ∈ s, sizeOf i) * constOf j)
        < sizeOf j * ∑ i ∈ s, sizeOf i * constOf i := fun j hj =>
    mul_lt_mul_of_pos_left (hnone j hj) (hsize j hj)
  have hstrict := Finset.sum_lt_sum_of_nonempty hs hpointwise
  have hleft : ∑ j ∈ s, sizeOf j * ((∑ i ∈ s, sizeOf i) * constOf j)
      = (∑ i ∈ s, sizeOf i) * ∑ j ∈ s, sizeOf j * constOf j := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hright : ∑ j ∈ s, sizeOf j * ∑ i ∈ s, sizeOf i * constOf i
      = (∑ j ∈ s, sizeOf j) * ∑ i ∈ s, sizeOf i * constOf i :=
    (Finset.sum_mul s sizeOf _).symm
  rw [hleft, hright] at hstrict
  exact lt_irrefl _ hstrict

/-- At a series node some child ratio `u_j / h_j` reaches the mean ratio
(cleared form; positivity is not even needed). -/
theorem exists_child_ratio_ge (s : Finset edgeIndex) (hs : s.Nonempty)
    (sizeOf uQuantity : edgeIndex → ℝ) :
    ∃ j ∈ s, (∑ i ∈ s, uQuantity i) * sizeOf j
      ≤ (∑ i ∈ s, sizeOf i) * uQuantity j := by
  by_contra hnone
  push Not at hnone
  have hstrict : ∑ j ∈ s, (∑ i ∈ s, sizeOf i) * uQuantity j
      < ∑ j ∈ s, (∑ i ∈ s, uQuantity i) * sizeOf j :=
    Finset.sum_lt_sum_of_nonempty hs fun j hj => hnone j hj
  rw [← Finset.mul_sum, ← Finset.mul_sum] at hstrict
  have hcomm : (∑ i ∈ s, sizeOf i) * ∑ i ∈ s, uQuantity i
      = (∑ i ∈ s, uQuantity i) * ∑ i ∈ s, sizeOf i := mul_comm _ _
  linarith

/-! ## The diamond instance

Vertices `0,1,2,3`; edges `e0 = 01`, `e1 = 02`, `e2 = 12` (the chord),
`e3 = 13`, `e4 = 32`; `n = 5` edges, rank `3`.  Two-terminal decomposition at
the terminals `(1,2)`: parallel composition of the chord, the series path
`1-0-2`, and the series path `1-3-2`.  Drops are oriented so that both paths
telescope to the terminal drop `u 1 - u 2`. -/

/-- Oriented potential drops along the five diamond edges. -/
def diamondNetDrop (edge : Fin 5) (potential : Fin 4 → ℝ) : ℝ :=
  ![potential 1 - potential 0, potential 0 - potential 2,
    potential 1 - potential 2, potential 1 - potential 3,
    potential 3 - potential 2] edge

theorem diamondNetDrop_zero (potential : Fin 4 → ℝ) :
    diamondNetDrop 0 potential = potential 1 - potential 0 := rfl

theorem diamondNetDrop_one (potential : Fin 4 → ℝ) :
    diamondNetDrop 1 potential = potential 0 - potential 2 := rfl

theorem diamondNetDrop_two (potential : Fin 4 → ℝ) :
    diamondNetDrop 2 potential = potential 1 - potential 2 := rfl

theorem diamondNetDrop_three (potential : Fin 4 → ℝ) :
    diamondNetDrop 3 potential = potential 1 - potential 3 := rfl

theorem diamondNetDrop_four (potential : Fin 4 → ℝ) :
    diamondNetDrop 4 potential = potential 3 - potential 2 := rfl

/-- Dirichlet energy of a potential on an edge set of the diamond. -/
def diamondNetEnergy (weight : Fin 5 → ℝ) (potential : Fin 4 → ℝ)
    (edgeSet : Finset (Fin 5)) : ℝ :=
  ∑ e ∈ edgeSet, weight e * diamondNetDrop e potential ^ 2

/-- The eight spanning trees of the diamond: every 3-subset of the five edges
except the two triangles `{0,1,2}` and `{2,3,4}`. -/
def diamondNetSpanningTrees : Finset (Finset (Fin 5)) :=
  {{0, 1, 3}, {0, 1, 4}, {0, 3, 4}, {1, 3, 4},
   {0, 2, 3}, {0, 2, 4}, {1, 2, 3}, {1, 2, 4}}

theorem diamondNetEnergy_pair (weight : Fin 5 → ℝ) (potential : Fin 4 → ℝ)
    (a b : Fin 5) (hab : a ≠ b) :
    diamondNetEnergy weight potential {a, b}
      = weight a * diamondNetDrop a potential ^ 2
        + weight b * diamondNetDrop b potential ^ 2 := by
  unfold diamondNetEnergy
  rw [Finset.sum_pair hab]

theorem diamondNetEnergy_triple (weight : Fin 5 → ℝ) (potential : Fin 4 → ℝ)
    (a b c : Fin 5) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    diamondNetEnergy weight potential {a, b, c}
      = weight a * diamondNetDrop a potential ^ 2
        + (weight b * diamondNetDrop b potential ^ 2
            + weight c * diamondNetDrop c potential ^ 2) := by
  unfold diamondNetEnergy
  rw [Finset.sum_insert (by simp [hab, hac]), Finset.sum_pair hbc]

/-- Tree and cotree energies always split the total: the structural witness
that each selected edge set partitions the five edges against its
complement. -/
theorem diamondNetEnergy_sdiff_add (weight : Fin 5 → ℝ)
    (potential : Fin 4 → ℝ) (edgeSet : Finset (Fin 5)) :
    diamondNetEnergy weight potential (Finset.univ \ edgeSet)
        + diamondNetEnergy weight potential edgeSet
      = diamondNetEnergy weight potential Finset.univ :=
  Finset.sum_sdiff (Finset.subset_univ edgeSet)

/-- Path branch, tree mode: the series pair `(a, da), (b, db)` beats four
times its harmonic certificate.  Instance of Lemma 4.2; the difference is the
square `(2 (a da - b db))^2 / (a + b)`. -/
theorem diamondPathTree_bound (a b da db : ℝ) (ha : 0 < a) (hb : 0 < b) :
    4 * (a * b / (a + b)) * (da + db) ^ 2
      ≤ 4 * a * da ^ 2 + 4 * b * db ^ 2 := by
  rw [show 4 * (a * b / (a + b)) * (da + db) ^ 2
      = 4 * (a * b) * (da + db) ^ 2 / (a + b) from by ring,
    div_le_iff₀ (by positivity)]
  nlinarith [sq_nonneg (2 * (a * da - b * db))]

/-- Path branch, forest mode: drop the LIGHTER edge to the cotree and keep
the heavier in the tree.  Instance of Lemma 4.3 with his ratio choice; the
`8/3` is twice the branch constant `c = (4/3) a b / (a + b)`.  SOS
certificate (verified symbolically): with `alpha = a (5b - 3a) > 0`,
`alpha * (8ab Delta^2 - 3(a+b)(a da^2 - 4b db^2))
  = (alpha da + 8ab db)^2 + 60 ab (b^2 - a^2) db^2`. -/
theorem diamondPathForest_bound (a b da db : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hab : a ≤ b) :
    a * da ^ 2 - 4 * b * db ^ 2
      ≤ 8 / 3 * (a * b / (a + b)) * (da + db) ^ 2 := by
  have halpha : 0 < a * (5 * b - 3 * a) := by nlinarith
  have hkey : a * (5 * b - 3 * a)
        * (8 * (a * b) * (da + db) ^ 2
            - (a * da ^ 2 - 4 * b * db ^ 2) * (3 * (a + b)))
      = (a * (5 * b - 3 * a) * da + 8 * (a * b) * db) ^ 2
        + 60 * (a * b) * ((b - a) * (b + a)) * db ^ 2 := by ring
  have hextra : 0 ≤ 60 * (a * b) * ((b - a) * (b + a)) * db ^ 2 := by
    have hfirst : (0 : ℝ) ≤ 60 * (a * b) := by positivity
    have hsecond : (0 : ℝ) ≤ (b - a) * (b + a) :=
      mul_nonneg (sub_nonneg.2 hab) (by positivity)
    exact mul_nonneg (mul_nonneg hfirst hsecond) (sq_nonneg db)
  have hscaled : a * (5 * b - 3 * a) * 0
      ≤ a * (5 * b - 3 * a)
        * (8 * (a * b) * (da + db) ^ 2
            - (a * da ^ 2 - 4 * b * db ^ 2) * (3 * (a + b))) := by
    rw [mul_zero, hkey]
    exact add_nonneg (sq_nonneg _) hextra
  have hclear := le_of_mul_le_mul_left hscaled halpha
  rw [show 8 / 3 * (a * b / (a + b)) * (da + db) ^ 2
      = 8 * (a * b) * (da + db) ^ 2 / 3 / (a + b) from by ring,
    le_div_iff₀ (by positivity : (0 : ℝ) < a + b),
    le_div_iff₀ (by norm_num : (0 : ℝ) < 3)]
  linarith

/-- The three-way root selection at the diamond, in the cleared language of
the branch constants: chord constant `w 2`, path products
`X01 = w0 w1 / (w0 + w1)` and `X34 = w3 w4 / (w3 + w4)`. -/
theorem diamondRoot_choice (w : Fin 5 → ℝ) :
    w 2 + 8 / 3 * (w 3 * w 4 / (w 3 + w 4))
        ≤ 4 * (w 0 * w 1 / (w 0 + w 1))
      ∨ w 2 + 8 / 3 * (w 0 * w 1 / (w 0 + w 1))
        ≤ 4 * (w 3 * w 4 / (w 3 + w 4))
      ∨ w 0 * w 1 / (w 0 + w 1) + w 3 * w 4 / (w 3 + w 4)
        ≤ 3 / 2 * w 2 := by
  by_contra hnone
  push Not at hnone
  obtain ⟨hfirst, hsecond, hthird⟩ := hnone
  linarith

set_option maxHeartbeats 800000 in
/-- **Fixed-graph GTZ for the diamond at every positive weighting**
(the diamond instance of Nesterenko 2511.02387v2, Section 4): every positive
weighting of the five diamond edges admits a spanning tree whose cotree
energy is bounded by `n - 1 = 4` times its tree energy, at every potential.
The tree is produced by the paper's selection rule: pick the branch whose
constant reaches the weighted mean, and inside each forest-mode path keep
the heavier edge. -/
theorem diamondNet_exists_spanningTree_energy_bound (w : Fin 5 → ℝ)
    (hw : ∀ e, 0 < w e) :
    ∃ tree ∈ diamondNetSpanningTrees, ∀ potential : Fin 4 → ℝ,
      diamondNetEnergy w potential (Finset.univ \ tree)
        ≤ 4 * diamondNetEnergy w potential tree := by
  rcases diamondRoot_choice w with hpath01 | hpath34 | hchord
  · -- the 1-0-2 path carries the tree mode
    rcases le_total (w 3) (w 4) with h34 | h43
    · refine ⟨{0, 1, 4}, by decide, fun u => ?_⟩
      rw [show Finset.univ \ ({0, 1, 4} : Finset (Fin 5))
            = ({2, 3} : Finset (Fin 5)) from by decide,
        diamondNetEnergy_pair w u 2 3 (by decide),
        diamondNetEnergy_triple w u 0 1 4 (by decide) (by decide) (by decide),
        diamondNetDrop_zero, diamondNetDrop_one, diamondNetDrop_two,
        diamondNetDrop_three, diamondNetDrop_four]
      have htree := diamondPathTree_bound (w 0) (w 1) (u 1 - u 0) (u 0 - u 2)
        (hw 0) (hw 1)
      have hforest := diamondPathForest_bound (w 3) (w 4) (u 1 - u 3)
        (u 3 - u 2) (hw 3) (hw 4) h34
      rw [show u 1 - u 0 + (u 0 - u 2) = u 1 - u 2 from by ring] at htree
      rw [show u 1 - u 3 + (u 3 - u 2) = u 1 - u 2 from by ring] at hforest
      have hfactor : w 2 + 8 / 3 * (w 3 * w 4 / (w 3 + w 4))
          - 4 * (w 0 * w 1 / (w 0 + w 1)) ≤ 0 := by linarith
      have hmul := mul_le_mul_of_nonneg_right hfactor (sq_nonneg (u 1 - u 2))
      rw [zero_mul] at hmul
      linarith [htree, hforest, hmul]
    · refine ⟨{0, 1, 3}, by decide, fun u => ?_⟩
      rw [show Finset.univ \ ({0, 1, 3} : Finset (Fin 5))
            = ({2, 4} : Finset (Fin 5)) from by decide,
        diamondNetEnergy_pair w u 2 4 (by decide),
        diamondNetEnergy_triple w u 0 1 3 (by decide) (by decide) (by decide),
        diamondNetDrop_zero, diamondNetDrop_one, diamondNetDrop_two,
        diamondNetDrop_three, diamondNetDrop_four]
      have htree := diamondPathTree_bound (w 0) (w 1) (u 1 - u 0) (u 0 - u 2)
        (hw 0) (hw 1)
      have hforest := diamondPathForest_bound (w 4) (w 3) (u 3 - u 2)
        (u 1 - u 3) (hw 4) (hw 3) h43
      rw [show u 1 - u 0 + (u 0 - u 2) = u 1 - u 2 from by ring] at htree
      rw [show u 3 - u 2 + (u 1 - u 3) = u 1 - u 2 from by ring] at hforest
      have hswap : w 4 * w 3 / (w 4 + w 3) = w 3 * w 4 / (w 3 + w 4) := by
        rw [mul_comm, add_comm]
      rw [hswap] at hforest
      have hfactor : w 2 + 8 / 3 * (w 3 * w 4 / (w 3 + w 4))
          - 4 * (w 0 * w 1 / (w 0 + w 1)) ≤ 0 := by linarith
      have hmul := mul_le_mul_of_nonneg_right hfactor (sq_nonneg (u 1 - u 2))
      rw [zero_mul] at hmul
      linarith [htree, hforest, hmul]
  · -- the 1-3-2 path carries the tree mode
    rcases le_total (w 0) (w 1) with h01 | h10
    · refine ⟨{1, 3, 4}, by decide, fun u => ?_⟩
      rw [show Finset.univ \ ({1, 3, 4} : Finset (Fin 5))
            = ({0, 2} : Finset (Fin 5)) from by decide,
        diamondNetEnergy_pair w u 0 2 (by decide),
        diamondNetEnergy_triple w u 1 3 4 (by decide) (by decide) (by decide),
        diamondNetDrop_zero, diamondNetDrop_one, diamondNetDrop_two,
        diamondNetDrop_three, diamondNetDrop_four]
      have htree := diamondPathTree_bound (w 3) (w 4) (u 1 - u 3) (u 3 - u 2)
        (hw 3) (hw 4)
      have hforest := diamondPathForest_bound (w 0) (w 1) (u 1 - u 0)
        (u 0 - u 2) (hw 0) (hw 1) h01
      rw [show u 1 - u 3 + (u 3 - u 2) = u 1 - u 2 from by ring] at htree
      rw [show u 1 - u 0 + (u 0 - u 2) = u 1 - u 2 from by ring] at hforest
      have hfactor : w 2 + 8 / 3 * (w 0 * w 1 / (w 0 + w 1))
          - 4 * (w 3 * w 4 / (w 3 + w 4)) ≤ 0 := by linarith
      have hmul := mul_le_mul_of_nonneg_right hfactor (sq_nonneg (u 1 - u 2))
      rw [zero_mul] at hmul
      linarith [htree, hforest, hmul]
    · refine ⟨{0, 3, 4}, by decide, fun u => ?_⟩
      rw [show Finset.univ \ ({0, 3, 4} : Finset (Fin 5))
            = ({1, 2} : Finset (Fin 5)) from by decide,
        diamondNetEnergy_pair w u 1 2 (by decide),
        diamondNetEnergy_triple w u 0 3 4 (by decide) (by decide) (by decide),
        diamondNetDrop_zero, diamondNetDrop_one, diamondNetDrop_two,
        diamondNetDrop_three, diamondNetDrop_four]
      have htree := diamondPathTree_bound (w 3) (w 4) (u 1 - u 3) (u 3 - u 2)
        (hw 3) (hw 4)
      have hforest := diamondPathForest_bound (w 1) (w 0) (u 0 - u 2)
        (u 1 - u 0) (hw 1) (hw 0) h10
      rw [show u 1 - u 3 + (u 3 - u 2) = u 1 - u 2 from by ring] at htree
      rw [show u 0 - u 2 + (u 1 - u 0) = u 1 - u 2 from by ring] at hforest
      have hswap : w 1 * w 0 / (w 1 + w 0) = w 0 * w 1 / (w 0 + w 1) := by
        rw [mul_comm, add_comm]
      rw [hswap] at hforest
      have hfactor : w 2 + 8 / 3 * (w 0 * w 1 / (w 0 + w 1))
          - 4 * (w 3 * w 4 / (w 3 + w 4)) ≤ 0 := by linarith
      have hmul := mul_le_mul_of_nonneg_right hfactor (sq_nonneg (u 1 - u 2))
      rw [zero_mul] at hmul
      linarith [htree, hforest, hmul]
  · -- the chord carries the tree mode; both paths run forest mode
    rcases le_total (w 0) (w 1) with h01 | h10 <;>
      rcases le_total (w 3) (w 4) with h34 | h43
    · refine ⟨{1, 2, 4}, by decide, fun u => ?_⟩
      rw [show Finset.univ \ ({1, 2, 4} : Finset (Fin 5))
            = ({0, 3} : Finset (Fin 5)) from by decide,
        diamondNetEnergy_pair w u 0 3 (by decide),
        diamondNetEnergy_triple w u 1 2 4 (by decide) (by decide) (by decide),
        diamondNetDrop_zero, diamondNetDrop_one, diamondNetDrop_two,
        diamondNetDrop_three, diamondNetDrop_four]
      have hforestA := diamondPathForest_bound (w 0) (w 1) (u 1 - u 0)
        (u 0 - u 2) (hw 0) (hw 1) h01
      have hforestB := diamondPathForest_bound (w 3) (w 4) (u 1 - u 3)
        (u 3 - u 2) (hw 3) (hw 4) h34
      rw [show u 1 - u 0 + (u 0 - u 2) = u 1 - u 2 from by ring] at hforestA
      rw [show u 1 - u 3 + (u 3 - u 2) = u 1 - u 2 from by ring] at hforestB
      have hfactor : 8 / 3 * (w 0 * w 1 / (w 0 + w 1))
          + 8 / 3 * (w 3 * w 4 / (w 3 + w 4)) - 4 * w 2 ≤ 0 := by linarith
      have hmul := mul_le_mul_of_nonneg_right hfactor (sq_nonneg (u 1 - u 2))
      rw [zero_mul] at hmul
      linarith [hforestA, hforestB, hmul]
    · refine ⟨{1, 2, 3}, by decide, fun u => ?_⟩
      rw [show Finset.univ \ ({1, 2, 3} : Finset (Fin 5))
            = ({0, 4} : Finset (Fin 5)) from by decide,
        diamondNetEnergy_pair w u 0 4 (by decide),
        diamondNetEnergy_triple w u 1 2 3 (by decide) (by decide) (by decide),
        diamondNetDrop_zero, diamondNetDrop_one, diamondNetDrop_two,
        diamondNetDrop_three, diamondNetDrop_four]
      have hforestA := diamondPathForest_bound (w 0) (w 1) (u 1 - u 0)
        (u 0 - u 2) (hw 0) (hw 1) h01
      have hforestB := diamondPathForest_bound (w 4) (w 3) (u 3 - u 2)
        (u 1 - u 3) (hw 4) (hw 3) h43
      rw [show u 1 - u 0 + (u 0 - u 2) = u 1 - u 2 from by ring] at hforestA
      rw [show u 3 - u 2 + (u 1 - u 3) = u 1 - u 2 from by ring] at hforestB
      have hswap : w 4 * w 3 / (w 4 + w 3) = w 3 * w 4 / (w 3 + w 4) := by
        rw [mul_comm, add_comm]
      rw [hswap] at hforestB
      have hfactor : 8 / 3 * (w 0 * w 1 / (w 0 + w 1))
          + 8 / 3 * (w 3 * w 4 / (w 3 + w 4)) - 4 * w 2 ≤ 0 := by linarith
      have hmul := mul_le_mul_of_nonneg_right hfactor (sq_nonneg (u 1 - u 2))
      rw [zero_mul] at hmul
      linarith [hforestA, hforestB, hmul]
    · refine ⟨{0, 2, 4}, by decide, fun u => ?_⟩
      rw [show Finset.univ \ ({0, 2, 4} : Finset (Fin 5))
            = ({1, 3} : Finset (Fin 5)) from by decide,
        diamondNetEnergy_pair w u 1 3 (by decide),
        diamondNetEnergy_triple w u 0 2 4 (by decide) (by decide) (by decide),
        diamondNetDrop_zero, diamondNetDrop_one, diamondNetDrop_two,
        diamondNetDrop_three, diamondNetDrop_four]
      have hforestA := diamondPathForest_bound (w 1) (w 0) (u 0 - u 2)
        (u 1 - u 0) (hw 1) (hw 0) h10
      have hforestB := diamondPathForest_bound (w 3) (w 4) (u 1 - u 3)
        (u 3 - u 2) (hw 3) (hw 4) h34
      rw [show u 0 - u 2 + (u 1 - u 0) = u 1 - u 2 from by ring] at hforestA
      rw [show u 1 - u 3 + (u 3 - u 2) = u 1 - u 2 from by ring] at hforestB
      have hswap : w 1 * w 0 / (w 1 + w 0) = w 0 * w 1 / (w 0 + w 1) := by
        rw [mul_comm, add_comm]
      rw [hswap] at hforestA
      have hfactor : 8 / 3 * (w 0 * w 1 / (w 0 + w 1))
          + 8 / 3 * (w 3 * w 4 / (w 3 + w 4)) - 4 * w 2 ≤ 0 := by linarith
      have hmul := mul_le_mul_of_nonneg_right hfactor (sq_nonneg (u 1 - u 2))
      rw [zero_mul] at hmul
      linarith [hforestA, hforestB, hmul]
    · refine ⟨{0, 2, 3}, by decide, fun u => ?_⟩
      rw [show Finset.univ \ ({0, 2, 3} : Finset (Fin 5))
            = ({1, 4} : Finset (Fin 5)) from by decide,
        diamondNetEnergy_pair w u 1 4 (by decide),
        diamondNetEnergy_triple w u 0 2 3 (by decide) (by decide) (by decide),
        diamondNetDrop_zero, diamondNetDrop_one, diamondNetDrop_two,
        diamondNetDrop_three, diamondNetDrop_four]
      have hforestA := diamondPathForest_bound (w 1) (w 0) (u 0 - u 2)
        (u 1 - u 0) (hw 1) (hw 0) h10
      have hforestB := diamondPathForest_bound (w 4) (w 3) (u 3 - u 2)
        (u 1 - u 3) (hw 4) (hw 3) h43
      rw [show u 0 - u 2 + (u 1 - u 0) = u 1 - u 2 from by ring] at hforestA
      rw [show u 3 - u 2 + (u 1 - u 3) = u 1 - u 2 from by ring] at hforestB
      have hswapA : w 1 * w 0 / (w 1 + w 0) = w 0 * w 1 / (w 0 + w 1) := by
        rw [mul_comm, add_comm]
      have hswapB : w 4 * w 3 / (w 4 + w 3) = w 3 * w 4 / (w 3 + w 4) := by
        rw [mul_comm, add_comm]
      rw [hswapA] at hforestA
      rw [hswapB] at hforestB
      have hfactor : 8 / 3 * (w 0 * w 1 / (w 0 + w 1))
          + 8 / 3 * (w 3 * w 4 / (w 3 + w 4)) - 4 * w 2 ≤ 0 := by linarith
      have hmul := mul_le_mul_of_nonneg_right hfactor (sq_nonneg (u 1 - u 2))
      rw [zero_mul] at hmul
      linarith [hforestA, hforestB, hmul]

end Gtz
