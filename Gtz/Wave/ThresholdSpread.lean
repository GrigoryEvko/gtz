import Gtz.Wave.GramCrossFloor
import Gtz.Wave.PairGapFloor
import Gtz.Wave.PluckerMassFloor

/-!
# The threshold side of the objective, and its marginals

The third Sylvester minor of a selection splits into a bracket and a threshold,

  `tripleGapDet = tripleBracket ^ 2 - tripleThresholdForm`

The bracket is the squared Plucker coordinate and carries the whole sign of the
triple product.  The threshold reads leverages and pairing SQUARES only, so it is
sign-free (`Gtz.tripleThreshold_eq_of_flip`).  Every sign-blind certificate in this
campaign is a bound on the threshold, and this file computes the threshold exactly.

**The threshold is additively two-local.**  At uniform weight on six labels,

  `threshold = 36 * (the three pair minors) - 6 * (the three diagonal entries) + 1`

(`Gtz.projThresholdAt_eq_tripleThresholdForm`).  There is no three-label term.  The
bracket, by contrast, carries the genuinely three-local `P_cd P_ce P_de`.  So every
marginal of the threshold is closed-form in the landed level-one and level-two
totals, and none of the bracket's are.

**The three threshold marginals**, over ordered distinct triples:

  * through a pair  `= 72 * pairMinor + 54 * (P_cc + P_dd) - 14`
  * through a label `= 2 * (180 * P_cc + 46)`
  * total           `= 1632`

Each follows from `Gtz.sum_pairMinor_projection` and the trace.  No Cauchy--Binet.

**The three gap marginals, and they are the payload.**  Against the landed
determinantal marginals of the projection measure,

  * through a pair  `= 144 * pairMinor + 14 - 54 * (P_cc + P_dd)`
  * through a label `= 2 * (36 * P_cc - 46)`
  * total           `= -336`

**The one-point marginal can never certify.**  Every diagonal entry of a
projection lies in `[0,1]`, so the label marginal is at most `-20` at every design
and every label (`Gtz.sum_projGap_through_neg`).  The one-label pigeonhole is dead,
and that is now a theorem rather than a measurement.

**The two-point marginal CAN certify, and in a corner it reads the diagonal
alone.**  When `144 * pairMinor + 14 > 54 * (P_cc + P_dd)` some triple through the
pair has a positive third minor (`Gtz.exists_pos_projGap_of_pairMarginal_pos`).
Feeding the row-energy law into the pair minor removes the off-diagonal entry and
leaves a condition on two leverages:

  **two labels of leverage at least `7/8` force a positive third minor through
  them** (`Gtz.exists_pos_projGap_of_two_heavy`).

That is the first certificate in this campaign that reads only the leverage
diagonal.  It does not contradict `Gtz.margin_not_determined_by_leverage_diagonal`,
which says the diagonal cannot COMPUTE the margin: the diagonal can still certify
in a corner, and this is the corner.

**The flat stratum.**  At `P_cc = 1/2` the threshold collapses to
`19 - 36 * (triple energy)` and the gap to `8 - 72 * (triple energy) + 432 *
(triple product)`, so the flat objective is a pure spread statement about the
triple products.  The threshold is constant there exactly when the triple energy
is, which corrects the guess that flatness alone forces it, and when constant its
value is forced to `68/5` by the total alone -- the icosahedral `13.6` is not
special to the icosahedron.
-/

namespace Gtz

open Matrix Finset

/-! ## 1. The threshold as a scalar polynomial -/

/-- The threshold: the part of the Gram determinant that the third minor does NOT
see.  Reads the pairings through their squares only, so it is sign-free. -/
def tripleThresholdForm (p q r u v w : ℝ) : ℝ :=
  (p * q + p * r + q * r) + (p + q + r) + 1 - (u ^ 2 + v ^ 2 + w ^ 2)

theorem tripleThreshold_apply (p q r u v w : ℝ) :
    tripleThresholdForm p q r u v w
      = (p * q + p * r + q * r) + (p + q + r) + 1 - (u ^ 2 + v ^ 2 + w ^ 2) := rfl

/-- The Gram determinant as a polynomial in the surpluses and pairings: the third
minor with every surplus shifted back up by one. -/
def gramDetForm (p q r u v w : ℝ) : ℝ :=
  (p + 1) * (q + 1) * (r + 1) - (p + 1) * w ^ 2 - (q + 1) * v ^ 2 - (r + 1) * u ^ 2
    + 2 * (u * v * w)

theorem gramDetForm_apply (p q r u v w : ℝ) :
    gramDetForm p q r u v w
      = (p + 1) * (q + 1) * (r + 1) - (p + 1) * w ^ 2 - (q + 1) * v ^ 2
        - (r + 1) * u ^ 2 + 2 * (u * v * w) := rfl

/-- **THE SPLIT.**  The third Sylvester minor is the Gram determinant minus the
threshold.  Both sides are polynomials, and this identity is the whole reason the
threshold is worth naming. -/
theorem tripleDetForm_eq_gramDetForm_sub_threshold (p q r u v w : ℝ) :
    tripleDetForm p q r u v w = gramDetForm p q r u v w - tripleThresholdForm p q r u v w := by
  rw [tripleDetForm, gramDetForm, tripleThresholdForm]; ring

/-- The threshold is exactly the deficit the landed correction term names, so this
file's object is the one already in kernel. -/
theorem tripleThreshold_atoms_eq_evenGap (a b c : Fin 3 → ℝ) :
    tripleThresholdForm (leverageOf a - 1) (leverageOf b - 1) (leverageOf c - 1)
        (a ⬝ᵥ b) (a ⬝ᵥ c) (b ⬝ᵥ c)
      = evenAtLeverage a b c - atomEvenPart a b c := by
  rw [evenAtLeverage_sub_atomEvenPart, tripleThresholdForm]

/-- **THE ATOM-LEVEL SPLIT.**  The third minor is the squared bracket minus the
threshold. -/
theorem tripleGapDet_eq_sq_tripleBracket_sub_threshold (a b c : Fin 3 → ℝ) :
    tripleGapDet a b c
      = tripleBracket a b c ^ 2
        - tripleThresholdForm (leverageOf a - 1) (leverageOf b - 1) (leverageOf c - 1)
            (a ⬝ᵥ b) (a ⬝ᵥ c) (b ⬝ᵥ c) := by
  rw [tripleGapDet_eq_sq_tripleBracket_add_correction, tripleThresholdForm]; ring

/-- **THE OBJECTIVE, IN THRESHOLD FORM.**  A triple has a positive third minor
exactly when its squared bracket beats its threshold. -/
theorem tripleGapDet_pos_iff_threshold_lt_sq_tripleBracket (a b c : Fin 3 → ℝ) :
    0 < tripleGapDet a b c
      ↔ tripleThresholdForm (leverageOf a - 1) (leverageOf b - 1) (leverageOf c - 1)
            (a ⬝ᵥ b) (a ⬝ᵥ c) (b ⬝ᵥ c)
          < tripleBracket a b c ^ 2 := by
  rw [tripleGapDet_eq_sq_tripleBracket_sub_threshold]
  constructor <;> intro h <;> linarith

/-! ### The threshold is sign-free -/

theorem tripleThreshold_neg_first (p q r u v w : ℝ) :
    tripleThresholdForm p q r (-u) v w = tripleThresholdForm p q r u v w := by
  rw [tripleThresholdForm, tripleThresholdForm]; ring

theorem tripleThreshold_neg_second (p q r u v w : ℝ) :
    tripleThresholdForm p q r u (-v) w = tripleThresholdForm p q r u v w := by
  rw [tripleThresholdForm, tripleThresholdForm]; ring

theorem tripleThreshold_neg_third (p q r u v w : ℝ) :
    tripleThresholdForm p q r u v (-w) = tripleThresholdForm p q r u v w := by
  rw [tripleThresholdForm, tripleThresholdForm]; ring

/-- **THE THRESHOLD IS THE SIGN-BLIND OBSTRUCTION.**  The two orientations of a
triple differ only in the bracket, never in the threshold, so no certificate that
declines to read the sign can improve on it. -/
theorem tripleThreshold_eq_of_flip (p q r u v w : ℝ) :
    tripleThresholdForm p q r (-u) (-v) w = tripleThresholdForm p q r u v w := by
  rw [tripleThresholdForm, tripleThresholdForm]; ring

/-- A single sign flip changes the third minor by exactly four times the cross
term, and the threshold cancels out of the difference.  So the threshold is the
whole of what a sign-blind certificate sees, and `4 * u * v * w` is the whole of
what it misses. -/
theorem tripleDetForm_sub_flip (p q r u v w : ℝ) :
    tripleDetForm p q r u v w - tripleDetForm p q r (-u) v w = 4 * (u * v * w) := by
  rw [tripleDetForm, tripleDetForm]; ring

/-- Flipping two pairings changes nothing: the cross term is even under it, which
is why the campaign's orientation classes are pairs of sign patterns. -/
theorem tripleDetForm_eq_of_double_flip (p q r u v w : ℝ) :
    tripleDetForm p q r (-u) (-v) w = tripleDetForm p q r u v w := by
  rw [tripleDetForm, tripleDetForm]; ring

/-- The threshold at an admissible triangle is strictly positive, so no triple ever
dominates on a vanishing bracket. -/
theorem tripleThreshold_pos_of_admissible (p q r u v w : ℝ)
    (hpq : 0 < p * q - w ^ 2) (hpr : 0 < p * r - v ^ 2) (hqr : 0 < q * r - u ^ 2)
    (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) :
    0 < tripleThresholdForm p q r u v w := by
  rw [tripleThresholdForm]; nlinarith [hpq, hpr, hqr, hp, hq, hr]

/-! ## 2. The threshold in projection coordinates

At uniform weight on six labels the whitened Gram of a selection is `6` times the
projection block, so the surpluses are `6 P_cc - 1` and the pairings `6 P_cd`.
Clearing the sixes turns the threshold into a polynomial in the projection's own
entries, with no division. -/

variable {size rank : ℕ}

/-- The threshold of a selection read on a form at uniform weight.  Two-local by
construction: three pair minors, three diagonal entries, a constant, and no
three-label term. -/
def projThresholdAt (form : Matrix (Fin size) (Fin size) ℝ)
    (first second third : Fin size) : ℝ :=
  36 * (pairMinorAt form first second + pairMinorAt form first third
        + pairMinorAt form second third)
    - 6 * (form first first + form second second + form third third) + 1

theorem projThresholdAt_apply (form : Matrix (Fin size) (Fin size) ℝ)
    (first second third : Fin size) :
    projThresholdAt form first second third
      = 36 * (pairMinorAt form first second + pairMinorAt form first third
          + pairMinorAt form second third)
        - 6 * (form first first + form second second + form third third) + 1 := rfl

section Symmetric

variable {form : Matrix (Fin size) (Fin size) ℝ}

private theorem entry_flip (hsymmetric : formᵀ = form) (left right : Fin size) :
    form right left = form left right := by
  have := congrFun (congrFun hsymmetric left) right
  simpa only [Matrix.transpose_apply] using this

/-- **THE PROJECTION THRESHOLD IS THE SCALAR THRESHOLD.**  With uniform weight the
whitened surpluses are `6 P_cc - 1` and the whitened pairings `6 P_cd`, and the
sixes clear exactly.  No symmetry is needed: the threshold reads each off-diagonal
slot once. -/
theorem projThresholdAt_eq_tripleThresholdForm (form : Matrix (Fin size) (Fin size) ℝ)
    (first second third : Fin size) :
    projThresholdAt form first second third
      = tripleThresholdForm (6 * form first first - 1) (6 * form second second - 1)
          (6 * form third third - 1) (6 * form first second) (6 * form first third)
          (6 * form second third) := by
  rw [projThresholdAt, tripleThresholdForm, pairMinorAt, pairMinorAt, pairMinorAt]; ring

/-- The gap of a selection at uniform weight: the whitened third minor, with the
weight product cleared. -/
def projGapAt (form : Matrix (Fin size) (Fin size) ℝ)
    (first second third : Fin size) : ℝ :=
  216 * (tripleBlock form first second third).det - projThresholdAt form first second third

theorem projGapAt_apply (form : Matrix (Fin size) (Fin size) ℝ)
    (first second third : Fin size) :
    projGapAt form first second third
      = 216 * (tripleBlock form first second third).det
        - projThresholdAt form first second third := rfl

/-- **THE GAP IS THE THIRD MINOR OF THE WHITENED GRAM.**  A positive
`Gtz.projGapAt` is exactly the third Sylvester condition at uniform weight, so the
marginals below are marginals of the objective itself. -/
theorem projGapAt_eq_tripleDetForm (hsymmetric : formᵀ = form)
    (first second third : Fin size) :
    projGapAt form first second third
      = tripleDetForm (6 * form first first - 1) (6 * form second second - 1)
          (6 * form third third - 1) (6 * form first second) (6 * form first third)
          (6 * form second third) := by
  rw [projGapAt, projThresholdAt, det_tripleBlock form hsymmetric, tripleDetForm,
    pairMinorAt, pairMinorAt, pairMinorAt]
  ring

/-- **THE GAP IS THE SHIFTED PRINCIPAL MINOR.**  Subtracting the uniform weight
from the diagonal and clearing the weight product gives the same polynomial. -/
theorem projGapAt_eq_shiftedMinor (hsymmetric : formᵀ = form)
    (first second third : Fin size) :
    projGapAt form first second third
      = 216 * ((form first first - 1 / 6) * (form second second - 1 / 6)
            * (form third third - 1 / 6)
          + 2 * (form first second * form first third * form second third)
          - (form first first - 1 / 6) * form second third ^ 2
          - (form second second - 1 / 6) * form first third ^ 2
          - (form third third - 1 / 6) * form first second ^ 2) := by
  rw [projGapAt, projThresholdAt, det_tripleBlock form hsymmetric, pairMinorAt, pairMinorAt,
    pairMinorAt]
  ring

/-- **THE BRIDGE TO THE LANDED THRESHOLD.**  `Gtz.tripleThreshold` is the same
object at determinant scale and general weight.  Clearing the uniform weight
product multiplies it by `216`, so every marginal in this file is a marginal of
the landed threshold. -/
theorem projThresholdAt_eq_tripleThreshold (form : Matrix (Fin size) (Fin size) ℝ)
    (hsymmetric : formᵀ = form) (first second third : Fin size) (h12 : first ≠ second)
    (h13 : first ≠ third) (h23 : second ≠ third) :
    projThresholdAt form first second third
      = 216 * tripleThreshold form (fun _ => (1 : ℝ) / 6) first second third := by
  have h21 : second ≠ first := Ne.symm h12
  have h31 : third ≠ first := Ne.symm h13
  have h32 : third ≠ second := Ne.symm h23
  simp only [tripleThreshold, principalMinorThree, projThresholdAt, pairMinorAt,
    Matrix.sub_apply, Matrix.diagonal_apply, h12, h13, h23, h21, h31, h32,
    if_false, if_true, sub_zero, entry_flip hsymmetric first second,
    entry_flip hsymmetric first third, entry_flip hsymmetric second third]
  ring

/-- The threshold is symmetric in its first two slots. -/
theorem projThresholdAt_swap_left (hsymmetric : formᵀ = form) (first second third : Fin size) :
    projThresholdAt form second first third = projThresholdAt form first second third := by
  have h12 := entry_flip hsymmetric first second
  simp only [projThresholdAt, pairMinorAt, h12]
  ring

end Symmetric

/-! ## 3. The counting bridge

Two forks named the index matching between an ordered triple sum and a subset sum
as their own gap and avoided it.  Ordered distinct triples make the counting
elementary: peeling the two outer labels off an inner sum is `Finset.add_sum_erase`
applied twice. -/

section Counting

variable {n : ℕ}

/-- Peeling two distinct labels off a full sum.  This is the whole bridge. -/
theorem sum_erase_two (outer mid : Fin n) (hmid : mid ∈ (univ : Finset (Fin n)).erase outer)
    (f : Fin n → ℝ) :
    ∑ inner ∈ ((univ : Finset (Fin n)).erase outer).erase mid, f inner
      = (∑ inner : Fin n, f inner) - f outer - f mid := by
  classical
  have hinner := Finset.add_sum_erase ((univ : Finset (Fin n)).erase outer) f hmid
  have houter := Finset.add_sum_erase (univ : Finset (Fin n)) f (Finset.mem_univ outer)
  linarith [hinner, houter]

/-- Peeling one label off a full sum. -/
theorem sum_erase_one (outer : Fin n) (f : Fin n → ℝ) :
    ∑ inner ∈ (univ : Finset (Fin n)).erase outer, f inner
      = (∑ inner : Fin n, f inner) - f outer := by
  classical
  have := Finset.add_sum_erase (univ : Finset (Fin n)) f (Finset.mem_univ outer)
  linarith [this]

/-- The innermost slot of an ordered distinct triple ranges over `n - 2` labels. -/
theorem card_erase_two (outer mid : Fin n)
    (hmid : mid ∈ (univ : Finset (Fin n)).erase outer) :
    (((univ : Finset (Fin n)).erase outer).erase mid).card = n - 2 := by
  classical
  rw [Finset.card_erase_of_mem hmid, Finset.card_erase_of_mem (Finset.mem_univ outer),
    Finset.card_univ, Fintype.card_fin]
  omega

/-- The middle slot of an ordered distinct triple ranges over `n - 1` labels. -/
theorem card_erase_one (outer : Fin n) :
    ((univ : Finset (Fin n)).erase outer).card = n - 1 := by
  classical
  rw [Finset.card_erase_of_mem (Finset.mem_univ outer), Finset.card_univ, Fintype.card_fin]

end Counting

/-! ## 4. The threshold marginals

Every marginal of the threshold follows from two landed facts: the trace of the
projection form is the rank, and the ordered pair-minor sum along a row is
`(rank - 1)` times that row's diagonal entry.  No Cauchy--Binet enters. -/

section Marginals

variable (design : WeightedDesign 6 3)

private theorem proj_symm : (projectionOfDesign design)ᵀ = projectionOfDesign design :=
  projectionOfDesign_transpose design

private theorem proj_row (label : Fin 6) :
    ∑ other : Fin 6, pairMinorAt (projectionOfDesign design) label other
      = 2 * projectionOfDesign design label label := by
  have := sum_pairMinor_projection design label
  norm_num at this ⊢
  linarith [this]

private theorem proj_trace :
    ∑ label : Fin 6, projectionOfDesign design label label = 3 := by
  have := sum_projectionDiagonal_eq_rank design
  norm_num at this ⊢
  linarith [this]

private theorem proj_pairMinor_symm (first second : Fin 6) :
    pairMinorAt (projectionOfDesign design) second first
      = pairMinorAt (projectionOfDesign design) first second := by
  have h := entry_flip (proj_symm design) first second
  simp only [pairMinorAt, h]; ring

/-- **THE THRESHOLD MARGINAL THROUGH A PAIR.**  Summing the threshold over the
third slot of an ordered distinct triple leaves a function of the pair's own minor
and the two diagonal entries.  Two-locality is exactly what makes this closed-form,
and the bracket has no such law. -/
theorem sum_projThreshold_through_pair (outer mid : Fin 6)
    (hmid : mid ∈ (univ : Finset (Fin 6)).erase outer) :
    ∑ inner ∈ ((univ : Finset (Fin 6)).erase outer).erase mid,
        projThresholdAt (projectionOfDesign design) outer mid inner
      = 72 * pairMinorAt (projectionOfDesign design) outer mid
        + 54 * (projectionOfDesign design outer outer + projectionOfDesign design mid mid)
        - 14 := by
  classical
  have hcard : (((univ : Finset (Fin 6)).erase outer).erase mid).card = 4 :=
    card_erase_two outer mid hmid
  have hA : ∑ inner ∈ ((univ : Finset (Fin 6)).erase outer).erase mid,
      pairMinorAt (projectionOfDesign design) outer inner
      = 2 * projectionOfDesign design outer outer
        - pairMinorAt (projectionOfDesign design) outer mid := by
    rw [sum_erase_two outer mid hmid
        (fun inner => pairMinorAt (projectionOfDesign design) outer inner),
      proj_row design outer, pairMinorAt_self]
    ring
  have hB : ∑ inner ∈ ((univ : Finset (Fin 6)).erase outer).erase mid,
      pairMinorAt (projectionOfDesign design) mid inner
      = 2 * projectionOfDesign design mid mid
        - pairMinorAt (projectionOfDesign design) outer mid := by
    rw [sum_erase_two outer mid hmid
        (fun inner => pairMinorAt (projectionOfDesign design) mid inner),
      proj_row design mid, pairMinorAt_self, proj_pairMinor_symm design mid outer]
    ring
  have hC : ∑ inner ∈ ((univ : Finset (Fin 6)).erase outer).erase mid,
      projectionOfDesign design inner inner
      = 3 - projectionOfDesign design outer outer - projectionOfDesign design mid mid := by
    rw [sum_erase_two outer mid hmid (fun inner => projectionOfDesign design inner inner),
      proj_trace design]
  have hbody : ∀ inner ∈ ((univ : Finset (Fin 6)).erase outer).erase mid,
      projThresholdAt (projectionOfDesign design) outer mid inner
        = 36 * pairMinorAt (projectionOfDesign design) outer inner
          + 36 * pairMinorAt (projectionOfDesign design) mid inner
          + (-6 : ℝ) * projectionOfDesign design inner inner
          + (36 * pairMinorAt (projectionOfDesign design) outer mid
              - 6 * projectionOfDesign design outer outer
              - 6 * projectionOfDesign design mid mid + 1) := by
    intro inner _; rw [projThresholdAt]; ring
  rw [Finset.sum_congr rfl hbody, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
    Finset.sum_const, hcard, hA, hB, hC]
  ring

/-- **THE THRESHOLD MARGINAL THROUGH A LABEL.**  Summing over the two free slots of
an ordered distinct triple leaves a function of that label's leverage alone. -/
theorem sum_projThreshold_through (outer : Fin 6) :
    ∑ mid ∈ (univ : Finset (Fin 6)).erase outer,
        ∑ inner ∈ ((univ : Finset (Fin 6)).erase outer).erase mid,
          projThresholdAt (projectionOfDesign design) outer mid inner
      = 2 * (180 * projectionOfDesign design outer outer + 46) := by
  classical
  have hcard : ((univ : Finset (Fin 6)).erase outer).card = 5 := card_erase_one outer
  have hA : ∑ mid ∈ (univ : Finset (Fin 6)).erase outer,
      pairMinorAt (projectionOfDesign design) outer mid
      = 2 * projectionOfDesign design outer outer := by
    rw [sum_erase_one outer (fun mid => pairMinorAt (projectionOfDesign design) outer mid),
      proj_row design outer, pairMinorAt_self]
    ring
  have hB : ∑ mid ∈ (univ : Finset (Fin 6)).erase outer,
      projectionOfDesign design mid mid = 3 - projectionOfDesign design outer outer := by
    rw [sum_erase_one outer (fun mid => projectionOfDesign design mid mid), proj_trace design]
  have hbody : ∀ mid ∈ (univ : Finset (Fin 6)).erase outer,
      ∑ inner ∈ ((univ : Finset (Fin 6)).erase outer).erase mid,
          projThresholdAt (projectionOfDesign design) outer mid inner
        = 72 * pairMinorAt (projectionOfDesign design) outer mid
          + 54 * projectionOfDesign design mid mid
          + (54 * projectionOfDesign design outer outer - 14) := by
    intro mid hmid
    rw [sum_projThreshold_through_pair design outer mid hmid]; ring
  rw [Finset.sum_congr rfl hbody, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_const, hcard, hA, hB]
  ring

/-- **THE THRESHOLD TOTAL.**  Over all ordered distinct triples the threshold adds
to `1632`, which is six times the `272` of the twenty unordered selections. -/
theorem sum_projThreshold :
    ∑ outer : Fin 6, ∑ mid ∈ (univ : Finset (Fin 6)).erase outer,
        ∑ inner ∈ ((univ : Finset (Fin 6)).erase outer).erase mid,
          projThresholdAt (projectionOfDesign design) outer mid inner
      = 1632 := by
  classical
  have hbody : ∀ outer ∈ (univ : Finset (Fin 6)),
      ∑ mid ∈ (univ : Finset (Fin 6)).erase outer,
        ∑ inner ∈ ((univ : Finset (Fin 6)).erase outer).erase mid,
          projThresholdAt (projectionOfDesign design) outer mid inner
        = 360 * projectionOfDesign design outer outer + 92 := by
    intro outer _
    rw [sum_projThreshold_through design outer]; ring
  rw [Finset.sum_congr rfl hbody, Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, proj_trace design]
  ring

/-! ## 5. The bracket marginals

The landed two-point marginal of the projection determinantal measure supplies the
bracket side.  Summing it once more gives the one-point marginal, and once more
the Cauchy--Binet total, all in ordered distinct form. -/

/-- **THE BRACKET MARGINAL THROUGH A PAIR.**  The landed two-point marginal, with
the two degenerate slots removed.  At rank three the coefficient is one, so the
pair minor IS the determinantal mass of the triples through that pair. -/
theorem sum_tripleBlockDet_through_pair (outer mid : Fin 6)
    (hmid : mid ∈ (univ : Finset (Fin 6)).erase outer) :
    ∑ inner ∈ ((univ : Finset (Fin 6)).erase outer).erase mid,
        (tripleBlock (projectionOfDesign design) outer mid inner).det
      = pairMinorAt (projectionOfDesign design) outer mid := by
  classical
  have hfull := sum_det_tripleBlock_through_pair (projectionOfDesign design) (proj_symm design)
    (projectionOfDesign_mul_self design) (proj_trace design) outer mid
  rw [sum_erase_two outer mid hmid
      (fun inner => (tripleBlock (projectionOfDesign design) outer mid inner).det), hfull,
    det_tripleBlock_self_left (projectionOfDesign design) (proj_symm design) outer mid,
    det_tripleBlock_self_right (projectionOfDesign design) (proj_symm design) outer mid]
  ring

/-- **THE BRACKET MARGINAL THROUGH A LABEL.**  Twice that label's leverage: the
one-point marginal of the projection determinantal measure, in ordered form. -/
theorem sum_tripleBlockDet_through (outer : Fin 6) :
    ∑ mid ∈ (univ : Finset (Fin 6)).erase outer,
        ∑ inner ∈ ((univ : Finset (Fin 6)).erase outer).erase mid,
          (tripleBlock (projectionOfDesign design) outer mid inner).det
      = 2 * projectionOfDesign design outer outer := by
  classical
  rw [Finset.sum_congr rfl fun mid hmid =>
    sum_tripleBlockDet_through_pair design outer mid hmid,
    sum_erase_one outer (fun mid => pairMinorAt (projectionOfDesign design) outer mid),
    proj_row design outer, pairMinorAt_self]
  ring

/-- **THE CAUCHY--BINET TOTAL, IN ORDERED FORM.**  Six times the unordered total
of one. -/
theorem sum_tripleBlockDet :
    ∑ outer : Fin 6, ∑ mid ∈ (univ : Finset (Fin 6)).erase outer,
        ∑ inner ∈ ((univ : Finset (Fin 6)).erase outer).erase mid,
          (tripleBlock (projectionOfDesign design) outer mid inner).det
      = 6 := by
  classical
  rw [Finset.sum_congr rfl fun outer _ => sum_tripleBlockDet_through design outer]
  rw [← Finset.mul_sum, proj_trace design]
  ring

/-! ## 6. The gap marginals — the payload -/

/-- **THE GAP MARGINAL THROUGH A PAIR.**  The bracket marginal times `216`, less
the threshold marginal.  This is the sharpest of the three: it is the only one that
can be positive. -/
theorem sum_projGap_through_pair (outer mid : Fin 6)
    (hmid : mid ∈ (univ : Finset (Fin 6)).erase outer) :
    ∑ inner ∈ ((univ : Finset (Fin 6)).erase outer).erase mid,
        projGapAt (projectionOfDesign design) outer mid inner
      = 144 * pairMinorAt (projectionOfDesign design) outer mid + 14
        - 54 * (projectionOfDesign design outer outer
            + projectionOfDesign design mid mid) := by
  classical
  have hexpand : ∀ inner ∈ ((univ : Finset (Fin 6)).erase outer).erase mid,
      projGapAt (projectionOfDesign design) outer mid inner
      = 216 * (tripleBlock (projectionOfDesign design) outer mid inner).det
        - projThresholdAt (projectionOfDesign design) outer mid inner := fun _ _ => rfl
  rw [Finset.sum_congr rfl hexpand, Finset.sum_sub_distrib, ← Finset.mul_sum,
    sum_tripleBlockDet_through_pair design outer mid hmid,
    sum_projThreshold_through_pair design outer mid hmid]
  ring

/-- **THE GAP MARGINAL THROUGH A LABEL.** -/
theorem sum_projGap_through (outer : Fin 6) :
    ∑ mid ∈ (univ : Finset (Fin 6)).erase outer,
        ∑ inner ∈ ((univ : Finset (Fin 6)).erase outer).erase mid,
          projGapAt (projectionOfDesign design) outer mid inner
      = 2 * (36 * projectionOfDesign design outer outer - 46) := by
  classical
  have hbody : ∀ mid ∈ (univ : Finset (Fin 6)).erase outer,
      ∑ inner ∈ ((univ : Finset (Fin 6)).erase outer).erase mid,
          projGapAt (projectionOfDesign design) outer mid inner
        = 216 * (∑ inner ∈ ((univ : Finset (Fin 6)).erase outer).erase mid,
            (tripleBlock (projectionOfDesign design) outer mid inner).det)
          - ∑ inner ∈ ((univ : Finset (Fin 6)).erase outer).erase mid,
            projThresholdAt (projectionOfDesign design) outer mid inner := by
    intro mid _
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun _ _ => rfl
  rw [Finset.sum_congr rfl hbody, Finset.sum_sub_distrib, ← Finset.mul_sum,
    sum_tripleBlockDet_through design outer, sum_projThreshold_through design outer]
  ring

/-- **THE GAP TOTAL.**  Over all ordered distinct triples the gap adds to `-336`,
which is six times `-56`.  Averaging is dead, and this is the exact size of the
deficit it has to beat. -/
theorem sum_projGap :
    ∑ outer : Fin 6, ∑ mid ∈ (univ : Finset (Fin 6)).erase outer,
        ∑ inner ∈ ((univ : Finset (Fin 6)).erase outer).erase mid,
          projGapAt (projectionOfDesign design) outer mid inner
      = -336 := by
  classical
  have hbody : ∀ outer ∈ (univ : Finset (Fin 6)),
      ∑ mid ∈ (univ : Finset (Fin 6)).erase outer,
        ∑ inner ∈ ((univ : Finset (Fin 6)).erase outer).erase mid,
          projGapAt (projectionOfDesign design) outer mid inner
        = 72 * projectionOfDesign design outer outer + (-92 : ℝ) := by
    intro outer _
    rw [sum_projGap_through design outer]; ring
  rw [Finset.sum_congr rfl hbody, Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, proj_trace design]
  ring

end Marginals

/-! ## 7. The one-point marginal can never certify

Every diagonal entry of a projection lies in the unit interval, so the label
marginal is bounded above by `-20`.  The one-label pigeonhole is dead by theorem. -/

section OneNoGo

variable (design : WeightedDesign 6 3)

/-- **THE ONE-POINT NO-GO.**  The gap marginal through a label is at most `-20`, at
every design and every label, because a projection's diagonal never exceeds one.
So no pigeonhole over the triples through a single label can ever produce a
dominating selection. -/
theorem sum_projGap_through_neg (outer : Fin 6) :
    ∑ mid ∈ (univ : Finset (Fin 6)).erase outer,
        ∑ inner ∈ ((univ : Finset (Fin 6)).erase outer).erase mid,
          projGapAt (projectionOfDesign design) outer mid inner
      ≤ -20 := by
  have hdiag : projectionOfDesign design outer outer ≤ 1 :=
    diag_le_one_of_symm_idempotent (projectionOfDesign design)
      (projectionOfDesign_transpose design) (projectionOfDesign_mul_self design) outer
  rw [sum_projGap_through design outer]
  linarith

/-- The one-point bound is attained only at a saturated label. -/
theorem sum_projGap_through_eq_neg_twenty_iff (outer : Fin 6) :
    ∑ mid ∈ (univ : Finset (Fin 6)).erase outer,
        ∑ inner ∈ ((univ : Finset (Fin 6)).erase outer).erase mid,
          projGapAt (projectionOfDesign design) outer mid inner = -20
      ↔ projectionOfDesign design outer outer = 1 := by
  rw [sum_projGap_through design outer]
  constructor <;> intro h <;> linarith

end OneNoGo

/-! ## 8. The two-point marginal, and the certificate it carries -/

section TwoPoint

variable (design : WeightedDesign 6 3)

/-- **THE TWO-POINT CERTIFICATE.**  A positive pair marginal forces a positive
third minor somewhere through that pair.  This is the pigeonhole the one-point
marginal cannot support. -/
theorem exists_pos_projGap_of_pairMarginal_pos (outer mid : Fin 6)
    (hmid : mid ∈ (univ : Finset (Fin 6)).erase outer)
    (hpos : 0 < 144 * pairMinorAt (projectionOfDesign design) outer mid + 14
      - 54 * (projectionOfDesign design outer outer
          + projectionOfDesign design mid mid)) :
    ∃ inner ∈ ((univ : Finset (Fin 6)).erase outer).erase mid,
      0 < projGapAt (projectionOfDesign design) outer mid inner := by
  classical
  have hsum : (0 : ℝ) < ∑ inner ∈ ((univ : Finset (Fin 6)).erase outer).erase mid,
      projGapAt (projectionOfDesign design) outer mid inner := by
    rw [sum_projGap_through_pair design outer mid hmid]; linarith
  have hzero : ∑ _inner ∈ ((univ : Finset (Fin 6)).erase outer).erase mid, (0 : ℝ) = 0 :=
    Finset.sum_const_zero
  obtain ⟨inner, hinner, hlt⟩ :=
    Finset.exists_lt_of_sum_lt (s := ((univ : Finset (Fin 6)).erase outer).erase mid)
      (f := fun _ => (0 : ℝ))
      (g := fun inner => projGapAt (projectionOfDesign design) outer mid inner)
      (by rw [hzero]; exact hsum)
  exact ⟨inner, hinner, hlt⟩

/-- The pair minor is bounded below by the two leverages once the row-energy law
prices the off-diagonal square.  This is what removes the off-diagonal entry from
the certificate. -/
theorem sq_projectionEntry_le_rowEnergy (outer mid : Fin 6) (hne : mid ≠ outer) :
    projectionOfDesign design outer mid ^ 2
      ≤ projectionOfDesign design outer outer
        * (1 - projectionOfDesign design outer outer) := by
  classical
  have hmem : mid ∈ (univ : Finset (Fin 6)).erase outer :=
    Finset.mem_erase.mpr ⟨hne, Finset.mem_univ mid⟩
  have herase := sum_erase_sq_projectionRow design outer
  have hsplit := Finset.add_sum_erase ((univ : Finset (Fin 6)).erase outer)
    (fun other : Fin 6 => projectionOfDesign design outer other ^ 2) hmem
  have hrest : 0 ≤ ∑ other ∈ ((univ : Finset (Fin 6)).erase outer).erase mid,
      projectionOfDesign design outer other ^ 2 :=
    Finset.sum_nonneg fun other _ => sq_nonneg _
  nlinarith [hsplit, herase, hrest]

theorem pairMinorAt_ge_of_rowEnergy (outer mid : Fin 6) (hne : mid ≠ outer) :
    projectionOfDesign design outer outer * projectionOfDesign design mid mid
        - projectionOfDesign design outer outer
          * (1 - projectionOfDesign design outer outer)
      ≤ pairMinorAt (projectionOfDesign design) outer mid := by
  have hterm := sq_projectionEntry_le_rowEnergy design outer mid hne
  simp only [pairMinorAt]
  nlinarith [hterm]

/-- **THE CERTIFICATE THAT READS THE DIAGONAL ALONE.**  Two labels of leverage at
least `7/8` force a positive third minor through them.  The off-diagonal entry is
eliminated by the row-energy law, and the sign of the triple product is never
consulted.

This is the first certificate in this campaign whose hypothesis is a condition on
the leverage diagonal.  It does not contradict
`Gtz.margin_not_determined_by_leverage_diagonal`: the diagonal cannot COMPUTE the
margin, but it can certify in a corner, and this is the corner. -/
theorem exists_pos_projGap_of_two_heavy (outer mid : Fin 6)
    (hmid : mid ∈ (univ : Finset (Fin 6)).erase outer)
    (houter : 7 / 8 ≤ projectionOfDesign design outer outer)
    (hmidHeavy : 7 / 8 ≤ projectionOfDesign design mid mid) :
    ∃ inner ∈ ((univ : Finset (Fin 6)).erase outer).erase mid,
      0 < projGapAt (projectionOfDesign design) outer mid inner := by
  classical
  have hne : mid ≠ outer := (Finset.mem_erase.mp hmid).1
  have hOuterLe : projectionOfDesign design outer outer ≤ 1 :=
    diag_le_one_of_symm_idempotent (projectionOfDesign design)
      (projectionOfDesign_transpose design) (projectionOfDesign_mul_self design) outer
  have hMidLe : projectionOfDesign design mid mid ≤ 1 :=
    diag_le_one_of_symm_idempotent (projectionOfDesign design)
      (projectionOfDesign_transpose design) (projectionOfDesign_mul_self design) mid
  have hminor := pairMinorAt_ge_of_rowEnergy design outer mid hne
  refine exists_pos_projGap_of_pairMarginal_pos design outer mid hmid ?_
  nlinarith [hminor, houter, hmidHeavy, hOuterLe, hMidLe]

/-- The certificate is not vacuous on the leverage side: the profile it asks for is
compatible with the trace.  Two labels at `7/8` leave `5/4` for the other four. -/
theorem two_heavy_trace_compatible :
    (7 : ℝ) / 8 + 7 / 8 + 4 * (5 / 16) = 3 := by norm_num

end TwoPoint

/-! ## 9. The flat stratum

At uniform leverage the threshold reads only the triple's own pairing energy, and
the gap reads that energy together with the triple product.  The flat objective is
therefore a pure spread statement, and the threshold is constant exactly when the
energy is. -/

section Flat

variable {form : Matrix (Fin size) (Fin size) ℝ}

/-- The pairing energy of a selection, read on a bare form.  The design-level
version is the landed `Gtz.tripleEnergyAt`, and `Gtz.blockEnergyAt_projection`
bridges the two. -/
def blockEnergyAt (form : Matrix (Fin size) (Fin size) ℝ)
    (first second third : Fin size) : ℝ :=
  form first second ^ 2 + form first third ^ 2 + form second third ^ 2

/-- The pairing product of a selection: the only genuinely three-local quantity in
the whole split, and the reason the bracket has no closed-form marginals. -/
def blockProductAt (form : Matrix (Fin size) (Fin size) ℝ)
    (first second third : Fin size) : ℝ :=
  form first second * form first third * form second third

/-- The bare-form energy is the landed design-level energy. -/
theorem blockEnergyAt_projection (design : WeightedDesign size rank)
    (first second third : Fin size) :
    blockEnergyAt (projectionOfDesign design) first second third
      = tripleEnergyAt design first second third := rfl

/-- **THE THRESHOLD ON THE FLAT STRATUM.**  At uniform leverage one half the
threshold reads only the triple's own pairing energy. -/
theorem projThresholdAt_of_flat (first second third : Fin size)
    (h1 : form first first = 1 / 2) (h2 : form second second = 1 / 2)
    (h3 : form third third = 1 / 2) :
    projThresholdAt form first second third = 19 - 36 * blockEnergyAt form first second third := by
  rw [projThresholdAt, blockEnergyAt, pairMinorAt, pairMinorAt, pairMinorAt, h1, h2, h3]
  ring

/-- **THE GAP ON THE FLAT STRATUM.**  Energy against product, with no other data.
The whole flat objective is the statement that some selection has
`432 * product > 72 * energy - 8`. -/
theorem projGapAt_of_flat (hsymmetric : formᵀ = form) (first second third : Fin size)
    (h1 : form first first = 1 / 2) (h2 : form second second = 1 / 2)
    (h3 : form third third = 1 / 2) :
    projGapAt form first second third
      = 8 - 72 * blockEnergyAt form first second third
        + 432 * blockProductAt form first second third := by
  rw [projGapAt, projThresholdAt, det_tripleBlock form hsymmetric, blockEnergyAt,
    blockProductAt, pairMinorAt, pairMinorAt, pairMinorAt, h1, h2, h3]
  ring

/-- **CONSTANCY OF THE THRESHOLD IS CONSTANCY OF THE ENERGY.**  On the flat stratum
the threshold separates two selections exactly when their pairing energies differ,
so flatness alone does NOT force a constant threshold. -/
theorem projThresholdAt_eq_iff_energy_eq_of_flat
    (first second third firstAlt secondAlt thirdAlt : Fin size)
    (h1 : form first first = 1 / 2) (h2 : form second second = 1 / 2)
    (h3 : form third third = 1 / 2) (h1' : form firstAlt firstAlt = 1 / 2)
    (h2' : form secondAlt secondAlt = 1 / 2) (h3' : form thirdAlt thirdAlt = 1 / 2) :
    projThresholdAt form first second third = projThresholdAt form firstAlt secondAlt thirdAlt
      ↔ blockEnergyAt form first second third
        = blockEnergyAt form firstAlt secondAlt thirdAlt := by
  rw [projThresholdAt_of_flat first second third h1 h2 h3,
    projThresholdAt_of_flat firstAlt secondAlt thirdAlt h1' h2' h3']
  constructor <;> intro h <;> linarith

/-- **THE CONSTANT IS FORCED BY THE TOTAL.**  If the threshold takes one value at
every ordered distinct triple, that value is `68/5` -- the icosahedral `13.6`.  The
number is a consequence of the total alone and is not special to the
icosahedron. -/
theorem constant_projThreshold_eq (design : WeightedDesign 6 3) (value : ℝ)
    (hconst : ∀ outer : Fin 6, ∀ mid ∈ (univ : Finset (Fin 6)).erase outer,
      ∀ inner ∈ ((univ : Finset (Fin 6)).erase outer).erase mid,
        projThresholdAt (projectionOfDesign design) outer mid inner = value) :
    value = 68 / 5 := by
  classical
  have htotal := sum_projThreshold design
  have hcount : ∑ outer : Fin 6, ∑ mid ∈ (univ : Finset (Fin 6)).erase outer,
      ∑ inner ∈ ((univ : Finset (Fin 6)).erase outer).erase mid,
        projThresholdAt (projectionOfDesign design) outer mid inner
      = 120 * value := by
    have hinner : ∀ outer : Fin 6, ∀ mid ∈ (univ : Finset (Fin 6)).erase outer,
        ∑ inner ∈ ((univ : Finset (Fin 6)).erase outer).erase mid,
          projThresholdAt (projectionOfDesign design) outer mid inner = 4 * value := by
      intro outer mid hmid
      rw [Finset.sum_congr rfl fun inner hinner => hconst outer mid hmid inner hinner,
        Finset.sum_const, card_erase_two outer mid hmid]
      push_cast; ring
    have houter : ∀ outer : Fin 6,
        ∑ mid ∈ (univ : Finset (Fin 6)).erase outer,
          ∑ inner ∈ ((univ : Finset (Fin 6)).erase outer).erase mid,
            projThresholdAt (projectionOfDesign design) outer mid inner = 20 * value := by
      intro outer
      rw [Finset.sum_congr rfl fun mid hmid => hinner outer mid hmid, Finset.sum_const,
        card_erase_one outer]
      push_cast; ring
    rw [Finset.sum_congr rfl fun outer _ => houter outer, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin]
    ring
  rw [hcount] at htotal
  linarith

end Flat

/-! ## 10. The consumer

The gap is the third Sylvester minor of the whitened Gram at uniform weight, so a
positive gap together with the two smaller minors is domination.  The threshold
being sign-free is what makes it complete on the incoherent side. -/

section Consumer

variable (design : WeightedDesign 6 3)

/-- **THE OBJECTIVE, MARGINALIZED.**  Some ordered distinct triple has a positive
gap as soon as some pair carries a positive pair marginal.  Combined with the
one-point no-go, this says exactly where a pigeonhole can live: at level two and
nowhere lower. -/
theorem exists_pos_projGap_of_exists_pairMarginal_pos
    (hpair : ∃ outer : Fin 6, ∃ mid ∈ (univ : Finset (Fin 6)).erase outer,
      0 < 144 * pairMinorAt (projectionOfDesign design) outer mid + 14
        - 54 * (projectionOfDesign design outer outer
            + projectionOfDesign design mid mid)) :
    ∃ outer : Fin 6, ∃ mid ∈ (univ : Finset (Fin 6)).erase outer,
      ∃ inner ∈ ((univ : Finset (Fin 6)).erase outer).erase mid,
        0 < projGapAt (projectionOfDesign design) outer mid inner := by
  obtain ⟨outer, mid, hmid, hpos⟩ := hpair
  exact ⟨outer, mid, hmid, exists_pos_projGap_of_pairMarginal_pos design outer mid hmid hpos⟩

/-- The shifted three-slot block at uniform weight: the matrix the objective asks
to be positive definite.  This is `Gtz.projectionBlockGap` written on an explicit
ordered pick instead of a sorted `Finset`. -/
noncomputable def tripleBlockGapAt (form : Matrix (Fin size) (Fin size) ℝ)
    (first second third : Fin size) : Matrix (Fin 3) (Fin 3) ℝ :=
  tripleBlock form first second third - Matrix.diagonal (fun _ => (1 : ℝ) / 6)

theorem tripleBlockGapAt_zero_zero (form : Matrix (Fin size) (Fin size) ℝ)
    (first second third : Fin size) :
    tripleBlockGapAt form first second third 0 0 = form first first - 1 / 6 := by
  simp [tripleBlockGapAt, tripleBlock, Matrix.diagonal]

theorem tripleBlockGapAt_zero_one (form : Matrix (Fin size) (Fin size) ℝ)
    (first second third : Fin size) :
    tripleBlockGapAt form first second third 0 1 = form first second := by
  simp [tripleBlockGapAt, tripleBlock, Matrix.diagonal]

theorem tripleBlockGapAt_one_one (form : Matrix (Fin size) (Fin size) ℝ)
    (first second third : Fin size) :
    tripleBlockGapAt form first second third 1 1 = form second second - 1 / 6 := by
  simp [tripleBlockGapAt, tripleBlock, Matrix.diagonal]

theorem tripleBlockGapAt_two_two (form : Matrix (Fin size) (Fin size) ℝ)
    (first second third : Fin size) :
    tripleBlockGapAt form first second third 2 2 = form third third - 1 / 6 := by
  simp [tripleBlockGapAt, tripleBlock, Matrix.diagonal]

theorem tripleBlockGapAt_zero_two (form : Matrix (Fin size) (Fin size) ℝ)
    (first second third : Fin size) :
    tripleBlockGapAt form first second third 0 2 = form first third := by
  simp [tripleBlockGapAt, tripleBlock, Matrix.diagonal]

theorem tripleBlockGapAt_one_two (form : Matrix (Fin size) (Fin size) ℝ)
    (first second third : Fin size) :
    tripleBlockGapAt form first second third 1 2 = form second third := by
  simp [tripleBlockGapAt, tripleBlock, Matrix.diagonal]

theorem tripleBlockGapAt_one_zero (form : Matrix (Fin size) (Fin size) ℝ)
    (first second third : Fin size) :
    tripleBlockGapAt form first second third 1 0 = form second first := by
  simp [tripleBlockGapAt, tripleBlock, Matrix.diagonal]

theorem tripleBlockGapAt_two_zero (form : Matrix (Fin size) (Fin size) ℝ)
    (first second third : Fin size) :
    tripleBlockGapAt form first second third 2 0 = form third first := by
  simp [tripleBlockGapAt, tripleBlock, Matrix.diagonal]

theorem tripleBlockGapAt_two_one (form : Matrix (Fin size) (Fin size) ℝ)
    (first second third : Fin size) :
    tripleBlockGapAt form first second third 2 1 = form third second := by
  simp [tripleBlockGapAt, tripleBlock, Matrix.diagonal]

/-- **THE DETERMINANT OF THE SHIFTED BLOCK IS THE GAP, SCALED.**  So the third
Sylvester condition on the objective's own matrix is exactly `0 < projGapAt`. -/
theorem det_tripleBlockGapAt (form : Matrix (Fin size) (Fin size) ℝ)
    (hsymmetric : formᵀ = form) (first second third : Fin size) :
    (tripleBlockGapAt form first second third).det
      = projGapAt form first second third / 216 := by
  have hshift := projGapAt_eq_shiftedMinor hsymmetric first second third
  rw [Matrix.det_fin_three, tripleBlockGapAt_zero_zero, tripleBlockGapAt_zero_one,
    tripleBlockGapAt_zero_two, tripleBlockGapAt_one_zero, tripleBlockGapAt_one_one,
    tripleBlockGapAt_one_two, tripleBlockGapAt_two_zero, tripleBlockGapAt_two_one,
    tripleBlockGapAt_two_two, entry_flip hsymmetric first second,
    entry_flip hsymmetric first third, entry_flip hsymmetric second third, hshift]
  ring

theorem transpose_tripleBlockGapAt (form : Matrix (Fin size) (Fin size) ℝ)
    (hsymmetric : formᵀ = form) (first second third : Fin size) :
    (tripleBlockGapAt form first second third)ᵀ = tripleBlockGapAt form first second third := by
  ext slotLeft slotRight
  simp only [Matrix.transpose_apply, tripleBlockGapAt, Matrix.sub_apply, tripleBlock,
    Matrix.submatrix_apply, Matrix.diagonal_apply]
  rw [entry_flip hsymmetric]
  by_cases hEq : slotLeft = slotRight
  · subst hEq; rfl
  · simp [hEq, Ne.symm hEq]

/-- **THE CERTIFICATE REACHES POSITIVE DEFINITENESS.**  Two labels of leverage at
least `7/8` force a whole ordered triple through them whose shifted block is
positive definite -- not merely a positive third minor.

The first two leading minors are supplied by the heavy pair alone: the diagonal
entry clears `17/24`, and the two-by-two minor clears `(17/24)^2 - 7/64` once the
row-energy law prices the off-diagonal square.  The third is the marginal
certificate.  So the objective's own predicate holds at that selection. -/
theorem exists_posDef_tripleBlockGapAt_of_two_heavy (outer mid : Fin 6)
    (hmid : mid ∈ (univ : Finset (Fin 6)).erase outer)
    (houter : 7 / 8 ≤ projectionOfDesign design outer outer)
    (hmidHeavy : 7 / 8 ≤ projectionOfDesign design mid mid) :
    ∃ inner ∈ ((univ : Finset (Fin 6)).erase outer).erase mid,
      (tripleBlockGapAt (projectionOfDesign design) outer mid inner).PosDef := by
  classical
  obtain ⟨inner, hinner, hgap⟩ :=
    exists_pos_projGap_of_two_heavy design outer mid hmid houter hmidHeavy
  refine ⟨inner, hinner, ?_⟩
  have hne : mid ≠ outer := (Finset.mem_erase.mp hmid).1
  have hsymm := proj_symm design
  have hOuterLe : projectionOfDesign design outer outer ≤ 1 :=
    diag_le_one_of_symm_idempotent (projectionOfDesign design)
      (projectionOfDesign_transpose design) (projectionOfDesign_mul_self design) outer
  have hsq := sq_projectionEntry_le_rowEnergy design outer mid hne
  rw [posDef_finThree_iff_leadingMinors _ (transpose_tripleBlockGapAt _ hsymm outer mid inner)]
  refine ⟨?_, ?_, ?_⟩
  · rw [tripleBlockGapAt_zero_zero]; linarith
  · rw [tripleBlockGapAt_zero_zero, tripleBlockGapAt_one_one, tripleBlockGapAt_zero_one]
    nlinarith [hsq, houter, hmidHeavy, hOuterLe]
  · have hdet := det_tripleBlockGapAt (projectionOfDesign design) hsymm outer mid inner
    rw [Matrix.det_fin_three, tripleBlockGapAt_zero_zero, tripleBlockGapAt_zero_one,
      tripleBlockGapAt_zero_two, tripleBlockGapAt_one_zero, tripleBlockGapAt_one_one,
      tripleBlockGapAt_one_two, tripleBlockGapAt_two_zero, tripleBlockGapAt_two_one,
      tripleBlockGapAt_two_two, entry_flip hsymm outer mid, entry_flip hsymm outer inner,
      entry_flip hsymm mid inner] at hdet
    rw [tripleBlockGapAt_zero_zero, tripleBlockGapAt_zero_one, tripleBlockGapAt_zero_two,
      tripleBlockGapAt_one_one, tripleBlockGapAt_one_two, tripleBlockGapAt_two_two]
    nlinarith [hdet, hgap]

/-- **THE UNIFORM-WEIGHT SLICE OF THE OBJECTIVE, DISCHARGED ON THE HEAVY-PAIR
CORNER.**  A design whose weight is uniform and which carries two labels of
leverage at least `7/8` has a card-three selection whose projection block strictly
dominates its weight diagonal.  That is the conclusion
`Gtz.ProjectionBlockSelects` asks for, established under an explicit hypothesis on
the leverage diagonal alone. -/
theorem exists_posDef_block_of_uniform_of_two_heavy (outer mid : Fin 6)
    (hmid : mid ∈ (univ : Finset (Fin 6)).erase outer)
    (huniform : ∀ label : Fin 6, design.weight label = 1 / 6)
    (houter : 7 / 8 ≤ projectionOfDesign design outer outer)
    (hmidHeavy : 7 / 8 ≤ projectionOfDesign design mid mid) :
    ∃ inner ∈ ((univ : Finset (Fin 6)).erase outer).erase mid,
      (tripleBlock (projectionOfDesign design) outer mid inner
        - Matrix.diagonal (fun slot => design.weight (![outer, mid, inner] slot))).PosDef := by
  classical
  obtain ⟨inner, hinner, hposDef⟩ :=
    exists_posDef_tripleBlockGapAt_of_two_heavy design outer mid hmid houter hmidHeavy
  refine ⟨inner, hinner, ?_⟩
  have hdiag : (Matrix.diagonal fun slot => design.weight (![outer, mid, inner] slot))
      = Matrix.diagonal (fun _ : Fin 3 => (1 : ℝ) / 6) := by
    ext slotLeft slotRight
    simp only [Matrix.diagonal_apply]
    by_cases hEq : slotLeft = slotRight
    · subst hEq; simp [huniform]
    · simp [hEq]
  rw [hdiag]
  exact hposDef

/-- **THE TWO-POINT CERTIFICATE IS SILENT ON THE WHOLE FLAT STRATUM.**  At
uniform leverage one half the pair marginal reads `144 * pairMinor - 40`, and a
pair minor there is at most `1/4`, so the marginal never clears zero.  Both landed
extremal points -- the icosahedron and the graphic point of `K4` -- are flat, so
the certificate correctly declines to fire at either.  This is why the corner sits
at `7/8` and not lower, and it is a limitation of the certificate rather than of
the marginal law. -/
theorem pairMarginal_nonpos_of_flat (outer mid : Fin 6)
    (houter : projectionOfDesign design outer outer = 1 / 2)
    (hmidFlat : projectionOfDesign design mid mid = 1 / 2) :
    144 * pairMinorAt (projectionOfDesign design) outer mid + 14
      - 54 * (projectionOfDesign design outer outer
          + projectionOfDesign design mid mid) ≤ 0 := by
  have hminor : pairMinorAt (projectionOfDesign design) outer mid ≤ 1 / 4 := by
    simp only [pairMinorAt, houter, hmidFlat]
    nlinarith [sq_nonneg (projectionOfDesign design outer mid)]
  rw [houter, hmidFlat]
  linarith

/-- The pair marginal in its cleanest equivalent form: the certificate asks the
pair minor to beat a linear function of the two leverages. -/
theorem pairMarginal_pos_iff (outer mid : Fin 6) :
    0 < 144 * pairMinorAt (projectionOfDesign design) outer mid + 14
        - 54 * (projectionOfDesign design outer outer + projectionOfDesign design mid mid)
      ↔ 27 * (projectionOfDesign design outer outer + projectionOfDesign design mid mid) - 7
        < 72 * pairMinorAt (projectionOfDesign design) outer mid := by
  constructor <;> intro h <;> linarith

end Consumer

end Gtz
