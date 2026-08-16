import Gtz.Wave.JointMassThreshold

/-!
# Closing the second-moment theory onto the mass energy

`Gtz.gapSecondMoment_eq` splits the energy of the objective's gap into three
pieces: the mass energy, the cross term, and the threshold energy.  This file
computes the cross term in closed form, so that the mass energy stands alone.

The engine is that a triple block determinant VANISHES whenever two of its three
slots agree.  So every sum weighted by that determinant may be taken over all of
`Fin 6 × Fin 6 × Fin 6` rather than over the distinct triples, and the marginal
laws — which are stated on full sums — apply directly with no `powersetCard`
index matching.  Three forks named that index step as a gap and routed around it.
It is not needed.

The slot symmetry of the block determinant (`Gtz.det_tripleBlock_swap_first_second`
and its two companions) is what lets the same marginal serve all three slots.

The result is `Gtz.jointCrossMoment_eq`:

    jointCrossMoment = 23328 * pairSecondMoment - 7776 * levSecondMoment + 1296

whose proof is the one-point and two-point marginals of the projection
determinantal measure and nothing else.  The threshold is two-local, so the mass
only ever meets it through those two marginals, and both are landed.
-/

namespace Gtz

open Finset Matrix

/-! ## 1. Slot symmetry of the block determinant

A principal block does not know the order of its slots.  The expansion
`Gtz.det_tripleBlock` makes each statement a `ring` identity once the symmetric
form's transposed entries are flipped. -/

section SlotSymmetry

variable {size : ℕ}

private theorem entryFlip {form : Matrix (Fin size) (Fin size) ℝ} (hsymmetric : formᵀ = form)
    (left right : Fin size) : form right left = form left right := by
  have hentry := congrFun (congrFun hsymmetric left) right
  simpa only [Matrix.transpose_apply] using hentry

/-- Swapping the first two slots leaves the block determinant alone. -/
theorem det_tripleBlock_swap_first_second (form : Matrix (Fin size) (Fin size) ℝ)
    (hsymmetric : formᵀ = form) (first second third : Fin size) :
    (tripleBlock form second first third).det
      = (tripleBlock form first second third).det := by
  rw [det_tripleBlock form hsymmetric second first third,
    det_tripleBlock form hsymmetric first second third,
    entryFlip hsymmetric first second]
  ring

/-- Swapping the last two slots leaves the block determinant alone. -/
theorem det_tripleBlock_swap_second_third (form : Matrix (Fin size) (Fin size) ℝ)
    (hsymmetric : formᵀ = form) (first second third : Fin size) :
    (tripleBlock form first third second).det
      = (tripleBlock form first second third).det := by
  rw [det_tripleBlock form hsymmetric first third second,
    det_tripleBlock form hsymmetric first second third,
    entryFlip hsymmetric second third]
  ring

/-- Rotating the slots forward leaves the block determinant alone. -/
theorem det_tripleBlock_rotate (form : Matrix (Fin size) (Fin size) ℝ)
    (hsymmetric : formᵀ = form) (first second third : Fin size) :
    (tripleBlock form second third first).det
      = (tripleBlock form first second third).det := by
  rw [det_tripleBlock form hsymmetric second third first,
    det_tripleBlock form hsymmetric first second third,
    entryFlip hsymmetric first second, entryFlip hsymmetric first third]
  ring

/-- Rotating the slots backward leaves the block determinant alone. -/
theorem det_tripleBlock_rotate_back (form : Matrix (Fin size) (Fin size) ℝ)
    (hsymmetric : formᵀ = form) (first second third : Fin size) :
    (tripleBlock form third first second).det
      = (tripleBlock form first second third).det := by
  rw [det_tripleBlock form hsymmetric third first second,
    det_tripleBlock form hsymmetric first second third,
    entryFlip hsymmetric first third, entryFlip hsymmetric second third]
  ring

/-- A repeat in the FIRST two slots kills the block, which is the case the
landed pair of degeneracy lemmas does not cover. -/
theorem det_tripleBlock_self_mid (form : Matrix (Fin size) (Fin size) ℝ)
    (hsymmetric : formᵀ = form) (first third : Fin size) :
    (tripleBlock form first first third).det = 0 := by
  rw [det_tripleBlock form hsymmetric first first third]
  ring

end SlotSymmetry

/-! ## 2. Every determinant-weighted sum is a full sum

The three degeneracy lemmas say the block determinant vanishes on every diagonal
of the index cube.  So erasing the repeats changes nothing, and the marginal laws
— which quantify over all of `Fin 6` — apply verbatim. -/

section FullSums

variable (design : WeightedDesign 6 3)

private theorem detSelfLeft (first second : Fin 6) :
    (tripleBlock (projectionOfDesign design) first second first).det = 0 :=
  det_tripleBlock_self_left _ (projectionOfDesign_transpose design) first second

private theorem detSelfRight (first second : Fin 6) :
    (tripleBlock (projectionOfDesign design) first second second).det = 0 :=
  det_tripleBlock_self_right _ (projectionOfDesign_transpose design) first second

private theorem detSelfMid (first third : Fin 6) :
    (tripleBlock (projectionOfDesign design) first first third).det = 0 :=
  det_tripleBlock_self_mid _ (projectionOfDesign_transpose design) first third

/-- A determinant-weighted summand extends from the distinct triples to the full
index cube.  The weight may be anything at all. -/
theorem sum_det_weighted_eq_full (weight : Fin 6 → Fin 6 → Fin 6 → ℝ) :
    ∑ outer : Fin 6, ∑ mid ∈ (univ : Finset (Fin 6)).erase outer,
        ∑ inner ∈ ((univ : Finset (Fin 6)).erase outer).erase mid,
          (tripleBlock (projectionOfDesign design) outer mid inner).det
            * weight outer mid inner
      = ∑ outer : Fin 6, ∑ mid : Fin 6, ∑ inner : Fin 6,
          (tripleBlock (projectionOfDesign design) outer mid inner).det
            * weight outer mid inner := by
  classical
  refine Finset.sum_congr rfl fun outer _ => ?_
  have hinner : ∀ mid : Fin 6,
      ∑ inner ∈ ((univ : Finset (Fin 6)).erase outer).erase mid,
          (tripleBlock (projectionOfDesign design) outer mid inner).det
            * weight outer mid inner
        = ∑ inner : Fin 6,
          (tripleBlock (projectionOfDesign design) outer mid inner).det
            * weight outer mid inner := by
    intro mid
    rw [Finset.sum_erase _ (by rw [detSelfRight design outer mid]; ring),
      Finset.sum_erase _ (by rw [detSelfLeft design outer mid]; ring)]
  rw [Finset.sum_congr rfl fun mid _ => hinner mid]
  refine Finset.sum_erase _ ?_
  refine Finset.sum_eq_zero fun inner _ => ?_
  rw [detSelfMid design outer inner]; ring

/-- The cross moment over the full index cube. -/
theorem jointCrossMoment_eq_full :
    jointCrossMoment design
      = ∑ outer : Fin 6, ∑ mid : Fin 6, ∑ inner : Fin 6,
          (tripleBlock (projectionOfDesign design) outer mid inner).det
            * (216 * projThresholdAt (projectionOfDesign design) outer mid inner) := by
  classical
  have hrewrite : ∀ outer mid inner : Fin 6,
      (216 * (tripleBlock (projectionOfDesign design) outer mid inner).det)
          * projThresholdAt (projectionOfDesign design) outer mid inner
        = (tripleBlock (projectionOfDesign design) outer mid inner).det
          * (216 * projThresholdAt (projectionOfDesign design) outer mid inner) := by
    intro outer mid inner; ring
  simp only [jointCrossMoment, hrewrite]
  exact sum_det_weighted_eq_full design
    (fun outer mid inner => 216 * projThresholdAt (projectionOfDesign design) outer mid inner)

/-- The mass energy over the full index cube. -/
theorem massSecondMoment_eq_full :
    massSecondMoment design
      = ∑ outer : Fin 6, ∑ mid : Fin 6, ∑ inner : Fin 6,
          (tripleBlock (projectionOfDesign design) outer mid inner).det
            * (46656 * (tripleBlock (projectionOfDesign design) outer mid inner).det) := by
  classical
  have hrewrite : ∀ outer mid inner : Fin 6,
      (216 * (tripleBlock (projectionOfDesign design) outer mid inner).det) ^ 2
        = (tripleBlock (projectionOfDesign design) outer mid inner).det
          * (46656 * (tripleBlock (projectionOfDesign design) outer mid inner).det) := by
    intro outer mid inner; ring
  simp only [massSecondMoment, hrewrite]
  exact sum_det_weighted_eq_full design
    (fun outer mid inner =>
      46656 * (tripleBlock (projectionOfDesign design) outer mid inner).det)

end FullSums

/-! ## 3. The two marginals at rank three

The two-point marginal carries the coefficient `traceValue - 2`, which is one at
rank three, and the one-point marginal carries `(rank - 2) * (rank - 1)`, which is
two.  Both are landed for a general rank.  These are the `(6, 3)` readings. -/

section Marginals

variable (design : WeightedDesign 6 3)

/-- **THE TWO-POINT MARGINAL AT RANK THREE.**  The block determinants through a
fixed pair total that pair's own minor, with no coefficient. -/
theorem sum_inner_det (first second : Fin 6) :
    ∑ inner : Fin 6, (tripleBlock (projectionOfDesign design) first second inner).det
      = pairMinorAt (projectionOfDesign design) first second := by
  have hmarg := sum_det_tripleBlock_through_pair (projectionOfDesign design)
    (projectionOfDesign_transpose design) (projectionOfDesign_mul_self design)
    (sum_projectionDiagonal_cast design) first second
  rw [hmarg]; norm_num

/-- **THE ONE-POINT MARGINAL AT RANK THREE.**  The block determinants through a
fixed label total twice its leverage, the factor two being the ordered overcount. -/
theorem sum_mid_inner_det (label : Fin 6) :
    ∑ mid : Fin 6, ∑ inner : Fin 6,
        (tripleBlock (projectionOfDesign design) label mid inner).det
      = 2 * projectionOfDesign design label label := by
  have hmarg := sum_sum_det_tripleBlock_through_label design label
  rw [hmarg]; norm_num

/-- The pair-minor energy over the full index square is the landed ordered one,
because a diagonal pair minor vanishes. -/
theorem sum_sq_pairMinor_full :
    ∑ first : Fin 6, ∑ second : Fin 6,
        pairMinorAt (projectionOfDesign design) first second ^ 2
      = pairSecondMoment design := by
  classical
  simp only [pairSecondMoment]
  refine (Finset.sum_congr rfl fun first _ => ?_).symm
  refine Finset.sum_erase _ ?_
  rw [pairMinorAt_self (projectionOfDesign design) first]; ring

end Marginals

/-! ## 4. The six pieces of the cross moment

The threshold is `36` times three pair minors minus `6` times three diagonal
entries plus one.  Weighted by the block determinant, each of those six terms
collapses onto a marginal.  Slot symmetry is what makes the second and third
slots behave like the first. -/

section Pieces

variable (design : WeightedDesign 6 3)

/-- The determinant against the first slot's diagonal entry. -/
theorem sum_det_mul_diag_first :
    ∑ outer : Fin 6, ∑ mid : Fin 6, ∑ inner : Fin 6,
        (tripleBlock (projectionOfDesign design) outer mid inner).det
          * projectionOfDesign design outer outer
      = 2 * levSecondMoment design := by
  classical
  have hstep : ∀ outer : Fin 6,
      ∑ mid : Fin 6, ∑ inner : Fin 6,
          (tripleBlock (projectionOfDesign design) outer mid inner).det
            * projectionOfDesign design outer outer
        = 2 * projectionOfDesign design outer outer ^ 2 := by
    intro outer
    have hpull : ∀ mid : Fin 6,
        ∑ inner : Fin 6, (tripleBlock (projectionOfDesign design) outer mid inner).det
              * projectionOfDesign design outer outer
          = (∑ inner : Fin 6, (tripleBlock (projectionOfDesign design) outer mid inner).det)
              * projectionOfDesign design outer outer := by
      intro mid; rw [Finset.sum_mul]
    rw [Finset.sum_congr rfl fun mid _ => hpull mid, ← Finset.sum_mul,
      sum_mid_inner_det design outer]
    ring
  rw [Finset.sum_congr rfl fun outer _ => hstep outer, ← Finset.mul_sum]
  simp only [levSecondMoment]

/-- The determinant against the second slot's diagonal entry.  The swap of the
first two slots is what turns this into the one-point marginal again. -/
theorem sum_det_mul_diag_second :
    ∑ outer : Fin 6, ∑ mid : Fin 6, ∑ inner : Fin 6,
        (tripleBlock (projectionOfDesign design) outer mid inner).det
          * projectionOfDesign design mid mid
      = 2 * levSecondMoment design := by
  classical
  have hsymm := projectionOfDesign_transpose design
  have hswap : ∀ outer mid inner : Fin 6,
      (tripleBlock (projectionOfDesign design) outer mid inner).det
          * projectionOfDesign design mid mid
        = (tripleBlock (projectionOfDesign design) mid outer inner).det
          * projectionOfDesign design mid mid := by
    intro outer mid inner
    rw [det_tripleBlock_swap_first_second (projectionOfDesign design) hsymm outer mid inner]
  rw [Finset.sum_congr rfl fun outer _ => Finset.sum_congr rfl fun mid _ =>
    Finset.sum_congr rfl fun inner _ => hswap outer mid inner]
  rw [Finset.sum_comm]
  have hstep : ∀ mid : Fin 6,
      ∑ outer : Fin 6, ∑ inner : Fin 6,
          (tripleBlock (projectionOfDesign design) mid outer inner).det
            * projectionOfDesign design mid mid
        = 2 * projectionOfDesign design mid mid ^ 2 := by
    intro mid
    have hpull : ∀ outer : Fin 6,
        ∑ inner : Fin 6, (tripleBlock (projectionOfDesign design) mid outer inner).det
              * projectionOfDesign design mid mid
          = (∑ inner : Fin 6, (tripleBlock (projectionOfDesign design) mid outer inner).det)
              * projectionOfDesign design mid mid := by
      intro outer; rw [Finset.sum_mul]
    rw [Finset.sum_congr rfl fun outer _ => hpull outer, ← Finset.sum_mul,
      sum_mid_inner_det design mid]
    ring
  rw [Finset.sum_congr rfl fun mid _ => hstep mid, ← Finset.mul_sum]
  simp only [levSecondMoment]

/-- The determinant against the third slot's diagonal entry, through the backward
rotation. -/
theorem sum_det_mul_diag_third :
    ∑ outer : Fin 6, ∑ mid : Fin 6, ∑ inner : Fin 6,
        (tripleBlock (projectionOfDesign design) outer mid inner).det
          * projectionOfDesign design inner inner
      = 2 * levSecondMoment design := by
  classical
  have hsymm := projectionOfDesign_transpose design
  have hrot : ∀ outer mid inner : Fin 6,
      (tripleBlock (projectionOfDesign design) outer mid inner).det
          * projectionOfDesign design inner inner
        = (tripleBlock (projectionOfDesign design) inner outer mid).det
          * projectionOfDesign design inner inner := by
    intro outer mid inner
    rw [det_tripleBlock_rotate_back (projectionOfDesign design) hsymm outer mid inner]
  rw [Finset.sum_congr rfl fun outer _ => Finset.sum_congr rfl fun mid _ =>
    Finset.sum_congr rfl fun inner _ => hrot outer mid inner]
  have hinner : ∀ outer : Fin 6,
      ∑ mid : Fin 6, ∑ inner : Fin 6,
          (tripleBlock (projectionOfDesign design) inner outer mid).det
            * projectionOfDesign design inner inner
        = ∑ inner : Fin 6, ∑ mid : Fin 6,
          (tripleBlock (projectionOfDesign design) inner outer mid).det
            * projectionOfDesign design inner inner := fun _ => Finset.sum_comm
  rw [Finset.sum_congr rfl fun outer _ => hinner outer, Finset.sum_comm]
  have hstep : ∀ inner : Fin 6,
      ∑ outer : Fin 6, ∑ mid : Fin 6,
          (tripleBlock (projectionOfDesign design) inner outer mid).det
            * projectionOfDesign design inner inner
        = 2 * projectionOfDesign design inner inner ^ 2 := by
    intro inner
    have hpull : ∀ outer : Fin 6,
        ∑ mid : Fin 6, (tripleBlock (projectionOfDesign design) inner outer mid).det
              * projectionOfDesign design inner inner
          = (∑ mid : Fin 6, (tripleBlock (projectionOfDesign design) inner outer mid).det)
              * projectionOfDesign design inner inner := by
      intro outer; rw [Finset.sum_mul]
    rw [Finset.sum_congr rfl fun outer _ => hpull outer, ← Finset.sum_mul,
      sum_mid_inner_det design inner]
    ring
  rw [Finset.sum_congr rfl fun inner _ => hstep inner, ← Finset.mul_sum]
  simp only [levSecondMoment]

/-- The determinant against the pair minor of the first two slots.  This is the
two-point marginal meeting itself, which is why the answer is an energy. -/
theorem sum_det_mul_pairMinor_first_second :
    ∑ outer : Fin 6, ∑ mid : Fin 6, ∑ inner : Fin 6,
        (tripleBlock (projectionOfDesign design) outer mid inner).det
          * pairMinorAt (projectionOfDesign design) outer mid
      = pairSecondMoment design := by
  classical
  have hstep : ∀ outer mid : Fin 6,
      ∑ inner : Fin 6, (tripleBlock (projectionOfDesign design) outer mid inner).det
            * pairMinorAt (projectionOfDesign design) outer mid
        = pairMinorAt (projectionOfDesign design) outer mid ^ 2 := by
    intro outer mid
    rw [← Finset.sum_mul, sum_inner_det design outer mid]; ring
  rw [Finset.sum_congr rfl fun outer _ =>
    Finset.sum_congr rfl fun mid _ => hstep outer mid]
  exact sum_sq_pairMinor_full design

/-- The determinant against the pair minor of the outer and inner slots, through
the swap of the last two. -/
theorem sum_det_mul_pairMinor_first_third :
    ∑ outer : Fin 6, ∑ mid : Fin 6, ∑ inner : Fin 6,
        (tripleBlock (projectionOfDesign design) outer mid inner).det
          * pairMinorAt (projectionOfDesign design) outer inner
      = pairSecondMoment design := by
  classical
  have hsymm := projectionOfDesign_transpose design
  have hswap : ∀ outer mid inner : Fin 6,
      (tripleBlock (projectionOfDesign design) outer mid inner).det
          * pairMinorAt (projectionOfDesign design) outer inner
        = (tripleBlock (projectionOfDesign design) outer inner mid).det
          * pairMinorAt (projectionOfDesign design) outer inner := by
    intro outer mid inner
    rw [det_tripleBlock_swap_second_third (projectionOfDesign design) hsymm outer mid inner]
  rw [Finset.sum_congr rfl fun outer _ => Finset.sum_congr rfl fun mid _ =>
    Finset.sum_congr rfl fun inner _ => hswap outer mid inner]
  have hcomm : ∀ outer : Fin 6,
      ∑ mid : Fin 6, ∑ inner : Fin 6,
          (tripleBlock (projectionOfDesign design) outer inner mid).det
            * pairMinorAt (projectionOfDesign design) outer inner
        = ∑ inner : Fin 6, ∑ mid : Fin 6,
          (tripleBlock (projectionOfDesign design) outer inner mid).det
            * pairMinorAt (projectionOfDesign design) outer inner := fun _ => Finset.sum_comm
  rw [Finset.sum_congr rfl fun outer _ => hcomm outer]
  have hstep : ∀ outer inner : Fin 6,
      ∑ mid : Fin 6, (tripleBlock (projectionOfDesign design) outer inner mid).det
            * pairMinorAt (projectionOfDesign design) outer inner
        = pairMinorAt (projectionOfDesign design) outer inner ^ 2 := by
    intro outer inner
    rw [← Finset.sum_mul, sum_inner_det design outer inner]; ring
  rw [Finset.sum_congr rfl fun outer _ =>
    Finset.sum_congr rfl fun inner _ => hstep outer inner]
  exact sum_sq_pairMinor_full design

/-- The determinant against the pair minor of the last two slots, through the
forward rotation. -/
theorem sum_det_mul_pairMinor_second_third :
    ∑ outer : Fin 6, ∑ mid : Fin 6, ∑ inner : Fin 6,
        (tripleBlock (projectionOfDesign design) outer mid inner).det
          * pairMinorAt (projectionOfDesign design) mid inner
      = pairSecondMoment design := by
  classical
  have hsymm := projectionOfDesign_transpose design
  have hrot : ∀ outer mid inner : Fin 6,
      (tripleBlock (projectionOfDesign design) outer mid inner).det
          * pairMinorAt (projectionOfDesign design) mid inner
        = (tripleBlock (projectionOfDesign design) mid inner outer).det
          * pairMinorAt (projectionOfDesign design) mid inner := by
    intro outer mid inner
    rw [det_tripleBlock_rotate (projectionOfDesign design) hsymm outer mid inner]
  rw [Finset.sum_congr rfl fun outer _ => Finset.sum_congr rfl fun mid _ =>
    Finset.sum_congr rfl fun inner _ => hrot outer mid inner]
  rw [Finset.sum_comm]
  have hstep : ∀ mid : Fin 6,
      ∑ outer : Fin 6, ∑ inner : Fin 6,
          (tripleBlock (projectionOfDesign design) mid inner outer).det
            * pairMinorAt (projectionOfDesign design) mid inner
        = ∑ inner : Fin 6, pairMinorAt (projectionOfDesign design) mid inner ^ 2 := by
    intro mid
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun inner _ => ?_
    rw [← Finset.sum_mul, sum_inner_det design mid inner]; ring
  rw [Finset.sum_congr rfl fun mid _ => hstep mid]
  exact sum_sq_pairMinor_full design

end Pieces

/-! ## 5. The cross moment in closed form

Assembling the six pieces against the threshold's own shape gives the cross term
as a polynomial in the two invariants.  Nothing else survives. -/

section CrossMoment

variable (design : WeightedDesign 6 3)

/-- **THE CROSS MOMENT IS CLOSED FORM.**  Two invariants and a constant.  Every
step is a marginal of the projection determinantal measure: the block
determinants through a pair total that pair's minor, and through a label total
twice its leverage. -/
theorem jointCrossMoment_eq :
    jointCrossMoment design
      = 23328 * pairSecondMoment design - 7776 * levSecondMoment design + 1296 := by
  classical
  rw [jointCrossMoment_eq_full design]
  have hexpand : ∀ outer mid inner : Fin 6,
      (tripleBlock (projectionOfDesign design) outer mid inner).det
          * (216 * projThresholdAt (projectionOfDesign design) outer mid inner)
        = 7776 * ((tripleBlock (projectionOfDesign design) outer mid inner).det
              * pairMinorAt (projectionOfDesign design) outer mid)
          + 7776 * ((tripleBlock (projectionOfDesign design) outer mid inner).det
              * pairMinorAt (projectionOfDesign design) outer inner)
          + 7776 * ((tripleBlock (projectionOfDesign design) outer mid inner).det
              * pairMinorAt (projectionOfDesign design) mid inner)
          - 1296 * ((tripleBlock (projectionOfDesign design) outer mid inner).det
              * projectionOfDesign design outer outer)
          - 1296 * ((tripleBlock (projectionOfDesign design) outer mid inner).det
              * projectionOfDesign design mid mid)
          - 1296 * ((tripleBlock (projectionOfDesign design) outer mid inner).det
              * projectionOfDesign design inner inner)
          + 216 * (tripleBlock (projectionOfDesign design) outer mid inner).det := by
    intro outer mid inner
    rw [projThresholdAt]; ring
  simp only [hexpand, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [sum_det_mul_pairMinor_first_second design, sum_det_mul_pairMinor_first_third design,
    sum_det_mul_pairMinor_second_third design, sum_det_mul_diag_first design,
    sum_det_mul_diag_second design, sum_det_mul_diag_third design,
    sum_sum_sum_det_tripleBlock_sixThree design]
  ring

/-- **THE MASS ENERGY, WITH THE CROSS TERM DISCHARGED.**  Everything on the right
except the gap energy and the threshold energy is closed form. -/
theorem massSecondMoment_eq_cross_closed :
    massSecondMoment design
      = gapSecondMoment design + thresholdSecondMoment design
        - 2 * thresholdSecondMoment design
        + 2 * (23328 * pairSecondMoment design - 7776 * levSecondMoment design + 1296)
        + thresholdSecondMoment design - thresholdSecondMoment design := by
  rw [massSecondMoment_eq design, jointCrossMoment_eq design]; ring

/-- The same, stated without the cancelling threshold terms. -/
theorem massSecondMoment_eq_gap_add_closed :
    massSecondMoment design
      = gapSecondMoment design
        + (46656 * pairSecondMoment design - 15552 * levSecondMoment design + 2592)
        - thresholdSecondMoment design := by
  rw [massSecondMoment_eq design, jointCrossMoment_eq design]; ring

end CrossMoment

/-! ## 6. What the closure buys

Both remaining quantities are energies, hence non-negative, and the closed cross
term therefore brackets them against each other. -/

section Consequences

variable (design : WeightedDesign 6 3)

/-- The threshold energy is a sum of squares. -/
theorem thresholdSecondMoment_nonneg : 0 ≤ thresholdSecondMoment design :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- **THE CROSS TERM IS BRACKETED BY THE TWO ENERGIES.**  Cauchy-Schwarz on the
ordered triples, in the form that needs no square root: twice the cross term never
exceeds the sum of the two energies, because the gap energy is a sum of squares. -/
theorem two_mul_jointCrossMoment_le :
    2 * jointCrossMoment design
      ≤ massSecondMoment design + thresholdSecondMoment design := by
  have hsplit := gapSecondMoment_eq design
  have hnonneg := gapSecondMoment_nonneg design
  linarith [hsplit, hnonneg]

/-- **THE CLOSED FORM OF THAT BRACKET.**  The mass energy plus the threshold
energy is at least an explicit polynomial in the two invariants. -/
theorem massSecondMoment_add_thresholdSecondMoment_ge :
    46656 * pairSecondMoment design - 15552 * levSecondMoment design + 2592
      ≤ massSecondMoment design + thresholdSecondMoment design := by
  have hbound := two_mul_jointCrossMoment_le design
  rw [jointCrossMoment_eq design] at hbound
  linarith [hbound]

/-- **A LOWER BOUND ON THE MASS ENERGY FROM THE CLOSED CROSS TERM.**  Whenever the
closed polynomial exceeds the threshold energy, the mass energy is forced up by
the excess.  This is the first bound on the Plucker energy that reads only
two-local data. -/
theorem massSecondMoment_ge_of_thresholdSecondMoment_le {level : ℝ}
    (hlevel : thresholdSecondMoment design ≤ level) :
    46656 * pairSecondMoment design - 15552 * levSecondMoment design + 2592 - level
      ≤ massSecondMoment design := by
  have hbound := massSecondMoment_add_thresholdSecondMoment_ge design
  linarith [hbound, hlevel]

end Consequences

/-! ## 7. The tail bridge

The mass energy is the energy of a NON-NEGATIVE family whose total is known, so it
bounds that family's maximum from below.  That maximum is the objective's own
quantity, which is why the two routes to the objective — the second-moment theory
and the tail comparison — need the same unknown. -/

section TailBridge

variable (design : WeightedDesign 6 3)

/-- A principal block of a projection is positive semidefinite, so its
determinant is non-negative. -/
theorem det_tripleBlock_nonneg (outer mid inner : Fin 6) :
    0 ≤ (tripleBlock (projectionOfDesign design) outer mid inner).det := by
  have hpsd := posSemidef_projectionOfDesign design
  exact (hpsd.submatrix ![outer, mid, inner]).det_nonneg

/-- The scaled block determinants total `1296` over the full index cube. -/
theorem sum_scaled_det_full :
    ∑ outer : Fin 6, ∑ mid : Fin 6, ∑ inner : Fin 6,
        216 * (tripleBlock (projectionOfDesign design) outer mid inner).det
      = 1296 := by
  simp only [← Finset.mul_sum]
  rw [sum_sum_sum_det_tripleBlock_sixThree design]
  norm_num

/-- **THE TAIL BRIDGE.**  A mass energy beyond `1296` times a level forces some
triple's scaled block determinant to reach that level.  The proof is that the
family is non-negative with a known total, so its energy never exceeds the total
times its maximum.

This is the statement that makes `Gtz.massSecondMoment` the single quantity both
routes to the objective need: the second-moment theory needs it because it is the
one piece of `Gtz.gapSecondMoment_eq` that is not closed form, and the tail
comparison needs it because it is the only landed lower bound on the maximum. -/
theorem exists_det_tripleBlock_ge_of_massSecondMoment {level : ℝ}
    (hbig : 1296 * level < massSecondMoment design) :
    ∃ outer mid inner : Fin 6,
      level ≤ 216 * (tripleBlock (projectionOfDesign design) outer mid inner).det := by
  classical
  by_contra hcon
  push Not at hcon
  have hstep : ∀ outer mid inner : Fin 6,
      (tripleBlock (projectionOfDesign design) outer mid inner).det
          * (46656 * (tripleBlock (projectionOfDesign design) outer mid inner).det)
        ≤ (216 * (tripleBlock (projectionOfDesign design) outer mid inner).det) * level := by
    intro outer mid inner
    have hnn := det_tripleBlock_nonneg design outer mid inner
    have hlt := (hcon outer mid inner).le
    nlinarith [hnn, hlt]
  have hsum : massSecondMoment design
      ≤ ∑ outer : Fin 6, ∑ mid : Fin 6, ∑ inner : Fin 6,
          (216 * (tripleBlock (projectionOfDesign design) outer mid inner).det) * level := by
    rw [massSecondMoment_eq_full design]
    exact Finset.sum_le_sum fun outer _ => Finset.sum_le_sum fun mid _ =>
      Finset.sum_le_sum fun inner _ => hstep outer mid inner
  have htotal : ∑ outer : Fin 6, ∑ mid : Fin 6, ∑ inner : Fin 6,
      (216 * (tripleBlock (projectionOfDesign design) outer mid inner).det) * level
        = 1296 * level := by
    simp only [← Finset.sum_mul]
    rw [sum_scaled_det_full design]
  rw [htotal] at hsum
  linarith [hsum, hbig]

/-- The same, read against the closed cross term.  When the closed polynomial
beats the threshold energy by more than `1296` times a level, some triple's scaled
block determinant reaches that level — and every hypothesis except the threshold
energy is two-local. -/
theorem exists_det_tripleBlock_ge_of_closed {level : ℝ}
    (hbig : 1296 * level
      < gapSecondMoment design
        + (46656 * pairSecondMoment design - 15552 * levSecondMoment design + 2592)
        - thresholdSecondMoment design) :
    ∃ outer mid inner : Fin 6,
      level ≤ 216 * (tripleBlock (projectionOfDesign design) outer mid inner).det := by
  refine exists_det_tripleBlock_ge_of_massSecondMoment design ?_
  rw [massSecondMoment_eq_gap_add_closed design]
  exact hbig

end TailBridge

end Gtz
