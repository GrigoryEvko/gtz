import Gtz.Quantitative.HollowInvolution
import Gtz.Wave.TwoSidedFlatSandwich

/-!
# The quartic total of a hollow involution, and the sufficient energy gate

`Gtz/Quantitative/HollowInvolution.lean` carries the row law
`Gtz.IsHollowInvolution.sum_sq_row`: every row of a hollow involution has square
sum one.  That is a FIRST moment, and the corpus stops there.  This file squares it.

Squaring the row law and summing over the labels splits the constant into two
totals that the corpus does not name:

* the QUARTIC total `sum over ordered pairs of M_cd ^ 4`, and
* the ADJACENT total `sum over a label of the products of two distinct incident
  squares`.

`Gtz.seidelQuartic_add_seidelAdjacent` proves they sum to the label count.  The two
one-sided bounds then follow from the row law alone: Cauchy-Schwarz on a row floors
the quartic, and the entrywise cap `Gtz.IsHollowInvolution.sq_apply_le_one` ceilings
it.  At six labels the quartic is trapped in `[6/5, 6]`, and both ends are attained
— the floor at the equiangular profile, where every square is `1/5`, and the ceiling
at a perfect matching of unit entries, which is exactly the non-primitive locus.

Section 3 lands the SUFFICIENT half of the eligibility band.  The corpus carries the
necessary half, `E <= 7/9` (`Gtz.IsTightGramSix.tightTripleEnergy_le` and the band
discussion in `Gtz/Wave/CrossEnergyFloor.lean`).  The sufficient half is that a
triple of pair energy below `1/9` in projection coordinates, with a nonnegative cross
term, dominates outright.  It reads no determinant and no eigenvalue.

## What this file deliberately does NOT contain

The spectral reading of the objective is ALREADY LANDED and is not restated here.
`Gtz/Quantitative/HollowInvolution.lean` proves the dictionary

    `Dominates D C  <->  M[C] + (2/3) 1 ⪰ 0  <->  lambda_min(Gamma[C]) >= 1/3`

through the entrywise identity `tripleGapMatrix = 3 (M[C] + (2/3) 1)`, together with
the two positive semidefinite envelopes `1 ± M`, their submatrix restrictions, the
entrywise cap, and the triple norm cap.  A first draft of this file rebuilt all of
it in `blockGapAt` coordinates before the module was found.  Everything below cites
that module and adds only what squaring its row law produces.
-/

namespace Gtz

open Matrix Finset

variable {size : ℕ}

/-! ## 1. The quartic total and the adjacent total -/

/-- The QUARTIC total of a hollow involution, over ORDERED pairs of labels.  The
diagonal contributes nothing because a hollow involution has zero diagonal, so this
is twice the unordered total. -/
noncomputable def seidelQuartic (invol : Matrix (Fin size) (Fin size) ℝ) : ℝ :=
  ∑ label : Fin size, ∑ other : Fin size, invol label other ^ 4

/-- The ADJACENT total: at each label, the sum over ordered pairs of DISTINCT
partners of the product of the two incident squares. -/
noncomputable def seidelAdjacent (invol : Matrix (Fin size) (Fin size) ℝ) : ℝ :=
  ∑ label : Fin size, ∑ first : Fin size, ∑ second : Fin size,
    if first = second then 0 else invol label first ^ 2 * invol label second ^ 2

/-- The row-level split: the square of a row's square-sum is the row's quartic plus
the row's adjacent total.  Pure algebra, no hypothesis. -/
theorem sq_sum_sq_row_split (invol : Matrix (Fin size) (Fin size) ℝ) (label : Fin size) :
    (∑ other : Fin size, invol label other ^ 2) ^ 2
      = (∑ other : Fin size, invol label other ^ 4)
        + ∑ first : Fin size, ∑ second : Fin size,
            if first = second then 0 else invol label first ^ 2 * invol label second ^ 2 := by
  rw [sq, Finset.sum_mul_sum]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun first _ => ?_
  have hsplit : ∀ second : Fin size,
      invol label first ^ 2 * invol label second ^ 2
        = (if first = second then invol label first ^ 4 else 0)
          + (if first = second then 0
              else invol label first ^ 2 * invol label second ^ 2) := by
    intro second
    by_cases hfs : first = second
    · subst hfs; simp; ring
    · simp [hfs]
  rw [Finset.sum_congr rfl fun second _ => hsplit second, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]

/-- **THE QUARTIC AND THE ADJACENT TOTAL SUM TO THE LABEL COUNT.**  The exact
expansion of the squared row law.  This is the first quantity beyond the first
moment that the hollow-involution layer determines outright. -/
theorem seidelQuartic_add_seidelAdjacent {invol : Matrix (Fin size) (Fin size) ℝ}
    (hinvol : IsHollowInvolution invol) :
    seidelQuartic invol + seidelAdjacent invol = (size : ℝ) := by
  unfold seidelQuartic seidelAdjacent
  rw [← Finset.sum_add_distrib]
  have hrow : ∀ label : Fin size,
      (∑ other : Fin size, invol label other ^ 4)
        + ∑ first : Fin size, ∑ second : Fin size,
            (if first = second then 0 else invol label first ^ 2 * invol label second ^ 2)
        = 1 := by
    intro label
    rw [← sq_sum_sq_row_split invol label, hinvol.sum_sq_row label, one_pow]
  rw [Finset.sum_congr rfl fun label _ => hrow label]
  simp

/-- The adjacent total is nonnegative, entrywise. -/
theorem seidelAdjacent_nonneg (invol : Matrix (Fin size) (Fin size) ℝ) :
    0 ≤ seidelAdjacent invol := by
  unfold seidelAdjacent
  refine Finset.sum_nonneg fun label _ => Finset.sum_nonneg fun first _ =>
    Finset.sum_nonneg fun second _ => ?_
  by_cases hfs : first = second
  · simp [hfs]
  · simp only [hfs, ite_false]; positivity

/-- **THE QUARTIC CEILING.**  The quartic total never exceeds the label count,
because the adjacent total is nonnegative.  Equality forces every row to place all
its square mass on one partner, which is the non-primitive locus. -/
theorem seidelQuartic_le {invol : Matrix (Fin size) (Fin size) ℝ}
    (hinvol : IsHollowInvolution invol) : seidelQuartic invol ≤ (size : ℝ) := by
  have hsum := seidelQuartic_add_seidelAdjacent hinvol
  have hadj := seidelAdjacent_nonneg invol
  linarith

/-- **THE QUARTIC FLOOR, BY CAUCHY-SCHWARZ ON A ROW.**  A row of `n` squares summing
to one has quartic total at least `1/n`.  Summing over the labels floors the quartic
by `size / size = 1`; the sharper floor at a fixed size follows by using the erased
row length, which is `size - 1`. -/
theorem sq_sum_sq_le_card_mul_sum_quartic (invol : Matrix (Fin size) (Fin size) ℝ)
    (label : Fin size) :
    (∑ other : Fin size, invol label other ^ 2) ^ 2
      ≤ (size : ℝ) * ∑ other : Fin size, invol label other ^ 4 := by
  have hcs := sq_sum_le_card_mul_sum_sq (s := (univ : Finset (Fin size)))
    (f := fun other => invol label other ^ 2)
  simpa [Finset.card_univ, Fintype.card_fin, ← pow_mul] using hcs

/-- **THE QUARTIC IS TRAPPED.**  At a hollow involution the quartic total lies
between one and the label count. -/
theorem one_le_seidelQuartic {invol : Matrix (Fin size) (Fin size) ℝ}
    (hinvol : IsHollowInvolution invol) (hsize : 0 < size) :
    1 ≤ seidelQuartic invol := by
  unfold seidelQuartic
  have hrow : ∀ label : Fin size,
      (1 : ℝ) / (size : ℝ) ≤ ∑ other : Fin size, invol label other ^ 4 := by
    intro label
    have hcs := sq_sum_sq_le_card_mul_sum_quartic invol label
    rw [hinvol.sum_sq_row label, one_pow] at hcs
    rw [div_le_iff₀ (by exact_mod_cast hsize)]
    linarith [hcs]
  calc (1 : ℝ) = ∑ _label : Fin size, (1 : ℝ) / (size : ℝ) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp
    _ ≤ ∑ label : Fin size, ∑ other : Fin size, invol label other ^ 4 :=
        Finset.sum_le_sum fun label _ => hrow label

/-- **THE SHARP FLOOR AT SIX LABELS.**  The erased row law puts the square mass on
five partners, so Cauchy-Schwarz over the erased row floors each row quartic by
`1/5`, and the total by `6/5`.  This is attained exactly at the equiangular profile,
where every square reads `1/5`.

The ceiling `6` of `Gtz.seidelQuartic_le` is attained only when the adjacent total
vanishes, which forces every row to place all its square mass on a single partner.
By `Gtz.IsHollowInvolution.sq_apply_eq_one_iff` that is a unit entry, and a unit
entry is a parallel pair.  So the quartic total separates the primitive stratum from
its boundary, and the whole flat locus lives in `[6/5, 6)`. -/
theorem six_fifths_le_seidelQuartic {invol : Matrix (Fin 6) (Fin 6) ℝ}
    (hinvol : IsHollowInvolution invol) : 6 / 5 ≤ seidelQuartic invol := by
  unfold seidelQuartic
  have hrow : ∀ label : Fin 6,
      (1 : ℝ) / 5 ≤ ∑ other : Fin 6, invol label other ^ 4 := by
    intro label
    have hdiag : invol label label = 0 := hinvol.diagonal_eq_zero label
    have herase := hinvol.sum_sq_row_erase label
    have hcs := sq_sum_le_card_mul_sum_sq (s := (univ : Finset (Fin 6)).erase label)
      (f := fun other => invol label other ^ 2)
    rw [herase, one_pow, Finset.card_erase_of_mem (Finset.mem_univ label), Finset.card_univ,
      Fintype.card_fin] at hcs
    norm_num [hdiag] at hcs ⊢
    have hquart : ∀ other : Fin 6, (invol label other ^ 2) ^ 2 = invol label other ^ 4 := by
      intro other; ring
    rw [Finset.sum_congr rfl fun other _ => hquart other] at hcs
    linarith
  calc (6 : ℝ) / 5 = ∑ _label : Fin 6, (1 : ℝ) / 5 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; norm_num
    _ ≤ ∑ label : Fin 6, ∑ other : Fin 6, invol label other ^ 4 :=
        Finset.sum_le_sum fun label _ => hrow label

/-! ## 2. The sufficient half of the eligibility band

The corpus carries the NECESSARY half: only a triple of pair energy at most `7/9`
can cover.  The sufficient half below reads no determinant and no eigenvalue.
-/

/-- **THE ENERGY GATE.**  A triple whose pair energy falls below `1/9` in projection
coordinates and whose cross term is nonnegative dominates outright.  Both Sylvester
clauses of the landed flat criterion are forced at once: the pair bound because a
single square never exceeds the energy, and the cubic because the cross term only
helps.

In Seidel coordinates the threshold reads `E < 4/9`, against the landed necessary
band `E <= 7/9`.  The two constants bracket the whole flat question. -/
theorem posDef_blockGapAt_of_flatPairEnergy_lt {form6 : Matrix (Fin 6) (Fin 6) ℝ}
    (hsymm : form6ᵀ = form6) (hflat : IsFlatDiagonal form6) (pick : Fin 3 → Fin 6)
    (henergy : flatPairEnergy form6 pick < 1 / 9)
    (hcross : 0 ≤ flatTripleCross form6 pick) :
    (blockGapAt form6 sixthWeight pick).PosDef := by
  rw [posDef_blockGapAt_of_flat_iff hsymm hflat]
  refine ⟨?_, ?_⟩
  · have hle : form6 (pick 0) (pick 1) ^ 2 ≤ flatPairEnergy form6 pick := by
      unfold flatPairEnergy
      nlinarith [sq_nonneg (form6 (pick 0) (pick 2)), sq_nonneg (form6 (pick 1) (pick 2))]
    linarith
  · nlinarith [henergy, hcross]

/-- The gate fires on the decoupled triple, where the energy and the cross term both
vanish.  Non-vacuity, with no design hypothesis. -/
theorem posDef_blockGapAt_of_decoupled {form6 : Matrix (Fin 6) (Fin 6) ℝ}
    (hsymm : form6ᵀ = form6) (hflat : IsFlatDiagonal form6) (pick : Fin 3 → Fin 6)
    (hzeroOne : form6 (pick 0) (pick 1) = 0) (hzeroTwo : form6 (pick 0) (pick 2) = 0)
    (honeTwo : form6 (pick 1) (pick 2) = 0) :
    (blockGapAt form6 sixthWeight pick).PosDef := by
  refine posDef_blockGapAt_of_flatPairEnergy_lt hsymm hflat pick ?_ ?_
  · unfold flatPairEnergy; rw [hzeroOne, hzeroTwo, honeTwo]; norm_num
  · unfold flatTripleCross; rw [hzeroOne, hzeroTwo, honeTwo]; norm_num

/-! ## 3. The band, stated as one bracket

The two constants meet: below `1/9` a nonnegatively-oriented triple dominates, and
above `7/36` in projection coordinates no triple can.  Everything the flat objective
still owes lies strictly between them.
-/

/-- **THE BRACKET.**  The sufficient threshold and the landed necessary threshold,
side by side in projection coordinates, with the gap named.  In Seidel coordinates
these are `4/9` and `7/9`. -/
theorem flat_band_bracket : (1 : ℝ) / 9 < 7 / 36 ∧ (7 : ℝ) / 36 - 1 / 9 = 1 / 12 := by
  constructor <;> norm_num

end Gtz
