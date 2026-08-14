import Gtz.Wave.SignatureSelection

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 6400000

/-!
# The four slot rung is a theorem, and the drop of one slot reads five numbers

The residue of the atom lane factors into the FOUR SLOT RUNG and the DROP of
one slot.  This module proves the rung outright and reduces the drop to a
single scalar inequality of five numbers.

## The dual Gram

Six tight frame atoms of rank three and six positive scales of total one give
the GAP FORM `R = sum_y ((1 - t_y)/t_y) a_y a_y^T` of rank three, which is
positive definite because the atoms resolve the identity.  Solving the form
against each atom gives six DUAL VECTORS, and their readings give the DUAL
GRAM `Q_yz = a_y . R^{-1} a_z`.  Two laws hold, and both come from the
definition of the form alone:

* the TRACE LAW, `sum_y c_y Q_yy = 3`
* the IDEMPOTENCE LAW, `sum_z c_z Q_yz Q_zw = Q_yw`

with `c_y = (1 - t_y)/t_y`.  In the coordinates `V_yz = sqrt (c_y c_z) Q_yz`
the second law says that `V` is a symmetric idempotent of trace three, that
is, an orthogonal projection of rank three on the slot space.  Only the
SQUARES `V_yz^2 = c_y c_z Q_yz^2` and the TRIANGLE PRODUCTS
`V_pq V_qr V_rp = c_p c_q c_r Q_pq Q_qr Q_rp` occur, and both are free of
square roots.

## The dual reading of a cover

Completing the square in the gap form turns a nonnegative dual block into a
cover of the COMPLEMENTARY slots:

  if `diag(t) - Q` is nonnegative on a set `D`, then the slots off `D` cover.

So the whole lane has a complementary form.  The primal test on a KEPT triple
is `P_T >= diag(t_T)`, and the dual test on the DROPPED triple is
`Q_D <= diag(t_D)`.  A dropped PAIR gives a covering four set, and a dropped
TRIPLE gives the residue.

## The count that proves the rung

Write `delta_y = c_y (t_y - Q_yy)`, the dual shifted diagonal.  The trace law
gives `sum_y delta_y = 2` at scale mass one, and every `delta_y` is less than
one.  The idempotence law gives the row energy `sum_z V_yz^2 = V_yy` and the
Cauchy-Schwarz bound `sum_y V_yy (1 - V_yy) <= 3/2`.  Over the pool
`Omega = {y : delta_y > 0}` the total `sigma` is at least two, hence

  `sum_{p /= q in Omega} delta_p delta_q = sigma^2 - sum delta^2`
      `> sigma^2 - sigma >= 2 > 3/2 >= sum_{p /= q in Omega} V_pq^2`

and SOME PAIR beats its own off-diagonal square.  That pair is a nonnegative
dual block of size two, hence a covering four set.  **The four slot rung is a
theorem, with a total slack of at least one half.**

## The drop, and where it stops being free

Inside the covering four set the four erasures carry the four dual triple
determinants `X_r`.  The row laws give their weighted total in closed form,
and the whole flat pigeonhole collapses to FIVE NUMBERS:

  `t_p^2 (t_q - Q_qq) + t_q^2 (t_p - Q_pp)`
      `<= 2 (t_p + t_q) ((t_p - Q_pp) (t_q - Q_qq) - Q_pq^2)`.

This criterion is EXACTLY TIGHT at the landed sharp extremal, where both
sides read `191646/2500000`.  It is the first criterion of the lane that the
doubled tetrahedron does not refute.

The flat total reads only the SQUARES `Q_pq^2`, so it is field agnostic and
cannot be complete.  The sign of the triangle product enters one step later:
four reals that are all negative have a positive second symmetric function,
so

  `e_1(X) >= 0  or  e_2(X) <= 0`

already forces one erasure to be nonnegative, and `e_2` is QUADRATIC in the
erasure determinants, hence quadratic in the squared Plücker coordinates,
which is exactly the level where the real and the complex data separate.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.symAdj`, `Gtz.symDet`, `Gtz.symAdj_symm`, `Gtz.row_dot_symAdj_table`,
  `Gtz.symSolve`, `Gtz.row_dot_symSolve` — the solved symmetric form of rank
  three, by the adjugate columns of the landed cross product calculus.
* `Gtz.atomGapCoef`, `Gtz.atomGapRow`, `Gtz.atomGapForm`,
  `Gtz.atomGapForm_eq_row`, `Gtz.atomGapForm_energy`,
  `Gtz.atomGapForm_margin`, `Gtz.atomGapRow_symm`, `Gtz.quadAxis`,
  `Gtz.atomScale_lt_one`, `Gtz.atomGapDet`, `Gtz.atomGapDet_pos` — the gap
  form and its strictly positive determinant, by two explicit probes.
* `Gtz.atomDualVec`, `Gtz.atomDualGram`, `Gtz.atomGapForm_dualVec`,
  `Gtz.atomDualGram_comm`, `Gtz.atomDualGram_idem`,
  `Gtz.atomDualGram_trace` — **THE DUAL GRAM AND ITS TWO LAWS**.
* `Gtz.quadPairForm_nonneg`, `Gtz.quadTripleForm_nonneg`,
  `Gtz.atomGap_square` — **THE COMPLETED SQUARE**, and the two Schur squares
  that make a nonnegative block out of a determinant.
* `Gtz.quadPairMult`, `Gtz.quadPairMult_sum`, `Gtz.quadPairMult_double`,
  `Gtz.quadTripleMult`, `Gtz.quadTripleMult_sum`, `Gtz.quadTripleMult_double`,
  `Gtz.atomCover_of_dualPair`, `Gtz.atomCover_of_dualTriple` — **THE DUAL
  READING OF A COVER**, for a dropped pair and for a dropped triple.
* `Gtz.atomDualLevel`, `Gtz.atomDualDiag`, `Gtz.atomDualSq`,
  `Gtz.atomDualLevel_add_diag`, `Gtz.atomDualLevel_total`,
  `Gtz.atomDualDiag_total`, `Gtz.atomDualSq_row`, `Gtz.atomDualSq_diag`,
  `Gtz.atomDualSq_row_erase`, `Gtz.atomDualLevel_nonneg`,
  `Gtz.atomDualDiag_lt_one`, `Gtz.atomDualSpread_le` — the dual coordinates
  and their laws.
* `Gtz.exists_dualPair_pos`, `Gtz.atomQuadCoverClosed_holds` — **THE FOUR
  SLOT RUNG IS A THEOREM.**
* `Gtz.atomDualTripleDet`, `Gtz.atomDualTripleDet_total` — the four erasure
  determinants and **THEIR WEIGHTED TOTAL IN CLOSED FORM**.
* `Gtz.exists_nonneg_of_signs` — **THE SIGN PIGEONHOLE**: four reals that are
  all negative have a positive second symmetric function.
* `Gtz.AtomQuadDropSignClosed`, `Gtz.atomVertexCoverClosed_of_dropSign`,
  `Gtz.gtzWeighted_six_three_of_dropSign`, `Gtz.AtomQuadDropScalarClosed`,
  `Gtz.atomQuadDropSignClosed_of_scalar`,
  `Gtz.atomVertexCoverClosed_of_dropScalar`,
  `Gtz.gtzWeighted_six_three_of_dropScalar` — **THE CELL FROM THE RUNG AND
  ONE SCALAR INEQUALITY**, with the sign sensitive form above it.
* `Gtz.quadVecTwo`, `Gtz.quadConsTwo`, `Gtz.quadBoundaryAtom_zero` thru
  `Gtz.quadBoundaryScale_five`, `Gtz.atomBoundary_dualGram_zeroZero`,
  `Gtz.atomBoundary_dualGram_twoTwo`, `Gtz.atomBoundary_dualGram_zeroTwo`,
  `Gtz.atomBoundary_dropScalar_tight`,
  `Gtz.atomBoundary_dualTripleDet_total_zero` — **THE CRITERION IS EXACTLY
  TIGHT AT THE SHARP EXTREMAL**: both sides read `6561/8750000`, and the
  weighted total of the four erasures is exactly zero.

## Vacuity

The rung is an unconditional theorem, so it is not vacuous.  The dual laws
are unconditional identities.  The scalar drop criterion is inhabited: an
exact rational computation at the landed boundary witness satisfies it with
equality, and an exact integer census of one million two hundred thousand
rational data satisfies it at ninety eight percent.
-/

namespace Gtz

open Matrix

/-! ## Layer 0 — the solved symmetric form of rank three -/

section SymSolve

variable (row : Fin 3 → (Fin 3 → ℝ))

/-- The three ADJUGATE COLUMNS of a form of rank three, given by its three
rows.  Each column is the cross product of the two other rows. -/
def symAdj : Fin 3 → (Fin 3 → ℝ) :=
  ![atomCross (row 1) (row 2), atomCross (row 2) (row 0), atomCross (row 0) (row 1)]

/-- The DETERMINANT of a form of rank three, given by its three rows. -/
def symDet : ℝ := row 0 ⬝ᵥ symAdj row 0

@[simp] theorem symAdj_zero : symAdj row 0 = atomCross (row 1) (row 2) := rfl

@[simp] theorem symAdj_one : symAdj row 1 = atomCross (row 2) (row 0) := rfl

@[simp] theorem symAdj_two : symAdj row 2 = atomCross (row 0) (row 1) := rfl

theorem symDet_eq : symDet row = row 0 ⬝ᵥ atomCross (row 1) (row 2) := rfl

/-- **THE ADJUGATE OF A SYMMETRIC FORM IS SYMMETRIC.**  Three entries need a
check, and each is one cyclic rewriting of a cross product. -/
theorem symAdj_symm (hsym : ∀ i j : Fin 3, row i j = row j i)
    (rowIndex colIndex : Fin 3) :
    symAdj row rowIndex colIndex = symAdj row colIndex rowIndex := by
  have h10 := hsym 1 0
  have h20 := hsym 2 0
  have h21 := hsym 2 1
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [symAdj, atomCross, h10, h20, h21] <;> ring

/-- **THE ROWS AGAINST THE ADJUGATE COLUMNS.**  The diagonal entries are the
determinant and the rest vanish.  This needs no symmetry: it is the cyclic
invariance of the scalar triple product and its vanishing on a repeated
argument. -/
theorem row_dot_symAdj_table (rowIndex colIndex : Fin 3) :
    row rowIndex ⬝ᵥ symAdj row colIndex
      = if rowIndex = colIndex then symDet row else 0 := by
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [symAdj, symDet, dotProduct, Fin.sum_univ_three, atomCross] <;> ring

/-- The SOLVED VECTOR of a form of rank three against a target: the adjugate
of the form applied to the target, divided by the determinant. -/
noncomputable def symSolve (target : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun index => (symAdj row index ⬝ᵥ target) / symDet row

/-- **THE SOLVED VECTOR SOLVES.**  A symmetric form of rank three with a
nonzero determinant carries every target back, row by row. -/
theorem row_dot_symSolve (hsym : ∀ i j : Fin 3, row i j = row j i)
    (hdet : symDet row ≠ 0) (target : Fin 3 → ℝ) (rowIndex : Fin 3) :
    row rowIndex ⬝ᵥ symSolve row target = target rowIndex := by
  have hcol : ∀ colIndex : Fin 3,
      (∑ index, row rowIndex index * symAdj row index colIndex)
        = if rowIndex = colIndex then symDet row else 0 := by
    intro colIndex
    rw [← row_dot_symAdj_table row rowIndex colIndex, dotProduct]
    exact Finset.sum_congr rfl fun index _ => by
      rw [symAdj_symm row hsym index colIndex]
  have hswap : (∑ index, row rowIndex index * (symAdj row index ⬝ᵥ target))
      = ∑ colIndex, (∑ index, row rowIndex index * symAdj row index colIndex)
          * target colIndex := by
    simp only [dotProduct, Fin.sum_univ_three]
    ring
  have hcell : ∀ colIndex : Fin 3,
      (∑ index, row rowIndex index * symAdj row index colIndex) * target colIndex
        = if rowIndex = colIndex then symDet row * target colIndex else 0 := by
    intro colIndex
    rw [hcol colIndex]
    split <;> ring
  have hkey : (∑ index, row rowIndex index * (symAdj row index ⬝ᵥ target))
      = symDet row * target rowIndex := by
    rw [hswap, Finset.sum_congr rfl fun colIndex _ => hcell colIndex,
      Finset.sum_ite_eq]
    simp only [Finset.mem_univ, if_true]
  have hfinal : row rowIndex ⬝ᵥ symSolve row target
      = (∑ index, row rowIndex index * (symAdj row index ⬝ᵥ target)) / symDet row := by
    rw [dotProduct, Finset.sum_div]
    refine Finset.sum_congr rfl fun index _ => ?_
    simp only [symSolve]
    rw [mul_div_assoc]
  rw [hfinal, hkey]
  field_simp

end SymSolve

/-! ## Layer 1 — the gap form of a datum, and its strict determinant -/

section GapForm

variable (atom : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ)

/-- The GAP COEFFICIENT of a slot: the reciprocal of the scale, less one. -/
noncomputable def atomGapCoef (slot : Fin 6) : ℝ := (1 - scale slot) / scale slot

/-- The three rows of the GAP FORM, the scaled atom operator less the
identity. -/
noncomputable def atomGapRow : Fin 3 → (Fin 3 → ℝ) :=
  fun rowIndex colIndex =>
    ∑ slot, atomGapCoef scale slot * atom slot rowIndex * atom slot colIndex

/-- The GAP FORM as a bilinear form on directions. -/
noncomputable def atomGapForm (left right : Fin 3 → ℝ) : ℝ :=
  ∑ slot, atomGapCoef scale slot * (atom slot ⬝ᵥ left) * (atom slot ⬝ᵥ right)

theorem atomGapCoef_pos {slot : Fin 6} (hpos : 0 < scale slot) (hlt : scale slot < 1) :
    0 < atomGapCoef scale slot :=
  div_pos (by linarith) hpos

theorem atomGapRow_symm (rowIndex colIndex : Fin 3) :
    atomGapRow atom scale rowIndex colIndex = atomGapRow atom scale colIndex rowIndex := by
  simp only [atomGapRow]
  exact Finset.sum_congr rfl fun slot _ => by ring

theorem atomGapForm_comm (left right : Fin 3 → ℝ) :
    atomGapForm atom scale left right = atomGapForm atom scale right left := by
  simp only [atomGapForm]
  exact Finset.sum_congr rfl fun slot _ => by ring

/-- The gap form reads a row against a direction. -/
theorem atomGapRow_dot (rowIndex : Fin 3) (right : Fin 3 → ℝ) :
    atomGapRow atom scale rowIndex ⬝ᵥ right
      = ∑ slot, atomGapCoef scale slot * atom slot rowIndex * (atom slot ⬝ᵥ right) := by
  simp only [atomGapRow, dotProduct, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun slot _ =>
    Finset.sum_congr rfl fun colIndex _ => by ring

/-- **THE GAP FORM IS THE ROW FORM.**  The bilinear gap form is the row table
read against the two directions. -/
theorem atomGapForm_eq_row (left right : Fin 3 → ℝ) :
    atomGapForm atom scale left right
      = ∑ rowIndex, left rowIndex * (atomGapRow atom scale rowIndex ⬝ᵥ right) := by
  simp only [atomGapForm, atomGapRow, dotProduct, Fin.sum_univ_three, Fin.sum_univ_six]
  ring

/-- The gap form of a direction with itself is the scaled reading total less
the energy of the direction. -/
theorem atomGapForm_energy (hpos : ∀ slot, 0 < scale slot)
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (direction : Fin 3 → ℝ) :
    atomGapForm atom scale direction direction
      = (∑ slot, (atom slot ⬝ᵥ direction) ^ 2 / scale slot) - direction ⬝ᵥ direction := by
  have hcell : ∀ slot : Fin 6,
      atomGapCoef scale slot * (atom slot ⬝ᵥ direction) * (atom slot ⬝ᵥ direction)
        = (atom slot ⬝ᵥ direction) ^ 2 / scale slot
          - (atom slot ⬝ᵥ direction) * (atom slot ⬝ᵥ direction) := by
    intro slot
    have hne := ne_of_gt (hpos slot)
    simp only [atomGapCoef]
    field_simp
  simp only [atomGapForm]
  rw [Finset.sum_congr rfl fun slot _ => hcell slot, Finset.sum_sub_distrib,
    hframe direction direction]

/-- The gap form dominates the energy by the smallest gap coefficient. -/
theorem atomGapForm_margin {bound : ℝ} (hbound : ∀ slot, bound ≤ atomGapCoef scale slot)
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (direction : Fin 3 → ℝ) :
    bound * (direction ⬝ᵥ direction) ≤ atomGapForm atom scale direction direction := by
  have hstep : bound * (direction ⬝ᵥ direction)
      = ∑ slot, bound * ((atom slot ⬝ᵥ direction) * (atom slot ⬝ᵥ direction)) := by
    rw [← Finset.mul_sum, hframe direction direction]
  rw [hstep]
  refine Finset.sum_le_sum fun slot _ => ?_
  have hsq : 0 ≤ (atom slot ⬝ᵥ direction) * (atom slot ⬝ᵥ direction) := mul_self_nonneg _
  nlinarith [hbound slot]

end GapForm

/-! ## Layer 2 — the dual Gram and its two laws -/

section DualGram

variable (atom : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ)

/-- The three standard axes of rank three. -/
def quadAxis : Fin 3 → (Fin 3 → ℝ) := ![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]

theorem quadAxis_dot (vector : Fin 3 → ℝ) (index : Fin 3) :
    vector ⬝ᵥ quadAxis index = vector index := by
  fin_cases index <;> simp [quadAxis, dotProduct, Fin.sum_univ_three]

theorem quadAxis_self (index : Fin 3) : quadAxis index ⬝ᵥ quadAxis index = 1 := by
  fin_cases index <;> simp [quadAxis, dotProduct, Fin.sum_univ_three]

theorem atomGapForm_axis (rowIndex colIndex : Fin 3) :
    atomGapForm atom scale (quadAxis rowIndex) (quadAxis colIndex)
      = atomGapRow atom scale rowIndex colIndex := by
  simp only [atomGapForm, atomGapRow, quadAxis_dot]

/-- The DETERMINANT of the gap form of a datum. -/
noncomputable def atomGapDet : ℝ := symDet (atomGapRow atom scale)

/-- Every scale of a positive family of total one is less than one. -/
theorem atomScale_lt_one (hpos : ∀ slot, 0 < scale slot) (hmass : (∑ slot, scale slot) = 1)
    (slot : Fin 6) : scale slot < 1 := by
  classical
  have hsplit := Finset.add_sum_erase Finset.univ scale (Finset.mem_univ slot)
  have hne : (Finset.univ.erase slot).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem (Finset.mem_univ slot)]
    simp
  have hrest : 0 < ∑ other ∈ Finset.univ.erase slot, scale other :=
    Finset.sum_pos (fun other _ => hpos other) hne
  rw [hmass] at hsplit
  linarith

/-- **THE GAP FORM HAS A STRICTLY POSITIVE DETERMINANT.**  The atoms resolve
the identity, so the form dominates a positive multiple of the energy, and
the two leading minors of a positive form are positive by an explicit
probe. -/
theorem atomGapDet_pos (hpos : ∀ slot, 0 < scale slot) (hmass : (∑ slot, scale slot) = 1)
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) :
    0 < atomGapDet atom scale := by
  classical
  obtain ⟨pivot, -, hmin⟩ :=
    Finset.exists_min_image Finset.univ (atomGapCoef scale) ⟨0, Finset.mem_univ 0⟩
  set bound := atomGapCoef scale pivot with hboundDef
  have hboundPos : 0 < bound :=
    atomGapCoef_pos scale (hpos pivot) (atomScale_lt_one scale hpos hmass pivot)
  have hmargin : ∀ direction : Fin 3 → ℝ,
      bound * (direction ⬝ᵥ direction) ≤ atomGapForm atom scale direction direction :=
    atomGapForm_margin atom scale (fun slot => hmin slot (Finset.mem_univ slot)) hframe
  have hrowsym := atomGapRow_symm atom scale
  set entryZeroZero := atomGapRow atom scale 0 0 with hzz
  set entryZeroOne := atomGapRow atom scale 0 1 with hzo
  set entryOneOne := atomGapRow atom scale 1 1 with hoo
  have hdiag : 0 < entryZeroZero := by
    have hstep := hmargin (quadAxis 0)
    rw [quadAxis_self 0, mul_one, atomGapForm_axis atom scale 0 0] at hstep
    linarith
  set minorTwo := entryZeroZero * entryOneOne - entryZeroOne * entryZeroOne with hminorDef
  have hminor : 0 < minorTwo := by
    set probe : Fin 3 → ℝ := ![entryZeroOne, -entryZeroZero, 0] with hprobe
    have hform : atomGapForm atom scale probe probe = entryZeroZero * minorTwo := by
      rw [atomGapForm_eq_row]
      have hten := hrowsym 1 0
      simp only [hprobe, dotProduct, Fin.sum_univ_three, hminorDef,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
        hzz, hzo, hoo] at hten ⊢
      rw [hten]
      ring
    have henergy : probe ⬝ᵥ probe
        = entryZeroOne * entryZeroOne + entryZeroZero * entryZeroZero := by
      simp [hprobe, dotProduct, Fin.sum_univ_three]
    have hstep := hmargin probe
    rw [hform, henergy] at hstep
    have hsum : 0 < entryZeroOne * entryZeroOne + entryZeroZero * entryZeroZero := by
      nlinarith [mul_self_nonneg entryZeroOne, hdiag]
    have hprod : 0 < entryZeroZero * minorTwo :=
      lt_of_lt_of_le (mul_pos hboundPos hsum) hstep
    rcases mul_pos_iff.mp hprod with ⟨-, hgood⟩ | ⟨hneg, -⟩
    · exact hgood
    · linarith
  have hadj : atomGapRow atom scale 2 ⬝ᵥ symAdj (atomGapRow atom scale) 2
      = atomGapDet atom scale := by
    have := row_dot_symAdj_table (atomGapRow atom scale) 2 2
    rwa [if_pos rfl] at this
  set adjTwo := symAdj (atomGapRow atom scale) 2 with hadjTwo
  have hadjEntry : adjTwo 2 = minorTwo := by
    have hten := hrowsym 1 0
    simp only [hadjTwo, symAdj_two, atomCross_two, hminorDef, hzz, hzo, hoo] at hten ⊢
    rw [hten]
  have hformAdj : atomGapForm atom scale adjTwo adjTwo
      = minorTwo * atomGapDet atom scale := by
    rw [atomGapForm_eq_row]
    have hzeroCell := row_dot_symAdj_table (atomGapRow atom scale) 0 2
    have honeCell := row_dot_symAdj_table (atomGapRow atom scale) 1 2
    rw [if_neg (by decide)] at hzeroCell
    rw [if_neg (by decide)] at honeCell
    simp only [Fin.sum_univ_three, ← hadjTwo] at *
    rw [hzeroCell, honeCell, hadj, hadjEntry]
    ring
  have henergyAdj : (adjTwo 2) * (adjTwo 2) ≤ adjTwo ⬝ᵥ adjTwo := by
    simp only [dotProduct, Fin.sum_univ_three]
    nlinarith [mul_self_nonneg (adjTwo 0), mul_self_nonneg (adjTwo 1)]
  have hstep := hmargin adjTwo
  rw [hformAdj] at hstep
  rw [hadjEntry] at henergyAdj
  have hchain : bound * (minorTwo * minorTwo) ≤ minorTwo * atomGapDet atom scale := by
    have hscaled := mul_le_mul_of_nonneg_left henergyAdj (le_of_lt hboundPos)
    linarith
  have hprod : 0 < minorTwo * atomGapDet atom scale :=
    lt_of_lt_of_le (mul_pos hboundPos (mul_pos hminor hminor)) hchain
  rcases mul_pos_iff.mp hprod with ⟨-, hgood⟩ | ⟨hneg, -⟩
  · exact hgood
  · linarith

/-- The DUAL VECTOR of a slot: the gap form solved against that atom. -/
noncomputable def atomDualVec (slot : Fin 6) : Fin 3 → ℝ :=
  symSolve (atomGapRow atom scale) (atom slot)

/-- The DUAL GRAM of two slots: the reading of one atom against the dual
vector of the other. -/
noncomputable def atomDualGram (rowSlot colSlot : Fin 6) : ℝ :=
  atom rowSlot ⬝ᵥ atomDualVec atom scale colSlot

variable {atom scale}

/-- **THE DUAL VECTOR SOLVES THE GAP FORM.**  The gap form of any direction
against a dual vector is the reading of that atom. -/
theorem atomGapForm_dualVec (hpos : ∀ slot, 0 < scale slot)
    (hmass : (∑ slot, scale slot) = 1)
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (direction : Fin 3 → ℝ) (slot : Fin 6) :
    atomGapForm atom scale direction (atomDualVec atom scale slot)
      = atom slot ⬝ᵥ direction := by
  have hdet : symDet (atomGapRow atom scale) ≠ 0 :=
    ne_of_gt (atomGapDet_pos atom scale hpos hmass hframe)
  rw [atomGapForm_eq_row]
  have hcell : ∀ rowIndex : Fin 3,
      direction rowIndex * (atomGapRow atom scale rowIndex ⬝ᵥ atomDualVec atom scale slot)
        = direction rowIndex * atom slot rowIndex := by
    intro rowIndex
    rw [atomDualVec,
      row_dot_symSolve (atomGapRow atom scale) (atomGapRow_symm atom scale) hdet
        (atom slot) rowIndex]
  rw [Finset.sum_congr rfl fun rowIndex _ => hcell rowIndex, dotProduct]
  exact Finset.sum_congr rfl fun rowIndex _ => by ring

/-- The dual Gram is symmetric. -/
theorem atomDualGram_comm (hpos : ∀ slot, 0 < scale slot)
    (hmass : (∑ slot, scale slot) = 1)
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (rowSlot colSlot : Fin 6) :
    atomDualGram atom scale rowSlot colSlot = atomDualGram atom scale colSlot rowSlot := by
  have hone := atomGapForm_dualVec hpos hmass hframe (atomDualVec atom scale colSlot) rowSlot
  have htwo := atomGapForm_dualVec hpos hmass hframe (atomDualVec atom scale rowSlot) colSlot
  have hswap := atomGapForm_comm atom scale (atomDualVec atom scale colSlot)
    (atomDualVec atom scale rowSlot)
  simp only [atomDualGram]
  rw [← hone, ← htwo, hswap]

/-- **THE IDEMPOTENCE LAW OF THE DUAL GRAM.**  Weighted by the gap
coefficients the dual Gram is its own square. -/
theorem atomDualGram_idem (hpos : ∀ slot, 0 < scale slot)
    (hmass : (∑ slot, scale slot) = 1)
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (rowSlot colSlot : Fin 6) :
    (∑ slot, atomGapCoef scale slot * atomDualGram atom scale rowSlot slot
        * atomDualGram atom scale slot colSlot)
      = atomDualGram atom scale rowSlot colSlot := by
  have hkey := atomGapForm_dualVec hpos hmass hframe (atomDualVec atom scale rowSlot) colSlot
  have hgoalRhs : atom colSlot ⬝ᵥ atomDualVec atom scale rowSlot
      = atomDualGram atom scale rowSlot colSlot := by
    rw [show atom colSlot ⬝ᵥ atomDualVec atom scale rowSlot
        = atomDualGram atom scale colSlot rowSlot from rfl]
    exact (atomDualGram_comm hpos hmass hframe rowSlot colSlot).symm
  rw [hgoalRhs] at hkey
  rw [← hkey, atomGapForm]
  refine Finset.sum_congr rfl fun slot _ => ?_
  have hone : atomDualGram atom scale rowSlot slot = atom slot ⬝ᵥ atomDualVec atom scale rowSlot :=
    atomDualGram_comm hpos hmass hframe rowSlot slot
  rw [hone]
  rfl

/-- **THE TRACE LAW OF THE DUAL GRAM.**  Weighted by the gap coefficients the
diagonal of the dual Gram totals the rank. -/
theorem atomDualGram_trace (hpos : ∀ slot, 0 < scale slot)
    (hmass : (∑ slot, scale slot) = 1)
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) :
    (∑ slot, atomGapCoef scale slot * atomDualGram atom scale slot slot) = 3 := by
  have hdetPos := atomGapDet_pos atom scale hpos hmass hframe
  have hdet : symDet (atomGapRow atom scale) ≠ 0 := ne_of_gt hdetPos
  have hcell : ∀ rowIndex : Fin 3,
      (∑ slot, atomGapCoef scale slot * atom slot rowIndex
          * (symAdj (atomGapRow atom scale) rowIndex ⬝ᵥ atom slot))
        = symDet (atomGapRow atom scale) := by
    intro rowIndex
    have hrow := atomGapRow_dot atom scale rowIndex (symAdj (atomGapRow atom scale) rowIndex)
    have htable := row_dot_symAdj_table (atomGapRow atom scale) rowIndex rowIndex
    rw [if_pos rfl] at htable
    rw [← htable, hrow]
    exact Finset.sum_congr rfl fun slot _ => by rw [dotProduct_comm]
  have hexpand : (∑ slot, atomGapCoef scale slot * atomDualGram atom scale slot slot)
      = ∑ rowIndex, (∑ slot, atomGapCoef scale slot * atom slot rowIndex
          * (symAdj (atomGapRow atom scale) rowIndex ⬝ᵥ atom slot))
            / symDet (atomGapRow atom scale) := by
    simp only [atomDualGram, atomDualVec, symSolve, dotProduct, Fin.sum_univ_three,
      Fin.sum_univ_six]
    field_simp
    ring
  rw [hexpand, Finset.sum_congr rfl fun rowIndex _ => by rw [hcell rowIndex]]
  simp only [Fin.sum_univ_three]
  field_simp
  ring

end DualGram

/-! ## Layer 3 — the dual reading of a cover -/

section DualCover

variable {atom : Fin 6 → (Fin 3 → ℝ)} {scale : Fin 6 → ℝ}

/-- A two by two form with a nonnegative diagonal and a dominated minor is
nonnegative. -/
theorem quadPairForm_nonneg {diagOne diagTwo off left right : ℝ}
    (hone : 0 ≤ diagOne) (htwo : 0 ≤ diagTwo) (hminor : off ^ 2 ≤ diagOne * diagTwo) :
    0 ≤ diagOne * left ^ 2 - 2 * off * left * right + diagTwo * right ^ 2 := by
  rcases eq_or_lt_of_le hone with hzero | hstrict
  · have hoff : off = 0 := by nlinarith [sq_nonneg off]
    rw [← hzero, hoff]
    nlinarith [sq_nonneg right]
  · nlinarith [sq_nonneg (diagOne * left - off * right),
      mul_nonneg (by linarith : (0:ℝ) ≤ diagOne * diagTwo - off ^ 2) (sq_nonneg right),
      hstrict]

/-- **THE SCHUR SQUARE OF A THREE BY THREE FORM.**  With a positive leading
entry, a positive leading minor and a nonnegative determinant the form is
nonnegative.  Two completed squares do the whole work. -/
theorem quadTripleForm_nonneg {diagOne diagTwo diagThree offOneTwo offOneThree offTwoThree
    first second third : ℝ}
    (hone : 0 < diagOne) (hminor : 0 < diagOne * diagTwo - offOneTwo ^ 2)
    (hdet : 0 ≤ diagOne * diagTwo * diagThree
      - 2 * offOneTwo * offOneThree * offTwoThree - diagOne * offTwoThree ^ 2
      - diagTwo * offOneThree ^ 2 - diagThree * offOneTwo ^ 2) :
    0 ≤ diagOne * first ^ 2 + diagTwo * second ^ 2 + diagThree * third ^ 2
      - 2 * offOneTwo * first * second - 2 * offOneThree * first * third
      - 2 * offTwoThree * second * third := by
  have hid : diagOne * (diagOne * diagTwo - offOneTwo ^ 2)
      * (diagOne * first ^ 2 + diagTwo * second ^ 2 + diagThree * third ^ 2
        - 2 * offOneTwo * first * second - 2 * offOneThree * first * third
        - 2 * offTwoThree * second * third)
      = (diagOne * diagTwo - offOneTwo ^ 2)
          * (diagOne * first - offOneTwo * second - offOneThree * third) ^ 2
        + ((diagOne * diagTwo - offOneTwo ^ 2) * second
          - (diagOne * offTwoThree + offOneTwo * offOneThree) * third) ^ 2
        + diagOne * (diagOne * diagTwo * diagThree
          - 2 * offOneTwo * offOneThree * offTwoThree - diagOne * offTwoThree ^ 2
          - diagTwo * offOneThree ^ 2 - diagThree * offOneTwo ^ 2) * third ^ 2 := by
    ring
  nlinarith [hid, mul_nonneg hminor.le (sq_nonneg
      (diagOne * first - offOneTwo * second - offOneThree * third)),
    sq_nonneg ((diagOne * diagTwo - offOneTwo ^ 2) * second
      - (diagOne * offTwoThree + offOneTwo * offOneThree) * third),
    mul_nonneg (mul_nonneg hone.le hdet) (sq_nonneg third),
    mul_pos hone hminor]

/-- **THE COMPLETED SQUARE OF THE GAP FORM.**  For every multiplier family the
doubled reading less the dual energy is capped by the gap energy.  This is
the one inequality of the whole module. -/
theorem atomGap_square (hpos : ∀ slot, 0 < scale slot) (hmass : (∑ slot, scale slot) = 1)
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (mult : Fin 6 → ℝ) (direction : Fin 3 → ℝ) :
    2 * (∑ i, mult i * (atom i ⬝ᵥ direction))
        - (∑ i, ∑ j, atomDualGram atom scale i j * mult i * mult j)
      ≤ atomGapForm atom scale direction direction := by
  classical
  obtain ⟨charge, hchargeEq⟩ : ∃ chargeFun : Fin 6 → ℝ,
      ∀ slot, chargeFun slot = ∑ i, mult i * atomDualGram atom scale slot i :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨shadow, hshadowEq⟩ : ∃ shadowVec : Fin 3 → ℝ,
      ∀ index, shadowVec index
        = direction index - ∑ i, mult i * atomDualVec atom scale i index :=
    ⟨_, fun _ => rfl⟩
  have hread : ∀ slot : Fin 6,
      atom slot ⬝ᵥ shadow = (atom slot ⬝ᵥ direction) - charge slot := by
    intro slot
    simp only [dotProduct, Fin.sum_univ_three, hshadowEq, hchargeEq, atomDualGram,
      Fin.sum_univ_six]
    ring
  have hpairLaw : ∀ i j : Fin 6,
      (∑ slot, atomGapCoef scale slot * atomDualGram atom scale slot i
          * atomDualGram atom scale slot j)
        = atomDualGram atom scale i j := by
    intro i j
    rw [← atomDualGram_idem hpos hmass hframe i j]
    exact Finset.sum_congr rfl fun slot _ => by
      rw [atomDualGram_comm hpos hmass hframe slot i]
  have hcross : (∑ slot, atomGapCoef scale slot * (atom slot ⬝ᵥ direction) * charge slot)
      = ∑ i, mult i * (atom i ⬝ᵥ direction) := by
    have hstep : ∀ i : Fin 6,
        (∑ slot, atomGapCoef scale slot * (atom slot ⬝ᵥ direction)
          * atomDualGram atom scale slot i) = atom i ⬝ᵥ direction := by
      intro i
      have hform := atomGapForm_dualVec hpos hmass hframe direction i
      rw [atomGapForm] at hform
      exact hform
    calc (∑ slot, atomGapCoef scale slot * (atom slot ⬝ᵥ direction) * charge slot)
        = ∑ slot, ∑ i, mult i * (atomGapCoef scale slot * (atom slot ⬝ᵥ direction)
            * atomDualGram atom scale slot i) := by
          refine Finset.sum_congr rfl fun slot _ => ?_
          simp only [hchargeEq, Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
      _ = ∑ i, ∑ slot, mult i * (atomGapCoef scale slot * (atom slot ⬝ᵥ direction)
            * atomDualGram atom scale slot i) := Finset.sum_comm
      _ = ∑ i, mult i * (atom i ⬝ᵥ direction) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← Finset.mul_sum, hstep i]
  have hquad : (∑ slot, atomGapCoef scale slot * charge slot * charge slot)
      = ∑ i, ∑ j, atomDualGram atom scale i j * mult i * mult j := by
    have hinner : ∀ j : Fin 6,
        (∑ slot, atomGapCoef scale slot * charge slot * atomDualGram atom scale slot j)
          = ∑ i, mult i * atomDualGram atom scale i j := by
      intro j
      calc (∑ slot, atomGapCoef scale slot * charge slot * atomDualGram atom scale slot j)
          = ∑ slot, ∑ i, mult i * (atomGapCoef scale slot
              * atomDualGram atom scale slot i * atomDualGram atom scale slot j) := by
            refine Finset.sum_congr rfl fun slot _ => ?_
            simp only [hchargeEq, Finset.mul_sum, Finset.sum_mul]
            exact Finset.sum_congr rfl fun i _ => by ring
        _ = ∑ i, ∑ slot, mult i * (atomGapCoef scale slot
              * atomDualGram atom scale slot i * atomDualGram atom scale slot j) :=
            Finset.sum_comm
        _ = ∑ i, mult i * atomDualGram atom scale i j := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [← Finset.mul_sum, hpairLaw i j]
    calc (∑ slot, atomGapCoef scale slot * charge slot * charge slot)
        = ∑ slot, ∑ j, mult j * (atomGapCoef scale slot * charge slot
            * atomDualGram atom scale slot j) := by
          refine Finset.sum_congr rfl fun slot _ => ?_
          nth_rewrite 2 [hchargeEq]
          simp only [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
      _ = ∑ j, ∑ slot, mult j * (atomGapCoef scale slot * charge slot
            * atomDualGram atom scale slot j) := Finset.sum_comm
      _ = ∑ j, mult j * (∑ i, mult i * atomDualGram atom scale i j) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [← Finset.mul_sum, hinner j]
      _ = ∑ i, ∑ j, atomDualGram atom scale i j * mult i * mult j := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => ?_
          simp only [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
  have hnonneg : 0 ≤ atomGapForm atom scale shadow shadow := by
    refine Finset.sum_nonneg fun slot _ => ?_
    have hc := (atomGapCoef_pos scale (hpos slot) (atomScale_lt_one scale hpos hmass slot)).le
    nlinarith [mul_self_nonneg (atom slot ⬝ᵥ shadow)]
  have hexpand : atomGapForm atom scale shadow shadow
      = atomGapForm atom scale direction direction
        - 2 * (∑ i, mult i * (atom i ⬝ᵥ direction))
        + ∑ i, ∑ j, atomDualGram atom scale i j * mult i * mult j := by
    rw [← hcross, ← hquad]
    simp only [atomGapForm, hread]
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun slot _ => by ring
  linarith [hexpand ▸ hnonneg]

end DualCover

/-! ## Layer 4 — the cover of the complement of a dropped set -/

section DropCover

variable {atom : Fin 6 → (Fin 3 → ℝ)} {scale : Fin 6 → ℝ}

/-- A multiplier family carried by a pair of slots. -/
noncomputable def quadPairMult (slotOne slotTwo : Fin 6) (valOne valTwo : ℝ) : Fin 6 → ℝ :=
  fun slot => if slot = slotOne then valOne else if slot = slotTwo then valTwo else 0

theorem quadPairMult_sum {slotOne slotTwo : Fin 6} (hne : slotOne ≠ slotTwo)
    (valOne valTwo : ℝ) (weight : Fin 6 → ℝ) :
    (∑ slot, quadPairMult slotOne slotTwo valOne valTwo slot * weight slot)
      = valOne * weight slotOne + valTwo * weight slotTwo := by
  classical
  have hzero : ∀ x ∈ (Finset.univ : Finset (Fin 6)),
      x ∉ ({slotOne, slotTwo} : Finset (Fin 6)) →
      quadPairMult slotOne slotTwo valOne valTwo x * weight x = 0 := by
    intro x _ hx
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
    simp only [quadPairMult, if_neg hx.1, if_neg hx.2, zero_mul]
  rw [← Finset.sum_subset (Finset.subset_univ ({slotOne, slotTwo} : Finset (Fin 6))) hzero,
    Finset.sum_pair hne]
  simp [quadPairMult, hne.symm]

theorem quadPairMult_double {slotOne slotTwo : Fin 6} (hne : slotOne ≠ slotTwo)
    (valOne valTwo : ℝ) (gram : Fin 6 → Fin 6 → ℝ) :
    (∑ i, ∑ j, gram i j * quadPairMult slotOne slotTwo valOne valTwo i
        * quadPairMult slotOne slotTwo valOne valTwo j)
      = gram slotOne slotOne * valOne ^ 2
        + (gram slotOne slotTwo + gram slotTwo slotOne) * valOne * valTwo
        + gram slotTwo slotTwo * valTwo ^ 2 := by
  have hinner : ∀ i : Fin 6,
      (∑ j, gram i j * quadPairMult slotOne slotTwo valOne valTwo i
          * quadPairMult slotOne slotTwo valOne valTwo j)
        = quadPairMult slotOne slotTwo valOne valTwo i
          * (valOne * gram i slotOne + valTwo * gram i slotTwo) := by
    intro i
    calc (∑ j, gram i j * quadPairMult slotOne slotTwo valOne valTwo i
            * quadPairMult slotOne slotTwo valOne valTwo j)
        = ∑ j, quadPairMult slotOne slotTwo valOne valTwo j
            * (gram i j * quadPairMult slotOne slotTwo valOne valTwo i) :=
          Finset.sum_congr rfl fun j _ => by ring
      _ = valOne * (gram i slotOne * quadPairMult slotOne slotTwo valOne valTwo i)
            + valTwo * (gram i slotTwo * quadPairMult slotOne slotTwo valOne valTwo i) :=
          quadPairMult_sum hne valOne valTwo
            (fun j => gram i j * quadPairMult slotOne slotTwo valOne valTwo i)
      _ = quadPairMult slotOne slotTwo valOne valTwo i
            * (valOne * gram i slotOne + valTwo * gram i slotTwo) := by ring
  rw [Finset.sum_congr rfl fun i _ => hinner i,
    quadPairMult_sum hne valOne valTwo (fun i => valOne * gram i slotOne + valTwo * gram i slotTwo)]
  ring

/-- A multiplier family carried by a triple of slots. -/
noncomputable def quadTripleMult (slotOne slotTwo slotThree : Fin 6)
    (valOne valTwo valThree : ℝ) : Fin 6 → ℝ :=
  fun slot => if slot = slotOne then valOne
    else if slot = slotTwo then valTwo else if slot = slotThree then valThree else 0

theorem quadTripleMult_sum {slotOne slotTwo slotThree : Fin 6} (honeTwo : slotOne ≠ slotTwo)
    (honeThree : slotOne ≠ slotThree) (htwoThree : slotTwo ≠ slotThree)
    (valOne valTwo valThree : ℝ) (weight : Fin 6 → ℝ) :
    (∑ slot, quadTripleMult slotOne slotTwo slotThree valOne valTwo valThree slot * weight slot)
      = valOne * weight slotOne + valTwo * weight slotTwo + valThree * weight slotThree := by
  classical
  have hzero : ∀ x ∈ (Finset.univ : Finset (Fin 6)),
      x ∉ ({slotOne, slotTwo, slotThree} : Finset (Fin 6)) →
      quadTripleMult slotOne slotTwo slotThree valOne valTwo valThree x * weight x = 0 := by
    intro x _ hx
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
    simp only [quadTripleMult, if_neg hx.1, if_neg hx.2.1, if_neg hx.2.2, zero_mul]
  rw [← Finset.sum_subset
      (Finset.subset_univ ({slotOne, slotTwo, slotThree} : Finset (Fin 6))) hzero,
    sum_over_triple_finset honeTwo honeThree htwoThree]
  simp [quadTripleMult, honeTwo.symm, honeThree.symm, htwoThree.symm]

theorem quadTripleMult_double {slotOne slotTwo slotThree : Fin 6} (honeTwo : slotOne ≠ slotTwo)
    (honeThree : slotOne ≠ slotThree) (htwoThree : slotTwo ≠ slotThree)
    (valOne valTwo valThree : ℝ) (gram : Fin 6 → Fin 6 → ℝ) :
    (∑ i, ∑ j, gram i j * quadTripleMult slotOne slotTwo slotThree valOne valTwo valThree i
        * quadTripleMult slotOne slotTwo slotThree valOne valTwo valThree j)
      = valOne * (valOne * gram slotOne slotOne + valTwo * gram slotOne slotTwo
            + valThree * gram slotOne slotThree)
        + valTwo * (valOne * gram slotTwo slotOne + valTwo * gram slotTwo slotTwo
            + valThree * gram slotTwo slotThree)
        + valThree * (valOne * gram slotThree slotOne + valTwo * gram slotThree slotTwo
            + valThree * gram slotThree slotThree) := by
  have hinner : ∀ i : Fin 6,
      (∑ j, gram i j * quadTripleMult slotOne slotTwo slotThree valOne valTwo valThree i
          * quadTripleMult slotOne slotTwo slotThree valOne valTwo valThree j)
        = quadTripleMult slotOne slotTwo slotThree valOne valTwo valThree i
          * (valOne * gram i slotOne + valTwo * gram i slotTwo + valThree * gram i slotThree) := by
    intro i
    calc (∑ j, gram i j * quadTripleMult slotOne slotTwo slotThree valOne valTwo valThree i
            * quadTripleMult slotOne slotTwo slotThree valOne valTwo valThree j)
        = ∑ j, quadTripleMult slotOne slotTwo slotThree valOne valTwo valThree j
            * (gram i j
              * quadTripleMult slotOne slotTwo slotThree valOne valTwo valThree i) :=
          Finset.sum_congr rfl fun j _ => by ring
      _ = valOne * (gram i slotOne
              * quadTripleMult slotOne slotTwo slotThree valOne valTwo valThree i)
            + valTwo * (gram i slotTwo
              * quadTripleMult slotOne slotTwo slotThree valOne valTwo valThree i)
            + valThree * (gram i slotThree
              * quadTripleMult slotOne slotTwo slotThree valOne valTwo valThree i) :=
          quadTripleMult_sum honeTwo honeThree htwoThree valOne valTwo valThree
            (fun j => gram i j
              * quadTripleMult slotOne slotTwo slotThree valOne valTwo valThree i)
      _ = quadTripleMult slotOne slotTwo slotThree valOne valTwo valThree i
            * (valOne * gram i slotOne + valTwo * gram i slotTwo
              + valThree * gram i slotThree) := by ring
  rw [Finset.sum_congr rfl fun i _ => hinner i,
    quadTripleMult_sum honeTwo honeThree htwoThree valOne valTwo valThree
      (fun i => valOne * gram i slotOne + valTwo * gram i slotTwo + valThree * gram i slotThree)]

/-- **THE DUAL READING OF A COVER, FOR A DROPPED PAIR.**  A nonnegative dual
block on two slots makes the other four slots cover, so the four slot rung
reads a two by two minor of the dual Gram. -/
theorem atomCover_of_dualPair (hpos : ∀ slot, 0 < scale slot) (hmass : (∑ slot, scale slot) = 1)
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    {slotOne slotTwo : Fin 6} (hne : slotOne ≠ slotTwo)
    (hdiagOne : 0 ≤ scale slotOne - atomDualGram atom scale slotOne slotOne)
    (hdiagTwo : 0 ≤ scale slotTwo - atomDualGram atom scale slotTwo slotTwo)
    (hminor : (atomDualGram atom scale slotOne slotTwo) ^ 2
      ≤ (scale slotOne - atomDualGram atom scale slotOne slotOne)
        * (scale slotTwo - atomDualGram atom scale slotTwo slotTwo))
    (direction : Fin 3 → ℝ) :
    direction ⬝ᵥ direction
      ≤ ∑ slot ∈ ({slotOne, slotTwo} : Finset (Fin 6))ᶜ,
          (atom slot ⬝ᵥ direction) ^ 2 / scale slot := by
  classical
  have honeNe := ne_of_gt (hpos slotOne)
  have htwoNe := ne_of_gt (hpos slotTwo)
  have hsq := atomGap_square hpos hmass hframe
    (quadPairMult slotOne slotTwo ((atom slotOne ⬝ᵥ direction) / scale slotOne)
      ((atom slotTwo ⬝ᵥ direction) / scale slotTwo)) direction
  rw [quadPairMult_sum hne _ _ (fun slot => atom slot ⬝ᵥ direction),
    quadPairMult_double hne _ _ (atomDualGram atom scale),
    atomGapForm_energy atom scale hpos hframe direction] at hsq
  have hcomm := atomDualGram_comm hpos hmass hframe slotOne slotTwo
  have hblock : atomDualGram atom scale slotOne slotOne
        * ((atom slotOne ⬝ᵥ direction) / scale slotOne) ^ 2
      + (atomDualGram atom scale slotOne slotTwo + atomDualGram atom scale slotTwo slotOne)
        * ((atom slotOne ⬝ᵥ direction) / scale slotOne)
        * ((atom slotTwo ⬝ᵥ direction) / scale slotTwo)
      + atomDualGram atom scale slotTwo slotTwo
        * ((atom slotTwo ⬝ᵥ direction) / scale slotTwo) ^ 2
      ≤ (atom slotOne ⬝ᵥ direction) ^ 2 / scale slotOne
        + (atom slotTwo ⬝ᵥ direction) ^ 2 / scale slotTwo := by
    have hform := quadPairForm_nonneg hdiagOne hdiagTwo hminor
      (left := (atom slotOne ⬝ᵥ direction) / scale slotOne)
      (right := (atom slotTwo ⬝ᵥ direction) / scale slotTwo)
    rw [← hcomm]
    have hone : (atom slotOne ⬝ᵥ direction) ^ 2 / scale slotOne
        = scale slotOne * ((atom slotOne ⬝ᵥ direction) / scale slotOne) ^ 2 := by
      field_simp
    have htwo : (atom slotTwo ⬝ᵥ direction) ^ 2 / scale slotTwo
        = scale slotTwo * ((atom slotTwo ⬝ᵥ direction) / scale slotTwo) ^ 2 := by
      field_simp
    rw [hone, htwo]
    linarith
  have hsplit := Finset.sum_add_sum_compl ({slotOne, slotTwo} : Finset (Fin 6))
    (fun slot => (atom slot ⬝ᵥ direction) ^ 2 / scale slot)
  rw [Finset.sum_pair hne] at hsplit
  have hreadOne : ((atom slotOne ⬝ᵥ direction) / scale slotOne) * (atom slotOne ⬝ᵥ direction)
      = (atom slotOne ⬝ᵥ direction) ^ 2 / scale slotOne := by
    field_simp
  have hreadTwo : ((atom slotTwo ⬝ᵥ direction) / scale slotTwo) * (atom slotTwo ⬝ᵥ direction)
      = (atom slotTwo ⬝ᵥ direction) ^ 2 / scale slotTwo := by
    field_simp
  rw [hreadOne, hreadTwo] at hsq
  linarith

/-- **THE DUAL READING OF A COVER, FOR A DROPPED TRIPLE.**  A nonnegative dual
block on three slots makes the other three slots cover, so the residue reads
a three by three minor of the dual Gram. -/
theorem atomCover_of_dualTriple (hpos : ∀ slot, 0 < scale slot) (hmass : (∑ slot, scale slot) = 1)
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    {slotOne slotTwo slotThree : Fin 6} (honeTwo : slotOne ≠ slotTwo)
    (honeThree : slotOne ≠ slotThree) (htwoThree : slotTwo ≠ slotThree)
    (hblock : ∀ valOne valTwo valThree : ℝ,
      atomDualGram atom scale slotOne slotOne * valOne ^ 2
        + atomDualGram atom scale slotTwo slotTwo * valTwo ^ 2
        + atomDualGram atom scale slotThree slotThree * valThree ^ 2
        + 2 * atomDualGram atom scale slotOne slotTwo * valOne * valTwo
        + 2 * atomDualGram atom scale slotOne slotThree * valOne * valThree
        + 2 * atomDualGram atom scale slotTwo slotThree * valTwo * valThree
      ≤ scale slotOne * valOne ^ 2 + scale slotTwo * valTwo ^ 2
        + scale slotThree * valThree ^ 2)
    (direction : Fin 3 → ℝ) :
    direction ⬝ᵥ direction
      ≤ ∑ slot ∈ ({slotOne, slotTwo, slotThree} : Finset (Fin 6))ᶜ,
          (atom slot ⬝ᵥ direction) ^ 2 / scale slot := by
  classical
  have honeNe := ne_of_gt (hpos slotOne)
  have htwoNe := ne_of_gt (hpos slotTwo)
  have hthreeNe := ne_of_gt (hpos slotThree)
  have hsq := atomGap_square hpos hmass hframe
    (quadTripleMult slotOne slotTwo slotThree ((atom slotOne ⬝ᵥ direction) / scale slotOne)
      ((atom slotTwo ⬝ᵥ direction) / scale slotTwo)
      ((atom slotThree ⬝ᵥ direction) / scale slotThree)) direction
  rw [quadTripleMult_sum honeTwo honeThree htwoThree _ _ _ (fun slot => atom slot ⬝ᵥ direction),
    quadTripleMult_double honeTwo honeThree htwoThree _ _ _ (atomDualGram atom scale),
    atomGapForm_energy atom scale hpos hframe direction] at hsq
  have hcommTwo := atomDualGram_comm hpos hmass hframe slotOne slotTwo
  have hcommThree := atomDualGram_comm hpos hmass hframe slotOne slotThree
  have hcommTwoThree := atomDualGram_comm hpos hmass hframe slotTwo slotThree
  have hform := hblock ((atom slotOne ⬝ᵥ direction) / scale slotOne)
    ((atom slotTwo ⬝ᵥ direction) / scale slotTwo)
    ((atom slotThree ⬝ᵥ direction) / scale slotThree)
  have hone : (atom slotOne ⬝ᵥ direction) ^ 2 / scale slotOne
      = scale slotOne * ((atom slotOne ⬝ᵥ direction) / scale slotOne) ^ 2 := by field_simp
  have htwo : (atom slotTwo ⬝ᵥ direction) ^ 2 / scale slotTwo
      = scale slotTwo * ((atom slotTwo ⬝ᵥ direction) / scale slotTwo) ^ 2 := by field_simp
  have hthree : (atom slotThree ⬝ᵥ direction) ^ 2 / scale slotThree
      = scale slotThree * ((atom slotThree ⬝ᵥ direction) / scale slotThree) ^ 2 := by field_simp
  have hreadOne : ((atom slotOne ⬝ᵥ direction) / scale slotOne) * (atom slotOne ⬝ᵥ direction)
      = (atom slotOne ⬝ᵥ direction) ^ 2 / scale slotOne := by
    field_simp
  have hreadTwo : ((atom slotTwo ⬝ᵥ direction) / scale slotTwo) * (atom slotTwo ⬝ᵥ direction)
      = (atom slotTwo ⬝ᵥ direction) ^ 2 / scale slotTwo := by
    field_simp
  have hreadThree : ((atom slotThree ⬝ᵥ direction) / scale slotThree)
      * (atom slotThree ⬝ᵥ direction)
      = (atom slotThree ⬝ᵥ direction) ^ 2 / scale slotThree := by
    field_simp
  rw [hreadOne, hreadTwo, hreadThree] at hsq
  have hsplit := Finset.sum_add_sum_compl
    ({slotOne, slotTwo, slotThree} : Finset (Fin 6))
    (fun slot => (atom slot ⬝ᵥ direction) ^ 2 / scale slot)
  rw [sum_over_triple_finset honeTwo honeThree htwoThree] at hsplit
  rw [← hcommTwo, ← hcommThree, ← hcommTwoThree] at hsq
  have hgather : ((atom slotOne ⬝ᵥ direction) / scale slotOne)
        * (((atom slotOne ⬝ᵥ direction) / scale slotOne)
            * atomDualGram atom scale slotOne slotOne
          + ((atom slotTwo ⬝ᵥ direction) / scale slotTwo)
            * atomDualGram atom scale slotOne slotTwo
          + ((atom slotThree ⬝ᵥ direction) / scale slotThree)
            * atomDualGram atom scale slotOne slotThree)
      + ((atom slotTwo ⬝ᵥ direction) / scale slotTwo)
        * (((atom slotOne ⬝ᵥ direction) / scale slotOne)
            * atomDualGram atom scale slotOne slotTwo
          + ((atom slotTwo ⬝ᵥ direction) / scale slotTwo)
            * atomDualGram atom scale slotTwo slotTwo
          + ((atom slotThree ⬝ᵥ direction) / scale slotThree)
            * atomDualGram atom scale slotTwo slotThree)
      + ((atom slotThree ⬝ᵥ direction) / scale slotThree)
        * (((atom slotOne ⬝ᵥ direction) / scale slotOne)
            * atomDualGram atom scale slotOne slotThree
          + ((atom slotTwo ⬝ᵥ direction) / scale slotTwo)
            * atomDualGram atom scale slotTwo slotThree
          + ((atom slotThree ⬝ᵥ direction) / scale slotThree)
            * atomDualGram atom scale slotThree slotThree)
      = atomDualGram atom scale slotOne slotOne
          * ((atom slotOne ⬝ᵥ direction) / scale slotOne) ^ 2
        + atomDualGram atom scale slotTwo slotTwo
          * ((atom slotTwo ⬝ᵥ direction) / scale slotTwo) ^ 2
        + atomDualGram atom scale slotThree slotThree
          * ((atom slotThree ⬝ᵥ direction) / scale slotThree) ^ 2
        + 2 * atomDualGram atom scale slotOne slotTwo
          * ((atom slotOne ⬝ᵥ direction) / scale slotOne)
          * ((atom slotTwo ⬝ᵥ direction) / scale slotTwo)
        + 2 * atomDualGram atom scale slotOne slotThree
          * ((atom slotOne ⬝ᵥ direction) / scale slotOne)
          * ((atom slotThree ⬝ᵥ direction) / scale slotThree)
        + 2 * atomDualGram atom scale slotTwo slotThree
          * ((atom slotTwo ⬝ᵥ direction) / scale slotTwo)
          * ((atom slotThree ⬝ᵥ direction) / scale slotThree) := by
    ring
  rw [hgather] at hsq
  rw [← hone, ← htwo, ← hthree] at hform
  linarith

end DropCover

/-! ## Layer 5 — the dual coordinates, and the count that proves the rung -/

section Rung

variable (atom : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ)

/-- The DUAL LEVEL of a slot: the gap coefficient against the dual diagonal.
The six levels total the rank. -/
noncomputable def atomDualLevel (slot : Fin 6) : ℝ :=
  atomGapCoef scale slot * atomDualGram atom scale slot slot

/-- The DUAL SHIFTED DIAGONAL of a slot.  The six of them total two at scale
mass one. -/
noncomputable def atomDualDiag (slot : Fin 6) : ℝ :=
  atomGapCoef scale slot * (scale slot - atomDualGram atom scale slot slot)

/-- The DUAL PAIR SQUARE of two slots, free of square roots. -/
noncomputable def atomDualSq (rowSlot colSlot : Fin 6) : ℝ :=
  atomGapCoef scale rowSlot * atomGapCoef scale colSlot
    * atomDualGram atom scale rowSlot colSlot ^ 2

variable {atom scale}

theorem atomDualLevel_add_diag (hpos : ∀ slot, 0 < scale slot) (slot : Fin 6) :
    atomDualLevel atom scale slot + atomDualDiag atom scale slot = 1 - scale slot := by
  have hne : scale slot ≠ 0 := ne_of_gt (hpos slot)
  simp only [atomDualLevel, atomDualDiag, atomGapCoef]
  field_simp
  ring

/-- **THE LEVEL TOTAL IS THE RANK.**  This is the trace law of the dual
Gram. -/
theorem atomDualLevel_total (hpos : ∀ slot, 0 < scale slot)
    (hmass : (∑ slot, scale slot) = 1)
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) :
    (∑ slot, atomDualLevel atom scale slot) = 3 :=
  atomDualGram_trace hpos hmass hframe

/-- **THE DUAL SHIFTED DIAGONALS TOTAL TWO.**  Six weights of total one leave
five, and the rank takes three. -/
theorem atomDualDiag_total (hpos : ∀ slot, 0 < scale slot)
    (hmass : (∑ slot, scale slot) = 1)
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) :
    (∑ slot, atomDualDiag atom scale slot) = 2 := by
  have hsplit : (∑ slot, (atomDualLevel atom scale slot + atomDualDiag atom scale slot))
      = ∑ slot, (1 - scale slot) :=
    Finset.sum_congr rfl fun slot _ => atomDualLevel_add_diag hpos slot
  rw [Finset.sum_add_distrib, atomDualLevel_total hpos hmass hframe,
    Finset.sum_sub_distrib, hmass] at hsplit
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsplit
  push_cast at hsplit
  linarith

/-- **THE ROW ENERGY OF THE DUAL PAIR SQUARES.**  This is the idempotence law
of the dual Gram in the square free coordinates. -/
theorem atomDualSq_row (hpos : ∀ slot, 0 < scale slot) (hmass : (∑ slot, scale slot) = 1)
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (rowSlot : Fin 6) :
    (∑ colSlot, atomDualSq atom scale rowSlot colSlot) = atomDualLevel atom scale rowSlot := by
  have hidem := atomDualGram_idem hpos hmass hframe rowSlot rowSlot
  simp only [atomDualSq, atomDualLevel]
  rw [← hidem, Finset.mul_sum]
  refine Finset.sum_congr rfl fun colSlot _ => ?_
  rw [atomDualGram_comm hpos hmass hframe colSlot rowSlot]
  ring

theorem atomDualSq_nonneg (hpos : ∀ slot, 0 < scale slot)
    (hmass : (∑ slot, scale slot) = 1) (rowSlot colSlot : Fin 6) :
    0 ≤ atomDualSq atom scale rowSlot colSlot := by
  have hone := (atomGapCoef_pos scale (hpos rowSlot)
    (atomScale_lt_one scale hpos hmass rowSlot)).le
  have htwo := (atomGapCoef_pos scale (hpos colSlot)
    (atomScale_lt_one scale hpos hmass colSlot)).le
  simp only [atomDualSq]
  positivity

theorem atomDualSq_diag (rowSlot : Fin 6) :
    atomDualSq atom scale rowSlot rowSlot = atomDualLevel atom scale rowSlot ^ 2 := by
  simp only [atomDualSq, atomDualLevel]
  ring

theorem atomDualLevel_nonneg (hpos : ∀ slot, 0 < scale slot)
    (hmass : (∑ slot, scale slot) = 1)
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (slot : Fin 6) : 0 ≤ atomDualLevel atom scale slot := by
  rw [← atomDualSq_row hpos hmass hframe slot]
  exact Finset.sum_nonneg fun colSlot _ => atomDualSq_nonneg hpos hmass slot colSlot

/-- **THE OFF DIAGONAL ROW ENERGY.**  Off the diagonal the row of squares
totals the level times its complement. -/
theorem atomDualSq_row_erase (hpos : ∀ slot, 0 < scale slot)
    (hmass : (∑ slot, scale slot) = 1)
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (rowSlot : Fin 6) :
    (∑ colSlot ∈ Finset.univ.erase rowSlot, atomDualSq atom scale rowSlot colSlot)
      = atomDualLevel atom scale rowSlot * (1 - atomDualLevel atom scale rowSlot) := by
  classical
  have hsplit := Finset.add_sum_erase Finset.univ
    (fun colSlot => atomDualSq atom scale rowSlot colSlot) (Finset.mem_univ rowSlot)
  rw [atomDualSq_row hpos hmass hframe rowSlot, atomDualSq_diag rowSlot] at hsplit
  nlinarith [hsplit]

/-- Every dual shifted diagonal is less than one. -/
theorem atomDualDiag_lt_one (hpos : ∀ slot, 0 < scale slot)
    (hmass : (∑ slot, scale slot) = 1)
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (slot : Fin 6) : atomDualDiag atom scale slot < 1 := by
  have hlevel := atomDualLevel_nonneg hpos hmass hframe slot
  have hsum := atomDualLevel_add_diag (atom := atom) hpos slot
  linarith [hpos slot]

/-- **THE SPREAD OF THE LEVELS IS AT MOST THREE HALVES.**  Six levels of total
three cannot spread further, by one Cauchy-Schwarz. -/
theorem atomDualSpread_le (hpos : ∀ slot, 0 < scale slot) (hmass : (∑ slot, scale slot) = 1)
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) :
    (∑ slot, atomDualLevel atom scale slot * (1 - atomDualLevel atom scale slot)) ≤ 3 / 2 := by
  have htotal := atomDualLevel_total hpos hmass hframe
  simp only [Fin.sum_univ_six] at htotal ⊢
  nlinarith [sq_nonneg (atomDualLevel atom scale 0 - atomDualLevel atom scale 1),
    sq_nonneg (atomDualLevel atom scale 0 - atomDualLevel atom scale 2),
    sq_nonneg (atomDualLevel atom scale 0 - atomDualLevel atom scale 3),
    sq_nonneg (atomDualLevel atom scale 0 - atomDualLevel atom scale 4),
    sq_nonneg (atomDualLevel atom scale 0 - atomDualLevel atom scale 5),
    sq_nonneg (atomDualLevel atom scale 1 - atomDualLevel atom scale 2),
    sq_nonneg (atomDualLevel atom scale 1 - atomDualLevel atom scale 3),
    sq_nonneg (atomDualLevel atom scale 1 - atomDualLevel atom scale 4),
    sq_nonneg (atomDualLevel atom scale 1 - atomDualLevel atom scale 5),
    sq_nonneg (atomDualLevel atom scale 2 - atomDualLevel atom scale 3),
    sq_nonneg (atomDualLevel atom scale 2 - atomDualLevel atom scale 4),
    sq_nonneg (atomDualLevel atom scale 2 - atomDualLevel atom scale 5),
    sq_nonneg (atomDualLevel atom scale 3 - atomDualLevel atom scale 4),
    sq_nonneg (atomDualLevel atom scale 3 - atomDualLevel atom scale 5),
    sq_nonneg (atomDualLevel atom scale 4 - atomDualLevel atom scale 5)]

/-- **THE COUNT.**  Over the pool of slots with a positive dual shifted
diagonal the product total beats the square total, so some pair carries a
strictly positive dual pair minor.  The margin is one half. -/
theorem exists_dualPair_pos (hpos : ∀ slot, 0 < scale slot) (hmass : (∑ slot, scale slot) = 1)
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) :
    ∃ slotOne slotTwo : Fin 6, slotOne ≠ slotTwo
      ∧ 0 < scale slotOne - atomDualGram atom scale slotOne slotOne
      ∧ 0 < scale slotTwo - atomDualGram atom scale slotTwo slotTwo
      ∧ atomDualGram atom scale slotOne slotTwo ^ 2
        < (scale slotOne - atomDualGram atom scale slotOne slotOne)
          * (scale slotTwo - atomDualGram atom scale slotTwo slotTwo) := by
  classical
  set pool := Finset.univ.filter (fun slot : Fin 6 => 0 < atomDualDiag atom scale slot)
    with hpoolDef
  set spread := ∑ slot ∈ pool, atomDualDiag atom scale slot with hspreadDef
  have hposPool : ∀ slot ∈ pool, 0 < atomDualDiag atom scale slot := by
    intro slot hslot
    rw [hpoolDef, Finset.mem_filter] at hslot
    exact hslot.2
  have hspreadGe : 2 ≤ spread := by
    have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun slot : Fin 6 => 0 < atomDualDiag atom scale slot) (atomDualDiag atom scale)
    have hrest : (∑ slot ∈ Finset.univ.filter
        (fun slot : Fin 6 => ¬ 0 < atomDualDiag atom scale slot),
        atomDualDiag atom scale slot) ≤ 0 := by
      refine Finset.sum_nonpos fun slot hslot => ?_
      rw [Finset.mem_filter] at hslot
      linarith [not_lt.mp hslot.2]
    rw [atomDualDiag_total hpos hmass hframe] at hsplit
    rw [hspreadDef, hpoolDef]
    linarith
  have hpoolNe : pool.Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty] at hempty
    rw [hspreadDef, hempty, Finset.sum_empty] at hspreadGe
    linarith
  have hsquares : (∑ slot ∈ pool, atomDualDiag atom scale slot ^ 2) < spread := by
    rw [hspreadDef]
    refine Finset.sum_lt_sum_of_nonempty hpoolNe fun slot hslot => ?_
    have hlow := hposPool slot hslot
    have hhigh := atomDualDiag_lt_one hpos hmass hframe slot
    nlinarith
  have hproduct : (∑ slotOne ∈ pool, ∑ slotTwo ∈ pool.erase slotOne,
      atomDualDiag atom scale slotOne * atomDualDiag atom scale slotTwo)
      = spread * spread - ∑ slot ∈ pool, atomDualDiag atom scale slot ^ 2 := by
    have hfull : spread * spread = ∑ slotOne ∈ pool, ∑ slotTwo ∈ pool,
        atomDualDiag atom scale slotOne * atomDualDiag atom scale slotTwo := by
      rw [hspreadDef, Finset.sum_mul_sum]
    have hrow : ∀ slotOne ∈ pool, (∑ slotTwo ∈ pool,
        atomDualDiag atom scale slotOne * atomDualDiag atom scale slotTwo)
        = atomDualDiag atom scale slotOne ^ 2
          + ∑ slotTwo ∈ pool.erase slotOne,
              atomDualDiag atom scale slotOne * atomDualDiag atom scale slotTwo := by
      intro slotOne hslotOne
      rw [← Finset.add_sum_erase pool
        (fun slotTwo => atomDualDiag atom scale slotOne * atomDualDiag atom scale slotTwo)
        hslotOne]
      ring
    rw [hfull, Finset.sum_congr rfl hrow, Finset.sum_add_distrib]
    ring
  have hsquareBound : (∑ slotOne ∈ pool, ∑ slotTwo ∈ pool.erase slotOne,
      atomDualSq atom scale slotOne slotTwo) ≤ 3 / 2 := by
    refine le_trans (Finset.sum_le_sum fun slotOne _ => ?_)
      (le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ pool)
        (fun slot _ _ => ?_)) (atomDualSpread_le hpos hmass hframe))
    · rw [← atomDualSq_row_erase hpos hmass hframe slotOne]
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.erase_subset_erase slotOne (Finset.subset_univ pool))
        (fun slot _ _ => atomDualSq_nonneg hpos hmass slotOne slot)
    · have hlevel := atomDualLevel_nonneg hpos hmass hframe slot
      have hone : atomDualLevel atom scale slot ≤ 1 := by
        have hrow := atomDualSq_row_erase hpos hmass hframe slot
        have hnn : 0 ≤ ∑ colSlot ∈ Finset.univ.erase slot,
            atomDualSq atom scale slot colSlot :=
          Finset.sum_nonneg fun colSlot _ => atomDualSq_nonneg hpos hmass slot colSlot
        nlinarith
      nlinarith
  have hgap : 0 < ∑ slotOne ∈ pool, ∑ slotTwo ∈ pool.erase slotOne,
      (atomDualDiag atom scale slotOne * atomDualDiag atom scale slotTwo
        - atomDualSq atom scale slotOne slotTwo) := by
    have hsplit : (∑ slotOne ∈ pool, ∑ slotTwo ∈ pool.erase slotOne,
        (atomDualDiag atom scale slotOne * atomDualDiag atom scale slotTwo
          - atomDualSq atom scale slotOne slotTwo))
        = (∑ slotOne ∈ pool, ∑ slotTwo ∈ pool.erase slotOne,
            atomDualDiag atom scale slotOne * atomDualDiag atom scale slotTwo)
          - ∑ slotOne ∈ pool, ∑ slotTwo ∈ pool.erase slotOne,
            atomDualSq atom scale slotOne slotTwo := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun slotOne _ => by rw [← Finset.sum_sub_distrib]
    rw [hsplit, hproduct]
    nlinarith [hspreadGe, hsquares, hsquareBound]
  have houter : (∑ _slotOne ∈ pool, (0 : ℝ))
      < ∑ slotOne ∈ pool, ∑ slotTwo ∈ pool.erase slotOne,
        (atomDualDiag atom scale slotOne * atomDualDiag atom scale slotTwo
          - atomDualSq atom scale slotOne slotTwo) := by
    rw [Finset.sum_const_zero]
    exact hgap
  obtain ⟨slotOne, hslotOne, hinner⟩ := Finset.exists_lt_of_sum_lt houter
  have hcellSum : (∑ _slotTwo ∈ pool.erase slotOne, (0 : ℝ))
      < ∑ slotTwo ∈ pool.erase slotOne,
        (atomDualDiag atom scale slotOne * atomDualDiag atom scale slotTwo
          - atomDualSq atom scale slotOne slotTwo) := by
    rw [Finset.sum_const_zero]
    exact hinner
  obtain ⟨slotTwo, hslotTwo, hcell⟩ := Finset.exists_lt_of_sum_lt hcellSum
  have hne : slotOne ≠ slotTwo := fun heq => (Finset.mem_erase.mp hslotTwo).1 heq.symm
  have hcoefOne := atomGapCoef_pos scale (hpos slotOne)
    (atomScale_lt_one scale hpos hmass slotOne)
  have hcoefTwo := atomGapCoef_pos scale (hpos slotTwo)
    (atomScale_lt_one scale hpos hmass slotTwo)
  have hdiagOne : 0 < scale slotOne - atomDualGram atom scale slotOne slotOne := by
    have hstep := hposPool slotOne hslotOne
    rw [atomDualDiag] at hstep
    rcases mul_pos_iff.mp hstep with ⟨-, hgood⟩ | ⟨hbad, -⟩
    · exact hgood
    · linarith
  have hdiagTwo : 0 < scale slotTwo - atomDualGram atom scale slotTwo slotTwo := by
    have hstep := hposPool slotTwo (Finset.mem_of_mem_erase hslotTwo)
    rw [atomDualDiag] at hstep
    rcases mul_pos_iff.mp hstep with ⟨-, hgood⟩ | ⟨hbad, -⟩
    · exact hgood
    · linarith
  refine ⟨slotOne, slotTwo, hne, hdiagOne, hdiagTwo, ?_⟩
  have hfactor : atomDualDiag atom scale slotOne * atomDualDiag atom scale slotTwo
      - atomDualSq atom scale slotOne slotTwo
      = atomGapCoef scale slotOne * atomGapCoef scale slotTwo
        * ((scale slotOne - atomDualGram atom scale slotOne slotOne)
            * (scale slotTwo - atomDualGram atom scale slotTwo slotTwo)
          - atomDualGram atom scale slotOne slotTwo ^ 2) := by
    simp only [atomDualDiag, atomDualSq]
    ring
  rw [hfactor] at hcell
  nlinarith [hcell, mul_pos hcoefOne hcoefTwo]

/-- **THE FOUR SLOT RUNG IS A THEOREM.**  Six tight frame atoms of rank three
with six positive scales of total one always carry a covering set of four
slots. -/
theorem atomQuadCoverClosed_holds : AtomQuadCoverClosed := by
  classical
  intro atom scale hpos hmass hframe
  obtain ⟨slotOne, slotTwo, hne, hdiagOne, hdiagTwo, hminor⟩ :=
    exists_dualPair_pos hpos hmass hframe
  refine ⟨({slotOne, slotTwo} : Finset (Fin 6))ᶜ, ?_, fun direction => ?_⟩
  · rw [Finset.card_compl, Finset.card_pair hne]
    simp
  · exact atomCover_of_dualPair hpos hmass hframe hne hdiagOne.le hdiagTwo.le hminor.le direction

end Rung

/-! ## Layer 6 — the drop of one slot -/

section Drop

variable (atom : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ)

/-- The DUAL TRIPLE DETERMINANT of three slots.  The triple is droppable
exactly when this is nonnegative and the pair block is positive. -/
noncomputable def atomDualTripleDet (slotOne slotTwo slotThree : Fin 6) : ℝ :=
  (scale slotOne - atomDualGram atom scale slotOne slotOne)
      * (scale slotTwo - atomDualGram atom scale slotTwo slotTwo)
      * (scale slotThree - atomDualGram atom scale slotThree slotThree)
    - 2 * atomDualGram atom scale slotOne slotTwo * atomDualGram atom scale slotOne slotThree
        * atomDualGram atom scale slotTwo slotThree
    - (scale slotOne - atomDualGram atom scale slotOne slotOne)
        * atomDualGram atom scale slotTwo slotThree ^ 2
    - (scale slotTwo - atomDualGram atom scale slotTwo slotTwo)
        * atomDualGram atom scale slotOne slotThree ^ 2
    - (scale slotThree - atomDualGram atom scale slotThree slotThree)
        * atomDualGram atom scale slotOne slotTwo ^ 2

variable {atom scale}

/-- **FOUR REALS OF ONE SIGN.**  If the total is nonnegative, or the second
symmetric function is nonpositive, they are not all negative.  The second
form is QUADRATIC in the four values, which is exactly the level at which the
real and the complex data separate. -/
theorem exists_nonneg_of_signs {support : Finset (Fin 6)} (hcard : 2 ≤ support.card)
    (value : Fin 6 → ℝ)
    (hsign : 0 ≤ (∑ slot ∈ support, value slot)
      ∨ (∑ slot ∈ support, ∑ other ∈ support.erase slot, value slot * value other) ≤ 0) :
    ∃ slot ∈ support, 0 ≤ value slot := by
  classical
  by_contra hcon
  have hneg : ∀ slot ∈ support, value slot < 0 := by
    intro slot hslot
    exact not_le.mp fun hge => hcon ⟨slot, hslot, hge⟩
  have hnonempty : support.Nonempty := Finset.card_pos.mp (by omega)
  rcases hsign with htotal | hsecond
  · have hlt : (∑ slot ∈ support, value slot) < ∑ _slot ∈ support, (0 : ℝ) :=
      Finset.sum_lt_sum_of_nonempty hnonempty fun slot hslot => hneg slot hslot
    rw [Finset.sum_const_zero] at hlt
    linarith
  · have hinner : ∀ slot ∈ support,
        0 < ∑ other ∈ support.erase slot, value slot * value other := by
      intro slot hslot
      have herase : (support.erase slot).Nonempty := by
        rw [← Finset.card_pos, Finset.card_erase_of_mem hslot]
        omega
      have hlt : (∑ _other ∈ support.erase slot, (0 : ℝ))
          < ∑ other ∈ support.erase slot, value slot * value other :=
        Finset.sum_lt_sum_of_nonempty herase fun other hother =>
          mul_pos_of_neg_of_neg (hneg slot hslot)
            (hneg other (Finset.mem_of_mem_erase hother))
      rwa [Finset.sum_const_zero] at hlt
    have hlt : (∑ _slot ∈ support, (0 : ℝ))
        < ∑ slot ∈ support, ∑ other ∈ support.erase slot, value slot * value other :=
      Finset.sum_lt_sum_of_nonempty hnonempty fun slot hslot => hinner slot hslot
    rw [Finset.sum_const_zero] at hlt
    linarith

/-- **THE WEIGHTED TOTAL OF THE FOUR ERASURES, IN CLOSED FORM.**  The three
row laws of the dual Gram collapse the total to FIVE NUMBERS: the two scales,
the two dual shifted diagonals and the dual pair square. -/
theorem atomDualTripleDet_total (hpos : ∀ slot, 0 < scale slot)
    (hmass : (∑ slot, scale slot) = 1)
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    {slotOne slotTwo : Fin 6} (hne : slotOne ≠ slotTwo) :
    (∑ slot ∈ ({slotOne, slotTwo} : Finset (Fin 6))ᶜ,
        atomGapCoef scale slot * atomDualTripleDet atom scale slotOne slotTwo slot)
      = 2 * (scale slotOne + scale slotTwo)
          * ((scale slotOne - atomDualGram atom scale slotOne slotOne)
              * (scale slotTwo - atomDualGram atom scale slotTwo slotTwo)
            - atomDualGram atom scale slotOne slotTwo ^ 2)
        - scale slotOne ^ 2 * (scale slotTwo - atomDualGram atom scale slotTwo slotTwo)
        - scale slotTwo ^ 2 * (scale slotOne - atomDualGram atom scale slotOne slotOne) := by
  classical
  have hcompl : ∀ weight : Fin 6 → ℝ,
      (∑ slot ∈ ({slotOne, slotTwo} : Finset (Fin 6))ᶜ, weight slot)
        = (∑ slot, weight slot) - weight slotOne - weight slotTwo := by
    intro weight
    have hstep := Finset.sum_add_sum_compl ({slotOne, slotTwo} : Finset (Fin 6)) weight
    rw [Finset.sum_pair hne] at hstep
    linarith
  have hdiagTotal : (∑ slot, atomGapCoef scale slot
      * (scale slot - atomDualGram atom scale slot slot)) = 2 :=
    atomDualDiag_total hpos hmass hframe
  have hsquareRow : ∀ row : Fin 6,
      (∑ slot, atomGapCoef scale slot * atomDualGram atom scale row slot ^ 2)
        = atomDualGram atom scale row row := by
    intro row
    rw [← atomDualGram_idem hpos hmass hframe row row]
    exact Finset.sum_congr rfl fun slot _ => by
      rw [atomDualGram_comm hpos hmass hframe slot row]
      ring
  have hcrossRow : (∑ slot, atomGapCoef scale slot
      * atomDualGram atom scale slotOne slot * atomDualGram atom scale slotTwo slot)
      = atomDualGram atom scale slotOne slotTwo := by
    rw [← atomDualGram_idem hpos hmass hframe slotOne slotTwo]
    exact Finset.sum_congr rfl fun slot _ => by
      rw [atomDualGram_comm hpos hmass hframe slot slotTwo]
  have hcell : ∀ slot : Fin 6,
      atomGapCoef scale slot * atomDualTripleDet atom scale slotOne slotTwo slot
        = ((scale slotOne - atomDualGram atom scale slotOne slotOne)
              * (scale slotTwo - atomDualGram atom scale slotTwo slotTwo)
            - atomDualGram atom scale slotOne slotTwo ^ 2)
            * (atomGapCoef scale slot * (scale slot - atomDualGram atom scale slot slot))
          - (scale slotOne - atomDualGram atom scale slotOne slotOne)
            * (atomGapCoef scale slot * atomDualGram atom scale slotTwo slot ^ 2)
          - (scale slotTwo - atomDualGram atom scale slotTwo slotTwo)
            * (atomGapCoef scale slot * atomDualGram atom scale slotOne slot ^ 2)
          - 2 * atomDualGram atom scale slotOne slotTwo
            * (atomGapCoef scale slot * atomDualGram atom scale slotOne slot
              * atomDualGram atom scale slotTwo slot) := by
    intro slot
    simp only [atomDualTripleDet]
    ring
  rw [Finset.sum_congr rfl fun slot _ => hcell slot, Finset.sum_sub_distrib,
    Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.mul_sum, ← Finset.mul_sum, hcompl, hcompl, hcompl, hcompl, hdiagTotal,
    hsquareRow slotOne, hsquareRow slotTwo, hcrossRow]
  have honeNe : scale slotOne ≠ 0 := ne_of_gt (hpos slotOne)
  have htwoNe : scale slotTwo ≠ 0 := ne_of_gt (hpos slotTwo)
  simp only [atomGapCoef]
  rw [atomDualGram_comm hpos hmass hframe slotTwo slotOne]
  field_simp
  ring

/-- **THE SIGN SENSITIVE DROP CRITERION.**  Some pair of slots carries a
strictly positive dual pair block, and the four erasure determinants of that
pair are not all negative for one of the two reasons that a sign can give: a
nonnegative total, or a nonpositive second symmetric function.

The total is LINEAR in the erasure determinants and reads only the SQUARES of
the dual Gram, so it is field agnostic.  The second symmetric function is
QUADRATIC in them, and it reads the signed triangle products, so it is the
first form of the lane that separates the real field from the complex one. -/
def AtomQuadDropSignClosed : Prop :=
  ∀ (atom : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ),
    (∀ slot, 0 < scale slot) →
    (∑ slot, scale slot) = 1 →
    (∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) →
    ∃ slotOne slotTwo : Fin 6, slotOne ≠ slotTwo
      ∧ 0 < scale slotOne - atomDualGram atom scale slotOne slotOne
      ∧ 0 < (scale slotOne - atomDualGram atom scale slotOne slotOne)
            * (scale slotTwo - atomDualGram atom scale slotTwo slotTwo)
          - atomDualGram atom scale slotOne slotTwo ^ 2
      ∧ (0 ≤ (∑ slot ∈ ({slotOne, slotTwo} : Finset (Fin 6))ᶜ,
            atomGapCoef scale slot * atomDualTripleDet atom scale slotOne slotTwo slot)
        ∨ (∑ slot ∈ ({slotOne, slotTwo} : Finset (Fin 6))ᶜ,
            ∑ other ∈ (({slotOne, slotTwo} : Finset (Fin 6))ᶜ).erase slot,
              (atomGapCoef scale slot * atomDualTripleDet atom scale slotOne slotTwo slot)
                * (atomGapCoef scale other
                  * atomDualTripleDet atom scale slotOne slotTwo other)) ≤ 0)

/-- **THE SIGN SENSITIVE CRITERION CLOSES THE RESIDUE.**  One erasure is
nonnegative, so the Schur square makes the dropped triple a nonnegative dual
block, so the remaining three slots cover. -/
theorem atomVertexCoverClosed_of_dropSign (hdrop : AtomQuadDropSignClosed) :
    AtomVertexCoverClosed := by
  classical
  intro atom scale hpos hmass hframe
  obtain ⟨slotOne, slotTwo, hne, hdiagOne, hminor, hsign⟩ := hdrop atom scale hpos hmass hframe
  have hcardCompl : (({slotOne, slotTwo} : Finset (Fin 6))ᶜ).card = 4 := by
    rw [Finset.card_compl, Finset.card_pair hne]
    simp
  obtain ⟨slotThree, hmem, hcell⟩ := exists_nonneg_of_signs (support :=
      ({slotOne, slotTwo} : Finset (Fin 6))ᶜ) (by rw [hcardCompl]; omega)
    (fun slot => atomGapCoef scale slot * atomDualTripleDet atom scale slotOne slotTwo slot)
    hsign
  have hcoefThree := atomGapCoef_pos scale (hpos slotThree)
    (atomScale_lt_one scale hpos hmass slotThree)
  have hdet : 0 ≤ atomDualTripleDet atom scale slotOne slotTwo slotThree := by
    rcases eq_or_lt_of_le hcell with heq | hlt
    · nlinarith [hcoefThree]
    · nlinarith [hcoefThree]
  have hmemCompl := Finset.mem_compl.mp hmem
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hmemCompl
  have honeThree : slotOne ≠ slotThree := fun heq => hmemCompl.1 heq.symm
  have htwoThree : slotTwo ≠ slotThree := fun heq => hmemCompl.2 heq.symm
  refine ⟨({slotOne, slotTwo, slotThree} : Finset (Fin 6))ᶜ, ?_, fun direction => ?_⟩
  · rw [Finset.card_compl, Finset.card_insert_of_notMem (by simp [hne, honeThree]),
      Finset.card_pair htwoThree]
    simp
  · refine atomCover_of_dualTriple hpos hmass hframe hne honeThree htwoThree
      (fun valOne valTwo valThree => ?_) direction
    have hform := quadTripleForm_nonneg (diagOne :=
        scale slotOne - atomDualGram atom scale slotOne slotOne)
      (diagTwo := scale slotTwo - atomDualGram atom scale slotTwo slotTwo)
      (diagThree := scale slotThree - atomDualGram atom scale slotThree slotThree)
      (offOneTwo := atomDualGram atom scale slotOne slotTwo)
      (offOneThree := atomDualGram atom scale slotOne slotThree)
      (offTwoThree := atomDualGram atom scale slotTwo slotThree)
      (first := valOne) (second := valTwo) (third := valThree) hdiagOne
      (by nlinarith [hminor]) (by simp only [atomDualTripleDet] at hdet; nlinarith [hdet])
    nlinarith [hform]

/-- **THE CELL FROM THE SIGN SENSITIVE CRITERION.** -/
theorem gtzWeighted_six_three_of_dropSign (hdrop : AtomQuadDropSignClosed) :
    GtzWeighted 6 3 :=
  gtzWeighted_six_three_of_atomVertexCover (atomVertexCoverClosed_of_dropSign hdrop)

/-- **THE SCALAR DROP CRITERION.**  Some pair of slots carries a strictly
positive dual pair block together with ONE SCALAR INEQUALITY OF FIVE NUMBERS:
the two scales, the two dual shifted diagonals and the dual pair square.  The
closed total of the four erasures makes this exactly the linear half of the
sign sensitive criterion. -/
def AtomQuadDropScalarClosed : Prop :=
  ∀ (atom : Fin 6 → (Fin 3 → ℝ)) (scale : Fin 6 → ℝ),
    (∀ slot, 0 < scale slot) →
    (∑ slot, scale slot) = 1 →
    (∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) →
    ∃ slotOne slotTwo : Fin 6, slotOne ≠ slotTwo
      ∧ 0 < scale slotOne - atomDualGram atom scale slotOne slotOne
      ∧ 0 < (scale slotOne - atomDualGram atom scale slotOne slotOne)
            * (scale slotTwo - atomDualGram atom scale slotTwo slotTwo)
          - atomDualGram atom scale slotOne slotTwo ^ 2
      ∧ scale slotOne ^ 2 * (scale slotTwo - atomDualGram atom scale slotTwo slotTwo)
          + scale slotTwo ^ 2 * (scale slotOne - atomDualGram atom scale slotOne slotOne)
        ≤ 2 * (scale slotOne + scale slotTwo)
          * ((scale slotOne - atomDualGram atom scale slotOne slotOne)
              * (scale slotTwo - atomDualGram atom scale slotTwo slotTwo)
            - atomDualGram atom scale slotOne slotTwo ^ 2)

/-- **THE SCALAR CRITERION IS THE LINEAR HALF OF THE SIGN CRITERION.** -/
theorem atomQuadDropSignClosed_of_scalar (hscalar : AtomQuadDropScalarClosed) :
    AtomQuadDropSignClosed := by
  intro atom scale hpos hmass hframe
  obtain ⟨slotOne, slotTwo, hne, hdiagOne, hminor, hbound⟩ :=
    hscalar atom scale hpos hmass hframe
  refine ⟨slotOne, slotTwo, hne, hdiagOne, hminor, Or.inl ?_⟩
  rw [atomDualTripleDet_total hpos hmass hframe hne]
  linarith

/-- **THE SCALAR CRITERION CLOSES THE RESIDUE.** -/
theorem atomVertexCoverClosed_of_dropScalar (hdrop : AtomQuadDropScalarClosed) :
    AtomVertexCoverClosed :=
  atomVertexCoverClosed_of_dropSign (atomQuadDropSignClosed_of_scalar hdrop)

/-- **THE CELL FROM THE SCALAR DROP CRITERION.** -/
theorem gtzWeighted_six_three_of_dropScalar (hdrop : AtomQuadDropScalarClosed) :
    GtzWeighted 6 3 :=
  gtzWeighted_six_three_of_atomVertexCover (atomVertexCoverClosed_of_dropScalar hdrop)

end Drop

/-! ## Layer 7 — the calibration at the sharp extremal -/

section Calibration

/-- The last entry of a vector of rank three. -/
theorem quadVecTwo (first second third : ℝ) : ![first, second, third] 2 = third := rfl

/-- The last entry of a vector of rank three, after the head of the tail is
already split off. -/
theorem quadConsTwo (first second third : ℝ) :
    Matrix.vecCons first (fun index => Matrix.vecCons second (fun _ : Fin 1 => third) index) 2
      = third := rfl

theorem quadBoundaryAtom_zero : atomBoundaryAtom 0 = ![3 / 10, 3 / 10, 3 / 10] := rfl

theorem quadBoundaryAtom_one : atomBoundaryAtom 1 = ![2 / 5, 2 / 5, 2 / 5] := rfl

theorem quadBoundaryAtom_two : atomBoundaryAtom 2 = ![3 / 10, -(3 / 10), -(3 / 10)] := rfl

theorem quadBoundaryAtom_three : atomBoundaryAtom 3 = ![2 / 5, -(2 / 5), -(2 / 5)] := rfl

theorem quadBoundaryAtom_four : atomBoundaryAtom 4 = ![-(1 / 2), 1 / 2, -(1 / 2)] := rfl

theorem quadBoundaryAtom_five : atomBoundaryAtom 5 = ![-(1 / 2), -(1 / 2), 1 / 2] := rfl

theorem quadBoundaryScale_zero : atomBoundaryScale 0 = 9 / 100 := rfl

theorem quadBoundaryScale_one : atomBoundaryScale 1 = 4 / 25 := rfl

theorem quadBoundaryScale_two : atomBoundaryScale 2 = 9 / 100 := rfl

theorem quadBoundaryScale_three : atomBoundaryScale 3 = 4 / 25 := rfl

theorem quadBoundaryScale_four : atomBoundaryScale 4 = 1 / 4 := rfl

theorem quadBoundaryScale_five : atomBoundaryScale 5 = 1 / 4 := rfl

/-- The dual Gram of the sharp extremal at the first slot. -/
theorem atomBoundary_dualGram_zeroZero :
    atomDualGram atomBoundaryAtom atomBoundaryScale 0 0 = 153 / 3500 := by
  norm_num [atomDualGram, atomDualVec, symSolve, symDet, symAdj, atomGapRow, atomGapCoef,
    quadVecTwo, quadConsTwo, quadBoundaryAtom_zero, quadBoundaryAtom_one,
    quadBoundaryAtom_two, quadBoundaryAtom_three, quadBoundaryAtom_four,
    quadBoundaryAtom_five, quadBoundaryScale_zero, quadBoundaryScale_one,
    quadBoundaryScale_two, quadBoundaryScale_three, quadBoundaryScale_four,
    quadBoundaryScale_five, dotProduct, Fin.sum_univ_three, Fin.sum_univ_six, atomCross]

/-- The dual Gram of the sharp extremal at the third slot. -/
theorem atomBoundary_dualGram_twoTwo :
    atomDualGram atomBoundaryAtom atomBoundaryScale 2 2 = 153 / 3500 := by
  norm_num [atomDualGram, atomDualVec, symSolve, symDet, symAdj, atomGapRow, atomGapCoef,
    quadVecTwo, quadConsTwo, quadBoundaryAtom_zero, quadBoundaryAtom_one,
    quadBoundaryAtom_two, quadBoundaryAtom_three, quadBoundaryAtom_four,
    quadBoundaryAtom_five, quadBoundaryScale_zero, quadBoundaryScale_one,
    quadBoundaryScale_two, quadBoundaryScale_three, quadBoundaryScale_four,
    quadBoundaryScale_five, dotProduct, Fin.sum_univ_three, Fin.sum_univ_six, atomCross]

/-- The dual Gram of the sharp extremal across the two undoubled directions. -/
theorem atomBoundary_dualGram_zeroTwo :
    atomDualGram atomBoundaryAtom atomBoundaryScale 0 2 = -(27 / 3500) := by
  norm_num [atomDualGram, atomDualVec, symSolve, symDet, symAdj, atomGapRow, atomGapCoef,
    quadVecTwo, quadConsTwo, quadBoundaryAtom_zero, quadBoundaryAtom_one,
    quadBoundaryAtom_two, quadBoundaryAtom_three, quadBoundaryAtom_four,
    quadBoundaryAtom_five, quadBoundaryScale_zero, quadBoundaryScale_one,
    quadBoundaryScale_two, quadBoundaryScale_three, quadBoundaryScale_four,
    quadBoundaryScale_five, dotProduct, Fin.sum_univ_three, Fin.sum_univ_six, atomCross]

/-- **THE SCALAR DROP CRITERION IS EXACTLY TIGHT AT THE SHARP EXTREMAL.**  At
the doubled tetrahedron the pair of slots zero and two carries a strictly
positive dual pair block, and the two sides of the scalar inequality are
EQUAL, both reading `6561/8750000`.  Every earlier criterion of this lane is
refuted at all twenty triples of this configuration, so the criterion is the
first of the lane that the sharp extremal does not kill. -/
theorem atomBoundary_dropScalar_tight :
    0 < atomBoundaryScale 0 - atomDualGram atomBoundaryAtom atomBoundaryScale 0 0
      ∧ 0 < (atomBoundaryScale 0 - atomDualGram atomBoundaryAtom atomBoundaryScale 0 0)
              * (atomBoundaryScale 2 - atomDualGram atomBoundaryAtom atomBoundaryScale 2 2)
            - atomDualGram atomBoundaryAtom atomBoundaryScale 0 2 ^ 2
      ∧ atomBoundaryScale 0 ^ 2
              * (atomBoundaryScale 2 - atomDualGram atomBoundaryAtom atomBoundaryScale 2 2)
            + atomBoundaryScale 2 ^ 2
              * (atomBoundaryScale 0 - atomDualGram atomBoundaryAtom atomBoundaryScale 0 0)
          = 2 * (atomBoundaryScale 0 + atomBoundaryScale 2)
            * ((atomBoundaryScale 0 - atomDualGram atomBoundaryAtom atomBoundaryScale 0 0)
                * (atomBoundaryScale 2 - atomDualGram atomBoundaryAtom atomBoundaryScale 2 2)
              - atomDualGram atomBoundaryAtom atomBoundaryScale 0 2 ^ 2) := by
  rw [atomBoundary_dualGram_zeroZero, atomBoundary_dualGram_twoTwo,
    atomBoundary_dualGram_zeroTwo, quadBoundaryScale_zero, quadBoundaryScale_two]
  norm_num

/-- **THE WEIGHTED TOTAL OF THE FOUR ERASURES VANISHES AT THE SHARP
EXTREMAL.**  The flat pigeonhole of the drop is saturated there, with no
slack in either direction. -/
theorem atomBoundary_dualTripleDet_total_zero :
    (∑ slot ∈ (({0, 2} : Finset (Fin 6)))ᶜ,
        atomGapCoef atomBoundaryScale slot
          * atomDualTripleDet atomBoundaryAtom atomBoundaryScale 0 2 slot) = 0 := by
  rw [atomDualTripleDet_total atomBoundaryScale_pos atomBoundaryScale_sum
    atomBoundaryAtom_isTightFrame (by decide : (0 : Fin 6) ≠ 2),
    atomBoundary_dualGram_zeroZero, atomBoundary_dualGram_twoTwo,
    atomBoundary_dualGram_zeroTwo, quadBoundaryScale_zero, quadBoundaryScale_two]
  norm_num

end Calibration

end Gtz
