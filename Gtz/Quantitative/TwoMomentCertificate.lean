/-
# The two-moment certificate, and the exact obstruction that caps it

A triple `C` of a weighted `(m,3)` design dominates iff its Gram `S_C` satisfies
`S_C ⪰ I`.  This file isolates the strongest sufficient condition for that which
reads only TWO of the three elementary symmetric functions of `S_C` — its trace
and its determinant — and then shows, by an exact witness already in the repo,
that no such condition can settle `(6,3)`.

## The certificate

`twoMomentGap = 4·det S_C − (tr S_C − 1)²`, written in the six inner products of
the triple.  `dominates_of_twoMomentGap_nonneg`: a heavy triple with
`twoMomentGap ≥ 0` dominates.  The whole proof is one factorisation,

  `x(L − x)² − (L − 1)²  =  (x − 1)·(x² + (1 − 2L)x + (L − 1)²)`,

evaluated at an eigenvalue `x` of `S_C` with `L = tr S_C`: AM–GM on the other two
eigenvalues gives `4·det S_C ≤ x(L − x)²`, the quadratic cofactor is positive on
`[0,1]` whenever `L > 3` (its value at `1` is `(L−1)(L−3)`), and the sign of the
linear factor then forces `x ≥ 1`.  No SDP, no hierarchy: the multiplier is the
explicit quadratic `x² + (1 − 2L)x + (L − 1)²`.

Equivalently, in the gap scalars `aᵢ = eᵢ(Gram − I)`, the criterion is
`4a₂ + 4a₃ ≥ a₁²` — so it is `discriminantTie` and the SUM of the three `2×2`
minors, traded against the squared trace.

The criterion is SHARP among two-moment criteria: if `L > 3` and
`4d < (L − 1)²`, then `diag(x, (L−x)/2, (L−x)/2)` with `x ∈ [0,1)` chosen so that
`x(L−x)² = 4d` is positive semidefinite, has trace `L` and determinant `d`, and
does NOT dominate.  So `twoMomentGap ≥ 0` is exactly the set of `(tr, det)` pairs
that force domination, and any criterion reading only `(tr, det)` is weaker.

## The obstruction

`icosaDesign` — the six real equiangular diagonals of the icosahedron, uniform
weight `1/6`, already proved here to dominate on `{0,2,4}` and in fact STRICTLY
(`icosaDesign_dominates`, `icosaDesign_strictly_dominates`) — has

  `twoMomentGap = 8·⟨a,b⟩⟨a,c⟩⟨b,c⟩ − 104/5`   at every triple,

and the Bargmann triangle product squares to `(9/5)³ = 729/125 < 169/25`, so the
gap is at most `8·(13/5)⁻ − 104/5 < 0` at ALL twenty triples
(`icosa_twoMomentGap_neg`).  Hence `icosa_no_twoMoment_certificate`: a design
that dominates, on which the sharpest two-moment criterion fails everywhere.

Read as a lower bound on certificate shape: **any Positivstellensatz proof of
`GtzWeighted 6 3` must consume the middle symmetric function `e₂(Gram_C)` of a
triple, not only its trace and determinant.**  The two-moment relaxation is
exactly tight on the tetrahedron tie stratum (`tr = 9`, `det = 16`, gap `= 0`)
and strictly loses on the icosahedron, which is the other extreme of the same
`tr = 9` fibre.  The reason is visible in the proof: AM–GM is an equality only
when the two eigenvalues other than the minimum coincide, which is the
tetrahedron's `(1,4,4)`; the icosahedron's good triples are `(1.65…, 1.65…, 5.68…)`,
where the two coinciding eigenvalues are the SMALL ones and the bound is loose.

## Scope — what is NOT claimed

Nothing here proves or disproves `GtzWeighted 6 3`.  `twoMomentGap ≥ 0` is
sufficient for domination and is not necessary; the obstruction says only that
the two-moment relaxation of the covering problem is infeasible, which is a
statement about certificate SHAPE, not about the truth of the conjecture.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.LinAlg.PsdKit
import Gtz.Quantitative.DiscriminantSystem
import Gtz.Quantitative.RealnessEngine
import Gtz.Quantitative.DecisionAtlasSevenThree

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace Gtz

open Matrix

/-! ## The scalar heart: one factorisation and one AM–GM -/

/-- **The certificate identity.**  The whole two-moment criterion is this single
factorisation; the quadratic cofactor is the Positivstellensatz multiplier. -/
theorem twoMoment_factorisation (smallest total : ℝ) :
    smallest * (total - smallest) ^ 2 - (total - 1) ^ 2
      = (smallest - 1)
        * (smallest ^ 2 + (1 - 2 * total) * smallest + (total - 1) ^ 2) := by
  ring

/-- The multiplier is strictly positive on the unit interval once the trace
exceeds the rank: its value at `1` is `(total − 1)(total − 3)`, and it decreases
towards `1` because its vertex sits at `total − 1/2 > 1`. -/
theorem twoMoment_multiplier_pos {smallest total : ℝ} (hnonneg : 0 ≤ smallest)
    (hsmall : smallest ≤ 1) (hbig : 3 < total) :
    0 < smallest ^ 2 + (1 - 2 * total) * smallest + (total - 1) ^ 2 := by
  nlinarith [mul_nonneg hnonneg (sub_nonneg.mpr hsmall), sq_nonneg (smallest - 1),
    mul_nonneg (sub_nonneg.mpr hsmall) (le_of_lt (sub_pos.mpr hbig))]

/-- **The scalar certificate.**  Three nonnegative reals whose sum exceeds `3`
and whose product clears the two-moment threshold are each at least `1`.  Stated
asymmetrically in the first argument; the hypotheses are symmetric, so the other
two follow by reordering. -/
theorem one_le_of_twoMoment {first second third : ℝ} (hfirst : 0 ≤ first)
    (hsecond : 0 ≤ second) (hthird : 0 ≤ third)
    (hbig : 3 < first + second + third)
    (hmoment : (first + second + third - 1) ^ 2 ≤ 4 * (first * second * third)) :
    1 ≤ first := by
  by_contra hcontra
  push Not at hcontra
  have hamgm : 4 * (second * third) ≤ (second + third) ^ 2 := by
    nlinarith [sq_nonneg (second - third)]
  have hbound :
      4 * (first * second * third)
        ≤ first * ((first + second + third) - first) ^ 2 := by
    nlinarith [hamgm, hfirst]
  have hmult := twoMoment_multiplier_pos hfirst hcontra.le hbig
  have hfact := twoMoment_factorisation first (first + second + third)
  nlinarith [hfact, hmult, hbound, hmoment,
    mul_pos_of_neg_of_neg (sub_neg.mpr hcontra) (neg_neg_iff_pos.mpr hmult)]

/-! ## From the two moments of a positive semidefinite form to `⪰ I` -/

/-- The spectral theorem in congruence form: the eigenvector unitary conjugates
the eigenvalue diagonal back to the form. -/
theorem eigenvector_congruence {form : Matrix (Fin 3) (Fin 3) ℝ}
    (hform : form.IsHermitian) :
    (hform.eigenvectorUnitary : Matrix (Fin 3) (Fin 3) ℝ)
        * (Matrix.diagonal hform.eigenvalues)
        * (hform.eigenvectorUnitary : Matrix (Fin 3) (Fin 3) ℝ)ᴴ = form := by
  have hthm := hform.spectral_theorem
  simp [Unitary.conjStarAlgAut] at hthm
  exact hthm.symm

/-- Eigenvalue shift: a Hermitian form all of whose eigenvalues are at least one
dominates the identity.  Congruence of a nonnegative diagonal by the eigenvector
unitary. -/
theorem posSemidef_sub_one_of_eigenvalues_ge_one
    {form : Matrix (Fin 3) (Fin 3) ℝ} (hform : form.IsHermitian)
    (heigen : ∀ slot, (1 : ℝ) ≤ hform.eigenvalues slot) :
    (form - 1).PosSemidef := by
  classical
  set unitaryPart : Matrix (Fin 3) (Fin 3) ℝ :=
    (hform.eigenvectorUnitary : Matrix (Fin 3) (Fin 3) ℝ) with hunitaryPart
  have hunitaryRight : unitaryPart * unitaryPartᴴ = 1 := by
    have hmem := hform.eigenvectorUnitary.2
    rw [Matrix.mem_unitaryGroup_iff] at hmem
    simpa [hunitaryPart, Matrix.star_eq_conjTranspose] using hmem
  have hshifted :
      (Matrix.diagonal fun slot => hform.eigenvalues slot - 1).PosSemidef :=
    Matrix.posSemidef_diagonal_iff.mpr fun slot => by linarith [heigen slot]
  have hconj := hshifted.mul_mul_conjTranspose_same unitaryPart
  have hspectral : unitaryPart * (Matrix.diagonal hform.eigenvalues) * unitaryPartᴴ = form :=
    eigenvector_congruence hform
  have hsplit :
      unitaryPart * (Matrix.diagonal fun slot => hform.eigenvalues slot - 1) * unitaryPartᴴ
        = form - 1 := by
    have hdiagSplit :
        (Matrix.diagonal fun slot => hform.eigenvalues slot - 1)
          = Matrix.diagonal hform.eigenvalues - 1 := by
      ext rowIndex colIndex
      by_cases hdiag : rowIndex = colIndex
      · subst hdiag; simp
      · simp [Matrix.diagonal_apply_ne _ hdiag, Matrix.one_apply_ne hdiag]
    rw [hdiagSplit, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hspectral,
      hunitaryRight]
  rwa [hsplit] at hconj

/-- **The two-moment criterion, in matrix form.**  A positive semidefinite `3×3`
form whose trace exceeds `3` and whose determinant clears
`(tr − 1)²/4` dominates the identity. -/
theorem posSemidef_sub_one_of_twoMoment {form : Matrix (Fin 3) (Fin 3) ℝ}
    (hform : form.PosSemidef) (hbig : 3 < Matrix.trace form)
    (hmoment : (Matrix.trace form - 1) ^ 2 ≤ 4 * form.det) :
    (form - 1).PosSemidef := by
  classical
  set eigen : Fin 3 → ℝ := hform.1.eigenvalues with heigen
  have htrace : Matrix.trace form = eigen 0 + eigen 1 + eigen 2 := by
    have := hform.1.trace_eq_sum_eigenvalues
    simpa [heigen, Fin.sum_univ_three] using this
  have hdet : form.det = eigen 0 * eigen 1 * eigen 2 := by
    have := hform.1.det_eq_prod_eigenvalues
    simpa [heigen, Fin.prod_univ_three, mul_assoc] using this
  have hnonneg : ∀ slot, 0 ≤ eigen slot := fun slot => hform.eigenvalues_nonneg slot
  rw [htrace] at hbig hmoment
  rw [hdet] at hmoment
  have hslotZero : (1 : ℝ) ≤ eigen 0 :=
    one_le_of_twoMoment (hnonneg 0) (hnonneg 1) (hnonneg 2) hbig hmoment
  have hslotOne : (1 : ℝ) ≤ eigen 1 := by
    refine one_le_of_twoMoment (hnonneg 1) (hnonneg 0) (hnonneg 2) (by linarith) ?_
    calc (eigen 1 + eigen 0 + eigen 2 - 1) ^ 2
        = (eigen 0 + eigen 1 + eigen 2 - 1) ^ 2 := by ring
      _ ≤ 4 * (eigen 0 * eigen 1 * eigen 2) := hmoment
      _ = 4 * (eigen 1 * eigen 0 * eigen 2) := by ring
  have hslotTwo : (1 : ℝ) ≤ eigen 2 := by
    refine one_le_of_twoMoment (hnonneg 2) (hnonneg 0) (hnonneg 1) (by linarith) ?_
    calc (eigen 2 + eigen 0 + eigen 1 - 1) ^ 2
        = (eigen 0 + eigen 1 + eigen 2 - 1) ^ 2 := by ring
      _ ≤ 4 * (eigen 0 * eigen 1 * eigen 2) := hmoment
      _ = 4 * (eigen 2 * eigen 0 * eigen 1) := by ring
  refine posSemidef_sub_one_of_eigenvalues_ge_one hform.1 fun slot => ?_
  fin_cases slot
  · exact hslotZero
  · exact hslotOne
  · exact hslotTwo

/-! ## The gap in the six scalars of a triple -/

variable {m : ℕ}

/-- **The two-moment gap** of a triple, in its six inner products:
`4·det Gram − (tr Gram − 1)²`.  Degree three in the Gram entries — the same
degree as `discriminantTie`, and one polynomial rather than two. -/
def twoMomentGap (levFirst levSecond levThird pairFirstSecond pairFirstThird
    pairSecondThird : ℝ) : ℝ :=
  4 * (levFirst * levSecond * levThird
        + 2 * pairFirstSecond * pairFirstThird * pairSecondThird
        - levFirst * pairSecondThird ^ 2
        - levSecond * pairFirstThird ^ 2
        - levThird * pairFirstSecond ^ 2)
    - (levFirst + levSecond + levThird - 1) ^ 2

/-- The gap is the trace/determinant combination of the triple's Gram matrix. -/
theorem twoMomentGap_eq_det_trace (D : WeightedDesign m 3)
    (pivot pairFirst pairSecond : Fin m) :
    twoMomentGap (leverageOf (D.atom pivot)) (leverageOf (D.atom pairFirst))
        (leverageOf (D.atom pairSecond)) (atomPairing D pivot pairFirst)
        (atomPairing D pivot pairSecond) (atomPairing D pairFirst pairSecond)
      = 4 * ((tripleMatrix D pivot pairFirst pairSecond)ᵀ
              * tripleMatrix D pivot pairFirst pairSecond).det
        - (Matrix.trace ((tripleMatrix D pivot pairFirst pairSecond)ᵀ
              * tripleMatrix D pivot pairFirst pairSecond) - 1) ^ 2 := by
  have hentry := tripleMatrix_transpose_mul_apply D pivot pairFirst pairSecond
  rw [Matrix.det_fin_three, Matrix.trace_fin_three]
  simp only [hentry, tripleAtom, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  simp only [twoMomentGap, atomPairing, leverageOf, dotProduct_self_eq_sum_sq,
    dotProduct_comm]
  ring

/-- **THE CERTIFICATE.**  A triple whose two-moment gap is nonnegative and whose
total leverage exceeds the rank DOMINATES.  One polynomial inequality of degree
three, no test vector, no eigenvalue in the statement. -/
theorem dominates_of_twoMomentGap_nonneg (D : WeightedDesign m 3)
    {pivot pairFirst pairSecond : Fin m} (hpivotFirst : pivot ≠ pairFirst)
    (hpivotSecond : pivot ≠ pairSecond) (hpairDistinct : pairFirst ≠ pairSecond)
    (hheavy : 3 < leverageOf (D.atom pivot) + leverageOf (D.atom pairFirst)
        + leverageOf (D.atom pairSecond))
    (hgap : 0 ≤ twoMomentGap (leverageOf (D.atom pivot))
        (leverageOf (D.atom pairFirst)) (leverageOf (D.atom pairSecond))
        (atomPairing D pivot pairFirst) (atomPairing D pivot pairSecond)
        (atomPairing D pairFirst pairSecond)) :
    Dominates D {pivot, pairFirst, pairSecond} := by
  classical
  set gram := (tripleMatrix D pivot pairFirst pairSecond)ᵀ
      * tripleMatrix D pivot pairFirst pairSecond with hgram
  have hpsd : gram.PosSemidef := Matrix.posSemidef_conjTranspose_mul_self _
  have htrace : Matrix.trace gram
      = leverageOf (D.atom pivot) + leverageOf (D.atom pairFirst)
        + leverageOf (D.atom pairSecond) := by
    have hentry := tripleMatrix_transpose_mul_apply D pivot pairFirst pairSecond
    rw [hgram, Matrix.trace_fin_three]
    simp only [hentry, tripleAtom, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
    simp [leverageOf, dotProduct_self_eq_sum_sq]
  have hkey := twoMomentGap_eq_det_trace D pivot pairFirst pairSecond
  rw [← hgram] at hkey
  have hmoment : (Matrix.trace gram - 1) ^ 2 ≤ 4 * gram.det := by
    rw [hkey] at hgap; linarith
  have hbig : 3 < Matrix.trace gram := by rw [htrace]; exact hheavy
  have hgapPsd := posSemidef_sub_one_of_twoMoment hpsd hbig hmoment
  have hframe := tripleMatrix_mul_transpose D hpivotFirst hpivotSecond hpairDistinct
  rw [Dominates, ← hframe]
  exact (posSemidef_transpose_mul_sub_one_comm
    (tripleMatrix D pivot pairFirst pairSecond)).mp hgapPsd

/-! ## The obstruction: the icosahedron kills every two-moment criterion -/

/-- On `icosaDesign` the two-moment gap collapses to `8·τ − 104/5`, where `τ` is
the Bargmann triangle product `⟨a,b⟩⟨a,c⟩⟨b,c⟩` — the ONLY place the six scalars
remember more than their moduli. -/
theorem icosa_twoMomentGap_eq {atomFirst atomSecond atomThird : Fin 6}
    (hone : atomFirst ≠ atomSecond) (htwo : atomFirst ≠ atomThird)
    (hthree : atomSecond ≠ atomThird) :
    twoMomentGap (leverageOf (icosaDesign.atom atomFirst))
        (leverageOf (icosaDesign.atom atomSecond))
        (leverageOf (icosaDesign.atom atomThird))
        (atomPairing icosaDesign atomFirst atomSecond)
        (atomPairing icosaDesign atomFirst atomThird)
        (atomPairing icosaDesign atomSecond atomThird)
      = 8 * (atomPairing icosaDesign atomFirst atomSecond
              * atomPairing icosaDesign atomFirst atomThird
              * atomPairing icosaDesign atomSecond atomThird) - 104 / 5 := by
  have hlev : ∀ index : Fin 6, leverageOf (icosaDesign.atom index) = 3 := fun index => by
    have := icosaAtom_leverage index
    simpa [leverageOf, dotProduct_self_eq_sum_sq] using this
  have hsqOne : (atomPairing icosaDesign atomFirst atomSecond) ^ 2 = 9 / 5 :=
    icosaAtom_dot_sq_of_ne hone
  have hsqTwo : (atomPairing icosaDesign atomFirst atomThird) ^ 2 = 9 / 5 :=
    icosaAtom_dot_sq_of_ne htwo
  have hsqThree : (atomPairing icosaDesign atomSecond atomThird) ^ 2 = 9 / 5 :=
    icosaAtom_dot_sq_of_ne hthree
  rw [twoMomentGap, hlev, hlev, hlev]
  linear_combination (-12 : ℝ) * hsqThree - 12 * hsqTwo - 12 * hsqOne

/-- **THE OBSTRUCTION.**  Every one of the twenty triples of `icosaDesign` has a
strictly negative two-moment gap — while the design dominates, strictly, on
`{0,2,4}`.  So the sharpest criterion that reads only the trace and the
determinant of a triple's Gram certifies NOTHING on this design. -/
theorem icosa_twoMomentGap_neg {atomFirst atomSecond atomThird : Fin 6}
    (hone : atomFirst ≠ atomSecond) (htwo : atomFirst ≠ atomThird)
    (hthree : atomSecond ≠ atomThird) :
    twoMomentGap (leverageOf (icosaDesign.atom atomFirst))
        (leverageOf (icosaDesign.atom atomSecond))
        (leverageOf (icosaDesign.atom atomThird))
        (atomPairing icosaDesign atomFirst atomSecond)
        (atomPairing icosaDesign atomFirst atomThird)
        (atomPairing icosaDesign atomSecond atomThird) < 0 := by
  have hsqOne : (atomPairing icosaDesign atomFirst atomSecond) ^ 2 = 9 / 5 :=
    icosaAtom_dot_sq_of_ne hone
  have hsqTwo : (atomPairing icosaDesign atomFirst atomThird) ^ 2 = 9 / 5 :=
    icosaAtom_dot_sq_of_ne htwo
  have hsqThree : (atomPairing icosaDesign atomSecond atomThird) ^ 2 = 9 / 5 :=
    icosaAtom_dot_sq_of_ne hthree
  have htriangleSq :
      (atomPairing icosaDesign atomFirst atomSecond
        * atomPairing icosaDesign atomFirst atomThird
        * atomPairing icosaDesign atomSecond atomThird) ^ 2 = 729 / 125 := by
    have hexpand :
        (atomPairing icosaDesign atomFirst atomSecond
          * atomPairing icosaDesign atomFirst atomThird
          * atomPairing icosaDesign atomSecond atomThird) ^ 2
          = (atomPairing icosaDesign atomFirst atomSecond) ^ 2
            * (atomPairing icosaDesign atomFirst atomThird) ^ 2
            * (atomPairing icosaDesign atomSecond atomThird) ^ 2 := by ring
    rw [hexpand, hsqOne, hsqTwo, hsqThree]; norm_num
  rw [icosa_twoMomentGap_eq hone htwo hthree]
  nlinarith [htriangleSq, sq_nonneg (atomPairing icosaDesign atomFirst atomSecond
        * atomPairing icosaDesign atomFirst atomThird
        * atomPairing icosaDesign atomSecond atomThird - 13 / 5)]

/-- **The obstruction, assembled**: a weighted `(6,3)` design that DOMINATES yet
on which the two-moment certificate is negative at every triple.  Any
Positivstellensatz proof of `GtzWeighted 6 3` must therefore read the middle
symmetric function `e₂(Gram_C)` of a triple, not only its trace and determinant. -/
theorem icosa_no_twoMoment_certificate :
    Dominates icosaDesign {0, 2, 4}
      ∧ ∀ atomFirst atomSecond atomThird : Fin 6, atomFirst ≠ atomSecond →
          atomFirst ≠ atomThird → atomSecond ≠ atomThird →
          twoMomentGap (leverageOf (icosaDesign.atom atomFirst))
              (leverageOf (icosaDesign.atom atomSecond))
              (leverageOf (icosaDesign.atom atomThird))
              (atomPairing icosaDesign atomFirst atomSecond)
              (atomPairing icosaDesign atomFirst atomThird)
              (atomPairing icosaDesign atomSecond atomThird) < 0 :=
  ⟨icosaDesign_dominates, fun _ _ _ hone htwo hthree =>
    icosa_twoMomentGap_neg hone htwo hthree⟩

/-! ## The tie stratum, where the certificate is exactly tight -/

/-- On the `(4,3)` tetrahedron every triple has leverage sum `9` and Gram
determinant `16`, so the two-moment gap is exactly `0`: the certificate is TIGHT
on the tie stratum it was designed to reach, and reaches it with no slack.

The distinct-atom dot product `tetraAtom_dot_of_ne` used below is NOT restated
here — it is imported from `Gtz/Quantitative/DecisionAtlasSevenThree.lean`,
which declared it first.  An identical copy did live here; Lean 4.32 accepts two
files declaring one global name without complaint and silently lets the last
import win, so the duplicate was a latent hazard rather than a build error. -/
theorem tetra_twoMomentGap_eq_zero {atomFirst atomSecond atomThird : Fin 4}
    (hone : atomFirst ≠ atomSecond) (htwo : atomFirst ≠ atomThird)
    (hthree : atomSecond ≠ atomThird) :
    twoMomentGap (leverageOf (tetraDesign.atom atomFirst))
        (leverageOf (tetraDesign.atom atomSecond))
        (leverageOf (tetraDesign.atom atomThird))
        (atomPairing tetraDesign atomFirst atomSecond)
        (atomPairing tetraDesign atomFirst atomThird)
        (atomPairing tetraDesign atomSecond atomThird) = 0 := by
  have hlev : ∀ index : Fin 4, leverageOf (tetraDesign.atom index) = 3 := fun index => by
    have := tetraAtom_dot_self index
    simpa [leverageOf, dotProduct_self_eq_sum_sq, tetraDesign] using this
  have hpairOne : atomPairing tetraDesign atomFirst atomSecond = -1 :=
    tetraAtom_dot_of_ne hone
  have hpairTwo : atomPairing tetraDesign atomFirst atomThird = -1 :=
    tetraAtom_dot_of_ne htwo
  have hpairThree : atomPairing tetraDesign atomSecond atomThird = -1 :=
    tetraAtom_dot_of_ne hthree
  rw [twoMomentGap, hlev, hlev, hlev, hpairOne, hpairTwo, hpairThree]
  norm_num

end Gtz
