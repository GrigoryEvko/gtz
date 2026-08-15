import Gtz.Design.RowCertificateAtlas

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

/-!
# The Z-matrix alternative

The row-certificate bridge reads three minors from one positive vector.  This
module supplies the two missing directions of that reading, at the exact `3x3`
symmetric Z-matrix shape of every atlas cell.

* `zThreeRowCertificate_of_minors` — three positive leading minors return an
  EXPLICIT positive vector whose three row readings all equal the determinant.
  The vector is the adjugate row sum, and the Z-signs make each cofactor a sum
  of nonnegative terms with one strictly positive anchor.
* `zThreeDualWitness_of_corner`, `_of_minorTwo`, `_of_det` — each minor failure
  returns an explicit nonzero nonnegative vector with all three row readings
  nonpositive.  The witnesses are a standard basis vector, a `2x2` adjugate
  column, and the `3x3` adjugate column.
* `zThreeDualWitness_of_not_minors` — the packaged alternative: a cell matrix
  with some minor not positive carries a dual witness.
* `zThree_gershgorin_of_dualWitness` — a dual witness forces a diagonally
  non-dominant row.  This is the exact necessity behind the probe law that a
  failing tree names a bad edge.

Every statement is scalar.  The matrix is `!![a, b, c; b, d, e; c, e, f]` with
`b, c, e ≤ 0`, and a row reading at `(u₁, u₂, u₃)` is the literal linear form.
-/

namespace Gtz

/-! ## The forward direction: minors give the adjugate certificate -/

/-- The two off-corner diagonal entries of a Z-matrix with positive leading
minors are positive. -/
theorem zThree_diag_pos {a b c d e f : ℝ}
    (hb : b ≤ 0) (hc : c ≤ 0) (he : e ≤ 0)
    (hcorner : 0 < a) (hminorTwo : 0 < a * d - b ^ 2)
    (hdet : 0 < a * d * f - a * e ^ 2 - b ^ 2 * f + 2 * b * c * e - c ^ 2 * d) :
    0 < d ∧ 0 < f := by
  have hd : 0 < d := by nlinarith
  refine ⟨hd, ?_⟩
  by_contra hf
  push Not at hf
  have hbce : b * c * e ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos ((by nlinarith : (0:ℝ) ≤ b * c)) he
  nlinarith [mul_nonneg (sq_nonneg c) hd.le, mul_nonneg hcorner.le (sq_nonneg e),
    mul_nonneg (neg_nonneg.mpr hf) hminorTwo.le]

/-- The first adjugate cofactor block is positive: `a * (d * f - e ^ 2)`
dominates the determinant under the Z-signs. -/
theorem zThree_cofactorOne_pos {a b c d e f : ℝ}
    (hb : b ≤ 0) (hc : c ≤ 0) (he : e ≤ 0) (hcorner : 0 < a)
    (hdet : 0 < a * d * f - a * e ^ 2 - b ^ 2 * f + 2 * b * c * e - c ^ 2 * d)
    (hf : 0 < f) (hd : 0 < d) :
    0 < d * f - e ^ 2 := by
  nlinarith [mul_nonneg (mul_nonneg (neg_nonneg.mpr hb) (neg_nonneg.mpr hc)) (neg_nonneg.mpr he), sq_nonneg b, sq_nonneg c]

/-- The second diagonal cofactor is positive under the Z-signs. -/
theorem zThree_cofactorTwo_pos {a b c d e f : ℝ}
    (hb : b ≤ 0) (hc : c ≤ 0) (he : e ≤ 0) (hcorner : 0 < a)
    (hdet : 0 < a * d * f - a * e ^ 2 - b ^ 2 * f + 2 * b * c * e - c ^ 2 * d)
    (hd : 0 < d) (hf : 0 < f) :
    0 < a * f - c ^ 2 := by
  have hbce : b * c * e ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos ((by nlinarith : (0:ℝ) ≤ b * c)) he
  nlinarith [mul_nonneg (sq_nonneg b) hf.le, mul_nonneg hcorner.le (sq_nonneg e)]

/-- **THE ADJUGATE ROW CERTIFICATE.**  Three positive leading minors of a
symmetric `3x3` Z-matrix return an explicit positive vector whose three row
readings all equal the determinant.  The vector is the adjugate row sum:
each entry is one positive cofactor plus four nonnegative Z-sign products. -/
theorem zThreeRowCertificate_of_minors {a b c d e f : ℝ}
    (hb : b ≤ 0) (hc : c ≤ 0) (he : e ≤ 0)
    (hcorner : 0 < a) (hminorTwo : 0 < a * d - b ^ 2)
    (hdet : 0 < a * d * f - a * e ^ 2 - b ^ 2 * f + 2 * b * c * e - c ^ 2 * d) :
    ∃ uOne uTwo uThree : ℝ, 0 < uOne ∧ 0 < uTwo ∧ 0 < uThree
      ∧ 0 < a * uOne + b * uTwo + c * uThree
      ∧ 0 < b * uOne + d * uTwo + e * uThree
      ∧ 0 < c * uOne + e * uTwo + f * uThree := by
  obtain ⟨hd, hf⟩ := zThree_diag_pos hb hc he hcorner hminorTwo hdet
  refine ⟨(d * f - e ^ 2) + (c * e - b * f) + (b * e - c * d),
    (c * e - b * f) + (a * f - c ^ 2) + (b * c - a * e),
    (b * e - c * d) + (b * c - a * e) + (a * d - b ^ 2), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hone := zThree_cofactorOne_pos hb hc he hcorner hdet hf hd
    nlinarith [mul_nonneg (neg_nonneg.mpr hc) (neg_nonneg.mpr he), mul_nonneg (neg_nonneg.mpr hb) hf.le,
      mul_nonneg (neg_nonneg.mpr hb) (neg_nonneg.mpr he), mul_nonneg (neg_nonneg.mpr hc) hd.le]
  · have htwo := zThree_cofactorTwo_pos hb hc he hcorner hdet hd hf
    nlinarith [mul_nonneg (neg_nonneg.mpr hc) (neg_nonneg.mpr he), mul_nonneg (neg_nonneg.mpr hb) hf.le,
      mul_nonneg (neg_nonneg.mpr hb) (neg_nonneg.mpr hc), mul_nonneg (neg_nonneg.mpr he) hcorner.le]
  · nlinarith [mul_nonneg (neg_nonneg.mpr hb) (neg_nonneg.mpr he), mul_nonneg (neg_nonneg.mpr hc) hd.le,
      mul_nonneg (neg_nonneg.mpr hb) (neg_nonneg.mpr hc), mul_nonneg (neg_nonneg.mpr he) hcorner.le]
  · have hrow : a * ((d * f - e ^ 2) + (c * e - b * f) + (b * e - c * d))
        + b * ((c * e - b * f) + (a * f - c ^ 2) + (b * c - a * e))
        + c * ((b * e - c * d) + (b * c - a * e) + (a * d - b ^ 2))
        = a * d * f - a * e ^ 2 - b ^ 2 * f + 2 * b * c * e - c ^ 2 * d := by ring
    linarith [hrow.ge, hrow.le, hdet]
  · have hrow : b * ((d * f - e ^ 2) + (c * e - b * f) + (b * e - c * d))
        + d * ((c * e - b * f) + (a * f - c ^ 2) + (b * c - a * e))
        + e * ((b * e - c * d) + (b * c - a * e) + (a * d - b ^ 2))
        = a * d * f - a * e ^ 2 - b ^ 2 * f + 2 * b * c * e - c ^ 2 * d := by ring
    linarith [hrow.ge, hrow.le, hdet]
  · have hrow : c * ((d * f - e ^ 2) + (c * e - b * f) + (b * e - c * d))
        + e * ((c * e - b * f) + (a * f - c ^ 2) + (b * c - a * e))
        + f * ((b * e - c * d) + (b * c - a * e) + (a * d - b ^ 2))
        = a * d * f - a * e ^ 2 - b ^ 2 * f + 2 * b * c * e - c ^ 2 * d := by ring
    linarith [hrow.ge, hrow.le, hdet]

/-! ## The reverse direction: minor failures give dual witnesses -/

/-- A nonpositive corner gives the first basis vector as a dual witness. -/
theorem zThreeDualWitness_of_corner {a b c d e f : ℝ}
    (hb : b ≤ 0) (hc : c ≤ 0) (hcorner : a ≤ 0) :
    ∃ yOne yTwo yThree : ℝ, 0 ≤ yOne ∧ 0 ≤ yTwo ∧ 0 ≤ yThree
      ∧ ¬ (yOne = 0 ∧ yTwo = 0 ∧ yThree = 0)
      ∧ a * yOne + b * yTwo + c * yThree ≤ 0
      ∧ b * yOne + d * yTwo + e * yThree ≤ 0
      ∧ c * yOne + e * yTwo + f * yThree ≤ 0 := by
  refine ⟨1, 0, 0, by norm_num, le_rfl, le_rfl, ?_, by linarith, by linarith, by linarith⟩
  intro habsurd
  exact one_ne_zero habsurd.1

/-- A failed second minor under a positive corner gives the `2x2` adjugate
column as a dual witness. -/
theorem zThreeDualWitness_of_minorTwo {a b c d e f : ℝ}
    (hb : b ≤ 0) (hc : c ≤ 0) (he : e ≤ 0)
    (hcorner : 0 < a) (hminorTwo : a * d - b ^ 2 ≤ 0) :
    ∃ yOne yTwo yThree : ℝ, 0 ≤ yOne ∧ 0 ≤ yTwo ∧ 0 ≤ yThree
      ∧ ¬ (yOne = 0 ∧ yTwo = 0 ∧ yThree = 0)
      ∧ a * yOne + b * yTwo + c * yThree ≤ 0
      ∧ b * yOne + d * yTwo + e * yThree ≤ 0
      ∧ c * yOne + e * yTwo + f * yThree ≤ 0 := by
  refine ⟨-b, a, 0, neg_nonneg.mpr hb, hcorner.le, le_rfl, ?_, ?_, ?_, ?_⟩
  · intro habsurd
    exact hcorner.ne' habsurd.2.1
  · nlinarith
  · nlinarith
  · nlinarith [mul_nonneg (neg_nonneg.mpr hb) (neg_nonneg.mpr hc), mul_nonpos_of_nonneg_of_nonpos hcorner.le he]

/-- A failed determinant under positive earlier minors gives the `3x3`
adjugate column as a dual witness. -/
theorem zThreeDualWitness_of_det {a b c d e f : ℝ}
    (hb : b ≤ 0) (hc : c ≤ 0) (he : e ≤ 0)
    (hcorner : 0 < a) (hminorTwo : 0 < a * d - b ^ 2)
    (hdet : a * d * f - a * e ^ 2 - b ^ 2 * f + 2 * b * c * e - c ^ 2 * d ≤ 0) :
    ∃ yOne yTwo yThree : ℝ, 0 ≤ yOne ∧ 0 ≤ yTwo ∧ 0 ≤ yThree
      ∧ ¬ (yOne = 0 ∧ yTwo = 0 ∧ yThree = 0)
      ∧ a * yOne + b * yTwo + c * yThree ≤ 0
      ∧ b * yOne + d * yTwo + e * yThree ≤ 0
      ∧ c * yOne + e * yTwo + f * yThree ≤ 0 := by
  refine ⟨b * e - c * d, b * c - a * e, a * d - b ^ 2, ?_, ?_, hminorTwo.le, ?_, ?_, ?_, ?_⟩
  · nlinarith [mul_nonneg (neg_nonneg.mpr hb) (neg_nonneg.mpr he), mul_nonpos_of_nonpos_of_nonneg hc
      (by nlinarith : (0 : ℝ) ≤ d)]
  · nlinarith [mul_nonneg (neg_nonneg.mpr hb) (neg_nonneg.mpr hc), mul_nonpos_of_nonneg_of_nonpos hcorner.le he]
  · intro habsurd
    exact hminorTwo.ne' habsurd.2.2
  · have hrow : a * (b * e - c * d) + b * (b * c - a * e) + c * (a * d - b ^ 2) = 0 := by ring
    linarith [hrow.le]
  · have hrow : b * (b * e - c * d) + d * (b * c - a * e) + e * (a * d - b ^ 2) = 0 := by ring
    linarith [hrow.le]
  · have hrow : c * (b * e - c * d) + e * (b * c - a * e) + f * (a * d - b ^ 2)
        = a * d * f - a * e ^ 2 - b ^ 2 * f + 2 * b * c * e - c ^ 2 * d := by ring
    linarith [hrow.le, hdet]

/-- **THE PACKAGED ALTERNATIVE.**  A symmetric `3x3` Z-matrix with some
leading minor not positive carries a nonzero nonnegative dual vector with all
three row readings nonpositive. -/
theorem zThreeDualWitness_of_not_minors {a b c d e f : ℝ}
    (hb : b ≤ 0) (hc : c ≤ 0) (he : e ≤ 0)
    (hfail : ¬ (0 < a ∧ 0 < a * d - b ^ 2
      ∧ 0 < a * d * f - a * e ^ 2 - b ^ 2 * f + 2 * b * c * e - c ^ 2 * d)) :
    ∃ yOne yTwo yThree : ℝ, 0 ≤ yOne ∧ 0 ≤ yTwo ∧ 0 ≤ yThree
      ∧ ¬ (yOne = 0 ∧ yTwo = 0 ∧ yThree = 0)
      ∧ a * yOne + b * yTwo + c * yThree ≤ 0
      ∧ b * yOne + d * yTwo + e * yThree ≤ 0
      ∧ c * yOne + e * yTwo + f * yThree ≤ 0 := by
  by_cases hcorner : 0 < a
  · by_cases hminorTwo : 0 < a * d - b ^ 2
    · have hdet : a * d * f - a * e ^ 2 - b ^ 2 * f + 2 * b * c * e - c ^ 2 * d ≤ 0 := by
        by_contra hpos
        exact hfail ⟨hcorner, hminorTwo, lt_of_not_ge fun hge => hpos (by linarith)⟩
      exact zThreeDualWitness_of_det hb hc he hcorner hminorTwo hdet
    · exact zThreeDualWitness_of_minorTwo hb hc he hcorner (le_of_not_gt hminorTwo)
  · exact zThreeDualWitness_of_corner hb hc (le_of_not_gt hcorner)

/-! ## The Gershgorin necessity -/

/-- A dual witness forces a diagonally non-dominant row: some diagonal entry
is at most the negated off-diagonal row sum.  The row is the maximal witness
coordinate. -/
theorem zThree_gershgorin_of_dualWitness {a b c d e f : ℝ}
    (hb : b ≤ 0) (hc : c ≤ 0) (he : e ≤ 0)
    {yOne yTwo yThree : ℝ} (hyOne : 0 ≤ yOne) (hyTwo : 0 ≤ yTwo) (hyThree : 0 ≤ yThree)
    (hne : ¬ (yOne = 0 ∧ yTwo = 0 ∧ yThree = 0))
    (hrowOne : a * yOne + b * yTwo + c * yThree ≤ 0)
    (hrowTwo : b * yOne + d * yTwo + e * yThree ≤ 0)
    (hrowThree : c * yOne + e * yTwo + f * yThree ≤ 0) :
    a ≤ -b - c ∨ d ≤ -b - e ∨ f ≤ -c - e := by
  have hcornerCase : ∀ {u v w bu cu du : ℝ}, 0 ≤ u → 0 ≤ v → 0 ≤ w
      → v ≤ u → w ≤ u → 0 < u
      → bu ≤ 0 → cu ≤ 0 → du * u + bu * v + cu * w ≤ 0 → du ≤ -bu - cu := by
    intro u v w bu cu du hu hv hw hvu hwu hupos hbu hcu hrow
    have hbTerm : (-bu) * v ≤ (-bu) * u := mul_le_mul_of_nonneg_left hvu (neg_nonneg.mpr hbu)
    have hcTerm : (-cu) * w ≤ (-cu) * u := mul_le_mul_of_nonneg_left hwu (neg_nonneg.mpr hcu)
    have hbound : du * u ≤ (-bu - cu) * u := by nlinarith
    exact le_of_mul_le_mul_right hbound hupos
  rcases le_total yOne yTwo with hOneTwo | hTwoOne
  · rcases le_total yTwo yThree with hTwoThree | hThreeTwo
    · right; right
      have hupos : 0 < yThree := by
        rcases lt_or_eq_of_le hyThree with hpos | hzero
        · exact hpos
        · refine absurd ⟨le_antisymm (by linarith) hyOne,
            le_antisymm (by linarith) hyTwo, hzero.symm⟩ hne
      exact hcornerCase hyThree hyOne hyTwo (by linarith) hTwoThree hupos hc he
        (by linarith [hrowThree])
    · right; left
      have hupos : 0 < yTwo := by
        rcases lt_or_eq_of_le hyTwo with hpos | hzero
        · exact hpos
        · refine absurd ⟨le_antisymm (by linarith) hyOne, hzero.symm,
            le_antisymm (by linarith) hyThree⟩ hne
      exact hcornerCase hyTwo hyOne hyThree hOneTwo hThreeTwo hupos hb he
        (by linarith [hrowTwo])
  · rcases le_total yOne yThree with hOneThree | hThreeOne
    · right; right
      have hupos : 0 < yThree := by
        rcases lt_or_eq_of_le hyThree with hpos | hzero
        · exact hpos
        · refine absurd ⟨le_antisymm (by linarith) hyOne,
            le_antisymm (by linarith) hyTwo, hzero.symm⟩ hne
      exact hcornerCase hyThree hyOne hyTwo hOneThree (by linarith) hupos hc he
        (by linarith [hrowThree])
    · left
      have hupos : 0 < yOne := by
        rcases lt_or_eq_of_le hyOne with hpos | hzero
        · exact hpos
        · refine absurd ⟨hzero.symm, le_antisymm (by linarith) hyTwo,
            le_antisymm (by linarith) hyThree⟩ hne
      exact hcornerCase hyOne hyTwo hyThree hTwoOne hThreeOne hupos hb hc
        (by linarith [hrowOne])

end Gtz
