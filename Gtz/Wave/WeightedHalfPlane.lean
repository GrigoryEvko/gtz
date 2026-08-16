/-
# The weighted half-plane floor, and the one-line normal it was built for

`Gtz/Design/BhatiaDavis.lean` carries the MEAN-ZERO half-plane lemma: on
`∑ x = 0`, `∑ x² = n` some pair has product at most `-1`, with the two-valued
equality locus in `Gtz.tie_two_valued`.  Every landed consumer of it, in
`Gtz/Corner/`, works in that same normalization.

The one-line stratum does not present a mean-zero family.  It presents an
ORTHOGONALITY.  Write `n` for a unit normal of the line and `p` for an in-plane
probe.  Weighted Parseval read on the pair `(p, n)` gives

  `∑ c, w c * (a c ⬝ᵥ p) * (a c ⬝ᵥ n) = p ⬝ᵥ n = 0`

and the three line atoms drop out of it, because they are orthogonal to `n`.
So the free atoms carry an exact orthogonality with no mean-zero structure
anywhere.  This file supplies the half-plane floor in that shape.

The telescope generalizes: for ANY two families and ANY two reals,

  `∑ (M * x i - y i) * (y i - m * x i)
     = (M + m) * ∑ x i * y i - ∑ y i ^ 2 - M * m * ∑ x i ^ 2`.

Under orthogonality the first term vanishes, and nonnegativity of every factor
gives `∑ y² ≤ -(M * m) * ∑ x²`.  The equality locus is again two-valued, and
that is the classification the mean-zero file leaves unconsumed.

Setting `x ≡ 1` recovers the mean-zero hypotheses `∑ y = 0` and `∑ x² = n`, and
the floor becomes `n ≤ -(M * m) * n`, which is `M * m ≤ -1`.  So the landed
lemma is the constant-`x` case.  This file does NOT restate it: the mean-zero
statement and its pair form stay where they are, and are cited, not copied.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Design.BhatiaDavis
import Gtz.Reduction.RealVolumeFloor

namespace Gtz

open Finset Matrix

variable {n : ℕ}

/-! ## 1. The telescope, with no hypothesis at all -/

/-- **THE WEIGHTED HALF-PLANE TELESCOPE.**  An identity, for any two families
and any two reals.  `Gtz.bhatiaDavis_telescope` is the case `x ≡ 1` after its
two hypotheses are spent. -/
theorem weightedHalfPlane_telescope (x y : Fin n → ℝ) (bigM smallM : ℝ) :
    ∑ i, (bigM * x i - y i) * (y i - smallM * x i)
      = (bigM + smallM) * (∑ i, x i * y i) - (∑ i, y i ^ 2)
        - bigM * smallM * (∑ i, x i ^ 2) := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- A sandwich on one slot, in the form the floor consumes.  Either ordering of
the two rays gives a nonnegative product. -/
theorem sandwich_nonneg_of_between {xi yi bigM smallM : ℝ}
    (hbetween : (smallM * xi ≤ yi ∧ yi ≤ bigM * xi)
      ∨ (bigM * xi ≤ yi ∧ yi ≤ smallM * xi)) :
    0 ≤ (bigM * xi - yi) * (yi - smallM * xi) := by
  rcases hbetween with ⟨hlow, hhigh⟩ | ⟨hlow, hhigh⟩
  · exact mul_nonneg (sub_nonneg.mpr hhigh) (sub_nonneg.mpr hlow)
  · nlinarith [hlow, hhigh]

/-! ## 2. The floor -/

/-- **THE WEIGHTED HALF-PLANE FLOOR.**  Under one orthogonality and a slotwise
sandwich, the `y` energy is capped by the negated product of the two rays times
the `x` energy.  No mean-zero hypothesis, no sphere normalization, and the index
count never appears. -/
theorem sum_sq_le_of_orthogonal_of_sandwich (x y : Fin n → ℝ) (bigM smallM : ℝ)
    (horthogonal : ∑ i, x i * y i = 0)
    (hsandwich : ∀ i, 0 ≤ (bigM * x i - y i) * (y i - smallM * x i)) :
    ∑ i, y i ^ 2 ≤ -(bigM * smallM) * ∑ i, x i ^ 2 := by
  have hnonneg : 0 ≤ ∑ i, (bigM * x i - y i) * (y i - smallM * x i) :=
    Finset.sum_nonneg fun i _ => hsandwich i
  rw [weightedHalfPlane_telescope x y bigM smallM, horthogonal] at hnonneg
  linarith

/-- The floor in its contrapositive reading: an `y` energy at or beyond the cap
forces the ray product up.  This is the direction a covering argument uses, and
it needs the `x` energy strictly positive. -/
theorem neg_one_le_mul_of_sum_sq_ge (x y : Fin n → ℝ) (bigM smallM cap : ℝ)
    (hcap : 0 < cap)
    (hxenergy : ∑ i, x i ^ 2 = cap)
    (horthogonal : ∑ i, x i * y i = 0)
    (hsandwich : ∀ i, 0 ≤ (bigM * x i - y i) * (y i - smallM * x i))
    (hyenergy : cap ≤ ∑ i, y i ^ 2) :
    bigM * smallM ≤ -1 := by
  have hfloor := sum_sq_le_of_orthogonal_of_sandwich x y bigM smallM horthogonal hsandwich
  rw [hxenergy] at hfloor
  nlinarith [hfloor, hyenergy, hcap]

/-! ## 3. The equality locus, which is the classification the mean-zero file
leaves unconsumed -/

/-- **TWO-VALUED AT EQUALITY.**  If the floor is attained then every slot sits on
one of the two rays.  This is `Gtz.tie_two_valued` transported out of the
mean-zero normalization, and unlike that statement it reads a genuine pair of
families. -/
theorem two_valued_of_orthogonal_of_sandwich_eq (x y : Fin n → ℝ) (bigM smallM : ℝ)
    (horthogonal : ∑ i, x i * y i = 0)
    (hsandwich : ∀ i, 0 ≤ (bigM * x i - y i) * (y i - smallM * x i))
    (hequality : ∑ i, y i ^ 2 = -(bigM * smallM) * ∑ i, x i ^ 2) :
    ∀ i, y i = bigM * x i ∨ y i = smallM * x i := by
  have hzero : ∑ i, (bigM * x i - y i) * (y i - smallM * x i) = 0 := by
    rw [weightedHalfPlane_telescope x y bigM smallM, horthogonal, hequality]; ring
  have hterms :=
    (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hsandwich i).mp hzero
  intro i
  rcases mul_eq_zero.mp (hterms i (Finset.mem_univ i)) with h | h
  · exact Or.inl (by linarith [sub_eq_zero.mp h])
  · exact Or.inr (by linarith [sub_eq_zero.mp h])

/-- The strict form: off the two rays at even one slot, the floor is strict. -/
theorem sum_sq_lt_of_orthogonal_of_sandwich_of_off_rays (x y : Fin n → ℝ)
    (bigM smallM : ℝ)
    (horthogonal : ∑ i, x i * y i = 0)
    (hsandwich : ∀ i, 0 ≤ (bigM * x i - y i) * (y i - smallM * x i))
    (witness : Fin n) (hwitness : y witness ≠ bigM * x witness)
    (hwitness' : y witness ≠ smallM * x witness) :
    ∑ i, y i ^ 2 < -(bigM * smallM) * ∑ i, x i ^ 2 := by
  rcases lt_or_eq_of_le
      (sum_sq_le_of_orthogonal_of_sandwich x y bigM smallM horthogonal hsandwich) with h | h
  · exact h
  · exact absurd
      (two_valued_of_orthogonal_of_sandwich_eq x y bigM smallM horthogonal hsandwich h witness)
      (by push Not; exact ⟨hwitness, hwitness'⟩)

/-! ## 4. Polarized Parseval, the input the one-line stratum actually hands over -/

/-- The cross reading of one atom matrix.  The corpus carries only the diagonal
form `Gtz.dotProduct_atomMatrix_mulVec`. -/
theorem dotProduct_atomMatrix_mulVec_cross {rank : ℕ} (atomVec first second : Fin rank → ℝ) :
    first ⬝ᵥ (atomMatrix atomVec *ᵥ second)
      = (atomVec ⬝ᵥ first) * (atomVec ⬝ᵥ second) := by
  simp only [atomMatrix, Matrix.vecMulVec, Matrix.mulVec, dotProduct, Matrix.of_apply,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun leftCoord _ =>
    Finset.sum_congr rfl fun rightCoord _ => by ring

/-- **PARSEVAL, POLARIZED.**  The corpus carries the diagonal reading
`Gtz.dotProduct_self_eq_sum_weight_mul_sq`.  The design identity is bilinear, so
the cross reading holds too, and it is what an orthogonality argument needs. -/
theorem dotProduct_eq_sum_weight_mul_dotProduct {size rank : ℕ}
    (design : WeightedDesign size rank) (first second : Fin rank → ℝ) :
    first ⬝ᵥ second
      = ∑ atomLabel, design.weight atomLabel
          * (design.atom atomLabel ⬝ᵥ first) * (design.atom atomLabel ⬝ᵥ second) := by
  have hidentity : first ⬝ᵥ ((1 : Matrix (Fin rank) (Fin rank) ℝ) *ᵥ second)
      = first ⬝ᵥ second := by rw [Matrix.one_mulVec]
  rw [← hidentity, ← design.isParseval, Matrix.sum_mulVec, dotProduct_sum]
  refine Finset.sum_congr rfl fun atomLabel _ => ?_
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
    dotProduct_atomMatrix_mulVec_cross, mul_assoc]

/-! ## 5. The one-line normal, and the orthogonality it hands the floor -/

/-- **THE FREE ATOMS CARRY THE WHOLE ORTHOGONALITY.**  At a line pattern with
normal `n` and an in-plane probe `p`, the weighted cross sum over the free atoms
vanishes, because the total is `p ⬝ᵥ n` and the line atoms read zero against `n`.
No heaviness, no weight hypothesis, and the line triple is arbitrary. -/
theorem oneLineNormal_orthogonality {size : ℕ} (design : WeightedDesign size 3)
    (lineTriple : Finset (Fin size)) (normalVec probeVec : Fin 3 → ℝ)
    (horthogonal : ∀ lineLabel ∈ lineTriple, design.atom lineLabel ⬝ᵥ normalVec = 0)
    (hprobe : probeVec ⬝ᵥ normalVec = 0) :
    ∑ freeLabel ∈ lineTripleᶜ,
        design.weight freeLabel * (design.atom freeLabel ⬝ᵥ probeVec)
          * (design.atom freeLabel ⬝ᵥ normalVec) = 0 := by
  have hpolar := dotProduct_eq_sum_weight_mul_dotProduct design probeVec normalVec
  have hlineVanishes : ∑ lineLabel ∈ lineTriple,
      design.weight lineLabel * (design.atom lineLabel ⬝ᵥ probeVec)
        * (design.atom lineLabel ⬝ᵥ normalVec) = 0 :=
    Finset.sum_eq_zero fun lineLabel hmem => by
      rw [horthogonal lineLabel hmem]; ring
  rw [← Finset.sum_add_sum_compl lineTriple
      (fun atomLabel => design.weight atomLabel * (design.atom atomLabel ⬝ᵥ probeVec)
        * (design.atom atomLabel ⬝ᵥ normalVec)), hlineVanishes, zero_add] at hpolar
  rw [← hpolar, hprobe]

/-- The two families the floor consumes at a line pattern.  The `x` slot is the
weighted normal shadow and the `y` slot the weighted in-plane shadow, both
scaled by the square root of the weight so that the products are exactly the
weighted sums. -/
noncomputable def normalShadow {size : ℕ} (design : WeightedDesign size 3)
    (normalVec : Fin 3 → ℝ) (atomLabel : Fin size) : ℝ :=
  Real.sqrt (design.weight atomLabel) * (design.atom atomLabel ⬝ᵥ normalVec)

theorem normalShadow_mul {size : ℕ} (design : WeightedDesign size 3)
    (normalVec probeVec : Fin 3 → ℝ) (atomLabel : Fin size) :
    normalShadow design probeVec atomLabel * normalShadow design normalVec atomLabel
      = design.weight atomLabel * (design.atom atomLabel ⬝ᵥ probeVec)
        * (design.atom atomLabel ⬝ᵥ normalVec) := by
  unfold normalShadow
  rw [show Real.sqrt (design.weight atomLabel) * (design.atom atomLabel ⬝ᵥ probeVec)
        * (Real.sqrt (design.weight atomLabel) * (design.atom atomLabel ⬝ᵥ normalVec))
      = (Real.sqrt (design.weight atomLabel) * Real.sqrt (design.weight atomLabel))
        * ((design.atom atomLabel ⬝ᵥ probeVec) * (design.atom atomLabel ⬝ᵥ normalVec)) from
      by ring, Real.mul_self_sqrt (design.weight_pos atomLabel).le]
  ring

theorem normalShadow_sq {size : ℕ} (design : WeightedDesign size 3)
    (normalVec : Fin 3 → ℝ) (atomLabel : Fin size) :
    normalShadow design normalVec atomLabel ^ 2
      = design.weight atomLabel * (design.atom atomLabel ⬝ᵥ normalVec) ^ 2 := by
  unfold normalShadow
  rw [mul_pow, Real.sq_sqrt (design.weight_pos atomLabel).le]

/-! ## 6. The two hypotheses of the floor, delivered by the line pattern -/

/-- The free atoms carry unit normal energy in the shadow coordinates.  The
landed `Gtz.normalParseval_on_complement` is the `size = 6` case of the sum law
underneath this, in the unscaled coordinates. -/
theorem oneLine_freeShadow_energy {size : ℕ} (design : WeightedDesign size 3)
    (lineTriple : Finset (Fin size)) (normalVec : Fin 3 → ℝ)
    (hunit : normalVec ⬝ᵥ normalVec = 1)
    (horthogonal : ∀ lineLabel ∈ lineTriple, design.atom lineLabel ⬝ᵥ normalVec = 0) :
    ∑ freeLabel ∈ lineTripleᶜ, normalShadow design normalVec freeLabel ^ 2 = 1 := by
  classical
  have htotal := dotProduct_self_eq_sum_weight_mul_sq design normalVec
  have hsplit := Finset.sum_add_sum_compl lineTriple
    (fun atomLabel => design.weight atomLabel * (design.atom atomLabel ⬝ᵥ normalVec) ^ 2)
  have hlineVanishes : ∑ lineLabel ∈ lineTriple,
      design.weight lineLabel * (design.atom lineLabel ⬝ᵥ normalVec) ^ 2 = 0 :=
    Finset.sum_eq_zero fun lineLabel hmem => by rw [horthogonal lineLabel hmem]; ring
  have hshadow : ∑ freeLabel ∈ lineTripleᶜ, normalShadow design normalVec freeLabel ^ 2
      = ∑ freeLabel ∈ lineTripleᶜ,
          design.weight freeLabel * (design.atom freeLabel ⬝ᵥ normalVec) ^ 2 :=
    Finset.sum_congr rfl fun freeLabel _ => normalShadow_sq design normalVec freeLabel
  rw [hshadow]
  rw [hunit] at htotal
  linarith [htotal, hsplit, hlineVanishes]

/-- The free atoms carry an exact orthogonality in the shadow coordinates. -/
theorem oneLine_freeShadow_orthogonal {size : ℕ} (design : WeightedDesign size 3)
    (lineTriple : Finset (Fin size)) (normalVec probeVec : Fin 3 → ℝ)
    (horthogonal : ∀ lineLabel ∈ lineTriple, design.atom lineLabel ⬝ᵥ normalVec = 0)
    (hprobe : probeVec ⬝ᵥ normalVec = 0) :
    ∑ freeLabel ∈ lineTripleᶜ,
        normalShadow design normalVec freeLabel * normalShadow design probeVec freeLabel = 0 := by
  rw [← oneLineNormal_orthogonality design lineTriple normalVec probeVec horthogonal hprobe]
  exact Finset.sum_congr rfl fun freeLabel _ => by
    rw [mul_comm (normalShadow design normalVec freeLabel),
      normalShadow_mul design normalVec probeVec freeLabel]

/-- **THE LINE ATOMS PAY FOR THE RAY PRODUCT.**  At a line pattern with unit
normal, a half-plane sandwich on the free shadows forces the LINE atoms to carry
in-plane energy at least the probe energy plus the ray product.  So a negative
ray product is exactly a budget the three line atoms must cover, and the only way
to make that budget cheap is to starve the line weight — which is what the landed
`Gtz.margin_cap_and_its_floor` says from the other side.

No heaviness, no weak dominator, no blind spot, and the line triple is arbitrary. -/
theorem oneLine_lineEnergy_ge_of_sandwich {size : ℕ} (design : WeightedDesign size 3)
    (lineTriple : Finset (Fin size)) (normalVec probeVec : Fin 3 → ℝ)
    (bigM smallM : ℝ)
    (hunit : normalVec ⬝ᵥ normalVec = 1)
    (horthogonal : ∀ lineLabel ∈ lineTriple, design.atom lineLabel ⬝ᵥ normalVec = 0)
    (hprobe : probeVec ⬝ᵥ normalVec = 0)
    (hsandwich : ∀ freeLabel ∈ lineTripleᶜ,
      0 ≤ (bigM * normalShadow design normalVec freeLabel
            - normalShadow design probeVec freeLabel)
        * (normalShadow design probeVec freeLabel
            - smallM * normalShadow design normalVec freeLabel)) :
    probeVec ⬝ᵥ probeVec + bigM * smallM
      ≤ ∑ lineLabel ∈ lineTriple,
          design.weight lineLabel * (design.atom lineLabel ⬝ᵥ probeVec) ^ 2 := by
  classical
  have hnonneg : 0 ≤ ∑ freeLabel ∈ lineTripleᶜ,
      (bigM * normalShadow design normalVec freeLabel
          - normalShadow design probeVec freeLabel)
        * (normalShadow design probeVec freeLabel
            - smallM * normalShadow design normalVec freeLabel) :=
    Finset.sum_nonneg hsandwich
  have htelescope : ∑ freeLabel ∈ lineTripleᶜ,
      (bigM * normalShadow design normalVec freeLabel
          - normalShadow design probeVec freeLabel)
        * (normalShadow design probeVec freeLabel
            - smallM * normalShadow design normalVec freeLabel)
      = (bigM + smallM)
          * (∑ freeLabel ∈ lineTripleᶜ,
              normalShadow design normalVec freeLabel
                * normalShadow design probeVec freeLabel)
        - (∑ freeLabel ∈ lineTripleᶜ, normalShadow design probeVec freeLabel ^ 2)
        - bigM * smallM
          * (∑ freeLabel ∈ lineTripleᶜ, normalShadow design normalVec freeLabel ^ 2) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun freeLabel _ => by ring
  rw [htelescope,
    oneLine_freeShadow_orthogonal design lineTriple normalVec probeVec horthogonal hprobe,
    oneLine_freeShadow_energy design lineTriple normalVec hunit horthogonal] at hnonneg
  have hfreeEnergy : ∑ freeLabel ∈ lineTripleᶜ, normalShadow design probeVec freeLabel ^ 2
      = probeVec ⬝ᵥ probeVec
        - ∑ lineLabel ∈ lineTriple,
            design.weight lineLabel * (design.atom lineLabel ⬝ᵥ probeVec) ^ 2 := by
    have htotal := dotProduct_self_eq_sum_weight_mul_sq design probeVec
    have hsplit := Finset.sum_add_sum_compl lineTriple
      (fun atomLabel => design.weight atomLabel * (design.atom atomLabel ⬝ᵥ probeVec) ^ 2)
    have hshadow : ∑ freeLabel ∈ lineTripleᶜ, normalShadow design probeVec freeLabel ^ 2
        = ∑ freeLabel ∈ lineTripleᶜ,
            design.weight freeLabel * (design.atom freeLabel ⬝ᵥ probeVec) ^ 2 :=
      Finset.sum_congr rfl fun freeLabel _ => normalShadow_sq design probeVec freeLabel
    rw [hshadow]
    linarith [htotal, hsplit]
  rw [hfreeEnergy] at hnonneg
  linarith

end Gtz
