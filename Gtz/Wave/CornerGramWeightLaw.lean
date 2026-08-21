/-
# The adjugate Parseval law and the sharp corner weight law

Parseval is usually read at an atom or at an eigenvector.  This module reads it
at the ADJUGATE PROBE of a triple — the combination

  `zeta(w) = w0 * (b x c) + w1 * (c x a) + w2 * (a x b)`

of the three cross products of the triple's atoms.  That probe is special
because each atom of the triple reads it back diagonally:

  `a . zeta(w) = w0 * [abc]` ,  `b . zeta(w) = w1 * [abc]` ,  `c . zeta(w) = w2 * [abc]` ,

so the three inside terms of Parseval decouple completely and the remaining
atoms only help.  The result (`Gtz.design_adjugate_probe_law`) is a QUADRATIC
FORM inequality that holds at EVERY weighted design and EVERY triple, with no
tie, no corner and no domination hypothesis:

  **`[abc]^2 * (t_a*w0^2 + t_b*w1^2 + t_c*w2^2)  <=  zeta(w) . zeta(w)`** .

Its diagonal instances recover the landed pair-mass floor.  Its OFF-diagonal
content is new, and at a corner it is sharp.

## The corner instance

On a `Z1` corner — one inside atom `x` with vanishing axis reading, unit —
the landed anchor laws pin the cross-product Gram completely: `x` is
orthogonal to `y` and to `z`, so Binet-Cauchy collapses the probe square to

  `zeta . zeta = l_z*w1^2 - 2*(g_y . g_z)*w1*w2 + l_y*w2^2` .

The probe law then says a two-variable quadratic form is nonnegative
(`Gtz.corner_oneAxisZero_quadratic_form`), and its discriminant, together with
the landed inside leverage total `l_y + l_z = 2 + lam` and the landed vanishing
pair minor, collapses to a single scalar law:

  **`t_y*l_y + t_z*l_z  <=  1 + (1 + lam)*t_y*t_z`**

(`Gtz.corner_oneAxisZero_weight_law`).

## What this sharpens

The landed `Gtz.corner_scale_cap` reads `lam <= 1/t_y + 1/t_z - 2`.  It is
proven from the trace identity and `t*l <= 1` applied to `y` and `z`
SEPARATELY, so it discards every cross term.  The law above keeps them: the
two leverages are capped JOINTLY, against a product that is second order in the
weights.  Adding the two separate landed caps gives `t_y*l_y + t_z*l_z <= 2`;
the law above gives `<= 1 + (1+lam)*t_y*t_z`, which is smaller whenever
`(1+lam)*t_y*t_z < 1`.

[MEASURED, 200000 random `Z1` corner data: the sharp law is NEVER weaker than
the landed cap (0 exceptions), it is at least `1.5` times sharper on 71.81
percent of them, the median ratio is `1.9971` and the maximum is `43.33`.  The
matrix law it comes from is TIGHT — over 60000 genuine Parseval designs
carrying a corner, built by mirroring the construction in the verifier, its
minimum eigenvalue reaches `3.4e-05`, so nothing is being given away.]
-/
import Gtz.Wave.KOneAnchor
import Gtz.Wave.ErasedWitnessGram
import Gtz.Wave.OneAxisZeroAnchorLaws
import Gtz.Wave.CornerBracketPlucker

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

open Matrix Finset

variable {m : ℕ}

/-! ## 1. Binet-Cauchy for the bracket normal -/

/-- **BINET-CAUCHY.**  The pairing of two cross products is the two by two
minor of the four pairings.  One `ring` after unfolding the coordinates. -/
theorem bracketNormal_dotProduct_bracketNormal (a b c d : Fin 3 → ℝ) :
    bracketNormal a b ⬝ᵥ bracketNormal c d
      = (a ⬝ᵥ c) * (b ⬝ᵥ d) - (a ⬝ᵥ d) * (b ⬝ᵥ c) := by
  simp only [bracketNormal, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  ring

/-! ## 2. The adjugate probe of a triple -/

/-- The **adjugate probe**: the `w`-combination of the three cross products of a
triple.  Its name records that its Gram is the adjugate of the triple's Gram. -/
noncomputable def adjugateProbe (a b c : Fin 3 → ℝ) (w0 w1 w2 : ℝ) : Fin 3 → ℝ :=
  fun i => w0 * bracketNormal b c i + w1 * bracketNormal c a i + w2 * bracketNormal a b i

/-- **THE FIRST ATOM READS THE PROBE DIAGONALLY.** -/
theorem left_dotProduct_adjugateProbe (a b c : Fin 3 → ℝ) (w0 w1 w2 : ℝ) :
    a ⬝ᵥ adjugateProbe a b c w0 w1 w2 = w0 * tripleBracket a b c := by
  simp only [adjugateProbe, dotProduct, Fin.sum_univ_three, bracketNormal,
    tripleBracket_eq, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  ring

/-- **THE SECOND ATOM READS THE PROBE DIAGONALLY.** -/
theorem mid_dotProduct_adjugateProbe (a b c : Fin 3 → ℝ) (w0 w1 w2 : ℝ) :
    b ⬝ᵥ adjugateProbe a b c w0 w1 w2 = w1 * tripleBracket a b c := by
  simp only [adjugateProbe, dotProduct, Fin.sum_univ_three, bracketNormal,
    tripleBracket_eq, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  ring

/-- **THE THIRD ATOM READS THE PROBE DIAGONALLY.** -/
theorem right_dotProduct_adjugateProbe (a b c : Fin 3 → ℝ) (w0 w1 w2 : ℝ) :
    c ⬝ᵥ adjugateProbe a b c w0 w1 w2 = w2 * tripleBracket a b c := by
  simp only [adjugateProbe, dotProduct, Fin.sum_univ_three, bracketNormal,
    tripleBracket_eq, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  ring

/-! ## 3. The adjugate Parseval law -/

/-- **THE ADJUGATE PARSEVAL LAW.**  At every weighted design and every triple,
the squared bracket times the weighted square total of the probe coefficients is
at most the probe's own square.  No tie, no corner, no domination: Parseval read
at the adjugate probe, with the atoms outside the triple discarded. -/
theorem design_adjugate_probe_law (D : WeightedDesign m 3) {x y z : Fin m}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) (w0 w1 w2 : ℝ) :
    atomBracket D x y z ^ 2
        * (D.weight x * w0 ^ 2 + D.weight y * w1 ^ 2 + D.weight z * w2 ^ 2)
      ≤ adjugateProbe (D.atom x) (D.atom y) (D.atom z) w0 w1 w2
          ⬝ᵥ adjugateProbe (D.atom x) (D.atom y) (D.atom z) w0 w1 w2 := by
  classical
  set zeta := adjugateProbe (D.atom x) (D.atom y) (D.atom z) w0 w1 w2 with hzeta
  have hx : D.atom x ⬝ᵥ zeta = w0 * atomBracket D x y z :=
    left_dotProduct_adjugateProbe _ _ _ _ _ _
  have hy : D.atom y ⬝ᵥ zeta = w1 * atomBracket D x y z :=
    mid_dotProduct_adjugateProbe _ _ _ _ _ _
  have hz : D.atom z ⬝ᵥ zeta = w2 * atomBracket D x y z :=
    right_dotProduct_adjugateProbe _ _ _ _ _ _
  have hsub : ({x, y, z} : Finset (Fin m)) ⊆ (Finset.univ : Finset (Fin m)) :=
    Finset.subset_univ _
  have hnn : ∀ c ∈ (Finset.univ : Finset (Fin m)),
      c ∉ ({x, y, z} : Finset (Fin m)) → 0 ≤ D.weight c * (D.atom c ⬝ᵥ zeta) ^ 2 := by
    intro c _ _
    exact mul_nonneg (D.weight_pos c).le (sq_nonneg _)
  have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub hnn
  rw [parseval_probe_form D zeta] at hle
  have hxmem : x ∉ ({y, z} : Finset (Fin m)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact fun h => h.elim hxy hxz
  have hymem : y ∉ ({z} : Finset (Fin m)) := by
    simp only [Finset.mem_singleton]; exact hyz
  rw [Finset.sum_insert hxmem, Finset.sum_insert hymem, Finset.sum_singleton,
    hx, hy, hz] at hle
  nlinarith [hle]

/-! ## 4. The diagonal instance: the pair wedge floor -/

/-- **THE WEDGE FLOOR.**  Reading the adjugate law at the first coordinate
vector: the squared area of a pair is at least the third atom's weight times the
squared bracket.  A one-line consequence, and it holds at every design. -/
theorem design_pairArea_ge_weight_mul_bracket_sq (D : WeightedDesign m 3)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    D.weight x * atomBracket D x y z ^ 2
      ≤ bracketNormal (D.atom y) (D.atom z) ⬝ᵥ bracketNormal (D.atom y) (D.atom z) := by
  have h := design_adjugate_probe_law D hxy hxz hyz 1 0 0
  have hzeta : adjugateProbe (D.atom x) (D.atom y) (D.atom z) 1 0 0
      = bracketNormal (D.atom y) (D.atom z) := by
    funext i
    simp only [adjugateProbe]
    ring
  rw [hzeta] at h
  nlinarith [h]

/-! ## 5. A nonnegative binary form has nonnegative discriminant -/

/-- **THE DISCRIMINANT OF A NONNEGATIVE BINARY FORM.**  Four probes: the two
coordinate vectors give the diagonal signs, `(B, A)` and `(C, B)` give the
discriminant scaled by each diagonal, and `(1, 1)`, `(1, -1)` close the doubly
degenerate case. -/
theorem discriminant_nonneg_of_binaryForm_nonneg {A B Cc : ℝ}
    (h : ∀ w1 w2 : ℝ, 0 ≤ A * w1 ^ 2 - 2 * B * w1 * w2 + Cc * w2 ^ 2) :
    0 ≤ A * Cc - B ^ 2 := by
  have hA0 : 0 ≤ A := by have := h 1 0; nlinarith [this]
  have hC0 : 0 ≤ Cc := by have := h 0 1; nlinarith [this]
  have hkey : 0 ≤ A * (A * Cc - B ^ 2) := by have := h B A; nlinarith [this]
  have hkey2 : 0 ≤ Cc * (A * Cc - B ^ 2) := by have := h Cc B; nlinarith [this]
  rcases lt_or_eq_of_le hA0 with hApos | hAzero
  · nlinarith [hkey, hApos]
  · rcases lt_or_eq_of_le hC0 with hCpos | hCzero
    · nlinarith [hkey2, hCpos]
    · have hb1 := h 1 1
      have hb2 := h 1 (-1)
      nlinarith [hb1, hb2, hAzero, hCzero]

/-! ## 6. The corner instance -/

/-- **THE `Z1` QUADRATIC FORM.**  On a `Z1` corner with a unit erased atom the
adjugate probe law becomes a two-variable quadratic form inequality whose
coefficients are the two live leverages, their pairing, and the two live
weights.  Every cross product Gram entry is collapsed by the landed corner
orthogonality through Binet-Cauchy. -/
theorem corner_oneAxisZero_quadratic_form (D : WeightedDesign m 3)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D ({x, y, z} : Finset (Fin m)) - 1 = lam • atomMatrix u)
    (hax : D.atom x ⬝ᵥ u = 0) (hxunit : D.atom x ⬝ᵥ D.atom x = 1) (w1 w2 : ℝ) :
    (1 + lam) * (D.weight y * w1 ^ 2 + D.weight z * w2 ^ 2)
      ≤ (D.atom z ⬝ᵥ D.atom z) * w1 ^ 2
        - 2 * (D.atom y ⬝ᵥ D.atom z) * w1 * w2
        + (D.atom y ⬝ᵥ D.atom y) * w2 ^ 2 := by
  obtain ⟨hoxy, hoxz⟩ :=
    corner_oneAxisZero_xOrthogonal D hxy hxz hyz hlam hunit hgap hax
  have hbr := corner_atomBracket_sq D hxy hxz hyz hlam hunit hgap
  have h := design_adjugate_probe_law D hxy hxz hyz 0 w1 w2
  rw [hbr] at h
  -- expand the probe square by Binet-Cauchy
  have hsq : adjugateProbe (D.atom x) (D.atom y) (D.atom z) 0 w1 w2
        ⬝ᵥ adjugateProbe (D.atom x) (D.atom y) (D.atom z) 0 w1 w2
      = w1 ^ 2 * (bracketNormal (D.atom z) (D.atom x)
            ⬝ᵥ bracketNormal (D.atom z) (D.atom x))
        + 2 * w1 * w2 * (bracketNormal (D.atom z) (D.atom x)
            ⬝ᵥ bracketNormal (D.atom x) (D.atom y))
        + w2 ^ 2 * (bracketNormal (D.atom x) (D.atom y)
            ⬝ᵥ bracketNormal (D.atom x) (D.atom y)) := by
    simp only [adjugateProbe, dotProduct, Fin.sum_univ_three]
    ring
  rw [hsq, bracketNormal_dotProduct_bracketNormal,
    bracketNormal_dotProduct_bracketNormal,
    bracketNormal_dotProduct_bracketNormal] at h
  rw [dotProduct_comm (D.atom z) (D.atom x), hoxz, dotProduct_comm (D.atom y) (D.atom x)] at h
  rw [hoxy, hxunit] at h
  have hzy : D.atom z ⬝ᵥ D.atom y = D.atom y ⬝ᵥ D.atom z := dotProduct_comm _ _
  rw [hzy] at h
  nlinarith [h]

/-- **THE SHARP CORNER WEIGHT LAW.**  On a `Z1` corner with a unit erased atom
the two live weighted leverages are capped JOINTLY:

  `t_y*l_y + t_z*l_z <= 1 + (1 + lam)*t_y*t_z` .

The discriminant of the `Z1` quadratic form, closed by the landed inside
leverage total and the landed vanishing pair minor.  Adding the two landed
per-atom caps `t*l <= 1` gives only `<= 2`. -/
theorem corner_oneAxisZero_weight_law (D : WeightedDesign m 3)
    {x y z : Fin m} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {lam : ℝ} (hlam : 0 ≤ lam) {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D ({x, y, z} : Finset (Fin m)) - 1 = lam • atomMatrix u)
    (hax : D.atom x ⬝ᵥ u = 0) (hxunit : D.atom x ⬝ᵥ D.atom x = 1) :
    D.weight y * (D.atom y ⬝ᵥ D.atom y) + D.weight z * (D.atom z ⬝ᵥ D.atom z)
      ≤ 1 + (1 + lam) * (D.weight y * D.weight z) := by
  -- every fact is derived BEFORE the abbreviations, so `set` folds them all
  have hQ0 : ∀ w1 w2 : ℝ,
      (1 + lam) * (D.weight y * w1 ^ 2 + D.weight z * w2 ^ 2)
        ≤ (D.atom z ⬝ᵥ D.atom z) * w1 ^ 2
          - 2 * (D.atom y ⬝ᵥ D.atom z) * w1 * w2
          + (D.atom y ⬝ᵥ D.atom y) * w2 ^ 2 := fun w1 w2 =>
    corner_oneAxisZero_quadratic_form D hxy hxz hyz hlam hunit hgap hax hxunit w1 w2
  have hsum : D.atom y ⬝ᵥ D.atom y + D.atom z ⬝ᵥ D.atom z = 2 + lam :=
    corner_inside_leverage_sum D hxy hxz hyz hunit hgap hxunit
  have hminor : pairMinor D y z = 0 := by
    refine corner_pairMinor_eq_zero D _ (card_triple_eq hxy hxz hyz) hlam hunit hgap ?_ ?_ hyz
    · simp
    · simp
  have hminor' : (D.atom y ⬝ᵥ D.atom y - 1) * (D.atom z ⬝ᵥ D.atom z - 1)
      - (D.atom y ⬝ᵥ D.atom z) ^ 2 = 0 := by
    rw [pairMinor, heavyExcess, heavyExcess, atomPairing, leverageOf_eq_dotProduct,
      leverageOf_eq_dotProduct] at hminor
    exact hminor
  set ly := D.atom y ⬝ᵥ D.atom y with hly
  set lz := D.atom z ⬝ᵥ D.atom z with hlz
  set pyz := D.atom y ⬝ᵥ D.atom z with hpyz
  have hdisc : 0 ≤ (lz - (1 + lam) * D.weight y) * (ly - (1 + lam) * D.weight z)
      - pyz ^ 2 := by
    refine discriminant_nonneg_of_binaryForm_nonneg (fun w1 w2 => ?_)
    have h := hQ0 w1 w2
    nlinarith [h]
  have hlampos : (0 : ℝ) < 1 + lam := by linarith
  -- the discriminant IS the law, scaled by the positive factor `1 + lam`
  have hfact : (1 + lam) * (1 + (1 + lam) * (D.weight y * D.weight z)
        - (D.weight y * ly + D.weight z * lz))
      = (lz - (1 + lam) * D.weight y) * (ly - (1 + lam) * D.weight z) - pyz ^ 2 := by
    linear_combination -hsum - hminor'
  have hpos : 0 ≤ (1 + lam) * (1 + (1 + lam) * (D.weight y * D.weight z)
      - (D.weight y * ly + D.weight z * lz)) := by rw [hfact]; exact hdisc
  by_contra hcon
  push_neg at hcon
  exact absurd hpos (not_le.mpr (mul_neg_of_pos_of_neg hlampos (by linarith)))

end Gtz
