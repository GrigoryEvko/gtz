import Gtz.Wave.WeightGapDeterminant

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

/-!
# The anchor transport: the whole cell-H tie condition at one matrix

The erase-`x` anchor of a `Z1` corner is one rank-one update of the surviving
four-set: `B = S_{univ∖x} − 1 = A_y + g_zg_zᵀ`.  The landed pair system says
the tie IS the pair disjunctions at `B`
(`Gtz.corner_oneAxisZero_isTie_iff_pairSystem`), and the landed two-sided
Sherman–Morrison update (`Gtz.update_cross_reading`) moves every `B⁻¹`
reading into `A_y⁻¹` coordinates.  This module composes the two: on the
heavy-inside cell the ENTIRE tie condition becomes one explicit polynomial
clause system in the `A_y⁻¹`-Gram of the six atoms — the same unification
that the seesaw exchange gave the both-light cell.

## The anchor split

`{z} ∪ ({y} ∪ Cᶜ) = univ ∖ {x}`, so the anchor gap is the four-set gap plus
the `z` atom (`Gtz.corner_anchor_eq_fourSet_add_atom`):

  `S_{univ∖x} − 1 = (S_{{y}∪Cᶜ} − 1) + g_zg_zᵀ` .

## The reading transport

For `A_y ≻ 0` every anchor reading clears through the positive factor
`1 + r_z` (`Gtz.corner_anchor_reading_transport`):

  `(1 + r_z) · g_aᵀB⁻¹g_b = (1 + r_z)·c_ab − c_az·c_bz` ,

with `r_z = g_zᵀA_y⁻¹g_z`, `c_ab = g_aᵀA_y⁻¹g_b`, `c_az = g_aᵀA_y⁻¹g_z`.  The
two branch shapes of the pair system transport losslessly
(`Gtz.corner_anchor_heavy_branch_iff`, `Gtz.corner_anchor_minor_branch_iff`).

## The transported pair system

On the heavy-inside cell the tie condition becomes
(`Gtz.corner_oneAxisZero_heavyInside_isTie_iff_transportedPairs`): for every
pair `a ≠ b` of the five-set,

  `c_az² ≤ (1 + r_z)(r_a − 1)`      (the heavy branch at `a`), or
  `((1+r_z)(1−r_a) + c_az²)·((1+r_z)(1−r_b) + c_bz²)
      ≤ ((1+r_z)·c_ab − c_az·c_bz)²`   (the minor branch),

with every symbol an `A_y⁻¹` reading — a lossless re-expression of `IsTie`
as one polynomial system at one positive matrix.  The per-pair branch
patterns of this system are exactly the information that every aggregate
clause discards, and the measured survivor investigation reads them.

## The inverse moment identity

The two reading rails of the campaign are one matrix equation
(`Gtz.fourSet_inverse_moment_identity`): for any subset `F` with invertible
gap `A = S_F − 1`,

  `Σ_{a∈F} A⁻¹G_a − Σ_c t_c · A⁻¹G_c = 1` .

Its trace is the reading total against the Parseval trace; any probe pair
reads a moment relation of the whitened frame out of it.
-/

namespace Gtz

open Matrix Finset

variable {m : ℕ}

/-! ## 1. The anchor split -/

/-- The five-set of the erased atom is the surviving four-set plus `z`. -/
theorem corner_anchor_insert_eq {x y z : Fin 6}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    insert z (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
      = (univ : Finset (Fin 6)).erase x := by
  ext a
  simp only [Finset.mem_insert, Finset.mem_compl, Finset.mem_erase,
    Finset.mem_univ, and_true, Finset.mem_singleton, not_or]
  constructor
  · rintro (rfl | rfl | ⟨h1, h2, h3⟩)
    · exact Ne.symm hxz
    · exact Ne.symm hxy
    · exact h1
  · intro hax
    by_cases haz : a = z
    · exact Or.inl haz
    by_cases hay : a = y
    · exact Or.inr (Or.inl hay)
    · exact Or.inr (Or.inr ⟨hax, hay, haz⟩)

/-- **THE ANCHOR SPLIT.**  The erase-`x` anchor gap is the surviving four-set
gap plus the `z` atom: `B = A_y + g_zg_zᵀ`.  Every matrix of the heavy-inside
cell is a rank-one or rank-two update of `A_y`. -/
theorem corner_anchor_eq_fourSet_add_atom (D : WeightedDesign 6 3)
    {x y z : Fin 6} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    subsetSum D ((univ : Finset (Fin 6)).erase x) - 1
      = (subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1)
        + atomMatrix (D.atom z) := by
  have hzF : z ∉ insert y (({x, y, z} : Finset (Fin 6))ᶜ) := by
    simp [Ne.symm hyz]
  rw [← corner_anchor_insert_eq hxy hxz hyz, subsetSum, subsetSum,
    Finset.sum_insert hzF]
  abel

/-! ## 2. The reading transport -/

/-- **THE ANCHOR READING TRANSPORT.**  Every reading of the anchor inverse
clears through the positive factor `1 + r_z` into `A_y⁻¹` readings. -/
theorem corner_anchor_reading_transport (D : WeightedDesign 6 3)
    {x y z : Fin 6} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hAy : (subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).PosDef)
    (a b : Fin 6) :
    (1 + D.atom z ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
          - 1)⁻¹ *ᵥ D.atom z))
      * (D.atom a ⬝ᵥ ((subsetSum D ((univ : Finset (Fin 6)).erase x) - 1)⁻¹
          *ᵥ D.atom b))
      = (1 + D.atom z ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
            - 1)⁻¹ *ᵥ D.atom z))
        * (D.atom a ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
            - 1)⁻¹ *ᵥ D.atom b))
        - (D.atom a ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
            - 1)⁻¹ *ᵥ D.atom z))
          * (D.atom z ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
              - 1)⁻¹ *ᵥ D.atom b)) := by
  have hB := corner_anchor_eq_fourSet_add_atom D hxy hxz hyz
  have hkey := update_cross_reading hAy (D.atom z) (D.atom a) (D.atom b)
  rw [← hB] at hkey
  exact hkey

/-! ## 3. The two branch shapes transport losslessly -/

/-- **THE HEAVY BRANCH, TRANSPORTED.**  An anchor self-reading reaches one
exactly when the squared `z`-cross clears the four-set excess:

  `1 ≤ g_aᵀB⁻¹g_a  ⟺  c_az² ≤ (1 + r_z)(r_a − 1)` . -/
theorem corner_anchor_heavy_branch_iff (D : WeightedDesign 6 3)
    {x y z : Fin 6} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hAy : (subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).PosDef)
    (a : Fin 6) :
    (1 ≤ D.atom a ⬝ᵥ ((subsetSum D ((univ : Finset (Fin 6)).erase x) - 1)⁻¹
        *ᵥ D.atom a))
    ↔ (D.atom a ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
          - 1)⁻¹ *ᵥ D.atom z)) ^ 2
        ≤ (1 + D.atom z ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
              - 1)⁻¹ *ᵥ D.atom z))
          * (D.atom a ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
              - 1)⁻¹ *ᵥ D.atom a) - 1) := by
  have hrz0 : 0 ≤ D.atom z ⬝ᵥ
      ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1)⁻¹
        *ᵥ D.atom z) := by
    have h := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hAy.inv.posSemidef).2
      (D.atom z)
    rwa [star_trivial] at h
  have hpos : (0 : ℝ) < 1 + D.atom z ⬝ᵥ
      ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1)⁻¹
        *ᵥ D.atom z) := by linarith
  have ht := corner_anchor_reading_transport D hxy hxz hyz hAy a a
  have hsym : D.atom z ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
        - 1)⁻¹ *ᵥ D.atom a)
      = D.atom a ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
          - 1)⁻¹ *ᵥ D.atom z) := inv_reading_symm hAy (D.atom z) (D.atom a)
  rw [hsym] at ht
  -- the exact excess identity that carries both directions
  have hexc : (1 + D.atom z ⬝ᵥ
        ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1)⁻¹
          *ᵥ D.atom z))
      * (D.atom a ⬝ᵥ ((subsetSum D ((univ : Finset (Fin 6)).erase x) - 1)⁻¹
          *ᵥ D.atom a) - 1)
      = (1 + D.atom z ⬝ᵥ
          ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1)⁻¹
            *ᵥ D.atom z))
        * (D.atom a ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
            - 1)⁻¹ *ᵥ D.atom a) - 1)
        - (D.atom a ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
            - 1)⁻¹ *ᵥ D.atom z)) ^ 2 := by
    linear_combination ht
  constructor
  · intro h
    have h0 : 0 ≤ (1 + D.atom z ⬝ᵥ
        ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1)⁻¹
          *ᵥ D.atom z))
        * (D.atom a ⬝ᵥ ((subsetSum D ((univ : Finset (Fin 6)).erase x) - 1)⁻¹
            *ᵥ D.atom a) - 1) :=
      mul_nonneg hpos.le (by linarith)
    linarith [hexc, h0]
  · intro h
    have h0 : 0 ≤ (1 + D.atom z ⬝ᵥ
        ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1)⁻¹
          *ᵥ D.atom z))
        * (D.atom a ⬝ᵥ ((subsetSum D ((univ : Finset (Fin 6)).erase x) - 1)⁻¹
            *ᵥ D.atom a) - 1) := by
      linarith [hexc]
    have hstep := (mul_nonneg_iff_of_pos_left hpos).mp h0
    linarith

/-- **THE MINOR BRANCH, TRANSPORTED.**  The pair minor of the anchor clears
through the square of the positive factor:

  `(1 − r_a(B))(1 − r_b(B)) ≤ ρ_ab(B)²
     ⟺ ((1+r_z)(1−r_a) + c_az²)·((1+r_z)(1−r_b) + c_bz²)
         ≤ ((1+r_z)c_ab − c_az·c_bz)²` . -/
theorem corner_anchor_minor_branch_iff (D : WeightedDesign 6 3)
    {x y z : Fin 6} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hAy : (subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).PosDef)
    (a b : Fin 6) :
    ((1 - D.atom a ⬝ᵥ ((subsetSum D ((univ : Finset (Fin 6)).erase x) - 1)⁻¹
          *ᵥ D.atom a))
        * (1 - D.atom b ⬝ᵥ ((subsetSum D ((univ : Finset (Fin 6)).erase x) - 1)⁻¹
            *ᵥ D.atom b))
      ≤ (D.atom a ⬝ᵥ ((subsetSum D ((univ : Finset (Fin 6)).erase x) - 1)⁻¹
          *ᵥ D.atom b)) ^ 2)
    ↔ ((1 + D.atom z ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
            - 1)⁻¹ *ᵥ D.atom z))
        * (1 - D.atom a ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
            - 1)⁻¹ *ᵥ D.atom a))
        + (D.atom a ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
            - 1)⁻¹ *ᵥ D.atom z)) ^ 2)
      * ((1 + D.atom z ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
              - 1)⁻¹ *ᵥ D.atom z))
          * (1 - D.atom b ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
              - 1)⁻¹ *ᵥ D.atom b))
          + (D.atom b ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
              - 1)⁻¹ *ᵥ D.atom z)) ^ 2)
      ≤ ((1 + D.atom z ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
              - 1)⁻¹ *ᵥ D.atom z))
          * (D.atom a ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
              - 1)⁻¹ *ᵥ D.atom b))
          - (D.atom a ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
              - 1)⁻¹ *ᵥ D.atom z))
            * (D.atom b ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
                - 1)⁻¹ *ᵥ D.atom z))) ^ 2 := by
  have hrz0 : 0 ≤ D.atom z ⬝ᵥ
      ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1)⁻¹
        *ᵥ D.atom z) := by
    have h := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hAy.inv.posSemidef).2
      (D.atom z)
    rwa [star_trivial] at h
  have hpos : (0 : ℝ) < 1 + D.atom z ⬝ᵥ
      ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1)⁻¹
        *ᵥ D.atom z) := by linarith
  have hta := corner_anchor_reading_transport D hxy hxz hyz hAy a a
  have htb := corner_anchor_reading_transport D hxy hxz hyz hAy b b
  have htab := corner_anchor_reading_transport D hxy hxz hyz hAy a b
  have hsa : D.atom z ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
        - 1)⁻¹ *ᵥ D.atom a)
      = D.atom a ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
          - 1)⁻¹ *ᵥ D.atom z) := inv_reading_symm hAy (D.atom z) (D.atom a)
  have hsb : D.atom z ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
        - 1)⁻¹ *ᵥ D.atom b)
      = D.atom b ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
          - 1)⁻¹ *ᵥ D.atom z) := inv_reading_symm hAy (D.atom z) (D.atom b)
  rw [hsa] at hta
  rw [hsb] at htb
  rw [hsb] at htab
  -- the two exact product identities that carry the equivalence
  have hprod : ((1 + D.atom z ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
            - 1)⁻¹ *ᵥ D.atom z))
        * (1 - D.atom a ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
            - 1)⁻¹ *ᵥ D.atom a))
        + (D.atom a ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
            - 1)⁻¹ *ᵥ D.atom z)) ^ 2)
      * ((1 + D.atom z ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
              - 1)⁻¹ *ᵥ D.atom z))
          * (1 - D.atom b ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
              - 1)⁻¹ *ᵥ D.atom b))
          + (D.atom b ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
              - 1)⁻¹ *ᵥ D.atom z)) ^ 2)
      = (1 + D.atom z ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
            - 1)⁻¹ *ᵥ D.atom z)) ^ 2
        * ((1 - D.atom a ⬝ᵥ ((subsetSum D ((univ : Finset (Fin 6)).erase x) - 1)⁻¹
              *ᵥ D.atom a))
          * (1 - D.atom b ⬝ᵥ ((subsetSum D ((univ : Finset (Fin 6)).erase x) - 1)⁻¹
              *ᵥ D.atom b))) := by
    linear_combination ((1 + D.atom z ⬝ᵥ
          ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1)⁻¹
            *ᵥ D.atom z))
        * (1 - D.atom b ⬝ᵥ ((subsetSum D ((univ : Finset (Fin 6)).erase x) - 1)⁻¹
            *ᵥ D.atom b))) * hta
      + ((1 + D.atom z ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
              - 1)⁻¹ *ᵥ D.atom z))
          * (1 - D.atom a ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
              - 1)⁻¹ *ᵥ D.atom a))
          + (D.atom a ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
              - 1)⁻¹ *ᵥ D.atom z)) ^ 2) * htb
  have hsq : ((1 + D.atom z ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
            - 1)⁻¹ *ᵥ D.atom z))
        * (D.atom a ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
            - 1)⁻¹ *ᵥ D.atom b))
        - (D.atom a ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
            - 1)⁻¹ *ᵥ D.atom z))
          * (D.atom b ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
              - 1)⁻¹ *ᵥ D.atom z))) ^ 2
      = (1 + D.atom z ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
            - 1)⁻¹ *ᵥ D.atom z)) ^ 2
        * ((D.atom a ⬝ᵥ ((subsetSum D ((univ : Finset (Fin 6)).erase x) - 1)⁻¹
            *ᵥ D.atom b)) ^ 2) := by
    linear_combination (-((1 + D.atom z ⬝ᵥ
          ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1)⁻¹
            *ᵥ D.atom z))
          * (D.atom a ⬝ᵥ ((subsetSum D ((univ : Finset (Fin 6)).erase x) - 1)⁻¹
              *ᵥ D.atom b))
        + ((1 + D.atom z ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
              - 1)⁻¹ *ᵥ D.atom z))
            * (D.atom a ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
                - 1)⁻¹ *ᵥ D.atom b))
          - (D.atom a ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
              - 1)⁻¹ *ᵥ D.atom z))
            * (D.atom b ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
                - 1)⁻¹ *ᵥ D.atom z))))) * htab
  have hsqpos : (0 : ℝ) < (1 + D.atom z ⬝ᵥ
      ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1)⁻¹
        *ᵥ D.atom z)) ^ 2 := by positivity
  constructor
  · intro h
    rw [hprod, hsq]
    exact mul_le_mul_of_nonneg_left h (le_of_lt hsqpos)
  · intro h
    rw [hprod, hsq] at h
    exact le_of_mul_le_mul_left h hsqpos

/-! ## 4. The inverse moment identity -/

/-- **THE INVERSE MOMENT IDENTITY.**  The member atoms of any invertible gap
against the Parseval family close into the identity matrix:

  `Σ_{a∈F} A⁻¹G_a − Σ_c t_c · A⁻¹G_c = 1` ,  `A = S_F − 1` .

The trace form is the reading total against the Parseval trace; any probe
pair reads a moment relation of the whitened frame out of it. -/
theorem fourSet_inverse_moment_identity (D : WeightedDesign m 3)
    (F : Finset (Fin m)) (hdet : IsUnit (subsetSum D F - 1).det) :
    (∑ a ∈ F, (subsetSum D F - 1)⁻¹ * atomMatrix (D.atom a))
        - ∑ c, D.weight c • ((subsetSum D F - 1)⁻¹ * atomMatrix (D.atom c))
      = 1 := by
  classical
  set A : Matrix (Fin 3) (Fin 3) ℝ := subsetSum D F - 1 with hA
  have hmember : ∑ a ∈ F, A⁻¹ * atomMatrix (D.atom a) = A⁻¹ * subsetSum D F := by
    rw [subsetSum, Matrix.mul_sum]
  have hparseval : ∑ c, D.weight c • (A⁻¹ * atomMatrix (D.atom c)) = A⁻¹ := by
    calc ∑ c, D.weight c • (A⁻¹ * atomMatrix (D.atom c))
        = A⁻¹ * ∑ c, D.weight c • atomMatrix (D.atom c) := by
          rw [Matrix.mul_sum]
          exact Finset.sum_congr rfl fun c _ => (Matrix.mul_smul _ _ _).symm
      _ = A⁻¹ := by rw [D.isParseval, Matrix.mul_one]
  have hSF : subsetSum D F = A + 1 := by rw [hA]; abel
  rw [hmember, hparseval, hSF, Matrix.mul_add, Matrix.mul_one,
    Matrix.nonsing_inv_mul A hdet]
  abel

/-! ## 5. The transported pair system of the heavy-inside cell -/

/-- **THE TRANSPORTED PAIR SYSTEM.**  On the heavy-inside cell the WHOLE tie
condition lives at `A_y`: the tie holds exactly when every pair `a ≠ b` of
the five-set satisfies the transported heavy branch at `a` or the
transported minor branch at `(a, b)`, with every symbol an `A_y⁻¹` reading.
Lossless — the anchor split, the reading transport and the positive factor
`1 + r_z` carry the landed pair system both ways. -/
theorem corner_oneAxisZero_heavyInside_isTie_iff_transportedPairs
    (D : WeightedDesign 6 3) {x y z : Fin 6}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {lam : ℝ} (hlam : 0 < lam) {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D ({x, y, z} : Finset (Fin 6)) - 1 = lam • atomMatrix u)
    (hax : D.atom x ⬝ᵥ u = 0) (haz : D.atom z ⬝ᵥ u ≠ 0)
    (hnotz : ¬ (subsetSum D (insert z (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).PosDef) :
    IsTie D ↔ ∀ a ∈ (univ : Finset (Fin 6)).erase x,
      ∀ b ∈ (univ : Finset (Fin 6)).erase x, a ≠ b →
      (D.atom a ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
            - 1)⁻¹ *ᵥ D.atom z)) ^ 2
        ≤ (1 + D.atom z ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
              - 1)⁻¹ *ᵥ D.atom z))
          * (D.atom a ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
              - 1)⁻¹ *ᵥ D.atom a) - 1)
      ∨ ((1 + D.atom z ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
              - 1)⁻¹ *ᵥ D.atom z))
          * (1 - D.atom a ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
              - 1)⁻¹ *ᵥ D.atom a))
          + (D.atom a ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
              - 1)⁻¹ *ᵥ D.atom z)) ^ 2)
        * ((1 + D.atom z ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
                - 1)⁻¹ *ᵥ D.atom z))
            * (1 - D.atom b ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
                - 1)⁻¹ *ᵥ D.atom b))
            + (D.atom b ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
                - 1)⁻¹ *ᵥ D.atom z)) ^ 2)
        ≤ ((1 + D.atom z ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
                - 1)⁻¹ *ᵥ D.atom z))
            * (D.atom a ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
                - 1)⁻¹ *ᵥ D.atom b))
            - (D.atom a ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
                - 1)⁻¹ *ᵥ D.atom z))
              * (D.atom b ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
                  - 1)⁻¹ *ᵥ D.atom z))) ^ 2 := by
  classical
  have hAy : (subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).PosDef :=
    (corner_oneAxisZero_fourSet_split D hxy hxz hyz hlam hunit hgap hax
      haz).resolve_left hnotz
  rw [corner_oneAxisZero_isTie_iff_pairSystem D hxy hxz hyz hlam.le hunit hgap hax]
  constructor
  · intro hpairs a ha b hb hab
    rcases hpairs a ha b hb hab with hheavy | hminor
    · exact Or.inl ((corner_anchor_heavy_branch_iff D hxy hxz hyz hAy a).mp hheavy)
    · exact Or.inr ((corner_anchor_minor_branch_iff D hxy hxz hyz hAy a b).mp hminor)
  · intro hpairs a ha b hb hab
    rcases hpairs a ha b hb hab with hheavy | hminor
    · exact Or.inl ((corner_anchor_heavy_branch_iff D hxy hxz hyz hAy a).mpr hheavy)
    · exact Or.inr ((corner_anchor_minor_branch_iff D hxy hxz hyz hAy a b).mpr hminor)

/-! ## 6. The pairs through `z` are the floors -/

/-- **THE `z`-HEAVY BRANCH IS IMPOSSIBLE.**  The anchor self-reading of the
added atom never reaches one: `r_z(B) = r_z/(1 + r_z) < 1`.  In transported
form the branch demands `r_z² ≤ r_z² − 1`. -/
theorem corner_anchor_zHeavy_false (D : WeightedDesign 6 3)
    {x y z : Fin 6} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hAy : (subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).PosDef) :
    ¬ (1 ≤ D.atom z ⬝ᵥ ((subsetSum D ((univ : Finset (Fin 6)).erase x) - 1)⁻¹
        *ᵥ D.atom z)) := by
  rw [corner_anchor_heavy_branch_iff D hxy hxz hyz hAy z]
  intro hcon
  nlinarith [hcon, sq_nonneg (D.atom z ⬝ᵥ
    ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1)⁻¹
      *ᵥ D.atom z))]

/-- **THE `z`-PAIR COLLAPSE.**  An anchor pair clause through the added atom
is EXACTLY the four-set floor of the other member:

  `1 ≤ r_z(B)  ∨  (1 − r_z(B))(1 − r_b(B)) ≤ ρ_zb(B)²   ⟺   1 ≤ r_b(A_y)` .

The transported `z`-factor is one — `(1+r_z)(1−r_z) + r_z² = 1` — and the
transported cross square collapses to `c_bz²`, so the minor branch IS the
floor.  This is the measured survivor diagnosis of the campaign, exact: at
every stored survivor the ONLY failing anchor pairs are the pairs through
`z`, because those pairs are the raw floors and nothing else is. -/
theorem corner_anchor_zPair_iff_floor (D : WeightedDesign 6 3)
    {x y z : Fin 6} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hAy : (subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).PosDef)
    (b : Fin 6) :
    ((1 ≤ D.atom z ⬝ᵥ ((subsetSum D ((univ : Finset (Fin 6)).erase x) - 1)⁻¹
        *ᵥ D.atom z))
      ∨ (1 - D.atom z ⬝ᵥ ((subsetSum D ((univ : Finset (Fin 6)).erase x) - 1)⁻¹
            *ᵥ D.atom z))
        * (1 - D.atom b ⬝ᵥ ((subsetSum D ((univ : Finset (Fin 6)).erase x) - 1)⁻¹
            *ᵥ D.atom b))
        ≤ (D.atom z ⬝ᵥ ((subsetSum D ((univ : Finset (Fin 6)).erase x) - 1)⁻¹
            *ᵥ D.atom b)) ^ 2)
    ↔ 1 ≤ D.atom b ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
        - 1)⁻¹ *ᵥ D.atom b) := by
  have hrz0 : 0 ≤ D.atom z ⬝ᵥ
      ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1)⁻¹
        *ᵥ D.atom z) := by
    have h := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hAy.inv.posSemidef).2
      (D.atom z)
    rwa [star_trivial] at h
  have hpos : (0 : ℝ) < 1 + D.atom z ⬝ᵥ
      ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1)⁻¹
        *ᵥ D.atom z) := by linarith
  constructor
  · rintro (hheavy | hminor)
    · exact absurd hheavy (corner_anchor_zHeavy_false D hxy hxz hyz hAy)
    · have hm := (corner_anchor_minor_branch_iff D hxy hxz hyz hAy z b).mp hminor
      have hzz : D.atom z ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
            - 1)⁻¹ *ᵥ D.atom b)
          = D.atom b ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
              - 1)⁻¹ *ᵥ D.atom z) := inv_reading_symm hAy (D.atom z) (D.atom b)
      rw [hzz] at hm
      -- the z-factor is one and the cross square collapses: the floor remains
      nlinarith [hm, hpos, sq_nonneg (D.atom b ⬝ᵥ
        ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1)⁻¹
          *ᵥ D.atom z))]
  · intro hfloor
    refine Or.inr ((corner_anchor_minor_branch_iff D hxy hxz hyz hAy z b).mpr ?_)
    have hzz : D.atom z ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
          - 1)⁻¹ *ᵥ D.atom b)
        = D.atom b ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
            - 1)⁻¹ *ᵥ D.atom z) := inv_reading_symm hAy (D.atom z) (D.atom b)
    rw [hzz]
    nlinarith [hfloor, hpos, sq_nonneg (D.atom b ⬝ᵥ
      ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1)⁻¹
        *ᵥ D.atom z))]

end Gtz
