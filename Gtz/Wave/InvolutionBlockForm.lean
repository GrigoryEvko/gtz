import Gtz.Wave.SpectralSupplyCell

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 12800000

/-!
# The involution block form of the deciding cell

The Gram of a rank-three Parseval frame of six atoms is a projection `G`, and
`H := 2 G - 1` is a symmetric involution of trace zero.  This module lands the
block laws of that involution.

## 1. The Jacobi block law, at every leverage profile

* `Gtz.atomBlockDet_complement` — **the determinant of a complementary block
  reads off the SAME block**: for every enumeration of the six slots,
  `det(Gram of slots 3,4,5) = det(1 - Gram block of slots 0,1,2)`.  The proof
  runs the Weinstein-Aronszajn identity against the frame law, with no kernel
  basis and no eigenvalue.

## 2. The balanced dictionary

At balanced leverage (`atomGram y y = 1/2` at every slot) the two determinants
of a cut are two readings of one block:

* `Gtz.atomBlockDet_balanced` — `8 p_T = 1 - Q + 2 c` with `Q` the sum of the
  three squared doubled correlations and `c` their product
* `Gtz.atomBlockDet_balanced_twin` — `8 p_(Tc) = 1 - Q - 2 c`
* `Gtz.atomBalancedCut_mass`, `Gtz.atomBalancedCut_gap` — the cut mass is
  `(1 - Q) / 4` and the cut gap is `c / 2`.

## 3. The shifted block and the triangle criterion

* `Gtz.atomShiftBlockDet` — the determinant of `G_T - (1/6) 1`, entrywise
* `Gtz.atomShiftBlockDet_balanced` — `216 det = 8 - 18 Q + 54 c` at balance
* `Gtz.atomShiftBlockDet_balanced_nonneg_iff` — the determinant arm of the
  balanced criterion is EXACTLY the triangle inequality `Q - 3 c ≤ 4/9`
* `Gtz.atomEquilateralCubic` — `3 r ^ 2 - 3 r ^ 3 ≤ 4 / 9` for `r ≥ -1/3`,
  from the factorization `27 r ^ 3 - 27 r ^ 2 + 4 = (3 r - 2) ^ 2 (3 r + 1)`:
  every equilateral triangle passes the criterion, sharp only at `r = 2/3`.

## 4. The path law and its kills

* `Gtz.atomInvolutionPath` — for every pair, the four two-step paths total
  `-(d_x + d_y) H_xy`, where `d` is the doubled leverage minus one
* `Gtz.atomBalancedPolygon` — at balance the total is zero
* `Gtz.atomBalancedPathKill` — one path product is dominated by half the
  cross weight of its endpoints: heavy twin triangles cannot carry light
  crosses.

## 5. The quartet interface

* `Gtz.atomQuartetThird` — the third symmetric function of a shifted four-set
  block, as the sum of its four erased shifted determinants
* `Gtz.exists_pos_of_quartetThird_pos` — a positive third symmetric function
  hands a positive erased determinant.

Everything below is unconditional real algebra over the frame law.
-/

namespace Gtz

open Matrix

/-- The frame law read entrywise: the atom coordinates satisfy
`∑ y, atom y i * atom y j = δ i j`. -/
theorem atomFrame_entry (atom : Fin 6 → (Fin 3 → ℝ))
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (i j : Fin 3) :
    (∑ slot, atom slot i * atom slot j) = if i = j then 1 else 0 := by
  classical
  have hpick : ∀ (v : Fin 3 → ℝ) (k : Fin 3), v ⬝ᵥ Pi.single k 1 = v k := by
    intro v k
    simp [dotProduct, Pi.single_apply]
  have hkey := hframe (Pi.single i 1) (Pi.single j 1)
  rw [hpick (Pi.single i 1) j] at hkey
  have hsingle : (Pi.single i 1 : Fin 3 → ℝ) j = if i = j then 1 else 0 := by
    rcases eq_or_ne i j with hij | hij
    · subst hij; simp
    · simp [hij]
  rw [hsingle] at hkey
  calc (∑ slot, atom slot i * atom slot j)
      = ∑ slot, (atom slot ⬝ᵥ Pi.single i 1) * (atom slot ⬝ᵥ Pi.single j 1) := by
        refine Finset.sum_congr rfl fun slot _ => ?_
        rw [hpick (atom slot) i, hpick (atom slot) j]
    _ = if i = j then 1 else 0 := hkey

/-- The row matrix of three slots: the three atoms as the three rows. -/
def atomTripleRows (atom : Fin 6 → (Fin 3 → ℝ)) (slotOne slotTwo slotThree : Fin 6) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun rowIndex colIndex => atom (![slotOne, slotTwo, slotThree] rowIndex) colIndex

theorem atomTripleRows_mul_transpose (atom : Fin 6 → (Fin 3 → ℝ))
    (slotOne slotTwo slotThree : Fin 6) (rowIndex colIndex : Fin 3) :
    (atomTripleRows atom slotOne slotTwo slotThree
        * (atomTripleRows atom slotOne slotTwo slotThree)ᵀ) rowIndex colIndex
      = atomGram atom (![slotOne, slotTwo, slotThree] rowIndex)
          (![slotOne, slotTwo, slotThree] colIndex) := by
  simp [Matrix.mul_apply, atomTripleRows, atomGram, dotProduct, Matrix.transpose_apply]

theorem atomTripleRows_transpose_mul (atom : Fin 6 → (Fin 3 → ℝ))
    (slotOne slotTwo slotThree : Fin 6) (rowIndex colIndex : Fin 3) :
    ((atomTripleRows atom slotOne slotTwo slotThree)ᵀ
        * atomTripleRows atom slotOne slotTwo slotThree) rowIndex colIndex
      = atom slotOne rowIndex * atom slotOne colIndex
        + atom slotTwo rowIndex * atom slotTwo colIndex
        + atom slotThree rowIndex * atom slotThree colIndex := by
  simp [Matrix.mul_apply, atomTripleRows, Matrix.transpose_apply, Fin.sum_univ_three]

/-- **THE JACOBI BLOCK LAW.**  For every enumeration `σ` of the six slots, the
determinant of the Gram block of the last three slots equals the determinant of
`1` minus the Gram block of the first three.  Both cut determinants read off
ONE block, at every leverage profile. -/
theorem atomBlockDet_complement (atom : Fin 6 → (Fin 3 → ℝ))
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (σ : Equiv.Perm (Fin 6)) :
    atomBlockDet atom (σ 3) (σ 4) (σ 5)
      = (1 - atomGram atom (σ 0) (σ 0)) * (1 - atomGram atom (σ 1) (σ 1))
            * (1 - atomGram atom (σ 2) (σ 2))
        - (1 - atomGram atom (σ 0) (σ 0)) * atomGram atom (σ 1) (σ 2) ^ 2
        - (1 - atomGram atom (σ 1) (σ 1)) * atomGram atom (σ 0) (σ 2) ^ 2
        - (1 - atomGram atom (σ 2) (σ 2)) * atomGram atom (σ 0) (σ 1) ^ 2
        - 2 * atomGram atom (σ 0) (σ 1) * atomGram atom (σ 0) (σ 2)
            * atomGram atom (σ 1) (σ 2) := by
  classical
  set R := atomTripleRows atom (σ 0) (σ 1) (σ 2) with hR
  set S := atomTripleRows atom (σ 3) (σ 4) (σ 5) with hS
  have hsplit : Rᵀ * R + Sᵀ * S = 1 := by
    ext rowIndex colIndex
    rw [Matrix.add_apply, hR, hS, atomTripleRows_transpose_mul,
      atomTripleRows_transpose_mul]
    have hentry := atomFrame_entry atom hframe rowIndex colIndex
    have hperm : (∑ slot, atom slot rowIndex * atom slot colIndex)
        = ∑ k, atom (σ k) rowIndex * atom (σ k) colIndex :=
      (Equiv.sum_comp σ fun slot => atom slot rowIndex * atom slot colIndex).symm
    rw [hperm, Fin.sum_univ_six] at hentry
    have hone : (1 : Matrix (Fin 3) (Fin 3) ℝ) rowIndex colIndex
        = if rowIndex = colIndex then 1 else 0 := Matrix.one_apply
    rw [hone]
    linarith
  have hcomm : (1 - R * Rᵀ).det = (1 - Rᵀ * R).det :=
    Matrix.det_one_sub_mul_comm R Rᵀ
  have hSS : (1 : Matrix (Fin 3) (Fin 3) ℝ) - Rᵀ * R = Sᵀ * S := by
    rw [← hsplit]; abel
  have hchain : (1 - R * Rᵀ).det = (S * Sᵀ).det := by
    rw [hcomm, hSS, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, mul_comm]
  have hvec0 : (![σ 3, σ 4, σ 5] : Fin 3 → Fin 6) 0 = σ 3 := rfl
  have hvec1 : (![σ 3, σ 4, σ 5] : Fin 3 → Fin 6) 1 = σ 4 := rfl
  have hvec2 : (![σ 3, σ 4, σ 5] : Fin 3 → Fin 6) 2 = σ 5 := rfl
  have hleft : (S * Sᵀ).det = atomBlockDet atom (σ 3) (σ 4) (σ 5) := by
    rw [Matrix.det_fin_three]
    rw [hS]
    simp only [atomTripleRows_mul_transpose, hvec0, hvec1, hvec2]
    rw [atomBlockDet, atomGram_comm atom (σ 4) (σ 3), atomGram_comm atom (σ 5) (σ 3),
      atomGram_comm atom (σ 5) (σ 4)]
    ring
  have hwec0 : (![σ 0, σ 1, σ 2] : Fin 3 → Fin 6) 0 = σ 0 := rfl
  have hwec1 : (![σ 0, σ 1, σ 2] : Fin 3 → Fin 6) 1 = σ 1 := rfl
  have hwec2 : (![σ 0, σ 1, σ 2] : Fin 3 → Fin 6) 2 = σ 2 := rfl
  have hright : (1 - R * Rᵀ).det
      = (1 - atomGram atom (σ 0) (σ 0)) * (1 - atomGram atom (σ 1) (σ 1))
            * (1 - atomGram atom (σ 2) (σ 2))
        - (1 - atomGram atom (σ 0) (σ 0)) * atomGram atom (σ 1) (σ 2) ^ 2
        - (1 - atomGram atom (σ 1) (σ 1)) * atomGram atom (σ 0) (σ 2) ^ 2
        - (1 - atomGram atom (σ 2) (σ 2)) * atomGram atom (σ 0) (σ 1) ^ 2
        - 2 * atomGram atom (σ 0) (σ 1) * atomGram atom (σ 0) (σ 2)
            * atomGram atom (σ 1) (σ 2) := by
    rw [Matrix.det_fin_three]
    simp only [Matrix.sub_apply, Matrix.one_apply, hR, atomTripleRows_mul_transpose,
      hwec0, hwec1, hwec2]
    norm_num [Fin.ext_iff]
    rw [atomGram_comm atom (σ 1) (σ 0), atomGram_comm atom (σ 2) (σ 0),
      atomGram_comm atom (σ 2) (σ 1)]
    ring
  rw [← hleft, ← hchain, hright]

/-- The balanced block dictionary: with every leverage one half,
`8 p_T = 1 - Q + 2 c` on the doubled correlations. -/
theorem atomBlockDet_balanced (atom : Fin 6 → (Fin 3 → ℝ))
    (hbal : ∀ y : Fin 6, atomGram atom y y = 1 / 2) (a b c : Fin 6) :
    8 * atomBlockDet atom a b c
      = 1 - ((2 * atomGram atom a b) ^ 2 + (2 * atomGram atom a c) ^ 2
            + (2 * atomGram atom b c) ^ 2)
        + 2 * ((2 * atomGram atom a b) * (2 * atomGram atom a c)
            * (2 * atomGram atom b c)) := by
  rw [atomBlockDet, hbal a, hbal b, hbal c]
  ring

/-- **THE JACOBI TWIN.**  The complementary determinant reads the SAME doubled
correlations with the cycle negated: `8 p_(Tc) = 1 - Q - 2 c`. -/
theorem atomBlockDet_balanced_twin (atom : Fin 6 → (Fin 3 → ℝ))
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (hbal : ∀ y : Fin 6, atomGram atom y y = 1 / 2) (σ : Equiv.Perm (Fin 6)) :
    8 * atomBlockDet atom (σ 3) (σ 4) (σ 5)
      = 1 - ((2 * atomGram atom (σ 0) (σ 1)) ^ 2 + (2 * atomGram atom (σ 0) (σ 2)) ^ 2
            + (2 * atomGram atom (σ 1) (σ 2)) ^ 2)
        - 2 * ((2 * atomGram atom (σ 0) (σ 1)) * (2 * atomGram atom (σ 0) (σ 2))
            * (2 * atomGram atom (σ 1) (σ 2))) := by
  rw [atomBlockDet_complement atom hframe σ, hbal (σ 0), hbal (σ 1), hbal (σ 2)]
  ring

/-- The cut mass at balance: `p_T + p_(Tc) = (1 - Q) / 4`. -/
theorem atomBalancedCut_mass (atom : Fin 6 → (Fin 3 → ℝ))
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (hbal : ∀ y : Fin 6, atomGram atom y y = 1 / 2) (σ : Equiv.Perm (Fin 6)) :
    atomBlockDet atom (σ 0) (σ 1) (σ 2) + atomBlockDet atom (σ 3) (σ 4) (σ 5)
      = (1 - ((2 * atomGram atom (σ 0) (σ 1)) ^ 2 + (2 * atomGram atom (σ 0) (σ 2)) ^ 2
            + (2 * atomGram atom (σ 1) (σ 2)) ^ 2)) / 4 := by
  have hone := atomBlockDet_balanced atom hbal (σ 0) (σ 1) (σ 2)
  have htwo := atomBlockDet_balanced_twin atom hframe hbal σ
  linarith

/-- The cut gap at balance: `p_T - p_(Tc) = c / 2` on the doubled cycle. -/
theorem atomBalancedCut_gap (atom : Fin 6 → (Fin 3 → ℝ))
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (hbal : ∀ y : Fin 6, atomGram atom y y = 1 / 2) (σ : Equiv.Perm (Fin 6)) :
    atomBlockDet atom (σ 0) (σ 1) (σ 2) - atomBlockDet atom (σ 3) (σ 4) (σ 5)
      = ((2 * atomGram atom (σ 0) (σ 1)) * (2 * atomGram atom (σ 0) (σ 2))
          * (2 * atomGram atom (σ 1) (σ 2))) / 2 := by
  have hone := atomBlockDet_balanced atom hbal (σ 0) (σ 1) (σ 2)
  have htwo := atomBlockDet_balanced_twin atom hframe hbal σ
  linarith

/-- The determinant of the shifted block `G_T - (1/6) 1`, entrywise. -/
noncomputable def atomShiftBlockDet (atom : Fin 6 → (Fin 3 → ℝ)) (a b c : Fin 6) : ℝ :=
  (atomGram atom a a - 1 / 6) * (atomGram atom b b - 1 / 6)
      * (atomGram atom c c - 1 / 6)
    + 2 * atomGram atom a b * atomGram atom a c * atomGram atom b c
    - (atomGram atom a a - 1 / 6) * atomGram atom b c ^ 2
    - (atomGram atom b b - 1 / 6) * atomGram atom a c ^ 2
    - (atomGram atom c c - 1 / 6) * atomGram atom a b ^ 2

/-- The balanced shifted determinant on the doubled correlations:
`216 det(G_T - 1/6) = 8 - 18 Q + 54 c`. -/
theorem atomShiftBlockDet_balanced (atom : Fin 6 → (Fin 3 → ℝ))
    (hbal : ∀ y : Fin 6, atomGram atom y y = 1 / 2) (a b c : Fin 6) :
    216 * atomShiftBlockDet atom a b c
      = 8 - 18 * ((2 * atomGram atom a b) ^ 2 + (2 * atomGram atom a c) ^ 2
            + (2 * atomGram atom b c) ^ 2)
        + 54 * ((2 * atomGram atom a b) * (2 * atomGram atom a c)
            * (2 * atomGram atom b c)) := by
  rw [atomShiftBlockDet, hbal a, hbal b, hbal c]
  ring

/-- **THE TRIANGLE CRITERION.**  At balance, the determinant arm of the win is
exactly the triangle inequality `Q - 3 c ≤ 4 / 9`. -/
theorem atomShiftBlockDet_balanced_nonneg_iff (atom : Fin 6 → (Fin 3 → ℝ))
    (hbal : ∀ y : Fin 6, atomGram atom y y = 1 / 2) (a b c : Fin 6) :
    0 ≤ atomShiftBlockDet atom a b c
      ↔ (2 * atomGram atom a b) ^ 2 + (2 * atomGram atom a c) ^ 2
          + (2 * atomGram atom b c) ^ 2
        - 3 * ((2 * atomGram atom a b) * (2 * atomGram atom a c)
            * (2 * atomGram atom b c)) ≤ 4 / 9 := by
  have hkey := atomShiftBlockDet_balanced atom hbal a b c
  constructor
  · intro hpos
    nlinarith
  · intro htri
    nlinarith

/-- **THE EQUILATERAL FACT.**  `3 r ^ 2 - 3 r ^ 3 ≤ 4 / 9` for every
`r ≥ -1/3`, from `27 r ^ 3 - 27 r ^ 2 + 4 = (3 r - 2) ^ 2 * (3 r + 1)`.
Every equilateral triangle passes the criterion, and only `r = 2/3` is
sharp. -/
theorem atomEquilateralCubic (r : ℝ) (hr : -(1 : ℝ) / 3 ≤ r) :
    3 * r ^ 2 - 3 * r ^ 3 ≤ 4 / 9 := by
  nlinarith [mul_nonneg (sq_nonneg (3 * r - 2)) (by linarith : (0 : ℝ) ≤ 3 * r + 1)]

/-- **THE PATH LAW.**  For distinct slots the four two-step paths total the
negated leverage charge: `∑ paths = -(d_x + d_y) H_xy` with
`d = 2 leverage - 1`. -/
theorem atomInvolutionPath (atom : Fin 6 → (Fin 3 → ℝ))
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (x y : Fin 6) (hxy : x ≠ y) :
    (∑ z ∈ (Finset.univ.erase x).erase y,
        (2 * atomGram atom x z) * (2 * atomGram atom z y))
      = -(((2 * atomGram atom x x - 1) + (2 * atomGram atom y y - 1))
          * (2 * atomGram atom x y)) := by
  classical
  have hidem := atomGram_idempotent (atom := atom) hframe x y
  have hy : y ∈ Finset.univ.erase x := by
    simp [Finset.mem_erase, Ne.symm hxy]
  have hx : x ∈ (Finset.univ : Finset (Fin 6)) := Finset.mem_univ x
  have hsplitx : (∑ z, atomGram atom x z * atomGram atom z y)
      = atomGram atom x x * atomGram atom x y
        + ∑ z ∈ Finset.univ.erase x, atomGram atom x z * atomGram atom z y := by
    rw [← Finset.add_sum_erase _ _ hx]
  have hsplity : (∑ z ∈ Finset.univ.erase x, atomGram atom x z * atomGram atom z y)
      = atomGram atom x y * atomGram atom y y
        + ∑ z ∈ (Finset.univ.erase x).erase y,
            atomGram atom x z * atomGram atom z y := by
    rw [← Finset.add_sum_erase _ _ hy]
  have hbase : (∑ z ∈ (Finset.univ.erase x).erase y,
      atomGram atom x z * atomGram atom z y)
      = atomGram atom x y - atomGram atom x x * atomGram atom x y
        - atomGram atom x y * atomGram atom y y := by
    have hclose := hidem
    rw [hsplitx, hsplity] at hclose
    linarith
  have hfour : (∑ z ∈ (Finset.univ.erase x).erase y,
      (2 * atomGram atom x z) * (2 * atomGram atom z y))
      = 4 * ∑ z ∈ (Finset.univ.erase x).erase y,
          atomGram atom x z * atomGram atom z y := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun z _ => by ring
  rw [hfour, hbase]
  ring

/-- **THE POLYGON LAW.**  At balance the leverage charge vanishes: the four
two-step paths of every pair total zero. -/
theorem atomBalancedPolygon (atom : Fin 6 → (Fin 3 → ℝ))
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (hbal : ∀ y : Fin 6, atomGram atom y y = 1 / 2)
    (x y : Fin 6) (hxy : x ≠ y) :
    (∑ z ∈ (Finset.univ.erase x).erase y,
        (2 * atomGram atom x z) * (2 * atomGram atom z y)) = 0 := by
  rw [atomInvolutionPath atom hframe x y hxy, hbal x, hbal y]
  ring

/-- **THE PATH KILL.**  At balance, one path product is dominated by half the
total cross weight of its endpoints.  A heavy in-triangle pair forces heavy
cancellation weight outside the triangle. -/
theorem atomBalancedPathKill (atom : Fin 6 → (Fin 3 → ℝ))
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (hbal : ∀ y : Fin 6, atomGram atom y y = 1 / 2)
    (x y z : Fin 6) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    |(2 * atomGram atom x z) * (2 * atomGram atom z y)|
      ≤ ∑ w ∈ ((Finset.univ.erase x).erase y).erase z,
          ((2 * atomGram atom x w) ^ 2 + (2 * atomGram atom y w) ^ 2) / 2 := by
  classical
  have hz : z ∈ (Finset.univ.erase x).erase y := by
    simp [Finset.mem_erase, Ne.symm hxz, Ne.symm hyz]
  have hpoly := atomBalancedPolygon atom hframe hbal x y hxy
  have hsplit : (∑ w ∈ (Finset.univ.erase x).erase y,
      (2 * atomGram atom x w) * (2 * atomGram atom w y))
      = (2 * atomGram atom x z) * (2 * atomGram atom z y)
        + ∑ w ∈ ((Finset.univ.erase x).erase y).erase z,
            (2 * atomGram atom x w) * (2 * atomGram atom w y) := by
    rw [← Finset.add_sum_erase _ _ hz]
  have hneg : (2 * atomGram atom x z) * (2 * atomGram atom z y)
      = -(∑ w ∈ ((Finset.univ.erase x).erase y).erase z,
          (2 * atomGram atom x w) * (2 * atomGram atom w y)) := by
    rw [hsplit] at hpoly
    linarith
  rw [hneg, abs_neg]
  calc |∑ w ∈ ((Finset.univ.erase x).erase y).erase z,
        (2 * atomGram atom x w) * (2 * atomGram atom w y)|
      ≤ ∑ w ∈ ((Finset.univ.erase x).erase y).erase z,
          |(2 * atomGram atom x w) * (2 * atomGram atom w y)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ w ∈ ((Finset.univ.erase x).erase y).erase z,
          ((2 * atomGram atom x w) ^ 2 + (2 * atomGram atom y w) ^ 2) / 2 := by
        refine Finset.sum_le_sum fun w _ => ?_
        rw [abs_mul, atomGram_comm atom w y]
        nlinarith [sq_nonneg (|2 * atomGram atom x w| - |2 * atomGram atom y w|),
          sq_abs (2 * atomGram atom x w), sq_abs (2 * atomGram atom y w),
          abs_nonneg (2 * atomGram atom x w), abs_nonneg (2 * atomGram atom y w)]

/-- The third symmetric function of a shifted four-set block: the sum of its
four erased shifted determinants. -/
noncomputable def atomQuartetThird (atom : Fin 6 → (Fin 3 → ℝ)) (a b c d : Fin 6) : ℝ :=
  atomShiftBlockDet atom b c d + atomShiftBlockDet atom a c d
    + atomShiftBlockDet atom a b d + atomShiftBlockDet atom a b c

/-- **THE QUARTET PIGEONHOLE.**  A positive third symmetric function hands a
positive erased shifted determinant.  Together with a cover of the four-set
this is the quartet route to a winning triple. -/
theorem exists_pos_of_quartetThird_pos (atom : Fin 6 → (Fin 3 → ℝ))
    (a b c d : Fin 6) (hpos : 0 < atomQuartetThird atom a b c d) :
    0 < atomShiftBlockDet atom b c d ∨ 0 < atomShiftBlockDet atom a c d
      ∨ 0 < atomShiftBlockDet atom a b d ∨ 0 < atomShiftBlockDet atom a b c := by
  by_contra hcon
  simp only [not_or, not_lt] at hcon
  obtain ⟨hone, htwo, hthree, hfour⟩ := hcon
  rw [atomQuartetThird] at hpos
  linarith


/-! ## 6. The row law, the mass cap and the triangle budget -/

/-- **THE ROW LAW.**  At balance the six doubled correlations of one slot carry
total square two: the diagonal unit plus one unit of off-diagonal weight. -/
theorem atomBalancedRowSix (atom : Fin 6 → (Fin 3 → ℝ))
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (hbal : ∀ y : Fin 6, atomGram atom y y = 1 / 2) (y : Fin 6) :
    (∑ z, (2 * atomGram atom y z) ^ 2) = 2 := by
  have hidem := atomGram_idempotent (atom := atom) hframe y y
  have hsq : (∑ z, (2 * atomGram atom y z) ^ 2)
      = 4 * ∑ z, atomGram atom y z * atomGram atom z y := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [atomGram_comm atom z y]
    ring
  rw [hsq, hidem, hbal y]
  norm_num

/-- The off-diagonal row weight of one slot at balance: erase the slot and one
unit remains. -/
theorem atomBalancedRow (atom : Fin 6 → (Fin 3 → ℝ))
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (hbal : ∀ y : Fin 6, atomGram atom y y = 1 / 2) (y : Fin 6) :
    (∑ z ∈ Finset.univ.erase y, (2 * atomGram atom y z) ^ 2) = 1 := by
  have hsix := atomBalancedRowSix atom hframe hbal y
  have hsplit : (∑ z, (2 * atomGram atom y z) ^ 2)
      = (2 * atomGram atom y y) ^ 2
        + ∑ z ∈ Finset.univ.erase y, (2 * atomGram atom y z) ^ 2 := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ y)]
  rw [hsplit, hbal y] at hsix
  norm_num at hsix
  linarith

/-- **THE MASS CAP.**  At balance every block obeys `Q + 2 c ≤ 1` and
`Q - 2 c ≤ 1`: the two determinants of the cut are nonnegative, so the squared
weight of a block never passes one. -/
theorem atomBalancedMassCap (atom : Fin 6 → (Fin 3 → ℝ))
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (hbal : ∀ y : Fin 6, atomGram atom y y = 1 / 2) (σ : Equiv.Perm (Fin 6)) :
    (2 * atomGram atom (σ 0) (σ 1)) ^ 2 + (2 * atomGram atom (σ 0) (σ 2)) ^ 2
        + (2 * atomGram atom (σ 1) (σ 2)) ^ 2
      + 2 * ((2 * atomGram atom (σ 0) (σ 1)) * (2 * atomGram atom (σ 0) (σ 2))
          * (2 * atomGram atom (σ 1) (σ 2))) ≤ 1
    ∧ (2 * atomGram atom (σ 0) (σ 1)) ^ 2 + (2 * atomGram atom (σ 0) (σ 2)) ^ 2
        + (2 * atomGram atom (σ 1) (σ 2)) ^ 2
      - 2 * ((2 * atomGram atom (σ 0) (σ 1)) * (2 * atomGram atom (σ 0) (σ 2))
          * (2 * atomGram atom (σ 1) (σ 2))) ≤ 1 := by
  have hone := atomBlockDet_balanced atom hbal (σ 0) (σ 1) (σ 2)
  have htwo := atomBlockDet_balanced_twin atom hframe hbal σ
  have hnn₁ := atomBlockDet_nonneg atom (σ 0) (σ 1) (σ 2)
  have hnn₂ := atomBlockDet_nonneg atom (σ 3) (σ 4) (σ 5)
  constructor
  · nlinarith
  · nlinarith

/-- **THE TRIANGLE BUDGET.**  At balance, twice the modulus of one path product
plus twice the closing weight plus the two path weights never passes two.  This
is the polygon law spent against the row law: a heavy adjacent pair leaves no
room for its closing edge. -/
theorem atomBalancedTriangleBudget (atom : Fin 6 → (Fin 3 → ℝ))
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (hbal : ∀ y : Fin 6, atomGram atom y y = 1 / 2)
    (x y z : Fin 6) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    2 * |(2 * atomGram atom x z) * (2 * atomGram atom z y)|
        + 2 * (2 * atomGram atom x y) ^ 2
        + (2 * atomGram atom x z) ^ 2 + (2 * atomGram atom y z) ^ 2 ≤ 2 := by
  classical
  have hkill := atomBalancedPathKill atom hframe hbal x y z hxy hxz hyz
  have hy : y ∈ Finset.univ.erase x := by
    simp [Finset.mem_erase, Ne.symm hxy]
  have hz : z ∈ (Finset.univ.erase x).erase y := by
    simp [Finset.mem_erase, Ne.symm hxz, Ne.symm hyz]
  have hrowx : (∑ w ∈ ((Finset.univ.erase x).erase y).erase z,
      (2 * atomGram atom x w) ^ 2)
      = 1 - (2 * atomGram atom x y) ^ 2 - (2 * atomGram atom x z) ^ 2 := by
    have hbase := atomBalancedRow atom hframe hbal x
    have hsy : (∑ w ∈ Finset.univ.erase x, (2 * atomGram atom x w) ^ 2)
        = (2 * atomGram atom x y) ^ 2
          + ∑ w ∈ (Finset.univ.erase x).erase y, (2 * atomGram atom x w) ^ 2 := by
      rw [← Finset.add_sum_erase _ _ hy]
    have hsz : (∑ w ∈ (Finset.univ.erase x).erase y, (2 * atomGram atom x w) ^ 2)
        = (2 * atomGram atom x z) ^ 2
          + ∑ w ∈ ((Finset.univ.erase x).erase y).erase z,
              (2 * atomGram atom x w) ^ 2 := by
      rw [← Finset.add_sum_erase _ _ hz]
    rw [hsy, hsz] at hbase
    linarith
  have hyx : x ∈ Finset.univ.erase y := by
    simp [Finset.mem_erase, hxy]
  have hzmem : z ∈ (Finset.univ.erase y).erase x := by
    simp [Finset.mem_erase, Ne.symm hyz, Ne.symm hxz]
  have hrowy : (∑ w ∈ ((Finset.univ.erase x).erase y).erase z,
      (2 * atomGram atom y w) ^ 2)
      = 1 - (2 * atomGram atom y x) ^ 2 - (2 * atomGram atom y z) ^ 2 := by
    have hbase := atomBalancedRow atom hframe hbal y
    have hsx : (∑ w ∈ Finset.univ.erase y, (2 * atomGram atom y w) ^ 2)
        = (2 * atomGram atom y x) ^ 2
          + ∑ w ∈ (Finset.univ.erase y).erase x, (2 * atomGram atom y w) ^ 2 := by
      rw [← Finset.add_sum_erase _ _ hyx]
    have hsz : (∑ w ∈ (Finset.univ.erase y).erase x, (2 * atomGram atom y w) ^ 2)
        = (2 * atomGram atom y z) ^ 2
          + ∑ w ∈ ((Finset.univ.erase y).erase x).erase z,
              (2 * atomGram atom y w) ^ 2 := by
      rw [← Finset.add_sum_erase _ _ hzmem]
    have hswap : ((Finset.univ.erase y).erase x).erase z
        = ((Finset.univ.erase x).erase y).erase z := by
      rw [Finset.erase_right_comm (a := y) (b := x)]
    rw [hsx, hsz, hswap] at hbase
    linarith
  have hhalf : (∑ w ∈ ((Finset.univ.erase x).erase y).erase z,
      ((2 * atomGram atom x w) ^ 2 + (2 * atomGram atom y w) ^ 2) / 2)
      = ((1 - (2 * atomGram atom x y) ^ 2 - (2 * atomGram atom x z) ^ 2)
        + (1 - (2 * atomGram atom y x) ^ 2 - (2 * atomGram atom y z) ^ 2)) / 2 := by
    rw [← hrowx, ← hrowy, ← Finset.sum_add_distrib, ← Finset.sum_div]
  have hsym : atomGram atom y x = atomGram atom x y := atomGram_comm atom y x
  rw [hhalf, hsym] at hkill
  linarith

/-- **THE ANTI-CLUSTERING LAW.**  Two doubled correlations of modulus at least
`2/3` at a common slot force the closing squared correlation down to `1/9`:
heavy edges never close into heavy triangles. -/
theorem atomBalancedHeavyPairThird (atom : Fin 6 → (Fin 3 → ℝ))
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (hbal : ∀ y : Fin 6, atomGram atom y y = 1 / 2)
    (x y z : Fin 6) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hone : 4 / 9 ≤ (2 * atomGram atom x z) ^ 2)
    (htwo : 4 / 9 ≤ (2 * atomGram atom y z) ^ 2) :
    (2 * atomGram atom x y) ^ 2 ≤ 1 / 9 := by
  have hbudget := atomBalancedTriangleBudget atom hframe hbal x y z hxy hxz hyz
  have habs : 4 / 9 ≤ |(2 * atomGram atom x z) * (2 * atomGram atom z y)| := by
    rw [abs_mul, atomGram_comm atom z y]
    have hax : (2 : ℝ) / 3 ≤ |2 * atomGram atom x z| := by
      nlinarith [sq_abs (2 * atomGram atom x z), abs_nonneg (2 * atomGram atom x z)]
    have hay : (2 : ℝ) / 3 ≤ |2 * atomGram atom y z| := by
      nlinarith [sq_abs (2 * atomGram atom y z), abs_nonneg (2 * atomGram atom y z)]
    nlinarith [abs_nonneg (2 * atomGram atom x z), abs_nonneg (2 * atomGram atom y z)]
  linarith

/-- The shifted trace at balance: the first symmetric function of
`G_T - (1/6) 1` is one. -/
theorem atomBalancedShiftTrace (atom : Fin 6 → (Fin 3 → ℝ))
    (hbal : ∀ y : Fin 6, atomGram atom y y = 1 / 2) (a b c : Fin 6) :
    (atomGram atom a a - 1 / 6) + (atomGram atom b b - 1 / 6)
      + (atomGram atom c c - 1 / 6) = 1 := by
  rw [hbal a, hbal b, hbal c]
  norm_num

/-- **THE FREE SECOND CONDITION.**  At balance the second symmetric function of
the shifted block is at least `1/12`: the mass cap makes the middle test of
the criterion free, and only the determinant arm decides. -/
theorem atomBalancedShiftSecond (atom : Fin 6 → (Fin 3 → ℝ))
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (hbal : ∀ y : Fin 6, atomGram atom y y = 1 / 2) (σ : Equiv.Perm (Fin 6)) :
    1 / 12
      ≤ ((atomGram atom (σ 0) (σ 0) - 1 / 6) * (atomGram atom (σ 1) (σ 1) - 1 / 6)
            - atomGram atom (σ 0) (σ 1) ^ 2)
        + ((atomGram atom (σ 0) (σ 0) - 1 / 6) * (atomGram atom (σ 2) (σ 2) - 1 / 6)
            - atomGram atom (σ 0) (σ 2) ^ 2)
        + ((atomGram atom (σ 1) (σ 1) - 1 / 6) * (atomGram atom (σ 2) (σ 2) - 1 / 6)
            - atomGram atom (σ 1) (σ 2) ^ 2) := by
  obtain ⟨hcapPlus, hcapMinus⟩ := atomBalancedMassCap atom hframe hbal σ
  rw [hbal (σ 0), hbal (σ 1), hbal (σ 2)]
  nlinarith

/-- **THE BALANCED TRIANGLE TARGET.**  The determinant arm of balanced
one-sixth supply: some triple of every balanced frame carries a nonnegative
shifted determinant.  With `atomBalancedShiftTrace` and
`atomBalancedShiftSecond` the other two symmetric functions of that block are
free, so this Prop is the whole balanced criterion. -/
def AtomBalancedDetWin : Prop :=
  ∀ atom : Fin 6 → (Fin 3 → ℝ),
    (∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction) →
    (∀ y : Fin 6, atomGram atom y y = 1 / 2) →
    ∃ slotOne slotTwo slotThree : Fin 6,
      slotOne ≠ slotTwo ∧ slotOne ≠ slotThree ∧ slotTwo ≠ slotThree
        ∧ 0 ≤ atomShiftBlockDet atom slotOne slotTwo slotThree

/-- **THE HEAVY EDGE ESCAPE.**  A doubled correlation of squared modulus at
least `2/3` hands a triple through its first slot whose squared block weight
stays at or below `4/9`: the six opposite triples total `4 - 2 t`. -/
theorem atomHeavyEdgeEscape (atom : Fin 6 → (Fin 3 → ℝ))
    (hframe : ∀ probe direction : Fin 3 → ℝ,
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ direction)) = probe ⬝ᵥ direction)
    (hbal : ∀ y : Fin 6, atomGram atom y y = 1 / 2)
    (σ : Equiv.Perm (Fin 6))
    (hheavy : 2 / 3 ≤ (2 * atomGram atom (σ 0) (σ 1)) ^ 2) :
    ∃ i j : Fin 6, i ≠ j ∧ σ 0 ≠ i ∧ σ 0 ≠ j ∧ σ 1 ≠ i ∧ σ 1 ≠ j
      ∧ (2 * atomGram atom (σ 0) i) ^ 2 + (2 * atomGram atom (σ 0) j) ^ 2
          + (2 * atomGram atom i j) ^ 2 ≤ 4 / 9 := by
  classical
  have hrow : ∀ y : Fin 6,
      (2 * atomGram atom y (σ 0)) ^ 2 + (2 * atomGram atom y (σ 1)) ^ 2
        + (2 * atomGram atom y (σ 2)) ^ 2 + (2 * atomGram atom y (σ 3)) ^ 2
        + (2 * atomGram atom y (σ 4)) ^ 2 + (2 * atomGram atom y (σ 5)) ^ 2 = 2 := by
    intro y
    have hsix := atomBalancedRowSix atom hframe hbal y
    have hperm : (∑ z, (2 * atomGram atom y z) ^ 2)
        = ∑ k, (2 * atomGram atom y (σ k)) ^ 2 :=
      (Equiv.sum_comp σ fun z => (2 * atomGram atom y z) ^ 2).symm
    rw [hperm, Fin.sum_univ_six] at hsix
    linarith
  have hq : ∀ a b : Fin 6, (2 * atomGram atom a b) ^ 2 = (2 * atomGram atom b a) ^ 2 := by
    intro a b
    rw [atomGram_comm atom a b]
  have hd : ∀ y : Fin 6, (2 * atomGram atom y y) ^ 2 = 1 := by
    intro y
    rw [hbal y]
    norm_num
  by_contra hcon
  push Not at hcon
  have hinj : Function.Injective σ := σ.injective
  have hne : ∀ i j : Fin 6, i ≠ j → σ i ≠ σ j := fun i j hij h => hij (hinj h)
  have hQ : ∀ i j : Fin 6, i ≠ j → 2 ≤ i → 2 ≤ j →
      4 / 9 < (2 * atomGram atom (σ 0) (σ i)) ^ 2
        + (2 * atomGram atom (σ 0) (σ j)) ^ 2
        + (2 * atomGram atom (σ i) (σ j)) ^ 2 := by
    intro i j hij hi hj
    exact hcon (σ i) (σ j) (hne i j hij) (hne 0 i (by omega)) (hne 0 j (by omega))
      (hne 1 i (by omega)) (hne 1 j (by omega))
  have h23 := hQ 2 3 (by omega) (by omega) (by omega)
  have h24 := hQ 2 4 (by omega) (by omega) (by omega)
  have h25 := hQ 2 5 (by omega) (by omega) (by omega)
  have h34 := hQ 3 4 (by omega) (by omega) (by omega)
  have h35 := hQ 3 5 (by omega) (by omega) (by omega)
  have h45 := hQ 4 5 (by omega) (by omega) (by omega)
  have hrow0 := hrow (σ 0)
  have hrow1 := hrow (σ 1)
  have hrow2 := hrow (σ 2)
  have hrow3 := hrow (σ 3)
  have hrow4 := hrow (σ 4)
  have hrow5 := hrow (σ 5)
  linarith [h23, h24, h25, h34, h35, h45, hrow0, hrow1, hrow2, hrow3, hrow4, hrow5,
    hd (σ 0), hd (σ 1), hd (σ 2), hd (σ 3), hd (σ 4), hd (σ 5), hheavy,
    hq (σ 0) (σ 1), hq (σ 2) (σ 0), hq (σ 3) (σ 0), hq (σ 4) (σ 0), hq (σ 5) (σ 0),
    hq (σ 2) (σ 1), hq (σ 3) (σ 1), hq (σ 4) (σ 1), hq (σ 5) (σ 1),
    hq (σ 3) (σ 2), hq (σ 4) (σ 2), hq (σ 5) (σ 2), hq (σ 4) (σ 3),
    hq (σ 5) (σ 3), hq (σ 5) (σ 4), hq (σ 1) (σ 0)]

end Gtz
