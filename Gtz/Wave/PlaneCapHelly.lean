import Gtz.Wave.PlaneWitnessLedger
import Mathlib.Analysis.Convex.Radon
import Mathlib.LinearAlgebra.CrossProduct

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The cap reading of the plane residue, and the Helly collapse to three atoms

The plane pair residue asks for a dominating pair among six plane atoms.  The
plane witness ledger replaced that search by a dual certificate.  This module
replaces the certificate by a POINT OF THE UNIT DISC.

The bridge is the DOUBLED READING.  A plane carries an orthonormal frame of two
vectors, an atom of the plane reads as a pair of coordinates, and the doubled
reading squares that pair.  The doubled reading obeys two polynomial laws: its
own energy is the square of the atom energy, and the doubled dot of two atoms is
twice the squared atom dot minus the product of the two energies.  Thus the pair
hypothesis becomes a LINEAR inequality between doubled readings, and a
dominating witness becomes a point of the closed unit disc that meets one half
plane at every atom.

That is a family of CONVEX sets in a plane.  Helly's theorem in dimension two
asks only for THREE-WISE intersection, thus the whole residue at six atoms
reduces to the residue at THREE atoms.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.cross_smul_right`, `Gtz.cross_dot_axis`, `Gtz.exists_planeUnit` — the
  cross-product laws that build the frame.
* `Gtz.exists_planeOrthoFrame` — **THE ORTHONORMAL FRAME OF A PLANE.**  Every
  plane of three-space carries two orthonormal vectors, and every pair of plane
  vectors reads its dot product through them.
* `Gtz.doubleRead`, `Gtz.doubleRead_dot_raw`, `Gtz.doubleRead_dot`,
  `Gtz.doubleRead_dot_self` — **THE TWO LAWS OF THE DOUBLED READING.**
* `Gtz.planeCap`, `Gtz.convex_planeCap`, `Gtz.zero_mem_planeCap` — the cap of an
  atom, its convexity, and the origin.
* `Gtz.PlaneCapTripleClosed` — **THE RESIDUE AT THREE ATOMS.**  Three vectors of
  a plane and six real numbers.  No combinatorial search, no eigenvalue, no
  square root, no atom.
* `Gtz.exists_capPoint_of_triple` — **THE HELLY COLLAPSE.**  The three-atom
  residue supplies a common cap point at every atom count of at least three.
* `Gtz.false_of_capPoint` — **THE CAP KILL.**  A plane frame with nonnegative
  scales of total less than one admits no common cap point.
* `Gtz.atomPairGramClosed_of_capTriple` — **THE THREE-ATOM RESIDUE CLOSES THE
  PLANE PAIR CEILING.**
* `Gtz.atomPairCeilingClosed_of_capTriple`,
  `Gtz.rankFiveDenseHeavyFiveClosed_of_capTriple`,
  `Gtz.rankFiveDenseHeavyFiveDistinctClosed_of_capTriple`,
  `Gtz.forall_shifted_weight_pos_of_capTriple`,
  `Gtz.SixThreeCrux.shifted_weight_pos_of_capTriple`,
  `Gtz.SixThreeCrux.false_of_capTriple_of_shift_zero` — the campaign
  consequences, from the three-atom residue alone.
* `Gtz.capPoint_of_full_gap` — **THE SHARP STRATUM.**  One atom whose gap is its
  whole energy pins the cap point, and the pair law IS the domination.
* `Gtz.capPoint_of_light` — **THE LIGHT STRATUM.**
* `Gtz.capPoint_of_cover` — **THE COVER STRATUM.**
* `Gtz.exists_capPoint_of_pair` — **THE TWO-ATOM CAP LAW.**  Two caps of the
  plane ALWAYS meet.  Thus the residue lives at three atoms and no fewer.
-/

namespace Gtz

open scoped BigOperators Matrix

/-! ## Layer 1 — the orthonormal frame of a plane in three-space -/

/-- The cross product is linear in its second factor. -/
theorem cross_smul_right (vecOne vecTwo : Fin 3 → ℝ) (factor : ℝ) :
    vecOne ⨯₃ (factor • vecTwo) = factor • (vecOne ⨯₃ vecTwo) := by
  ext index
  fin_cases index <;> simp [cross_apply]

/-- The cross product of a vector with a plane vector leaves the plane. -/
theorem cross_dot_axis (axis vec : Fin 3 → ℝ) : (axis ⨯₃ vec) ⬝ᵥ axis = 0 := by
  rw [dotProduct_comm (axis ⨯₃ vec) axis]
  exact dot_self_cross axis vec

/-- A plane of three-space carries a unit vector. -/
theorem exists_planeUnit (axis : Fin 3 → ℝ) (haxis : (0 : ℝ) < axis ⬝ᵥ axis) :
    ∃ first : Fin 3 → ℝ, first ⬝ᵥ axis = 0 ∧ first ⬝ᵥ first = 1 := by
  classical
  have hcoords : axis ⬝ᵥ axis = axis 0 ^ 2 + axis 1 ^ 2 + axis 2 ^ 2 := by
    rw [dot_self_eq_sum_sq]
    simp [Fin.sum_univ_three]
  have hexists : ∃ index : Fin 3, (0 : ℝ) < axis ⬝ᵥ axis - axis index ^ 2 := by
    by_contra hnone
    rw [not_exists] at hnone
    have h0 := not_lt.mp (hnone 0)
    have h1 := not_lt.mp (hnone 1)
    have h2 := not_lt.mp (hnone 2)
    linarith
  obtain ⟨index, hindex⟩ := hexists
  have hcrossEnergy : (axis ⨯₃ unitVector index) ⬝ᵥ (axis ⨯₃ unitVector index)
      = axis ⬝ᵥ axis - axis index ^ 2 := by
    rw [cross_dot_cross, unitVector_dot_self, dotProduct_comm axis (unitVector index),
      unitVector_dot]
    ring
  have hrawEnergy : (0 : ℝ) < (axis ⨯₃ unitVector index) ⬝ᵥ (axis ⨯₃ unitVector index) := by
    rw [hcrossEnergy]; exact hindex
  refine ⟨(Real.sqrt ((axis ⨯₃ unitVector index) ⬝ᵥ (axis ⨯₃ unitVector index)))⁻¹
      • (axis ⨯₃ unitVector index), ?_, ?_⟩
  · rw [smul_dotProduct, cross_dot_axis, smul_eq_mul, mul_zero]
  · rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc, ← mul_inv,
      Real.mul_self_sqrt hrawEnergy.le, inv_mul_cancel₀ (ne_of_gt hrawEnergy)]

/-- **THE ORTHONORMAL FRAME OF A PLANE.**  A plane of three-space, given as the
orthogonal complement of a nonzero axis, carries two orthonormal vectors, and
every pair of plane vectors reads its dot product through them.

The construction is the cross product.  The completeness comes from the vector
triple product: a plane vector orthogonal to the two frame vectors has a
vanishing cross with the axis, thus a vanishing energy. -/
theorem exists_planeOrthoFrame (axis : Fin 3 → ℝ) (haxis : (0 : ℝ) < axis ⬝ᵥ axis) :
    ∃ first second : Fin 3 → ℝ,
      first ⬝ᵥ axis = 0 ∧ second ⬝ᵥ axis = 0
        ∧ first ⬝ᵥ first = 1 ∧ second ⬝ᵥ second = 1 ∧ first ⬝ᵥ second = 0
        ∧ ∀ vecOne vecTwo : Fin 3 → ℝ, vecOne ⬝ᵥ axis = 0 → vecTwo ⬝ᵥ axis = 0 →
            vecOne ⬝ᵥ vecTwo
              = (vecOne ⬝ᵥ first) * (vecTwo ⬝ᵥ first)
                + (vecOne ⬝ᵥ second) * (vecTwo ⬝ᵥ second) := by
  classical
  obtain ⟨first, hfirstAxis, hfirstEnergy⟩ := exists_planeUnit axis haxis
  have hcrossFirst : (axis ⨯₃ first) ⬝ᵥ (axis ⨯₃ first) = axis ⬝ᵥ axis := by
    rw [cross_dot_cross, hfirstEnergy, dotProduct_comm axis first, hfirstAxis]
    ring
  refine ⟨first, (Real.sqrt (axis ⬝ᵥ axis))⁻¹ • (axis ⨯₃ first), hfirstAxis, ?_, hfirstEnergy,
    ?_, ?_, ?_⟩
  · rw [smul_dotProduct, cross_dot_axis, smul_eq_mul, mul_zero]
  · rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, hcrossFirst, ← mul_assoc,
      ← mul_inv, Real.mul_self_sqrt haxis.le, inv_mul_cancel₀ (ne_of_gt haxis)]
  · rw [dotProduct_smul, dot_cross_self, smul_eq_mul, mul_zero]
  · intro vecOne vecTwo _ htwo
    set second : Fin 3 → ℝ := (Real.sqrt (axis ⬝ᵥ axis))⁻¹ • (axis ⨯₃ first) with hsecondDef
    have hsecondAxis : second ⬝ᵥ axis = 0 := by
      rw [hsecondDef, smul_dotProduct, cross_dot_axis, smul_eq_mul, mul_zero]
    have hsecondEnergy : second ⬝ᵥ second = 1 := by
      rw [hsecondDef, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, hcrossFirst,
        ← mul_assoc, ← mul_inv, Real.mul_self_sqrt haxis.le, inv_mul_cancel₀ (ne_of_gt haxis)]
    have hfirstSecond : first ⬝ᵥ second = 0 := by
      rw [hsecondDef, dotProduct_smul, dot_cross_self, smul_eq_mul, mul_zero]
    have hframeCross : first ⨯₃ second = (Real.sqrt (axis ⬝ᵥ axis))⁻¹ • axis := by
      rw [hsecondDef, cross_smul_right, cross_cross_eq_smul_sub_smul' first axis first,
        hfirstEnergy, dotProduct_comm axis first, hfirstAxis]
      simp
    have hcomplete : ∀ vec : Fin 3 → ℝ, vec ⬝ᵥ axis = 0 →
        vec = (vec ⬝ᵥ first) • first + (vec ⬝ᵥ second) • second := by
      intro vec hvec
      set residual : Fin 3 → ℝ := vec - ((vec ⬝ᵥ first) • first + (vec ⬝ᵥ second) • second)
        with hresidualDef
      have hresFirst : residual ⬝ᵥ first = 0 := by
        rw [hresidualDef, sub_dotProduct, add_dotProduct, smul_dotProduct, smul_dotProduct,
          hfirstEnergy, dotProduct_comm second first, hfirstSecond]
        ring
      have hresSecond : residual ⬝ᵥ second = 0 := by
        rw [hresidualDef, sub_dotProduct, add_dotProduct, smul_dotProduct, smul_dotProduct,
          hsecondEnergy, hfirstSecond]
        ring
      have hresAxis : residual ⬝ᵥ axis = 0 := by
        rw [hresidualDef, sub_dotProduct, add_dotProduct, smul_dotProduct, smul_dotProduct,
          hfirstAxis, hsecondAxis, hvec]
        ring
      have hcrossZero : residual ⨯₃ axis = 0 := by
        have hkey : residual ⨯₃ (first ⨯₃ second) = 0 := by
          rw [cross_cross_eq_smul_sub_smul' residual first second, hresSecond,
            dotProduct_comm first residual, hresFirst]
          simp
        rw [hframeCross, cross_smul_right] at hkey
        have hne : (Real.sqrt (axis ⬝ᵥ axis))⁻¹ ≠ 0 :=
          inv_ne_zero (ne_of_gt (Real.sqrt_pos.mpr haxis))
        exact (smul_eq_zero.mp hkey).resolve_left hne
      have hlag := cross_dot_cross residual axis residual axis
      rw [hcrossZero, hresAxis] at hlag
      simp only [zero_dotProduct, zero_mul, sub_zero] at hlag
      have hprod : (residual ⬝ᵥ residual) * (axis ⬝ᵥ axis) = 0 := hlag.symm
      have hresEnergy : residual ⬝ᵥ residual = 0 :=
        (mul_eq_zero.mp hprod).resolve_right (ne_of_gt haxis)
      have hzero : residual = 0 := dotProduct_self_eq_zero.mp hresEnergy
      rw [hresidualDef] at hzero
      exact sub_eq_zero.mp hzero
    have hexp := hcomplete vecTwo htwo
    calc vecOne ⬝ᵥ vecTwo
        = vecOne ⬝ᵥ ((vecTwo ⬝ᵥ first) • first + (vecTwo ⬝ᵥ second) • second) := by rw [← hexp]
      _ = (vecOne ⬝ᵥ first) * (vecTwo ⬝ᵥ first) + (vecOne ⬝ᵥ second) * (vecTwo ⬝ᵥ second) := by
          rw [dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
          ring

/-! ## Layer 2 — the doubled reading of a plane atom -/

/-- The dot product of the plane, written out. -/
theorem dot_fin_two (vecOne vecTwo : Fin 2 → ℝ) :
    vecOne ⬝ᵥ vecTwo = vecOne 0 * vecTwo 0 + vecOne 1 * vecTwo 1 := by
  simp [dotProduct, Fin.sum_univ_two]

/-- **THE DOUBLED READING.**  A plane vector reads as two coordinates against an
orthonormal frame of the plane.  The doubled reading squares that pair: its
first entry is the difference of the squares, its second entry is twice the
product.

The doubled reading turns a QUADRATIC test on the plane into a LINEAR test on
the plane of readings.  That is the whole point of the construction. -/
def doubleRead (first second vec : Fin 3 → ℝ) : Fin 2 → ℝ :=
  ![(vec ⬝ᵥ first) ^ 2 - (vec ⬝ᵥ second) ^ 2, 2 * ((vec ⬝ᵥ first) * (vec ⬝ᵥ second))]

theorem doubleRead_zero (first second : Fin 3 → ℝ) (index : Fin 2) :
    doubleRead first second 0 index = 0 := by
  fin_cases index <;> simp [doubleRead]

/-- The doubled reading in raw coordinates. -/
theorem doubleRead_dot_raw (first second vecOne vecTwo : Fin 3 → ℝ) :
    doubleRead first second vecOne ⬝ᵥ doubleRead first second vecTwo
      = 2 * ((vecOne ⬝ᵥ first) * (vecTwo ⬝ᵥ first)
            + (vecOne ⬝ᵥ second) * (vecTwo ⬝ᵥ second)) ^ 2
        - ((vecOne ⬝ᵥ first) ^ 2 + (vecOne ⬝ᵥ second) ^ 2)
          * ((vecTwo ⬝ᵥ first) ^ 2 + (vecTwo ⬝ᵥ second) ^ 2) := by
  rw [dot_fin_two]
  simp only [doubleRead, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- **THE LAW OF THE DOUBLED READING.**  The doubled dot of two plane atoms is
twice the squared atom dot minus the product of the two atom energies. -/
theorem doubleRead_dot {axis first second : Fin 3 → ℝ}
    (hparse : ∀ vecOne vecTwo : Fin 3 → ℝ, vecOne ⬝ᵥ axis = 0 → vecTwo ⬝ᵥ axis = 0 →
      vecOne ⬝ᵥ vecTwo
        = (vecOne ⬝ᵥ first) * (vecTwo ⬝ᵥ first) + (vecOne ⬝ᵥ second) * (vecTwo ⬝ᵥ second))
    (vecOne vecTwo : Fin 3 → ℝ) (hone : vecOne ⬝ᵥ axis = 0) (htwo : vecTwo ⬝ᵥ axis = 0) :
    doubleRead first second vecOne ⬝ᵥ doubleRead first second vecTwo
      = 2 * (vecOne ⬝ᵥ vecTwo) ^ 2 - (vecOne ⬝ᵥ vecOne) * (vecTwo ⬝ᵥ vecTwo) := by
  have hcross := hparse vecOne vecTwo hone htwo
  have hself : ∀ vec : Fin 3 → ℝ, vec ⬝ᵥ axis = 0 →
      vec ⬝ᵥ vec = (vec ⬝ᵥ first) ^ 2 + (vec ⬝ᵥ second) ^ 2 := by
    intro vec hvec
    rw [hparse vec vec hvec hvec]
    ring
  rw [doubleRead_dot_raw, ← hcross, hself vecOne hone, hself vecTwo htwo]

/-- The doubled reading carries the square of the atom energy. -/
theorem doubleRead_dot_self {axis first second : Fin 3 → ℝ}
    (hparse : ∀ vecOne vecTwo : Fin 3 → ℝ, vecOne ⬝ᵥ axis = 0 → vecTwo ⬝ᵥ axis = 0 →
      vecOne ⬝ᵥ vecTwo
        = (vecOne ⬝ᵥ first) * (vecTwo ⬝ᵥ first) + (vecOne ⬝ᵥ second) * (vecTwo ⬝ᵥ second))
    (vec : Fin 3 → ℝ) (hvec : vec ⬝ᵥ axis = 0) :
    doubleRead first second vec ⬝ᵥ doubleRead first second vec = (vec ⬝ᵥ vec) ^ 2 := by
  rw [doubleRead_dot hparse vec vec hvec hvec]
  ring

/-! ## Layer 3 — the caps of the plane of readings -/

/-- **THE CAP OF AN ATOM.**  The points of the closed unit disc whose reading
against one doubled atom reaches the level of that atom. -/
def planeCap (read : Fin 2 → ℝ) (level : ℝ) : Set (Fin 2 → ℝ) :=
  {point | point ⬝ᵥ point ≤ 1 ∧ level ≤ point ⬝ᵥ read}

theorem mem_planeCap {read : Fin 2 → ℝ} {level : ℝ} {point : Fin 2 → ℝ} :
    point ∈ planeCap read level ↔ point ⬝ᵥ point ≤ 1 ∧ level ≤ point ⬝ᵥ read := Iff.rfl

/-- **THE CAP IS CONVEX.**  It is the closed unit disc cut by one half plane. -/
theorem convex_planeCap (read : Fin 2 → ℝ) (level : ℝ) :
    Convex ℝ (planeCap read level) := by
  intro pointOne hone pointTwo htwo shareOne shareTwo hshareOne hshareTwo hshare
  obtain ⟨hdiscOne, hlevelOne⟩ := hone
  obtain ⟨hdiscTwo, hlevelTwo⟩ := htwo
  rw [dot_fin_two] at hdiscOne hdiscTwo
  have hcross : pointOne 0 * pointTwo 0 + pointOne 1 * pointTwo 1 ≤ 1 := by
    nlinarith [sq_nonneg (pointOne 0 - pointTwo 0), sq_nonneg (pointOne 1 - pointTwo 1)]
  have hpartOne : 0 ≤ shareOne ^ 2
      * (1 - (pointOne 0 * pointOne 0 + pointOne 1 * pointOne 1)) :=
    mul_nonneg (sq_nonneg _) (by linarith)
  have hpartTwo : 0 ≤ shareTwo ^ 2
      * (1 - (pointTwo 0 * pointTwo 0 + pointTwo 1 * pointTwo 1)) :=
    mul_nonneg (sq_nonneg _) (by linarith)
  have hpartCross : 0 ≤ 2 * (shareOne * shareTwo)
      * (1 - (pointOne 0 * pointTwo 0 + pointOne 1 * pointTwo 1)) :=
    mul_nonneg (by positivity) (by linarith)
  constructor
  · rw [dot_fin_two]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have hid : (shareOne * pointOne 0 + shareTwo * pointTwo 0)
          * (shareOne * pointOne 0 + shareTwo * pointTwo 0)
        + (shareOne * pointOne 1 + shareTwo * pointTwo 1)
          * (shareOne * pointOne 1 + shareTwo * pointTwo 1)
        = (shareOne + shareTwo) ^ 2
          - (shareOne ^ 2 * (1 - (pointOne 0 * pointOne 0 + pointOne 1 * pointOne 1))
            + shareTwo ^ 2 * (1 - (pointTwo 0 * pointTwo 0 + pointTwo 1 * pointTwo 1))
            + 2 * (shareOne * shareTwo)
              * (1 - (pointOne 0 * pointTwo 0 + pointOne 1 * pointTwo 1))) := by
      ring
    rw [hid, hshare]
    nlinarith [hpartOne, hpartTwo, hpartCross]
  · rw [add_dotProduct, smul_dotProduct, smul_dotProduct, smul_eq_mul, smul_eq_mul]
    have hone : shareOne * level ≤ shareOne * (pointOne ⬝ᵥ read) :=
      mul_le_mul_of_nonneg_left hlevelOne hshareOne
    have htwo : shareTwo * level ≤ shareTwo * (pointTwo ⬝ᵥ read) :=
      mul_le_mul_of_nonneg_left hlevelTwo hshareTwo
    have hsum : shareOne * level + shareTwo * level = level := by
      rw [← add_mul, hshare, one_mul]
    linarith

/-- A cap of nonpositive level holds the origin. -/
theorem zero_mem_planeCap {read : Fin 2 → ℝ} {level : ℝ} (hlevel : level ≤ 0) :
    (0 : Fin 2 → ℝ) ∈ planeCap read level := by
  refine ⟨?_, ?_⟩
  · rw [dot_fin_two]; norm_num
  · rw [zero_dotProduct]; exact hlevel

/-! ## Layer 4 — the residue at three atoms, and the Helly collapse -/

/-- **THE RESIDUE AT THREE ATOMS.**  Three readings of the plane, three
energies and three gaps, tied by the pair law, always carry a common cap point.

This is a statement about three vectors of a plane and six real numbers.  It
carries no combinatorial search, no eigenvalue, no square root and no atom. -/
def PlaneCapTripleClosed : Prop :=
  ∀ (read : Fin 3 → (Fin 2 → ℝ)) (energy gap : Fin 3 → ℝ),
    (∀ index, read index ⬝ᵥ read index = energy index ^ 2) →
    (∀ index, 0 ≤ gap index) →
    (∀ index, gap index ≤ energy index) →
    (∀ indexOne indexTwo,
      2 * gap indexOne * gap indexTwo - energy indexOne * energy indexTwo
        ≤ read indexOne ⬝ᵥ read indexTwo) →
    ∃ point : Fin 2 → ℝ, point ⬝ᵥ point ≤ 1
      ∧ ∀ index, 2 * gap index - energy index ≤ point ⬝ᵥ read index

/-- **THE HELLY COLLAPSE.**  The residue at three atoms supplies a common cap
point at every atom count of at least three.

The caps are convex sets of a plane, and the plane has dimension two.  Thus
Helly's theorem asks only for the intersection of three of them. -/
theorem exists_capPoint_of_triple {slotCount : ℕ} (hcount : 3 ≤ slotCount)
    (htriple : PlaneCapTripleClosed)
    (read : Fin slotCount → (Fin 2 → ℝ)) (energy gap : Fin slotCount → ℝ)
    (henergy : ∀ slot, read slot ⬝ᵥ read slot = energy slot ^ 2)
    (hgapNonneg : ∀ slot, 0 ≤ gap slot)
    (hgapLe : ∀ slot, gap slot ≤ energy slot)
    (hpair : ∀ slotOne slotTwo,
      2 * gap slotOne * gap slotTwo - energy slotOne * energy slotTwo
        ≤ read slotOne ⬝ᵥ read slotTwo) :
    ∃ point : Fin 2 → ℝ, point ⬝ᵥ point ≤ 1
      ∧ ∀ slot, 2 * gap slot - energy slot ≤ point ⬝ᵥ read slot := by
  classical
  have hrank : Module.finrank ℝ (Fin 2 → ℝ) = 2 := by simp
  have hcard : Module.finrank ℝ (Fin 2 → ℝ) + 1
      ≤ (Finset.univ : Finset (Fin slotCount)).card := by
    rw [hrank, Finset.card_univ, Fintype.card_fin]
    omega
  have hinter : ∀ subset ⊆ (Finset.univ : Finset (Fin slotCount)),
      subset.card = Module.finrank ℝ (Fin 2 → ℝ) + 1 →
      (⋂ slot ∈ subset, planeCap (read slot) (2 * gap slot - energy slot)).Nonempty := by
    intro subset _ hsize
    rw [hrank] at hsize
    obtain ⟨slotA, slotB, slotC, _, _, _, hsubset⟩ := Finset.card_eq_three.mp hsize
    obtain ⟨point, hdisc, hlevel⟩ :=
      htriple ![read slotA, read slotB, read slotC]
        ![energy slotA, energy slotB, energy slotC] ![gap slotA, gap slotB, gap slotC]
        (fun index => by fin_cases index <;> simpa using henergy _)
        (fun index => by fin_cases index <;> simpa using hgapNonneg _)
        (fun index => by fin_cases index <;> simpa using hgapLe _)
        (fun indexOne indexTwo => by
          fin_cases indexOne <;> fin_cases indexTwo <;> simpa using hpair _ _)
    refine ⟨point, ?_⟩
    rw [Set.mem_iInter₂]
    intro slot hslot
    rw [hsubset, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hslot
    rcases hslot with rfl | rfl | rfl
    · exact ⟨hdisc, by simpa using hlevel 0⟩
    · exact ⟨hdisc, by simpa using hlevel 1⟩
    · exact ⟨hdisc, by simpa using hlevel 2⟩
  obtain ⟨point, hpoint⟩ :=
    Convex.helly_theorem (𝕜 := ℝ) (F := fun slot : Fin slotCount =>
      planeCap (read slot) (2 * gap slot - energy slot)) hcard
      (fun slot _ => convex_planeCap _ _) hinter
  rw [Set.mem_iInter₂] at hpoint
  have hpos : 0 < slotCount := by omega
  obtain ⟨hdisc, _⟩ := hpoint ⟨0, hpos⟩ (Finset.mem_univ _)
  exact ⟨point, hdisc, fun slot => (hpoint slot (Finset.mem_univ slot)).2⟩

/-! ## Layer 5 — the cap kill -/

/-- **THE CAP KILL.**  A plane frame with nonnegative scales of total less than
one admits NO common cap point.

The point of the disc becomes a positive semidefinite form of the plane with
trace one.  The form is written on three plane directions — the two frame
vectors and their sum — and the master law of the witness ledger then caps the
total gap at one, while the trace law puts it at more than one. -/
theorem false_of_capPoint {slotCount : ℕ}
    (atom : Fin slotCount → (Fin 3 → ℝ)) (scale : Fin slotCount → ℝ)
    (axis first second : Fin 3 → ℝ)
    (haxis : (0 : ℝ) < axis ⬝ᵥ axis)
    (hplane : ∀ slot, atom slot ⬝ᵥ axis = 0)
    (hfirstAxis : first ⬝ᵥ axis = 0) (hsecondAxis : second ⬝ᵥ axis = 0)
    (hfirstEnergy : first ⬝ᵥ first = 1) (hsecondEnergy : second ⬝ᵥ second = 1)
    (hfirstSecond : first ⬝ᵥ second = 0)
    (hparse : ∀ vecOne vecTwo : Fin 3 → ℝ, vecOne ⬝ᵥ axis = 0 → vecTwo ⬝ᵥ axis = 0 →
      vecOne ⬝ᵥ vecTwo
        = (vecOne ⬝ᵥ first) * (vecTwo ⬝ᵥ first) + (vecOne ⬝ᵥ second) * (vecTwo ⬝ᵥ second))
    (hsmall : (∑ slot, scale slot) < 1)
    (hframe : ∀ probe other : Fin 3 → ℝ, probe ⬝ᵥ axis = 0 → other ⬝ᵥ axis = 0 →
      (∑ slot, (atom slot ⬝ᵥ probe) * (atom slot ⬝ᵥ other)) = probe ⬝ᵥ other)
    (point : Fin 2 → ℝ)
    (hcover : ∀ slot, 2 * (atom slot ⬝ᵥ atom slot - scale slot) - (atom slot ⬝ᵥ atom slot)
      ≤ point ⬝ᵥ doubleRead first second (atom slot)) :
    False := by
  classical
  refine false_of_plane_witness atom scale axis
    ![first, second, first + second]
    ![(1 + point 0) / 2 - point 1 / 2, (1 - point 0) / 2 - point 1 / 2, point 1 / 2] 0
    haxis hplane ?_ hsmall hframe ?_ ?_
  · intro index
    fin_cases index <;> simp [add_dotProduct, hfirstAxis, hsecondAxis]
  · have hsum : (first + second) ⬝ᵥ (first + second) = 2 := by
      rw [add_dotProduct, dotProduct_add, dotProduct_add, hfirstEnergy, hsecondEnergy,
        hfirstSecond, dotProduct_comm second first, hfirstSecond]
      ring
    rw [Fin.sum_univ_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, hfirstEnergy, hsecondEnergy, hsum]
    ring_nf
    norm_num
  · intro slot
    have hplaneSlot := hplane slot
    have hparseSlot := hparse (atom slot) (atom slot) hplaneSlot hplaneSlot
    have hsplit : (atom slot + 0) = atom slot := by ring
    have hcoverSlot := hcover slot
    rw [dot_fin_two] at hcoverSlot
    simp only [doubleRead, Matrix.cons_val_zero, Matrix.cons_val_one] at hcoverSlot
    rw [Fin.sum_univ_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, dotProduct_add, zero_mul, zero_add]
    nlinarith [hcoverSlot, hparseSlot]

/-! ## Layer 6 — the residue closes the plane pair ceiling -/

/-- **THE THREE-ATOM RESIDUE CLOSES THE PLANE PAIR CEILING.** -/
theorem atomPairGramClosed_of_capTriple (htriple : PlaneCapTripleClosed) :
    AtomPairGramClosed := by
  classical
  intro atom scale axis haxis hplane hnonneg hsmall hframe
  by_contra hnone
  have hfail : ∀ slotOne slotTwo : Fin 6, slotOne ≠ slotTwo →
      0 < atom slotOne ⬝ᵥ atom slotOne - scale slotOne →
      (atom slotOne ⬝ᵥ atom slotOne - scale slotOne)
          * (atom slotTwo ⬝ᵥ atom slotTwo - scale slotTwo)
        ≤ (atom slotOne ⬝ᵥ atom slotTwo) ^ 2 := by
    intro slotOne slotTwo hne hpos
    by_contra hlt
    exact hnone ⟨slotOne, slotTwo, hne, hpos, lt_of_not_ge hlt⟩
  obtain ⟨first, second, hfirstAxis, hsecondAxis, hfirstEnergy, hsecondEnergy, hfirstSecond,
    hparse⟩ := exists_planeOrthoFrame axis haxis
  have hgapLe : ∀ slot : Fin 6,
      max (atom slot ⬝ᵥ atom slot - scale slot) 0 ≤ atom slot ⬝ᵥ atom slot :=
    fun slot => max_le (by linarith [hnonneg slot]) (dotProduct_self_nonneg (atom slot))
  have hpair : ∀ slotOne slotTwo : Fin 6,
      2 * (max (atom slotOne ⬝ᵥ atom slotOne - scale slotOne) 0)
          * (max (atom slotTwo ⬝ᵥ atom slotTwo - scale slotTwo) 0)
        - (atom slotOne ⬝ᵥ atom slotOne) * (atom slotTwo ⬝ᵥ atom slotTwo)
      ≤ doubleRead first second (atom slotOne) ⬝ᵥ doubleRead first second (atom slotTwo) := by
    intro slotOne slotTwo
    rw [doubleRead_dot hparse (atom slotOne) (atom slotTwo) (hplane slotOne) (hplane slotTwo)]
    have hkey : (max (atom slotOne ⬝ᵥ atom slotOne - scale slotOne) 0)
        * (max (atom slotTwo ⬝ᵥ atom slotTwo - scale slotTwo) 0)
        ≤ (atom slotOne ⬝ᵥ atom slotTwo) ^ 2 := by
      by_cases hsame : slotOne = slotTwo
      · subst hsame
        have hlow : (0 : ℝ) ≤ max (atom slotOne ⬝ᵥ atom slotOne - scale slotOne) 0 :=
          le_max_right _ _
        nlinarith [hgapLe slotOne, hlow]
      · rcases le_or_gt (atom slotOne ⬝ᵥ atom slotOne - scale slotOne) 0 with hone | hone
        · rw [max_eq_right hone, zero_mul]
          exact sq_nonneg _
        · rcases le_or_gt (atom slotTwo ⬝ᵥ atom slotTwo - scale slotTwo) 0 with htwo | htwo
          · rw [max_eq_right htwo, mul_zero]
            exact sq_nonneg _
          · rw [max_eq_left hone.le, max_eq_left htwo.le]
            exact hfail slotOne slotTwo hsame hone
    linarith
  obtain ⟨point, hdisc, hlevel⟩ :=
    exists_capPoint_of_triple (by norm_num) htriple
      (fun slot => doubleRead first second (atom slot))
      (fun slot => atom slot ⬝ᵥ atom slot)
      (fun slot => max (atom slot ⬝ᵥ atom slot - scale slot) 0)
      (fun slot => doubleRead_dot_self hparse (atom slot) (hplane slot))
      (fun slot => le_max_right _ _) hgapLe hpair
  refine false_of_capPoint atom scale axis first second haxis hplane hfirstAxis hsecondAxis
    hfirstEnergy hsecondEnergy hfirstSecond hparse hsmall hframe point fun slot => ?_
  have hmax : atom slot ⬝ᵥ atom slot - scale slot
      ≤ max (atom slot ⬝ᵥ atom slot - scale slot) 0 := le_max_left _ _
  have := hlevel slot
  linarith

/-! ## Layer 7 — the campaign consequences of the three-atom residue -/

/-- The plane pair ceiling from the three-atom residue. -/
theorem atomPairCeilingClosed_of_capTriple (htriple : PlaneCapTripleClosed) :
    AtomPairCeilingClosed :=
  atomPairCeilingClosed_of_gram (atomPairGramClosed_of_capTriple htriple)

/-- **DENSE PROFILE A AT RANK FIVE FROM THE THREE-ATOM RESIDUE.** -/
theorem rankFiveDenseHeavyFiveClosed_of_capTriple (htriple : PlaneCapTripleClosed) :
    RankFiveDenseHeavyFiveClosed :=
  rankFiveDenseHeavyFiveClosed_of_atomPairGram (atomPairGramClosed_of_capTriple htriple)

/-- The residual cycle cell of profile A from the three-atom residue. -/
theorem rankFiveDenseHeavyFiveDistinctClosed_of_capTriple (htriple : PlaneCapTripleClosed) :
    RankFiveDenseHeavyFiveDistinctClosed :=
  rankFiveDenseHeavyFiveDistinctClosed_of_atomPairGram (atomPairGramClosed_of_capTriple htriple)

/-- **THE THREE-ATOM RESIDUE MAKES EVERY CRUX INTERIOR.** -/
theorem SixThreeCrux.shifted_weight_pos_of_capTriple (crux : SixThreeCrux)
    (htriple : PlaneCapTripleClosed) (atomIndex : Fin 6) :
    0 < chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight atomIndex :=
  crux.shifted_weight_pos_of_atomPairCeiling (atomPairCeilingClosed_of_capTriple htriple)
    atomIndex

/-- The campaign-level interiority input, from the three-atom residue. -/
theorem forall_shifted_weight_pos_of_capTriple (htriple : PlaneCapTripleClosed) :
    ∀ (crux : SixThreeCrux) (atomIndex : Fin 6),
      0 < chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomIndex :=
  forall_shifted_weight_pos_of_atomPairGram (atomPairGramClosed_of_capTriple htriple)

/-- The boundary crux kill, from the three-atom residue. -/
theorem SixThreeCrux.false_of_capTriple_of_shift_zero (crux : SixThreeCrux)
    (htriple : PlaneCapTripleClosed) {boundary : Fin 6}
    (hzero : chartObjective (chartPointOfDesign crux.design)
      + (chartPointOfDesign crux.design).weight boundary = 0) :
    False :=
  crux.false_of_atomPairCeiling_of_shift_zero (atomPairCeilingClosed_of_capTriple htriple) hzero

/-! ## Layer 8 — unconditional strata of the three-atom residue -/

/-- **THE SHARP STRATUM.**  One atom whose gap is its whole energy pins the cap
point: the point is that reading, normalized.  The pair law at that atom IS the
domination, with no slack at all.

This is the sharp case of the plane residue.  The measured extremals of the dual
all carry such an atom. -/
theorem capPoint_of_full_gap {indexCount : ℕ} (read : Fin indexCount → (Fin 2 → ℝ))
    (energy gap : Fin indexCount → ℝ) (heavy : Fin indexCount)
    (henergy : ∀ index, read index ⬝ᵥ read index = energy index ^ 2)
    (hheavy : (0 : ℝ) < energy heavy) (hfull : gap heavy = energy heavy)
    (hpair : ∀ indexOne indexTwo,
      2 * gap indexOne * gap indexTwo - energy indexOne * energy indexTwo
        ≤ read indexOne ⬝ᵥ read indexTwo) :
    ∃ point : Fin 2 → ℝ, point ⬝ᵥ point ≤ 1
      ∧ ∀ index, 2 * gap index - energy index ≤ point ⬝ᵥ read index := by
  refine ⟨(energy heavy)⁻¹ • read heavy, ?_, fun index => ?_⟩
  · rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, henergy heavy]
    field_simp
    exact le_refl 1
  · rw [smul_dotProduct, smul_eq_mul]
    have hbound := hpair heavy index
    rw [hfull] at hbound
    have hkey : (2 * gap index - energy index) * energy heavy ≤ read heavy ⬝ᵥ read index := by
      nlinarith [hbound]
    rw [inv_mul_eq_div, le_div_iff₀ hheavy]
    exact hkey

/-- **THE LIGHT STRATUM.**  Every gap at most half its energy, and the origin is
the cap point.  The pair law is not necessary. -/
theorem capPoint_of_light {indexCount : ℕ} (read : Fin indexCount → (Fin 2 → ℝ))
    (energy gap : Fin indexCount → ℝ)
    (hlight : ∀ index, 2 * gap index ≤ energy index) :
    ∃ point : Fin 2 → ℝ, point ⬝ᵥ point ≤ 1
      ∧ ∀ index, 2 * gap index - energy index ≤ point ⬝ᵥ read index := by
  refine ⟨0, ?_, fun index => ?_⟩
  · rw [dot_fin_two]; norm_num
  · rw [zero_dotProduct]
    linarith [hlight index]

/-- **THE COVER STRATUM.**  One reading that already dominates every level, once
normalized, supplies the cap point outright. -/
theorem capPoint_of_cover {indexCount : ℕ} (read : Fin indexCount → (Fin 2 → ℝ))
    (energy gap : Fin indexCount → ℝ) (pivot : Fin indexCount)
    (henergy : read pivot ⬝ᵥ read pivot = energy pivot ^ 2)
    (hpivot : (0 : ℝ) < energy pivot)
    (hcover : ∀ index, (2 * gap index - energy index) * energy pivot
      ≤ read pivot ⬝ᵥ read index) :
    ∃ point : Fin 2 → ℝ, point ⬝ᵥ point ≤ 1
      ∧ ∀ index, 2 * gap index - energy index ≤ point ⬝ᵥ read index := by
  refine ⟨(energy pivot)⁻¹ • read pivot, ?_, fun index => ?_⟩
  · rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, henergy]
    field_simp
    exact le_refl 1
  · rw [smul_dotProduct, smul_eq_mul, inv_mul_eq_div, le_div_iff₀ hpivot]
    exact hcover index

/-- **THE TWO-ATOM CAP LAW.**  Two caps of the plane always meet.

The meeting point is a convex combination of the two readings, and the pair law
is exactly what makes the combination reach both levels.  Thus the plane residue
lives at three atoms and no fewer. -/
theorem exists_capPoint_of_pair (readOne readTwo : Fin 2 → ℝ) (levelOne levelTwo : ℝ)
    (hone : readOne ⬝ᵥ readOne = 1) (htwo : readTwo ⬝ᵥ readTwo = 1)
    (hlevelOne : levelOne ≤ 1) (hlevelTwo : levelTwo ≤ 1)
    (hpair : (1 + levelOne) * (1 + levelTwo) ≤ 2 * (1 + readOne ⬝ᵥ readTwo)) :
    ∃ point : Fin 2 → ℝ, point ⬝ᵥ point ≤ 1
      ∧ levelOne ≤ point ⬝ᵥ readOne ∧ levelTwo ≤ point ⬝ᵥ readTwo := by
  classical
  have hcross : readOne ⬝ᵥ readTwo ≤ 1 := by
    rw [dot_fin_two] at hone htwo ⊢
    nlinarith [sq_nonneg (readOne 0 - readTwo 0), sq_nonneg (readOne 1 - readTwo 1)]
  rcases le_or_gt 1 (readOne ⬝ᵥ readTwo) with hfull | hlt
  · refine ⟨readOne, by rw [hone], by rw [hone]; exact hlevelOne, ?_⟩
    linarith
  rcases le_or_gt levelOne (readOne ⬝ᵥ readTwo) with hsmall | hbig
  · refine ⟨readTwo, by rw [htwo], ?_, by rw [htwo]; exact hlevelTwo⟩
    rw [dotProduct_comm]
    exact hsmall
  -- the share that puts the first level exactly on the boundary
  set share : ℝ := (levelOne - readOne ⬝ᵥ readTwo) / (1 - readOne ⬝ᵥ readTwo) with hshareDef
  have hgap : (0 : ℝ) < 1 - readOne ⬝ᵥ readTwo := by linarith
  have hshareNonneg : (0 : ℝ) ≤ share := by
    rw [hshareDef]
    exact div_nonneg (by linarith) hgap.le
  have hshareLe : share ≤ 1 := by
    rw [hshareDef, div_le_one hgap]
    linarith
  have hshareMul : share * (1 - readOne ⬝ᵥ readTwo) = levelOne - readOne ⬝ᵥ readTwo := by
    rw [hshareDef]
    field_simp
  have hexpand : (share • readOne + (1 - share) • readTwo)
        ⬝ᵥ (share • readOne + (1 - share) • readTwo)
      = share ^ 2 * (readOne ⬝ᵥ readOne)
        + 2 * share * (1 - share) * (readOne ⬝ᵥ readTwo)
        + (1 - share) ^ 2 * (readTwo ⬝ᵥ readTwo) := by
    rw [dot_fin_two, dot_fin_two, dot_fin_two, dot_fin_two]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hprojOne : (share • readOne + (1 - share) • readTwo) ⬝ᵥ readOne
      = share * (readOne ⬝ᵥ readOne) + (1 - share) * (readTwo ⬝ᵥ readOne) := by
    rw [add_dotProduct, smul_dotProduct, smul_dotProduct]
    simp only [smul_eq_mul]
  have hprojTwo : (share • readOne + (1 - share) • readTwo) ⬝ᵥ readTwo
      = share * (readOne ⬝ᵥ readTwo) + (1 - share) * (readTwo ⬝ᵥ readTwo) := by
    rw [add_dotProduct, smul_dotProduct, smul_dotProduct]
    simp only [smul_eq_mul]
  refine ⟨share • readOne + (1 - share) • readTwo, ?_, ?_, ?_⟩
  · rw [hexpand, hone, htwo]
    nlinarith [mul_nonneg hshareNonneg (by linarith : (0 : ℝ) ≤ 1 - share), hcross]
  · rw [hprojOne, hone, dotProduct_comm readTwo readOne]
    nlinarith [hshareMul]
  · rw [hprojTwo, htwo]
    nlinarith [hshareMul, hpair]

end Gtz
