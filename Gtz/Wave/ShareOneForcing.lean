/-
# The share-one boundary of a rank-three tie

`Gtz.atomShare_lt_one_of_stressFree` caps every share of a branch-(i) design
strictly below one.  This module reads the same boundary from the TIE side and
finds that the cap needs no stress at all.

## What is proved

* A rank-three design with a share of exactly one carries a STRICTLY dominating
  triple (`exists_posDef_triple_of_atomShare_eq_one`).  A share of one splits
  the space: the atom is orthogonal to all the others, so the others live in its
  orthogonal plane, and rank-two GTZ (`Gtz.gtz_rank_two`, a theorem) covers that
  plane with a pair.  A deflation of the plane design by the share-one label's
  own weight turns the covering into a strict one.
* Hence `atomShare_lt_one_of_isTie`: EVERY share of a rank-three tie is strictly
  below one, at every size, with or without a stress.

## The consequence for the forcing route

The statement "a stress-free `(6,3)` tie forces some atom share to equal one"
has a consequent that is never true.  `atomShare_lt_one_of_stressFree` already
refutes it on the stratum, and `atomShare_lt_one_of_isTie` refutes it again from
the tie alone.  An implication whose consequent is always false is exactly the
negation of its antecedent, so the forcing statement IS branch (i), letter for
letter (`shareOneForcing_iff_stressFreeSixThreeTieFree`).  It is a restatement of the
target and not a route to it.

## The heavy floor

The landed balance law `Gtz.posDef_subsetSum_compl_of_baseShare_lt` gives a
second reading of the same boundary.  A rank-three design whose light labels
(leverage at most one) are all outside a fixed pair or larger set has a strictly
dominating complement.  So a rank-three tie carries at least FOUR labels of
leverage above one (`four_le_card_heavySet_of_isTie`), one more than the
unconditional three of `Gtz.three_le_card_heavySet`.  The regular tetrahedron
attains four, so the floor is sharp.

## Honest scope

Nothing here decides branch (i).  The share cap on the stress-free stratum is
not uniform: `Gtz/Wave/ShareOneForcingWitness.lean` exhibits stress-free `(6,3)`
designs of share arbitrarily near one.  Whether the cap is uniform on the TIE
sub-stratum is open, and no statement below claims it.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Core.Sanity
import Gtz.Design.ComplementLeverageLaw
import Gtz.Design.InPlaneRestriction
import Gtz.Design.LivePairExistence
import Gtz.Design.StressFreeClosureFailure
import Gtz.Design.UThreeSixDisjunction
import Gtz.Reduction.RayleighCertificate
import Gtz.Reduction.Reductions
import Gtz.Wave.ShareOneForcingConic
import Gtz.Wave.VeroneseWeightElimination

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace Gtz

open Finset Matrix

variable {size : ℕ}

/-! ## Part 1: an orthonormal frame of a plane -/

/-- The unit vector along a nonzero vector. -/
noncomputable def unitize (vector : Fin 3 → ℝ) : Fin 3 → ℝ :=
  (Real.sqrt (vector ⬝ᵥ vector))⁻¹ • vector

theorem unitize_dotProduct_self {vector : Fin 3 → ℝ} (hne : vector ≠ 0) :
    unitize vector ⬝ᵥ unitize vector = 1 := by
  have hpos : 0 < vector ⬝ᵥ vector := dotProduct_self_pos hne
  have hsq : Real.sqrt (vector ⬝ᵥ vector) ^ 2 = vector ⬝ᵥ vector := Real.sq_sqrt hpos.le
  have hsqrtNe : Real.sqrt (vector ⬝ᵥ vector) ≠ 0 := by
    intro hzero
    rw [hzero] at hsq
    simp at hsq
    exact absurd hsq.symm (ne_of_gt hpos)
  rw [unitize, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul]
  field_simp
  nlinarith [hsq]

theorem dotProduct_unitize (left right : Fin 3 → ℝ) :
    left ⬝ᵥ unitize right = (Real.sqrt (right ⬝ᵥ right))⁻¹ * (left ⬝ᵥ right) := by
  rw [unitize, dotProduct_smul, smul_eq_mul]

theorem smul_unitize_dotProduct {vector : Fin 3 → ℝ} (hne : vector ≠ 0) (probe : Fin 3 → ℝ) :
    (probe ⬝ᵥ unitize vector) • unitize vector
      = ((probe ⬝ᵥ vector) / (vector ⬝ᵥ vector)) • vector := by
  have hpos : 0 < vector ⬝ᵥ vector := dotProduct_self_pos hne
  have hsq : Real.sqrt (vector ⬝ᵥ vector) ^ 2 = vector ⬝ᵥ vector := Real.sq_sqrt hpos.le
  have hsqrtNe : Real.sqrt (vector ⬝ᵥ vector) ≠ 0 := by
    intro hzero
    rw [hzero] at hsq
    simp at hsq
    exact absurd hsq.symm (ne_of_gt hpos)
  rw [dotProduct_unitize, unitize, smul_smul]
  congr 1
  field_simp
  rw [hsq]
  ring

theorem unitize_ne_zero {vector : Fin 3 → ℝ} (hne : vector ≠ 0) : unitize vector ≠ 0 := by
  intro hzero
  have hself := unitize_dotProduct_self hne
  rw [hzero] at hself
  simp at hself

/-- The first frame vector of the plane orthogonal to a direction. -/
noncomputable def planeFirst (base : Fin 3 → ℝ) : Fin 3 → ℝ :=
  unitize (perpWitness base)

/-- The second frame vector of the plane orthogonal to a direction. -/
noncomputable def planeSecond (base : Fin 3 → ℝ) : Fin 3 → ℝ :=
  unitize (crossProduct base (perpWitness base))

theorem cross_ne_zero_of_ne_zero {base : Fin 3 → ℝ} (hbase : base ≠ 0) :
    crossProduct base (perpWitness base) ≠ 0 := by
  intro hzero
  have hnorm := cross_dot_cross base (perpWitness base) base (perpWitness base)
  rw [hzero] at hnorm
  have hperp : perpWitness base ⬝ᵥ base = 0 := perpWitness_dotProduct base
  have hperp' : base ⬝ᵥ perpWitness base = 0 := by rw [dotProduct_comm]; exact hperp
  rw [hperp'] at hnorm
  have hbasePos : 0 < base ⬝ᵥ base := dotProduct_self_pos hbase
  have hwitPos : 0 < perpWitness base ⬝ᵥ perpWitness base :=
    dotProduct_self_pos (perpWitness_ne_zero base)
  simp only [zero_dotProduct] at hnorm
  nlinarith [hnorm, hbasePos, hwitPos]

theorem planeFirst_dotProduct_self (base : Fin 3 → ℝ) :
    planeFirst base ⬝ᵥ planeFirst base = 1 :=
  unitize_dotProduct_self (perpWitness_ne_zero base)

theorem planeSecond_dotProduct_self {base : Fin 3 → ℝ} (hbase : base ≠ 0) :
    planeSecond base ⬝ᵥ planeSecond base = 1 :=
  unitize_dotProduct_self (cross_ne_zero_of_ne_zero hbase)

theorem base_dotProduct_planeFirst (base : Fin 3 → ℝ) : base ⬝ᵥ planeFirst base = 0 := by
  rw [planeFirst, dotProduct_unitize]
  have hperp : perpWitness base ⬝ᵥ base = 0 := perpWitness_dotProduct base
  rw [dotProduct_comm base, hperp, mul_zero]

theorem base_dotProduct_planeSecond (base : Fin 3 → ℝ) : base ⬝ᵥ planeSecond base = 0 := by
  rw [planeSecond, dotProduct_unitize, dot_self_cross, mul_zero]

theorem planeFirst_dotProduct_planeSecond (base : Fin 3 → ℝ) :
    planeFirst base ⬝ᵥ planeSecond base = 0 := by
  rw [planeFirst, planeSecond, dotProduct_unitize, unitize, smul_dotProduct, smul_eq_mul,
    dot_cross_self, mul_zero, mul_zero]

/-! ## Part 2: the orthogonal expansion in the frame -/

/-- **THE ORTHOGONAL BASIS IDENTITY.**  A direction, a vector orthogonal to it
and their cross product expand every probe.  The only hypothesis is the
orthogonality of the first two, and the identity is division free. -/
theorem smul_eq_orthogonalTriple_expansion (base perp probe : Fin 3 → ℝ)
    (horth : base ⬝ᵥ perp = 0) :
    ((base ⬝ᵥ base) * (perp ⬝ᵥ perp)) • probe
      = ((perp ⬝ᵥ perp) * (probe ⬝ᵥ base)) • base
        + ((base ⬝ᵥ base) * (probe ⬝ᵥ perp)) • perp
        + (probe ⬝ᵥ crossProduct base perp) • crossProduct base perp := by
  have horth' : base 0 * perp 0 + base 1 * perp 1 + base 2 * perp 2 = 0 := by
    simpa [dotProduct, Fin.sum_univ_three] using horth
  funext coord
  fin_cases coord
  · simp [dotProduct, Fin.sum_univ_three, cross_apply]
    linear_combination ((base 0 * perp 0 + base 1 * perp 1 + base 2 * perp 2) * probe 0
      - (probe 0 * perp 0 + probe 1 * perp 1 + probe 2 * perp 2) * base 0
      - (probe 0 * base 0 + probe 1 * base 1 + probe 2 * base 2) * perp 0) * horth'
  · simp [dotProduct, Fin.sum_univ_three, cross_apply]
    linear_combination ((base 0 * perp 0 + base 1 * perp 1 + base 2 * perp 2) * probe 1
      - (probe 0 * perp 0 + probe 1 * perp 1 + probe 2 * perp 2) * base 1
      - (probe 0 * base 0 + probe 1 * base 1 + probe 2 * base 2) * perp 1) * horth'
  · simp [dotProduct, Fin.sum_univ_three, cross_apply]
    linear_combination ((base 0 * perp 0 + base 1 * perp 1 + base 2 * perp 2) * probe 2
      - (probe 0 * perp 0 + probe 1 * perp 1 + probe 2 * perp 2) * base 2
      - (probe 0 * base 0 + probe 1 * base 1 + probe 2 * base 2) * perp 2) * horth'

theorem cross_dotProduct_self_of_perpWitness (base : Fin 3 → ℝ) :
    crossProduct base (perpWitness base) ⬝ᵥ crossProduct base (perpWitness base)
      = (base ⬝ᵥ base) * (perpWitness base ⬝ᵥ perpWitness base) := by
  have horth : base ⬝ᵥ perpWitness base = 0 := by
    rw [dotProduct_comm]; exact perpWitness_dotProduct base
  rw [cross_dot_cross, horth]
  ring

/-- **THE FRAME EXPANSION.**  A direction and the two frame vectors of its
orthogonal plane resolve every probe.  The first coefficient is the Rayleigh
ratio along the direction and the other two are the frame readings. -/
theorem frame_expansion {base : Fin 3 → ℝ} (hbase : base ≠ 0) (probe : Fin 3 → ℝ) :
    probe = ((probe ⬝ᵥ base) / (base ⬝ᵥ base)) • base
      + (probe ⬝ᵥ planeFirst base) • planeFirst base
      + (probe ⬝ᵥ planeSecond base) • planeSecond base := by
  have horth : base ⬝ᵥ perpWitness base = 0 := by
    rw [dotProduct_comm]; exact perpWitness_dotProduct base
  have hbasePos : (0 : ℝ) < base ⬝ᵥ base := dotProduct_self_pos hbase
  have hperpPos : (0 : ℝ) < perpWitness base ⬝ᵥ perpWitness base :=
    dotProduct_self_pos (perpWitness_ne_zero base)
  have hcross := cross_dotProduct_self_of_perpWitness base
  rw [planeFirst, planeSecond, smul_unitize_dotProduct (perpWitness_ne_zero base),
    smul_unitize_dotProduct (cross_ne_zero_of_ne_zero hbase), hcross]
  funext coord
  have key := congrFun (smul_eq_orthogonalTriple_expansion base (perpWitness base) probe horth) coord
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at key ⊢
  field_simp
  linear_combination key

/-- Every pairing reads through the frame. -/
theorem dotProduct_frame_expansion {base : Fin 3 → ℝ} (hbase : base ≠ 0)
    (left probe : Fin 3 → ℝ) :
    left ⬝ᵥ probe = (probe ⬝ᵥ base) / (base ⬝ᵥ base) * (left ⬝ᵥ base)
      + (probe ⬝ᵥ planeFirst base) * (left ⬝ᵥ planeFirst base)
      + (probe ⬝ᵥ planeSecond base) * (left ⬝ᵥ planeSecond base) := by
  conv_lhs => rw [frame_expansion hbase probe]
  rw [dotProduct_add, dotProduct_add, dotProduct_smul, dotProduct_smul, dotProduct_smul,
    smul_eq_mul, smul_eq_mul, smul_eq_mul]

/-- Parseval in the frame: the squared length splits into the squared Rayleigh
ratio along the direction and the two squared frame readings. -/
theorem frame_parseval {base : Fin 3 → ℝ} (hbase : base ≠ 0) (probe : Fin 3 → ℝ) :
    probe ⬝ᵥ probe = (probe ⬝ᵥ base) ^ 2 / (base ⬝ᵥ base)
      + (probe ⬝ᵥ planeFirst base) ^ 2 + (probe ⬝ᵥ planeSecond base) ^ 2 := by
  have hbasePos : (0 : ℝ) < base ⬝ᵥ base := dotProduct_self_pos hbase
  have hexp := dotProduct_frame_expansion hbase probe probe
  rw [hexp]
  field_simp

/-- A vector orthogonal to the direction pairs with every probe through the frame
readings alone. -/
theorem frame_inPlane_pairing {base : Fin 3 → ℝ} (hbase : base ≠ 0) {inPlane : Fin 3 → ℝ}
    (hinPlane : inPlane ⬝ᵥ base = 0) (probe : Fin 3 → ℝ) :
    inPlane ⬝ᵥ probe
      = (inPlane ⬝ᵥ planeFirst base) * (probe ⬝ᵥ planeFirst base)
        + (inPlane ⬝ᵥ planeSecond base) * (probe ⬝ᵥ planeSecond base) := by
  rw [dotProduct_frame_expansion hbase inPlane probe, hinPlane]
  ring

/-! ## Part 3: the deflation of a rank-two design at a vanishing atom -/

/-- The deflation scale: the factor by which a covering pair of the deflated
design overshoots the identity on the original one. -/
noncomputable def deflationScale (design : WeightedDesign size 2) (label : Fin size) : ℝ :=
  (1 - design.weight label) / (1 - design.weight label / 2)

theorem deflationScale_pos (design : WeightedDesign size 2) (hsize : 2 ≤ size)
    (label : Fin size) : 0 < deflationScale design label := by
  have hlt : design.weight label < 1 := weight_lt_one design hsize label
  have hpos : 0 < design.weight label := design.weight_pos label
  rw [deflationScale]
  exact div_pos (by linarith) (by linarith)

theorem deflationScale_lt_one (design : WeightedDesign size 2) (hsize : 2 ≤ size)
    (label : Fin size) : deflationScale design label < 1 := by
  have hlt : design.weight label < 1 := weight_lt_one design hsize label
  have hpos : 0 < design.weight label := design.weight_pos label
  rw [deflationScale, div_lt_one (by linarith)]
  linarith

/-- **THE DEFLATION AT A VANISHING ATOM.**  A rank-two design with a zero atom
carries a second design on the same directions.  The zero atom keeps half of its
weight and the rest redistributes, so the atoms shrink by the deflation scale. -/
noncomputable def deflateAtZeroAtom (design : WeightedDesign size 2) (label : Fin size)
    (hsize : 2 ≤ size) (hzero : design.atom label = 0) : WeightedDesign size 2 where
  atom := fun other => Real.sqrt (deflationScale design label) • design.atom other
  weight := fun other =>
    if other = label then design.weight label / 2
    else (1 - design.weight label / 2) * design.weight other / (1 - design.weight label)
  weight_pos := by
    intro other
    have hlt : design.weight label < 1 := weight_lt_one design hsize label
    have hpos : 0 < design.weight label := design.weight_pos label
    split_ifs with hother
    · linarith
    · exact div_pos (mul_pos (by linarith) (design.weight_pos other)) (by linarith)
  weight_sum_one := by
    have hlt : design.weight label < 1 := weight_lt_one design hsize label
    have hne : (1 : ℝ) - design.weight label ≠ 0 := by linarith
    have hsplit := Finset.add_sum_erase Finset.univ design.weight (Finset.mem_univ label)
    rw [design.weight_sum_one] at hsplit
    have hrest : ∑ other ∈ Finset.univ.erase label, design.weight other
        = 1 - design.weight label := by linarith
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ label)]
    simp only [↓reduceIte]
    have hterm : ∀ other ∈ Finset.univ.erase label,
        (if other = label then design.weight label / 2
          else (1 - design.weight label / 2) * design.weight other / (1 - design.weight label))
          = (1 - design.weight label / 2) / (1 - design.weight label) * design.weight other := by
      intro other hother
      rw [ite_eq_right_of_eq_false _ _ (eq_false (Finset.mem_erase.mp hother).1)]
      ring
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, hrest, div_mul_cancel₀ _ hne]
    ring
  isParseval := by
    have hscale : Real.sqrt (deflationScale design label) ^ 2 = deflationScale design label :=
      Real.sq_sqrt (deflationScale_pos design hsize label).le
    have hpos : 0 < design.weight label := design.weight_pos label
    have hlt : design.weight label < 1 := weight_lt_one design hsize label
    have hne : (1 : ℝ) - design.weight label ≠ 0 := by linarith
    have hneHalf : (1 : ℝ) - design.weight label / 2 ≠ 0 := by linarith
    have hneTwo : (2 : ℝ) - design.weight label ≠ 0 := by linarith
    have hterm : ∀ other : Fin size,
        (if other = label then design.weight label / 2
          else (1 - design.weight label / 2) * design.weight other / (1 - design.weight label))
            • atomMatrix (Real.sqrt (deflationScale design label) • design.atom other)
          = design.weight other • atomMatrix (design.atom other) := by
      intro other
      rw [atomMatrix_smul, hscale, smul_smul]
      by_cases hother : other = label
      · subst hother
        rw [hzero]
        simp [atomMatrix]
      · rw [ite_eq_right_of_eq_false _ _ (eq_false hother)]
        congr 1
        rw [deflationScale]
        field_simp
    rw [Finset.sum_congr rfl fun other _ => hterm other, design.isParseval]

/-- **THE DEFLATED COVERING OVERSHOOTS.**  A dominating subset of the deflated
design covers the original with the deflation scale to spare, and that scale is
strictly below one. -/
theorem dotProduct_self_le_deflationScale_mul_sum (design : WeightedDesign size 2)
    (label : Fin size) (hsize : 2 ≤ size) (hzero : design.atom label = 0)
    (selected : Finset (Fin size))
    (hdom : Dominates (deflateAtZeroAtom design label hsize hzero) selected)
    (probe : Fin 2 → ℝ) :
    probe ⬝ᵥ probe
      ≤ deflationScale design label * ∑ other ∈ selected, (design.atom other ⬝ᵥ probe) ^ 2 := by
  have hscale : Real.sqrt (deflationScale design label) ^ 2 = deflationScale design label :=
    Real.sq_sqrt (deflationScale_pos design hsize label).le
  have hform := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hdom).2 probe
  rw [star_trivial, dominationGap_form] at hform
  have hreading : ∀ other : Fin size,
      ((deflateAtZeroAtom design label hsize hzero).atom other ⬝ᵥ probe) ^ 2
        = deflationScale design label * (design.atom other ⬝ᵥ probe) ^ 2 := by
    intro other
    show (Real.sqrt (deflationScale design label) • design.atom other ⬝ᵥ probe) ^ 2 = _
    rw [smul_dotProduct, smul_eq_mul, mul_pow, hscale]
  rw [Finset.sum_congr rfl fun other _ => hreading other, ← Finset.mul_sum] at hform
  linarith

/-! ## Part 4: a share of one produces a strictly dominating triple -/

theorem leverageOf_pos_of_atomShare_eq_one (design : WeightedDesign size 3) (label : Fin size)
    (hshare : atomShare design label = 1) : 0 < leverageOf (design.atom label) := by
  rcases lt_or_eq_of_le (leverageOf_nonneg (design.atom label)) with hpos | hzero
  · exact hpos
  · rw [atomShare, ← hzero, mul_zero] at hshare
    norm_num at hshare

theorem one_lt_leverageOf_of_atomShare_eq_one (design : WeightedDesign size 3) (hsize : 2 ≤ size)
    (label : Fin size) (hshare : atomShare design label = 1) :
    1 < leverageOf (design.atom label) := by
  have hpos := design.weight_pos label
  have hlt := weight_lt_one design hsize label
  rw [atomShare] at hshare
  nlinarith [hshare, hpos, hlt, leverageOf_nonneg (design.atom label)]

/-- **A SHARE OF ONE IS A STRICT DOMINATOR.**  An atom of share one is orthogonal
to every other atom, so the others live in its orthogonal plane.  Rank-two GTZ
covers that plane with a pair, and the deflation by the share-one label's own
weight turns the covering strict.  The share-one atom then supplies the missing
direction with its leverage to spare. -/
theorem exists_posDef_triple_of_atomShare_eq_one (design : WeightedDesign size 3)
    (label : Fin size) (hshare : atomShare design label = 1) :
    ∃ triple : Finset (Fin size), triple.card = 3 ∧ (subsetSum design triple - 1).PosDef := by
  classical
  have hsize3 : 3 ≤ size := rank_le_of_design design
  have hsize : 2 ≤ size := by omega
  have hlev : 0 < leverageOf (design.atom label) :=
    leverageOf_pos_of_atomShare_eq_one design label hshare
  have hbase : design.atom label ≠ 0 := by
    intro hzero
    rw [hzero] at hlev
    simp [leverageOf] at hlev
  have honeLt : 1 < leverageOf (design.atom label) :=
    one_lt_leverageOf_of_atomShare_eq_one design hsize label hshare
  have horth := (atomShare_eq_one_iff_forall_dotProduct_eq_zero design label hlev).mp hshare
  have hfirstUnit : planeFirst (design.atom label) ⬝ᵥ planeFirst (design.atom label) = 1 :=
    planeFirst_dotProduct_self (design.atom label)
  have hsecondUnit : planeSecond (design.atom label) ⬝ᵥ planeSecond (design.atom label) = 1 :=
    planeSecond_dotProduct_self hbase
  have hframeOrth : planeFirst (design.atom label) ⬝ᵥ planeSecond (design.atom label) = 0 :=
    planeFirst_dotProduct_planeSecond (design.atom label)
  set plane := inPlaneRestriction design (planeFirst (design.atom label))
    (planeSecond (design.atom label)) hfirstUnit hsecondUnit hframeOrth with hplaneDef
  have hplaneAtom : ∀ other : Fin size, plane.atom other
      = ![design.atom other ⬝ᵥ planeFirst (design.atom label),
          design.atom other ⬝ᵥ planeSecond (design.atom label)] := fun _ => rfl
  have hplaneZero : plane.atom label = 0 := by
    rw [hplaneAtom, base_dotProduct_planeFirst, base_dotProduct_planeSecond]
    funext coord
    fin_cases coord <;> simp
  obtain ⟨pair, hcard, hdom⟩ := gtz_rank_two size (deflateAtZeroAtom plane label hsize hplaneZero)
  obtain ⟨first, second, hne, hpairEq⟩ := Finset.card_eq_two.mp hcard
  have hcover : ∀ probe : Fin 2 → ℝ, probe ⬝ᵥ probe
      ≤ deflationScale plane label
        * ((plane.atom first ⬝ᵥ probe) ^ 2 + (plane.atom second ⬝ᵥ probe) ^ 2) := by
    intro probe
    have hraw := dotProduct_self_le_deflationScale_mul_sum plane label hsize hplaneZero pair
      hdom probe
    rwa [hpairEq, Finset.sum_insert (by simp [hne]), Finset.sum_singleton] at hraw
  have hscalePos : 0 < deflationScale plane label := deflationScale_pos plane hsize label
  have hscaleLt : deflationScale plane label < 1 := deflationScale_lt_one plane hsize label
  have hkill : ∀ survivor : Fin size,
      (∀ probe : Fin 2 → ℝ, probe ⬝ᵥ probe
        ≤ deflationScale plane label * (plane.atom survivor ⬝ᵥ probe) ^ 2) → False := by
    intro survivor hbad
    have hperp := hbad ![-(plane.atom survivor 1), plane.atom survivor 0]
    simp only [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at hperp
    have hzeroFirst : plane.atom survivor 0 * plane.atom survivor 0 = 0 := by
      nlinarith [hperp, mul_self_nonneg (plane.atom survivor 0),
        mul_self_nonneg (plane.atom survivor 1)]
    have hzeroSecond : plane.atom survivor 1 * plane.atom survivor 1 = 0 := by
      nlinarith [hperp, mul_self_nonneg (plane.atom survivor 0),
        mul_self_nonneg (plane.atom survivor 1)]
    have hunit := hbad ![1, 0]
    simp only [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at hunit
    nlinarith [hunit, hzeroFirst, hzeroSecond, hscalePos,
      mul_self_eq_zero.mp hzeroFirst, mul_self_eq_zero.mp hzeroSecond]
  have hnotMem : label ∉ pair := by
    rw [hpairEq]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro (hleft | hright)
    · refine hkill second fun probe => ?_
      have hraw := hcover probe
      rw [← hleft, hplaneZero] at hraw
      simp only [zero_dotProduct] at hraw
      nlinarith [hraw]
    · refine hkill first fun probe => ?_
      have hraw := hcover probe
      rw [← hright, hplaneZero] at hraw
      simp only [zero_dotProduct] at hraw
      nlinarith [hraw]
  have hfirstNe : first ≠ label := by
    intro heq
    exact hnotMem (by rw [hpairEq, ← heq]; exact Finset.mem_insert_self _ _)
  have hsecondNe : second ≠ label := by
    intro heq
    exact hnotMem (by rw [hpairEq, ← heq]; simp)
  refine ⟨insert label pair, by rw [Finset.card_insert_of_notMem hnotMem, hcard],
    Matrix.posDef_iff_dotProduct_mulVec.mpr
      ⟨isHermitian_designGap design (insert label pair), ?_⟩⟩
  · intro probe hprobe
    rw [star_trivial, dominationGap_form, Finset.sum_insert hnotMem, hpairEq,
      Finset.sum_insert (by simp [hne]), Finset.sum_singleton]
    have hplaneRead : ∀ other : Fin size, other ≠ label →
        design.atom other ⬝ᵥ probe
          = plane.atom other ⬝ᵥ ![probe ⬝ᵥ planeFirst (design.atom label),
              probe ⬝ᵥ planeSecond (design.atom label)] := by
      intro other hother
      rw [hplaneAtom]
      simp only [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
      exact frame_inPlane_pairing hbase (horth other hother) probe
    have hpar := frame_parseval hbase probe
    have hbb : (0 : ℝ) < design.atom label ⬝ᵥ design.atom label := dotProduct_self_pos hbase
    have hbbNe : design.atom label ⬝ᵥ design.atom label ≠ 0 := ne_of_gt hbb
    have hbbOne : (1 : ℝ) < design.atom label ⬝ᵥ design.atom label := by
      rw [← leverageOf_eq_dotProduct_self]; exact honeLt
    have hparMul : (design.atom label ⬝ᵥ design.atom label) * (probe ⬝ᵥ probe)
        = (probe ⬝ᵥ design.atom label) ^ 2
          + (design.atom label ⬝ᵥ design.atom label)
            * ((probe ⬝ᵥ planeFirst (design.atom label)) ^ 2
              + (probe ⬝ᵥ planeSecond (design.atom label)) ^ 2) := by
      rw [hpar]
      field_simp
      ring
    have hcoverProbe := hcover ![probe ⬝ᵥ planeFirst (design.atom label),
      probe ⬝ᵥ planeSecond (design.atom label)]
    have hyy : (![probe ⬝ᵥ planeFirst (design.atom label),
          probe ⬝ᵥ planeSecond (design.atom label)] : Fin 2 → ℝ)
        ⬝ᵥ ![probe ⬝ᵥ planeFirst (design.atom label),
          probe ⬝ᵥ planeSecond (design.atom label)]
        = (probe ⬝ᵥ planeFirst (design.atom label)) ^ 2
          + (probe ⬝ᵥ planeSecond (design.atom label)) ^ 2 := by
      simp only [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
      ring
    rw [hyy] at hcoverProbe
    rw [hplaneRead first hfirstNe, hplaneRead second hsecondNe]
    have hprobePos : 0 < probe ⬝ᵥ probe := dotProduct_self_pos hprobe
    have hlabelRead : design.atom label ⬝ᵥ probe = probe ⬝ᵥ design.atom label := dotProduct_comm _ _
    rw [hlabelRead]
    set planeMass := (plane.atom first ⬝ᵥ ![probe ⬝ᵥ planeFirst (design.atom label),
        probe ⬝ᵥ planeSecond (design.atom label)]) ^ 2
      + (plane.atom second ⬝ᵥ ![probe ⬝ᵥ planeFirst (design.atom label),
        probe ⬝ᵥ planeSecond (design.atom label)]) ^ 2 with hplaneMass
    set frameMass := (probe ⬝ᵥ planeFirst (design.atom label)) ^ 2
      + (probe ⬝ᵥ planeSecond (design.atom label)) ^ 2 with hframeMass
    have hplaneMassNonneg : 0 ≤ planeMass := by
      rw [hplaneMass]; positivity
    have hframeLe : frameMass ≤ planeMass := by
      nlinarith [hcoverProbe, hplaneMassNonneg, hscaleLt, hscalePos]
    rcases eq_or_lt_of_le (sq_nonneg (probe ⬝ᵥ design.atom label)) with haxis | haxis
    · have hcancel : (design.atom label ⬝ᵥ design.atom label) * (probe ⬝ᵥ probe)
          = (design.atom label ⬝ᵥ design.atom label) * frameMass := by linarith [hparMul]
      have hprobeEq : probe ⬝ᵥ probe = frameMass := mul_left_cancel₀ hbbNe hcancel
      have hframePos : 0 < frameMass := by linarith [hprobePos, hprobeEq]
      have hstrict : frameMass < planeMass := by
        nlinarith [hcoverProbe, hscaleLt, hscalePos, hframePos, hplaneMassNonneg]
      linarith [hprobeEq, hstrict, haxis]
    · nlinarith [hparMul, hframeLe, hbb, hbbOne, haxis, hprobePos]

/-! ## Part 5: the share cap of a tie -/

/-- **A SHARE OF ONE IS INCOMPATIBLE WITH A TIE.**  No stress hypothesis is used. -/
theorem not_isTie_of_atomShare_eq_one (design : WeightedDesign size 3) (label : Fin size)
    (hshare : atomShare design label = 1) : ¬ IsTie design := by
  intro htie
  obtain ⟨triple, hcard, hposDef⟩ := exists_posDef_triple_of_atomShare_eq_one design label hshare
  exact htie.2 triple hcard hposDef

/-- **EVERY SHARE OF A RANK-THREE TIE IS STRICTLY BELOW ONE.**  This is the tie
counterpart of `Gtz.atomShare_lt_one_of_stressFree`, at every size and with no
stress hypothesis at all. -/
theorem atomShare_lt_one_of_isTie (design : WeightedDesign size 3) (htie : IsTie design)
    (label : Fin size) : atomShare design label < 1 := by
  rcases lt_or_eq_of_le (atomShare_le_one_ofAnyRank design label) with hlt | heq
  · exact hlt
  · exact absurd htie (not_isTie_of_atomShare_eq_one design label heq)

theorem not_exists_atomShare_eq_one_of_isTie (design : WeightedDesign size 3)
    (htie : IsTie design) : ¬ ∃ label, atomShare design label = 1 := by
  rintro ⟨label, hlabel⟩
  exact not_isTie_of_atomShare_eq_one design label hlabel htie

/-- **NO ATOM OF A TIE IS ORTHOGONAL TO ALL THE OTHERS.**  The share defect of
`Gtz.leverage_mul_one_sub_atomShare` is the weighted mean square correlation of
one atom with the rest, and the strict cap makes it positive. -/
theorem sum_weight_mul_sq_dotProduct_pos_of_isTie (design : WeightedDesign size 3)
    (htie : IsTie design) (label : Fin size) (hlev : 0 < leverageOf (design.atom label)) :
    0 < ∑ other ∈ Finset.univ.erase label,
      design.weight other * (design.atom other ⬝ᵥ design.atom label) ^ 2 := by
  have hdefect := leverage_mul_one_sub_atomShare design label
  have hshare := atomShare_lt_one_of_isTie design htie label
  nlinarith [hdefect, hshare, hlev]

theorem exists_ne_dotProduct_ne_zero_of_isTie (design : WeightedDesign size 3)
    (htie : IsTie design) (label : Fin size) (hlev : 0 < leverageOf (design.atom label)) :
    ∃ other, other ≠ label ∧ design.atom other ⬝ᵥ design.atom label ≠ 0 := by
  classical
  by_contra hcontra
  push Not at hcontra
  have hvanish : ∑ other ∈ Finset.univ.erase label,
      design.weight other * (design.atom other ⬝ᵥ design.atom label) ^ 2 = 0 := by
    refine Finset.sum_eq_zero fun other hother => ?_
    rw [hcontra other (Finset.mem_erase.mp hother).1]
    ring
  have hpos := sum_weight_mul_sq_dotProduct_pos_of_isTie design htie label hlev
  linarith

/-! ## Part 6: the forcing statement is branch (i) -/

/-- The forcing statement: a stress-free `(6,3)` tie carries a share of one. -/
def ShareOneForcing : Prop :=
  ∀ design : WeightedDesign 6 3,
    (∀ stressCoeff : Fin 6 → ℝ,
      (∑ atomIndex, stressCoeff atomIndex • atomMatrix (design.atom atomIndex)) = 0 →
        stressCoeff = 0) →
      IsTie design → ∃ label, atomShare design label = 1

/-- Branch (i) of `Gtz.sixThree_stress_trichotomy`, read as tie emptiness. -/
def StressFreeSixThreeTieFree : Prop :=
  ∀ design : WeightedDesign 6 3,
    (∀ stressCoeff : Fin 6 → ℝ,
      (∑ atomIndex, stressCoeff atomIndex • atomMatrix (design.atom atomIndex)) = 0 →
        stressCoeff = 0) →
      ¬ IsTie design

/-- **THE FORCING STATEMENT IS THE TARGET.**  Its consequent is false at every
design of the stratum (`Gtz.atomShare_lt_one_of_stressFree`) and false again at
every rank-three tie (`atomShare_lt_one_of_isTie`).  An implication with an
always-false consequent is the negation of its antecedent, so the forcing
statement and branch (i) are the same proposition.  A proof of the forcing
statement is a proof of branch (i) and nothing less. -/
theorem shareOneForcing_iff_stressFreeSixThreeTieFree :
    ShareOneForcing ↔ StressFreeSixThreeTieFree := by
  constructor
  · intro hforce design hstressFree htie
    obtain ⟨label, hlabel⟩ := hforce design hstressFree htie
    exact absurd hlabel (ne_of_lt (atomShare_lt_one_of_stressFree design hstressFree label))
  · intro hfree design hstressFree htie
    exact absurd htie (hfree design hstressFree)

/-- The same collapse from the tie side alone, with the stress hypothesis unused. -/
theorem shareOneForcing_of_stressFreeSixThreeTieFree_tieOnly :
    ShareOneForcing ↔ ∀ design : WeightedDesign 6 3,
      (∀ stressCoeff : Fin 6 → ℝ,
        (∑ atomIndex, stressCoeff atomIndex • atomMatrix (design.atom atomIndex)) = 0 →
          stressCoeff = 0) →
        ¬ IsTie design := by
  constructor
  · intro hforce design hstressFree htie
    obtain ⟨label, hlabel⟩ := hforce design hstressFree htie
    exact not_isTie_of_atomShare_eq_one design label hlabel htie
  · intro hfree design hstressFree htie
    exact absurd htie (hfree design hstressFree)

/-! ## Part 7: the heavy floor of a rank-three tie -/

/-- **A LIGHT COMPLEMENT DOMINATES STRICTLY.**  If every label outside a set of
two or more labels has leverage at most one, that set strictly dominates.  The
balance law `Gtz.posDef_subsetSum_compl_of_baseShare_lt` supplies the certificate
because a light label's share never exceeds its weight. -/
theorem posDef_subsetSum_of_forall_leverage_le_one (design : WeightedDesign size 3)
    (selected : Finset (Fin size)) (hcard : 2 ≤ selected.card)
    (hlight : ∀ label ∉ selected, leverageOf (design.atom label) ≤ 1) :
    (subsetSum design selected - 1).PosDef := by
  classical
  have hne : selected.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨pivot, hpivotMem, hpivotMax⟩ := Finset.exists_max_image selected design.weight hne
  have hmaxPos : 0 < design.weight pivot := design.weight_pos pivot
  have hbound : ∀ label ∈ (selectedᶜ)ᶜ, design.weight label ≤ design.weight pivot := by
    intro label hlabel
    rw [compl_compl] at hlabel
    exact hpivotMax label hlabel
  have hterm : ∀ label ∈ selectedᶜ, atomShare design label ≤ design.weight label := by
    intro label hlabel
    rw [atomShare]
    have hl := hlight label (Finset.mem_compl.mp hlabel)
    nlinarith [design.weight_pos label, hl]
  have hsum := Finset.sum_le_sum hterm
  have hsplit := Finset.sum_add_sum_compl selected design.weight
  rw [design.weight_sum_one] at hsplit
  have herase := Finset.add_sum_erase selected design.weight hpivotMem
  have hrestPos : 0 < ∑ label ∈ selected.erase pivot, design.weight label :=
    Finset.sum_pos (fun l _ => design.weight_pos l)
      (Finset.card_pos.mp (by rw [Finset.card_erase_of_mem hpivotMem]; omega))
  have hselected : design.weight pivot < ∑ label ∈ selected, design.weight label := by
    linarith
  have hshareBound : ∑ label ∈ selectedᶜ, atomShare design label < 1 - design.weight pivot := by
    linarith
  have hres := posDef_subsetSum_compl_of_baseShare_lt design selectedᶜ (design.weight pivot)
    hmaxPos hbound hshareBound
  rwa [compl_compl] at hres

theorem leverageOf_le_one_of_notMem_heavySet (design : WeightedDesign size 3)
    {label : Fin size} (hnotMem : label ∉ heavySet design) :
    leverageOf (design.atom label) ≤ 1 := by
  have hexcess : gapExcessOf design label ≤ 0 := by
    by_contra hcontra
    exact hnotMem ((mem_heavySet_iff design label).mpr (lt_of_not_ge hcontra))
  rw [gapExcessOf] at hexcess
  linarith

/-- **THE HEAVY FLOOR OF A RANK-THREE TIE.**  A tie carries at least FOUR labels
of leverage above one.  The unconditional floor is three
(`Gtz.three_le_card_heavySet`), and the regular tetrahedron attains four, so this
floor is sharp. -/
theorem four_le_card_heavySet_of_isTie (design : WeightedDesign size 3) (htie : IsTie design) :
    4 ≤ (heavySet design).card := by
  classical
  by_contra hcontra
  have hsize : 3 ≤ size := rank_le_of_design design
  have hle : (heavySet design).card ≤ 3 := by omega
  have hcardBound : 3 ≤ Fintype.card (Fin size) := by
    rw [Fintype.card_fin]; exact hsize
  obtain ⟨selected, hsubset, hselectedCard⟩ :=
    Finset.exists_superset_card_eq hle hcardBound
  have hlight : ∀ label ∉ selected, leverageOf (design.atom label) ≤ 1 := by
    intro label hlabel
    exact leverageOf_le_one_of_notMem_heavySet design fun hmem => hlabel (hsubset hmem)
  exact htie.2 selected hselectedCard
    (posDef_subsetSum_of_forall_leverage_le_one design selected (by omega) hlight)

/-! ## Part 8: the hyperplane no-go -/

/-- **AN ATOM THAT ALONE READS A DIRECTION HAS SHARE ONE.**  Parseval spends the
whole of a direction on the atoms that read it.  If only one atom reads it, the
Cauchy-Schwarz step is tight and the share is exactly one. -/
theorem atomShare_eq_one_of_forall_dotProduct_normal_eq_zero (design : WeightedDesign size 3)
    (label : Fin size) (normal : Fin 3 → ℝ) (hnormal : normal ≠ 0)
    (hflat : ∀ other, other ≠ label → design.atom other ⬝ᵥ normal = 0) :
    atomShare design label = 1 := by
  classical
  have hparseval := sum_weight_mul_sq_dotProduct_probe design normal
  rw [leverageOf_eq_dotProduct_self] at hparseval
  have hcollapse : ∑ atomIndex, design.weight atomIndex * (design.atom atomIndex ⬝ᵥ normal) ^ 2
      = design.weight label * (design.atom label ⬝ᵥ normal) ^ 2 := by
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ label)]
    have hzero : ∑ other ∈ Finset.univ.erase label,
        design.weight other * (design.atom other ⬝ᵥ normal) ^ 2 = 0 := by
      refine Finset.sum_eq_zero fun other hother => ?_
      rw [hflat other (Finset.mem_erase.mp hother).1]
      ring
    rw [hzero, add_zero]
  rw [hcollapse] at hparseval
  have hnormPos : 0 < normal ⬝ᵥ normal := dotProduct_self_pos hnormal
  have hcs := sq_dotProduct_le_mul_dotProduct_self (design.atom label) normal
  have hge : 1 ≤ atomShare design label := by
    rw [atomShare, leverageOf_eq_dotProduct_self]
    nlinarith [hparseval, hcs, hnormPos, design.weight_pos label]
  linarith [atomShare_le_one_ofAnyRank design label, hge]

/-- **THE HYPERPLANE NO-GO.**  A rank-three design whose atoms lie in one plane
apart from a single label is never a tie.  The exceptional atom carries a whole
direction by itself, so its share is one. -/
theorem not_isTie_of_forall_dotProduct_normal_eq_zero (design : WeightedDesign size 3)
    (label : Fin size) (normal : Fin 3 → ℝ) (hnormal : normal ≠ 0)
    (hflat : ∀ other, other ≠ label → design.atom other ⬝ᵥ normal = 0) : ¬ IsTie design :=
  not_isTie_of_atomShare_eq_one design label
    (atomShare_eq_one_of_forall_dotProduct_normal_eq_zero design label normal hnormal hflat)

/-- **THE FLAT-LABEL DICHOTOMY AT `(6,3)`.**  Five coplanar atoms out of six kill
the tie and kill stress-freeness at the same time.  The tie half is the
hyperplane no-go and the stress half is `Gtz.not_five_coplanar_of_stressFree`. -/
theorem not_isTie_and_hasStress_of_five_coplanar (design : WeightedDesign 6 3)
    (label : Fin 6) (normal : Fin 3 → ℝ) (hnormal : normal ≠ 0)
    (hflat : ∀ other, other ≠ label → design.atom other ⬝ᵥ normal = 0) :
    ¬ IsTie design
      ∧ ¬ (∀ stressCoeff : Fin 6 → ℝ,
            (∑ atomIndex, stressCoeff atomIndex • atomMatrix (design.atom atomIndex)) = 0 →
              stressCoeff = 0) := by
  refine ⟨not_isTie_of_forall_dotProduct_normal_eq_zero design label normal hnormal hflat, ?_⟩
  intro hstressFree
  obtain ⟨other, hother, hne⟩ :=
    not_five_coplanar_of_stressFree design.atom hstressFree normal hnormal label
  exact hne (hflat other hother)

end Gtz
