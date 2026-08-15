import Gtz.Design.NormalSchurClosure
import Gtz.Design.LineStrataCardFourSplit

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The flat-split criterion, the whole-line margin, and the refutation of the
# rank-two weld

`Gtz.flat_dominates_on_free_orthogonal` says the flat atoms of a
whole-flat-plus-one selection must dominate ALONE on the free atom's orthogonal
complement.  That is a rank-two domination statement, and the obvious move is to
feed it to `Gtz.gtz_rank_two`, which is a THEOREM.  This module supplies the
exact criterion the line strata read, and then refutes that weld.

## The flat-split criterion

`Gtz.posDef_subsetSum_sub_one_iff_normalSchur` is an equivalence at any nonzero
normal.  At a flat set every selected flat atom drops out of the normal sum and
out of the cross sum, because both carry a factor `atom ⬝ normal`.  Only the
labels of `selected \ flat` survive there, while the plane sum keeps every
selected label.  The result is `flatSplit_posDef_iff`: ONE division-free,
weight-free equivalence, generic in the selection AND in the flat set.

It reads every class of both line strata at once:

* one line, whole-line class (three selections) — `selected \ flat` is a single
  free label
* one line, two-line class (nine selections) — `selected \ flat` is a free pair
* one line, one-line class (three selections) — `selected \ flat` is a free
  triple
* two meeting lines, first line and second line (three plus three, and never
  both by `Gtz.twoMeetingLines_cardFour_not_both_lines`).

## The whole-line margin

Specialising to a single outside label gives the exact margin

  `1 < h²`  and  `b² < (h² − 1) · (L − ⟨v,v⟩)`

with `h` the free height, `b` its in-plane reading and `L` the flat atoms'
summed squared readings.  The flat atoms must beat the probe energy by
`b²/(h² − 1)`, not merely beat it.  Erasing one flat label subtracts one squared
reading from `L` and changes nothing else, so the whole-line branch of the
card-four escape is exactly a planar DROP problem.

## The weld is refuted, and heaviness does not rescue it

That drop statement is FALSE, and `heavy_planar_dropOne_false` proves it with
three EXACTLY UNIT vectors — leverage one, so exactly heavy.  The trine
`(1,0)`, `(−3/5, 4/5)`, `(−3/5, −4/5)` has

  `∑ᵢ vᵢvᵢᵀ − 1 = diag(18/25, 7/25) ≻ 0`

while every pair fails to dominate even weakly.  Rank-two GTZ cannot supply the
missing pair, because rank-two GTZ consumes Parseval and the drop statement
consumes only heaviness.  Any future route through the flat atoms must consume
Parseval ON THE PLANE.
-/

namespace Gtz

open Finset Matrix

variable {size rank : ℕ}

/-! ## 1. A vanishing summand restricts a sum to the complement -/

/-- A function that vanishes on `flat` sums over `selected` exactly as it sums
over `selected \ flat`. -/
theorem sum_eq_sum_sdiff_of_vanishing (selected flat : Finset (Fin size))
    (summand : Fin size → ℝ) (hvanish : ∀ label ∈ flat, summand label = 0) :
    ∑ label ∈ selected, summand label = ∑ label ∈ selected \ flat, summand label := by
  have hinter : (∑ label ∈ selected ∩ flat, summand label) = 0 :=
    Finset.sum_eq_zero fun label hlabel =>
      hvanish label (Finset.mem_of_mem_inter_right hlabel)
  have hset : selected \ (selected ∩ flat) = selected \ flat := by
    ext testLabel
    simp only [Finset.mem_sdiff, Finset.mem_inter]
    tauto
  have hsplit := Finset.sum_sdiff (f := summand)
    (Finset.inter_subset_left (s₁ := selected) (s₂ := flat))
  rw [hset, hinter, add_zero] at hsplit
  exact hsplit.symm

/-- At the normal only the selected labels OUTSIDE the flat set are visible. -/
theorem flatSplit_normalSum (design : WeightedDesign size rank)
    (selected flat : Finset (Fin size)) (normalVec : Fin rank → ℝ)
    (hflat : ∀ label ∈ flat, design.atom label ⬝ᵥ normalVec = 0) :
    ∑ label ∈ selected, (design.atom label ⬝ᵥ normalVec) ^ 2
      = ∑ label ∈ selected \ flat, (design.atom label ⬝ᵥ normalVec) ^ 2 :=
  sum_eq_sum_sdiff_of_vanishing selected flat _
    fun label hlabel => by rw [hflat label hlabel]; ring

/-- The cross sum is carried by the selected labels outside the flat set alone. -/
theorem flatSplit_crossSum (design : WeightedDesign size rank)
    (selected flat : Finset (Fin size)) (normalVec planeProbe : Fin rank → ℝ)
    (hflat : ∀ label ∈ flat, design.atom label ⬝ᵥ normalVec = 0) :
    ∑ label ∈ selected,
        (design.atom label ⬝ᵥ planeProbe) * (design.atom label ⬝ᵥ normalVec)
      = ∑ label ∈ selected \ flat,
        (design.atom label ⬝ᵥ planeProbe) * (design.atom label ⬝ᵥ normalVec) :=
  sum_eq_sum_sdiff_of_vanishing selected flat _
    fun label hlabel => by rw [hflat label hlabel]; ring

/-! ## 2. The flat-split criterion -/

/-- **THE FLAT-SPLIT CRITERION.**

At a unit normal killed by every atom of `flat`, a selection's gap is positive
definite exactly when the selected labels OUTSIDE the flat set carry more than
one unit of squared height, and at every nonzero in-plane probe their cross
reading is beaten by the excess height times the whole plane reading.

The flat atoms are invisible in the first two sums and fully present in the
third.  The statement is division-free, weight-free, and generic in BOTH the
selection and the flat set, so one instance serves every class of both line
strata. -/
theorem flatSplit_posDef_iff (design : WeightedDesign size rank)
    (selected flat : Finset (Fin size))
    (normalVec : Fin rank → ℝ) (hunit : normalVec ⬝ᵥ normalVec = 1)
    (hflat : ∀ label ∈ flat, design.atom label ⬝ᵥ normalVec = 0) :
    (subsetSum design selected - 1).PosDef ↔
      (1 < ∑ label ∈ selected \ flat, (design.atom label ⬝ᵥ normalVec) ^ 2 ∧
        ∀ planeProbe : Fin rank → ℝ, planeProbe ⬝ᵥ normalVec = 0 → planeProbe ≠ 0 →
          (∑ label ∈ selected \ flat,
              (design.atom label ⬝ᵥ planeProbe) * (design.atom label ⬝ᵥ normalVec)) ^ 2
            < ((∑ label ∈ selected \ flat, (design.atom label ⬝ᵥ normalVec) ^ 2) - 1)
              * ((∑ label ∈ selected, (design.atom label ⬝ᵥ planeProbe) ^ 2)
                  - planeProbe ⬝ᵥ planeProbe)) := by
  have hnormalNe : normalVec ≠ 0 := by
    intro hzero
    rw [hzero, zero_dotProduct] at hunit
    norm_num at hunit
  rw [posDef_subsetSum_sub_one_iff_normalSchur design selected hnormalNe,
    flatSplit_normalSum design selected flat normalVec hflat, hunit]
  constructor
  · rintro ⟨hheight, hschur⟩
    refine ⟨hheight, fun planeProbe hplaneOrth hplaneNe => ?_⟩
    have hstrict := hschur planeProbe hplaneOrth hplaneNe
    rwa [flatSplit_crossSum design selected flat normalVec planeProbe hflat] at hstrict
  · rintro ⟨hheight, hmargin⟩
    refine ⟨hheight, fun planeProbe hplaneOrth hplaneNe => ?_⟩
    have hstrict := hmargin planeProbe hplaneOrth hplaneNe
    rwa [flatSplit_crossSum design selected flat normalVec planeProbe hflat]

/-- **THE TWO-OUTSIDE CRITERION — the nine.**

At one line, nine of the fifteen card-four selections hold exactly two line
atoms, so `selected \ flat` is a free PAIR.  This is that class read explicitly:
the two free heights must jointly carry more than one unit, and their combined
cross reading must be beaten by the excess.  This is the largest class of the
`3 / 9 / 3` split of `Gtz.oneLine_twoLine_cardFour_card`. -/
theorem flatSplit_pair_posDef_iff (design : WeightedDesign size rank)
    (selected flat : Finset (Fin size)) (freeFirst freeSecond : Fin size)
    (hne : freeFirst ≠ freeSecond)
    (hsdiff : selected \ flat = {freeFirst, freeSecond})
    (normalVec : Fin rank → ℝ) (hunit : normalVec ⬝ᵥ normalVec = 1)
    (hflat : ∀ label ∈ flat, design.atom label ⬝ᵥ normalVec = 0) :
    (subsetSum design selected - 1).PosDef ↔
      (1 < (design.atom freeFirst ⬝ᵥ normalVec) ^ 2
            + (design.atom freeSecond ⬝ᵥ normalVec) ^ 2 ∧
        ∀ planeProbe : Fin rank → ℝ, planeProbe ⬝ᵥ normalVec = 0 → planeProbe ≠ 0 →
          ((design.atom freeFirst ⬝ᵥ planeProbe)
                * (design.atom freeFirst ⬝ᵥ normalVec)
              + (design.atom freeSecond ⬝ᵥ planeProbe)
                * (design.atom freeSecond ⬝ᵥ normalVec)) ^ 2
            < ((design.atom freeFirst ⬝ᵥ normalVec) ^ 2
                + (design.atom freeSecond ⬝ᵥ normalVec) ^ 2 - 1)
              * ((∑ label ∈ selected, (design.atom label ⬝ᵥ planeProbe) ^ 2)
                  - planeProbe ⬝ᵥ planeProbe)) := by
  rw [flatSplit_posDef_iff design selected flat normalVec hunit hflat, hsdiff]
  simp only [Finset.sum_pair hne]

/-! ## 3. The whole-flat specialisation: the exact margin -/

/-- A whole-flat-plus-one selection has exactly one label outside the flat set. -/
theorem insert_sdiff_self (flat : Finset (Fin size)) (free : Fin size)
    (hfree : free ∉ flat) : insert free flat \ flat = {free} := by
  ext testLabel
  simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hmem, hnot⟩
    rcases hmem with rfl | hmem
    · rfl
    · exact absurd hmem hnot
  · rintro rfl
    exact ⟨Or.inl rfl, hfree⟩

/-- **THE WHOLE-FLAT MARGIN CRITERION.**

A whole-flat-plus-one selection is positive definite exactly when its single
outside atom stands strictly above the unit normal, and at every nonzero
in-plane probe the flat atoms beat the probe energy by the exact margin
`(free reading)² / (height² − 1)`.

It is strictly stronger than `Gtz.flat_dominates_on_free_orthogonal`, which is
the special case where the free atom reads zero on the probe: there the margin
term vanishes and only `⟨v,v⟩ < L` survives. -/
theorem wholeFlat_posDef_iff_margin (design : WeightedDesign size rank)
    (flat : Finset (Fin size)) (free : Fin size) (hfree : free ∉ flat)
    (normalVec : Fin rank → ℝ) (hunit : normalVec ⬝ᵥ normalVec = 1)
    (hflat : ∀ label ∈ flat, design.atom label ⬝ᵥ normalVec = 0) :
    (subsetSum design (insert free flat) - 1).PosDef ↔
      (1 < (design.atom free ⬝ᵥ normalVec) ^ 2 ∧
        ∀ planeProbe : Fin rank → ℝ, planeProbe ⬝ᵥ normalVec = 0 → planeProbe ≠ 0 →
          (design.atom free ⬝ᵥ planeProbe) ^ 2
            < ((design.atom free ⬝ᵥ normalVec) ^ 2 - 1)
              * ((∑ label ∈ flat, (design.atom label ⬝ᵥ planeProbe) ^ 2)
                  - planeProbe ⬝ᵥ planeProbe)) := by
  rw [flatSplit_posDef_iff design (insert free flat) flat normalVec hunit hflat,
    insert_sdiff_self flat free hfree]
  simp only [Finset.sum_singleton, Finset.sum_insert hfree]
  constructor
  · rintro ⟨hheight, hmargin⟩
    refine ⟨hheight, fun planeProbe hplaneOrth hplaneNe => ?_⟩
    have hstrict := hmargin planeProbe hplaneOrth hplaneNe
    nlinarith [hstrict, hheight]
  · rintro ⟨hheight, hmargin⟩
    refine ⟨hheight, fun planeProbe hplaneOrth hplaneNe => ?_⟩
    have hstrict := hmargin planeProbe hplaneOrth hplaneNe
    nlinarith [hstrict, hheight]

/-- **THE ERASURE READS THE SAME MARGIN, WITH ONE TERM REMOVED.**

Erasing one flat label from a whole-flat-plus-one selection subtracts exactly
that label's squared reading from the flat sum and changes nothing else.  The
whole-flat branch of the card-four escape is therefore precisely a planar DROP
problem: remove one rank-one term and keep the strict margin. -/
theorem wholeFlat_erase_posDef_iff_margin (design : WeightedDesign size rank)
    (flat : Finset (Fin size)) (free : Fin size) (hfree : free ∉ flat)
    (dropped : Fin size) (hdropped : dropped ∈ flat)
    (normalVec : Fin rank → ℝ) (hunit : normalVec ⬝ᵥ normalVec = 1)
    (hflat : ∀ label ∈ flat, design.atom label ⬝ᵥ normalVec = 0) :
    (subsetSum design (insert free (flat.erase dropped)) - 1).PosDef ↔
      (1 < (design.atom free ⬝ᵥ normalVec) ^ 2 ∧
        ∀ planeProbe : Fin rank → ℝ, planeProbe ⬝ᵥ normalVec = 0 → planeProbe ≠ 0 →
          (design.atom free ⬝ᵥ planeProbe) ^ 2
            < ((design.atom free ⬝ᵥ normalVec) ^ 2 - 1)
              * (((∑ label ∈ flat, (design.atom label ⬝ᵥ planeProbe) ^ 2)
                    - (design.atom dropped ⬝ᵥ planeProbe) ^ 2)
                  - planeProbe ⬝ᵥ planeProbe)) := by
  have hfreeErase : free ∉ flat.erase dropped := fun hmem =>
    hfree (Finset.mem_of_mem_erase hmem)
  have hflatErase : ∀ label ∈ flat.erase dropped,
      design.atom label ⬝ᵥ normalVec = 0 := fun label hlabel =>
    hflat label (Finset.mem_of_mem_erase hlabel)
  rw [wholeFlat_posDef_iff_margin design (flat.erase dropped) free hfreeErase
    normalVec hunit hflatErase]
  constructor
  · rintro ⟨hheight, hmargin⟩
    refine ⟨hheight, fun planeProbe hplaneOrth hplaneNe => ?_⟩
    have hstrict := hmargin planeProbe hplaneOrth hplaneNe
    rwa [Finset.sum_erase_eq_sub hdropped] at hstrict
  · rintro ⟨hheight, hmargin⟩
    refine ⟨hheight, fun planeProbe hplaneOrth hplaneNe => ?_⟩
    have hstrict := hmargin planeProbe hplaneOrth hplaneNe
    rwa [Finset.sum_erase_eq_sub hdropped]

/-- **THE WHOLE-FLAT ESCAPE IS EXACTLY A PLANAR DROP.**  Under the standing
margin of the full selection, some flat label may be erased with the selection
still positive definite exactly when that label's squared reading can be spared
from the flat sum at every in-plane probe. -/
theorem wholeFlat_escape_iff_planarDrop (design : WeightedDesign size rank)
    (flat : Finset (Fin size)) (free : Fin size) (hfree : free ∉ flat)
    (normalVec : Fin rank → ℝ) (hunit : normalVec ⬝ᵥ normalVec = 1)
    (hflat : ∀ label ∈ flat, design.atom label ⬝ᵥ normalVec = 0)
    (hposDef : (subsetSum design (insert free flat) - 1).PosDef) :
    (∃ dropped ∈ flat,
        (subsetSum design (insert free (flat.erase dropped)) - 1).PosDef)
      ↔ (∃ dropped ∈ flat,
        ∀ planeProbe : Fin rank → ℝ, planeProbe ⬝ᵥ normalVec = 0 → planeProbe ≠ 0 →
          (design.atom free ⬝ᵥ planeProbe) ^ 2
            < ((design.atom free ⬝ᵥ normalVec) ^ 2 - 1)
              * (((∑ label ∈ flat, (design.atom label ⬝ᵥ planeProbe) ^ 2)
                    - (design.atom dropped ⬝ᵥ planeProbe) ^ 2)
                  - planeProbe ⬝ᵥ planeProbe)) := by
  have hheight : 1 < (design.atom free ⬝ᵥ normalVec) ^ 2 :=
    ((wholeFlat_posDef_iff_margin design flat free hfree normalVec hunit
      hflat).mp hposDef).1
  constructor
  · rintro ⟨dropped, hdropped, hdropPosDef⟩
    exact ⟨dropped, hdropped,
      ((wholeFlat_erase_posDef_iff_margin design flat free hfree dropped hdropped
        normalVec hunit hflat).mp hdropPosDef).2⟩
  · rintro ⟨dropped, hdropped, hmargin⟩
    exact ⟨dropped, hdropped,
      (wholeFlat_erase_posDef_iff_margin design flat free hfree dropped hdropped
        normalVec hunit hflat).mpr ⟨hheight, hmargin⟩⟩

/-! ## 4. The planar drop statement is FALSE, at exactly unit atoms -/

/-- The trine: three unit vectors of the plane at mutual angle `2π/3`, in exact
rational coordinates. -/
noncomputable def trineVec : Fin 3 → (Fin 2 → ℝ)
  | 0 => ![1, 0]
  | 1 => ![-3/5, 4/5]
  | 2 => ![-3/5, -4/5]

/-- Every trine vector has leverage exactly one, so the trine is exactly heavy. -/
theorem trineVec_unit (index : Fin 3) : trineVec index ⬝ᵥ trineVec index = 1 := by
  fin_cases index <;>
    norm_num [trineVec, dotProduct, Fin.sum_univ_two]

/-- The trine reads any probe with the exact energy `(43x² + 32y²)/25`. -/
theorem trineVec_sum_reading (probe : Fin 2 → ℝ) :
    ∑ index : Fin 3, (trineVec index ⬝ᵥ probe) ^ 2
      = (43 * probe 0 ^ 2 + 32 * probe 1 ^ 2) / 25 := by
  rw [Fin.sum_univ_three]
  simp only [trineVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  ring

/-- **The trine strictly dominates the identity of the plane.** -/
theorem trineVec_triple_strict (probe : Fin 2 → ℝ) (hprobe : probe ≠ 0) :
    probe ⬝ᵥ probe < ∑ index : Fin 3, (trineVec index ⬝ᵥ probe) ^ 2 := by
  have hcoord : probe 0 ≠ 0 ∨ probe 1 ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hprobe (by funext coordIndex; fin_cases coordIndex <;> simp [hall.1, hall.2])
  rw [trineVec_sum_reading]
  have henergy : probe ⬝ᵥ probe = probe 0 ^ 2 + probe 1 ^ 2 := by
    simp only [dotProduct, Fin.sum_univ_two]; ring
  rw [henergy]
  rcases hcoord with hfirst | hsecond
  · have hpos : 0 < probe 0 ^ 2 := by positivity
    nlinarith [sq_nonneg (probe 1)]
  · have hpos : 0 < probe 1 ^ 2 := by positivity
    nlinarith [sq_nonneg (probe 0)]

/-- **No pair of the trine dominates the identity, even weakly.**  Each pair is
beaten on one coordinate axis. -/
theorem trineVec_pair_fails (index : Fin 3) :
    ∃ probe : Fin 2 → ℝ,
      ∑ other ∈ Finset.univ.erase index, (trineVec other ⬝ᵥ probe) ^ 2
        < probe ⬝ᵥ probe := by
  refine ⟨if index = 0 then ![1, 0] else ![0, 1], ?_⟩
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ index), Fin.sum_univ_three]
  fin_cases index <;>
    norm_num [trineVec, dotProduct, Fin.sum_univ_two]

/-- **THE PLANAR DROP STATEMENT IS FALSE, AND HEAVINESS DOES NOT RESCUE IT.**

Three vectors of the plane, each of leverage exactly one, whose triple strictly
dominates the identity while no pair of them dominates it even weakly.

This refutes the weld of `Gtz.flat_dominates_on_free_orthogonal` to
`Gtz.gtz_rank_two`.  Rank-two GTZ hands back a dominating PAIR only because it
consumes Parseval; the drop statement consumes only heaviness, and heaviness is
not enough.  Any route through the flat atoms must consume Parseval ON THE
PLANE. -/
theorem heavy_planar_dropOne_false :
    ∃ vec : Fin 3 → (Fin 2 → ℝ),
      (∀ index : Fin 3, vec index ⬝ᵥ vec index = 1)
      ∧ (∀ probe : Fin 2 → ℝ, probe ≠ 0 →
          probe ⬝ᵥ probe < ∑ index : Fin 3, (vec index ⬝ᵥ probe) ^ 2)
      ∧ (∀ index : Fin 3, ∃ probe : Fin 2 → ℝ,
          ∑ other ∈ Finset.univ.erase index, (vec other ⬝ᵥ probe) ^ 2
            < probe ⬝ᵥ probe) :=
  ⟨trineVec, trineVec_unit, trineVec_triple_strict, trineVec_pair_fails⟩

end Gtz
