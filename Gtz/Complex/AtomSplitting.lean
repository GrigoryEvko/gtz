/-
# Atom splitting: the complex record is attained at EVERY size above its own

An upper bound on a rank constant is one exhibited design, and every design has
a size.  So `ComplexRankConstantAtMost 3 hesseMarginRankThree` — the Hesse SIC
at nine atoms — leaves open at which sizes the level is REACHED.  This file
answers that, for every rank and every bound, by a construction that costs
nothing: split one atom's WEIGHT in two and list the atom vector twice.

  `t_c g_c g_c*  =  (f t_c) g_c g_c*  +  ((1-f) t_c) g_c g_c*`

so Parseval survives verbatim, the weights still total one, and both new weights
are positive when `0 < f < 1`.  The subset sums are WEIGHT-FREE, so nothing moves
except the index set:

* a `k`-subset avoiding the new index has the old atom sum;
* a `k`-subset containing the new index but not the split source has the old atom
  sum of the subset with the source swapped in;
* a `k`-subset containing BOTH sees the same atom vector twice, so its `k` rows
  are dependent — the atom block annihilates a nonzero vector, and a block that
  kills a vector cannot dominate any positive level.

Hence the design's value is unchanged, and by induction the level is reached at
every size at or above the witness's own.  Specialised at rank three this says
the Hesse level `3(1 - cos 2 pi / 9)` is attained by a genuine weighted design at
every `m >= 9`, so the complex rank-three record is not a nine-atom accident.

## What is PROVED here vs MEASURED elsewhere

PROVED (kernel-checked, this file): the splitting construction, its value
preservation, and the size ladder `>= 9` for the Hesse level.

MEASURED (floating point, NOT proved, recorded in the ledger at the end of this
file): that no complex weighted `(m,3)`-design with `6 <= m <= 15` gets below
`0.700`, and that the size profile jumps exactly at `m = 9`.  Those numbers are
evidence for `alpha_3 = 3(1 - cos 2 pi / 9)`, not a proof of it; the proved
window at rank three remains `1/3 <= alpha_3 <= 3(1 - cos 2 pi / 9)`.

CITED (published, not mechanized): Nesterenko, arXiv:2604.24087, Proposition 1 —
at rank two the analogous constant `2 - 2/sqrt 3` is exact and its equality case
is rigid.  The rank-three analogue is open.
-/
import Mathlib
import Gtz.Complex.PerRankConstantLedger

namespace Gtz

open Matrix Complex
open scoped ComplexOrder

/-! ## A repeated atom vector kills the whole subset

The only genuinely new linear algebra.  If a `k`-subset lists the same atom
vector at two different labels, then the `k` conjugated atom rows form a square
matrix with two equal rows, hence a singular one, hence there is a nonzero
direction orthogonal to every atom of the subset.  The atom block sends that
direction to zero, so the shifted block has a strictly negative quadratic form at
any positive level. -/

section RepeatedAtom

variable {m k : ℕ}

/-- The `k x k` matrix of CONJUGATED atom rows along an enumeration of a
`k`-subset.  Its `mulVec` reads off the projections of a direction on the
subset's atoms. -/
noncomputable def conjugatedSubsetRows (atomOf : Fin m → (Fin k → ℂ))
    {subset : Finset (Fin m)} (enumerate : {x // x ∈ subset} ≃ Fin k) :
    Matrix (Fin k) (Fin k) ℂ :=
  fun rowIndex colIndex => (starRingEnd ℂ) (atomOf (enumerate.symm rowIndex) colIndex)

theorem conjugatedSubsetRows_mulVec (atomOf : Fin m → (Fin k → ℂ))
    {subset : Finset (Fin m)} (enumerate : {x // x ∈ subset} ≃ Fin k)
    (direction : Fin k → ℂ) (rowIndex : Fin k) :
    (conjugatedSubsetRows atomOf enumerate *ᵥ direction) rowIndex
      = star (atomOf (enumerate.symm rowIndex)) ⬝ᵥ direction := by
  simp only [conjugatedSubsetRows, Matrix.mulVec, dotProduct, Pi.star_apply,
    RCLike.star_def]

/-- **A repeated atom vector forbids domination at any positive level.**  The
enumeration turns the subset into `Fin k`, two of its rows coincide, so the
determinant vanishes and the row matrix has a nonzero kernel vector; that vector
is orthogonal to every atom of the subset, so the atom block annihilates it and
the shifted block's quadratic form is `- level * |x|^2 < 0`. -/
theorem not_posSemidef_atomSum_sub_of_repeatedAtom
    (atomOf : Fin m → (Fin k → ℂ)) {subset : Finset (Fin m)} (hcard : subset.card = k)
    {firstLabel secondLabel : Fin m}
    (hfirst : firstLabel ∈ subset) (hsecond : secondLabel ∈ subset)
    (hdistinct : firstLabel ≠ secondLabel)
    (hsameAtom : atomOf firstLabel = atomOf secondLabel)
    {level : ℝ} (hlevelPos : 0 < level) :
    ¬ ((∑ atomLabel ∈ subset, complexAtom (atomOf atomLabel))
        - ((level : ℝ) : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ)).PosSemidef := by
  intro hpsd
  classical
  set enumerate : {x // x ∈ subset} ≃ Fin k := Finset.equivFinOfCardEq hcard with henum
  set rowMatrix := conjugatedSubsetRows atomOf enumerate with hrow
  have hrowsEqual : rowMatrix (enumerate ⟨firstLabel, hfirst⟩)
      = rowMatrix (enumerate ⟨secondLabel, hsecond⟩) := by
    funext colIndex
    simp only [hrow, conjugatedSubsetRows, Equiv.symm_apply_apply, hsameAtom]
  have hindicesDiffer : enumerate ⟨firstLabel, hfirst⟩ ≠ enumerate ⟨secondLabel, hsecond⟩ := by
    intro hcontra
    exact hdistinct (congrArg Subtype.val (enumerate.injective hcontra))
  have hdetZero : rowMatrix.det = 0 :=
    Matrix.det_zero_of_row_eq hindicesDiffer hrowsEqual
  obtain ⟨nullVector, hnullNe, hnullMul⟩ :=
    (Matrix.exists_mulVec_eq_zero_iff (M := rowMatrix)).mpr hdetZero
  have horthogonal : ∀ atomLabel ∈ subset,
      star (atomOf atomLabel) ⬝ᵥ nullVector = 0 := by
    intro atomLabel hmember
    have hrowZero := congrFun hnullMul (enumerate ⟨atomLabel, hmember⟩)
    rw [conjugatedSubsetRows_mulVec] at hrowZero
    simpa only [Equiv.symm_apply_apply, Pi.zero_apply] using hrowZero
  have hblockKills : (∑ atomLabel ∈ subset, complexAtom (atomOf atomLabel))
      *ᵥ nullVector = 0 := by
    rw [Matrix.sum_mulVec]
    refine Finset.sum_eq_zero fun atomLabel hmember => ?_
    rw [complexAtom_mulVec, horthogonal atomLabel hmember, zero_smul]
  have hshifted : ((∑ atomLabel ∈ subset, complexAtom (atomOf atomLabel))
        - ((level : ℝ) : ℂ) • (1 : Matrix (Fin k) (Fin k) ℂ)) *ᵥ nullVector
      = (-((level : ℝ) : ℂ)) • nullVector := by
    rw [Matrix.sub_mulVec, hblockKills, smul_mulVec, Matrix.one_mulVec, zero_sub, neg_smul]
  have hquad := hpsd.dotProduct_mulVec_nonneg nullVector
  rw [hshifted, dotProduct_smul, smul_eq_mul] at hquad
  have hnormPos : (0 : ℂ) < star nullVector ⬝ᵥ nullVector :=
    dotProduct_star_self_pos_iff.mpr hnullNe
  obtain ⟨hnormRe, hnormIm⟩ := Complex.lt_def.mp hnormPos
  obtain ⟨hprodRe, hprodIm⟩ := Complex.le_def.mp hquad
  simp only [Complex.zero_re, Complex.zero_im] at hnormRe hnormIm hprodRe hprodIm
  rw [Complex.mul_re] at hprodRe
  simp only [Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
    neg_zero, zero_mul, sub_zero] at hprodRe
  nlinarith [hprodRe, hnormRe, hlevelPos]

end RepeatedAtom

/-! ## Splitting one atom's weight

The design gains one label; the atom LIST gains a copy of the split source, and
the source's weight is divided between the two copies. -/

section SplitAtomWeight

variable {m k : ℕ}

/-- **The split design**: atom `source` is listed twice, its weight cut into the
shares `fraction` and `1 - fraction`.  Parseval is untouched because the two
shares recombine to the original weight on the SAME rank-one atom. -/
noncomputable def splitAtomWeight (design : ComplexWeightedDesign m k)
    (source : Fin m) (fraction : ℝ) (hlow : 0 < fraction) (hhigh : fraction < 1) :
    ComplexWeightedDesign (m + 1) k where
  atom := Fin.snoc design.atom (design.atom source)
  weight := Fin.snoc
    (Function.update design.weight source (fraction * design.weight source))
    ((1 - fraction) * design.weight source)
  weight_pos := by
    intro atomLabel
    refine Fin.lastCases ?_ ?_ atomLabel
    · rw [Fin.snoc_last]
      exact mul_pos (by linarith) (design.weight_pos source)
    · intro innerLabel
      rw [Fin.snoc_castSucc]
      by_cases hsame : innerLabel = source
      · subst hsame
        rw [Function.update_self]
        exact mul_pos hlow (design.weight_pos innerLabel)
      · rw [Function.update_of_ne hsame]
        exact design.weight_pos innerLabel
  weight_sum_one := by
    classical
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
    rw [Finset.sum_update_of_mem (Finset.mem_univ source),
      Finset.sum_sdiff_eq_sub (Finset.singleton_subset_iff.mpr (Finset.mem_univ source)),
      Finset.sum_singleton, design.weight_sum_one]
    ring
  isParseval := by
    classical
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
    have hasUpdate : (fun innerLabel => ((Function.update design.weight source
          (fraction * design.weight source) innerLabel : ℝ) : ℂ)
          • complexAtom (design.atom innerLabel))
        = Function.update (fun innerLabel => ((design.weight innerLabel : ℝ) : ℂ)
            • complexAtom (design.atom innerLabel)) source
            (((fraction * design.weight source : ℝ) : ℂ)
              • complexAtom (design.atom source)) := by
      funext innerLabel
      by_cases hsame : innerLabel = source
      · subst hsame; simp
      · simp [Function.update_of_ne hsame]
    rw [hasUpdate, Finset.sum_update_of_mem (Finset.mem_univ source),
      Finset.sum_sdiff_eq_sub (Finset.singleton_subset_iff.mpr (Finset.mem_univ source)),
      Finset.sum_singleton, design.isParseval]
    push_cast
    module

@[simp] theorem splitAtomWeight_atom_castSucc (design : ComplexWeightedDesign m k)
    (source : Fin m) (fraction : ℝ) (hlow : 0 < fraction) (hhigh : fraction < 1)
    (innerLabel : Fin m) :
    (splitAtomWeight design source fraction hlow hhigh).atom innerLabel.castSucc
      = design.atom innerLabel := by
  change Fin.snoc (α := fun _ => Fin k → ℂ) design.atom (design.atom source)
      innerLabel.castSucc = design.atom innerLabel
  exact Fin.snoc_castSucc _ _ innerLabel

@[simp] theorem splitAtomWeight_atom_last (design : ComplexWeightedDesign m k)
    (source : Fin m) (fraction : ℝ) (hlow : 0 < fraction) (hhigh : fraction < 1) :
    (splitAtomWeight design source fraction hlow hhigh).atom (Fin.last m)
      = design.atom source := by
  change Fin.snoc (α := fun _ => Fin k → ℂ) design.atom (design.atom source)
      (Fin.last m) = design.atom source
  exact Fin.snoc_last _ _

/-! ### The three subset cases -/

/-- A subset of the enlarged index set that avoids the new label is the image of
a subset of the old one, with the same cardinality. -/
theorem exists_preimage_of_last_notMem {subset : Finset (Fin (m + 1))}
    (hlast : Fin.last m ∉ subset) :
    ∃ oldSubset : Finset (Fin m),
      subset = oldSubset.map Fin.castSuccEmb ∧ oldSubset.card = subset.card := by
  classical
  have hcovered : subset ⊆ (Finset.univ : Finset (Fin m)).map Fin.castSuccEmb := by
    intro atomLabel hmember
    refine Fin.lastCases ?_ ?_ atomLabel hmember
    · intro hcontra; exact absurd hcontra hlast
    · intro innerLabel _
      exact Finset.mem_map.mpr ⟨innerLabel, Finset.mem_univ innerLabel, rfl⟩
  obtain ⟨oldSubset, _, hequal⟩ := Finset.subset_map_iff.mp hcovered
  exact ⟨oldSubset, hequal, by rw [hequal, Finset.card_map]⟩

/-- Transporting the atom sum across the index embedding. -/
theorem atomSum_map_castSucc (design : ComplexWeightedDesign m k)
    (source : Fin m) (fraction : ℝ) (hlow : 0 < fraction) (hhigh : fraction < 1)
    (oldSubset : Finset (Fin m)) :
    (∑ atomLabel ∈ oldSubset.map Fin.castSuccEmb,
        complexAtom ((splitAtomWeight design source fraction hlow hhigh).atom atomLabel))
      = ∑ atomLabel ∈ oldSubset, complexAtom (design.atom atomLabel) := by
  rw [Finset.sum_map]
  refine Finset.sum_congr rfl fun innerLabel _ => ?_
  rw [Fin.castSuccEmb_apply, splitAtomWeight_atom_castSucc]

/-- **Value preservation.**  The split design has the same best-subset value as
the design it came from: every `k`-subset either transports to a `k`-subset of
the original or repeats an atom, and a repeat cannot dominate. -/
theorem splitAtomWeight_valueAtMost (design : ComplexWeightedDesign m k)
    (source : Fin m) (fraction : ℝ) (hlow : 0 < fraction) (hhigh : fraction < 1)
    {bound : ℝ} (hboundNonneg : 0 ≤ bound)
    (hvalue : ComplexDesignValueAtMost design bound) :
    ComplexDesignValueAtMost (splitAtomWeight design source fraction hlow hhigh) bound := by
  classical
  intro subset hcard level habove hpsd
  have hlevelPos : 0 < level := lt_of_le_of_lt hboundNonneg habove
  set splitDesign := splitAtomWeight design source fraction hlow hhigh with hsplit
  by_cases hlastMember : Fin.last m ∈ subset
  · by_cases hsourceMember : source.castSucc ∈ subset
    · -- both copies present: the atom list repeats, so nothing dominates
      refine not_posSemidef_atomSum_sub_of_repeatedAtom splitDesign.atom hcard
        hsourceMember hlastMember (Fin.castSucc_lt_last source).ne ?_ hlevelPos hpsd
      rw [hsplit, splitAtomWeight_atom_castSucc, splitAtomWeight_atom_last]
    · -- only the new copy: swap it for the source and land in the old index set
      set trimmedSubset := subset.erase (Fin.last m) with htrim
      have hlastGone : Fin.last m ∉ trimmedSubset := Finset.notMem_erase _ _
      obtain ⟨oldSubset, holdEq, holdCard⟩ := exists_preimage_of_last_notMem hlastGone
      have hsourceOut : source ∉ oldSubset := by
        intro hcontra
        have hmapped : source.castSucc ∈ trimmedSubset := by
          rw [holdEq]
          exact Finset.mem_map.mpr ⟨source, hcontra, rfl⟩
        exact hsourceMember (Finset.mem_of_mem_erase hmapped)
      have htrimCard : trimmedSubset.card = k - 1 := by
        rw [htrim, Finset.card_erase_of_mem hlastMember, hcard]
      have hkPos : 0 < k := by
        by_contra hcontra
        push_neg at hcontra
        interval_cases k
        · exact absurd (Finset.card_eq_zero.mp hcard ▸ hlastMember) (by simp)
      have hinsertCard : (insert source oldSubset).card = k := by
        rw [Finset.card_insert_of_notMem hsourceOut, holdCard, htrimCard]
        omega
      refine hvalue (insert source oldSubset) hinsertCard level habove ?_
      have hsumSplit : ∑ atomLabel ∈ subset, complexAtom (splitDesign.atom atomLabel)
          = ∑ atomLabel ∈ insert source oldSubset,
              complexAtom (design.atom atomLabel) := by
        rw [← Finset.add_sum_erase _ _ hlastMember, ← htrim, holdEq,
          atomSum_map_castSucc, Finset.sum_insert hsourceOut, hsplit,
          splitAtomWeight_atom_last]
      rw [ComplexDominatesAtLevel, ← hsumSplit]
      exact hpsd
  · -- the new copy is absent: the subset already lives in the old index set
    obtain ⟨oldSubset, holdEq, holdCard⟩ := exists_preimage_of_last_notMem hlastMember
    refine hvalue oldSubset (by rw [holdCard, hcard]) level habove ?_
    rw [ComplexDominatesAtLevel, ← atomSum_map_castSucc design source fraction hlow hhigh
      oldSubset, ← holdEq]
    exact hpsd

end SplitAtomWeight

/-! ## The size ladder

`ComplexRankConstantAtMost` forgets the size.  Its size-aware refinement is the
statement a witness actually delivers, and splitting walks it upward one atom at
a time. -/

section SizeLadder

/-- **`alpha_rank <= bound`, at a NAMED size**: an exhibited design on exactly
`size` atoms whose every `rank`-subset fails above `bound`. -/
def ComplexRankConstantAtMostAtSize (size rank : ℕ) (bound : ℝ) : Prop :=
  ∃ design : ComplexWeightedDesign size rank, ComplexDesignValueAtMost design bound

theorem complexRankConstantAtMost_of_atSize {size rank : ℕ} {bound : ℝ}
    (hwitness : ComplexRankConstantAtMostAtSize size rank bound) :
    ComplexRankConstantAtMost rank bound := by
  obtain ⟨design, hvalue⟩ := hwitness
  exact ⟨size, design, hvalue⟩

/-- One rung: a witness at `size` gives one at `size + 1`, by halving any atom's
weight.  Needs a positive size to have an atom to split, and a nonnegative bound
so that a repeated atom really is fatal. -/
theorem complexRankConstantAtMostAtSize_succ {size rank : ℕ} {bound : ℝ}
    (hsizePos : 0 < size) (hboundNonneg : 0 ≤ bound)
    (hwitness : ComplexRankConstantAtMostAtSize size rank bound) :
    ComplexRankConstantAtMostAtSize (size + 1) rank bound := by
  obtain ⟨design, hvalue⟩ := hwitness
  exact ⟨splitAtomWeight design ⟨0, hsizePos⟩ (1 / 2) (by norm_num) (by norm_num),
    splitAtomWeight_valueAtMost design ⟨0, hsizePos⟩ (1 / 2) (by norm_num) (by norm_num)
      hboundNonneg hvalue⟩

/-- **The ladder**: a witness at `size` gives one at every larger size. -/
theorem complexRankConstantAtMostAtSize_of_le {size largerSize rank : ℕ} {bound : ℝ}
    (hsizePos : 0 < size) (hboundNonneg : 0 ≤ bound) (hle : size ≤ largerSize)
    (hwitness : ComplexRankConstantAtMostAtSize size rank bound) :
    ComplexRankConstantAtMostAtSize largerSize rank bound := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hle
  induction extra with
  | zero => simpa only [Nat.add_zero] using hwitness
  | succ predecessor inductiveStep =>
      have hgrown := inductiveStep (Nat.le_add_right size predecessor)
      have hgrownPos : 0 < size + predecessor := by omega
      have hstep := complexRankConstantAtMostAtSize_succ (rank := rank) (bound := bound)
        hgrownPos hboundNonneg hgrown
      simpa only [Nat.add_succ] using hstep

end SizeLadder

/-! ## Rank three: the Hesse level at every size at least nine -/

section HesseLadder

/-- The Hesse SIC as a SIZE-AWARE witness. -/
theorem complexRankConstantAtMostAtSize_nine_hesse :
    ComplexRankConstantAtMostAtSize 9 3 hesseMarginRankThree :=
  ⟨hesseDesign, hesseDesign_valueAtMost⟩

/-- **The complex rank-three record is not a nine-atom accident.**  For every
`size >= 9` there is a complex weighted `(size, 3)`-design no `3`-subset of which
survives above `3(1 - cos 2 pi / 9)`. -/
theorem complexRankConstantAtMostAtSize_three_hesse (size : ℕ) (hsize : 9 ≤ size) :
    ComplexRankConstantAtMostAtSize size 3 hesseMarginRankThree :=
  complexRankConstantAtMostAtSize_of_le (by norm_num) hesseMargin_nonneg hsize
    complexRankConstantAtMostAtSize_nine_hesse

/-- The same statement in refutation form: complex weighted GTZ is FALSE at rank
three for every size at least nine, with a uniform quantitative margin. -/
theorem not_complexGtzWeighted_three_of_nine_le (size : ℕ) (hsize : 9 ≤ size) :
    ¬ ComplexGtzWeighted size 3 := by
  obtain ⟨design, hvalue⟩ := complexRankConstantAtMostAtSize_three_hesse size hsize
  have hbelowOne : hesseMarginRankThree < 1 := by
    have := hesseMargin_window
    linarith [this.2]
  exact not_complexGtzWeighted_of_designValueAtMost hbelowOne hvalue

end HesseLadder

/-! ## MEASURED ledger — the rank-three complex global search

Floating-point evidence, produced by an independent global search in projection
coordinates (`V` complex `m x 3` with orthonormal columns, so the Parseval
residual is `~1e-16` BY CONSTRUCTION, never as a penalty; every least eigenvalue
read as the square of the smallest SINGULAR value of `D^{-1/2} V_C`, never by
eigendecomposing the formed product).  None of it is proved.

* **No design beats the Hesse SIC.**  Two thousand independent cold multistarts
  (two hundred per size, sizes six through fifteen) of a target-feasibility
  descent aimed at the threshold `0.700`, strictly below
  `3(1 - cos 2 pi / 9) = 0.7018666706430659`, produced ZERO designs below it.
  So `3(1 - cos 2 pi / 9)` is the record, and the measured value of `alpha_3`
  over ℂ.

* **The size profile jumps at nine.**  Measured minima: sizes six, seven and
  eight all sit at `3 - sqrt 5 = 0.7639320225002102`, the shared-axis trine of
  `Gtz/Complex/PerRankConstantLedger.lean` and its splittings; size nine drops to
  the Hesse level and stays there.  The jump is exactly where `m = k^2` first
  admits a symmetric informationally complete set.

* **The tie pattern at the record.**  At the Hesse SIC all nine leverages equal
  three, all thirty-six pairwise overlap moduli equal `9/4`, twelve of the
  eighty-four triples are SINGULAR (the twelve lines of the Hesse configuration,
  Bargmann phase `pi`) and the remaining seventy-two ALL tie at the record
  (Bargmann phase `+- pi/3`).  A seventy-two-fold tie is the rank-three analogue
  of the rank-two rigidity Nesterenko proves, and it is why local search stalls:
  the active set is the whole non-degenerate part of the subset family.

* **The divisibility mirror.**  The size ladder above is a WEIGHTED statement:
  splitting produces unequal weights.  With the weights FROZEN at `1/m` — the
  unweighted problem, the one in which Nesterenko's `4 | n` condition lives — the
  Hesse level is realizable by clustering only when `9 | m`, since a cluster of
  `n_c` parallel atoms carries weight `n_c/m` and must match `1/9`.
-/

end Gtz
