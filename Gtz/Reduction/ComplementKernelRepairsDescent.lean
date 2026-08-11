import Gtz.Reduction.ComplementKernelWeld
import Gtz.Ties.CorankOneTieCriterion
import Gtz.Design.TraceIdentity
import Gtz.Reduction.DescentLadder
import Gtz.Quantitative.GeneralPositionWindow
import Gtz.LinAlg.SchurRankOne
import Gtz.Quantitative.WindowGramSignature

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The descent ladder, its supply, its blind spot, and the kernel that repairs it

Three landed vocabularies describe the same lattice of dominating subsets, and
this module puts them in one place and closes the gap between them.

**The ladder as principal minors.**  `Gtz/Reduction/ComplementKernelWeld.lean`
rewrites every complement test as a principal-minor test on `1 - K`, the
inverse-full-excess Gram of the omitted atoms, and identifies the first rung
with the landed full-base `Gtz.pivot`.  `complementKernel_submatrix` below turns
that into a statement about ONE matrix: the kernel of a sub-pick is the
corresponding principal submatrix, so the omitted-size one, two and three welds
are three readings of a single object.  The three rung equivalences then
identify each rung of the descent with a nested minor WITHOUT any rank-one
update identity -- both sides are the positive definiteness of the same
complement gap.  This matters: at `Gtz.tetraDesign` every `1 - K` diagonal entry
is exactly zero, the erased base is singular and the rank-one-update form of the
second rung does not exist, while the principal-minor form still decides.

**The supply.**  `Gtz.excess_balance` equates the insiders' weighted excess with
the outsiders' at a base of cardinality `rank + 1`.  The trace identity holds at
every base, so the two differ everywhere by a term that depends only on the
cardinality: `insider excess = outsider excess + (rank + 1 - card)`.  That term
is the descent supply.  It is strictly positive above the last rung, exactly
zero at it, and negative below -- so the landed criterion must not be read as a
rung condition below `rank + 1`.  At the full base the outsider sum is empty and
a strictly dominating erasure exists unconditionally once `rank + 1 < size`.

**The blind spot, and the repair.**  A pivot descent computes a pivot only
against a POSITIVE DEFINITE base, so it reaches a subset only as the erasure of
a positive definite superset one label larger.  Adding one rank-one atom closes
at most one kernel dimension, so a dominating subset whose gap has corank two or
more is unreachable from above -- `not_posDef_gap_insert_of_two_independent_gapProbes`
proves exactly that, and it is the direction the reachability half
(`exists_notMem_dotProduct_ne_zero_of_gap_mulVec_eq_zero`, below) does not give.
The kernel test has no such restriction: it inverts the full excess, which is
positive definite for every design of size at least two, and then reads
principal minors.  `kernelGap_decides_dominates_of_two_independent_gapProbes`
states the two together -- the descent provably cannot reach the subset, and the
kernel gap decides its domination anyway.

Nothing here discharges an obligation.  The weld's own docstring says it buys a
change of coordinates and discharges nothing; what is added is that the change
of coordinates is exactly the repair of the descent's incompleteness.
-/

namespace Gtz

open Matrix

variable {size rank : ℕ}

/-! ### One matrix, many rungs -/

/-- **The kernel of a sub-pick is a principal submatrix.**  Immediate from the
entrywise formula, and it is what makes the successive rungs readings of ONE
inverse-metric kernel rather than of a family of unrelated matrices. -/
theorem complementKernel_submatrix {omittedSize innerSize : ℕ}
    (design : WeightedDesign size rank) (pick : Fin omittedSize → Fin size)
    (reindex : Fin innerSize → Fin omittedSize) :
    complementKernel design (pick ∘ reindex)
      = (complementKernel design pick).submatrix reindex reindex := by
  ext first second
  rw [complementKernel_apply, Matrix.submatrix_apply, complementKernel_apply]
  rfl

/-- The kernel gap of a sub-pick is the corresponding principal submatrix. -/
theorem complementKernelGap_submatrix {omittedSize innerSize : ℕ}
    (design : WeightedDesign size rank) (pick : Fin omittedSize → Fin size)
    (reindex : Fin innerSize → Fin omittedSize) (hinjective : Function.Injective reindex) :
    complementKernelGap design (pick ∘ reindex)
      = (complementKernelGap design pick).submatrix reindex reindex := by
  ext first second
  rw [complementKernelGap, complementKernelGap, complementKernel_submatrix]
  by_cases hequal : first = second
  · subst hequal
    simp
  · have hreindex : reindex first ≠ reindex second := fun hcontra =>
      hequal (hinjective hcontra)
    simp [hequal, hreindex]

/-! ### The omitted set, as a finite set -/

/-- The image of a one-element pick. -/
theorem image_pick_one (pick : Fin 1 → Fin size) :
    Finset.image pick Finset.univ = {pick 0} := by
  ext label
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · rintro ⟨index, rfl⟩
    rw [Subsingleton.elim index 0]
  · rintro rfl
    exact ⟨0, rfl⟩

/-- The image of a two-element pick. -/
theorem image_pick_two (pick : Fin 2 → Fin size) :
    Finset.image pick Finset.univ = {pick 0, pick 1} := by
  ext label
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro ⟨index, rfl⟩
    fin_cases index
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩

/-- The image of a three-element pick. -/
theorem image_pick_three (pick : Fin 3 → Fin size) :
    Finset.image pick Finset.univ = {pick 0, pick 1, pick 2} := by
  ext label
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro ⟨index, rfl⟩
    fin_cases index
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  · rintro (rfl | rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩

/-- Erasing twice is complementing a pair. -/
theorem compl_pair_eq_erase_erase (first second : Fin size) :
    ({first, second} : Finset (Fin size))ᶜ
      = (Finset.univ.erase first).erase second := by
  ext label
  simp only [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton,
    Finset.mem_erase, Finset.mem_univ, and_true]
  tauto

/-- Erasing three times is complementing a triple. -/
theorem compl_triple_eq_erase_erase_erase (first second third : Fin size) :
    ({first, second, third} : Finset (Fin size))ᶜ
      = ((Finset.univ.erase first).erase second).erase third := by
  ext label
  simp only [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton,
    Finset.mem_erase, Finset.mem_univ, and_true]
  tauto

/-! ### The three rungs, in kernel vocabulary -/

/-- **RUNG ONE.**  The kernel gap of a single omitted label is positive definite
exactly when that label's full-base pivot is below one. -/
theorem posDef_kernelGap_singleton_iff_pivot_univ_lt_one
    (design : WeightedDesign size rank) (hsize : 2 ≤ size) (pick : Fin 1 → Fin size) :
    (complementKernelGap design pick).PosDef
      ↔ pivot design Finset.univ (pick 0) < 1 := by
  have hinjective : Function.Injective pick := fun first second _ =>
    Subsingleton.elim first second
  rw [← posDef_complementGap_iff_kernel_posDef design hsize pick hinjective,
    image_pick_one pick, Finset.compl_singleton]
  exact erase_strictDominates_iff_pivot_lt_one design Finset.univ
    (posDef_fullExcess design hsize) (Finset.mem_univ (pick 0))

/-- **RUNG TWO.**  The kernel gap of an omitted PAIR is positive definite exactly
when, from the base the ladder reaches after erasing the first label, the pivot
of the second is below one.  The ladder inverts a base one label smaller at
every rung; the kernel always inverts the full excess; this says the two decide
the same thing. -/
theorem posDef_kernelGap_pair_iff_pivot_erase_lt_one
    (design : WeightedDesign size rank) (hsize : 2 ≤ size)
    (pick : Fin 2 → Fin size) (hinjective : Function.Injective pick)
    (hbase : (subsetSum design (Finset.univ.erase (pick 0)) - 1).PosDef) :
    (complementKernelGap design pick).PosDef
      ↔ pivot design (Finset.univ.erase (pick 0)) (pick 1) < 1 := by
  have hdistinct : pick 1 ≠ pick 0 := fun hcontra => by
    have : (1 : Fin 2) = 0 := hinjective hcontra
    exact absurd this (by decide)
  have hmember : pick 1 ∈ Finset.univ.erase (pick 0) :=
    Finset.mem_erase.mpr ⟨hdistinct, Finset.mem_univ _⟩
  rw [← posDef_complementGap_iff_kernel_posDef design hsize pick hinjective,
    image_pick_two pick, compl_pair_eq_erase_erase]
  exact erase_strictDominates_iff_pivot_lt_one design
    (Finset.univ.erase (pick 0)) hbase hmember

/-- **RUNG THREE.**  The kernel gap of an omitted TRIPLE is positive definite
exactly when, from the base reached after erasing the first two labels, the
pivot of the third is below one. -/
theorem posDef_kernelGap_triple_iff_pivot_eraseTwo_lt_one
    (design : WeightedDesign size rank) (hsize : 2 ≤ size)
    (pick : Fin 3 → Fin size) (hinjective : Function.Injective pick)
    (hbase : (subsetSum design ((Finset.univ.erase (pick 0)).erase (pick 1)) - 1).PosDef) :
    (complementKernelGap design pick).PosDef
      ↔ pivot design ((Finset.univ.erase (pick 0)).erase (pick 1)) (pick 2) < 1 := by
  have hdistinctZero : pick 2 ≠ pick 0 := fun hcontra => by
    have : (2 : Fin 3) = 0 := hinjective hcontra
    exact absurd this (by decide)
  have hdistinctOne : pick 2 ≠ pick 1 := fun hcontra => by
    have : (2 : Fin 3) = 1 := hinjective hcontra
    exact absurd this (by decide)
  have hmember : pick 2 ∈ (Finset.univ.erase (pick 0)).erase (pick 1) :=
    Finset.mem_erase.mpr ⟨hdistinctOne,
      Finset.mem_erase.mpr ⟨hdistinctZero, Finset.mem_univ _⟩⟩
  rw [← posDef_complementGap_iff_kernel_posDef design hsize pick hinjective,
    image_pick_three pick, compl_triple_eq_erase_erase_erase]
  exact erase_strictDominates_iff_pivot_lt_one design
    ((Finset.univ.erase (pick 0)).erase (pick 1)) hbase hmember

/-- **THE LADDER IS THE LEADING MINORS.**  Once the ladder has descended two
rungs -- which is exactly the two positive definiteness hypotheses -- its third
rung test is the landed three-leading-minor test on one inverse-metric kernel. -/
theorem pivot_eraseTwo_lt_one_iff_kernel_leadingMinors
    (design : WeightedDesign size 3) (hsize : 2 ≤ size)
    (pick : Fin 3 → Fin size) (hinjective : Function.Injective pick)
    (hbase : (subsetSum design ((Finset.univ.erase (pick 0)).erase (pick 1)) - 1).PosDef) :
    pivot design ((Finset.univ.erase (pick 0)).erase (pick 1)) (pick 2) < 1
      ↔ 0 < 1 - complementKernel design pick 0 0
        ∧ 0 < (1 - complementKernel design pick 0 0)
              * (1 - complementKernel design pick 1 1)
            - complementKernel design pick 0 1 ^ 2
        ∧ 0 < (complementKernelGap design pick).det := by
  rw [← posDef_kernelGap_triple_iff_pivot_eraseTwo_lt_one design hsize pick hinjective hbase,
    ← posDef_complementGap_iff_kernel_posDef design hsize pick hinjective]
  exact posDef_complementGap_three_iff_kernel_rungs design hsize pick hinjective

/-! ### The kernel gap in closed form -/

/-- **THE COMPLEMENT KERNEL GAP IS MINUS THE INVERSE FULL GRAM GAP.**  Taking the
pick to be every label at once turns the whole domination lattice of a design
into the principal-minor structure of ONE `size x size` matrix, and that matrix
has a closed form: it is the negated inverse of `Gram - 1`, where `Gram` is the
ordinary Gram matrix of the atoms.

Nothing is derived here that is not already in the tree.  The push-through
identity `Gtz.transpose_mul_gapInv_mul_rectangle` supplies
`B^T (B B^T - 1)^-1 B = 1 + (B^T B - 1)^-1` and `Gtz.det_gramGap` supplies the
Weinstein-Aronszajn determinant shadow that makes the Gram gap invertible; what
was missing was the identification of the left side with the complement kernel.
Its consequences are worth stating because they are easy to rediscover: the
signature of the kernel gap is the reversed signature of the Gram gap, which is
`(rank, size - rank)` by `Gtz.gramGap_form_pos_of_range`,
`Gtz.gramGap_form_neg_of_kernel` and `Gtz.kernel_orthogonal_range`; and by
`Gtz.no_posSemidef_principal_of_diag_neg` and the two `inertiaNoGoMatrix`
witnesses, a signature alone never decides whether a positive semidefinite
principal block exists.  So the closed form is a coordinate statement and not a
route. -/
theorem complementKernelGap_id_eq_neg_inv_atomGramGap
    (design : WeightedDesign size rank) (hsize : 2 ≤ size) :
    complementKernelGap design (id : Fin size → Fin size)
      = -(selectedAtomRows design (id : Fin size → Fin size)
            * (selectedAtomRows design (id : Fin size → Fin size))ᵀ - 1)⁻¹ := by
  classical
  set rows := selectedAtomRows design (id : Fin size → Fin size) with hrows
  have hidInjective : Function.Injective (id : Fin size → Fin size) := fun _ _ hequal => hequal
  have himage : Finset.image (id : Fin size → Fin size) Finset.univ = Finset.univ := by
    ext label
    simp
  have hmoment : rowsᵀ * rows = subsetSum design Finset.univ := by
    rw [hrows, transpose_mul_selectedAtomRows design _ hidInjective, himage]
  have hmetric : complementKernelMetric design = rowsᵀ * rows - 1 := by
    rw [complementKernelMetric_eq_fullExcess, hmoment]
  have hmomentPosDef : (rowsᵀ * rows - 1).PosDef := by
    rw [hmoment]
    exact posDef_fullExcess design hsize
  have hmomentUnit : IsUnit ((rowsᵀ : Matrix (Fin rank) (Fin size) ℝ)
      * (rowsᵀ)ᵀ - 1).det := by
    rw [Matrix.transpose_transpose]
    exact isUnit_iff_ne_zero.mpr (ne_of_gt hmomentPosDef.det_pos)
  have hgramUnit : IsUnit (((rowsᵀ : Matrix (Fin rank) (Fin size) ℝ))ᵀ * rowsᵀ - 1).det := by
    rw [det_gramGap (rowsᵀ : Matrix (Fin rank) (Fin size) ℝ),
      Matrix.transpose_transpose]
    refine isUnit_iff_ne_zero.mpr (mul_ne_zero ?_ (ne_of_gt hmomentPosDef.det_pos))
    exact pow_ne_zero _ (by norm_num)
  have hpush := transpose_mul_gapInv_mul_rectangle
    (rowsᵀ : Matrix (Fin rank) (Fin size) ℝ) hmomentUnit hgramUnit
  rw [Matrix.transpose_transpose] at hpush
  have hkernel : complementKernel design (id : Fin size → Fin size)
      = 1 + (rows * rowsᵀ - 1)⁻¹ := by
    rw [complementKernel, hmetric, ← hrows]
    exact hpush
  rw [complementKernelGap, hkernel]
  abel

/-! ### The descent supply -/

/-- **THE DESCENT SLACK.**  The insiders' weighted excess exceeds the outsiders'
by exactly `rank + 1 - card`, at EVERY positive definite base.  The landed
`Gtz.excess_balance` is the `card = rank + 1` instance, where the term vanishes. -/
theorem excess_balance_with_cardinality_slack (design : WeightedDesign size rank)
    (base : Finset (Fin size)) (hbase : (subsetSum design base - 1).PosDef) :
    ∑ insider ∈ base, (1 - design.weight insider) * (pivot design base insider - 1)
      = (∑ outsider ∈ baseᶜ,
          design.weight outsider * (pivot design base outsider - 1))
        + ((rank : ℝ) + 1 - base.card) := by
  have htrace := trace_identity design base hbase
  have hweightTotal : ∑ insider ∈ base, design.weight insider
      + ∑ outsider ∈ baseᶜ, design.weight outsider = 1 := by
    rw [Finset.sum_add_sum_compl]
    exact design.weight_sum_one
  have hinsiderPeel :
      ∑ insider ∈ base, (1 - design.weight insider) * (pivot design base insider - 1)
        = (∑ insider ∈ base,
            (1 - design.weight insider) * pivot design base insider)
          - ∑ insider ∈ base, (1 - design.weight insider) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun insider _ => by ring
  have houtsiderPeel :
      ∑ outsider ∈ baseᶜ,
          design.weight outsider * (pivot design base outsider - 1)
        = (∑ outsider ∈ baseᶜ,
            design.weight outsider * pivot design base outsider)
          - ∑ outsider ∈ baseᶜ, design.weight outsider := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun outsider _ => by ring
  have hcoweight : ∑ insider ∈ base, (1 - design.weight insider)
      = (base.card : ℝ) - ∑ insider ∈ base, design.weight insider := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [hinsiderPeel, houtsiderPeel, hcoweight]
  linarith [htrace, hweightTotal]

/-- **THE DESCENT MOVE.**  When the outsiders' weighted excess stays strictly
below the slack, some insider erasure is STRICTLY dominating.  At
`card = rank + 1` the slack is zero and this is the strict twin of the landed
`Gtz.pigeonhole`; above it the hypothesis is strictly weaker. -/
theorem exists_erase_posDef_of_outsiderExcess_lt_slack
    (design : WeightedDesign size rank) (hsize : 2 ≤ size)
    (base : Finset (Fin size)) (hbase : (subsetSum design base - 1).PosDef)
    (hslack : ∑ outsider ∈ baseᶜ,
        design.weight outsider * (pivot design base outsider - 1)
      < (base.card : ℝ) - rank - 1) :
    ∃ insider ∈ base, (subsetSum design (base.erase insider) - 1).PosDef := by
  classical
  have hbalance := excess_balance_with_cardinality_slack design base hbase
  have hnegative :
      ∑ insider ∈ base, (1 - design.weight insider) * (pivot design base insider - 1)
        < 0 := by linarith
  by_contra hnone
  push Not at hnone
  have hnonneg : ∀ insider ∈ base,
      0 ≤ (1 - design.weight insider) * (pivot design base insider - 1) := by
    intro insider hinsider
    have hnotBelow : ¬ pivot design base insider < 1 := fun hbelow =>
      hnone insider hinsider
        ((erase_strictDominates_iff_pivot_lt_one design base hbase hinsider).mpr hbelow)
    rw [not_lt] at hnotBelow
    have hcoweight : 0 < 1 - design.weight insider := by
      have := weight_lt_one design hsize insider
      linarith
    exact mul_nonneg hcoweight.le (by linarith)
  exact absurd (Finset.sum_nonneg hnonneg) (not_le.mpr hnegative)

/-- **THE TOP RUNG IS ALWAYS A STRICT MOVE.**  At the full base there are no
outsiders, so the slack is all there is, and it is positive as soon as the design
carries more than `rank + 1` atoms.  The strict sharpening of
`Gtz.card_pivot_le_one_ge`. -/
theorem exists_erase_univ_posDef_of_succ_rank_lt_size
    (design : WeightedDesign size rank) (hsize : 2 ≤ size)
    (hrank : rank + 1 < size) :
    ∃ insider ∈ (Finset.univ : Finset (Fin size)),
      (subsetSum design (Finset.univ.erase insider) - 1).PosDef := by
  classical
  refine exists_erase_posDef_of_outsiderExcess_lt_slack design hsize Finset.univ
    (posDef_fullExcess design hsize) ?_
  have hempty : (Finset.univ : Finset (Fin size))ᶜ = (∅ : Finset (Fin size)) :=
    Finset.compl_univ
  rw [hempty, Finset.sum_empty, Finset.card_univ, Fintype.card_fin]
  have hcast : ((rank : ℝ) + 1) < (size : ℝ) := by exact_mod_cast hrank
  linarith

/-! ### Reachability, its failure, and the repair -/

/-- **THE PARSEVAL OUTSIDER LAW.**  A nonzero vector annihilated by the gap of a
subset is seen by some atom OUTSIDE that subset.  Reason: the gap's quadratic
form makes the insiders' co-weighted squared pairings vanish, and every
co-weight is strictly positive, so every INSIDER pairing vanishes too -- and then
Parseval, read at the empty base, says the vector has zero norm.

This is the reachability half of the descent's completeness: a weakly dominating
subset whose gap has corank ONE sits inside a strictly dominating subset one
label larger, because the added atom is not blind to the kernel line. -/
theorem exists_notMem_dotProduct_ne_zero_of_gap_mulVec_eq_zero
    (design : WeightedDesign size rank) (hsize : 2 ≤ size)
    (selected : Finset (Fin size)) {probe : Fin rank → ℝ} (hprobe : probe ≠ 0)
    (hkernel : (subsetSum design selected - 1) *ᵥ probe = 0) :
    ∃ outside, outside ∉ selected ∧ design.atom outside ⬝ᵥ probe ≠ 0 := by
  classical
  by_contra hnone
  push Not at hnone
  have houtsiderZero : ∀ label ∈ selectedᶜ,
      design.weight label * (design.atom label ⬝ᵥ probe) ^ 2 = 0 := by
    intro label hlabel
    rw [hnone label (Finset.mem_compl.mp hlabel)]
    ring
  have hselectedForm := dotProduct_subsetSum_sub_one_mulVec design selected probe
  rw [hkernel, dotProduct_zero, Finset.sum_congr rfl houtsiderZero,
    Finset.sum_const_zero, sub_zero] at hselectedForm
  have hinsiderZero : ∀ label ∈ selected, design.atom label ⬝ᵥ probe = 0 := by
    intro label hlabel
    have hterms : ∀ other ∈ selected,
        0 ≤ (1 - design.weight other) * (design.atom other ⬝ᵥ probe) ^ 2 := by
      intro other _
      have := weight_lt_one design hsize other
      have hsquare : (0 : ℝ) ≤ (design.atom other ⬝ᵥ probe) ^ 2 := sq_nonneg _
      nlinarith
    have hzero := (Finset.sum_eq_zero_iff_of_nonneg hterms).mp hselectedForm.symm label hlabel
    have hcoweight : 0 < 1 - design.weight label := by
      have := weight_lt_one design hsize label
      linarith
    have hsquare : (design.atom label ⬝ᵥ probe) ^ 2 = 0 := by
      rcases mul_eq_zero.mp hzero with hleft | hright
      · exact absurd hleft (ne_of_gt hcoweight)
      · exact hright
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsquare
  have hallZero : ∀ label ∈ (∅ : Finset (Fin size))ᶜ,
      design.weight label * (design.atom label ⬝ᵥ probe) ^ 2 = 0 := by
    intro label _
    by_cases hmem : label ∈ selected
    · rw [hinsiderZero label hmem]; ring
    · rw [hnone label hmem]; ring
  have hemptyForm := dotProduct_subsetSum_sub_one_mulVec design ∅ probe
  rw [Finset.sum_empty, Finset.sum_congr rfl hallZero, Finset.sum_const_zero,
    sub_zero, subsetSum, Finset.sum_empty, zero_sub, Matrix.neg_mulVec,
    Matrix.one_mulVec, dotProduct_neg] at hemptyForm
  have hnorm : probe ⬝ᵥ probe = 0 := by linarith
  exact hprobe (dotProduct_self_eq_zero.mp hnorm)

/-- **A KERNEL LINE ORTHOGONAL TO A CHOSEN ATOM.**  Two independent probes in the
kernel of a gap span a plane, and a plane meets the hyperplane orthogonal to any
single vector in at least a line.  Elementary, and it is the whole content of
"one rank-one atom closes at most one kernel dimension". -/
theorem exists_gapProbe_ne_zero_orthogonal_of_two_independent
    (design : WeightedDesign size rank) (selected : Finset (Fin size))
    {firstProbe secondProbe : Fin rank → ℝ}
    (hfirst : (subsetSum design selected - 1) *ᵥ firstProbe = 0)
    (hsecond : (subsetSum design selected - 1) *ᵥ secondProbe = 0)
    (hindependent : ∀ firstScalar secondScalar : ℝ,
      firstScalar • firstProbe + secondScalar • secondProbe = 0 →
        firstScalar = 0 ∧ secondScalar = 0)
    (target : Fin rank → ℝ) :
    ∃ probe : Fin rank → ℝ, probe ≠ 0
      ∧ (subsetSum design selected - 1) *ᵥ probe = 0
      ∧ target ⬝ᵥ probe = 0 := by
  have hfirstNe : firstProbe ≠ 0 := by
    intro hzero
    have hone : (1 : ℝ) = 0 :=
      (hindependent 1 0 (by rw [hzero]; simp)).1
    norm_num at hone
  by_cases htarget : target ⬝ᵥ firstProbe = 0
  · exact ⟨firstProbe, hfirstNe, hfirst, htarget⟩
  refine ⟨(target ⬝ᵥ firstProbe) • secondProbe - (target ⬝ᵥ secondProbe) • firstProbe,
    ?_, ?_, ?_⟩
  · intro hzero
    have hcombination :
        (-(target ⬝ᵥ secondProbe)) • firstProbe + (target ⬝ᵥ firstProbe) • secondProbe = 0 := by
      rw [neg_smul, ← hzero]
      abel
    exact htarget (hindependent _ _ hcombination).2
  · rw [Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul, hfirst, hsecond,
      smul_zero, smul_zero, sub_zero]
  · rw [dotProduct_sub, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    ring

/-- **THE DESCENT'S BLIND SPOT, PROVED.**  If the gap of a subset is annihilated
by two independent probes, then adjoining ANY single further atom leaves a gap
that is not positive definite.

A pivot descent computes a pivot only against a positive definite base, so it
reaches a subset only as the single-label erasure of a positive definite
superset.  This says no such superset exists: a dominating subset of corank two
or more is invisible from above, whatever tie-break rule the descent uses. -/
theorem not_posDef_gap_insert_of_two_independent_gapProbes
    (design : WeightedDesign size rank) (selected : Finset (Fin size))
    (extra : Fin size) (hextra : extra ∉ selected)
    {firstProbe secondProbe : Fin rank → ℝ}
    (hfirst : (subsetSum design selected - 1) *ᵥ firstProbe = 0)
    (hsecond : (subsetSum design selected - 1) *ᵥ secondProbe = 0)
    (hindependent : ∀ firstScalar secondScalar : ℝ,
      firstScalar • firstProbe + secondScalar • secondProbe = 0 →
        firstScalar = 0 ∧ secondScalar = 0) :
    ¬ (subsetSum design (insert extra selected) - 1).PosDef := by
  classical
  obtain ⟨probe, hprobeNe, hprobeKernel, hprobeOrthogonal⟩ :=
    exists_gapProbe_ne_zero_orthogonal_of_two_independent design selected hfirst hsecond
      hindependent (design.atom extra)
  intro hposDef
  have hsplit : subsetSum design (insert extra selected) - 1
      = atomMatrix (design.atom extra) + (subsetSum design selected - 1) := by
    rw [subsetSum, subsetSum, Finset.sum_insert hextra]
    abel
  have hform : probe ⬝ᵥ ((subsetSum design (insert extra selected) - 1) *ᵥ probe) = 0 := by
    rw [hsplit, Matrix.add_mulVec, dotProduct_add, hprobeKernel, dotProduct_zero,
      add_zero, atomMatrix, vecMulVec_mulVec_eq, dotProduct_smul, smul_eq_mul,
      hprobeOrthogonal, zero_mul]
  have hpositive := (Matrix.posDef_iff_dotProduct_mulVec.mp hposDef).2 hprobeNe
  rw [star_trivial] at hpositive
  exact absurd hform (ne_of_gt hpositive)

/-- **THE REPAIR.**  At a subset whose gap carries two independent probes both
halves hold at once: no single-label superset is positive definite, so no pivot
descent from above can reach the subset -- and the complement kernel decides its
domination anyway, because the kernel test inverts the full excess, which is
positive definite for every design of size at least two, and never inverts the
subset's own base.

The change of coordinates the weld buys is therefore exactly the repair of the
descent's incompleteness.  It still discharges nothing: both sides of the
equivalence are the same question, and the statement is about which algorithm
can ask it. -/
theorem kernelGap_decides_dominates_of_two_independent_gapProbes {omittedSize : ℕ}
    (design : WeightedDesign size rank) (hsize : 2 ≤ size)
    (pick : Fin omittedSize → Fin size) (hinjective : Function.Injective pick)
    {firstProbe secondProbe : Fin rank → ℝ}
    (hfirst : (subsetSum design (Finset.image pick Finset.univ)ᶜ - 1) *ᵥ firstProbe = 0)
    (hsecond : (subsetSum design (Finset.image pick Finset.univ)ᶜ - 1) *ᵥ secondProbe = 0)
    (hindependent : ∀ firstScalar secondScalar : ℝ,
      firstScalar • firstProbe + secondScalar • secondProbe = 0 →
        firstScalar = 0 ∧ secondScalar = 0) :
    (∀ extra, extra ∉ (Finset.image pick Finset.univ)ᶜ →
        ¬ (subsetSum design (insert extra (Finset.image pick Finset.univ)ᶜ) - 1).PosDef)
      ∧ (Dominates design (Finset.image pick Finset.univ)ᶜ
          ↔ (complementKernelGap design pick).PosSemidef) :=
  ⟨fun extra hextra =>
      not_posDef_gap_insert_of_two_independent_gapProbes design
        (Finset.image pick Finset.univ)ᶜ extra hextra hfirst hsecond hindependent,
    dominates_complement_iff_kernel_posSemidef design hsize pick hinjective⟩

end Gtz
