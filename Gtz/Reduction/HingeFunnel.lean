import Mathlib
import Gtz.Reduction.Reductions
import Gtz.Reduction.SplitTransfer
import Gtz.Reduction.StressSignSplit
import Gtz.Certificates.ResidueDissolution
import Gtz.LinAlg.SchurRankOne
import Gtz.Design.MarginTransfer
import Gtz.Core.Sanity
import Gtz.Reduction.CholeskyWhitening

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The hinge funnel and the (6,3) stress trichotomy

Two assemblies of landed machinery, no new hard mathematics.

**Part 1 (the funnel).**  The shipped `Gtz.dominating_of_parallel_pair` merges an
exactly parallel pair and pulls a dominating subset back up with NO quantitative
hypothesis; feeding it the decided `Gtz.gtzWeighted_of_le_five` closes every
`(6,3)` design carrying a parallel pair, and — conditionally on
`GtzWeighted 6 3` — every `(7,3)` design carrying one.  Contrapositives: every
counterexample at the two open cells is PARALLEL-FREE, and the hinge at `(6,3)`
is exactly the statement that no parallel-free tie exists.

**Part 2 (the trichotomy).**  The landed split law
(`Gtz.Reduction.StressSignSplit`) cuts the parallel-free landscape at `(6,3)`
into three kernel strata: (i) stress-free designs (six linearly independent
atom matrices), (ii) designs with a FULL-SUPPORT stress, which the split law
forces to split exactly `(3,3)` with a positive-definite middle matrix shared
by both sides, and (iii) designs whose every-nonzero-stress support is a
COPLANAR proper subfamily (a common nonzero orthogonal probe).  Stratum (ii)
is the two-frame normal-form entry point: whitening the middle matrix
(`Gtz.Reduction.CholeskyWhitening`) exhibits both stress sides as exact
Parseval triples in one common frame.
-/

namespace Gtz

open Matrix Finset

variable {n k : ℕ}

/-! ## Part 1: the parallel funnel -/

/-- **A `(6,3)` design with a parallel pair always dominates.**  Instantiation of
the shipped margin-free merge `Gtz.dominating_of_parallel_pair` at the decided
recursive cell `Gtz.gtzWeighted_of_le_five 5 3`. -/
theorem dominating_of_hasParallelPair_sixThree (design : WeightedDesign 6 3)
    (hpair : HasParallelPair design) :
    ∃ C : Finset (Fin 6), C.card = 3 ∧ Dominates design C := by
  obtain ⟨keptLabel, dropLabel, ratio, hdistinct, hparallel⟩ := hpair
  exact dominating_of_parallel_pair (m := 5) design
    (gtzWeighted_of_le_five 5 3 (by norm_num) (by norm_num)) hdistinct hparallel

/-- **Every `(6,3)` counterexample is parallel-free.**  Contrapositive of the
funnel: a design admitting no dominating triple carries no parallel pair. -/
theorem parallelFree_of_no_dominating_sixThree (design : WeightedDesign 6 3)
    (hnone : ∀ C : Finset (Fin 6), C.card = 3 → ¬ Dominates design C) :
    ¬ HasParallelPair design := by
  intro hpair
  obtain ⟨C, hcard, hdominates⟩ := dominating_of_hasParallelPair_sixThree design hpair
  exact hnone C hcard hdominates

/-- **The hinge at `(6,3)` is exactly "no parallel-free tie".**  The forward
direction is the definition read at a witness; the reverse is classical
contraposition.  Combined with `Gtz.gtzWeightedAll_three_of_hinge`, all of
rank three reduces to the emptiness of the parallel-free `(6,3)` tie locus. -/
theorem hingeHoldsAtSize_six_three_iff_no_parallelFree_tie :
    HingeHoldsAtSize 6 3
      ↔ ¬ ∃ design : WeightedDesign 6 3, IsTie design ∧ ¬ HasParallelPair design := by
  constructor
  · rintro hhinge ⟨design, htie, hnopair⟩
    exact hnopair (hhinge design htie)
  · intro hnone design htie
    by_contra hnopair
    exact hnone ⟨design, htie, hnopair⟩

/-- **A `(7,3)` design with a parallel pair dominates, given the `(6,3)` cell.**
The same shipped merge, one size up, consuming `GtzWeighted 6 3` as an explicit
hypothesis. -/
theorem sevenThree_dominating_of_hasParallelPair_of_sixThree
    (hsixThree : GtzWeighted 6 3) (design : WeightedDesign 7 3)
    (hpair : HasParallelPair design) :
    ∃ C : Finset (Fin 7), C.card = 3 ∧ Dominates design C := by
  obtain ⟨keptLabel, dropLabel, ratio, hdistinct, hparallel⟩ := hpair
  exact dominating_of_parallel_pair (m := 6) design hsixThree hdistinct hparallel

/-- Given the `(6,3)` cell, every `(7,3)` counterexample is parallel-free. -/
theorem sevenThree_parallelFree_of_no_dominating_of_sixThree
    (hsixThree : GtzWeighted 6 3) (design : WeightedDesign 7 3)
    (hnone : ∀ C : Finset (Fin 7), C.card = 3 → ¬ Dominates design C) :
    ¬ HasParallelPair design := by
  intro hpair
  obtain ⟨C, hcard, hdominates⟩ :=
    sevenThree_dominating_of_hasParallelPair_of_sixThree hsixThree design hpair
  exact hnone C hcard hdominates

/-! ## Part 2: the stress trichotomy at `(6,3)` -/

/-- The quadratic form of a coefficient combination over ANY index subset is the
coefficient-weighted sum of squared pairings — the finset-relative sibling of the
landed `Gtz.weighted_atomForm_eq`. -/
theorem weighted_atomForm_eq_on (selected : Finset (Fin n)) (coeff : Fin n → ℝ)
    (atomFamily : Fin n → Fin k → ℝ) (probe : Fin k → ℝ) :
    probe ⬝ᵥ ((∑ c ∈ selected, coeff c • atomMatrix (atomFamily c)) *ᵥ probe)
      = ∑ c ∈ selected, coeff c * (atomFamily c ⬝ᵥ probe) ^ 2 := by
  rw [Matrix.sum_mulVec, dotProduct_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, atom_form_eq_sq]

/-- **The `(6,3)` forced split is exactly `(3,3)`.**  A full-support stress of a
spanning six-family in rank three has at least three coordinates of each sign by
the landed split law, and six coordinates in all. -/
theorem sixThree_fullSupport_stress_splits_three_three
    (atomFamily : Fin 6 → Fin 3 → ℝ)
    (hspan : ∀ probe : Fin 3 → ℝ, (∀ c, atomFamily c ⬝ᵥ probe = 0) → probe = 0)
    {stressCoeff : Fin 6 → ℝ}
    (hstress : ∑ c, stressCoeff c • atomMatrix (atomFamily c) = 0)
    (hfull : ∀ c, stressCoeff c ≠ 0) :
    (Finset.univ.filter fun c => 0 < stressCoeff c).card = 3
      ∧ (Finset.univ.filter fun c => stressCoeff c < 0).card = 3 := by
  have hposCard := rank_le_card_pos_side atomFamily hspan hstress hfull
  have hnegCard := rank_le_card_neg_side atomFamily hspan hstress hfull
  have hdisjoint : Disjoint (Finset.univ.filter fun c => 0 < stressCoeff c)
      (Finset.univ.filter fun c => stressCoeff c < 0) := by
    rw [Finset.disjoint_left]
    intro c hcPos hcNeg
    exact absurd (Finset.mem_filter.mp hcNeg).2 (asymm (Finset.mem_filter.mp hcPos).2)
  have hcover : (Finset.univ.filter fun c => 0 < stressCoeff c)
      ∪ (Finset.univ.filter fun c => stressCoeff c < 0) = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro c
    rcases lt_or_lt_iff_ne.mpr (hfull c) with hlt | hgt
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ c, hlt⟩)
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ c, hgt⟩)
  have hsum : (Finset.univ.filter fun c => 0 < stressCoeff c).card
      + (Finset.univ.filter fun c => stressCoeff c < 0).card = 6 := by
    rw [← Finset.card_union_of_disjoint hdisjoint, hcover, Finset.card_univ,
      Fintype.card_fin]
  omega

/-- **A stress on fewer than `2k` atoms leaves a common orthogonal probe.**  If
the support of a stress has fewer than `2k` members, then one sign side has
fewer than `k` members, a probe annihilates that side by rank-nullity, and the
landed transfer law `Gtz.neg_side_orthogonal_of_pos_side` carries the
annihilation to the other side — so the probe is orthogonal to EVERY supported
atom.  This is the mechanism behind the coplanar stratum. -/
theorem exists_orthogonal_probe_of_support_card_lt
    (atomFamily : Fin n → Fin k → ℝ) {stressCoeff : Fin n → ℝ}
    (hstress : ∑ c, stressCoeff c • atomMatrix (atomFamily c) = 0)
    (hcard : (Finset.univ.filter fun c => stressCoeff c ≠ 0).card < 2 * k) :
    ∃ probe : Fin k → ℝ, probe ≠ 0
      ∧ ∀ c, stressCoeff c ≠ 0 → atomFamily c ⬝ᵥ probe = 0 := by
  have hdisjoint : Disjoint (Finset.univ.filter fun c => 0 < stressCoeff c)
      (Finset.univ.filter fun c => stressCoeff c < 0) := by
    rw [Finset.disjoint_left]
    intro c hcPos hcNeg
    exact absurd (Finset.mem_filter.mp hcNeg).2 (asymm (Finset.mem_filter.mp hcPos).2)
  have hunion : (Finset.univ.filter fun c => 0 < stressCoeff c)
      ∪ (Finset.univ.filter fun c => stressCoeff c < 0)
      = Finset.univ.filter fun c => stressCoeff c ≠ 0 := by
    ext c
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [or_comm]
    exact lt_or_lt_iff_ne
  have hcardSplit : (Finset.univ.filter fun c => 0 < stressCoeff c).card
      + (Finset.univ.filter fun c => stressCoeff c < 0).card
      = (Finset.univ.filter fun c => stressCoeff c ≠ 0).card := by
    rw [← Finset.card_union_of_disjoint hdisjoint, hunion]
  rcases Nat.lt_or_ge (Finset.univ.filter fun c => 0 < stressCoeff c).card k with
    hposSmall | hposLarge
  · obtain ⟨probe, hprobeNe, hprobeOrth⟩ := exists_ne_zero_orthogonal_of_card_lt
      atomFamily (Finset.univ.filter fun c => 0 < stressCoeff c) hposSmall
    have hposZero : ∀ c, 0 < stressCoeff c → atomFamily c ⬝ᵥ probe = 0 := fun c hc =>
      hprobeOrth c (Finset.mem_filter.mpr ⟨Finset.mem_univ c, hc⟩)
    have hnegZero := neg_side_orthogonal_of_pos_side hstress hposZero
    refine ⟨probe, hprobeNe, fun c hc => ?_⟩
    rcases lt_or_lt_iff_ne.mpr hc with hlt | hgt
    · exact hnegZero c hlt
    · exact hposZero c hgt
  · have hnegSmall : (Finset.univ.filter fun c => stressCoeff c < 0).card < k := by
      omega
    obtain ⟨probe, hprobeNe, hprobeOrth⟩ := exists_ne_zero_orthogonal_of_card_lt
      atomFamily (Finset.univ.filter fun c => stressCoeff c < 0) hnegSmall
    have hstressNeg : ∑ c, (-stressCoeff) c • atomMatrix (atomFamily c) = 0 := by
      have hpointwise : ∀ c ∈ Finset.univ,
          (-stressCoeff) c • atomMatrix (atomFamily c)
            = -(stressCoeff c • atomMatrix (atomFamily c)) := by
        intro c _
        rw [Pi.neg_apply, neg_smul]
      rw [Finset.sum_congr rfl hpointwise]
      simp [hstress]
    have hposZeroNeg : ∀ c, 0 < (-stressCoeff) c → atomFamily c ⬝ᵥ probe = 0 := by
      intro c hc
      rw [Pi.neg_apply] at hc
      exact hprobeOrth c (Finset.mem_filter.mpr ⟨Finset.mem_univ c, by linarith⟩)
    have hnegZeroNeg := neg_side_orthogonal_of_pos_side hstressNeg hposZeroNeg
    refine ⟨probe, hprobeNe, fun c hc => ?_⟩
    rcases lt_or_lt_iff_ne.mpr hc with hlt | hgt
    · exact hposZeroNeg c (by rw [Pi.neg_apply]; linarith)
    · exact hnegZeroNeg c (by rw [Pi.neg_apply]; linarith)

/-- **Full support or a coplanar support.**  At every cell with `n ≤ 2k` —
`(6,3)` in particular — a stress either has full support, or its supported
atoms admit a common nonzero orthogonal probe. -/
theorem stress_fullSupport_or_orthogonalProbe (hsize : n ≤ 2 * k)
    (atomFamily : Fin n → Fin k → ℝ) {stressCoeff : Fin n → ℝ}
    (hstress : ∑ c, stressCoeff c • atomMatrix (atomFamily c) = 0) :
    (∀ c, stressCoeff c ≠ 0)
      ∨ ∃ probe : Fin k → ℝ, probe ≠ 0
          ∧ ∀ c, stressCoeff c ≠ 0 → atomFamily c ⬝ᵥ probe = 0 := by
  by_cases hfull : ∀ c, stressCoeff c ≠ 0
  · exact Or.inl hfull
  · push Not at hfull
    obtain ⟨zeroLabel, hzeroLabel⟩ := hfull
    refine Or.inr (exists_orthogonal_probe_of_support_card_lt atomFamily hstress ?_)
    have hsubset : (Finset.univ.filter fun c => stressCoeff c ≠ 0)
        ⊆ Finset.univ.erase zeroLabel := by
      intro c hc
      refine Finset.mem_erase.mpr ⟨fun hEq => ?_, Finset.mem_univ c⟩
      exact (Finset.mem_filter.mp hc).2 (hEq ▸ hzeroLabel)
    have hle := Finset.card_le_card hsubset
    have hErase : (Finset.univ.erase zeroLabel).card = n - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ zeroLabel), Finset.card_univ,
        Fintype.card_fin]
    have hpos : 0 < n := zeroLabel.pos
    omega

/-- **The stress rearranged**: the positive side's weighted atom sum equals the
negative side's, with the absolute coefficients — the shared middle matrix of
the two-frame picture. -/
theorem posSide_sum_eq_negSide_sum (atomFamily : Fin n → Fin k → ℝ)
    {stressCoeff : Fin n → ℝ}
    (hstress : ∑ c, stressCoeff c • atomMatrix (atomFamily c) = 0)
    (hfull : ∀ c, stressCoeff c ≠ 0) :
    ∑ c ∈ Finset.univ.filter (fun c => 0 < stressCoeff c),
        stressCoeff c • atomMatrix (atomFamily c)
      = ∑ c ∈ Finset.univ.filter (fun c => stressCoeff c < 0),
          (-stressCoeff c) • atomMatrix (atomFamily c) := by
  have hdisjoint : Disjoint (Finset.univ.filter fun c => 0 < stressCoeff c)
      (Finset.univ.filter fun c => stressCoeff c < 0) := by
    rw [Finset.disjoint_left]
    intro c hcPos hcNeg
    exact absurd (Finset.mem_filter.mp hcNeg).2 (asymm (Finset.mem_filter.mp hcPos).2)
  have hcover : (Finset.univ.filter fun c => 0 < stressCoeff c)
      ∪ (Finset.univ.filter fun c => stressCoeff c < 0) = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro c
    rcases lt_or_lt_iff_ne.mpr (hfull c) with hlt | hgt
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ c, hlt⟩)
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ c, hgt⟩)
  have hsplit : ∑ c ∈ Finset.univ.filter (fun c => 0 < stressCoeff c),
        stressCoeff c • atomMatrix (atomFamily c)
      + ∑ c ∈ Finset.univ.filter (fun c => stressCoeff c < 0),
          stressCoeff c • atomMatrix (atomFamily c) = 0 := by
    rw [← Finset.sum_union hdisjoint, hcover]
    exact hstress
  have hneg : ∑ c ∈ Finset.univ.filter (fun c => stressCoeff c < 0),
        (-stressCoeff c) • atomMatrix (atomFamily c)
      = -∑ c ∈ Finset.univ.filter (fun c => stressCoeff c < 0),
          stressCoeff c • atomMatrix (atomFamily c) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun c _ => by rw [neg_smul]
  rw [hneg]
  exact eq_neg_of_add_eq_zero_left hsplit

/-- **The positive side of a full-support stress is positive definite.**  Its
quadratic form is a positively weighted sum of squared pairings, and the landed
`Gtz.pos_side_spans` says no nonzero probe annihilates the positive side. -/
theorem posDef_posSide_sum (atomFamily : Fin n → Fin k → ℝ)
    (hspan : ∀ probe : Fin k → ℝ, (∀ c, atomFamily c ⬝ᵥ probe = 0) → probe = 0)
    {stressCoeff : Fin n → ℝ}
    (hstress : ∑ c, stressCoeff c • atomMatrix (atomFamily c) = 0)
    (hfull : ∀ c, stressCoeff c ≠ 0) :
    (∑ c ∈ Finset.univ.filter (fun c => 0 < stressCoeff c),
        stressCoeff c • atomMatrix (atomFamily c)).PosDef := by
  have hsymm : (∑ c ∈ Finset.univ.filter (fun c => 0 < stressCoeff c),
      stressCoeff c • atomMatrix (atomFamily c))ᵀ
      = ∑ c ∈ Finset.univ.filter (fun c => 0 < stressCoeff c),
          stressCoeff c • atomMatrix (atomFamily c) := by
    rw [Matrix.transpose_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Matrix.transpose_smul,
      transpose_eq_of_isHermitian (posSemidef_atomMatrix (atomFamily c)).1]
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr
    ⟨isHermitian_of_transpose_eq hsymm, fun probe hprobe => ?_⟩
  rw [star_trivial, weighted_atomForm_eq_on]
  have hterms : ∀ c ∈ Finset.univ.filter (fun c => 0 < stressCoeff c),
      0 ≤ stressCoeff c * (atomFamily c ⬝ᵥ probe) ^ 2 := fun c hc =>
    mul_nonneg (Finset.mem_filter.mp hc).2.le (sq_nonneg _)
  have hwitness : ∃ c ∈ Finset.univ.filter (fun c => 0 < stressCoeff c),
      0 < stressCoeff c * (atomFamily c ⬝ᵥ probe) ^ 2 := by
    have hoverlap : ∃ c, 0 < stressCoeff c ∧ atomFamily c ⬝ᵥ probe ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hprobe (pos_side_spans atomFamily hspan hstress hfull probe hcon)
    obtain ⟨c, hcPos, hcOverlap⟩ := hoverlap
    refine ⟨c, Finset.mem_filter.mpr ⟨Finset.mem_univ c, hcPos⟩, mul_pos hcPos ?_⟩
    exact (sq_nonneg _).lt_of_ne (Ne.symm (pow_ne_zero 2 hcOverlap))
  exact Finset.sum_pos' hterms hwitness

/-- **THE `(6,3)` STRESS TRICHOTOMY.**  Every weighted `(6,3)` design falls into
at least one of three kernel strata:

(i) **stress-free** — the six atom matrices are linearly independent;

(ii) **balanced** — some FULL-SUPPORT stress exists; it splits exactly `(3,3)`
by sign, the positive side's weighted atom sum is POSITIVE DEFINITE, and it
equals the negative side's sum with the absolute coefficients — one middle
matrix presenting the design's two halves as a pair of frames;

(iii) **degenerate** — some nonzero stress is supported on a proper subfamily
admitting a common nonzero orthogonal probe (a coplanar subfamily).

Stratum (i) excludes (ii) and (iii) outright; (ii) and (iii) may coexist when
the stress space has dimension above one, so the statement is a covering
disjunction, which is what the primitive-tie exclusion consumes. -/
theorem sixThree_stress_trichotomy (design : WeightedDesign 6 3) :
    (∀ stressCoeff : Fin 6 → ℝ,
        (∑ c, stressCoeff c • atomMatrix (design.atom c)) = 0 → stressCoeff = 0)
    ∨ (∃ stressCoeff : Fin 6 → ℝ,
        (∑ c, stressCoeff c • atomMatrix (design.atom c)) = 0
        ∧ (∀ c, stressCoeff c ≠ 0)
        ∧ (Finset.univ.filter fun c => 0 < stressCoeff c).card = 3
        ∧ (Finset.univ.filter fun c => stressCoeff c < 0).card = 3
        ∧ (∑ c ∈ Finset.univ.filter (fun c => 0 < stressCoeff c),
            stressCoeff c • atomMatrix (design.atom c)).PosDef
        ∧ ∑ c ∈ Finset.univ.filter (fun c => 0 < stressCoeff c),
            stressCoeff c • atomMatrix (design.atom c)
          = ∑ c ∈ Finset.univ.filter (fun c => stressCoeff c < 0),
              (-stressCoeff c) • atomMatrix (design.atom c))
    ∨ (∃ (stressCoeff : Fin 6 → ℝ) (probe : Fin 3 → ℝ),
        stressCoeff ≠ 0 ∧ probe ≠ 0
        ∧ (∑ c, stressCoeff c • atomMatrix (design.atom c)) = 0
        ∧ ∀ c, stressCoeff c ≠ 0 → design.atom c ⬝ᵥ probe = 0) := by
  by_cases hindependent : ∀ stressCoeff : Fin 6 → ℝ,
      (∑ c, stressCoeff c • atomMatrix (design.atom c)) = 0 → stressCoeff = 0
  · exact Or.inl hindependent
  · push Not at hindependent
    obtain ⟨stressCoeff, hstress, hstressNe⟩ := hindependent
    have hspan : ∀ probe : Fin 3 → ℝ, (∀ c, design.atom c ⬝ᵥ probe = 0) → probe = 0 :=
      fun probe hprobe => weightedDesign_atoms_span design hprobe
    rcases stress_fullSupport_or_orthogonalProbe (by norm_num) design.atom hstress with
      hfull | ⟨probe, hprobeNe, hprobeOrth⟩
    · obtain ⟨hposCard, hnegCard⟩ :=
        sixThree_fullSupport_stress_splits_three_three design.atom hspan hstress hfull
      exact Or.inr (Or.inl ⟨stressCoeff, hstress, hfull, hposCard, hnegCard,
        posDef_posSide_sum design.atom hspan hstress hfull,
        posSide_sum_eq_negSide_sum design.atom hstress hfull⟩)
    · exact Or.inr (Or.inr ⟨stressCoeff, probe, hstressNe, hprobeNe, hstress, hprobeOrth⟩)

/-! ## Part 3: the two-frame normal form (whitening the balanced stratum) -/

/-- **Three rank-ones summing to the identity in `ℝ³` form an orthonormal
triple.**  The matrix with the three vectors as columns satisfies `B Bᵀ = 1`,
hence `Bᵀ B = 1` in a square matrix ring, which reads off pairwise
orthonormality. -/
theorem orthonormal_of_three_rank_ones_sum_one (frameVec : Fin 3 → Fin 3 → ℝ)
    (hsum : ∑ index, Matrix.vecMulVec (frameVec index) (frameVec index)
      = (1 : Matrix (Fin 3) (Fin 3) ℝ)) (leftIdx rightIdx : Fin 3) :
    frameVec leftIdx ⬝ᵥ frameVec rightIdx = if leftIdx = rightIdx then 1 else 0 := by
  have hright : (Matrix.of fun row col => frameVec col row)
      * (Matrix.of fun row col => frameVec col row)ᵀ = 1 := by
    ext row col
    have hentry : (∑ index, Matrix.vecMulVec (frameVec index) (frameVec index)) row col
        = (1 : Matrix (Fin 3) (Fin 3) ℝ) row col := by rw [hsum]
    rw [Matrix.sum_apply] at hentry
    rw [Matrix.mul_apply, ← hentry]
    refine Finset.sum_congr rfl fun index _ => ?_
    rw [Matrix.transpose_apply, Matrix.vecMulVec_apply]
    simp only [Matrix.of_apply]
  have hleft := mul_eq_one_comm.mp hright
  have hentry : ((Matrix.of fun row col => frameVec col row)ᵀ
      * (Matrix.of fun row col => frameVec col row)) leftIdx rightIdx
      = (1 : Matrix (Fin 3) (Fin 3) ℝ) leftIdx rightIdx := by rw [hleft]
  rw [Matrix.mul_apply, Matrix.one_apply] at hentry
  rw [← hentry]
  simp only [dotProduct]
  refine Finset.sum_congr rfl fun row _ => ?_
  rw [Matrix.transpose_apply]
  simp only [Matrix.of_apply]

/-- **The balanced stratum's middle matrix admits an explicit whitener** — the
landed 3×3 Cholesky machinery, no square roots of matrices: an invertible
`whitener` with `whitener * X * whitenerᵀ = 1` for the positive side sum `X`.
In whitened coordinates each stress side becomes an exact Parseval triple, and
`Gtz.orthonormal_of_three_rank_ones_sum_one` turns the positive side into an
orthonormal frame. -/
theorem exists_whitening_of_positiveSide (design : WeightedDesign 6 3)
    {stressCoeff : Fin 6 → ℝ}
    (hstress : ∑ c, stressCoeff c • atomMatrix (design.atom c) = 0)
    (hfull : ∀ c, stressCoeff c ≠ 0) :
    ∃ whitener : Matrix (Fin 3) (Fin 3) ℝ, whitener.det ≠ 0
      ∧ whitener * (∑ c ∈ Finset.univ.filter (fun c => 0 < stressCoeff c),
          stressCoeff c • atomMatrix (design.atom c)) * whitenerᵀ = 1 := by
  have hspan : ∀ probe : Fin 3 → ℝ, (∀ c, design.atom c ⬝ᵥ probe = 0) → probe = 0 :=
    fun probe hprobe => weightedDesign_atoms_span design hprobe
  have hpd := posDef_posSide_sum design.atom hspan hstress hfull
  have hsymm : (∑ c ∈ Finset.univ.filter (fun c => 0 < stressCoeff c),
      stressCoeff c • atomMatrix (design.atom c))ᵀ
      = ∑ c ∈ Finset.univ.filter (fun c => 0 < stressCoeff c),
          stressCoeff c • atomMatrix (design.atom c) := by
    rw [Matrix.transpose_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Matrix.transpose_smul,
      transpose_eq_of_isHermitian (posSemidef_atomMatrix (design.atom c)).1]
  have hsymmEntry : ∀ leftIdx rightIdx : Fin 3,
      (∑ c ∈ Finset.univ.filter (fun c => 0 < stressCoeff c),
        stressCoeff c • atomMatrix (design.atom c)) leftIdx rightIdx
      = (∑ c ∈ Finset.univ.filter (fun c => 0 < stressCoeff c),
          stressCoeff c • atomMatrix (design.atom c)) rightIdx leftIdx := by
    intro leftIdx rightIdx
    have happlied := congrFun (congrFun hsymm rightIdx) leftIdx
    rwa [Matrix.transpose_apply] at happlied
  exact ⟨whitenMatrix _,
    whitenMatrix_det_ne_zero hpd (hsymmEntry 0 1) (hsymmEntry 0 2) (hsymmEntry 1 2),
    sandwich_eq_one
      (cholOf_mul_transpose hpd (hsymmEntry 0 1) (hsymmEntry 0 2) (hsymmEntry 1 2))
      (whitenMatrix_mul_cholOf hpd (hsymmEntry 0 1) (hsymmEntry 0 2) (hsymmEntry 1 2))⟩

/-- **Whitening a weighted atom sum whitens each atom.**  If a congruence by
`whitener` carries a selected weighted atom sum to the identity, the transported
atoms form an exact weighted Parseval family — the landed rank-one congruence
`Gtz.atomMatrix_conj` summed over the selection. -/
theorem whitened_sum_parseval {count : ℕ} (selected : Finset (Fin count))
    (coeff : Fin count → ℝ) (atomFamily : Fin count → Fin 3 → ℝ)
    {whitener : Matrix (Fin 3) (Fin 3) ℝ}
    (hsandwich : whitener * (∑ atomLabel ∈ selected,
        coeff atomLabel • atomMatrix (atomFamily atomLabel)) * whitenerᵀ = 1) :
    ∑ atomLabel ∈ selected,
        coeff atomLabel • atomMatrix (whitener *ᵥ atomFamily atomLabel) = 1 := by
  calc ∑ atomLabel ∈ selected,
        coeff atomLabel • atomMatrix (whitener *ᵥ atomFamily atomLabel)
      = ∑ atomLabel ∈ selected,
          whitener * (coeff atomLabel • atomMatrix (atomFamily atomLabel))
            * whitenerᵀ := by
        refine Finset.sum_congr rfl fun atomLabel _ => ?_
        rw [atomMatrix_conj, Matrix.mul_smul, Matrix.smul_mul]
    _ = whitener * (∑ atomLabel ∈ selected,
          coeff atomLabel • atomMatrix (atomFamily atomLabel)) * whitenerᵀ := by
        rw [Finset.mul_sum, Finset.sum_mul]
    _ = 1 := hsandwich

/-- **THE TWO-FRAME NORMAL FORM.**  In the balanced stratum, whitening the
positive side's middle matrix turns that side into an exact orthonormal frame
of `ℝ³`: for any enumeration of the three positive-sign atoms, the vectors
`√(stress) • (whitener *ᵥ atom)` are pairwise orthonormal.  Assembly of
`Gtz.exists_whitening_of_positiveSide`, the smul law `Gtz.atomMatrix_smul`,
the congruence `Gtz.atomMatrix_conj`, and
`Gtz.orthonormal_of_three_rank_ones_sum_one`. -/
theorem twoFrame_normalForm (design : WeightedDesign 6 3)
    {stressCoeff : Fin 6 → ℝ}
    (hstress : ∑ atomLabel, stressCoeff atomLabel
      • atomMatrix (design.atom atomLabel) = 0)
    (hfull : ∀ atomLabel, stressCoeff atomLabel ≠ 0)
    (posEnum : Fin 3 → Fin 6) (hasInjectiveEnum : Function.Injective posEnum)
    (henumPos : ∀ frameIdx, 0 < stressCoeff (posEnum frameIdx))
    (henumOnto : ∀ atomLabel, 0 < stressCoeff atomLabel
      → ∃ frameIdx, posEnum frameIdx = atomLabel) :
    ∃ whitener : Matrix (Fin 3) (Fin 3) ℝ, whitener.det ≠ 0
      ∧ ∀ leftIdx rightIdx : Fin 3,
          (Real.sqrt (stressCoeff (posEnum leftIdx))
              • (whitener *ᵥ design.atom (posEnum leftIdx)))
            ⬝ᵥ (Real.sqrt (stressCoeff (posEnum rightIdx))
              • (whitener *ᵥ design.atom (posEnum rightIdx)))
          = if leftIdx = rightIdx then 1 else 0 := by
  obtain ⟨whitener, hdetNe, hsandwich⟩ :=
    exists_whitening_of_positiveSide design hstress hfull
  refine ⟨whitener, hdetNe, ?_⟩
  have hterm : ∀ frameIdx : Fin 3,
      Matrix.vecMulVec
        (Real.sqrt (stressCoeff (posEnum frameIdx))
          • (whitener *ᵥ design.atom (posEnum frameIdx)))
        (Real.sqrt (stressCoeff (posEnum frameIdx))
          • (whitener *ᵥ design.atom (posEnum frameIdx)))
      = stressCoeff (posEnum frameIdx)
          • atomMatrix (whitener *ᵥ design.atom (posEnum frameIdx)) := by
    intro frameIdx
    show atomMatrix _ = _
    rw [atomMatrix_smul, Real.sq_sqrt (henumPos frameIdx).le]
  have hreindex : ∑ frameIdx : Fin 3, stressCoeff (posEnum frameIdx)
        • atomMatrix (whitener *ᵥ design.atom (posEnum frameIdx))
      = ∑ atomLabel ∈ Finset.univ.filter (fun atomLabel => 0 < stressCoeff atomLabel),
          stressCoeff atomLabel • atomMatrix (whitener *ᵥ design.atom atomLabel) := by
    refine Finset.sum_bij (fun frameIdx _ => posEnum frameIdx)
      (fun frameIdx _ => Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, henumPos frameIdx⟩)
      (fun leftIdx _ rightIdx _ hEq => hasInjectiveEnum hEq)
      (fun atomLabel hmem => ?_) (fun frameIdx _ => rfl)
    obtain ⟨frameIdx, hframeIdx⟩ :=
      henumOnto atomLabel (Finset.mem_filter.mp hmem).2
    exact ⟨frameIdx, Finset.mem_univ frameIdx, hframeIdx⟩
  have hframeSum : ∑ frameIdx : Fin 3, Matrix.vecMulVec
      (Real.sqrt (stressCoeff (posEnum frameIdx))
        • (whitener *ᵥ design.atom (posEnum frameIdx)))
      (Real.sqrt (stressCoeff (posEnum frameIdx))
        • (whitener *ᵥ design.atom (posEnum frameIdx))) = 1 :=
    (Finset.sum_congr rfl fun frameIdx _ => hterm frameIdx).trans
      (hreindex.trans (whitened_sum_parseval _ _ _ hsandwich))
  exact orthonormal_of_three_rank_ones_sum_one
    (fun frameIdx => Real.sqrt (stressCoeff (posEnum frameIdx))
      • (whitener *ᵥ design.atom (posEnum frameIdx))) hframeSum

end Gtz
