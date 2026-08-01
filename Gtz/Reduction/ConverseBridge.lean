/-
# The missing converse: classical GTZ implies the weighted form

The campaign's bridge `Gtz.original_of_weighted_single` runs ONE way — weighted GTZ at
size `n` gives the 1997 statement at `n` — via `Gtz.rowDesign`, which sends an
orthonormal-column matrix to the design with UNIFORM weights `1/n`.  Nothing in the tree
runs the other way, so a weighted counterexample at `(6,3)` did not, in the kernel,
refute the 1997 conjecture.  This file supplies the arrow, and upgrades the frame to an
equivalence:

    GtzWeightedAll k  ↔  ∀ n, 0 < n → GtzOriginal n k     (`gtzWeightedAll_iff_forall_gtzOriginal`)

and in counterexample form: a failing `(m,k)` design manufactures an explicit `N` and an
`N × k` orthonormal-column matrix no `k`-row pick of which reaches `σ_min ≥ 1/√N`
(`exists_not_gtzOriginal_of_forall_not_dominates`).

Downstream, the campaign's rank-three termini stop being sufficient conditions and become
CHARACTERISATIONS of the 1997 conjecture:
`isEmpty_sixThreeCrux_iff_gtzOriginal_rank_three`,
`forall_not_isSixThreeRefutationCandidateSharp_iff_gtzOriginal_rank_three`,
`gtzWeighted_six_three_iff_forall_gtzOriginal_rank_three`.

## The four steps

1. **Rounding** (`exists_multiplicityWeights_of_forall_not_dominates`).  Non-domination
   of a `k`-subset is a STRICT inequality `Σ_{c∈C}(g_c·x)² < |x|²` at a witness `x`
   (`Gtz.dominationGap_form`).  There are finitely many subsets, so finitely many strict
   inequalities, each with a positive gap.  Rounding the weights to `⌊n t_c⌋ / Σ⌊n t_c⌋`
   moves each one by at most a fixed constant `Σ_c |b_c − a|`, so ONE archimedean choice
   of `n` preserves all of them at once, together with positive definiteness of the
   frame operator.  This is the only analytic step in the file, and it is elementary:
   no continuity, no compactness, no Lipschitz constant.  In particular the tree's
   `Gtz.continuous_designMargin` / `Gtz.continuous_dominationMargin` machinery is NOT
   used anywhere in this file; whether a topological route would also close is untested.

2. **Whitening** (`exists_design_of_frame`).  Rounded weights break Parseval.  Any
   invertible congruence `R` with `Rᵀ F R = I` (`Gtz.exists_congruence_to_one`, applied
   to the frame operator `F`) repairs it, and — because `Gtz.Dominates` is a congruence
   statement — the repaired design's domination is exactly the RAW Loewner comparison
   `S_C ⪰ F` of the unwhitened atoms.  No matrix square root is built and no continuity
   in `R` is needed: any congruence works, since the congruence cancels on both sides.
   The design and its moment identity are the shipped `Gtz.whitenedFamilyDesign`,
   `Gtz.whitenedDesign_subsetSum_eq` and `Gtz.sum_atomMatrix_conj`; only the domination
   equivalence, and the weakening of the hypothesis from `Gtz.FrameOperatorIsPinched` to
   bare positive definiteness, are new.

3. **Replication** (`uniformReplication`).  A design whose weights are the fractions
   `p_c / N` becomes the `N`-atom design repeating atom `c` exactly `p_c` times at the
   flat weight `1/N`.  This is `Gtz.replicatedDesign` (one atom halved) carried out at
   arbitrary integer multiplicities all the way to the flat weight.  A `k`-subset of the
   replica either repeats an atom — killed by the shipped
   `Gtz.not_dominates_of_repeated_atom_general` — or is a faithful copy of a `k`-subset
   of the original.  So replication creates no dominator.

4. **Reading off the matrix** (`exists_dominates_of_gtzOriginal_uniform`).  On the
   uniform slice the bridge is already an equivalence in the tree: `Gtz.scaledAtomRows`
   inverts `Gtz.rowDesign` and `Gtz.transpose_mul_scaledAtomRows` says its columns are
   orthonormal.  A `k`-row pick is injective, hence enumerates a genuine `k`-subset —
   the duplicate-pick bookkeeping is already spent in step 3 — and
   `BᵀB − (1/N)·I = (1/N)·(S_C − I)` transfers the decision by positive scaling.

## Honest scope

The construction is size-changing: a counterexample at `(m,k)` produces one at `(N,k)`
for an `N` the archimedean step chooses (only `N ≥ m` is guaranteed), not at `n = m`.
That is all the equivalence needs, since `GtzWeightedAll k` and `∀ n, GtzOriginal n k`
both quantify over all sizes.  NOTHING here proves or disproves a fixed-size arrow
`GtzOriginal n k → GtzWeighted n k`; the classical statement's uniform weights make one
look unlikely without new input, but that is an opinion, not a theorem.

The `N` is not effective in any useful sense: it is `Σ_c ⌊scale · t_c⌋` for a `scale`
produced by `exists_nat_gt` off the per-gate ratios `slack/gapValue`, so extracting it
numerically would need those ratios at the actual counterexample.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Core.Sanity
import Gtz.LinAlg.PsdKit
import Gtz.LinAlg.ProjectionForm
import Gtz.Design.MarginTransfer
import Gtz.Reduction.Reductions
import Gtz.Reduction.RankFourWindow
import Gtz.Reduction.RayleighCertificate
import Gtz.Reduction.RealVolumeFloor
import Gtz.Reduction.StressWalk
import Gtz.Quantitative.SixThreeCrux
import Gtz.Quantitative.SixThreeFrontierSharp

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

variable {m k : ℕ}

/-! ## Raw atom families: the frame operator and the subset moment -/

/-- The frame operator `Σ_c w_c g_c g_cᵀ` of a raw atom family at a weight vector.
Equals `1` exactly when the pair is a design (`WeightedDesign.isParseval`). -/
def frameOperatorOfAtoms (atomFamily : Fin m → Fin k → ℝ) (weight : Fin m → ℝ) :
    Matrix (Fin k) (Fin k) ℝ :=
  ∑ c, weight c • atomMatrix (atomFamily c)

/-- The unweighted moment `Σ_{c∈C} g_c g_cᵀ` of a subset of a raw atom family — the
weight-free datum `Gtz.subsetSum` reads off a design. -/
def subsetSumOfAtoms (atomFamily : Fin m → Fin k → ℝ) (selected : Finset (Fin m)) :
    Matrix (Fin k) (Fin k) ℝ :=
  ∑ c ∈ selected, atomMatrix (atomFamily c)

theorem transpose_subsetSumOfAtoms (atomFamily : Fin m → Fin k → ℝ)
    (selected : Finset (Fin m)) :
    (subsetSumOfAtoms atomFamily selected)ᵀ = subsetSumOfAtoms atomFamily selected :=
  transpose_eq_of_isHermitian
    (Matrix.posSemidef_sum selected fun c _ => posSemidef_atomMatrix (atomFamily c)).1

theorem transpose_frameOperatorOfAtoms (atomFamily : Fin m → Fin k → ℝ)
    {weight : Fin m → ℝ} (hnonneg : ∀ c, 0 ≤ weight c) :
    (frameOperatorOfAtoms atomFamily weight)ᵀ = frameOperatorOfAtoms atomFamily weight :=
  transpose_eq_of_isHermitian
    (Matrix.posSemidef_sum Finset.univ fun c _ =>
      (posSemidef_atomMatrix (atomFamily c)).smul (hnonneg c)).1

/-- The quadratic form of a frame operator is the weighted sum of squared overlaps. -/
theorem form_frameOperatorOfAtoms (atomFamily : Fin m → Fin k → ℝ) (weight : Fin m → ℝ)
    (probe : Fin k → ℝ) :
    probe ⬝ᵥ (frameOperatorOfAtoms atomFamily weight *ᵥ probe)
      = ∑ c, weight c * (atomFamily c ⬝ᵥ probe) ^ 2 := by
  rw [frameOperatorOfAtoms, Matrix.sum_mulVec, dotProduct_sum]
  exact Finset.sum_congr rfl fun c _ => by
    rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, atom_form_eq_sq]

/-- The quadratic form of a raw subset moment — `Gtz.subsetSum_form_eq_sum_sq` off a
design. -/
theorem form_subsetSumOfAtoms (atomFamily : Fin m → Fin k → ℝ)
    (selected : Finset (Fin m)) (probe : Fin k → ℝ) :
    probe ⬝ᵥ (subsetSumOfAtoms atomFamily selected *ᵥ probe)
      = ∑ c ∈ selected, (atomFamily c ⬝ᵥ probe) ^ 2 := by
  rw [subsetSumOfAtoms, Matrix.sum_mulVec, dotProduct_sum]
  exact Finset.sum_congr rfl fun c _ => atom_form_eq_sq (atomFamily c) probe

/-! ## Step 2: whitening a positive frame into a design -/

/-- **Whitening.**  A positive weight vector whose frame operator is positive definite
becomes a genuine `WeightedDesign` after ONE invertible congruence of the atoms, and —
because `Gtz.Dominates` is a congruence statement — domination of the whitened design is
exactly the raw Loewner comparison `S_C ⪰ F`.  No matrix square root anywhere: the
congruence cancels on both sides of the comparison, so any `R` from
`Gtz.exists_congruence_to_one` serves.

The design itself is the shipped `Gtz.whitenedFamilyDesign`, and the moment identity is
the shipped `Gtz.sum_atomMatrix_conj` read through `Gtz.whitenedDesign_subsetSum_eq`;
what is new here is only the DOMINATION EQUIVALENCE, and the hypothesis, which is bare
positive definiteness rather than the pinch `Gtz.FrameOperatorIsPinched` that
`Gtz.exists_whitenedDesign_of_framePinched` demands (a frame operator with spectrum
`{1/10, 5}` is positive definite but pinched only at `etaBound ≥ 4`). -/
theorem exists_design_of_frame (atomFamily : Fin m → Fin k → ℝ) (weight : Fin m → ℝ)
    (hpos : ∀ c, 0 < weight c) (hsum : ∑ c, weight c = 1)
    (hframePD : (frameOperatorOfAtoms atomFamily weight).PosDef) :
    ∃ D : WeightedDesign m k, D.weight = weight ∧
      ∀ selected : Finset (Fin m), Dominates D selected ↔
        (subsetSumOfAtoms atomFamily selected
          - frameOperatorOfAtoms atomFamily weight).PosSemidef := by
  obtain ⟨congruence, hunit, hcongr⟩ := exists_congruence_to_one hframePD
  have hwhiten : congruenceᵀ * (∑ c, weight c • atomMatrix (atomFamily c)) * congruence = 1 :=
    hcongr
  refine ⟨whitenedFamilyDesign atomFamily weight hpos hsum congruence hwhiten, rfl,
    fun selected => ?_⟩
  have hmoment : subsetSum
      (whitenedFamilyDesign atomFamily weight hpos hsum congruence hwhiten) selected
      = congruenceᵀ * subsetSumOfAtoms atomFamily selected * congruence := by
    rw [whitenedDesign_subsetSum_eq, sum_atomMatrix_conj, subsetSumOfAtoms]
  show (subsetSum _ selected - 1).PosSemidef ↔ _
  rw [hmoment, ← hcongr, Matrix.mul_assoc congruenceᵀ, Matrix.mul_assoc congruenceᵀ,
    ← Matrix.mul_sub, ← Matrix.sub_mul, ← Matrix.mul_assoc]
  exact (posSemidef_congr_right
    (by rw [Matrix.transpose_sub, transpose_subsetSumOfAtoms,
      transpose_frameOperatorOfAtoms _ fun c => (hpos c).le])
    hunit).symm

/-! ## Step 1: the archimedean multiplicity choice -/

/-- **The only analytic step.**  From a design all of whose `k`-subsets fail to dominate,
produce integer multiplicities `p_c ≥ 1` whose fractions `p_c / Σp` still carry a
positive-definite frame operator and still fail every `k`-subset comparison.

Each of the finitely many failures is a strict inequality with a positive gap
`gapValue`; rounding a weight down to `⌊n t_c⌋` perturbs the failing inequality by at
most the fixed constant `slack = Σ_c |b_c − a|`; one `n` with `n · gapValue > slack` at
every gate and `n · t_c > 2` at every atom does all of it at once. -/
theorem exists_multiplicityWeights_of_forall_not_dominates (D : WeightedDesign m k)
    (hfail : ∀ selected : Finset (Fin m), selected.card = k → ¬ Dominates D selected) :
    ∃ multiplicity : Fin m → ℕ, (0 < ∑ c, multiplicity c) ∧ (∀ c, 0 < multiplicity c) ∧
      (frameOperatorOfAtoms D.atom
        (fun c => (multiplicity c : ℝ) / ((∑ d, multiplicity d : ℕ) : ℝ))).PosDef ∧
      (∀ selected : Finset (Fin m), selected.card = k →
        ¬ (subsetSumOfAtoms D.atom selected
            - frameOperatorOfAtoms D.atom
                (fun c => (multiplicity c : ℝ)
                  / ((∑ d, multiplicity d : ℕ) : ℝ))).PosSemidef) := by
  classical
  have hwitnessExists : ∀ selected : Finset (Fin m), ∃ probe : Fin k → ℝ,
      selected.card = k →
        ∑ c ∈ selected, (D.atom c ⬝ᵥ probe) ^ 2 < probe ⬝ᵥ probe := by
    intro selected
    by_cases hcard : selected.card = k
    · have hsymm : (subsetSum D selected - 1)ᵀ = subsetSum D selected - 1 := by
        rw [Matrix.transpose_sub, Matrix.transpose_one, subsetSum_transpose]
      obtain ⟨probe, hprobe⟩ : ∃ probe : Fin k → ℝ,
          probe ⬝ᵥ ((subsetSum D selected - 1) *ᵥ probe) < 0 := by
        by_contra hall
        push Not at hall
        exact hfail selected hcard (Matrix.posSemidef_iff_dotProduct_mulVec.mpr
          ⟨isHermitian_of_transpose_eq hsymm, fun vector => by
            rw [star_trivial]; exact hall vector⟩)
      rw [dominationGap_form] at hprobe
      exact ⟨probe, fun _ => by linarith⟩
    · exact ⟨0, fun hbad => absurd hbad hcard⟩
  choose witness hwitness using hwitnessExists
  set overlap : Finset (Fin m) → Fin m → ℝ :=
    fun selected c => (D.atom c ⬝ᵥ witness selected) ^ 2 with hoverlapDef
  set gateMass : Finset (Fin m) → ℝ :=
    fun selected => ∑ c ∈ selected, overlap selected c with hgateMassDef
  set gapValue : Finset (Fin m) → ℝ :=
    fun selected => (witness selected ⬝ᵥ witness selected) - gateMass selected with hgapDef
  set slack : Finset (Fin m) → ℝ :=
    fun selected => ∑ c, |overlap selected c - gateMass selected| with hslackDef
  have hgapPos : ∀ selected : Finset (Fin m), selected.card = k → 0 < gapValue selected := by
    intro selected hcard
    have hstrict := hwitness selected hcard
    rw [hgapDef]
    simpa [hgateMassDef, hoverlapDef] using sub_pos.mpr hstrict
  obtain ⟨boundAtoms, hboundAtoms⟩ := Finite.exists_le fun c : Fin m => 2 / D.weight c
  obtain ⟨boundGates, hboundGates⟩ :=
    Finite.exists_le fun selected : Finset (Fin m) => slack selected / gapValue selected
  obtain ⟨scale, hscale⟩ := exists_nat_gt (max boundAtoms boundGates)
  have hscaleAtoms : ∀ c : Fin m, 2 / D.weight c < (scale : ℝ) := fun c =>
    lt_of_le_of_lt (le_trans (hboundAtoms c) (le_max_left _ _)) hscale
  have hscaleGates : ∀ selected : Finset (Fin m),
      slack selected / gapValue selected < (scale : ℝ) := fun selected =>
    lt_of_le_of_lt (le_trans (hboundGates selected) (le_max_right _ _)) hscale
  set multiplicity : Fin m → ℕ := fun c => ⌊(scale : ℝ) * D.weight c⌋₊ with hmulDef
  have htarget : ∀ c : Fin m, 2 < (scale : ℝ) * D.weight c := by
    intro c
    have hcpos := D.weight_pos c
    have hlt := hscaleAtoms c
    rw [div_lt_iff₀ hcpos] at hlt
    linarith
  have hfloorLe : ∀ c : Fin m, ((multiplicity c : ℕ) : ℝ) ≤ (scale : ℝ) * D.weight c :=
    fun c => Nat.floor_le (by linarith [htarget c])
  have hfloorGt : ∀ c : Fin m, (scale : ℝ) * D.weight c < ((multiplicity c : ℕ) : ℝ) + 1 :=
    fun c => Nat.lt_floor_add_one _
  have hmulPos : ∀ c : Fin m, 0 < multiplicity c := by
    intro c
    have hone : 1 ≤ multiplicity c := Nat.le_floor (by push_cast; linarith [htarget c])
    omega
  have htotalPos : 0 < ∑ c, multiplicity c := by
    obtain ⟨someAtom⟩ : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp (size_pos_of_design D)
    exact lt_of_lt_of_le (hmulPos someAtom) (Finset.single_le_sum
      (f := multiplicity) (fun d _ => Nat.zero_le _) (Finset.mem_univ someAtom))
  have htotalR : (0 : ℝ) < ((∑ d, multiplicity d : ℕ) : ℝ) := by exact_mod_cast htotalPos
  have hcastTotal : ((∑ d, multiplicity d : ℕ) : ℝ) = ∑ d, ((multiplicity d : ℕ) : ℝ) :=
    Nat.cast_sum _ _
  have hhalf : ∀ c : Fin m,
      (scale : ℝ) * D.weight c / 2 ≤ ((multiplicity c : ℕ) : ℝ) := by
    intro c
    have hgt := hfloorGt c
    have hbig := htarget c
    linarith
  refine ⟨multiplicity, htotalPos, hmulPos, ?_, ?_⟩
  · refine Matrix.posDef_iff_dotProduct_mulVec.mpr
      ⟨isHermitian_of_transpose_eq
        (transpose_frameOperatorOfAtoms _ fun c => by positivity), ?_⟩
    intro probe hprobe
    rw [star_trivial, form_frameOperatorOfAtoms]
    have hprobePos : 0 < probe ⬝ᵥ probe := dotProduct_self_pos hprobe
    have hscalePos : (0 : ℝ) < scale := by
      obtain ⟨someAtom⟩ : Nonempty (Fin m) :=
        Fin.pos_iff_nonempty.mp (size_pos_of_design D)
      nlinarith [htarget someAtom, D.weight_pos someAtom]
    have hsplit : ∑ c, ((multiplicity c : ℕ) : ℝ)
          / ((∑ d, multiplicity d : ℕ) : ℝ) * (D.atom c ⬝ᵥ probe) ^ 2
        = (∑ c, ((multiplicity c : ℕ) : ℝ) * (D.atom c ⬝ᵥ probe) ^ 2)
          / ((∑ d, multiplicity d : ℕ) : ℝ) := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun c _ => by ring
    rw [hsplit]
    refine div_pos ?_ htotalR
    calc (0 : ℝ) < (scale : ℝ) / 2 * (probe ⬝ᵥ probe) := by positivity
      _ = ∑ c, (scale : ℝ) * D.weight c / 2 * (D.atom c ⬝ᵥ probe) ^ 2 := by
          rw [dotProduct_self_eq_sum_weight_mul_sq D probe, Finset.mul_sum]
          exact Finset.sum_congr rfl fun c _ => by ring
      _ ≤ ∑ c, ((multiplicity c : ℕ) : ℝ) * (D.atom c ⬝ᵥ probe) ^ 2 :=
          Finset.sum_le_sum fun c _ =>
            mul_le_mul_of_nonneg_right (hhalf c) (sq_nonneg _)
  · intro selected hcard hpsd
    set probe : Fin k → ℝ := witness selected with hprobeDef
    set deviation : Fin m → ℝ :=
      fun c => overlap selected c - gateMass selected with hdevDef
    have hdecomp : (∑ c, ((multiplicity c : ℕ) : ℝ) * deviation c)
          + ∑ c, ((scale : ℝ) * D.weight c - ((multiplicity c : ℕ) : ℝ)) * deviation c
        = (scale : ℝ) * ∑ c, D.weight c * deviation c := by
      rw [← Finset.sum_add_distrib, Finset.mul_sum]
      exact Finset.sum_congr rfl fun c _ => by ring
    have hweightDev : ∑ c, D.weight c * deviation c = gapValue selected := by
      have hexpand : ∑ c, D.weight c * deviation c
          = (∑ c, D.weight c * overlap selected c)
            - (∑ c, D.weight c) * gateMass selected := by
        rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun c _ => by rw [hdevDef]; ring
      rw [hexpand, D.weight_sum_one, one_mul, hgapDef]
      exact congrArg (fun value => value - gateMass selected)
        (dotProduct_self_eq_sum_weight_mul_sq D probe).symm
    have hroundCap : ∑ c, ((scale : ℝ) * D.weight c - ((multiplicity c : ℕ) : ℝ))
          * deviation c ≤ slack selected := by
      refine Finset.sum_le_sum fun c _ => ?_
      have hlow : 0 ≤ (scale : ℝ) * D.weight c - ((multiplicity c : ℕ) : ℝ) := by
        linarith [hfloorLe c]
      have hhigh : (scale : ℝ) * D.weight c - ((multiplicity c : ℕ) : ℝ) ≤ 1 := by
        linarith [hfloorGt c]
      have hupper := le_abs_self (deviation c)
      have hnonneg := abs_nonneg (deviation c)
      nlinarith [mul_nonneg hlow (sub_nonneg.mpr hupper),
        mul_nonneg (sub_nonneg.mpr hhigh) hnonneg]
    have hgap := hgapPos selected hcard
    have hbeatsSlack : slack selected < (scale : ℝ) * gapValue selected := by
      have hdiv := hscaleGates selected
      rw [div_lt_iff₀ hgap] at hdiv
      linarith
    have hpositive : 0 < ∑ c, ((multiplicity c : ℕ) : ℝ) * deviation c := by
      rw [hweightDev] at hdecomp
      linarith
    have hunwind : ∑ c, ((multiplicity c : ℕ) : ℝ) * deviation c
        = (∑ c, ((multiplicity c : ℕ) : ℝ) * overlap selected c)
          - ((∑ d, multiplicity d : ℕ) : ℝ) * gateMass selected := by
      rw [hcastTotal, Finset.sum_mul, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun c _ => by rw [hdevDef]; ring
    have hform := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hpsd).2 probe
    rw [star_trivial, Matrix.sub_mulVec, dotProduct_sub, form_subsetSumOfAtoms,
      form_frameOperatorOfAtoms] at hform
    have hgateForm : ∑ c ∈ selected, (D.atom c ⬝ᵥ probe) ^ 2 = gateMass selected := rfl
    have hframeForm : ∑ c, ((multiplicity c : ℕ) : ℝ)
          / ((∑ d, multiplicity d : ℕ) : ℝ) * (D.atom c ⬝ᵥ probe) ^ 2
        = (∑ c, ((multiplicity c : ℕ) : ℝ) * overlap selected c)
          / ((∑ d, multiplicity d : ℕ) : ℝ) := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun c _ => by rw [hoverlapDef]; ring
    rw [hgateForm, hframeForm, sub_nonneg, div_le_iff₀ htotalR] at hform
    rw [hunwind] at hpositive
    nlinarith [hform, hpositive]

/-! ## Step 3: replication to a uniform design -/

/-- The row-to-atom map of the replication: row `r` is a copy of atom
`replicationLabel r`. -/
noncomputable def replicationLabel {multiplicity : Fin m → ℕ}
    (row : Fin (∑ c, multiplicity c)) : Fin m :=
  (finSigmaFinEquiv.symm row).1

/-- **The counting identity.**  Summing any quantity over the replicated rows is summing
it over the atoms with the multiplicities as coefficients. -/
theorem sum_replicationLabel {Target : Type*} [AddCommMonoid Target]
    (multiplicity : Fin m → ℕ) (quantity : Fin m → Target) :
    ∑ row : Fin (∑ c, multiplicity c),
        quantity (replicationLabel (multiplicity := multiplicity) row)
      = ∑ c, multiplicity c • quantity c := by
  rw [← Equiv.sum_comp (finSigmaFinEquiv (n := multiplicity))
    (fun row => quantity (replicationLabel (multiplicity := multiplicity) row))]
  have hlabel : ∀ pair : (c : Fin m) × Fin (multiplicity c),
      replicationLabel (multiplicity := multiplicity) (finSigmaFinEquiv pair) = pair.1 := by
    intro pair
    rw [replicationLabel, Equiv.symm_apply_apply]
  rw [Finset.sum_congr rfl fun pair _ => congrArg quantity (hlabel pair)]
  rw [← Finset.univ_sigma_univ, Finset.sum_sigma]
  refine Finset.sum_congr rfl fun c _ => ?_
  show ∑ _copy : Fin (multiplicity c), quantity c = multiplicity c • quantity c
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]

/-- **Replication to a uniform design.**  A design whose weights are the fractions
`multiplicity c / N` is replaced by the `N`-atom design repeating atom `c` exactly
`multiplicity c` times at the flat weight `1/N`.  Parseval survives because the
multiplicity fractions were the weights to begin with — this is `Gtz.replicatedDesign`
(one atom halved) carried out at arbitrary integer multiplicities all the way to the
flat weight. -/
noncomputable def uniformReplication (D : WeightedDesign m k) (multiplicity : Fin m → ℕ)
    (htotal : 0 < ∑ c, multiplicity c)
    (hweight : ∀ c, D.weight c = (multiplicity c : ℝ) / ((∑ c, multiplicity c : ℕ) : ℝ)) :
    WeightedDesign (∑ c, multiplicity c) k where
  atom row := D.atom (replicationLabel (multiplicity := multiplicity) row)
  weight _ := (((∑ c, multiplicity c : ℕ) : ℝ))⁻¹
  weight_pos _ := inv_pos.mpr (by exact_mod_cast htotal)
  weight_sum_one := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact mul_inv_cancel₀ (by exact_mod_cast htotal.ne')
  isParseval := by
    rw [sum_replicationLabel multiplicity
      (fun c => (((∑ c, multiplicity c : ℕ) : ℝ))⁻¹ • atomMatrix (D.atom c)),
      ← D.isParseval]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, hweight c, div_eq_mul_inv]

theorem uniformReplication_atom (D : WeightedDesign m k) (multiplicity : Fin m → ℕ)
    (htotal : 0 < ∑ c, multiplicity c)
    (hweight : ∀ c, D.weight c = (multiplicity c : ℝ) / ((∑ c, multiplicity c : ℕ) : ℝ))
    (row : Fin (∑ c, multiplicity c)) :
    (uniformReplication D multiplicity htotal hweight).atom row
      = D.atom (replicationLabel (multiplicity := multiplicity) row) := rfl

theorem uniformReplication_weight (D : WeightedDesign m k) (multiplicity : Fin m → ℕ)
    (htotal : 0 < ∑ c, multiplicity c)
    (hweight : ∀ c, D.weight c = (multiplicity c : ℝ) / ((∑ c, multiplicity c : ℕ) : ℝ))
    (row : Fin (∑ c, multiplicity c)) :
    (uniformReplication D multiplicity htotal hweight).weight row
      = (((∑ c, multiplicity c : ℕ) : ℝ))⁻¹ := rfl

/-- **Replication creates no dominator.**  A `k`-subset of the replica either repeats an
atom — killed by the shipped `Gtz.not_dominates_of_repeated_atom_general` — or is a
faithful copy of a `k`-subset of the original, which fails by hypothesis. -/
theorem forall_not_dominates_uniformReplication (D : WeightedDesign m k)
    (multiplicity : Fin m → ℕ) (htotal : 0 < ∑ c, multiplicity c)
    (hweight : ∀ c, D.weight c = (multiplicity c : ℝ) / ((∑ c, multiplicity c : ℕ) : ℝ))
    (hfail : ∀ selected : Finset (Fin m), selected.card = k → ¬ Dominates D selected)
    (chosen : Finset (Fin (∑ c, multiplicity c))) (hcard : chosen.card = k) :
    ¬ Dominates (uniformReplication D multiplicity htotal hweight) chosen := by
  classical
  by_cases hinjOn : ∀ left ∈ chosen, ∀ right ∈ chosen,
      replicationLabel (multiplicity := multiplicity) left
        = replicationLabel (multiplicity := multiplicity) right → left = right
  · have himageCard :
        (chosen.image (replicationLabel (multiplicity := multiplicity))).card = k := by
      rw [Finset.card_image_of_injOn hinjOn, hcard]
    have hmoment :
        subsetSum (uniformReplication D multiplicity htotal hweight) chosen
          = subsetSum D (chosen.image (replicationLabel (multiplicity := multiplicity))) := by
      rw [subsetSum, subsetSum, Finset.sum_image hinjOn]
      rfl
    intro hdominates
    exact hfail _ himageCard (by rwa [Dominates, ← hmoment])
  · push Not at hinjOn
    obtain ⟨left, hleft, right, hright, hsame, hne⟩ := hinjOn
    exact not_dominates_of_repeated_atom_general _ hne hleft hright hcard.le
      (by rw [uniformReplication_atom, uniformReplication_atom, hsame])

/-! ## Step 4: the uniform slice, where the bridge is already an equivalence -/

/-- **The uniform-slice converse of `Gtz.original_of_weighted_single`.**  Classical GTZ
at size `n` forces every `n`-atom design with uniform weights `1/n` to have a dominating
`k`-subset.  `Gtz.scaledAtomRows` inverts `Gtz.rowDesign`; orthonormality of its columns
is the shipped `Gtz.transpose_mul_scaledAtomRows`. -/
theorem exists_dominates_of_gtzOriginal_uniform {n : ℕ} (hn : 0 < n)
    (horiginal : GtzOriginal n k) (D : WeightedDesign n k)
    (huniform : ∀ c, D.weight c = (n : ℝ)⁻¹) :
    ∃ selected : Finset (Fin n), selected.card = k ∧ Dominates D selected := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨rowPick, hinj, hpsd⟩ :=
    horiginal (scaledAtomRows D) (transpose_mul_scaledAtomRows D)
  refine ⟨Finset.image rowPick Finset.univ, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  · set block := (scaledAtomRows D).submatrix rowPick id with hblockDef
    have hgram : blockᵀ * block
        = (n : ℝ)⁻¹ • subsetSum D (Finset.image rowPick Finset.univ) := by
      rw [transpose_mul_self_eq_sum_rows, subsetSum,
        Finset.sum_image fun left _ right _ hlr => hinj hlr, Finset.smul_sum]
      refine Finset.sum_congr rfl fun selectedIndex _ => ?_
      show atomMatrix (scaledAtomRows D (rowPick selectedIndex)) = _
      rw [scaledAtomRows_row, atomMatrix_smul, huniform,
        Real.sq_sqrt (inv_nonneg.mpr hnR.le)]
    rw [hgram, ← smul_sub] at hpsd
    exact (posSemidef_smul_iff (inv_pos.mpr hnR)).mp hpsd

/-! ## The bridge -/

/-- **THE MISSING ARROW, in counterexample form.**  A weighted `(m,k)` design with no
dominating `k`-subset manufactures an explicit size `N` at which the ORIGINAL 1997
statement fails.  So a weighted counterexample refutes the 1997 conjecture. -/
theorem exists_not_gtzOriginal_of_forall_not_dominates (D : WeightedDesign m k)
    (hfail : ∀ selected : Finset (Fin m), selected.card = k → ¬ Dominates D selected) :
    ∃ n : ℕ, 0 < n ∧ ¬ GtzOriginal n k := by
  obtain ⟨multiplicity, htotalPos, hmulPos, hframePD, hgateFail⟩ :=
    exists_multiplicityWeights_of_forall_not_dominates D hfail
  have htotalR : (0 : ℝ) < ((∑ d, multiplicity d : ℕ) : ℝ) := by exact_mod_cast htotalPos
  have hweightPos : ∀ c, 0 < (multiplicity c : ℝ) / ((∑ d, multiplicity d : ℕ) : ℝ) := by
    intro c
    exact div_pos (by exact_mod_cast hmulPos c) htotalR
  have hweightSum : ∑ c, (multiplicity c : ℝ) / ((∑ d, multiplicity d : ℕ) : ℝ) = 1 := by
    rw [← Finset.sum_div, ← Nat.cast_sum]
    exact div_self htotalR.ne'
  obtain ⟨rounded, hroundedWeight, hroundedDominates⟩ :=
    exists_design_of_frame D.atom _ hweightPos hweightSum hframePD
  have hroundedFail : ∀ selected : Finset (Fin m), selected.card = k →
      ¬ Dominates rounded selected := by
    intro selected hcard hdom
    exact hgateFail selected hcard ((hroundedDominates selected).mp hdom)
  have hroundedFraction : ∀ c, rounded.weight c
      = (multiplicity c : ℝ) / ((∑ c, multiplicity c : ℕ) : ℝ) := by
    intro c
    rw [hroundedWeight]
  refine ⟨∑ c, multiplicity c, htotalPos, fun horiginal => ?_⟩
  obtain ⟨chosen, hchosenCard, hchosenDominates⟩ :=
    exists_dominates_of_gtzOriginal_uniform htotalPos horiginal
      (uniformReplication rounded multiplicity htotalPos hroundedFraction)
      (fun row => uniformReplication_weight rounded multiplicity htotalPos hroundedFraction row)
  exact forall_not_dominates_uniformReplication rounded multiplicity htotalPos
    hroundedFraction hroundedFail chosen hchosenCard hchosenDominates

/-- **The converse bridge.**  Classical GTZ at every size gives weighted GTZ at every
size — the arrow `Gtz.original_of_weighted` was missing. -/
theorem gtzWeighted_of_forall_gtzOriginal
    (horiginal : ∀ n, 0 < n → GtzOriginal n k) : GtzWeighted m k := by
  by_contra hfail
  rw [GtzWeighted] at hfail
  push Not at hfail
  obtain ⟨D, hD⟩ := hfail
  obtain ⟨n, hn, hnot⟩ :=
    exists_not_gtzOriginal_of_forall_not_dominates D fun selected hcard hdom =>
      absurd hdom (hD selected hcard)
  exact hnot (horiginal n hn)

/-- **THE FRAME IS AN EQUIVALENCE.**  Weighted GTZ at rank `k` for all sizes is
EQUIVALENT to the 1997 statement at rank `k` for all sizes.  Forward is the campaign's
`Gtz.original_of_weighted`; backward is the four-step construction of this file. -/
theorem gtzWeightedAll_iff_forall_gtzOriginal (rank : ℕ) :
    GtzWeightedAll rank ↔ ∀ n, 0 < n → GtzOriginal n rank :=
  ⟨original_of_weighted rank, fun horiginal _ => gtzWeighted_of_forall_gtzOriginal horiginal⟩

/-- **The rank-three payoff.**  Refuting `GtzWeighted 6 3` refutes the 1997 conjecture:
the single open cell of the campaign is now equivalent to the original problem at rank
three, in BOTH directions. -/
theorem gtzWeighted_six_three_iff_forall_gtzOriginal_rank_three :
    GtzWeighted 6 3 ↔ ∀ n, 0 < n → GtzOriginal n 3 :=
  ⟨fun h63 => (gtzWeightedAll_iff_forall_gtzOriginal 3).mp (rank_three_iff_six_three.mpr h63),
    fun horiginal => gtzWeighted_of_forall_gtzOriginal horiginal⟩


/-! ## BONUS: the campaign's rank-three termini become EQUIVALENCES

The one-antecedent terminus
`Gtz.gtzOriginal_rank_three_of_forall_not_isSixThreeRefutationCandidateSharp` and the
crux-emptiness form ran one way only, because the arrow back from `GtzOriginal` to
`GtzWeighted` did not exist.  With it, each becomes an iff — a characterisation of the
1997 conjecture at rank three, not merely a sufficient condition for it. -/

/-- **The sharp refutation box characterises rank three of the ORIGINAL problem.** -/
theorem forall_not_isSixThreeRefutationCandidateSharp_iff_gtzOriginal_rank_three :
    (∀ design : WeightedDesign 6 3, ¬ IsSixThreeRefutationCandidateSharp design)
      ↔ ∀ n : ℕ, 0 < n → GtzOriginal n 3 := by
  refine ⟨gtzOriginal_rank_three_of_forall_not_isSixThreeRefutationCandidateSharp,
    fun horiginal design hsharp => ?_⟩
  obtain ⟨n, hn, hnot⟩ :=
    exists_not_gtzOriginal_of_forall_not_dominates design hsharp.1.2.2.2.2.1
  exact hnot (horiginal n hn)

/-- **Crux emptiness characterises rank three of the ORIGINAL problem.**  The campaign's
single open cell, stated purely in 1997 terms. -/
theorem isEmpty_sixThreeCrux_iff_gtzOriginal_rank_three :
    IsEmpty SixThreeCrux ↔ ∀ n : ℕ, 0 < n → GtzOriginal n 3 := by
  rw [← not_nonempty_iff, nonempty_sixThreeCrux_iff_not_gtzWeighted_six_three, not_not]
  exact gtzWeighted_six_three_iff_forall_gtzOriginal_rank_three

/-- **The crux is exactly a counterexample to the 1997 conjecture at rank three.** -/
theorem nonempty_sixThreeCrux_iff_not_gtzOriginal_rank_three :
    Nonempty SixThreeCrux ↔ ¬ ∀ n : ℕ, 0 < n → GtzOriginal n 3 := by
  rw [nonempty_sixThreeCrux_iff_not_gtzWeighted_six_three]
  exact not_congr gtzWeighted_six_three_iff_forall_gtzOriginal_rank_three

/-! ## BONUS: one cell per rank decides the ORIGINAL problem, at every rank -/

/-- **The Veronese top characterises the 1997 conjecture at every rank.**  The
crystallization `Gtz.gtzWeightedAll_of_veroneseTop` collapses rank `k` to the single
size `k(k+1)/2`; composing it with the equivalence above turns that one cell into a
CHARACTERISATION of the original statement at rank `k`, in both directions.

At rank three this is `gtzWeighted_six_three_iff_forall_gtzOriginal_rank_three` — the
SAME statement, since `3 * (3 + 1) / 2 = 6` reduces on `Nat`, the reduction
`Gtz.gtzWeightedAll_three_of_six_three` already relies on — so the two are not
independent facts and should not be counted as such.  What is genuinely new is rank four
and beyond: `GtzWeighted 10 4` now decides the 1997 conjecture at rank four both ways,
where before the campaign had only the forward half. -/
theorem gtzWeighted_veroneseTop_iff_forall_gtzOriginal (rank : ℕ) :
    GtzWeighted (rank * (rank + 1) / 2) rank ↔ ∀ n, 0 < n → GtzOriginal n rank :=
  ⟨fun htop =>
      (gtzWeightedAll_iff_forall_gtzOriginal rank).mp (gtzWeightedAll_of_veroneseTop rank htop),
    fun horiginal => gtzWeighted_of_forall_gtzOriginal horiginal⟩

/-! ## Nonvacuity controls (P4): the arrow transports, and the build checks it

These are `example`s deliberately.  Each exercises the new arrow at build time — were it
ever to stop transporting, the build would break here — while introducing no name, so
none of them can silently duplicate a shipped statement or need a pin.

Controls 1 and 2 are the decisive ones.  They reprove weighted theorems the tree already
has (`Gtz.gtz_rank_two`, `Gtz.gtz_rank_one` give the same conclusions) but by the NEW
route, starting from the ORIGINAL rank-one and rank-two statements.  An arrow that
transported nothing would not typecheck here. -/

section NonvacuityControls

/-- Rank two, obtained from the ORIGINAL rank-two theorem rather than from
`Gtz.gtz_rank_two`. -/
example : GtzWeighted 7 2 := gtzWeighted_of_forall_gtzOriginal gtz_original_rank_two

/-- Rank one, at a different size. -/
example : GtzWeighted 12 1 := gtzWeighted_of_forall_gtzOriginal gtz_original_rank_one

/-- The payoff: a weighted `(6,3)` counterexample refutes the 1997 conjecture. -/
example (hrefute : ¬ GtzWeighted 6 3) : ¬ ∀ n, 0 < n → GtzOriginal n 3 :=
  fun horiginal => hrefute (gtzWeighted_of_forall_gtzOriginal horiginal)

/-- The counterexample form applies directly to a failing design. -/
example (D : WeightedDesign 6 3)
    (hfail : ∀ selected : Finset (Fin 6), selected.card = 3 → ¬ Dominates D selected) :
    ∃ n : ℕ, 0 < n ∧ ¬ GtzOriginal n 3 :=
  exists_not_gtzOriginal_of_forall_not_dominates D hfail

/-- A crux is exactly a counterexample to the 1997 conjecture at rank three. -/
example (crux : SixThreeCrux) : ¬ ∀ n : ℕ, 0 < n → GtzOriginal n 3 :=
  nonempty_sixThreeCrux_iff_not_gtzOriginal_rank_three.mp ⟨crux⟩

end NonvacuityControls

end Gtz
