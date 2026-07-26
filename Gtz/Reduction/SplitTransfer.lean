/-
# Split transfer: duplicating an atom, merging a parallel pair, and the branch shells

The Covered+ induction on the atom count `m` needs several pieces of exchange
machinery, and this file mechanizes them in one place, together with two
induction shells — a qualitative one that is exhaustive but sits on an open
region, and a compact one built on the repo's own floored-spread predicates.

1. **Splitting.**  Duplicate atom `splitLabel` into two copies carrying weights
   `share` and `t − share`.  The frame operator does not move, so the result is
   again a design (`splitDesign`), and the whole Loewner picture is carried
   across UNCHANGED: a `k`-subset upstairs either holds both copies — and then
   it never dominates — or it descends to a `k`-subset downstairs with the
   *same* atom sum (`splitDesign_subsetSum_trichotomy`).  Every margin therefore
   transfers exactly: `Dominates`, `DominatesAtLevel` at every level, strict
   domination, and `IsTie` are equivalences in both directions
   (`isTie_splitDesign_iff`).  The covering-level implication
   `GtzWeighted (m+1) k → GtzWeighted m k` is already in the repo
   (`Gtz.gtzWeighted_of_succ`); the new content here is the tie/margin level,
   and the generalisation of `Gtz.replicatedDesign` from the halving split
   `share = t/2` to an arbitrary share.

2. **Strict congruence.**  `Gtz.LinAlg.PsdKit` carries the PSD half of the
   congruence chain that `weighted_naimark_duality` walks.  Its definite
   companions are here — `posDef_one_sub_iff_strictContraction`,
   `strictContraction_flip`, `posDef_one_sub_transpose_comm`,
   `posDef_transpose_mul_sub_one_comm` — packaged as `LoewnerEquiv`, the
   two-sided (PSD **and** PosDef) equivalence of two symmetric matrices, which is
   preserved by every step of the chain.  This is exactly what `IsTie` transport
   needs, because `IsTie` is a conjunction of a PSD claim and the NEGATION of a
   PosDef claim: the PSD flip alone transports neither direction.

3. **Whitening.**  `whitenedFamilyDesign` turns any positively weighted family
   with weights summing to one into an exact design — Parseval on the nose, not
   approximately — given a whitener for its frame operator.  It takes that
   whitener as an argument; it does NOT take a pinch.  The pinch route is the
   composite `exists_whitenedDesign_of_framePinched`, and there the side
   condition `etaBound < 1` is load-bearing: at `etaBound >= 1` the lower pinch
   is vacuous, the frame operator need not be invertible, and no whitener need
   exist.  The Rayleigh floor then crosses both ways with the factors `1 − eta`
   (down to up) and `1/(1 + eta)` (up to down), each direction consuming only the
   ONE side of the pinch it needs.  The downward half is
   `Gtz.whitenedPullback_form_ge` at `defect = 1 − frameOperator` and re-proves
   nothing; what is added is the design constructor, the pinch predicate, the
   upward half, and `whitenedDesign_subsetSum_eq`, which joins the constructor to
   the two transfers — those are stated for a FREE `frameOperator`, so without it
   a consumer has to re-derive the link.

4. **The merge.**  Two EXACTLY parallel atoms `g_drop = ratio · g_kept` merge to
   one (`mergedParallelDesign`), and a dominating subset downstairs pulls back
   upstairs with **no margin at all** (`dominating_of_parallel_pair`): the merged
   atom's squared scale is a convex combination of `1` and `ratio^2`, hence at
   most the larger of the two, so replacing the merged atom by whichever original
   is longer only ADDS a positive semidefinite rank one.  This is one of the two
   branches of the induction that are margin-free, and that is not an accident —
   see the ceiling warning below.  CALIBRATION, so the branch is not oversold:
   exact parallelism is a codimension `rank − 1` condition on the atom family, so
   this branch discharges a Lebesgue-null part of design space.  Its worth is not
   measure-theoretic.  It is that the near-parallel corner is where the ties
   live, and this is the only known way to pay any part of that corner at all.

5. **Two shells.**  `gtzWeighted_of_branches` is the qualitative one: branch (i)
   discharged by the merge, `DustDropCertificate` and `SpreadFloorCertificate`
   named.  It is exhaustive by construction because `IsSpreadAndFloored` is
   DEFINED as the negation of the other two triggers — which is exactly what it
   pays: the region so defined is open, not compact, and no positive margin is
   available on it (NO-GO 1 below).
   `gtzWeightedRankThree_of_compactBranches` is the honest one.  It reuses the
   region predicates of `Gtz.Quantitative.FlooredSpreadRegion`
   (`Gtz.HasSpreadAtLeast`, `Gtz.HasWeightFloor`, `Gtz.IsFlooredSpreadDesign`)
   rather than re-inventing them, discharges TWO branches margin-free — a light
   atom by `Gtz.dominating_of_light_atom`, an exactly parallel pair by the merge
   — and leaves THREE named residues: `NearParallelCertificate` (the corner
   between exact parallelism and the angular floor), `DustDropCertificate`, and
   `FlooredSpreadDominationCertificate` on a region that is closed in the atoms.
   At size six the last residue follows from the repo's own
   `Gtz.FlooredSpreadCovering`
   (`flooredSpreadDominationCertificate_six_of_flooredSpreadCovering`), so the
   two files state ONE hypothesis between them, not two.

## PROVED here (kernel-checked)

`DominatesAtLevel` and its dictionary against `Gtz.GtzWeightedFloor`;
`splitDesign` and the full split correspondence — including the fact that the
SHARE is invisible to every Loewner verdict, since `isTie_splitDesign_iff`,
`exists_dominating_splitDesign_iff` and the level-wise transfer all hold at an
ARBITRARY share; the strict congruence kit and `LoewnerEquiv`;
`exists_naimarkDual_loewnerEquiv` and `isTie_naimarkDual`;
`whitenedFamilyDesign` with both transfer directions, the pinch composite and the
join `whitenedDesign_subsetSum_eq`; `mergedParallelDesign` with the exact-parallel
pullback; both shells; the diamond's non-parallelism and the falsity of the
hinge at `(5,3)`;
and the three fences that keep the shells off dead routes —
`dustBudget_forces_leverage_le_one`,
`dustDropCertificate_of_floor_collapses_to_lightAtom`, the weight-floor dichotomy
`hasDustAtom_of_sizeInv_lt_floor`, and the weight-independence of the graphic
share `atomShare_graphicDesign_of_solves`.

## CITED, not verified here

* Wood–Atkey-style context division plays no role; the split/merge pair is the
  frame-theoretic operation of *scalability* (diagonal rescaling of the analysis
  operator) — Kutyniok–Okoudjou–Philipp–Tuley, arXiv:1204.1880; Casazza–De
  Carli–Tran, arXiv:2203.12678.  A literature scan found NO theorem of the form
  "parallel extension preserves tightness"; matroid parallel extension carries no
  metric data.  The convexity argument behind `exists_longerParallelLabel` is
  therefore attributed to this campaign, not to prior art.
* Haynsworth inertia additivity (LAA 1 (1968) 73–81) and the singular-pivot
  generalisation (Carlson–Haynsworth–Markham 1974) are the classical route to the
  signature lemma "`Lambda|_U ⪰ 0` iff `−(Lambda⁻¹)|_{U-perp} ⪰ 0`".  It is NOT
  used: Haynsworth needs a nonsingular pivot block, and singular pivot blocks are
  exactly the tie locus this campaign studies.  The repo's own
  `weighted_naimark_duality` already delivers the PSD half by a sqrt-free
  four-congruence route, and `exists_naimarkDual_loewnerEquiv` below delivers the
  definite half by the same route.

## PROVENANCE of the two long proofs

`exists_naimarkDual_loewnerEquiv` is NOT an independent construction.  Its body —
the whitener `R`, the isometry `Amat`, the co-design, the orthonormal completion
`B`, the embedding, the two diagonal congruences — is the body of
`Gtz.weighted_naimark_duality` (`Gtz.Reduction.Naimark`), copied essentially
verbatim; 222 of its 240 lines are byte-identical to that proof (measured, not
asserted).  What is new is
the last dozen lines: the chain is walked ONCE in `LoewnerEquiv` instead of twice
in `PosSemidef`, which is what buys the definite verdict.  The consequence is
that the old theorem is now a corollary of the new one —
`weighted_naimark_duality_of_loewnerEquiv` below proves exactly that in two lines
— so the ~280-line proof in `Gtz.Reduction.Naimark` is redundant and should be
replaced by that corollary rather than maintained in parallel.  This file cannot
do the deletion; it can only leave the retirement path compiled and ready.

The atom family of `splitDesign` is `Gtz.replicatedAtoms` on the nose
(`splitAtoms_eq_replicatedAtoms` is `rfl`); the fold is `Gtz.replicationMerge`.
Only the weight family is new.

## MEASURED elsewhere, claimed by nothing here

The merge and drop cost constants; the `4·tau^2` law on the `(6,3)` critical
stratum; the tie-class census.  None of that is asserted below.  What is asserted
is exactly what is proved.  (Share-irrelevance USED to be listed here on the
strength of exact-rational spot checks; it has since been proved in general and
now sits under PROVED.)

## The honest hypothesis list of the shells

`gtzWeighted_of_branches` leaves THREE hypotheses, all named, none buried:
`hrecursive` (weighted GTZ one size down — at the `(7,3)` instance that is the
open problem one size down, and it is what branch (i) consumes), `hdust` (the
drop branch) and `hspread` (the spread-and-floored branch).  Branch (i) is
discharged.  The drop branch is supplied in the conditional forms
`exists_dominating_of_dust_atom`, `dustDropCertificate_of_floor` and
`dustDropCertificate_of_floorOnRegion`, which make visible the fact that it needs
a strictly positive level one size down and an explicit share budget.

`gtzWeightedRankThree_of_compactBranches` leaves FOUR: `hrecursive`, plus the
three residues `hnearParallel`, `hdust`, `hregion`.

`HingeHoldsAtSize` records the campaign's open structural lemma.  It is proved
FALSE at `(5,3)` here (`not_hingeHoldsAtSize_five_three`), and it is inert: it is
consumed only by `not_isTie_of_hinge_of_spread`, which nothing else consumes.
That is deliberate and worth stating plainly — tie-freeness is NOT a margin.  A
region can be tie-free and still have infimal margin zero, because the tie can
sit in its closure; that is precisely how NO-GO 1 kills the qualitative region.

**CEILING WARNING (proved elsewhere in the repo, must not be forgotten).**
`Gtz.paddedTetraDesign` is an exact tie at every size `>= 4`
(`Gtz.paddedTetraDesign_isTie`), so `GtzWeightedFloor m 3 level` is FALSE for
every `level > 1` and every `m >= 4` (`Gtz.not_gtzWeightedFloor_rankThree_of_one_lt`,
contrapositive `Gtz.gtzWeightedFloor_rankThree_level_le_one`).  Consequently no
branch of any induction on rank three may consume a globally positive margin one
size down.  The merge and light-atom branches are margin-free precisely for that
reason; the drop branch is not, and its margin hypothesis can only ever be
satisfied RELATIVE to a region, never globally.

## NO-GO ledger for this file's own routes

1. **A margin on the QUALITATIVE spread region does not exist.**
   `IsSpreadAndFloored` asks for `¬ HasParallelPair` — an OPEN condition — so the
   region is not compact, its closure meets the tie locus, and the infimum of the
   margin over it is `0`.  Exact witnesses (adversarial audit, certified in
   rationals, not floats): the bundled cycle on four arcs at `(6,3)` with bundle
   sizes `(2,2,1,1)`, conductances `(1/8,1/8,1/5,1/5)` and UNIFORM weights `1/6`
   is an exact tie; pulling its two parallel pairs apart by `delta = 10^-12`
   leaves a design with no parallel pair, weights still exactly `1/6` — the
   LARGEST floor six weights admit — that dominates at level `1` and at no level
   `1 + 10^-10`.  Same pattern at `(7,3)` with bundle sizes `(2,2,2,1)`,
   conductances `(1/10,1/10,1/10,1/6)`, weights `1/7`.  An earlier draft shipped
   `StratumNeighborhoodCovering` as "the one genuinely analytic input of the
   plan", justified by a compactness claim citing `Gtz.collaredSet` — which is
   the wrong set on two counts (it carries an all-heavy LEVERAGE floor the
   region does not, and no spread condition at all).  Both the definition and its
   constructor are RETRACTED.  The compact replacement is
   `Gtz.IsFlooredSpreadDesign`, whose spread condition `Gtz.HasSpreadAtLeast` is
   a closed polynomial inequality.
2. **The globally floored dust branch is inert at rank three.**  With `rank = 3`
   and size `>= 4` the ceiling forces `level <= 1`, and then the budget
   `1 − t_d <= level·(1 − s_d)` forces `s_d <= t_d`, i.e. leverage `<= 1` — the
   hypothesis of `Gtz.dominating_of_light_atom`, which is already a theorem.  So
   `dustDropCertificate_of_floor` never reaches past the repo's light-atom lemma
   at rank three.  This is PROVED here, not asserted:
   `dustBudget_forces_leverage_le_one` and
   `dustDropCertificate_of_floor_collapses_to_lightAtom`.  Worse for the naive
   reading, `Gtz.atomShare` on a graphic design is weight-INDEPENDENT —
   `atomShare_graphicDesign_of_solves` proves `t_e·leverage_e = c_e·(b_e ⬝ᵥ y)`
   for any `y` solving `L y = b_e`, a quantity with no weight in it — so making
   an atom light does not make it cheap to drop; it only inflates the leverage.
   The live form is
   `dustDropCertificate_of_floorOnRegion`, whose floor is asked only of the
   designs the deflation actually produces.
3. **No weight floor makes both residues non-trivial at once.**  Every design of
   size `n` has an atom of weight at most `1/n`.  For `weightFloor > 1/n` every
   design carries dust, so the spread residue is VACUOUS and the dust residue is
   literally the goal (`dustDropCertificate_iff_gtzWeighted_of_sizeInv_lt_floor`);
   for `weightFloor <= 1/n`, NO-GO 1 applies to the qualitative region.  Both
   halves are mechanized below.  Read the shells as specifications of what is
   owed, never as progress.
4. **The two region shapes cannot both be had.**  With the qualitative predicate
   the trichotomy is exhaustive but region (iii) is open; with the quantitative
   predicate region (iii) is compact but a fourth residue appears — the corner
   `0 < spread < spreadThreshold` of near-but-not-exactly-parallel pairs — which
   the merge cannot pay, since merging at angular defect `eps` leaves a frame
   defect of size `Theta(eps)` (`Gtz.mergeFrameDefect_eq`) and pulling that back
   needs a positive margin one size down, which the ceiling forbids.  The compact
   shell below names that corner `NearParallelCertificate` instead of absorbing
   it.  Closing it, or proving it cannot be closed, is the sharpest open question
   this file exposes.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Core.Sanity
import Gtz.LinAlg.PsdKit
import Gtz.LinAlg.SchurRankOne
import Gtz.LinAlg.Completion
import Gtz.Design.MarginTransfer
import Gtz.Design.DiamondPrimitive
import Gtz.Quantitative.FlooredSpreadRegion
import Gtz.Quantitative.GlobalMinimumRankThree
import Gtz.Certificates.ResidueDissolution
import Gtz.Reduction.Naimark
import Gtz.Reduction.Deflation
import Gtz.Reduction.RankFourWindow
import Gtz.Reduction.BranchTransferConstants
import Gtz.Reduction.RealVolumeFloor
import Gtz.Reduction.Reductions

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

variable {m k : ℕ}

/-! ## Graded domination

`Dominates` is the level-one instance of a one-parameter family.  Every
quantitative transfer in this file is stated at a level, and `GtzWeightedFloor`
(`Gtz.Reduction.RealVolumeFloor`) is the corresponding covering statement — the
two agree definitionally, which `gtzWeightedFloor_iff_dominatesAtLevel` records.
-/

/-- Subset `C` dominates at `level`: `S_C ⪰ level · I`.  `Gtz.Dominates` is the
case `level = 1`. -/
def DominatesAtLevel (D : WeightedDesign m k) (C : Finset (Fin m)) (level : ℝ) : Prop :=
  (subsetSum D C - level • (1 : Matrix (Fin k) (Fin k) ℝ)).PosSemidef

/-- At level one, graded domination IS domination. -/
theorem dominatesAtLevel_one_iff_dominates (D : WeightedDesign m k) (C : Finset (Fin m)) :
    DominatesAtLevel D C 1 ↔ Dominates D C := by
  rw [DominatesAtLevel, Dominates, one_smul]

/-- The covering statement at a level is the graded domination statement. -/
theorem gtzWeightedFloor_iff_dominatesAtLevel (size rank : ℕ) (level : ℝ) :
    GtzWeightedFloor size rank level
      ↔ ∀ D : WeightedDesign size rank,
          ∃ C : Finset (Fin size), C.card = rank ∧ DominatesAtLevel D C level :=
  Iff.rfl

/-- Lowering the level is free. -/
theorem dominatesAtLevel_mono {D : WeightedDesign m k} {C : Finset (Fin m)}
    {lowerLevel upperLevel : ℝ} (hlevel : lowerLevel ≤ upperLevel)
    (hdominates : DominatesAtLevel D C upperLevel) :
    DominatesAtLevel D C lowerLevel :=
  posSemidef_sub_smul_one_of_level_le hlevel hdominates

/-- Graded domination read on the quadratic form: a Rayleigh floor. -/
theorem dominatesAtLevel_iff_form (D : WeightedDesign m k) (C : Finset (Fin m)) (level : ℝ) :
    DominatesAtLevel D C level
      ↔ ∀ probe : Fin k → ℝ,
          level * (probe ⬝ᵥ probe) ≤ probe ⬝ᵥ (subsetSum D C *ᵥ probe) := by
  have hsymmetric : (subsetSum D C - level • (1 : Matrix (Fin k) (Fin k) ℝ))ᵀ
      = subsetSum D C - level • (1 : Matrix (Fin k) (Fin k) ℝ) := by
    rw [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_one, subsetSum_transpose]
  have hform : ∀ probe : Fin k → ℝ,
      probe ⬝ᵥ ((subsetSum D C - level • (1 : Matrix (Fin k) (Fin k) ℝ)) *ᵥ probe)
        = probe ⬝ᵥ (subsetSum D C *ᵥ probe) - level * (probe ⬝ᵥ probe) := by
    intro probe
    rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_smul, smul_eq_mul]
  constructor
  · intro hdominates probe
    have hstep := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hdominates).2 probe
    rw [star_trivial, hform probe] at hstep
    linarith
  · intro hfloor
    refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr
      ⟨isHermitian_of_transpose_eq hsymmetric, fun probe => ?_⟩
    rw [star_trivial, hform probe]
    linarith [hfloor probe]

/-- Strict domination read on the quadratic form. -/
theorem posDef_subsetSum_sub_smul_one_iff_form (D : WeightedDesign m k) (C : Finset (Fin m))
    (level : ℝ) :
    (subsetSum D C - level • (1 : Matrix (Fin k) (Fin k) ℝ)).PosDef
      ↔ ∀ probe : Fin k → ℝ, probe ≠ 0 →
          level * (probe ⬝ᵥ probe) < probe ⬝ᵥ (subsetSum D C *ᵥ probe) := by
  have hsymmetric : (subsetSum D C - level • (1 : Matrix (Fin k) (Fin k) ℝ))ᵀ
      = subsetSum D C - level • (1 : Matrix (Fin k) (Fin k) ℝ) := by
    rw [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_one, subsetSum_transpose]
  have hform : ∀ probe : Fin k → ℝ,
      probe ⬝ᵥ ((subsetSum D C - level • (1 : Matrix (Fin k) (Fin k) ℝ)) *ᵥ probe)
        = probe ⬝ᵥ (subsetSum D C *ᵥ probe) - level * (probe ⬝ᵥ probe) := by
    intro probe
    rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_smul, smul_eq_mul]
  constructor
  · intro hdefinite probe hprobe
    have hstep := (Matrix.posDef_iff_dotProduct_mulVec.mp hdefinite).2 hprobe
    rw [star_trivial, hform probe] at hstep
    linarith
  · intro hfloor
    refine Matrix.posDef_iff_dotProduct_mulVec.mpr
      ⟨isHermitian_of_transpose_eq hsymmetric, fun probe hprobe => ?_⟩
    rw [star_trivial, hform probe]
    linarith [hfloor probe hprobe]

/-! ## Splitting one atom at an arbitrary share

`Gtz.replicatedAtoms` already builds the duplicated atom family — the split does
not touch the vectors — so only the weight family is new.  Everything below is
stated for a bare family first, so that the design instance is a corollary and
the frame-operator invariance is visible as an identity rather than as two
appeals to Parseval.
-/

/-- The atom family after splitting `splitLabel`: the fresh copy at the new last
index carries the same vector.  Definitionally `Gtz.replicatedAtoms`, stated for a
bare family so that the frame-operator identity below needs no design. -/
def splitAtoms (atomFamily : Fin m → (Fin k → ℝ)) (splitLabel : Fin m) :
    Fin (m + 1) → (Fin k → ℝ) :=
  Fin.snoc atomFamily (atomFamily splitLabel)

theorem splitAtoms_eq_replicatedAtoms (D : WeightedDesign m k) (splitLabel : Fin m) :
    splitAtoms D.atom splitLabel = replicatedAtoms D splitLabel := rfl

/-- The weight family after splitting `splitLabel` into a copy of weight `share`
and a copy of weight `t − share`.  The fresh copy sits at the new last index. -/
noncomputable def splitWeights (weightFamily : Fin m → ℝ) (splitLabel : Fin m) (share : ℝ) :
    Fin (m + 1) → ℝ :=
  Fin.snoc (Function.update weightFamily splitLabel share) (weightFamily splitLabel - share)

@[simp] theorem splitWeights_last (weightFamily : Fin m → ℝ) (splitLabel : Fin m) (share : ℝ) :
    splitWeights weightFamily splitLabel share (Fin.last m) = weightFamily splitLabel - share :=
  Fin.snoc_last _ _

theorem splitWeights_castSucc_self (weightFamily : Fin m → ℝ) (splitLabel : Fin m) (share : ℝ) :
    splitWeights weightFamily splitLabel share splitLabel.castSucc = share := by
  rw [splitWeights, Fin.snoc_castSucc, Function.update_self]

theorem splitWeights_castSucc_of_ne (weightFamily : Fin m → ℝ) {splitLabel index : Fin m}
    (share : ℝ) (hne : index ≠ splitLabel) :
    splitWeights weightFamily splitLabel share index.castSucc = weightFamily index := by
  rw [splitWeights, Fin.snoc_castSucc, Function.update_of_ne hne]

/-- **The split preserves the total weight**, at the level of bare families. -/
theorem sum_splitWeights (weightFamily : Fin m → ℝ) (splitLabel : Fin m) (share : ℝ) :
    ∑ c, splitWeights weightFamily splitLabel share c = ∑ c, weightFamily c := by
  rw [Fin.sum_univ_castSucc]
  simp only [splitWeights, Fin.snoc_castSucc, Fin.snoc_last]
  rw [sum_eq_add_diff_of_agree_off weightFamily
    (Function.update weightFamily splitLabel share) splitLabel
    (fun index hindex => Function.update_of_ne hindex _ _), Function.update_self]
  ring

/-- **The split preserves the frame operator**, at the level of bare families:
the duplicated atom contributes `share · A + (t − share) · A = t · A`, exactly
what it contributed before.  This is the whole reason splitting is invisible to
every Loewner statement. -/
theorem sum_splitFrameOperator (atomFamily : Fin m → (Fin k → ℝ)) (weightFamily : Fin m → ℝ)
    (splitLabel : Fin m) (share : ℝ) :
    ∑ c, splitWeights weightFamily splitLabel share c
        • atomMatrix (splitAtoms atomFamily splitLabel c)
      = ∑ c, weightFamily c • atomMatrix (atomFamily c) := by
  rw [Fin.sum_univ_castSucc]
  simp only [splitWeights, splitAtoms, Fin.snoc_castSucc, Fin.snoc_last]
  rw [sum_eq_add_diff_of_agree_off
    (fun index => weightFamily index • atomMatrix (atomFamily index))
    (fun index =>
      Function.update weightFamily splitLabel share index • atomMatrix (atomFamily index))
    splitLabel
    (fun index hindex => by rw [Function.update_of_ne hindex]), Function.update_self]
  have hcancel : share • atomMatrix (atomFamily splitLabel)
      - weightFamily splitLabel • atomMatrix (atomFamily splitLabel)
      + (weightFamily splitLabel - share) • atomMatrix (atomFamily splitLabel) = 0 := by
    rw [← sub_smul, ← add_smul,
      show share - weightFamily splitLabel + (weightFamily splitLabel - share) = 0 from by ring,
      zero_smul]
  rw [add_assoc, hcancel, add_zero]

/-- **Splitting an atom produces a design.**  The atom family is the repo's
`Gtz.replicatedAtoms` (splitting never moves a vector); the weights are the
share and its complement.  Parseval and the weight sum are the two family-level
identities above. -/
noncomputable def splitDesign (D : WeightedDesign m k) (splitLabel : Fin m) (share : ℝ)
    (hshareLow : 0 < share) (hshareHigh : share < D.weight splitLabel) :
    WeightedDesign (m + 1) k where
  atom := splitAtoms D.atom splitLabel
  weight := splitWeights D.weight splitLabel share
  weight_pos := by
    intro c
    refine Fin.lastCases ?_ ?_ c
    · rw [splitWeights_last]
      linarith
    · intro index
      rcases eq_or_ne index splitLabel with hisSplit | hisOther
      · rw [hisSplit, splitWeights_castSucc_self]
        exact hshareLow
      · rw [splitWeights_castSucc_of_ne _ _ hisOther]
        exact D.weight_pos index
  weight_sum_one := by rw [sum_splitWeights, D.weight_sum_one]
  isParseval := by rw [sum_splitFrameOperator, D.isParseval]

@[simp] theorem splitDesign_atom_castSucc (D : WeightedDesign m k) (splitLabel index : Fin m)
    {share : ℝ} (hshareLow : 0 < share) (hshareHigh : share < D.weight splitLabel) :
    (splitDesign D splitLabel share hshareLow hshareHigh).atom index.castSucc = D.atom index :=
  replicatedAtoms_castSucc D splitLabel index

@[simp] theorem splitDesign_atom_last (D : WeightedDesign m k) (splitLabel : Fin m)
    {share : ℝ} (hshareLow : 0 < share) (hshareHigh : share < D.weight splitLabel) :
    (splitDesign D splitLabel share hshareLow hshareHigh).atom (Fin.last m) = D.atom splitLabel :=
  replicatedAtoms_last D splitLabel

@[simp] theorem splitDesign_weight_last (D : WeightedDesign m k) (splitLabel : Fin m)
    {share : ℝ} (hshareLow : 0 < share) (hshareHigh : share < D.weight splitLabel) :
    (splitDesign D splitLabel share hshareLow hshareHigh).weight (Fin.last m)
      = D.weight splitLabel - share :=
  splitWeights_last D.weight splitLabel share

theorem splitDesign_weight_castSucc_self (D : WeightedDesign m k) (splitLabel : Fin m)
    {share : ℝ} (hshareLow : 0 < share) (hshareHigh : share < D.weight splitLabel) :
    (splitDesign D splitLabel share hshareLow hshareHigh).weight splitLabel.castSucc = share :=
  splitWeights_castSucc_self D.weight splitLabel share

theorem splitDesign_weight_castSucc_of_ne (D : WeightedDesign m k) {splitLabel index : Fin m}
    {share : ℝ} (hshareLow : 0 < share) (hshareHigh : share < D.weight splitLabel)
    (hne : index ≠ splitLabel) :
    (splitDesign D splitLabel share hshareLow hshareHigh).weight index.castSucc
      = D.weight index :=
  splitWeights_castSucc_of_ne D.weight share hne

/-- **The frame operator is invariant under the split**, read on the designs. -/
theorem splitDesign_frameOperator_eq (D : WeightedDesign m k) (splitLabel : Fin m) {share : ℝ}
    (hshareLow : 0 < share) (hshareHigh : share < D.weight splitLabel) :
    ∑ c, (splitDesign D splitLabel share hshareLow hshareHigh).weight c
        • atomMatrix ((splitDesign D splitLabel share hshareLow hshareHigh).atom c)
      = ∑ c, D.weight c • atomMatrix (D.atom c) :=
  sum_splitFrameOperator D.atom D.weight splitLabel share

/-- The halving split of `Gtz.replicatedDesign` is the split at `share = t/2`:
same atoms, same weights. -/
theorem replicatedDesign_eq_splitDesign_half (D : WeightedDesign m k) (splitLabel : Fin m)
    (hshareLow : 0 < D.weight splitLabel / 2)
    (hshareHigh : D.weight splitLabel / 2 < D.weight splitLabel) :
    (replicatedDesign D splitLabel).atom
        = (splitDesign D splitLabel (D.weight splitLabel / 2) hshareLow hshareHigh).atom
      ∧ (replicatedDesign D splitLabel).weight
        = (splitDesign D splitLabel (D.weight splitLabel / 2) hshareLow hshareHigh).weight := by
  refine ⟨rfl, ?_⟩
  funext c
  refine Fin.lastCases ?_ ?_ c
  · rw [splitDesign_weight_last]
    show replicatedWeights D splitLabel (Fin.last m) = _
    rw [replicatedWeights, Fin.snoc_last]
    ring
  · intro index
    rcases eq_or_ne index splitLabel with hisSplit | hisOther
    · subst hisSplit
      rw [splitDesign_weight_castSucc_self]
      show replicatedWeights D index index.castSucc = _
      rw [replicatedWeights, Fin.snoc_castSucc, Function.update_self]
    · rw [splitDesign_weight_castSucc_of_ne _ _ _ hisOther]
      show replicatedWeights D splitLabel index.castSucc = _
      rw [replicatedWeights, Fin.snoc_castSucc, Function.update_of_ne hisOther]

/-! ### The subset correspondence

A `k`-subset upstairs is in exactly one of three classes: it holds neither copy
of the split atom, or exactly one, or both.  The first two classes descend along
`Gtz.replicationMerge` with the atom sum UNCHANGED; the third never dominates.
-/

/-- Folding back is injective on any subset that does not hold both copies. -/
theorem injOn_replicationMerge_of_not_both (splitLabel : Fin m) {C : Finset (Fin (m + 1))}
    (hnotBoth : Fin.last m ∈ C → splitLabel.castSucc ∉ C) :
    Set.InjOn (replicationMerge splitLabel) C := by
  have hfiber : ∀ c : Fin (m + 1),
      c = Fin.last m ∨ c = (replicationMerge splitLabel c).castSucc := by
    intro c
    refine Fin.lastCases ?_ ?_ c
    · exact Or.inl rfl
    · intro index
      exact Or.inr (by rw [replicationMerge_castSucc])
  intro left hleft right hright hmerge
  simp only [Finset.mem_coe] at hleft hright
  rcases hfiber left with hleftLast | hleftCast
  · rcases hfiber right with hrightLast | hrightCast
    · rw [hleftLast, hrightLast]
    · refine absurd ?_ (hnotBoth (hleftLast ▸ hleft))
      have hmergeRight : replicationMerge splitLabel right = splitLabel := by
        rw [← hmerge, hleftLast, replicationMerge_last]
      rw [← hmergeRight, ← hrightCast]
      exact hright
  · rcases hfiber right with hrightLast | hrightCast
    · refine absurd ?_ (hnotBoth (hrightLast ▸ hright))
      have hmergeLeft : replicationMerge splitLabel left = splitLabel := by
        rw [hmerge, hrightLast, replicationMerge_last]
      rw [← hmergeLeft, ← hleftCast]
      exact hleft
    · rw [hleftCast, hrightCast, hmerge]

/-- **The atom sum descends unchanged** along the fold, on any subset that does
not hold both copies. -/
theorem subsetSum_image_replicationMerge (D : WeightedDesign m k) (splitLabel : Fin m)
    {share : ℝ} (hshareLow : 0 < share) (hshareHigh : share < D.weight splitLabel)
    {C : Finset (Fin (m + 1))} (hnotBoth : Fin.last m ∈ C → splitLabel.castSucc ∉ C) :
    subsetSum D (C.image (replicationMerge splitLabel))
      = subsetSum (splitDesign D splitLabel share hshareLow hshareHigh) C := by
  have hinjective := injOn_replicationMerge_of_not_both splitLabel hnotBoth
  rw [subsetSum, subsetSum, Finset.sum_image
    (fun left hleft right hright hmerge => hinjective hleft hright hmerge)]
  exact Finset.sum_congr rfl fun c _ => by
    rw [atom_replicationMerge]
    rfl

/-- **The atom sum lifts unchanged** along the plain embedding. -/
theorem subsetSum_splitDesign_image_castSucc (D : WeightedDesign m k) (splitLabel : Fin m)
    {share : ℝ} (hshareLow : 0 < share) (hshareHigh : share < D.weight splitLabel)
    (baseSubset : Finset (Fin m)) :
    subsetSum (splitDesign D splitLabel share hshareLow hshareHigh)
        (baseSubset.image Fin.castSucc)
      = subsetSum D baseSubset := by
  rw [subsetSum, subsetSum, Finset.sum_image
    (fun left _ right _ hcast => Fin.castSucc_injective m hcast)]
  exact Finset.sum_congr rfl fun index _ => by
    rw [splitDesign_atom_castSucc]

theorem card_image_castSucc_eq (baseSubset : Finset (Fin m)) :
    (baseSubset.image (Fin.castSucc : Fin m → Fin (m + 1))).card = baseSubset.card :=
  Finset.card_image_of_injective _ (Fin.castSucc_injective m)

/-- **The triple correspondence.**  Every subset upstairs either holds both
copies of the split atom, or is the image of a subset downstairs of the same
cardinality carrying the SAME atom sum.  No margin is lost in either class. -/
theorem splitDesign_subsetSum_trichotomy (D : WeightedDesign m k) (splitLabel : Fin m)
    {share : ℝ} (hshareLow : 0 < share) (hshareHigh : share < D.weight splitLabel)
    (C : Finset (Fin (m + 1))) :
    (Fin.last m ∈ C ∧ splitLabel.castSucc ∈ C)
      ∨ ∃ baseSubset : Finset (Fin m), baseSubset.card = C.card ∧
          subsetSum (splitDesign D splitLabel share hshareLow hshareHigh) C
            = subsetSum D baseSubset := by
  classical
  by_cases hboth : Fin.last m ∈ C ∧ splitLabel.castSucc ∈ C
  · exact Or.inl hboth
  · refine Or.inr ⟨C.image (replicationMerge splitLabel), ?_, ?_⟩
    · exact Finset.card_image_of_injOn
        (injOn_replicationMerge_of_not_both splitLabel fun hlast hcast => hboth ⟨hlast, hcast⟩)
    · exact (subsetSum_image_replicationMerge D splitLabel hshareLow hshareHigh
        (fun hlast hcast => hboth ⟨hlast, hcast⟩)).symm

/-- A subset holding both copies never dominates: it selects a repeated atom. -/
theorem not_dominates_splitDesign_of_both_copies (D : WeightedDesign m k) (splitLabel : Fin m)
    {share : ℝ} (hshareLow : 0 < share) (hshareHigh : share < D.weight splitLabel)
    {C : Finset (Fin (m + 1))} (hcardLe : C.card ≤ k) (hlast : Fin.last m ∈ C)
    (hcast : splitLabel.castSucc ∈ C) :
    ¬ Dominates (splitDesign D splitLabel share hshareLow hshareHigh) C :=
  not_dominates_of_repeated_atom_general _ (Fin.castSucc_lt_last splitLabel).ne'
    hlast hcast hcardLe (by rw [splitDesign_atom_last, splitDesign_atom_castSucc])

/-! ### Margins transfer exactly

All four statements are rewritings of the same atom-sum identity, so nothing is
lost: the level, the strictness and the tie predicate all cross unchanged.
-/

theorem dominatesAtLevel_splitDesign_image_castSucc_iff (D : WeightedDesign m k)
    (splitLabel : Fin m) {share : ℝ} (hshareLow : 0 < share)
    (hshareHigh : share < D.weight splitLabel) (baseSubset : Finset (Fin m)) (level : ℝ) :
    DominatesAtLevel (splitDesign D splitLabel share hshareLow hshareHigh)
        (baseSubset.image Fin.castSucc) level
      ↔ DominatesAtLevel D baseSubset level := by
  rw [DominatesAtLevel, DominatesAtLevel,
    subsetSum_splitDesign_image_castSucc D splitLabel hshareLow hshareHigh baseSubset]

theorem dominates_splitDesign_image_castSucc_iff (D : WeightedDesign m k) (splitLabel : Fin m)
    {share : ℝ} (hshareLow : 0 < share) (hshareHigh : share < D.weight splitLabel)
    (baseSubset : Finset (Fin m)) :
    Dominates (splitDesign D splitLabel share hshareLow hshareHigh)
        (baseSubset.image Fin.castSucc)
      ↔ Dominates D baseSubset := by
  rw [Dominates, Dominates,
    subsetSum_splitDesign_image_castSucc D splitLabel hshareLow hshareHigh baseSubset]

theorem posDef_splitDesign_image_castSucc_iff (D : WeightedDesign m k) (splitLabel : Fin m)
    {share : ℝ} (hshareLow : 0 < share) (hshareHigh : share < D.weight splitLabel)
    (baseSubset : Finset (Fin m)) :
    (subsetSum (splitDesign D splitLabel share hshareLow hshareHigh)
        (baseSubset.image Fin.castSucc) - 1).PosDef
      ↔ (subsetSum D baseSubset - 1).PosDef := by
  rw [subsetSum_splitDesign_image_castSucc D splitLabel hshareLow hshareHigh baseSubset]

/-- **Domination transfers in both directions.**  Upwards by the plain
embedding, downwards by the fold — a dominating subset upstairs cannot hold both
copies, so the fold applies. -/
theorem exists_dominating_splitDesign_iff (D : WeightedDesign m k) (splitLabel : Fin m)
    {share : ℝ} (hshareLow : 0 < share) (hshareHigh : share < D.weight splitLabel) :
    (∃ C : Finset (Fin (m + 1)), C.card = k
        ∧ Dominates (splitDesign D splitLabel share hshareLow hshareHigh) C)
      ↔ ∃ baseSubset : Finset (Fin m), baseSubset.card = k ∧ Dominates D baseSubset := by
  classical
  constructor
  · rintro ⟨C, hcard, hdominates⟩
    rcases splitDesign_subsetSum_trichotomy D splitLabel hshareLow hshareHigh C with
      hboth | ⟨baseSubset, hbaseCard, hsum⟩
    · exact absurd hdominates (not_dominates_splitDesign_of_both_copies D splitLabel
        hshareLow hshareHigh (le_of_eq hcard) hboth.1 hboth.2)
    · refine ⟨baseSubset, by rw [hbaseCard, hcard], ?_⟩
      show (subsetSum D baseSubset - 1).PosSemidef
      rw [← hsum]
      exact hdominates
  · rintro ⟨baseSubset, hbaseCard, hdominates⟩
    exact ⟨baseSubset.image Fin.castSucc, by rw [card_image_castSucc_eq, hbaseCard],
      (dominates_splitDesign_image_castSucc_iff D splitLabel hshareLow hshareHigh
        baseSubset).mpr hdominates⟩

/-- **The tie predicate transfers in both directions**: splitting an atom neither
creates nor destroys an exact tie, at any share.  This is the margin-level
statement the covering-level `Gtz.gtzWeighted_of_succ` does not give. -/
theorem isTie_splitDesign_iff (D : WeightedDesign m k) (splitLabel : Fin m) {share : ℝ}
    (hshareLow : 0 < share) (hshareHigh : share < D.weight splitLabel) :
    IsTie (splitDesign D splitLabel share hshareLow hshareHigh) ↔ IsTie D := by
  classical
  constructor
  · rintro ⟨hexists, hnostrict⟩
    refine ⟨(exists_dominating_splitDesign_iff D splitLabel hshareLow hshareHigh).mp hexists,
      fun baseSubset hbaseCard => ?_⟩
    rw [← posDef_splitDesign_image_castSucc_iff D splitLabel hshareLow hshareHigh baseSubset]
    exact hnostrict _ (by rw [card_image_castSucc_eq, hbaseCard])
  · rintro ⟨hexists, hnostrict⟩
    refine ⟨(exists_dominating_splitDesign_iff D splitLabel hshareLow hshareHigh).mpr hexists,
      fun C hcard => ?_⟩
    intro hdefinite
    rcases splitDesign_subsetSum_trichotomy D splitLabel hshareLow hshareHigh C with
      hboth | ⟨baseSubset, hbaseCard, hsum⟩
    · exact not_dominates_splitDesign_of_both_copies D splitLabel hshareLow hshareHigh
        (le_of_eq hcard) hboth.1 hboth.2 hdefinite.posSemidef
    · refine hnostrict baseSubset (by rw [hbaseCard, hcard]) ?_
      rw [← hsum]
      exact hdefinite

/-! ## The definite half of the congruence chain

`Gtz.LinAlg.PsdKit` carries the positive-SEMIdefinite half of every step
`weighted_naimark_duality` walks.  Below are the definite companions.  The proofs
are the PSD ones with Cauchy–Schwarz upgraded from `≤` to `<`; the upgrade is
legitimate exactly because the two quantities that could vanish — the probe and
its image — are handled separately, and the image-is-zero branch is where a
naive "strict everywhere" argument would break.

`IsTie` is a PSD claim conjoined with the NEGATION of a definite claim, so the
PSD flip alone transports it in neither direction.  `LoewnerEquiv` bundles the
two verdicts and is what actually crosses.
-/

section StrictCongruence

variable {leftDim rightDim : ℕ}

/-- `I − XᵀX ≻ 0` says exactly that `X` STRICTLY contracts the quadratic form. -/
theorem posDef_one_sub_iff_strictContraction (X : Matrix (Fin leftDim) (Fin rightDim) ℝ) :
    (1 - Xᵀ * X).PosDef ↔
      ∀ probe : Fin rightDim → ℝ, probe ≠ 0 →
        (X *ᵥ probe) ⬝ᵥ (X *ᵥ probe) < probe ⬝ᵥ probe := by
  have hquad : ∀ probe : Fin rightDim → ℝ,
      probe ⬝ᵥ ((1 - Xᵀ * X) *ᵥ probe)
        = probe ⬝ᵥ probe - (X *ᵥ probe) ⬝ᵥ (X *ᵥ probe) := by
    intro probe
    rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec, ← Matrix.mulVec_mulVec,
      dotProduct_comm probe (Xᵀ *ᵥ (X *ᵥ probe)), dotProduct_mulVec_transpose]
  constructor
  · intro hdefinite probe hprobe
    have hstep := (Matrix.posDef_iff_dotProduct_mulVec.mp hdefinite).2 hprobe
    rw [star_trivial, hquad probe] at hstep
    linarith
  · intro hstrict
    refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨?_, fun probe hprobe => ?_⟩
    · refine isHermitian_of_transpose_eq ?_
      rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_mul,
        Matrix.transpose_transpose]
    · rw [star_trivial, hquad probe]
      linarith [hstrict probe hprobe]

/-- **The Cauchy–Schwarz flip, definite version**: a STRICT quadratic-form
contraction transposes.  When `Xᵀw` vanishes the conclusion is the positivity of
`|w|²`; otherwise `|Xᵀw|⁴ ≤ |w|²·|X(Xᵀw)|² < |w|²·|Xᵀw|²` and one factor of
`|Xᵀw|² > 0` cancels. -/
theorem strictContraction_flip (X : Matrix (Fin leftDim) (Fin rightDim) ℝ)
    (hstrict : ∀ probe : Fin rightDim → ℝ, probe ≠ 0 →
      (X *ᵥ probe) ⬝ᵥ (X *ᵥ probe) < probe ⬝ᵥ probe)
    (coprobe : Fin leftDim → ℝ) (hcoprobe : coprobe ≠ 0) :
    (Xᵀ *ᵥ coprobe) ⬝ᵥ (Xᵀ *ᵥ coprobe) < coprobe ⬝ᵥ coprobe := by
  rcases eq_or_ne (Xᵀ *ᵥ coprobe) 0 with hzero | hnonzero
  · rw [hzero, dotProduct_zero]
    exact dotProduct_self_pos hcoprobe
  · have hkey : (Xᵀ *ᵥ coprobe) ⬝ᵥ (Xᵀ *ᵥ coprobe)
        = coprobe ⬝ᵥ (X *ᵥ (Xᵀ *ᵥ coprobe)) :=
      dotProduct_mulVec_transpose X coprobe (Xᵀ *ᵥ coprobe)
    have hcoPos := dotProduct_self_pos hcoprobe
    have hselfPos := dotProduct_self_pos hnonzero
    have hbound : (coprobe ⬝ᵥ (X *ᵥ (Xᵀ *ᵥ coprobe))) ^ 2
        < (coprobe ⬝ᵥ coprobe) * ((Xᵀ *ᵥ coprobe) ⬝ᵥ (Xᵀ *ᵥ coprobe)) := by
      calc (coprobe ⬝ᵥ (X *ᵥ (Xᵀ *ᵥ coprobe))) ^ 2
          ≤ (coprobe ⬝ᵥ coprobe)
              * ((X *ᵥ (Xᵀ *ᵥ coprobe)) ⬝ᵥ (X *ᵥ (Xᵀ *ᵥ coprobe))) :=
            dotProduct_sq_le_mul coprobe (X *ᵥ (Xᵀ *ᵥ coprobe))
        _ < (coprobe ⬝ᵥ coprobe) * ((Xᵀ *ᵥ coprobe) ⬝ᵥ (Xᵀ *ᵥ coprobe)) :=
            mul_lt_mul_of_pos_left (hstrict _ hnonzero) hcoPos
    rw [← hkey] at hbound
    nlinarith [hbound, hselfPos]

/-- **The rectangular transfer, definite version**: `I − XᵀX ≻ 0 ⟺ I − XXᵀ ≻ 0`. -/
theorem posDef_one_sub_transpose_comm (X : Matrix (Fin leftDim) (Fin rightDim) ℝ) :
    (1 - Xᵀ * X).PosDef ↔ (1 - X * Xᵀ).PosDef := by
  have hflipped := posDef_one_sub_iff_strictContraction Xᵀ
  rw [Matrix.transpose_transpose] at hflipped
  rw [posDef_one_sub_iff_strictContraction X, hflipped]
  constructor
  · exact fun hstrict coprobe hcoprobe => strictContraction_flip X hstrict coprobe hcoprobe
  · intro hstrict probe hprobe
    have hback := strictContraction_flip Xᵀ hstrict probe hprobe
    rwa [Matrix.transpose_transpose] at hback

/-- **The square expansion transfer, definite version**: `MᵀM ≻ I ⟺ MMᵀ ≻ I`. -/
theorem posDef_transpose_mul_sub_one_comm (M : Matrix (Fin leftDim) (Fin leftDim) ℝ) :
    (Mᵀ * M - 1).PosDef ↔ (M * Mᵀ - 1).PosDef := by
  have hexpand : ∀ N : Matrix (Fin leftDim) (Fin leftDim) ℝ,
      (Nᵀ * N - 1).PosDef ↔
        ∀ probe : Fin leftDim → ℝ, probe ≠ 0 →
          probe ⬝ᵥ probe < (N *ᵥ probe) ⬝ᵥ (N *ᵥ probe) := by
    intro N
    have hquad : ∀ probe : Fin leftDim → ℝ,
        probe ⬝ᵥ ((Nᵀ * N - 1) *ᵥ probe)
          = (N *ᵥ probe) ⬝ᵥ (N *ᵥ probe) - probe ⬝ᵥ probe := by
      intro probe
      rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec, ← Matrix.mulVec_mulVec,
        dotProduct_comm probe (Nᵀ *ᵥ (N *ᵥ probe)), dotProduct_mulVec_transpose]
    constructor
    · intro hdefinite probe hprobe
      have hstep := (Matrix.posDef_iff_dotProduct_mulVec.mp hdefinite).2 hprobe
      rw [star_trivial, hquad probe] at hstep
      linarith
    · intro hstrict
      refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨?_, fun probe hprobe => ?_⟩
      · refine isHermitian_of_transpose_eq ?_
        rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_mul,
          Matrix.transpose_transpose]
      · rw [star_trivial, hquad probe]
        linarith [hstrict probe hprobe]
  have hdet : ∀ N : Matrix (Fin leftDim) (Fin leftDim) ℝ,
      (∀ probe : Fin leftDim → ℝ, probe ≠ 0 →
        probe ⬝ᵥ probe < (N *ᵥ probe) ⬝ᵥ (N *ᵥ probe)) → IsUnit N.det := by
    intro N hstrict
    rw [isUnit_iff_ne_zero]
    intro hvanishes
    obtain ⟨witness, hwitnessNonzero, hkernel⟩ :=
      Matrix.exists_mulVec_eq_zero_iff.mpr hvanishes
    have hstep := hstrict witness hwitnessNonzero
    rw [hkernel, dotProduct_zero] at hstep
    exact absurd (dotProduct_self_pos hwitnessNonzero) (by linarith)
  have hdir : ∀ N : Matrix (Fin leftDim) (Fin leftDim) ℝ,
      (Nᵀ * N - 1).PosDef → (N * Nᵀ - 1).PosDef := by
    intro N hdefinite
    have hstrict := (hexpand N).mp hdefinite
    have hNdet := hdet N hstrict
    have hcontrInv : ∀ coprobe : Fin leftDim → ℝ, coprobe ≠ 0 →
        (N⁻¹ *ᵥ coprobe) ⬝ᵥ (N⁻¹ *ᵥ coprobe) < coprobe ⬝ᵥ coprobe := by
      intro coprobe hcoprobe
      have hrecover : N *ᵥ (N⁻¹ *ᵥ coprobe) = coprobe := by
        rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv N hNdet, Matrix.one_mulVec]
      have hpreimageNonzero : N⁻¹ *ᵥ coprobe ≠ 0 := by
        intro hzero
        apply hcoprobe
        rw [← hrecover, hzero, Matrix.mulVec_zero]
      have hstep := hstrict (N⁻¹ *ᵥ coprobe) hpreimageNonzero
      rwa [hrecover] at hstep
    have hcontrInvT := strictContraction_flip N⁻¹ hcontrInv
    refine (hexpand Nᵀ).mpr fun coprobe hcoprobe => ?_
    have hrecoverT : (N⁻¹)ᵀ *ᵥ (Nᵀ *ᵥ coprobe) = coprobe := by
      rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul,
        Matrix.mul_nonsing_inv N hNdet, Matrix.transpose_one, Matrix.one_mulVec]
    have himageNonzero : Nᵀ *ᵥ coprobe ≠ 0 := by
      intro hzero
      apply hcoprobe
      rw [← hrecoverT, hzero, Matrix.mulVec_zero]
    have hstep := hcontrInvT (Nᵀ *ᵥ coprobe) himageNonzero
    rwa [hrecoverT] at hstep
  refine ⟨fun hdefinite => hdir M hdefinite, fun hdefinite => ?_⟩
  have hback := hdir Mᵀ (by rwa [Matrix.transpose_transpose])
  rwa [Matrix.transpose_transpose] at hback

end StrictCongruence

/-! ### Two-sided Loewner equivalence -/

/-- **Both Loewner verdicts agree.**  `LoewnerEquiv left right` says the two
symmetric matrices are simultaneously positive semidefinite and simultaneously
positive definite.  It is what `Gtz.IsTie` transports along, and every step of
Naimark's four-congruence chain preserves it. -/
def LoewnerEquiv {leftSize rightSize : ℕ} (left : Matrix (Fin leftSize) (Fin leftSize) ℝ)
    (right : Matrix (Fin rightSize) (Fin rightSize) ℝ) : Prop :=
  (left.PosSemidef ↔ right.PosSemidef) ∧ (left.PosDef ↔ right.PosDef)

namespace LoewnerEquiv

variable {leftSize middleSize rightSize : ℕ}

theorem refl (left : Matrix (Fin leftSize) (Fin leftSize) ℝ) : LoewnerEquiv left left :=
  ⟨Iff.rfl, Iff.rfl⟩

theorem symm {left : Matrix (Fin leftSize) (Fin leftSize) ℝ}
    {right : Matrix (Fin rightSize) (Fin rightSize) ℝ} (hequiv : LoewnerEquiv left right) :
    LoewnerEquiv right left :=
  ⟨hequiv.1.symm, hequiv.2.symm⟩

theorem trans {left : Matrix (Fin leftSize) (Fin leftSize) ℝ}
    {middle : Matrix (Fin middleSize) (Fin middleSize) ℝ}
    {right : Matrix (Fin rightSize) (Fin rightSize) ℝ}
    (hfirst : LoewnerEquiv left middle) (hsecond : LoewnerEquiv middle right) :
    LoewnerEquiv left right :=
  ⟨hfirst.1.trans hsecond.1, hfirst.2.trans hsecond.2⟩

theorem of_eq {left right : Matrix (Fin leftSize) (Fin leftSize) ℝ} (heq : left = right) :
    LoewnerEquiv left right := by
  rw [heq]
  exact refl right

end LoewnerEquiv

/-- **Invertible congruence is a Loewner equivalence** — both verdicts at once. -/
theorem loewnerEquiv_congr_right {size : ℕ} {form congruence : Matrix (Fin size) (Fin size) ℝ}
    (hsymmetric : formᵀ = form) (hcongruenceUnit : IsUnit congruence.det) :
    LoewnerEquiv form (congruenceᵀ * form * congruence) :=
  ⟨posSemidef_congr_right hsymmetric hcongruenceUnit,
    posDef_congr_right hsymmetric hcongruenceUnit⟩

/-- **The rectangular contraction flip is a Loewner equivalence.** -/
theorem loewnerEquiv_one_sub_transpose_comm {leftDim rightDim : ℕ}
    (X : Matrix (Fin leftDim) (Fin rightDim) ℝ) :
    LoewnerEquiv (1 - Xᵀ * X) (1 - X * Xᵀ) :=
  ⟨posSemidef_one_sub_transpose_comm X, posDef_one_sub_transpose_comm X⟩

/-- **The square expansion flip is a Loewner equivalence.** -/
theorem loewnerEquiv_transpose_mul_sub_one_comm {size : ℕ}
    (M : Matrix (Fin size) (Fin size) ℝ) :
    LoewnerEquiv (Mᵀ * M - 1) (M * Mᵀ - 1) :=
  ⟨posSemidef_transpose_mul_sub_one_comm M, posDef_transpose_mul_sub_one_comm M⟩

/-! ## Naimark duality, both verdicts

`Gtz.weighted_naimark_duality` flips `Dominates` across the dual.  The chain it
walks — Parseval complement, whitening congruence, Cauchy–Schwarz transfer, two
diagonal congruences, orthonormal completeness, square transfer — consists
entirely of steps that are `LoewnerEquiv`, so the DEFINITE verdict crosses too.
That is what `IsTie` needs, and the PSD statement alone does not give it: `IsTie`
asserts that some subset dominates AND that none dominates strictly, and the
second conjunct is a negated definite claim.

PROVENANCE, stated precisely rather than gestured at: the construction below is
COPIED from `Gtz.weighted_naimark_duality` — same whitener, same co-design, same
orthonormal completion, 222 of 240 lines byte-identical, `-- STEP N` markers
included so the two read alike.  What is new is the last dozen lines, where the
chain is walked ONCE in `LoewnerEquiv` instead of twice in `PosSemidef`.  Since
`Dominates D C` unfolds to `(subsetSum D C − 1).PosSemidef`, the old theorem is
the first projection of the new one; `weighted_naimark_duality_of_loewnerEquiv`
proves that in two lines and is the retirement path for the older proof.

TRAP for anyone reusing this.  The dual here is NOT the textbook Naimark
complement.  The natural choice — rows `√t_c · g_c`, which are orthonormal by
Parseval — makes the flip FALSE; an adversarial audit measured one to two
PSD/PosDef mismatches per random `(5,3)` design with it.  The correct isometry is
the one below, rows `√(1 − t_c) · (Rᵀ g_c)` where `R` whitens the CO-Parseval
operator `Σ_c (1 − t_c) A_c`.  The reason is that `Dominates` is weight-free
while Parseval is not, so the complement that has to be orthonormal is the one
built from `1 − t_c`.
-/

/-- **Naimark duality as a two-sided Loewner equivalence.**  For every weighted
`(m,k)`-design there is a dual `(m, m−k)`-design with the same weights whose gap
matrix at `Cᶜ` has the SAME positive-semidefinite and positive-definite verdicts
as the primal gap matrix at `C`. -/
theorem exists_naimarkDual_loewnerEquiv (hk : 1 ≤ k) (hkm : k + 1 ≤ m)
    (D : WeightedDesign m k) :
    ∃ dualDesign : WeightedDesign m (m - k),
      (∀ c, dualDesign.weight c = D.weight c) ∧
      ∀ C : Finset (Fin m), C.card = k →
        LoewnerEquiv (subsetSum D C - 1) (subsetSum dualDesign Cᶜ - 1) := by
  have hm2 : 2 ≤ m := by omega
  have hspos : ∀ c, 0 < 1 - D.weight c := fun c => by
    linarith [weight_lt_one D hm2 c]
  obtain ⟨R, hRdet, hRWR⟩ := exists_congruence_to_one (coParseval_posDef D hm2)
  set Amat : Matrix (Fin m) (Fin k) ℝ :=
    Matrix.of (fun c j =>
      Real.sqrt (1 - D.weight c) * (Rᵀ *ᵥ D.atom c) j) with hAmat
  have hconj : Rᵀ * (∑ c, (1 - D.weight c) • atomMatrix (D.atom c)) * R
      = ∑ c, (1 - D.weight c) • atomMatrix (Rᵀ *ᵥ D.atom c) := by
    rw [Matrix.mul_sum, Matrix.sum_mul]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Matrix.mul_smul, Matrix.smul_mul, transpose_mul_atomMatrix_mul]
  have hAA : Amatᵀ * Amat = 1 := by
    rw [← hRWR, hconj]
    ext i j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, hAmat, Matrix.of_apply,
      Matrix.sum_apply, Matrix.smul_apply, atomMatrix, Matrix.vecMulVec_apply,
      smul_eq_mul]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [show Real.sqrt (1 - D.weight c) * (Rᵀ *ᵥ D.atom c) i
          * (Real.sqrt (1 - D.weight c) * (Rᵀ *ᵥ D.atom c) j)
        = (Real.sqrt (1 - D.weight c) * Real.sqrt (1 - D.weight c))
          * ((Rᵀ *ᵥ D.atom c) i * (Rᵀ *ᵥ D.atom c) j) from by ring,
      Real.mul_self_sqrt (hspos c).le]
  obtain ⟨B, hBB, hAB, hcomplete⟩ := exists_orthonormal_completion Amat hAA
  have htpos : ∀ c, 0 < Real.sqrt (D.weight c) := fun c =>
    Real.sqrt_pos.mpr (D.weight_pos c)
  refine ⟨{ atom := fun c => (Real.sqrt (D.weight c))⁻¹ • (fun j => B c j)
            weight := D.weight
            weight_pos := D.weight_pos
            weight_sum_one := D.weight_sum_one
            isParseval := ?_ }, fun c => rfl, ?_⟩
  · calc ∑ c, D.weight c
          • atomMatrix ((Real.sqrt (D.weight c))⁻¹ • (fun j => B c j))
        = ∑ c, atomMatrix (fun j => B c j) := by
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [atomMatrix_smul, smul_smul, inv_pow,
            Real.sq_sqrt (D.weight_pos c).le,
            mul_inv_cancel₀ (D.weight_pos c).ne', one_smul]
      _ = 1 := by rw [← transpose_mul_self_eq_sum_rows, hBB]
  · intro C hC
    have hCc : Cᶜ.card = m - k := by
      rw [Finset.card_compl, Fintype.card_fin, hC]
    set embed : Fin (m - k) → Fin m :=
      fun i => ((Cᶜ.orderIsoOfFin hCc) i).val with hembed
    set Y : Matrix (Fin (m - k)) (Fin k) ℝ :=
      Matrix.of (fun i j => (Rᵀ *ᵥ D.atom (embed i)) j) with hY
    set Z : Matrix (Fin (m - k)) (Fin (m - k)) ℝ :=
      Matrix.of (fun i j => (Real.sqrt (D.weight (embed i)))⁻¹ * B (embed i) j)
      with hZ
    -- STEP 0: the complement dictionary S_C − 1 = W − S_{Cᶜ}
    have hL1 : subsetSum D C - 1
        = (∑ c, (1 - D.weight c) • atomMatrix (D.atom c)) - subsetSum D Cᶜ := by
      have hp := D.isParseval
      rw [← Finset.sum_add_sum_compl C
        (fun c => D.weight c • atomMatrix (D.atom c))] at hp
      have hsplitW : ∑ c, (1 - D.weight c) • atomMatrix (D.atom c)
          = (∑ c ∈ C, (1 - D.weight c) • atomMatrix (D.atom c))
            + ∑ c ∈ Cᶜ, (1 - D.weight c) • atomMatrix (D.atom c) :=
        (Finset.sum_add_sum_compl C _).symm
      have hsub : ∀ S : Finset (Fin m),
          ∑ c ∈ S, (1 - D.weight c) • atomMatrix (D.atom c)
          = (∑ c ∈ S, atomMatrix (D.atom c))
            - ∑ c ∈ S, D.weight c • atomMatrix (D.atom c) := by
        intro S
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun c _ => by rw [sub_smul, one_smul]
      rw [subsetSum, subsetSum, hsplitW, hsub C, hsub Cᶜ, ← hp]
      abel
    -- STEP 1: congruence by the whitening R
    have hWS_symm : ((∑ c, (1 - D.weight c) • atomMatrix (D.atom c))
        - subsetSum D Cᶜ)ᵀ
        = (∑ c, (1 - D.weight c) • atomMatrix (D.atom c)) - subsetSum D Cᶜ := by
      rw [Matrix.transpose_sub, Matrix.transpose_sum, subsetSum,
        Matrix.transpose_sum]
      congr 1
      · exact Finset.sum_congr rfl fun c _ => by
          rw [Matrix.transpose_smul,
            transpose_eq_of_isHermitian (posSemidef_atomMatrix (D.atom c)).1]
      · exact Finset.sum_congr rfl fun c _ =>
          transpose_eq_of_isHermitian (posSemidef_atomMatrix (D.atom c)).1
    have hRconj : Rᵀ * ((∑ c, (1 - D.weight c) • atomMatrix (D.atom c))
          - subsetSum D Cᶜ) * R
        = 1 - Yᵀ * Y := by
      have hYY : Yᵀ * Y = ∑ e ∈ Cᶜ, atomMatrix (Rᵀ *ᵥ D.atom e) := by
        rw [transpose_mul_self_eq_sum_rows,
          ← sum_orderIsoOfFin Cᶜ hCc (fun e => atomMatrix (Rᵀ *ᵥ D.atom e))]
        exact Finset.sum_congr rfl fun i _ =>
          congrArg atomMatrix (funext fun j => by simp [hY, hembed])
      have hRS : Rᵀ * subsetSum D Cᶜ * R
          = ∑ e ∈ Cᶜ, atomMatrix (Rᵀ *ᵥ D.atom e) := by
        rw [subsetSum, Matrix.mul_sum, Matrix.sum_mul]
        exact Finset.sum_congr rfl fun e _ => transpose_mul_atomMatrix_mul R _
      rw [Matrix.mul_sub, Matrix.sub_mul, hRWR, hRS, hYY]
    -- STEP 2 matrices: the A-row and B-row Gram formulas
    have hArow : ∀ c e, (Amat * Amatᵀ) c e
        = Real.sqrt (1 - D.weight c) * Real.sqrt (1 - D.weight e)
          * ((Rᵀ *ᵥ D.atom c) ⬝ᵥ (Rᵀ *ᵥ D.atom e)) := by
      intro c e
      simp only [Matrix.mul_apply, Matrix.transpose_apply, hAmat, Matrix.of_apply,
        dotProduct, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    have hYrow : ∀ i i', (Y * Yᵀ) i i'
        = (Rᵀ *ᵥ D.atom (embed i)) ⬝ᵥ (Rᵀ *ᵥ D.atom (embed i')) := by
      intro i i'
      simp only [Matrix.mul_apply, Matrix.transpose_apply, hY, Matrix.of_apply,
        dotProduct]
    have hBrow : ∀ i i', (Z * Zᵀ) i i'
        = (Real.sqrt (D.weight (embed i)))⁻¹
          * (Real.sqrt (D.weight (embed i')))⁻¹
          * ∑ j, B (embed i) j * B (embed i') j := by
      intro i i'
      simp only [Matrix.mul_apply, Matrix.transpose_apply, hZ, Matrix.of_apply,
        Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    have hembinj : Function.Injective embed := fun i i' hii' =>
      (Cᶜ.orderIsoOfFin hCc).toEquiv.injective (Subtype.val_injective hii')
    -- STEP 2: diagonal congruence by √s carries 1 − YYᵀ to D_s − (AAᵀ)|_{Cᶜ}
    have hdiagS : (Matrix.diagonal
          (fun i => Real.sqrt (1 - D.weight (embed i))))ᵀ
          * (1 - Y * Yᵀ)
          * Matrix.diagonal (fun i => Real.sqrt (1 - D.weight (embed i)))
        = Matrix.diagonal (fun i => 1 - D.weight (embed i))
          - Matrix.of (fun i i' => (Amat * Amatᵀ) (embed i) (embed i')) := by
      rw [Matrix.diagonal_transpose]
      ext i i'
      rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
      simp only [Matrix.sub_apply, Matrix.one_apply, Matrix.diagonal_apply,
        Matrix.of_apply]
      rw [hYrow i i', hArow (embed i) (embed i')]
      rcases eq_or_ne i i' with rfl | hne
      · rw [if_pos rfl, if_pos rfl]
        have hss := Real.mul_self_sqrt (hspos (embed i)).le
        linear_combination hss
      · rw [if_neg hne, if_neg hne]
        ring
    -- STEP 3: completeness swaps the A-block for the B-block
    have hcompl_entry : ∀ i i',
        (Amat * Amatᵀ) (embed i) (embed i') + (B * Bᵀ) (embed i) (embed i')
          = if i = i' then 1 else 0 := by
      intro i i'
      have hce := congrFun (congrFun hcomplete (embed i)) (embed i')
      rw [Matrix.add_apply, Matrix.one_apply] at hce
      rwa [if_congr ⟨fun h => hembinj h, fun h => h ▸ rfl⟩ rfl rfl] at hce
    have hL6 : Matrix.diagonal (fun i => 1 - D.weight (embed i))
          - Matrix.of (fun i i' => (Amat * Amatᵀ) (embed i) (embed i'))
        = Matrix.of (fun i i' => (B * Bᵀ) (embed i) (embed i'))
          - Matrix.diagonal (fun i => D.weight (embed i)) := by
      ext i i'
      simp only [Matrix.sub_apply, Matrix.diagonal_apply, Matrix.of_apply]
      have hce := hcompl_entry i i'
      rcases eq_or_ne i i' with rfl | hne
      · rw [if_pos rfl] at hce
        rw [if_pos rfl, if_pos rfl]
        linarith
      · rw [if_neg hne] at hce
        rw [if_neg hne, if_neg hne]
        linarith
    -- STEP 4: diagonal congruence by 1/√t carries it to ZZᵀ − 1
    have hdiagT : (Matrix.diagonal
          (fun i => (Real.sqrt (D.weight (embed i)))⁻¹))ᵀ
          * (Matrix.of (fun i i' => (B * Bᵀ) (embed i) (embed i'))
              - Matrix.diagonal (fun i => D.weight (embed i)))
          * Matrix.diagonal (fun i => (Real.sqrt (D.weight (embed i)))⁻¹)
        = Z * Zᵀ - 1 := by
      rw [Matrix.diagonal_transpose]
      ext i i'
      rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
      simp only [Matrix.sub_apply, Matrix.one_apply, Matrix.diagonal_apply,
        Matrix.of_apply]
      rw [hBrow i i',
        show (B * Bᵀ) (embed i) (embed i')
            = ∑ j, B (embed i) j * B (embed i') j from by
          simp [Matrix.mul_apply, Matrix.transpose_apply]]
      rcases eq_or_ne i i' with rfl | hne
      · rw [if_pos rfl, if_pos rfl]
        have htt := Real.mul_self_sqrt (D.weight_pos (embed i)).le
        have hinv1 : (Real.sqrt (D.weight (embed i)))⁻¹ * D.weight (embed i)
            * (Real.sqrt (D.weight (embed i)))⁻¹ = 1 := by
          rw [show (Real.sqrt (D.weight (embed i)))⁻¹ * D.weight (embed i)
                * (Real.sqrt (D.weight (embed i)))⁻¹
              = D.weight (embed i) * (Real.sqrt (D.weight (embed i))
                  * Real.sqrt (D.weight (embed i)))⁻¹ from by
            rw [mul_inv]; ring,
            htt, mul_inv_cancel₀ (D.weight_pos (embed i)).ne']
        linear_combination (-1 : ℝ) * hinv1
      · rw [if_neg hne, if_neg hne]
        ring
    -- STEP 5: the dual dictionary ZᵀZ = S′_{Cᶜ}
    have hZZdual : Zᵀ * Z = ∑ e ∈ Cᶜ,
        atomMatrix ((Real.sqrt (D.weight e))⁻¹ • (fun j => B e j)) := by
      rw [transpose_mul_self_eq_sum_rows, ← sum_orderIsoOfFin Cᶜ hCc
        (fun e => atomMatrix ((Real.sqrt (D.weight e))⁻¹ • (fun j => B e j)))]
      refine Finset.sum_congr rfl fun i _ => congrArg atomMatrix (funext fun j => ?_)
      simp [hZ, hembed, Pi.smul_apply, smul_eq_mul]
    have hXsymm1 : (1 - Y * Yᵀ)ᵀ = 1 - Y * Yᵀ := by
      rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_mul,
        Matrix.transpose_transpose]
    have hBBT : (B * Bᵀ)ᵀ = B * Bᵀ := by
      rw [Matrix.transpose_mul, Matrix.transpose_transpose]
    have hXsymm2 : (Matrix.of (fun i i' => (B * Bᵀ) (embed i) (embed i'))
          - Matrix.diagonal (fun i => D.weight (embed i)))ᵀ
        = Matrix.of (fun i i' => (B * Bᵀ) (embed i) (embed i'))
          - Matrix.diagonal (fun i => D.weight (embed i)) := by
      rw [Matrix.transpose_sub, Matrix.diagonal_transpose]
      congr 1
      ext i i'
      rw [Matrix.transpose_apply, Matrix.of_apply, Matrix.of_apply]
      have hsym := congrFun (congrFun hBBT (embed i)) (embed i')
      rw [Matrix.transpose_apply] at hsym
      exact hsym
    have hdetS : IsUnit (Matrix.diagonal
        (fun i => Real.sqrt (1 - D.weight (embed i)))).det := by
      rw [Matrix.det_diagonal, isUnit_iff_ne_zero]
      exact Finset.prod_ne_zero_iff.mpr fun i _ =>
        (Real.sqrt_pos.mpr (hspos (embed i))).ne'
    have hdetT : IsUnit (Matrix.diagonal
        (fun i => (Real.sqrt (D.weight (embed i)))⁻¹)).det := by
      rw [Matrix.det_diagonal, isUnit_iff_ne_zero]
      exact Finset.prod_ne_zero_iff.mpr fun i _ =>
        inv_ne_zero (htpos (embed i)).ne'
    -- the chain, walked once, carrying both verdicts
    show LoewnerEquiv (subsetSum D C - 1)
      ((∑ e ∈ Cᶜ, atomMatrix ((Real.sqrt (D.weight e))⁻¹ • (fun j => B e j))) - 1)
    refine LoewnerEquiv.trans (LoewnerEquiv.of_eq hL1) ?_
    refine LoewnerEquiv.trans (loewnerEquiv_congr_right hWS_symm hRdet) ?_
    rw [hRconj]
    refine LoewnerEquiv.trans (loewnerEquiv_one_sub_transpose_comm Y) ?_
    refine LoewnerEquiv.trans (loewnerEquiv_congr_right hXsymm1 hdetS) ?_
    rw [hdiagS, hL6]
    refine LoewnerEquiv.trans (loewnerEquiv_congr_right hXsymm2 hdetT) ?_
    rw [hdiagT, ← hZZdual]
    exact LoewnerEquiv.symm (loewnerEquiv_transpose_mul_sub_one_comm Z)

/-- **The shipped PSD flip is a corollary.**  `Gtz.weighted_naimark_duality` is
the first projection of `exists_naimarkDual_loewnerEquiv`, because `Dominates D C`
IS `(subsetSum D C − 1).PosSemidef`.  Shipped so that the ~280-line proof in
`Gtz.Reduction.Naimark` can be replaced by these two lines instead of maintained
beside a copy of itself; this file may not edit that module.

RETIREMENT IS NOT A BODY SWAP — READ BEFORE ATTEMPTING IT.  This file IMPORTS
`Gtz.Reduction.Naimark`, so `Gtz.weighted_naimark_duality` cannot cite anything
declared here: substituting `exact weighted_naimark_duality_of_loewnerEquiv hk
hkm D` for its body creates an import cycle and does not compile.  The
retirement therefore requires RELOCATING the `LoewnerEquiv` kit and
`exists_naimarkDual_loewnerEquiv` into `Gtz.Reduction.Naimark` itself (or into a
new module below it), after which BOTH statements are corollaries of the single
chain.  That is a ~300-line move through a module in the import path of most of
the tree, not a two-line edit, and earlier campaign notes that described it as
"compiled and ready" were wrong about the direction of the dependency. -/
theorem weighted_naimark_duality_of_loewnerEquiv (hk : 1 ≤ k) (hkm : k + 1 ≤ m)
    (D : WeightedDesign m k) :
    ∃ dualDesign : WeightedDesign m (m - k),
      (∀ c, dualDesign.weight c = D.weight c) ∧
      ∀ C : Finset (Fin m), C.card = k → (Dominates D C ↔ Dominates dualDesign Cᶜ) := by
  obtain ⟨dualDesign, hweights, hequiv⟩ := exists_naimarkDual_loewnerEquiv hk hkm D
  exact ⟨dualDesign, hweights, fun C hC => (hequiv C hC).1⟩

/-- **The tie predicate crosses Naimark duality.**  A design is an exact tie iff
its dual is: the dominating subset maps to its complement, and the absence of a
strict dominator maps back along the same bijection.  This is the statement the
PSD-only flip cannot give — it needs the definite half of the chain. -/
theorem isTie_naimarkDual (hk : 1 ≤ k) (hkm : k + 1 ≤ m) (D : WeightedDesign m k) :
    ∃ dualDesign : WeightedDesign m (m - k),
      (∀ c, dualDesign.weight c = D.weight c) ∧ (IsTie D ↔ IsTie dualDesign) := by
  classical
  obtain ⟨dualDesign, hweights, hequiv⟩ := exists_naimarkDual_loewnerEquiv hk hkm D
  refine ⟨dualDesign, hweights, ?_⟩
  have hcomplCard : ∀ C : Finset (Fin m), C.card = k → Cᶜ.card = m - k := by
    intro C hC
    rw [Finset.card_compl, Fintype.card_fin, hC]
  have hcomplCardBack : ∀ E : Finset (Fin m), E.card = m - k → Eᶜ.card = k := by
    intro E hE
    rw [Finset.card_compl, Fintype.card_fin, hE]
    omega
  constructor
  · rintro ⟨⟨C, hcard, hdominates⟩, hnostrict⟩
    refine ⟨⟨Cᶜ, hcomplCard C hcard, (hequiv C hcard).1.mp hdominates⟩,
      fun E hE hdefinite => ?_⟩
    refine hnostrict Eᶜ (hcomplCardBack E hE) ?_
    refine (hequiv Eᶜ (hcomplCardBack E hE)).2.mpr ?_
    rwa [compl_compl]
  · rintro ⟨⟨E, hE, hdominates⟩, hnostrict⟩
    refine ⟨⟨Eᶜ, hcomplCardBack E hE, (hequiv Eᶜ (hcomplCardBack E hE)).1.mpr
      (by rwa [compl_compl])⟩, fun C hcard hdefinite => ?_⟩
    exact hnostrict Cᶜ (hcomplCard C hcard) ((hequiv C hcard).2.mp hdefinite)

/-! ## Whitening a near-Parseval family

A family whose frame operator is only PINCHED between `(1 − eta)·I` and
`(1 + eta)·I` is not a design.  Whitening makes it one, exactly — Parseval on the
nose, no approximation — and the Rayleigh floor crosses in both directions with
the factors `1 − eta` (whitened to raw) and `1/(1 + eta)` (raw to whitened).

The downward half is `Gtz.whitenedPullback_form_ge` at `defect = 1 −
frameOperator`; nothing here re-proves it.  What is added is the design
constructor generalising `Gtz.deflatedDesign` from `1 − t_e·A_e` to an arbitrary
positive-definite frame operator, the pinch predicate, and the upward half.
-/

/-- **The whitened family is an exact design.**  Conjugating every atom by the
whitener of the frame operator turns any positively weighted family with weights
summing to one into a genuine `WeightedDesign` — Parseval holds identically, not
approximately. -/
noncomputable def whitenedFamilyDesign (atomFamily : Fin m → (Fin k → ℝ))
    (weightFamily : Fin m → ℝ) (hweightPos : ∀ c, 0 < weightFamily c)
    (hweightSumOne : ∑ c, weightFamily c = 1)
    (whitener : Matrix (Fin k) (Fin k) ℝ)
    (hwhiten : whitenerᵀ * (∑ c, weightFamily c • atomMatrix (atomFamily c)) * whitener = 1) :
    WeightedDesign m k where
  atom c := whitenerᵀ *ᵥ atomFamily c
  weight := weightFamily
  weight_pos := hweightPos
  weight_sum_one := hweightSumOne
  isParseval := by
    have hconjugate : ∑ c, weightFamily c • atomMatrix (whitenerᵀ *ᵥ atomFamily c)
        = whitenerᵀ * (∑ c, weightFamily c • atomMatrix (atomFamily c)) * whitener := by
      rw [Matrix.mul_sum, Matrix.sum_mul]
      exact Finset.sum_congr rfl fun c _ => by
        rw [Matrix.mul_smul, Matrix.smul_mul, transpose_mul_atomMatrix_mul]
    rw [hconjugate, hwhiten]

/-- **The pinch**: the frame operator sits between `(1 − eta)·I` and
`(1 + eta)·I` in the Loewner order.  At `eta = 0` this says the family is already
Parseval. -/
def FrameOperatorIsPinched (frameOperator : Matrix (Fin k) (Fin k) ℝ) (etaBound : ℝ) : Prop :=
  (frameOperator - (1 - etaBound) • (1 : Matrix (Fin k) (Fin k) ℝ)).PosSemidef ∧
  ((1 + etaBound) • (1 : Matrix (Fin k) (Fin k) ℝ) - frameOperator).PosSemidef

/-- The LOWER pinch alone gives the Rayleigh floor; the upper half is not used,
so it is not demanded. -/
theorem framePinched_form_lower {frameOperator : Matrix (Fin k) (Fin k) ℝ} {etaBound : ℝ}
    (hlowerPinch : (frameOperator - (1 - etaBound) • (1 : Matrix (Fin k) (Fin k) ℝ)).PosSemidef)
    (probe : Fin k → ℝ) :
    (1 - etaBound) * (probe ⬝ᵥ probe) ≤ probe ⬝ᵥ (frameOperator *ᵥ probe) := by
  have hstep := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hlowerPinch).2 probe
  rw [star_trivial, Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec,
    Matrix.one_mulVec, dotProduct_smul, smul_eq_mul] at hstep
  linarith

/-- The UPPER pinch alone gives the Rayleigh cap. -/
theorem framePinched_form_upper {frameOperator : Matrix (Fin k) (Fin k) ℝ} {etaBound : ℝ}
    (hupperPinch : ((1 + etaBound) • (1 : Matrix (Fin k) (Fin k) ℝ) - frameOperator).PosSemidef)
    (probe : Fin k → ℝ) :
    probe ⬝ᵥ (frameOperator *ᵥ probe) ≤ (1 + etaBound) * (probe ⬝ᵥ probe) := by
  have hstep := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hupperPinch).2 probe
  rw [star_trivial, Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec,
    Matrix.one_mulVec, dotProduct_smul, smul_eq_mul] at hstep
  linarith

/-- A pinched frame operator with `eta < 1` is positive definite, hence whitens. -/
theorem posDef_of_framePinched {frameOperator : Matrix (Fin k) (Fin k) ℝ} {etaBound : ℝ}
    (hetaBelowOne : etaBound < 1) (hpinch : FrameOperatorIsPinched frameOperator etaBound) :
    frameOperator.PosDef := by
  have hsymmetric : frameOperatorᵀ = frameOperator := by
    have hpart := transpose_eq_of_isHermitian hpinch.1.1
    rw [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_one] at hpart
    exact sub_left_inj.mp hpart
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr
    ⟨isHermitian_of_transpose_eq hsymmetric, fun probe hprobe => ?_⟩
  rw [star_trivial]
  have hlower := framePinched_form_lower hpinch.1 probe
  have hlengthPos := dotProduct_self_pos hprobe
  nlinarith [hlower, hlengthPos]

theorem exists_whitener_of_framePinched {frameOperator : Matrix (Fin k) (Fin k) ℝ}
    {etaBound : ℝ} (hetaBelowOne : etaBound < 1)
    (hpinch : FrameOperatorIsPinched frameOperator etaBound) :
    ∃ whitener : Matrix (Fin k) (Fin k) ℝ,
      IsUnit whitener.det ∧ whitenerᵀ * frameOperator * whitener = 1 :=
  exists_congruence_to_one (posDef_of_framePinched hetaBelowOne hpinch)

/-- **A pinched family whitens to a design** — the composite the header advertises
and the only route that turns a pinch into a `WeightedDesign`.  The side condition
`etaBound < 1` is not decoration: at `etaBound >= 1` the lower pinch is vacuous
and the frame operator need not be invertible.  Everything a transfer needs is
returned: the whitener, its unit determinant, the whitening identity, and the
atom and weight formulas. -/
theorem exists_whitenedDesign_of_framePinched (atomFamily : Fin m → (Fin k → ℝ))
    (weightFamily : Fin m → ℝ) (hweightPos : ∀ c, 0 < weightFamily c)
    (hweightSumOne : ∑ c, weightFamily c = 1) {etaBound : ℝ} (hetaBelowOne : etaBound < 1)
    (hpinch : FrameOperatorIsPinched
      (∑ c, weightFamily c • atomMatrix (atomFamily c)) etaBound) :
    ∃ (whitener : Matrix (Fin k) (Fin k) ℝ) (whitenedDesign : WeightedDesign m k),
      IsUnit whitener.det
      ∧ whitenerᵀ * (∑ c, weightFamily c • atomMatrix (atomFamily c)) * whitener = 1
      ∧ (∀ c, whitenedDesign.atom c = whitenerᵀ *ᵥ atomFamily c)
      ∧ (∀ c, whitenedDesign.weight c = weightFamily c) := by
  obtain ⟨whitener, hwhitenerUnit, hwhiten⟩ := exists_whitener_of_framePinched hetaBelowOne hpinch
  exact ⟨whitener,
    whitenedFamilyDesign atomFamily weightFamily hweightPos hweightSumOne whitener hwhiten,
    hwhitenerUnit, hwhiten, fun _ => rfl, fun _ => rfl⟩

/-- **The join.**  The two Rayleigh transfers below are stated for a FREE
`frameOperator` and a raw sum of atom matrices; this identifies that sum with the
whitened design's `subsetSum`, so a consumer never has to re-derive the link. -/
theorem whitenedDesign_subsetSum_eq (atomFamily : Fin m → (Fin k → ℝ))
    (weightFamily : Fin m → ℝ) (hweightPos : ∀ c, 0 < weightFamily c)
    (hweightSumOne : ∑ c, weightFamily c = 1) (whitener : Matrix (Fin k) (Fin k) ℝ)
    (hwhiten : whitenerᵀ * (∑ c, weightFamily c • atomMatrix (atomFamily c)) * whitener = 1)
    (selected : Finset (Fin m)) :
    subsetSum (whitenedFamilyDesign atomFamily weightFamily hweightPos hweightSumOne
        whitener hwhiten) selected
      = ∑ c ∈ selected, atomMatrix (whitenerᵀ *ᵥ atomFamily c) := rfl

/-- **Whitened to raw**: a Rayleigh floor on the whitened family transfers to the
raw family at the cost of the LOWER pinch.  This is
`Gtz.whitenedPullback_form_ge` at `defect = 1 − frameOperator`. -/
theorem rawForm_ge_of_whitenedForm_ge (atomFamily : Fin m → (Fin k → ℝ))
    (selected : Finset (Fin m)) {frameOperator whitener : Matrix (Fin k) (Fin k) ℝ}
    {etaBound level : ℝ} (hwhitenerUnit : IsUnit whitener.det)
    (hwhiten : whitenerᵀ * frameOperator * whitener = 1)
    (hlowerPinch : (frameOperator - (1 - etaBound) • (1 : Matrix (Fin k) (Fin k) ℝ)).PosSemidef)
    (hlevelNonneg : 0 ≤ level)
    (hwhitenedFloor : ∀ preimage : Fin k → ℝ, level * (preimage ⬝ᵥ preimage)
      ≤ preimage ⬝ᵥ ((∑ c ∈ selected, atomMatrix (whitenerᵀ *ᵥ atomFamily c)) *ᵥ preimage))
    (probe : Fin k → ℝ) :
    level * ((1 - etaBound) * (probe ⬝ᵥ probe))
      ≤ probe ⬝ᵥ ((∑ c ∈ selected, atomMatrix (atomFamily c)) *ᵥ probe) := by
  refine whitenedPullback_form_ge (defect := 1 - frameOperator) atomFamily selected
    hwhitenerUnit ?_ ?_ hlevelNonneg hwhitenedFloor probe
  · rw [sub_sub_cancel]
    exact hwhiten
  · intro probeInner
    have hlower := framePinched_form_lower hlowerPinch probeInner
    rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec]
    linarith

/-- **Raw to whitened**: a Rayleigh floor on the raw family transfers to the
whitened family at the cost of the UPPER pinch, in the division-free shape
`level ≤ (1 + eta) · whitenedForm`. -/
theorem whitenedForm_ge_of_rawForm_ge (atomFamily : Fin m → (Fin k → ℝ))
    (selected : Finset (Fin m)) {frameOperator whitener : Matrix (Fin k) (Fin k) ℝ}
    {etaBound level : ℝ} (hwhitenerUnit : IsUnit whitener.det)
    (hwhiten : whitenerᵀ * frameOperator * whitener = 1)
    (hupperPinch : ((1 + etaBound) • (1 : Matrix (Fin k) (Fin k) ℝ) - frameOperator).PosSemidef)
    (hlevelNonneg : 0 ≤ level) (hetaNonneg : 0 ≤ etaBound)
    (hrawFloor : ∀ probe : Fin k → ℝ, level * (probe ⬝ᵥ probe)
      ≤ probe ⬝ᵥ ((∑ c ∈ selected, atomMatrix (atomFamily c)) *ᵥ probe))
    (preimage : Fin k → ℝ) :
    level * (preimage ⬝ᵥ preimage)
      ≤ (1 + etaBound)
        * (preimage ⬝ᵥ ((∑ c ∈ selected, atomMatrix (whitenerᵀ *ᵥ atomFamily c)) *ᵥ preimage)) := by
  have hwhitenDefect : whitenerᵀ * (1 - (1 - frameOperator)) * whitener = 1 := by
    rw [sub_sub_cancel]
    exact hwhiten
  have hrecover : whitener⁻¹ *ᵥ (whitener *ᵥ preimage) = preimage := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul whitener hwhitenerUnit, Matrix.one_mulVec]
  have hformEq := conjugatedFamily_form_at_preimage atomFamily hwhitenerUnit selected
    (whitener *ᵥ preimage)
  rw [hrecover] at hformEq
  have hlengthEq := preimage_length_eq_defect_form hwhitenerUnit hwhitenDefect
    (whitener *ᵥ preimage)
  rw [hrecover] at hlengthEq
  have hlengthCap : preimage ⬝ᵥ preimage
      ≤ (1 + etaBound) * ((whitener *ᵥ preimage) ⬝ᵥ (whitener *ᵥ preimage)) := by
    rw [hlengthEq, sub_sub_cancel]
    exact framePinched_form_upper hupperPinch (whitener *ᵥ preimage)
  have hrawStep := hrawFloor (whitener *ᵥ preimage)
  rw [hformEq]
  nlinarith [hlengthCap, hrawStep, hlevelNonneg, hetaNonneg]

/-! ## Merging an exactly parallel pair

When `g_drop = ratio · g_kept` EXACTLY, the two atoms merge into one and the
pullback costs nothing.  The merged atom's squared scale

  `mergeScaleSq = (t_kept + t_drop·ratio²)/(t_kept + t_drop)`

is the convex combination of `1` and `ratio²` that Parseval forces, hence at most
`max(1, ratio²)`; so replacing the merged atom by whichever ORIGINAL atom is
longer adds a positive semidefinite rank one and can only help.  No margin, no
whitening, no perturbation is consumed.

This is the branch that survives the ceiling warning in the file header.  The
near-parallel version does not: merging at angular defect `eps` leaves a frame
defect of size `Theta(eps)` (`Gtz.mergeFrameDefect_eq`), and pulling that back
needs a strictly positive margin one size down, which
`Gtz.paddedTetraDesign_isTie` forbids globally at rank three.
-/

/-- The squared scale of the merged atom: the weight-average of `1` and
`ratio²`. -/
noncomputable def mergeScaleSq (weightKept weightDrop ratio : ℝ) : ℝ :=
  (weightKept + weightDrop * ratio ^ 2) / (weightKept + weightDrop)

/-- **The merge of an exactly parallel pair.**  Atom `dropLabel` disappears; atom
`keptLabel` — sitting at index `keptIndex` downstairs — is rescaled by
`sqrt (mergeScaleSq)` and carries the summed weight.  Parseval is exact. -/
noncomputable def mergedParallelDesign (D : WeightedDesign (m + 1) k)
    (keptLabel dropLabel : Fin (m + 1)) (ratio : ℝ) (keptIndex : Fin m)
    (hkeptIndex : dropLabel.succAbove keptIndex = keptLabel)
    (hparallel : D.atom dropLabel = ratio • D.atom keptLabel) :
    WeightedDesign m k where
  atom := Function.update (fun index => D.atom (dropLabel.succAbove index)) keptIndex
    (Real.sqrt (mergeScaleSq (D.weight keptLabel) (D.weight dropLabel) ratio)
      • D.atom keptLabel)
  weight := Function.update (fun index => D.weight (dropLabel.succAbove index)) keptIndex
    (D.weight keptLabel + D.weight dropLabel)
  weight_pos := by
    intro index
    rcases eq_or_ne index keptIndex with hiskept | hisother
    · rw [hiskept, Function.update_self]
      linarith [D.weight_pos keptLabel, D.weight_pos dropLabel]
    · rw [Function.update_of_ne hisother]
      exact D.weight_pos _
  weight_sum_one := by
    have hoff : ∑ index, D.weight (dropLabel.succAbove index) = 1 - D.weight dropLabel := by
      have hsplit := Fin.sum_univ_succAbove D.weight dropLabel
      rw [D.weight_sum_one] at hsplit
      linarith
    rw [sum_eq_add_diff_of_agree_off (fun index => D.weight (dropLabel.succAbove index))
      (Function.update (fun index => D.weight (dropLabel.succAbove index)) keptIndex
        (D.weight keptLabel + D.weight dropLabel)) keptIndex
      (fun index hindex => Function.update_of_ne hindex _ _),
      Function.update_self, hoff, hkeptIndex]
    ring
  isParseval := by
    have hweightSumPos : 0 < D.weight keptLabel + D.weight dropLabel := by
      linarith [D.weight_pos keptLabel, D.weight_pos dropLabel]
    have hscaleNonneg :
        0 ≤ mergeScaleSq (D.weight keptLabel) (D.weight dropLabel) ratio := by
      rw [mergeScaleSq]
      refine div_nonneg ?_ hweightSumPos.le
      nlinarith [D.weight_pos keptLabel, D.weight_pos dropLabel, sq_nonneg ratio]
    have hscaleIdentity : (D.weight keptLabel + D.weight dropLabel)
        * mergeScaleSq (D.weight keptLabel) (D.weight dropLabel) ratio
        = D.weight keptLabel + D.weight dropLabel * ratio ^ 2 := by
      rw [mergeScaleSq]
      field_simp
    have hoff : ∑ index, D.weight (dropLabel.succAbove index)
          • atomMatrix (D.atom (dropLabel.succAbove index))
        = 1 - D.weight dropLabel • atomMatrix (D.atom dropLabel) := by
      have hsplit := Fin.sum_univ_succAbove
        (fun c => D.weight c • atomMatrix (D.atom c)) dropLabel
      rw [D.isParseval] at hsplit
      rw [eq_sub_iff_add_eq, add_comm]
      exact hsplit.symm
    rw [sum_eq_add_diff_of_agree_off
      (fun index => D.weight (dropLabel.succAbove index)
        • atomMatrix (D.atom (dropLabel.succAbove index)))
      (fun index =>
        Function.update (fun idx => D.weight (dropLabel.succAbove idx)) keptIndex
            (D.weight keptLabel + D.weight dropLabel) index
          • atomMatrix (Function.update (fun idx => D.atom (dropLabel.succAbove idx)) keptIndex
              (Real.sqrt (mergeScaleSq (D.weight keptLabel) (D.weight dropLabel) ratio)
                • D.atom keptLabel) index))
      keptIndex
      (fun index hindex => by
        rw [Function.update_of_ne hindex, Function.update_of_ne hindex]),
      Function.update_self, Function.update_self, hoff, hkeptIndex, hparallel,
      atomMatrix_smul, atomMatrix_smul, Real.sq_sqrt hscaleNonneg]
    have hmerged : (D.weight keptLabel + D.weight dropLabel)
          • (mergeScaleSq (D.weight keptLabel) (D.weight dropLabel) ratio
            • atomMatrix (D.atom keptLabel))
        = D.weight keptLabel • atomMatrix (D.atom keptLabel)
          + D.weight dropLabel • (ratio ^ 2 • atomMatrix (D.atom keptLabel)) := by
      rw [smul_smul, smul_smul, ← add_smul, hscaleIdentity]
    rw [hmerged]
    abel

theorem mergedParallelDesign_atom_kept (D : WeightedDesign (m + 1) k)
    (keptLabel dropLabel : Fin (m + 1)) (ratio : ℝ) (keptIndex : Fin m)
    (hkeptIndex : dropLabel.succAbove keptIndex = keptLabel)
    (hparallel : D.atom dropLabel = ratio • D.atom keptLabel) :
    (mergedParallelDesign D keptLabel dropLabel ratio keptIndex hkeptIndex hparallel).atom
        keptIndex
      = Real.sqrt (mergeScaleSq (D.weight keptLabel) (D.weight dropLabel) ratio)
        • D.atom keptLabel := by
  show Function.update (fun index => D.atom (dropLabel.succAbove index)) keptIndex
      (Real.sqrt (mergeScaleSq (D.weight keptLabel) (D.weight dropLabel) ratio)
        • D.atom keptLabel) keptIndex
    = Real.sqrt (mergeScaleSq (D.weight keptLabel) (D.weight dropLabel) ratio)
      • D.atom keptLabel
  exact Function.update_self _ _ _

theorem mergedParallelDesign_atom_of_ne (D : WeightedDesign (m + 1) k)
    (keptLabel dropLabel : Fin (m + 1)) (ratio : ℝ) {keptIndex index : Fin m}
    (hkeptIndex : dropLabel.succAbove keptIndex = keptLabel)
    (hparallel : D.atom dropLabel = ratio • D.atom keptLabel) (hne : index ≠ keptIndex) :
    (mergedParallelDesign D keptLabel dropLabel ratio keptIndex hkeptIndex hparallel).atom index
      = D.atom (dropLabel.succAbove index) := by
  show Function.update (fun idx => D.atom (dropLabel.succAbove idx)) keptIndex
      (Real.sqrt (mergeScaleSq (D.weight keptLabel) (D.weight dropLabel) ratio)
        • D.atom keptLabel) index
    = D.atom (dropLabel.succAbove index)
  exact Function.update_of_ne hne _ _

/-- **The merged atom is Loewner-dominated by whichever original is longer.**
The merged squared scale is a convex combination of `1` and `ratio²`, hence at
most the larger; the difference is a nonnegative multiple of a rank-one atom. -/
theorem exists_longerParallelLabel (D : WeightedDesign (m + 1) k)
    (keptLabel dropLabel : Fin (m + 1)) (ratio : ℝ) (keptIndex : Fin m)
    (hkeptIndex : dropLabel.succAbove keptIndex = keptLabel)
    (hparallel : D.atom dropLabel = ratio • D.atom keptLabel) :
    ∃ longerLabel : Fin (m + 1), (longerLabel = keptLabel ∨ longerLabel = dropLabel) ∧
      (atomMatrix (D.atom longerLabel)
        - atomMatrix ((mergedParallelDesign D keptLabel dropLabel ratio keptIndex hkeptIndex
            hparallel).atom keptIndex)).PosSemidef := by
  have hweightSumPos : 0 < D.weight keptLabel + D.weight dropLabel := by
    linarith [D.weight_pos keptLabel, D.weight_pos dropLabel]
  have hscaleNonneg : 0 ≤ mergeScaleSq (D.weight keptLabel) (D.weight dropLabel) ratio := by
    rw [mergeScaleSq]
    refine div_nonneg ?_ hweightSumPos.le
    nlinarith [D.weight_pos keptLabel, D.weight_pos dropLabel, sq_nonneg ratio]
  rw [mergedParallelDesign_atom_kept, atomMatrix_smul, Real.sq_sqrt hscaleNonneg]
  rcases le_or_gt 1 (ratio ^ 2) with hlong | hshort
  · refine ⟨dropLabel, Or.inr rfl, ?_⟩
    have hcap : mergeScaleSq (D.weight keptLabel) (D.weight dropLabel) ratio ≤ ratio ^ 2 := by
      rw [mergeScaleSq, div_le_iff₀ hweightSumPos]
      nlinarith [D.weight_pos keptLabel]
    rw [hparallel, atomMatrix_smul, ← sub_smul]
    exact (posSemidef_atomMatrix (D.atom keptLabel)).smul (by linarith)
  · refine ⟨keptLabel, Or.inl rfl, ?_⟩
    have hcap : mergeScaleSq (D.weight keptLabel) (D.weight dropLabel) ratio ≤ 1 := by
      rw [mergeScaleSq, div_le_one hweightSumPos]
      nlinarith [D.weight_pos dropLabel]
    have hdifference : atomMatrix (D.atom keptLabel)
        - mergeScaleSq (D.weight keptLabel) (D.weight dropLabel) ratio
          • atomMatrix (D.atom keptLabel)
        = (1 - mergeScaleSq (D.weight keptLabel) (D.weight dropLabel) ratio)
          • atomMatrix (D.atom keptLabel) := by
      rw [sub_smul, one_smul]
    rw [hdifference]
    exact (posSemidef_atomMatrix (D.atom keptLabel)).smul (by linarith)

/-- **The merge pullback**: a dominating subset of the merged design lifts to a
dominating subset of the same size upstairs.  If the merged atom was not selected
the atom sums are literally equal; if it was, replace it by the longer original
and the gap only grows. -/
theorem exists_dominating_of_mergedParallel_dominates (D : WeightedDesign (m + 1) k)
    (keptLabel dropLabel : Fin (m + 1)) (ratio : ℝ) (keptIndex : Fin m)
    (hkeptIndex : dropLabel.succAbove keptIndex = keptLabel)
    (hparallel : D.atom dropLabel = ratio • D.atom keptLabel)
    {mergedSubset : Finset (Fin m)}
    (hdominates : Dominates
      (mergedParallelDesign D keptLabel dropLabel ratio keptIndex hkeptIndex hparallel)
      mergedSubset) :
    ∃ C : Finset (Fin (m + 1)), C.card = mergedSubset.card ∧ Dominates D C := by
  classical
  set mergedDesign :=
    mergedParallelDesign D keptLabel dropLabel ratio keptIndex hkeptIndex hparallel
    with hmergedDesign
  have hembedInjective : Function.Injective dropLabel.succAbove := Fin.succAbove_right_injective
  by_cases hkeptMem : keptIndex ∈ mergedSubset
  · obtain ⟨longerLabel, hlongerCase, hlongerPsd⟩ :=
      exists_longerParallelLabel D keptLabel dropLabel ratio keptIndex hkeptIndex hparallel
    set restImage := (mergedSubset.erase keptIndex).image dropLabel.succAbove with hrestImage
    have hlongerNotMem : longerLabel ∉ restImage := by
      rw [hrestImage, Finset.mem_image]
      rintro ⟨index, hindexMem, hindexEq⟩
      rcases hlongerCase with hiskept | hisdrop
      · rw [hiskept, ← hkeptIndex] at hindexEq
        exact (Finset.mem_erase.mp hindexMem).1 (hembedInjective hindexEq)
      · exact (Fin.succAbove_ne dropLabel index) (hindexEq.trans hisdrop)
    have hcardPos : 0 < mergedSubset.card := Finset.card_pos.mpr ⟨keptIndex, hkeptMem⟩
    refine ⟨insert longerLabel restImage, ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem hlongerNotMem, hrestImage,
        Finset.card_image_of_injective _ hembedInjective,
        Finset.card_erase_of_mem hkeptMem]
      omega
    · have hrestSum : ∑ c ∈ restImage, atomMatrix (D.atom c)
          = ∑ index ∈ mergedSubset.erase keptIndex, atomMatrix (mergedDesign.atom index) := by
        rw [hrestImage, Finset.sum_image
          (fun left _ right _ hcast => hembedInjective hcast)]
        refine Finset.sum_congr rfl fun index hindex => ?_
        rw [hmergedDesign, mergedParallelDesign_atom_of_ne D keptLabel dropLabel ratio
          hkeptIndex hparallel (Finset.mem_erase.mp hindex).1]
      have hupperSum : subsetSum D (insert longerLabel restImage)
          = subsetSum mergedDesign mergedSubset
            + (atomMatrix (D.atom longerLabel) - atomMatrix (mergedDesign.atom keptIndex)) := by
        rw [subsetSum, subsetSum, Finset.sum_insert hlongerNotMem, hrestSum,
          ← Finset.sum_erase_add mergedSubset
            (fun index => atomMatrix (mergedDesign.atom index)) hkeptMem]
        abel
      show (subsetSum D (insert longerLabel restImage) - 1).PosSemidef
      rw [hupperSum, show subsetSum mergedDesign mergedSubset
          + (atomMatrix (D.atom longerLabel) - atomMatrix (mergedDesign.atom keptIndex)) - 1
        = (subsetSum mergedDesign mergedSubset - 1)
          + (atomMatrix (D.atom longerLabel)
            - atomMatrix (mergedDesign.atom keptIndex)) from by abel]
      exact Matrix.PosSemidef.add hdominates hlongerPsd
  · refine ⟨mergedSubset.image dropLabel.succAbove, ?_, ?_⟩
    · exact Finset.card_image_of_injective _ hembedInjective
    · have hsumEq : subsetSum D (mergedSubset.image dropLabel.succAbove)
          = subsetSum mergedDesign mergedSubset := by
        rw [subsetSum, subsetSum, Finset.sum_image
          (fun left _ right _ hcast => hembedInjective hcast)]
        refine Finset.sum_congr rfl fun index hindex => ?_
        rw [hmergedDesign, mergedParallelDesign_atom_of_ne D keptLabel dropLabel ratio
          hkeptIndex hparallel (fun hiskept => hkeptMem (hiskept ▸ hindex))]
      show (subsetSum D (mergedSubset.image dropLabel.succAbove) - 1).PosSemidef
      rw [hsumEq]
      exact hdominates

/-- **Branch (i) of the induction, margin-free**: a design carrying an exactly
parallel pair inherits a dominating `k`-subset from one size down, with NO
quantitative hypothesis whatsoever. -/
theorem dominating_of_parallel_pair (D : WeightedDesign (m + 1) k) (hrecursive : GtzWeighted m k)
    {keptLabel dropLabel : Fin (m + 1)} {ratio : ℝ} (hdistinct : keptLabel ≠ dropLabel)
    (hparallel : D.atom dropLabel = ratio • D.atom keptLabel) :
    ∃ C : Finset (Fin (m + 1)), C.card = k ∧ Dominates D C := by
  obtain ⟨keptIndex, hkeptIndex⟩ := Fin.exists_succAbove_eq hdistinct
  obtain ⟨mergedSubset, hmergedCard, hmergedDominates⟩ :=
    hrecursive (mergedParallelDesign D keptLabel dropLabel ratio keptIndex hkeptIndex hparallel)
  obtain ⟨C, hcard, hdominates⟩ := exists_dominating_of_mergedParallel_dominates D keptLabel
    dropLabel ratio keptIndex hkeptIndex hparallel hmergedDominates
  exact ⟨C, by rw [hcard, hmergedCard], hdominates⟩

/-! ## Dropping a dust atom

`Gtz.dominating_of_light_atom` deflates an atom of LEVERAGE at most one, at no
cost.  Branch (ii) is about an atom of small WEIGHT, whose leverage may be large,
and those are different hypotheses: the light-atom pullback step
`(1 − g_d g_dᵀ) ⪰ 0` fails outright for a heavy-leverage atom.  What survives is
the SHARE `s_d = t_d·|g_d|²` (`Gtz.atomShare`): the deflation is legitimate as
soon as `s_d < 1`, and the pullback then costs the factor
`(1 − s_d)/(1 − t_d)` — which is what `Gtz.drop_pullback_form_ge` prices.  The
branch therefore consumes a strictly positive margin one size down, and the
budget inequality below is exactly how much.
-/

/-- **Deflation is legitimate below share one.**  `Gtz.deflatedDesign` needs
`I − t_d·A_d ≻ 0`; the repo derives it from `leverage ≤ 1`, but the true
condition is on the SHARE. -/
theorem posDef_one_sub_smul_atomMatrix_of_share_lt_one {weight : ℝ} {atomVector : Fin k → ℝ}
    (hweightPos : 0 < weight) (hshareBelowOne : weight * leverageOf atomVector < 1) :
    ((1 : Matrix (Fin k) (Fin k) ℝ) - weight • atomMatrix atomVector).PosDef := by
  have hsymmetric : ((1 : Matrix (Fin k) (Fin k) ℝ) - weight • atomMatrix atomVector)ᵀ
      = 1 - weight • atomMatrix atomVector := by
    rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_smul,
      transpose_eq_of_isHermitian (posSemidef_atomMatrix atomVector).1]
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr
    ⟨isHermitian_of_transpose_eq hsymmetric, fun probe hprobe => ?_⟩
  rw [star_trivial, Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec,
    Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  have hcap := atom_form_le_leverage atomVector probe
  have hlengthPos := dotProduct_self_pos hprobe
  nlinarith [hcap, hlengthPos, hweightPos]

/-- The deflated design's atom sum, unwound: the whitened lifted sum, scaled by
the surviving weight mass. -/
theorem subsetSum_deflatedDesign (D : WeightedDesign (m + 1) k) (dropLabel : Fin (m + 1))
    (whitener : Matrix (Fin k) (Fin k) ℝ) (hgap : 0 < 1 - D.weight dropLabel)
    (hwhiten : whitenerᵀ * (1 - D.weight dropLabel • atomMatrix (D.atom dropLabel))
      * whitener = 1)
    (deflatedSubset : Finset (Fin m)) :
    subsetSum (deflatedDesign D dropLabel whitener hgap hwhiten) deflatedSubset
      = (1 - D.weight dropLabel)
        • ∑ c ∈ deflatedSubset.image dropLabel.succAbove,
            atomMatrix (whitenerᵀ *ᵥ D.atom c) := by
  rw [subsetSum, Finset.sum_image
    (fun left _ right _ hcast => Fin.succAbove_right_injective hcast), Finset.smul_sum]
  refine Finset.sum_congr rfl fun index _ => ?_
  show atomMatrix (Real.sqrt (1 - D.weight dropLabel)
      • (whitenerᵀ *ᵥ D.atom (dropLabel.succAbove index))) = _
  rw [atomMatrix_smul, Real.sq_sqrt hgap.le]

/-- **Branch (ii)'s exchange rate, in division-free form.**  A graded dominating
subset of the deflated design lifts to an honestly dominating subset upstairs as
soon as the level pays the budget `1 − t_d ≤ level·(1 − s_d)`.  At `level = 1`
this reads `s_d ≤ t_d`, i.e. `leverage ≤ 1` — recovering
`Gtz.dominating_of_light_atom`; anything heavier must be bought with margin. -/
theorem dominates_image_of_deflated_dominatesAtLevel (D : WeightedDesign (m + 1) k)
    (dropLabel : Fin (m + 1)) {whitener : Matrix (Fin k) (Fin k) ℝ}
    (hwhitenerUnit : IsUnit whitener.det) (hgap : 0 < 1 - D.weight dropLabel)
    (hwhiten : whitenerᵀ * (1 - D.weight dropLabel • atomMatrix (D.atom dropLabel))
      * whitener = 1)
    {deflatedSubset : Finset (Fin m)} {level : ℝ} (hlevelNonneg : 0 ≤ level)
    (hdown : DominatesAtLevel (deflatedDesign D dropLabel whitener hgap hwhiten)
      deflatedSubset level)
    (hbudget : 1 - D.weight dropLabel ≤ level * (1 - atomShare D dropLabel)) :
    Dominates D (deflatedSubset.image dropLabel.succAbove) := by
  have hdownForm := (dominatesAtLevel_iff_form _ _ _).mp hdown
  rw [subsetSum_deflatedDesign] at hdownForm
  have hscaled : ∀ preimage : Fin k → ℝ,
      (level / (1 - D.weight dropLabel)) * (preimage ⬝ᵥ preimage)
        ≤ preimage ⬝ᵥ ((∑ c ∈ deflatedSubset.image dropLabel.succAbove,
            atomMatrix (whitenerᵀ *ᵥ D.atom c)) *ᵥ preimage) := by
    intro preimage
    have hstep := hdownForm preimage
    rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul] at hstep
    rw [div_mul_eq_mul_div, div_le_iff₀ hgap]
    nlinarith [hstep]
  have hpull := drop_pullback_form_ge D dropLabel (deflatedSubset.image dropLabel.succAbove)
    hwhitenerUnit hwhiten (level := level / (1 - D.weight dropLabel))
    (div_nonneg hlevelNonneg hgap.le) hscaled
  refine (dominatesAtLevel_one_iff_dominates D _).mp
    ((dominatesAtLevel_iff_form D _ 1).mpr fun probe => ?_)
  have hstep := hpull probe
  have hlengthNonneg := dotProduct_self_nonneg probe
  have hfactor : 1 ≤ (level / (1 - D.weight dropLabel)) * (1 - atomShare D dropLabel) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hgap]
    linarith [hbudget]
  nlinarith [hstep, hlengthNonneg, hfactor]

/-- **The dust-drop branch, conditional on a level one size down.**  The two
prices are visible: the dropped atom's share must be below one (else the
deflation does not exist), and the level must pay the budget. -/
theorem exists_dominating_of_dust_atom (D : WeightedDesign (m + 1) k)
    (dropLabel : Fin (m + 1)) (hsizeTwo : 2 ≤ m + 1) {level : ℝ} (hlevelNonneg : 0 ≤ level)
    (hshareBelowOne : atomShare D dropLabel < 1) (hfloor : GtzWeightedFloor m k level)
    (hbudget : 1 - D.weight dropLabel ≤ level * (1 - atomShare D dropLabel)) :
    ∃ C : Finset (Fin (m + 1)), C.card = k ∧ Dominates D C := by
  have hgap : 0 < 1 - D.weight dropLabel := by
    linarith [weight_lt_one D hsizeTwo dropLabel]
  have hdeflationPd : ((1 : Matrix (Fin k) (Fin k) ℝ)
      - D.weight dropLabel • atomMatrix (D.atom dropLabel)).PosDef :=
    posDef_one_sub_smul_atomMatrix_of_share_lt_one (D.weight_pos dropLabel) hshareBelowOne
  obtain ⟨whitener, hwhitenerUnit, hwhiten⟩ := exists_congruence_to_one hdeflationPd
  obtain ⟨deflatedSubset, hcard, hdown⟩ :=
    hfloor (deflatedDesign D dropLabel whitener hgap hwhiten)
  refine ⟨deflatedSubset.image dropLabel.succAbove, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ Fin.succAbove_right_injective, hcard]
  · exact dominates_image_of_deflated_dominatesAtLevel D dropLabel hwhitenerUnit hgap hwhiten
      hlevelNonneg hdown hbudget

/-- **The dust-drop branch from a level that need only hold where the deflation
lands.**  Identical to `exists_dominating_of_dust_atom` except that the level is
supplied for the deflated design itself rather than by a global
`Gtz.GtzWeightedFloor` one size down.  This is the form the rank-three ceiling
leaves alive: `dustBudget_forces_leverage_le_one` shows the global form collapses
to `Gtz.dominating_of_light_atom`, and the reason is that the ceiling caps the
GLOBAL level at one.  A level on a proper region is not capped by that argument. -/
theorem exists_dominating_of_dust_atom_of_deflatedLevel (D : WeightedDesign (m + 1) k)
    (dropLabel : Fin (m + 1)) (hgap : 0 < 1 - D.weight dropLabel) {level : ℝ}
    (hlevelNonneg : 0 ≤ level) (hshareBelowOne : atomShare D dropLabel < 1)
    (hdeflatedLevel : ∀ (whitener : Matrix (Fin k) (Fin k) ℝ)
      (hwhiten : whitenerᵀ * (1 - D.weight dropLabel • atomMatrix (D.atom dropLabel))
        * whitener = 1),
      ∃ deflatedSubset : Finset (Fin m), deflatedSubset.card = k
        ∧ DominatesAtLevel (deflatedDesign D dropLabel whitener hgap hwhiten)
            deflatedSubset level)
    (hbudget : 1 - D.weight dropLabel ≤ level * (1 - atomShare D dropLabel)) :
    ∃ C : Finset (Fin (m + 1)), C.card = k ∧ Dominates D C := by
  have hdeflationPd : ((1 : Matrix (Fin k) (Fin k) ℝ)
      - D.weight dropLabel • atomMatrix (D.atom dropLabel)).PosDef :=
    posDef_one_sub_smul_atomMatrix_of_share_lt_one (D.weight_pos dropLabel) hshareBelowOne
  obtain ⟨whitener, hwhitenerUnit, hwhiten⟩ := exists_congruence_to_one hdeflationPd
  obtain ⟨deflatedSubset, hcard, hdown⟩ := hdeflatedLevel whitener hwhiten
  refine ⟨deflatedSubset.image dropLabel.succAbove, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ Fin.succAbove_right_injective, hcard]
  · exact dominates_image_of_deflated_dominatesAtLevel D dropLabel hwhitenerUnit hgap hwhiten
      hlevelNonneg hdown hbudget

/-! ### Why the globally floored form of this branch is inert at rank three

The ceiling caps every rank-three global floor at level one
(`Gtz.gtzWeightedFloor_rankThree_level_le_one`).  At `level <= 1` the budget
`1 − t_d <= level·(1 − s_d)` forces `s_d <= t_d`, i.e. leverage at most one — the
hypothesis of `Gtz.dominating_of_light_atom`, which is already a theorem.  So the
globally floored constructor cannot reach a design the repo could not already
handle.  This is proved, not asserted, and it is the reason
`exists_dominating_of_dust_atom_of_deflatedLevel` exists. -/

/-- **The budget forces a light atom.**  At rank three, any level that satisfies a
global floor at some size `>= 4` is at most one, and then the drop budget says the
dropped atom has leverage at most one. -/
theorem dustBudget_forces_leverage_le_one {floorSize ambientSize : ℕ}
    (hfloorSizeFour : 4 ≤ floorSize) {level : ℝ}
    (hfloor : GtzWeightedFloor floorSize 3 level) (D : WeightedDesign ambientSize 3)
    (dustLabel : Fin ambientSize) (hshareBelowOne : atomShare D dustLabel < 1)
    (hbudget : 1 - D.weight dustLabel ≤ level * (1 - atomShare D dustLabel)) :
    leverageOf (D.atom dustLabel) ≤ 1 := by
  have hlevelCap : level ≤ 1 := gtzWeightedFloor_rankThree_level_le_one hfloorSizeFour hfloor
  have hshareGapPos : 0 < 1 - atomShare D dustLabel := by linarith
  have hweightPos := D.weight_pos dustLabel
  have hshareLeWeight : atomShare D dustLabel ≤ D.weight dustLabel := by
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 - level) hshareGapPos.le]
  rw [atomShare] at hshareLeWeight
  exact le_of_mul_le_mul_left (by rw [mul_one]; exact hshareLeWeight) hweightPos

/-- **The globally floored dust constructor is inert at rank three**: every design
its share budget applies to already carries a light atom, which
`Gtz.dominating_of_light_atom` drops with no budget at all. -/
theorem dustDropCertificate_of_floor_collapses_to_lightAtom {floorSize ambientSize : ℕ}
    (hfloorSizeFour : 4 ≤ floorSize) {weightFloor level : ℝ}
    (hfloor : GtzWeightedFloor floorSize 3 level)
    (hshareBudget : ∀ D : WeightedDesign ambientSize 3, ∀ dustLabel : Fin ambientSize,
      D.weight dustLabel < weightFloor →
        atomShare D dustLabel < 1
        ∧ 1 - D.weight dustLabel ≤ level * (1 - atomShare D dustLabel)) :
    ∀ D : WeightedDesign ambientSize 3, ∀ dustLabel : Fin ambientSize,
      D.weight dustLabel < weightFloor → leverageOf (D.atom dustLabel) ≤ 1 := by
  intro D dustLabel hdustWeight
  obtain ⟨hshareBelowOne, hbudget⟩ := hshareBudget D dustLabel hdustWeight
  exact dustBudget_forces_leverage_le_one hfloorSizeFour hfloor D dustLabel
    hshareBelowOne hbudget

/-- **A graphic design's share does not see the weights.**  If `potential` solves
`L y = b_e` then the share at `e` is `c_e · (b_e ⬝ᵥ y)` — the weight has cancelled,
and the right-hand side depends only on the graph and its conductances.  So
making a graphic atom LIGHT does not make it cheap to drop: its share is fixed and
only its leverage inflates.  That is the structural reason the drop budget of
`dustDropCertificate_of_floor` cannot be met by shrinking a weight, and it is why
the dust branch needs a region-relative level rather than a global one. -/
theorem atomShare_graphicDesign_of_solves {edgeCount vertexRank : ℕ}
    (data : GraphDesignData edgeCount vertexRank) (edge : Fin edgeCount)
    (potential : Fin vertexRank → ℝ)
    (hsolve : data.fullLaplacian *ᵥ potential = data.graph.edgeVector edge) :
    atomShare (graphicDesign data) edge
      = data.conductance edge * (data.graph.edgeVector edge ⬝ᵥ potential) := by
  have hweightNonzero : data.weight edge ≠ 0 := (data.weight_pos edge).ne'
  rw [atomShare, leverageOf_graphicAtom_of_solves data edge potential hsolve,
    graphicDesign_weight]
  field_simp

/-! ## The qualitative three-branch shell

Every hypothesis of the assembly is a named `Prop` and appears in the statement.
Branch (i) is DISCHARGED by `dominating_of_parallel_pair`.  Branches (ii) and
(iii) are the two named residues.

Read the shell as a specification of what is still owed, not as a proof of
anything about `GtzWeighted 6 3` or `GtzWeighted 7 3`: instantiating it requires
producing `DustDropCertificate` and `SpreadFloorCertificate` at a COMMON weight
floor, and NO weight floor makes both non-trivial —
`dustDropCertificate_iff_gtzWeighted_of_sizeInv_lt_floor` proves that above
`1/size` the dust residue IS the goal, and NO-GO 1 of the file header refutes a
margin below it.  The honest shell is the compact one at the end of this file;
this one is kept because it is exhaustive, which the compact one buys only by
naming a fourth residue.
-/

/-- Two distinct atoms of the design are parallel — one is a scalar multiple of
the other.  The scalar may be zero or negative; nothing below needs it signed. -/
def HasParallelPair (D : WeightedDesign m k) : Prop :=
  ∃ (keptLabel dropLabel : Fin m) (ratio : ℝ),
    keptLabel ≠ dropLabel ∧ D.atom dropLabel = ratio • D.atom keptLabel

/-- **Parallel design atoms come from parallel edge vectors.**  A graphic design's
atom is a POSITIVE multiple of the whitened incidence row, and the whitener is
invertible, so proportionality of two atoms descends to proportionality of the
two reduced incidence rows — where it is a statement about small integer vectors.
This is the tool that makes non-parallelism of a named graphic design checkable. -/
theorem exists_edgeVector_parallel_of_graphicAtom_parallel {edgeCount vertexRank : ℕ}
    (data : GraphDesignData edgeCount vertexRank) (keptEdge dropEdge : Fin edgeCount)
    {ratio : ℝ}
    (hparallel :
      (graphicDesign data).atom dropEdge = ratio • (graphicDesign data).atom keptEdge) :
    ∃ scale : ℝ,
      data.graph.edgeVector dropEdge = scale • data.graph.edgeVector keptEdge := by
  have hwhitenerTransposeUnit : IsUnit (data.whitener)ᵀ.det := by
    rw [Matrix.det_transpose]
    exact data.whitener_isUnit
  have hinjective : ∀ leftVector rightVector : Fin vertexRank → ℝ,
      (data.whitener)ᵀ *ᵥ leftVector = (data.whitener)ᵀ *ᵥ rightVector →
        leftVector = rightVector := by
    intro leftVector rightVector himage
    have hpull : ((data.whitener)ᵀ)⁻¹ *ᵥ ((data.whitener)ᵀ *ᵥ leftVector)
        = ((data.whitener)ᵀ)⁻¹ *ᵥ ((data.whitener)ᵀ *ᵥ rightVector) := by rw [himage]
    rwa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hwhitenerTransposeUnit,
      Matrix.one_mulVec, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ hwhitenerTransposeUnit, Matrix.one_mulVec] at hpull
  have hdropScalePos : 0 < Real.sqrt (data.conductance dropEdge / data.weight dropEdge) :=
    Real.sqrt_pos.mpr (div_pos (data.conductance_pos dropEdge) (data.weight_pos dropEdge))
  rw [graphicDesign_atom, graphicDesign_atom, graphicAtom_eq_whitenedRow,
    graphicAtom_eq_whitenedRow, smul_smul] at hparallel
  refine ⟨ratio * Real.sqrt (data.conductance keptEdge / data.weight keptEdge)
      / Real.sqrt (data.conductance dropEdge / data.weight dropEdge), hinjective _ _ ?_⟩
  rw [Matrix.mulVec_smul, div_eq_inv_mul, ← smul_smul, ← hparallel, smul_smul,
    inv_mul_cancel₀ hdropScalePos.ne', one_smul]

/-- The five reduced incidence rows of the diamond `K4 − e`, grounded at the last
vertex: the spine, the two edges to the ground, and the two remaining chords. -/
theorem diamondEdgeVector_eq (edge : Fin 5) :
    diamondData.graph.edgeVector edge
      = ![![1, -1, 0], ![1, 0, -1], ![1, 0, 0], ![0, 1, -1], ![0, 1, 0]] edge := by
  funext coord
  fin_cases edge <;> fin_cases coord <;>
    simp [diamondData, diamondGraph, MultigraphOnGround.edgeVector]

/-- **The diamond has no parallel pair.**  Its five incidence rows are pairwise
non-proportional — every pair is separated by a single vanishing coordinate, or
by two of them — and proportionality of atoms would force proportionality of
rows. -/
theorem not_hasParallelPair_diamondDesign : ¬ HasParallelPair diamondDesign := by
  rintro ⟨keptLabel, dropLabel, ratio, hdistinct, hparallel⟩
  obtain ⟨scale, hvec⟩ :=
    exists_edgeVector_parallel_of_graphicAtom_parallel diamondData keptLabel dropLabel hparallel
  rw [diamondEdgeVector_eq, diamondEdgeVector_eq] at hvec
  have hfirstCoord := congrFun hvec 0
  have hsecondCoord := congrFun hvec 1
  have hthirdCoord := congrFun hvec 2
  clear hvec hparallel
  fin_cases keptLabel <;> fin_cases dropLabel
  all_goals (try exact absurd rfl hdistinct)
  all_goals (try norm_num [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_cons] at hfirstCoord)
  all_goals (try norm_num [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_cons] at hsecondCoord)
  all_goals (try norm_num [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_cons] at hthirdCoord)
  all_goals linarith

/-- **The hinge** (OPEN at sizes six and seven, stated only): at size `size` and
rank `rank`, every exact tie carries a parallel pair.  Exhaustive supporting
evidence exists at `(6,3)`, and the campaign's classification of the equality
locus is consistent with it, but no proof is claimed here and nothing below
assumes it — it is consumed only by `not_isTie_of_hinge_of_spread`, which is an
implication.  It is a size-six/seven statement and not a general one:
`not_hingeHoldsAtSize_five_three` proves it FALSE at `(5,3)`. -/
def HingeHoldsAtSize (size rank : ℕ) : Prop :=
  ∀ D : WeightedDesign size rank, IsTie D → HasParallelPair D

/-- **The hinge is FALSE at `(5,3)`.**  The diamond `M(K4 − e)` is an exact tie
(`Gtz.diamondDesign_isTie`) with no parallel pair — an unsplit tie with a simple
direction matroid.  Both halves are kernel-checked; neither is a citation. -/
theorem not_hingeHoldsAtSize_five_three : ¬ HingeHoldsAtSize 5 3 :=
  fun hhinge => not_hasParallelPair_diamondDesign (hhinge diamondDesign diamondDesign_isTie)

/-- The design carries an atom below the weight floor. -/
def HasDustAtom (D : WeightedDesign m k) (weightFloor : ℝ) : Prop :=
  ∃ dustLabel : Fin m, D.weight dustLabel < weightFloor

/-- The complement of the first two branches: no parallel pair and no dust. -/
def IsSpreadAndFloored (D : WeightedDesign m k) (weightFloor : ℝ) : Prop :=
  ¬ HasParallelPair D ∧ ¬ HasDustAtom D weightFloor

/-- **Branch (ii) as an obligation.** -/
def DustDropCertificate (size rank : ℕ) (weightFloor : ℝ) : Prop :=
  ∀ D : WeightedDesign size rank, HasDustAtom D weightFloor →
    ∃ C : Finset (Fin size), C.card = rank ∧ Dominates D C

/-- **Branch (iii) as an obligation.** -/
def SpreadFloorCertificate (size rank : ℕ) (weightFloor : ℝ) : Prop :=
  ∀ D : WeightedDesign size rank, IsSpreadAndFloored D weightFloor →
    ∃ C : Finset (Fin size), C.card = rank ∧ Dominates D C

/-! ### The weight-floor dichotomy

RETRACTED at this point, and recorded so it is not re-attempted: an earlier
draft shipped a `StratumNeighborhoodCovering` hypothesis — a strictly positive
margin on the spread-and-floored region — advertised as "the one genuinely
analytic input of the plan" and justified by a compactness claim citing
`Gtz.collaredSet`.  Both halves fail.  `Gtz.collaredSet` is the wrong set (it
carries an all-heavy leverage floor this region does not, and no spread
condition at all), and the region is NOT compact, because `¬ HasParallelPair` is
an open condition; its closure meets the tie locus, so the infimum of the margin
over it is zero and the hypothesis is FALSE at rank three for every positive
margin and every weight floor.  See NO-GO 1 in the file header for the exact
witnesses.  The compact replacement is `Gtz.IsFlooredSpreadDesign` and the shell
at the end of this file.

What survives is the dichotomy below, which is proved here: above `1/size` the
dust residue is not a weakening of the goal but the goal itself, and the spread
residue is vacuous. -/

/-- Some atom of any design weighs at most `1/size` — the weights are positive and
sum to one, so they cannot all exceed their average. -/
theorem exists_weight_le_sizeInv (D : WeightedDesign m k) (hsizePos : 0 < m) :
    ∃ lightLabel : Fin m, D.weight lightLabel ≤ (m : ℝ)⁻¹ := by
  by_contra hnone
  simp only [not_exists, not_le] at hnone
  have hnonempty : (Finset.univ : Finset (Fin m)).Nonempty :=
    Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hsizePos)
  have hstrict : ∑ _c : Fin m, (m : ℝ)⁻¹ < ∑ c, D.weight c :=
    Finset.sum_lt_sum_of_nonempty hnonempty fun c _ => hnone c
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hsizePos.ne'), D.weight_sum_one] at hstrict
  exact lt_irrefl 1 hstrict

/-- **Above `1/size` every design carries dust.**  A weight floor larger than the
average is unsatisfiable. -/
theorem hasDustAtom_of_sizeInv_lt_floor (D : WeightedDesign m k) (hsizePos : 0 < m)
    {weightFloor : ℝ} (hfloorAboveAverage : (m : ℝ)⁻¹ < weightFloor) :
    HasDustAtom D weightFloor := by
  obtain ⟨lightLabel, hlight⟩ := exists_weight_le_sizeInv D hsizePos
  exact ⟨lightLabel, lt_of_le_of_lt hlight hfloorAboveAverage⟩

/-- Above `1/size` the spread-and-floored region is EMPTY. -/
theorem not_isSpreadAndFloored_of_sizeInv_lt_floor (D : WeightedDesign m k) (hsizePos : 0 < m)
    {weightFloor : ℝ} (hfloorAboveAverage : (m : ℝ)⁻¹ < weightFloor) :
    ¬ IsSpreadAndFloored D weightFloor :=
  fun hspread => hspread.2 (hasDustAtom_of_sizeInv_lt_floor D hsizePos hfloorAboveAverage)

/-- ...so branch (iii) is vacuously discharged there, which is worth exactly
nothing: branch (ii) has absorbed the whole problem. -/
theorem spreadFloorCertificate_of_sizeInv_lt_floor {size rank : ℕ} (hsizePos : 0 < size)
    {weightFloor : ℝ} (hfloorAboveAverage : (size : ℝ)⁻¹ < weightFloor) :
    SpreadFloorCertificate size rank weightFloor :=
  fun D hspread =>
    absurd hspread (not_isSpreadAndFloored_of_sizeInv_lt_floor D hsizePos hfloorAboveAverage)

/-- **The other horn.**  Above `1/size` the dust certificate is not a weakening of
weighted GTZ — it IS weighted GTZ.  Together with NO-GO 1 (which refutes a margin
below `1/size`) this says no weight floor makes both residues non-trivial. -/
theorem dustDropCertificate_iff_gtzWeighted_of_sizeInv_lt_floor {size rank : ℕ}
    (hsizePos : 0 < size) {weightFloor : ℝ}
    (hfloorAboveAverage : (size : ℝ)⁻¹ < weightFloor) :
    DustDropCertificate size rank weightFloor ↔ GtzWeighted size rank :=
  ⟨fun hdust D => hdust D (hasDustAtom_of_sizeInv_lt_floor D hsizePos hfloorAboveAverage),
    fun hgtz D _ => hgtz D⟩

/-- **What the hinge buys, and what it does not.**  The spread-and-floored region
is tie-free.  That is strictly weaker than a margin: a region can be tie-free and
still have infimal margin zero, because the tie can sit in its CLOSURE, and NO-GO
1 says that is exactly what happens here.  Nothing in this file consumes this
lemma; it is the honest statement of the hinge's payload. -/
theorem not_isTie_of_hinge_of_spread {size rank : ℕ} {weightFloor : ℝ}
    (hhinge : HingeHoldsAtSize size rank) {D : WeightedDesign size rank}
    (hspread : IsSpreadAndFloored D weightFloor) : ¬ IsTie D :=
  fun htie => hspread.1 (hhinge D htie)

/-- **The dust branch from a GLOBAL level one size down.**  Everything the branch
costs is in `hshareBudget`: the dropped atom's share must be below one and the
level must pay `1 − t_d ≤ level·(1 − s_d)`.

INERT AT RANK THREE, and shipped only because the collapse is worth recording.
`dustDropCertificate_of_floor_collapses_to_lightAtom` proves that at `rank = 3`
these hypotheses force the dropped atom's leverage below one, which is the
hypothesis of `Gtz.dominating_of_light_atom` — a theorem already.  Use
`dustDropCertificate_of_floorOnRegion` instead. -/
theorem dustDropCertificate_of_floor {rank : ℕ} {weightFloor level : ℝ}
    (hsizeTwo : 2 ≤ m + 1) (hlevelNonneg : 0 ≤ level)
    (hfloor : GtzWeightedFloor m rank level)
    (hshareBudget : ∀ D : WeightedDesign (m + 1) rank, ∀ dustLabel : Fin (m + 1),
      D.weight dustLabel < weightFloor →
        atomShare D dustLabel < 1
        ∧ 1 - D.weight dustLabel ≤ level * (1 - atomShare D dustLabel)) :
    DustDropCertificate (m + 1) rank weightFloor := by
  intro D hdust
  obtain ⟨dustLabel, hdustWeight⟩ := hdust
  obtain ⟨hshare, hbudget⟩ := hshareBudget D dustLabel hdustWeight
  exact exists_dominating_of_dust_atom D dustLabel hsizeTwo hlevelNonneg hshare hfloor hbudget

/-- **The dust branch from a level asked only where the deflation lands.**  The
same budget, but the level is demanded of the deflated designs themselves rather
than of every design one size down.  This is the form the rank-three ceiling
leaves alive, because the ceiling caps GLOBAL floors, not floors on proper
regions.  The price is visible in `hdeflatedLevel`, which quantifies over the
whitener the deflation produces. -/
theorem dustDropCertificate_of_floorOnRegion {rank : ℕ} {weightFloor level : ℝ}
    (hsizeTwo : 2 ≤ m + 1) (hlevelNonneg : 0 ≤ level)
    (hshareBudget : ∀ D : WeightedDesign (m + 1) rank, ∀ dustLabel : Fin (m + 1),
      D.weight dustLabel < weightFloor →
        atomShare D dustLabel < 1
        ∧ 1 - D.weight dustLabel ≤ level * (1 - atomShare D dustLabel))
    (hdeflatedLevel : ∀ (D : WeightedDesign (m + 1) rank) (dustLabel : Fin (m + 1)),
      D.weight dustLabel < weightFloor →
      ∀ (whitener : Matrix (Fin rank) (Fin rank) ℝ) (hgap : 0 < 1 - D.weight dustLabel)
        (hwhiten : whitenerᵀ * (1 - D.weight dustLabel • atomMatrix (D.atom dustLabel))
          * whitener = 1),
        ∃ deflatedSubset : Finset (Fin m), deflatedSubset.card = rank
          ∧ DominatesAtLevel (deflatedDesign D dustLabel whitener hgap hwhiten)
              deflatedSubset level) :
    DustDropCertificate (m + 1) rank weightFloor := by
  intro D hdust
  obtain ⟨dustLabel, hdustWeight⟩ := hdust
  obtain ⟨hshareBelowOne, hbudget⟩ := hshareBudget D dustLabel hdustWeight
  have hgap : 0 < 1 - D.weight dustLabel := by
    linarith [weight_lt_one D hsizeTwo dustLabel]
  exact exists_dominating_of_dust_atom_of_deflatedLevel D dustLabel hgap hlevelNonneg
    hshareBelowOne (fun whitener hwhiten =>
      hdeflatedLevel D dustLabel hdustWeight whitener hgap hwhiten) hbudget

/-- **The three-branch induction step.**  Branch (i) — an exactly parallel pair —
is discharged by the merge; branches (ii) and (iii) are the named hypotheses.
The trichotomy is exhaustive by construction: `IsSpreadAndFloored` is the
negation of the other two triggers. -/
theorem gtzWeighted_of_branches {rank : ℕ} {weightFloor : ℝ}
    (hrecursive : GtzWeighted m rank)
    (hdust : DustDropCertificate (m + 1) rank weightFloor)
    (hspread : SpreadFloorCertificate (m + 1) rank weightFloor) :
    GtzWeighted (m + 1) rank := by
  classical
  intro D
  by_cases hparallelPair : HasParallelPair D
  · obtain ⟨keptLabel, dropLabel, ratio, hdistinct, hparallel⟩ := hparallelPair
    exact dominating_of_parallel_pair D hrecursive hdistinct hparallel
  · by_cases hdustAtom : HasDustAtom D weightFloor
    · exact hdust D hdustAtom
    · exact hspread D ⟨hparallelPair, hdustAtom⟩

/-- **The rank-three step `5 → 6`.**  The base is unconditional
(`Gtz.gtzWeighted_corank_two` at `k = 3`), so `(6,3)` is exactly the two named
certificates at size six. -/
theorem gtzWeightedSix_of_branches {weightFloor : ℝ}
    (hdust : DustDropCertificate 6 3 weightFloor)
    (hspread : SpreadFloorCertificate 6 3 weightFloor) :
    GtzWeighted 6 3 :=
  gtzWeighted_of_branches (gtzWeighted_corank_two 3 (by norm_num)) hdust hspread

/-- **The rank-three step `6 → 7`.** -/
theorem gtzWeightedSeven_of_branches {weightFloor : ℝ} (hsix : GtzWeighted 6 3)
    (hdust : DustDropCertificate 7 3 weightFloor)
    (hspread : SpreadFloorCertificate 7 3 weightFloor) :
    GtzWeighted 7 3 :=
  gtzWeighted_of_branches hsix hdust hspread

/-- **Rank three in full from the four named certificates.**  `(7,3)` alone
implies `GtzWeightedAll 3` (`Gtz.gtzWeightedAll_three_of_seven_three`), so this
is the entire remaining obligation of the Covered+ plan at rank three, with the
merge branch already paid. -/
theorem gtzWeightedAll_three_of_branches {weightFloorSix weightFloorSeven : ℝ}
    (hdustSix : DustDropCertificate 6 3 weightFloorSix)
    (hspreadSix : SpreadFloorCertificate 6 3 weightFloorSix)
    (hdustSeven : DustDropCertificate 7 3 weightFloorSeven)
    (hspreadSeven : SpreadFloorCertificate 7 3 weightFloorSeven) :
    GtzWeightedAll 3 :=
  gtzWeightedAll_three_of_seven_three
    (gtzWeightedSeven_of_branches (gtzWeightedSix_of_branches hdustSix hspreadSix)
      hdustSeven hspreadSeven)

/-! ## The compact four-branch shell at rank three

The shell above is exhaustive because its third region is DEFINED as the
complement of the other two, and it pays for that with an open region on which no
margin exists (NO-GO 1).  This one pays differently.  It takes the region
predicates from `Gtz.Quantitative.FlooredSpreadRegion` — `Gtz.HasSpreadAtLeast`
(squared cosine at most `1 − spread`, a CLOSED polynomial inequality, no
division), `Gtz.HasWeightFloor`, and their conjunction with all-heaviness
`Gtz.IsFlooredSpreadDesign` — instead of re-inventing them, and it discharges two
branches instead of one:

* a LIGHT atom (leverage at most one) by `Gtz.dominating_of_light_atom`, which is
  where `Gtz.AllHeavy` failing sends us — margin-free;
* an EXACTLY parallel pair by the merge of this file — margin-free.

What it does not get for free is the corner between them.  `¬ HasSpreadAtLeast D
spread` says some pair is nearly parallel; the merge pays only for pairs that are
EXACTLY parallel; and the ceiling forbids buying the difference with a global
margin one size down.  That corner is `NearParallelCertificate`, named rather
than absorbed.  It is the sharpest thing this file exposes: the qualitative shell
hides it inside an open region, the compact shell shows it as a residue, and no
route in the repo currently pays it.

`Gtz.FlooredSpreadCovering` — the repo's own already-named hypothesis for the
same region at size six — implies the third residue at size six, so the two files
state ONE hypothesis between them.
-/

/-- **The near-parallel corner as an obligation.**  A design with a pair below the
angular floor but NO exactly parallel pair; the merge cannot reach it and the
ceiling forbids paying for it with a global margin. -/
def NearParallelCertificate (size : ℕ) (spread : ℝ) : Prop :=
  ∀ D : WeightedDesign size 3, ¬ HasSpreadAtLeast D spread → ¬ HasParallelPair D →
    ∃ C : Finset (Fin size), C.card = 3 ∧ Dominates D C

/-- **The compact region as an obligation**: domination on
`Gtz.IsFlooredSpreadDesign`, which is closed in the atoms and bounded in the
weights. -/
def FlooredSpreadDominationCertificate (size : ℕ) (spread weightFloor : ℝ) : Prop :=
  ∀ D : WeightedDesign size 3, IsFlooredSpreadDesign D spread weightFloor →
    ∃ C : Finset (Fin size), C.card = 3 ∧ Dominates D C

/-- Carrying dust IS failing the repo's weight floor — the two predicates are the
same statement, so the qualitative and compact shells share branch (ii). -/
theorem hasDustAtom_iff_not_hasWeightFloor (D : WeightedDesign m 3) (weightFloor : ℝ) :
    HasDustAtom D weightFloor ↔ ¬ HasWeightFloor D weightFloor := by
  simp only [HasDustAtom, HasWeightFloor, not_forall, not_le]

/-- The dichotomy of NO-GO 3, on the compact region: above `1/size` it is empty. -/
theorem not_isFlooredSpreadDesign_of_sizeInv_lt_floor (D : WeightedDesign m 3)
    (hsizePos : 0 < m) {spread weightFloor : ℝ}
    (hfloorAboveAverage : (m : ℝ)⁻¹ < weightFloor) :
    ¬ IsFlooredSpreadDesign D spread weightFloor := by
  intro hregion
  exact ((hasDustAtom_iff_not_hasWeightFloor D weightFloor).mp
    (hasDustAtom_of_sizeInv_lt_floor D hsizePos hfloorAboveAverage)) hregion.2.2

theorem flooredSpreadDominationCertificate_of_sizeInv_lt_floor {size : ℕ} (hsizePos : 0 < size)
    {spread weightFloor : ℝ} (hfloorAboveAverage : (size : ℝ)⁻¹ < weightFloor) :
    FlooredSpreadDominationCertificate size spread weightFloor :=
  fun D hregion =>
    absurd hregion (not_isFlooredSpreadDesign_of_sizeInv_lt_floor D hsizePos hfloorAboveAverage)

/-- **The compact induction step at rank three.**  Four branches, exhaustive by
construction: light atom (DISCHARGED), exactly parallel pair (DISCHARGED),
near-parallel corner, dust, compact region.  The two discharged branches consume
`hrecursive` and nothing else — no margin, anywhere. -/
theorem gtzWeightedRankThree_of_compactBranches {baseSize : ℕ} {spread weightFloor : ℝ}
    (hbaseSizePos : 1 ≤ baseSize) (hrecursive : GtzWeighted baseSize 3)
    (hnearParallel : NearParallelCertificate (baseSize + 1) spread)
    (hdust : DustDropCertificate (baseSize + 1) 3 weightFloor)
    (hregion : FlooredSpreadDominationCertificate (baseSize + 1) spread weightFloor) :
    GtzWeighted (baseSize + 1) 3 := by
  classical
  intro D
  by_cases hallHeavy : AllHeavy D
  · by_cases hspreadAtLeast : HasSpreadAtLeast D spread
    · by_cases hweightFloor : HasWeightFloor D weightFloor
      · exact hregion D ⟨hallHeavy, hspreadAtLeast, hweightFloor⟩
      · exact hdust D ((hasDustAtom_iff_not_hasWeightFloor D weightFloor).mpr hweightFloor)
    · by_cases hparallelPair : HasParallelPair D
      · obtain ⟨keptLabel, dropLabel, ratio, hdistinct, hparallel⟩ := hparallelPair
        exact dominating_of_parallel_pair D hrecursive hdistinct hparallel
      · exact hnearParallel D hspreadAtLeast hparallelPair
  · obtain ⟨lightLabel, hlightLabel⟩ := not_forall.mp hallHeavy
    exact dominating_of_light_atom D hbaseSizePos hrecursive lightLabel (not_lt.mp hlightLabel)

/-- **The repo's own region hypothesis discharges the compact branch at size six.**
`Gtz.FlooredSpreadCovering` delivers the two `S_3`-invariant legs on the same
region, and `Gtz.dominates_triple_iff_symmetricLegs` reads them back as
domination — the heaviness the bridge needs is the region's own first
conjunct. -/
theorem flooredSpreadDominationCertificate_six_of_flooredSpreadCovering
    {spread weightFloor : ℝ} (hcovering : FlooredSpreadCovering spread weightFloor) :
    FlooredSpreadDominationCertificate 6 spread weightFloor := by
  intro D hregion
  obtain ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird, hminor, htie⟩ :=
    hcovering D hregion
  refine ⟨{first, second, third}, ?_, ?_⟩
  · rw [Finset.card_insert_of_notMem (by simp [hfirstSecond, hfirstThird]),
      Finset.card_insert_of_notMem (by simp [hsecondThird]), Finset.card_singleton]
  · exact (dominates_triple_iff_symmetricLegs D hfirstSecond hfirstThird hsecondThird
      (hregion.1 first) (hregion.1 second) (hregion.1 third)).mpr ⟨hminor, htie⟩

/-- **The compact step `5 → 6`**, with the third residue supplied by the repo's
`Gtz.FlooredSpreadCovering`.  The base is unconditional. -/
theorem gtzWeightedSix_of_compactBranches {spread weightFloor : ℝ}
    (hnearParallel : NearParallelCertificate 6 spread)
    (hdust : DustDropCertificate 6 3 weightFloor)
    (hcovering : FlooredSpreadCovering spread weightFloor) :
    GtzWeighted 6 3 :=
  gtzWeightedRankThree_of_compactBranches (by norm_num)
    (gtzWeighted_corank_two 3 (by norm_num)) hnearParallel hdust
    (flooredSpreadDominationCertificate_six_of_flooredSpreadCovering hcovering)

/-- **The compact step `6 → 7`.** -/
theorem gtzWeightedSeven_of_compactBranches {spread weightFloor : ℝ} (hsix : GtzWeighted 6 3)
    (hnearParallel : NearParallelCertificate 7 spread)
    (hdust : DustDropCertificate 7 3 weightFloor)
    (hregion : FlooredSpreadDominationCertificate 7 spread weightFloor) :
    GtzWeighted 7 3 :=
  gtzWeightedRankThree_of_compactBranches (by norm_num) hsix hnearParallel hdust hregion

/-- **Rank three in full from the compact branches.**  Six residues in total, none
of them a global margin, and the size-six region residue is the repo's own
`Gtz.FlooredSpreadCovering`.  As with the qualitative assembly, this asserts
nothing about the truth of `GtzWeighted 7 3`; it says precisely what is owed. -/
theorem gtzWeightedAll_three_of_compactBranches {spreadSix weightFloorSix : ℝ}
    {spreadSeven weightFloorSeven : ℝ}
    (hnearParallelSix : NearParallelCertificate 6 spreadSix)
    (hdustSix : DustDropCertificate 6 3 weightFloorSix)
    (hcoveringSix : FlooredSpreadCovering spreadSix weightFloorSix)
    (hnearParallelSeven : NearParallelCertificate 7 spreadSeven)
    (hdustSeven : DustDropCertificate 7 3 weightFloorSeven)
    (hregionSeven : FlooredSpreadDominationCertificate 7 spreadSeven weightFloorSeven) :
    GtzWeightedAll 3 :=
  gtzWeightedAll_three_of_seven_three
    (gtzWeightedSeven_of_compactBranches
      (gtzWeightedSix_of_compactBranches hnearParallelSix hdustSix hcoveringSix)
      hnearParallelSeven hdustSeven hregionSeven)

end Gtz
