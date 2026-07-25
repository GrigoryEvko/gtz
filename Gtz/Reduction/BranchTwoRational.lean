/-
# The rational branch-(b) consumer: cap certificates by one negative pivot

Branch (a) — the excess pigeonhole — has a fully rational consumer
(`Gtz.ratCertificate_dominates_of_excess`). Branch (b) — the cap criterion —
did not: `Gtz.cap_criterion` is stated with a SIGNATURE WITNESS (a negative
direction `w` together with nonnegativity of the form on the `N`-orthogonal
complement of `w`), and nothing in the tree produced that witness from
rational data. Before this file `cap_criterion` had exactly ONE consumer in the
tree — `corner_gate_cap_iff`, bespoke geometry at the exact tetrahedral corner
— and `cap_fires_iff_det_nonneg` had none at all. The gap was not cosmetic:
branch (a)'s consumer needs NONPOSITIVE weighted outsider excess at some
positive definite `(k+1)`-base, so on a design where every such base has
strictly positive excess it does not apply at all, while branch (b) can still
fire. Designs of that kind exist — exact rational ones — but exhibiting one
belongs to a layer this file may not import, so no such existence claim is made
here; what is proved here is the consumer.

This file closes it. The producing object is a **one-negative-pivot
congruence certificate** — the exact sign-flipped twin of the LDL certificate
branch (a) already consumes:

    `Lᵀ N L = diagonal d`,  `L` invertible,  `d negIndex < 0`,
    `d i > 0` for every `i ≠ negIndex`.

From that single piece of data every hypothesis of `cap_criterion` AND of
`cap_fires_iff_det_nonneg` follows, with no eigenvalues, no interlacing, no
Sturm sequence, no square roots and no rank or dimension reasoning:

* the negative direction is a COLUMN of the certificate basis,
  `w = L e_negIndex` — no triangular solve — and `wᵀNw = d negIndex < 0`
  by the congruence read at `e_negIndex` (`negativeDirection_quadForm`);
* in the coordinates `y = L⁻¹ probe` the constraint `probeᵀNw = 0` reads
  `d negIndex · y negIndex = 0`, hence `y negIndex = 0`, and then
  `probeᵀ N probe = Σ d i · (y i)²` is TERMWISE nonnegative — the `negIndex`
  term vanishes and every other pivot is positive
  (`signatureWitness_of_oneNegativePivot`);
* `det L² · det N = Π d < 0` because exactly one factor is negative
  (`det_neg_of_oneNegativePivot`), which is the hypothesis of
  `cap_fires_iff_det_nonneg`.

Assembling: `dominates_of_capCongruence` takes a gate `G`, a fresh atom `e`,
the congruence certificate for `S_G − 1`, and ONE further scalar — the sign of
`det(S_{G∪e} − 1)` — and returns Loewner domination of `G ∪ {e}`.
`ratDominates_of_capCongruence` is its exact-rational twin: every hypothesis
is a finite ℚ-identity or ℚ-comparison, and the conclusion is real domination.

## The interface identity

Branch (a) and branch (b) are not two certificate classes. They are two
readings of ONE determinant. For a `k`-subset `C`, an outside insider
`insider ∉ C` and a member `extra ∈ C`,

    det(S_{C∪insider} − 1)·(1 − q_insider)  =  det(S_C − 1)
                                           =  det(S_{C∖extra} − 1)·(1 + p_extra),

so the pigeonhole excess numerator and the cap numerator are literally the
same number (`det_interface_identity`), and under the two branches' side
conditions the two firing tests are each equivalent to `Dominates D C`
(`branchTests_agree`). What separates the branches is therefore ONLY their
side conditions — `S_{C∪insider} − 1 ≻ 0` upstairs versus
`det(S_{C∖extra} − 1) < 0` downstairs — never the test itself.

## How far the side condition is automatic

`capWitness_of_dominates` records the completeness half that is free: on a
subset that already dominates, the cap criterion's signature witness costs
nothing. Taking `w = N⁻¹ g_extra` turns the `N`-orthogonality constraint into
plain orthogonality to `g_extra`, on which `vᵀNv = vᵀ(N + g gᵀ)v ≥ 0`; and the
determinant lemma upgrades `det N < 0` plus `det(N + g gᵀ) ≥ 0` to
`g N⁻¹ g ≤ −1 < 0`. So branch (b)'s only genuine side condition is the SIGN
OF ONE GATE DETERMINANT. Whether every dominating subset owns a gate with that
sign is NOT proven here, at any rank.

## What is open at the end of this file

`dominates_of_pairGate` reduces branch (b) at rank three to three polynomial
inequalities in the design's own numbers, so the frontier object `(7,3)`
becomes a purely rational covering problem over the `105` pairs counted by
`capCombinations_card_seven_three`. Two things are NOT settled:

* whether every dominating triple owns a pair gate satisfying the STRICT
  inequality `(l_a − 1)(l_b − 1) > ⟨g_a, g_b⟩²`. Domination forces the
  non-strict version (each `2 × 2` principal block of a dominating triple's
  Gram exceeds the identity weakly), so the possible failure is confined to a
  boundary. `exists_dominatingTriple_withoutStrictGate` shows that boundary is
  NOT empty, so the rank-three producer is genuinely incomplete there; what is
  open is whether a design can be degenerate at EVERY one of its dominating
  triples at once.
* the covering itself, which is the whole remaining content of GTZ at rank
  three and is untouched by anything in this file.

## Scope, corrected after audit and after reconciliation with the discriminant system

Read this before using anything below.

**At rank three this file is superseded.** `Gtz.dominates_triple_iff_discriminantSystem`
(`Gtz/Quantitative/DiscriminantSystem.lean`) already reduces domination of a triple to
TWO scalar polynomial inequalities — `discriminantTrace ≥ 0` and `discriminantTie ≥ 0`
— and it is an IFF, needing only that one atom of the triple is heavy, which `AllHeavy`
supplies at every atom. The mechanism is a Schur complement in the heavy pivot followed
by the repo's own `twoByTwoForm_nonneg_iff_trace_det_nonneg`; concretely
`tr(Schur) = discriminantTrace / heavyExcess` and `det(Schur) = discriminantTie /
heavyExcess`, and `discriminantTie` IS `det (Gram − I)`. Two conditions, not the five
hypotheses of `dominates_of_pairGate`, and no strictness anywhere — so the boundary
failure this file discovered does not arise there at all.

**Where this file does earn its keep: general rank.** No discriminant system exists for
`k ≥ 4`. The congruence route does: `signatureWitness_of_oneNegativePivot` produces both
halves of `cap_criterion`'s signature witness from `(L, d, negIndex)` at every rank, the
negative direction being literally a column of `L`, and the complement half being
termwise in `y = L⁻¹ probe`. `dotProduct_congruence_bilinear` is the polarized transport
that makes it work and was not in the tree before.

**Corrections carried from the audits, all kernel-checked in the companion files.**

* `dominates_of_pairGate` is Sylvester's criterion in its STRICT-LEADING-minor form,
  reached through the cap criterion. `exists_dominatingTriple_withoutStrictGate` is the
  classical failure of that form on the PSD boundary, not a fact about GTZ. The textbook
  repair — all principal minors rather than leading ones — is
  `PrincipalMinorsThree.lean`; the every-rank repair is `PsdCongruenceConsumer.lean`.
* The blind spot is CONFINED. `pairGramShift_det_neg_of_strictDominatingTriple`
  (`BranchTwoCompleteness.lean`) proves branch (b) certifies every STRICTLY dominating
  triple, so degeneracy can only occur on the tie variety.
* Three hypotheses are provably redundant — `hdistinct`, `hfresh`, `hbasisDet`. The
  hypothesis-minimal restatements are `BranchTwoMinimal.lean`.
* `det_interface_identity` relates the cap numerator to the PIVOT numerator, not to the
  weighted outsider EXCESS that `certificate_dominates_of_excess` actually fires on. It
  is one pigeonhole step away from the branch that fires.
* Nothing in this file reads `D.weight`, `D.weight_pos`, `D.weight_sum_one` or
  `D.isParseval`. Branch (b) as landed is DESIGN-BLIND: every result holds for an
  arbitrary indexed family of vectors, and all GTZ-specific content sits in `hCapDet`.
  That is fine for a consumer and fatal for anything that claims to be a covering
  argument.

-/
import Mathlib
import Gtz.Core.Basic
import Gtz.LinAlg.PsdKit
import Gtz.LinAlg.CongruenceRobustness
import Gtz.Corner.CapCriterion
import Gtz.Design.CapSlack
import Gtz.Design.TraceIdentity
import Gtz.Reduction.Deflation
import Gtz.Reduction.RatCertificate
import Gtz.Reduction.RatCertificateInstance

namespace Gtz

open Matrix

variable {m k : ℕ}

/-! ### Congruence transport -/

/-- **Congruence moves the BILINEAR form along `L`**: `⟨u, (LᵀEL)v⟩ = ⟨Lu, E(Lv)⟩`.
The polarized companion of `Gtz.dotProduct_congruence`, which only states the
diagonal case `u = v`; the certificate below needs the off-diagonal reading to
convert an `N`-orthogonality constraint into a single coordinate equation. -/
theorem dotProduct_congruence_bilinear (form basis : Matrix (Fin k) (Fin k) ℝ)
    (leftVec rightVec : Fin k → ℝ) :
    leftVec ⬝ᵥ ((basisᵀ * form * basis) *ᵥ rightVec)
      = (basis *ᵥ leftVec) ⬝ᵥ (form *ᵥ (basis *ᵥ rightVec)) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    dotProduct_comm leftVec (basisᵀ *ᵥ (form *ᵥ (basis *ᵥ rightVec))),
    dotProduct_mulVec_transpose, dotProduct_comm]

/-- The diagonal bilinear form paired against one coordinate vector. -/
theorem dotProduct_diagonal_single (diagVec probe : Fin k → ℝ) (coord : Fin k) :
    probe ⬝ᵥ (Matrix.diagonal diagVec *ᵥ Pi.single coord (1 : ℝ))
      = probe coord * diagVec coord := by
  simp [dotProduct, Matrix.mulVec_diagonal, Pi.single_apply, Finset.sum_ite_eq']

/-- The diagonal quadratic form as a sum of scaled squares. -/
theorem dotProduct_diagonal_self (diagVec probe : Fin k → ℝ) :
    probe ⬝ᵥ (Matrix.diagonal diagVec *ᵥ probe)
      = ∑ i, diagVec i * probe i ^ 2 := by
  simp only [dotProduct, Matrix.mulVec_diagonal]
  exact Finset.sum_congr rfl fun i _ => by ring

/-! ### The signature witness from one negative pivot -/

/-- The negative direction named by a one-negative-pivot congruence: the
`negIndex` COLUMN of the congruence basis. No triangular solve, no square
root — the certificate carries its own witness. -/
noncomputable def negativeDirection (basis : Matrix (Fin k) (Fin k) ℝ)
    (negIndex : Fin k) : Fin k → ℝ :=
  basis *ᵥ Pi.single negIndex (1 : ℝ)

/-- The congruence read at one coordinate: the named column's quadratic value
is exactly the corresponding pivot. -/
theorem negativeDirection_quadForm
    {form basis : Matrix (Fin k) (Fin k) ℝ} {diagVec : Fin k → ℝ}
    {negIndex : Fin k}
    (hCongr : basisᵀ * form * basis = Matrix.diagonal diagVec) :
    (negativeDirection basis negIndex)
        ⬝ᵥ (form *ᵥ (negativeDirection basis negIndex)) = diagVec negIndex := by
  have hbilinear := dotProduct_congruence_bilinear form basis
    (Pi.single negIndex (1 : ℝ)) (Pi.single negIndex (1 : ℝ))
  rw [hCongr, dotProduct_diagonal_single] at hbilinear
  rw [negativeDirection, ← hbilinear]
  simp

/-- **The signature witness, from a one-negative-pivot congruence.** A
congruence `Lᵀ N L = diagonal d` whose diagonal is negative at exactly one
index supplies the witness pair `cap_criterion` asks for: the `negIndex`
column of `L` has strictly negative quadratic value, and the form is
nonnegative on that column's `N`-orthogonal complement.

The complement half is TERMWISE, not a splitting argument: in the coordinates
`y = L⁻¹ probe` the orthogonality constraint reads `d negIndex · y negIndex = 0`,
which pins `y negIndex = 0`, and `probeᵀ N probe = Σ d i (y i)²` then has a
vanishing `negIndex` term and positive pivots everywhere else. -/
theorem signatureWitness_of_oneNegativePivot
    {form basis : Matrix (Fin k) (Fin k) ℝ} {diagVec : Fin k → ℝ}
    {negIndex : Fin k}
    (hbasisDet : IsUnit basis.det)
    (hCongr : basisᵀ * form * basis = Matrix.diagonal diagVec)
    (hNegPivot : diagVec negIndex < 0)
    (hPosPivots : ∀ i, i ≠ negIndex → 0 < diagVec i) :
    (negativeDirection basis negIndex)
        ⬝ᵥ (form *ᵥ (negativeDirection basis negIndex)) < 0
      ∧ ∀ probe : Fin k → ℝ,
          probe ⬝ᵥ (form *ᵥ (negativeDirection basis negIndex)) = 0
            → 0 ≤ probe ⬝ᵥ (form *ᵥ probe) := by
  refine ⟨by rw [negativeDirection_quadForm hCongr]; exact hNegPivot, ?_⟩
  intro probe hOrthogonal
  set coords : Fin k → ℝ := basis⁻¹ *ᵥ probe with hcoords
  have hrecover : basis *ᵥ coords = probe := by
    rw [hcoords, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv basis hbasisDet,
      Matrix.one_mulVec]
  have hpinned : coords negIndex * diagVec negIndex = 0 := by
    have hbilinear := dotProduct_congruence_bilinear form basis coords
      (Pi.single negIndex (1 : ℝ))
    rw [hCongr, dotProduct_diagonal_single, hrecover] at hbilinear
    rw [negativeDirection, ← hbilinear] at hOrthogonal
    exact hOrthogonal
  have hcoordZero : coords negIndex = 0 := by
    rcases mul_eq_zero.mp hpinned with hzero | hzero
    · exact hzero
    · exact absurd hzero hNegPivot.ne
  have hformInCoords : probe ⬝ᵥ (form *ᵥ probe)
      = ∑ i, diagVec i * coords i ^ 2 := by
    have hbilinear := dotProduct_congruence_bilinear form basis coords coords
    rw [hCongr, dotProduct_diagonal_self, hrecover] at hbilinear
    exact hbilinear.symm
  rw [hformInCoords]
  refine Finset.sum_nonneg fun i _ => ?_
  rcases eq_or_ne i negIndex with rfl | hother
  · rw [hcoordZero]; simp
  · exact mul_nonneg (hPosPivots i hother).le (sq_nonneg _)

/-- **The same certificate forces a negative determinant**, which is the
hypothesis of `cap_fires_iff_det_nonneg`. Congruence multiplies the
determinant by `det(L)² > 0`, and the diagonal's product has exactly one
negative factor. -/
theorem det_neg_of_oneNegativePivot
    {form basis : Matrix (Fin k) (Fin k) ℝ} {diagVec : Fin k → ℝ}
    {negIndex : Fin k}
    (hbasisDet : IsUnit basis.det)
    (hCongr : basisᵀ * form * basis = Matrix.diagonal diagVec)
    (hNegPivot : diagVec negIndex < 0)
    (hPosPivots : ∀ i, i ≠ negIndex → 0 < diagVec i) :
    form.det < 0 := by
  have hdet := congrArg Matrix.det hCongr
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    Matrix.det_diagonal] at hdet
  have hprodNeg : ∏ i, diagVec i < 0 := by
    rw [← Finset.mul_prod_erase Finset.univ diagVec (Finset.mem_univ negIndex)]
    exact mul_neg_of_neg_of_pos hNegPivot
      (Finset.prod_pos fun i hi => hPosPivots i (Finset.mem_erase.mp hi).1)
  have hsquare : 0 < basis.det * basis.det :=
    mul_self_pos.mpr (isUnit_iff_ne_zero.mp hbasisDet)
  nlinarith [hdet, hprodNeg, hsquare]

/-! ### The Gram shift under one atom move -/

/-- Adding a fresh atom to a subset adds its rank-one atom to the Gram shift. -/
theorem gramShift_insert (D : WeightedDesign m k) (gate : Finset (Fin m))
    (extra : Fin m) (hfresh : extra ∉ gate) :
    subsetSum D (insert extra gate) - 1
      = (subsetSum D gate - 1) + atomMatrix (D.atom extra) := by
  rw [subsetSum, subsetSum, Finset.sum_insert hfresh]
  abel

/-- Erasing a member splits the Gram shift as the erased shift plus its atom. -/
theorem gramShift_erase (D : WeightedDesign m k) (core : Finset (Fin m))
    (extra : Fin m) (hmember : extra ∈ core) :
    subsetSum D core - 1
      = (subsetSum D (core.erase extra) - 1) + atomMatrix (D.atom extra) := by
  have hsum := Finset.sum_erase_add core (fun c => atomMatrix (D.atom c)) hmember
  rw [subsetSum, subsetSum, ← hsum]
  abel

/-! ### The real branch-(b) consumer -/

/-- **The branch-(b) consumer, witness form.** A gate `G`, a fresh atom `e`, a
signature witness for the gate's Gram shift, its determinant sign, and ONE
further scalar — the sign of `det(S_{G∪e} − 1)` — produce Loewner domination
of `G ∪ {e}`. Everything below feeds this. -/
theorem dominates_of_capWitness (D : WeightedDesign m k)
    (gate : Finset (Fin m)) (extra : Fin m) (hfresh : extra ∉ gate)
    (negDirection : Fin k → ℝ)
    (hnegative : negDirection ⬝ᵥ ((subsetSum D gate - 1) *ᵥ negDirection) < 0)
    (hcomplement : ∀ probe : Fin k → ℝ,
      probe ⬝ᵥ ((subsetSum D gate - 1) *ᵥ negDirection) = 0
        → 0 ≤ probe ⬝ᵥ ((subsetSum D gate - 1) *ᵥ probe))
    (hgateDetNeg : (subsetSum D gate - 1).det < 0)
    (hCapDet : 0 ≤ (subsetSum D (insert extra gate) - 1).det) :
    Dominates D (insert extra gate) := by
  have hsplit := gramShift_insert D gate extra hfresh
  have hgateSymm : (subsetSum D gate - 1)ᵀ = subsetSum D gate - 1 := by
    rw [Matrix.transpose_sub, subsetSum_transpose, Matrix.transpose_one]
  have hgateDetUnit : IsUnit (subsetSum D gate - 1).det :=
    isUnit_iff_ne_zero.mpr (ne_of_lt hgateDetNeg)
  rw [hsplit] at hCapDet
  have hfires : (D.atom extra) ⬝ᵥ ((subsetSum D gate - 1)⁻¹ *ᵥ (D.atom extra))
      ≤ -1 := (cap_fires_iff_det_nonneg hgateDetNeg (D.atom extra)).mpr hCapDet
  have hpsd := (cap_criterion hgateSymm hgateDetUnit hnegative
    hcomplement (D.atom extra)).mpr hfires
  rw [Dominates, hsplit, atomMatrix]
  exact hpsd

/-- **The branch-(b) certificate consumer.** A gate `G`, a fresh atom `e`, a
one-negative-pivot congruence certificate for the gate's Gram shift, and ONE
further scalar — the sign of `det(S_{G∪e} − 1)` — produce Loewner domination
of `G ∪ {e}`.

Compare `certificate_dominates_of_excess`, the branch-(a) consumer: the gate
certificate has the same shape `(L, d)` there, with the single difference that
`d` is required positive at EVERY index; here exactly one index is negative.
One sign flip in the certificate data separates the two branches, exactly as
`cap_fires_iff_det_nonneg` and `erase_dominates_iff_det_nonneg` are one sign
flip apart. -/
theorem dominates_of_capCongruence (D : WeightedDesign m k)
    (gate : Finset (Fin m)) (extra : Fin m) (hfresh : extra ∉ gate)
    (basis : Matrix (Fin k) (Fin k) ℝ) (diagVec : Fin k → ℝ) (negIndex : Fin k)
    (hbasisDet : IsUnit basis.det)
    (hCongr : basisᵀ * (subsetSum D gate - 1) * basis = Matrix.diagonal diagVec)
    (hNegPivot : diagVec negIndex < 0)
    (hPosPivots : ∀ i, i ≠ negIndex → 0 < diagVec i)
    (hCapDet : 0 ≤ (subsetSum D (insert extra gate) - 1).det) :
    Dominates D (insert extra gate) := by
  obtain ⟨hnegDirection, hcomplementPsd⟩ :=
    signatureWitness_of_oneNegativePivot hbasisDet hCongr hNegPivot hPosPivots
  exact dominates_of_capWitness D gate extra hfresh
    (negativeDirection basis negIndex) hnegDirection hcomplementPsd
    (det_neg_of_oneNegativePivot hbasisDet hCongr hNegPivot hPosPivots) hCapDet

/-! ### The rational branch-(b) consumer -/

/-- **The fully rational branch-(b) certificate.** Every hypothesis is a
finite ℚ-identity or ℚ-comparison on the certificate data — checkable by exact
rational arithmetic on concrete instances — and the conclusion is real Loewner
domination. This is the branch-(b) twin of
`ratCertificate_dominates_of_excess`, and it is what a rational `(7,3)`
certificate consumes.

Note what is NOT among the hypotheses: no matrix inverse, no pivot, no
positive-semidefiniteness predicate and no quantifier over test vectors. The
firing test is the sign of ONE rational determinant. -/
theorem ratDominates_of_capCongruence (R : RatDesign m k)
    (gate : Finset (Fin m)) (extra : Fin m) (hfresh : extra ∉ gate)
    (basisRat : Matrix (Fin k) (Fin k) ℚ) (diagRat : Fin k → ℚ)
    (negIndex : Fin k)
    (hbasisDet : basisRat.det ≠ 0)
    (hCongr : basisRatᵀ * ratGram R gate * basisRat = Matrix.diagonal diagRat)
    (hNegPivot : diagRat negIndex < 0)
    (hPosPivots : ∀ i, i ≠ negIndex → 0 < diagRat i)
    (hCapDet : 0 ≤ (ratGram R (insert extra gate)).det) :
    Dominates R.toReal (insert extra gate) := by
  refine dominates_of_capCongruence R.toReal gate extra hfresh
    (basisRat.map (fun q : ℚ => (q : ℝ))) (fun i => (diagRat i : ℝ)) negIndex
    ?_ ?_ ?_ ?_ ?_
  · rw [det_cast]
    exact isUnit_iff_ne_zero.mpr (by exact_mod_cast hbasisDet)
  · rw [R.gram_cast gate, ← Matrix.transpose_map, ← map_mul_cast, ← map_mul_cast,
      hCongr]
    ext i j
    rcases eq_or_ne i j with rfl | hoffDiagonal
    · simp [Matrix.map_apply]
    · simp [Matrix.map_apply, hoffDiagonal]
  · exact_mod_cast hNegPivot
  · intro i hother
    exact_mod_cast hPosPivots i hother
  · rw [R.gram_cast (insert extra gate), det_cast]
    exact_mod_cast hCapDet

/-- The rational branch-(b) certificate in the shape the frontier statement
`GtzWeighted m k` consumes: a gate of `k − 1` atoms and one fresh extra
produce a dominating `k`-subset. -/
theorem ratCapCertificate_exists_dominating (R : RatDesign m k)
    (gate : Finset (Fin m)) (extra : Fin m) (hfresh : extra ∉ gate)
    (hgateCard : gate.card + 1 = k)
    (basisRat : Matrix (Fin k) (Fin k) ℚ) (diagRat : Fin k → ℚ)
    (negIndex : Fin k)
    (hbasisDet : basisRat.det ≠ 0)
    (hCongr : basisRatᵀ * ratGram R gate * basisRat = Matrix.diagonal diagRat)
    (hNegPivot : diagRat negIndex < 0)
    (hPosPivots : ∀ i, i ≠ negIndex → 0 < diagRat i)
    (hCapDet : 0 ≤ (ratGram R (insert extra gate)).det) :
    ∃ C : Finset (Fin m), C.card = k ∧ Dominates R.toReal C :=
  ⟨insert extra gate, by rw [Finset.card_insert_of_notMem hfresh, hgateCard],
    ratDominates_of_capCongruence R gate extra hfresh basisRat diagRat negIndex
      hbasisDet hCongr hNegPivot hPosPivots hCapDet⟩

/-! ### The interface identity: both branches read one determinant -/

/-- **The interface identity.** For a `k`-subset `C`, an insider `insider ∉ C`
completing it upwards and a member `extra ∈ C` opening it downwards, branch
(a)'s excess numerator and branch (b)'s cap numerator are the SAME NUMBER —
namely `det(S_C − 1)`, computed once from above by a rank-one downdate and once
from below by a rank-one update.

This is the algebraic reason the two branches were observed to fire together:
they are not two certificate classes but two readings of one determinant. -/
theorem det_interface_identity (D : WeightedDesign m k)
    (core : Finset (Fin m)) (insider extra : Fin m)
    (hinsiderFresh : insider ∉ core) (hextraMember : extra ∈ core)
    (hUpperDet : IsUnit (subsetSum D (insert insider core) - 1).det)
    (hLowerDet : IsUnit (subsetSum D (core.erase extra) - 1).det) :
    (subsetSum D (insert insider core) - 1).det
        * (1 - pivot D (insert insider core) insider)
      = (subsetSum D (core.erase extra) - 1).det
        * (1 + D.atom extra
              ⬝ᵥ ((subsetSum D (core.erase extra) - 1)⁻¹ *ᵥ D.atom extra)) := by
  have hupper : subsetSum D core - 1
      = (subsetSum D (insert insider core) - 1) - atomMatrix (D.atom insider) := by
    rw [gramShift_insert D core insider hinsiderFresh]; abel
  have hlower := gramShift_erase D core extra hextraMember
  have hviaUpper : (subsetSum D core - 1).det
      = (subsetSum D (insert insider core) - 1).det
        * (1 - D.atom insider
              ⬝ᵥ ((subsetSum D (insert insider core) - 1)⁻¹ *ᵥ D.atom insider)) := by
    rw [hupper, det_sub_atomMatrix hUpperDet]
  have hviaLower : (subsetSum D core - 1).det
      = (subsetSum D (core.erase extra) - 1).det
        * (1 + D.atom extra
              ⬝ᵥ ((subsetSum D (core.erase extra) - 1)⁻¹ *ᵥ D.atom extra)) := by
    rw [hlower, det_add_atomMatrix hLowerDet]
  rw [pivot_eq_dot, ← hviaUpper, hviaLower]

/-- **Both branch tests read the same domination fact.** Under branch (a)'s
side condition upstairs and branch (b)'s side condition downstairs, the
pigeonhole depth test at `(C ∪ insider, insider)` and the cap test at
`(C ∖ extra, extra)` are each equivalent to `Dominates D C`, hence to each
other.

The consequence for coverage statements is exact and should be stated
plainly: an observation that "branch (a) or branch (b) fires" on a family of
designs carries no information beyond "some `k`-subset dominates" on that
family, because each branch's firing IS domination of its target. Coverage
becomes evidence only when the side conditions, not the tests, are what is
being measured. -/
theorem branchTests_agree (D : WeightedDesign m k)
    (core : Finset (Fin m)) (insider extra : Fin m)
    (hinsiderFresh : insider ∉ core) (hextraMember : extra ∈ core)
    (hUpperPosDef : (subsetSum D (insert insider core) - 1).PosDef)
    (hLowerDetNeg : (subsetSum D (core.erase extra) - 1).det < 0) :
    (pivot D (insert insider core) insider ≤ 1 ↔ Dominates D core)
      ∧ (D.atom extra ⬝ᵥ ((subsetSum D (core.erase extra) - 1)⁻¹ *ᵥ D.atom extra)
            ≤ -1 ↔ Dominates D core) := by
  have herased : (insert insider core).erase insider = core :=
    Finset.erase_insert hinsiderFresh
  have hmember : insider ∈ insert insider core := Finset.mem_insert_self insider core
  have hpivotReading := erase_dominates_iff_pivot_le_one D (insert insider core)
    hUpperPosDef hmember
  have hdetReading := erase_dominates_iff_det_nonneg D (insert insider core)
    hUpperPosDef hmember
  rw [herased] at hpivotReading hdetReading
  refine ⟨hpivotReading.symm, ?_⟩
  rw [cap_fires_iff_det_nonneg hLowerDetNeg (D.atom extra),
    ← gramShift_erase D core extra hextraMember]
  exact hdetReading.symm

/-! ### How much of branch (b)'s side condition is automatic -/

/-- **The signature witness is free on a dominating subset.** If `core`
already dominates and the gate `core ∖ {extra}` has negative determinant, the
cap criterion's witness pair costs nothing: take `w = N⁻¹ g_extra`, so that
`N`-orthogonality to `w` is plain orthogonality to `g_extra`, on which
`vᵀNv = vᵀ(N + g gᵀ)v ≥ 0`; and the determinant lemma turns `det N < 0`
together with `det(N + g gᵀ) ≥ 0` into `g N⁻¹ g ≤ −1 < 0`.

So branch (b) asks a dominating subset for exactly one thing that is not
automatic: a member whose complementary gate has NEGATIVE determinant. That is
a single rational scalar per member, and it is the whole side condition. -/
theorem capWitness_of_dominates (D : WeightedDesign m k)
    (core : Finset (Fin m)) (extra : Fin m) (hextraMember : extra ∈ core)
    (hdominates : Dominates D core)
    (hGateDetNeg : (subsetSum D (core.erase extra) - 1).det < 0) :
    ((subsetSum D (core.erase extra) - 1)⁻¹ *ᵥ D.atom extra)
        ⬝ᵥ ((subsetSum D (core.erase extra) - 1)
            *ᵥ ((subsetSum D (core.erase extra) - 1)⁻¹ *ᵥ D.atom extra)) < 0
      ∧ ∀ probe : Fin k → ℝ,
          probe ⬝ᵥ ((subsetSum D (core.erase extra) - 1)
              *ᵥ ((subsetSum D (core.erase extra) - 1)⁻¹ *ᵥ D.atom extra)) = 0
            → 0 ≤ probe ⬝ᵥ ((subsetSum D (core.erase extra) - 1) *ᵥ probe) := by
  have hsplit := gramShift_erase D core extra hextraMember
  have hgateDetUnit : IsUnit (subsetSum D (core.erase extra) - 1).det :=
    isUnit_iff_ne_zero.mpr (ne_of_lt hGateDetNeg)
  have hresolve : (subsetSum D (core.erase extra) - 1)
      *ᵥ ((subsetSum D (core.erase extra) - 1)⁻¹ *ᵥ D.atom extra)
      = D.atom extra := by
    rw [Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ hgateDetUnit, Matrix.one_mulVec]
  -- the cap value is at most −1, by the determinant lemma at a negative base
  have hcapDetNonneg : 0 ≤ ((subsetSum D (core.erase extra) - 1)
      + atomMatrix (D.atom extra)).det := by
    rw [← hsplit]
    exact hdominates.det_nonneg
  have hcapLe : D.atom extra
      ⬝ᵥ ((subsetSum D (core.erase extra) - 1)⁻¹ *ᵥ D.atom extra) ≤ -1 :=
    (cap_fires_iff_det_nonneg hGateDetNeg (D.atom extra)).mpr hcapDetNonneg
  refine ⟨?_, ?_⟩
  · rw [hresolve, dotProduct_comm]
    linarith [hcapLe]
  · intro probe hOrthogonal
    rw [hresolve] at hOrthogonal
    have hformSplit : probe ⬝ᵥ ((subsetSum D core - 1) *ᵥ probe)
        = probe ⬝ᵥ ((subsetSum D (core.erase extra) - 1) *ᵥ probe)
          + (D.atom extra ⬝ᵥ probe) ^ 2 := by
      rw [hsplit, Matrix.add_mulVec, dotProduct_add, atomMatrix,
        vecMulVec_mulVec_eq, dotProduct_smul, smul_eq_mul,
        dotProduct_comm probe (D.atom extra)]
      ring
    have hdominatesForm := (Matrix.posSemidef_iff_dotProduct_mulVec.mp
      hdominates).2 probe
    rw [star_trivial, hformSplit] at hdominatesForm
    rw [dotProduct_comm] at hOrthogonal
    rw [hOrthogonal] at hdominatesForm
    simpa using hdominatesForm

/-! ### The branch-(b) combination count at the frontier -/

/-- The branch-(b) index set at rank `k`: a gate of `k − 1` atoms together
with a fresh extra atom. This is the finite set a covering argument for
`GtzWeighted m k` would case-split over. -/
def capCombinations (m k : ℕ) : Finset (Finset (Fin m) × Fin m) :=
  ((Finset.univ.powersetCard (k - 1)) ×ˢ Finset.univ).filter
    fun pair => pair.2 ∉ pair.1

/-- **The frontier object `(7, 3)` offers 105 branch-(b) combinations.** -/
theorem capCombinations_card_seven_three : (capCombinations 7 3).card = 105 := by
  decide

/-- The retired object `(6, 3)` — which now follows from `(7, 3)` by atom
splitting, `gtzWeighted_six_three_of_seven_three` — offered 60. -/
theorem capCombinations_card_six_three : (capCombinations 6 3).card = 60 := by
  decide

/-! ### Rank three: the gate certificate produced from two scalars

At rank `3` a gate has `k − 1 = 2` atoms, and the congruence certificate does
not have to be supplied at all: it is produced from the pair's own leverages
and inner product. The gate's Gram shift `S_G − 1 = g_a g_aᵀ + g_b g_bᵀ − I`
has an explicit negative direction, the normal `g_a × g_b`; and the plane it
kills is spanned by the pair, by the Cramer expansion in the frame
`(g_a, g_b, g_a × g_b)` — a polynomial identity in nine real variables, no
basis theory. So the whole branch-(b) hypothesis at rank three is TWO SCALAR
POLYNOMIAL INEQUALITIES on the pair, plus one determinant sign on the target:

    `(l_a − 1) + (l_b − 1) > 0`,   `(l_a − 1)(l_b − 1) − ⟨g_a, g_b⟩² > 0`,
    `det(S_{G∪e} − 1) ≥ 0`.

This is the shape a covering argument over the frontier object's
`capCombinations 7 3` pairs would consume: no matrices supplied anywhere. -/

/-- The normal to the plane spanned by a pair of rank-three atoms. -/
def gateNormal (first second : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![first 1 * second 2 - first 2 * second 1,
    first 2 * second 0 - first 0 * second 2,
    first 0 * second 1 - first 1 * second 0]

/-- The Gram shift of a two-atom gate at rank three. -/
def pairGramShift (first second : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  atomMatrix first + atomMatrix second - 1

/-- Lagrange: the normal's square length is the pair's Gram determinant. -/
theorem gateNormal_selfDot (first second : Fin 3 → ℝ) :
    gateNormal first second ⬝ᵥ gateNormal first second
      = (first ⬝ᵥ first) * (second ⬝ᵥ second) - (first ⬝ᵥ second) ^ 2 := by
  simp [dotProduct, Fin.sum_univ_three, gateNormal]; ring

/-- **The Cramer expansion in the frame `(first, second, normal)`.** The step
that replaces every dimension or basis argument: scaled by the normal's square
length, an arbitrary probe decomposes explicitly along the pair and the normal,
as a polynomial identity in nine real variables. -/
theorem cramer_expansion (first second probe : Fin 3 → ℝ) :
    (gateNormal first second ⬝ᵥ gateNormal first second) • probe
      = ((probe ⬝ᵥ first) * (second ⬝ᵥ second)
          - (probe ⬝ᵥ second) * (first ⬝ᵥ second)) • first
        + ((probe ⬝ᵥ second) * (first ⬝ᵥ first)
            - (probe ⬝ᵥ first) * (first ⬝ᵥ second)) • second
        + (probe ⬝ᵥ gateNormal first second) • gateNormal first second := by
  funext coord
  fin_cases coord <;> simp [dotProduct, Fin.sum_univ_three, gateNormal] <;> ring

/-- The gate's Gram shift negates its normal. -/
theorem pairGramShift_mulVec_gateNormal (first second : Fin 3 → ℝ) :
    pairGramShift first second *ᵥ gateNormal first second
      = -gateNormal first second := by
  funext coord
  fin_cases coord <;>
    simp [pairGramShift, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      atomMatrix, Matrix.vecMulVec_apply, Matrix.one_apply, gateNormal] <;> ring

/-- **The gate determinant is the pair's shifted Gram determinant, negated.**
So `det(S_G − 1) < 0` is the SCALAR condition
`(l_a − 1)(l_b − 1) > ⟨g_a, g_b⟩²`. -/
theorem pairGramShift_det (first second : Fin 3 → ℝ) :
    (pairGramShift first second).det
      = -(((first ⬝ᵥ first) - 1) * ((second ⬝ᵥ second) - 1)
            - (first ⬝ᵥ second) ^ 2) := by
  simp [pairGramShift, Matrix.det_fin_three, atomMatrix, Matrix.vecMulVec_apply,
    dotProduct, Fin.sum_univ_three]
  ring

theorem pairGramShift_firstForm (first second : Fin 3 → ℝ) :
    first ⬝ᵥ (pairGramShift first second *ᵥ first)
      = (first ⬝ᵥ first) * ((first ⬝ᵥ first) - 1) + (first ⬝ᵥ second) ^ 2 := by
  simp [pairGramShift, Matrix.mulVec, dotProduct, Fin.sum_univ_three, atomMatrix,
    Matrix.vecMulVec_apply, Matrix.one_apply]
  ring

theorem pairGramShift_secondForm (first second : Fin 3 → ℝ) :
    second ⬝ᵥ (pairGramShift first second *ᵥ second)
      = (second ⬝ᵥ second) * ((second ⬝ᵥ second) - 1)
        + (first ⬝ᵥ second) ^ 2 := by
  simp [pairGramShift, Matrix.mulVec, dotProduct, Fin.sum_univ_three, atomMatrix,
    Matrix.vecMulVec_apply, Matrix.one_apply]
  ring

theorem pairGramShift_crossForm (first second : Fin 3 → ℝ) :
    first ⬝ᵥ (pairGramShift first second *ᵥ second)
      = (first ⬝ᵥ second) * ((first ⬝ᵥ first) + (second ⬝ᵥ second) - 1) := by
  simp [pairGramShift, Matrix.mulVec, dotProduct, Fin.sum_univ_three, atomMatrix,
    Matrix.vecMulVec_apply, Matrix.one_apply]
  ring

theorem pairGramShift_crossFormFlipped (first second : Fin 3 → ℝ) :
    second ⬝ᵥ (pairGramShift first second *ᵥ first)
      = (first ⬝ᵥ second) * ((first ⬝ᵥ first) + (second ⬝ᵥ second) - 1) := by
  simp [pairGramShift, Matrix.mulVec, dotProduct, Fin.sum_univ_three, atomMatrix,
    Matrix.vecMulVec_apply, Matrix.one_apply]
  ring

set_option maxHeartbeats 1000000 in
/-- **The rank-three signature witness, produced from two scalars.** The two
hypotheses say exactly that the pair's Gram exceeds the identity strictly; from
them the normal is a strictly negative direction and the form is nonnegative on
its `N`-orthogonal complement, which the Cramer expansion identifies with the
pair's own plane, where the form is the positive definite `2 × 2` block
`Gram·(Gram − I)` handled by its own sum-of-squares certificate. -/
theorem pairGate_signatureWitness (first second : Fin 3 → ℝ)
    (htrace : 0 < ((first ⬝ᵥ first) - 1) + ((second ⬝ᵥ second) - 1))
    (hgateDet : 0 < ((first ⬝ᵥ first) - 1) * ((second ⬝ᵥ second) - 1)
                     - (first ⬝ᵥ second) ^ 2) :
    (gateNormal first second)
        ⬝ᵥ (pairGramShift first second *ᵥ gateNormal first second) < 0
      ∧ ∀ probe : Fin 3 → ℝ,
          probe ⬝ᵥ (pairGramShift first second *ᵥ gateNormal first second) = 0
            → 0 ≤ probe ⬝ᵥ (pairGramShift first second *ᵥ probe) := by
  have hproductPos : 0 < ((first ⬝ᵥ first) - 1) * ((second ⬝ᵥ second) - 1) := by
    nlinarith [sq_nonneg (first ⬝ᵥ second)]
  have hfirstHeavy : 1 < first ⬝ᵥ first := by
    by_contra hle
    push Not at hle
    have hsecondPos : 0 < (second ⬝ᵥ second) - 1 := by linarith
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 - (first ⬝ᵥ first))
      hsecondPos.le]
  have hsecondHeavy : 1 < second ⬝ᵥ second := by
    by_contra hle
    push Not at hle
    have hfirstPos : 0 < (first ⬝ᵥ first) - 1 := by linarith
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 - (second ⬝ᵥ second))
      hfirstPos.le]
  have hnormSq : 0 < gateNormal first second ⬝ᵥ gateNormal first second := by
    rw [gateNormal_selfDot]; nlinarith
  refine ⟨?_, ?_⟩
  · rw [pairGramShift_mulVec_gateNormal, dotProduct_neg]
    linarith
  intro probe hOrthogonal
  rw [pairGramShift_mulVec_gateNormal, dotProduct_neg, neg_eq_zero] at hOrthogonal
  have hcramer := cramer_expansion first second probe
  rw [hOrthogonal, zero_smul, add_zero] at hcramer
  set normSq := gateNormal first second ⬝ᵥ gateNormal first second with hnormSqDef
  set alphaCoeff := (probe ⬝ᵥ first) * (second ⬝ᵥ second)
      - (probe ⬝ᵥ second) * (first ⬝ᵥ second) with halpha
  set betaCoeff := (probe ⬝ᵥ second) * (first ⬝ᵥ first)
      - (probe ⬝ᵥ first) * (first ⬝ᵥ second) with hbeta
  have hscaled : normSq ^ 2 * (probe ⬝ᵥ (pairGramShift first second *ᵥ probe))
      = (normSq • probe) ⬝ᵥ (pairGramShift first second *ᵥ (normSq • probe)) := by
    rw [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul,
      smul_eq_mul]
    ring
  rw [hcramer] at hscaled
  have hexpand : (alphaCoeff • first + betaCoeff • second)
        ⬝ᵥ (pairGramShift first second
              *ᵥ (alphaCoeff • first + betaCoeff • second))
      = alphaCoeff ^ 2 * (first ⬝ᵥ (pairGramShift first second *ᵥ first))
        + alphaCoeff * betaCoeff
            * (first ⬝ᵥ (pairGramShift first second *ᵥ second))
        + betaCoeff * alphaCoeff
            * (second ⬝ᵥ (pairGramShift first second *ᵥ first))
        + betaCoeff ^ 2
            * (second ⬝ᵥ (pairGramShift first second *ᵥ second)) := by
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct,
      dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    ring
  rw [hexpand, pairGramShift_firstForm, pairGramShift_secondForm,
    pairGramShift_crossForm, pairGramShift_crossFormFlipped] at hscaled
  set diagFirst := (first ⬝ᵥ first) * ((first ⬝ᵥ first) - 1)
      + (first ⬝ᵥ second) ^ 2 with hdiagFirst
  set offDiag := (first ⬝ᵥ second) * ((first ⬝ᵥ first) + (second ⬝ᵥ second) - 1)
      with hoffDiag
  set diagSecond := (second ⬝ᵥ second) * ((second ⬝ᵥ second) - 1)
      + (first ⬝ᵥ second) ^ 2 with hdiagSecond
  have hdiagFirstPos : 0 < diagFirst := by
    rw [hdiagFirst]; nlinarith [sq_nonneg (first ⬝ᵥ second)]
  have hminorPos : 0 < diagFirst * diagSecond - offDiag ^ 2 := by
    have hidentity : diagFirst * diagSecond - offDiag ^ 2
        = ((first ⬝ᵥ first) * (second ⬝ᵥ second) - (first ⬝ᵥ second) ^ 2)
          * (((first ⬝ᵥ first) - 1) * ((second ⬝ᵥ second) - 1)
              - (first ⬝ᵥ second) ^ 2) := by
      rw [hdiagFirst, hoffDiag, hdiagSecond]; ring
    rw [hidentity]
    have hnormSqExpand : 0 < (first ⬝ᵥ first) * (second ⬝ᵥ second)
        - (first ⬝ᵥ second) ^ 2 := by rw [← gateNormal_selfDot]; exact hnormSq
    exact mul_pos hnormSqExpand hgateDet
  have hformNonneg : 0 ≤ diagFirst * alphaCoeff ^ 2
      + 2 * offDiag * alphaCoeff * betaCoeff + diagSecond * betaCoeff ^ 2 := by
    nlinarith [sq_nonneg (diagFirst * alphaCoeff + offDiag * betaCoeff),
      sq_nonneg betaCoeff, hdiagFirstPos, hminorPos,
      mul_nonneg hminorPos.le (sq_nonneg betaCoeff)]
  nlinarith [hscaled, hformNonneg, hnormSq, sq_nonneg normSq,
    mul_pos hnormSq hnormSq]

/-- **Branch (b) at rank three, with no matrix data supplied.** A pair of
atoms whose shifted leverages have positive sum and positive determinant
against their inner product, and a fresh atom whose enlarged Gram shift has
nonnegative determinant, dominate.

Every hypothesis is a polynomial inequality in the design's own numbers. Over
a `RatDesign` all three are exact rational comparisons: this is the branch-(b)
certificate in the form the `capCombinations 7 3` covering problem needs. -/
theorem dominates_of_pairGate (D : WeightedDesign m 3)
    (firstGate secondGate extra : Fin m) (hdistinct : firstGate ≠ secondGate)
    (hfresh : extra ∉ ({firstGate, secondGate} : Finset (Fin m)))
    (htrace : 0 < (leverageOf (D.atom firstGate) - 1)
                    + (leverageOf (D.atom secondGate) - 1))
    (hgateDet : 0 < (leverageOf (D.atom firstGate) - 1)
                      * (leverageOf (D.atom secondGate) - 1)
                    - (D.atom firstGate ⬝ᵥ D.atom secondGate) ^ 2)
    (hCapDet : 0 ≤ (subsetSum D (insert extra {firstGate, secondGate}) - 1).det) :
    Dominates D (insert extra {firstGate, secondGate}) := by
  have hlevFirst : leverageOf (D.atom firstGate)
      = D.atom firstGate ⬝ᵥ D.atom firstGate :=
    (dotProduct_self_eq_sum_sq _).symm
  have hlevSecond : leverageOf (D.atom secondGate)
      = D.atom secondGate ⬝ᵥ D.atom secondGate :=
    (dotProduct_self_eq_sum_sq _).symm
  rw [hlevFirst, hlevSecond] at htrace hgateDet
  have hgateShift : subsetSum D {firstGate, secondGate} - 1
      = pairGramShift (D.atom firstGate) (D.atom secondGate) := by
    rw [subsetSum, Finset.sum_pair hdistinct, pairGramShift]
  obtain ⟨hnegative, hcomplement⟩ :=
    pairGate_signatureWitness (D.atom firstGate) (D.atom secondGate) htrace
      hgateDet
  refine dominates_of_capWitness D {firstGate, secondGate} extra hfresh
    (gateNormal (D.atom firstGate) (D.atom secondGate)) ?_ ?_ ?_ hCapDet
  · rw [hgateShift]; exact hnegative
  · rw [hgateShift]; exact hcomplement
  · rw [hgateShift, pairGramShift_det]; linarith

/-- Inner products of rational atoms cast entrywise. -/
theorem RatDesign.dot_cast (R : RatDesign m k) (firstIndex secondIndex : Fin m) :
    R.toReal.atom firstIndex ⬝ᵥ R.toReal.atom secondIndex
      = ((R.atom firstIndex ⬝ᵥ R.atom secondIndex : ℚ) : ℝ) := by
  simp only [dotProduct]
  push_cast
  rfl

/-- **Branch (b) at rank three, fully rational and matrix-free.** For a
`RatDesign` of rank `3`, a gate pair and a fresh extra dominate as soon as
three exact rational comparisons hold: positive shifted-leverage sum, positive
shifted-leverage determinant against the pair's inner product, and nonnegative
determinant of the enlarged rational Gram shift.

This is the consumer the frontier object `(7, 3)` needs. Its hypotheses range
over `capCombinations 7 3`, the 105 gate-plus-extra pairs, and contain no
matrix data, no inverse, no positive-semidefiniteness predicate and no
quantifier over test vectors — only polynomial inequalities in the design's own
rational numbers. -/
theorem ratDominates_of_pairGate (R : RatDesign m 3)
    (firstGate secondGate extra : Fin m) (hdistinct : firstGate ≠ secondGate)
    (hfresh : extra ∉ ({firstGate, secondGate} : Finset (Fin m)))
    (htrace : 0 < ((∑ i, R.atom firstGate i ^ 2) - 1)
                    + ((∑ i, R.atom secondGate i ^ 2) - 1))
    (hgateDet : 0 < ((∑ i, R.atom firstGate i ^ 2) - 1)
                      * ((∑ i, R.atom secondGate i ^ 2) - 1)
                    - (R.atom firstGate ⬝ᵥ R.atom secondGate) ^ 2)
    (hCapDet : 0 ≤ (ratGram R (insert extra {firstGate, secondGate})).det) :
    Dominates R.toReal (insert extra {firstGate, secondGate}) := by
  refine dominates_of_pairGate R.toReal firstGate secondGate extra hdistinct
    hfresh ?_ ?_ ?_
  · rw [R.leverage_cast firstGate, R.leverage_cast secondGate]
    exact_mod_cast htrace
  · rw [R.leverage_cast firstGate, R.leverage_cast secondGate,
      R.dot_cast firstGate secondGate]
    exact_mod_cast hgateDet
  · rw [R.gram_cast (insert extra {firstGate, secondGate}), det_cast]
    exact_mod_cast hCapDet

/-- **The rank-three gate condition is NOT automatic on a dominating triple.**
The three vectors `(1,1,0)`, `(1,0,1)`, `(0,1,1)` have Gram shift equal to the
rank-one atom of `(1,1,1)`, so they dominate; and every one of their three pair
gates has shifted-leverage determinant EXACTLY `0`, so `pairGramShift_det`
makes every gate determinant vanish and both `dominates_of_pairGate` and
`cap_fires_iff_det_nonneg` are silent at that triple.

Domination of a `k`-subset does force each pair's shifted Gram determinant to
be nonnegative, so the failure is confined to the boundary where it vanishes —
this witness says the boundary is NOT empty. It also sits inside an honest
all-heavy weighted `(9,3)` design (weights `1/5, 1/5, 1/5, 1/20, 1/20, 1/20,
1/12, 1/12, 1/12` on these three vectors, on `2·(1,-1,0)`, `2·(1,0,-1)`,
`2·(0,1,-1)`, and on `sqrt(12/5)` times the three axes; leverages `2, 8, 12/5`),
which is covered elsewhere — its triple `{0,3,4}` has strict gates. That
completion is verified symbolically only and is NOT part of this theorem. -/
theorem exists_dominatingTriple_withoutStrictGate :
    ∃ firstAtom secondAtom thirdAtom : Fin 3 → ℝ,
      (atomMatrix firstAtom + atomMatrix secondAtom + atomMatrix thirdAtom
          - 1).PosSemidef
        ∧ ((firstAtom ⬝ᵥ firstAtom) - 1) * ((secondAtom ⬝ᵥ secondAtom) - 1)
            - (firstAtom ⬝ᵥ secondAtom) ^ 2 = 0
        ∧ ((firstAtom ⬝ᵥ firstAtom) - 1) * ((thirdAtom ⬝ᵥ thirdAtom) - 1)
            - (firstAtom ⬝ᵥ thirdAtom) ^ 2 = 0
        ∧ ((secondAtom ⬝ᵥ secondAtom) - 1) * ((thirdAtom ⬝ᵥ thirdAtom) - 1)
            - (secondAtom ⬝ᵥ thirdAtom) ^ 2 = 0 := by
  refine ⟨![1, 1, 0], ![1, 0, 1], ![0, 1, 1], ?_, ?_, ?_, ?_⟩
  · have hrankOne : (atomMatrix ![1, 1, 0] + atomMatrix ![1, 0, 1]
        + atomMatrix ![0, 1, 1] - 1 : Matrix (Fin 3) (Fin 3) ℝ)
        = atomMatrix ![1, 1, 1] := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [atomMatrix, Matrix.vecMulVec_apply]
    rw [hrankOne]
    exact posSemidef_atomMatrix _
  all_goals simp [dotProduct, Fin.sum_univ_three]

/-! ### The certificate exercised: branch (b) at the tie locus -/

/-- The gate: two of the four distinct tetrahedron directions. -/
def splitTetraCapGate : Finset (Fin 6) := {0, 1}

/-- **The gate's Gram shift, exactly.** -/
theorem splitTetraCap_gateGram :
    ratGram splitTetraRatDesign splitTetraCapGate
      = !![1, 0, 0; 0, 1, 2; 0, 2, 1] := by
  ext i j
  rw [ratGram, Matrix.of_apply, splitTetraCapGate,
    show ({0, 1} : Finset (Fin 6)) = insert 0 {1} from rfl,
    Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [splitTetraRatDesign, splitTetraRatAtom, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  fin_cases i <;> fin_cases j <;> norm_num

/-- **The one-negative-pivot congruence certificate for the gate**: a unit
determinant basis and the diagonal `(1, 1, −3)`, negative at index `2`. -/
theorem splitTetraCap_congruence :
    (!![1, 0, 0; 0, 1, -2; 0, 0, 1] : Matrix (Fin 3) (Fin 3) ℚ)ᵀ
        * ratGram splitTetraRatDesign splitTetraCapGate
        * !![1, 0, 0; 0, 1, -2; 0, 0, 1]
      = Matrix.diagonal ![1, 1, -3] := by
  rw [splitTetraCap_gateGram]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three]
  norm_num

/-- **The cap determinant is EXACTLY zero** — the certificate fires at the
boundary of its own test, on the tie locus. -/
theorem splitTetraCap_capDet :
    (ratGram splitTetraRatDesign (insert 2 splitTetraCapGate)).det = 0 := by
  have hgram : ratGram splitTetraRatDesign (insert 2 splitTetraCapGate)
      = !![2, -1, 1; -1, 2, 1; 1, 1, 2] := by
    ext i j
    rw [ratGram, Matrix.of_apply, splitTetraCapGate,
      show insert 2 ({0, 1} : Finset (Fin 6)) = insert 2 (insert 0 {1}) from rfl,
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
    simp only [splitTetraRatDesign, splitTetraRatAtom, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons]
    fin_cases i <;> fin_cases j <;> norm_num
  rw [hgram, Matrix.det_fin_three]
  norm_num [Matrix.cons_val_two, Matrix.tail_cons]

/-- **Branch (b), end to end, on the tie locus.** The split-tetrahedron design
is an exact tie (`Gtz.splitTetraDesign_isTie`): it dominates weakly and no
`3`-subset dominates strictly. Branch (a) reaches it with outsider excess
exactly `0` (`splitTetraRatDesign_certified_dominates`); branch (b) reaches it
here with cap determinant exactly `0`. Both branches are non-strict, and both
are met with equality — which is what `branchTests_agree` predicts, since the
two tests read the same determinant. -/
theorem splitTetraRatDesign_capCertified_dominates :
    ∃ C : Finset (Fin 6), C.card = 3 ∧ Dominates splitTetraRatDesign.toReal C :=
  ratCapCertificate_exists_dominating splitTetraRatDesign splitTetraCapGate 2
    (by decide) (by decide) !![1, 0, 0; 0, 1, -2; 0, 0, 1] ![1, 1, -3] 2
    (by norm_num [Matrix.det_fin_three, Matrix.cons_val_two, Matrix.tail_cons])
    splitTetraCap_congruence
    (by norm_num [Matrix.cons_val_two, Matrix.tail_cons])
    (by
      intro i hother
      fin_cases i
      · norm_num
      · norm_num
      · exact absurd rfl hother)
    (le_of_eq splitTetraCap_capDet.symm)

/-- **The same tie, certified with no matrix data at all.** The rank-three
scalar producer needs only the gate pair's leverages (`3` each) and inner
product (`-1`): the shifted-leverage sum is `4 > 0`, the shifted-leverage
determinant is `2·2 − (−1)² = 3 > 0`, and the enlarged Gram shift has
determinant `0 ≥ 0`. Three rational comparisons, and domination out. -/
theorem splitTetraRatDesign_pairGateCertified_dominates :
    Dominates splitTetraRatDesign.toReal (insert 2 ({0, 1} : Finset (Fin 6))) :=
  ratDominates_of_pairGate splitTetraRatDesign 0 1 2 (by decide) (by decide)
    (by
      norm_num [splitTetraRatDesign, splitTetraRatAtom, Fin.sum_univ_three,
        Matrix.cons_val_two, Matrix.tail_cons])
    (by
      norm_num [splitTetraRatDesign, splitTetraRatAtom, Fin.sum_univ_three,
        dotProduct, Matrix.cons_val_two, Matrix.tail_cons])
    (le_of_eq splitTetraCap_capDet.symm)

end Gtz
