/-
# The near-pencil residue: the rank-two transport, and why a near-pencil is never a tie

`Gtz.Design.PrimitiveTightClassification` closes the near-pencil ledger entries
`q6m3` (one five-point line) and `q7m4` (one six-point line) modulo ONE named
residue.  Half of the entry was already mechanized there:
`exists_sharedNormal_of_isPrimitiveDesign` manufactures the single normal shared
by all planar atoms out of the line pattern, and `soleOffPlane_share_eq_one` /
`soleOffPlane_leverage_one_lt` pin the pole's share at `1` and its leverage
strictly above `1`.  What was missing is the RANK-TWO TRANSPORT: turning
`Gtz.gtz_rank_two` into a planar pair whose Gram exceeds the identity by a
FACTOR, not merely weakly.  This file supplies it and consumes it.

## The residue, and why the factor points the way it does

Write `t` for the pole's weight and `poleShare = 1 - t` for the planar weight
total.  Compressing the WHOLE design through the plane is already a rank-two
design (`Gtz.compressedDesign`; the pole compresses to the zero atom and
contributes nothing), so `gtz_rank_two` hands over a pair with
`Σ_{c ∈ pair} (P g_c)(P g_c)ᵀ ⪰ I₂`.  That is USELESS: weak domination on the
plane plus the pole axis gives `S_B − I ⪰ 0`, which a tie already has.  The
strictness has to come from somewhere, and it comes from the pole's WEIGHT being
dead mass on the plane.  Reallocating it — weights `t/2` on the (zero) pole atom
and `(1 − t/2)·t_c/poleShare` on the others, atoms rescaled by
`√(poleShare/(1 − t/2))` — is again a design, and now `gtz_rank_two` gives

    Σ_{c ∈ pair} (P g_c)(P g_c)ᵀ  ⪰  ((1 − t/2)/poleShare) · I₂,

with `(1 − t/2)/poleShare = (1 − t/2)/(1 − t) > 1`.  The factor is a RECIPROCAL
of the planar share; the file this one serves warns that "getting it backwards
makes the argument fail", and that is literal: `poleShare = 1 − t < 1`, so a
floor of `1 − t` would be a floor BELOW one and would prove nothing.  Any split
`eps ∈ (0, t)` works and `eps = t/2` is the one taken here.

The assembly is then block-diagonal.  On the pole's own axis the gap is
`|g_p|² − 1 = (1 − t)/t > 0` (`soleOffPlane_leverage_one_lt`); on the plane it is
`floor − 1 > 0`; the two blocks do not interact because the pole is orthogonal to
the plane.  So `S_{{pole} ∪ pair} − I` is POSITIVE DEFINITE, which is strictly
stronger than what a tie is allowed to have.

## PROVED here, kernel-checked, unconditional

* `exists_orthonormalPlane_of_ne_zero` — an orthonormal `2 × 3` frame killing a
  prescribed nonzero direction, together with the COMPLETENESS identity
  `Pᵀ P + |n|⁻² n nᵀ = I₃`.  Rides `Gtz.exists_orthonormal_completion`
  (`Gtz.LinAlg.Completion`) at a one-column input, so no case analysis on the
  normal's coordinates is needed.
* `exists_ne_zero_orthogonal_planar`, `not_dominates_of_zero_atom_planar` — in
  the plane a pair containing a ZERO atom never dominates: the surviving atom is
  rank one and something nonzero is orthogonal to it.  This is what forces the
  transported pair to avoid the pole.
* `rescaledPlanarDesign` — the transport itself: the pole-penalized, atom-rescaled
  rank-two design on the SAME index set.  Keeping all `m` labels (the pole's atom
  is the zero vector, its weight the split fraction) avoids every index surgery;
  the pole's weight is exactly the dead mass whose reallocation sharpens the floor.
* `exists_planar_pair_strictFloor` — the residue, stated in quadratic-form
  language: a pair avoiding the pole and a floor `> 1` it beats on every planar
  probe.  Rides `Gtz.gtz_rank_two`, which is a repository THEOREM, so nothing is
  assumed.
* `dotProduct_pole_eq_zero_of_solePole` — the shared normal is parallel to the
  pole atom (`soleOffPlane_normal_eq_smul_pole`), so the planar atoms are
  orthogonal to the POLE ATOM itself and the plane may be built from it.
* **`exists_posDef_triple_of_solePole`** — the payload: a near-pencil design at
  any size `≥ 2` has a triple whose gap matrix is POSITIVE DEFINITE.  So
  near-pencils satisfy weighted GTZ with room to spare.
* **`not_isTie_of_solePole`** — hence no near-pencil design is a tie.
* **`stratumIsTieFree_of_solePoleOffLine`** — the ledger form: any line pattern
  declaring one distinguished label off a line through all the others is
  tie-free.  Note primitivity is NOT a hypothesis: the pattern's own INEQUATION
  at the triple `(first, second, pole)` already forces the two chosen planar
  atoms non-parallel, which is all the normal needs.  This retires the two
  near-pencil isomorphism classes at `q = 6` and `q = 7` — and the same statement
  at every other size.
* `nearPencilSixDesign`, `nearPencilSevenDesign`,
  `nearPencilSixStratum_isNonempty_and_tieFree`,
  `nearPencilSevenStratum_isNonempty_and_tieFree` — the non-vacuity controls, in
  the shape `Gtz.parallelPairStratum_isNonempty_and_tieFree` set.  Both strata
  are INHABITED by exact rational designs and empty of ties, so neither
  emptiness claim hides behind an unsatisfiable `HasLinePattern`.

## CITED, not reproved here

* `Gtz.gtz_rank_two` (`Gtz.Reduction.Reductions`) — rank-two weighted GTZ, an
  in-repo proof.  It is the only external input to the transport.
* `Gtz.compressedDesign` / `Gtz.compressed_dominates_iff`
  (`Gtz.Reduction.Compression`) — Lemma G.  Only the Parseval half is used, to
  discharge the rescaled design's Parseval identity by termwise comparison.
* `Gtz.exists_orthonormal_completion` (`Gtz.LinAlg.Completion`) — orthonormal
  completion via `stdOrthonormalBasis` on the orthogonal complement.
* `Gtz.soleOffPlane_normal_eq_smul_pole`, `Gtz.soleOffPlane_leverage_one_lt`,
  `Gtz.LinePattern`, `Gtz.HasLinePattern`, `Gtz.StratumIsTieFree`,
  `Gtz.bracketNormal`, `Gtz.tripleBracket_eq_bracketNormal_dotProduct`
  (`Gtz.Design.PrimitiveTightClassification`) — the near-pencil collapse and the
  stratum vocabulary.
* `Gtz.not_dominates_of_commonOrthogonal`, `Gtz.dotProduct_subsetSum_mulVec_of_finset`
  (`Gtz.Ties.TotalTieCorankOne`), `Gtz.dotProduct_atomMatrix_mulVec`
  (`Gtz.Reduction.RealVolumeFloor`), `Gtz.weight_lt_one` (`Gtz.Core.Sanity`),
  `Gtz.dotProduct_mulVec_transpose` (`Gtz.LinAlg.PsdKit`).

## MEASURED, outside Lean — the exact-rational validation of the residue

The whole chain was executed in `Fraction` arithmetic before mechanization, at
the two shipped witnesses and at forty randomly generated exact-rational
near-pencils with `4 … 7` planar atoms.  Parseval residual was an EXACT zero in
every case, never a float tolerance.  At `nearPencilSixDesign`:
`t = 1/4`, `poleShare = 3/4`, pole leverage `4` with `t·leverage = 1` on the
nose, split `1/8`, `scale² = 6/7`, sharpened floor `7/6 > 1`, and the four
transported triples have `det(S − I) = 27, 24, 3, 9` — all four principal-minor
sequences strictly positive.  At `nearPencilSevenDesign` the six transported
triples have `det(S − I) = 27, 24, 24, 3, 9, 9`.  The backwards factor was
checked numerically as well: at both witnesses `1/(1 − t) = 4/3 > 1` while
`1 − t = 3/4 < 1`, so orienting the transport the other way yields a floor below
one.  Exhaustively, `nearPencilSevenDesign` has SIX strictly dominating triples
and one weak-but-not-strict triple, so the weak conclusion alone genuinely fails
to decide the question there while the sharpened one settles it.

## Name disjointness from the parallel mechanization

A second, independently authored module `Gtz.Design.NearPencilStrictDomination`
reaches the same conclusion by the same route (its `not_isTie_of_soleOffPlane`
and `stratumIsTieFree_nearPencil` correspond to this file's
`not_isTie_of_solePole` and `stratumIsTieFree_solePoleLinePattern`).  Every
declaration name here is therefore chosen DISJOINT from that module's — the
pattern is `solePoleLinePattern`, not `nearPencilLinePattern` — so both may be
imported into the umbrella and the axiom ledger without a duplicate global.  Two
independent derivations of the same residue is a cross-check, not a duplication
to be silently resolved; a wiring decision between them belongs upstream, not
here.

No statement in this file assumes total tie, criticality of the maximum, any
local-minimality property of a tie, or `GtzWeighted` at rank three.  The only
GTZ input is rank TWO, which is proved.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Core.Sanity
import Gtz.LinAlg.Completion
import Gtz.Reduction.Compression
import Gtz.Design.PrimitiveTightClassification

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

/-! ## Two pieces of atom bookkeeping -/

/-- The leverage is the self dot product. -/
theorem leverageOf_eq_dotProduct_self {k : ℕ} (vec : Fin k → ℝ) :
    leverageOf vec = vec ⬝ᵥ vec := by
  simp only [leverageOf, dotProduct, pow_two]

/-- The zero vector's atom is the zero matrix. -/
theorem atomMatrix_eq_zero {k : ℕ} : atomMatrix (0 : Fin k → ℝ) = 0 := by
  ext rowIndex colIndex
  simp only [atomMatrix, Matrix.vecMulVec_apply, Pi.zero_apply, Matrix.zero_apply, mul_zero]

/-- An atom applied to a vector is a rescaled copy of the atom's own direction. -/
theorem atomMatrix_mulVec_eq_smul {k : ℕ} (vec direction : Fin k → ℝ) :
    atomMatrix vec *ᵥ direction = (vec ⬝ᵥ direction) • vec := by
  funext coordIndex
  simp only [atomMatrix, Matrix.vecMulVec, Matrix.mulVec, dotProduct, Matrix.of_apply,
    Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-! ## An orthonormal plane orthogonal to a prescribed direction

`Gtz.exists_orthonormal_completion` completes a matrix with orthonormal columns
to a square orthogonal one.  Feeding it the single normalized column `n/|n|`
returns the plane's two columns together with the completeness identity, so no
case analysis on the normal's coordinates is required. -/

/-- **The orthonormal plane through a nonzero normal's orthogonal complement.**
The three conclusions are: the plane's rows are orthonormal, the plane kills the
normal, and the plane together with the normalized normal resolves the identity
of `ℝ³`.  The third is the one that makes `|x|² = |P x|² + (n ⬝ᵥ x)²/|n|²` and
lets a planar atom be reconstructed from its planar shadow. -/
theorem exists_orthonormalPlane_of_ne_zero (normalVec : Fin 3 → ℝ) (hne : normalVec ≠ 0) :
    ∃ plane : Matrix (Fin 2) (Fin 3) ℝ,
      plane * planeᵀ = 1 ∧ plane *ᵥ normalVec = 0 ∧
        planeᵀ * plane + (normalVec ⬝ᵥ normalVec)⁻¹ • atomMatrix normalVec = 1 := by
  have hnormPos : 0 < normalVec ⬝ᵥ normalVec := dotProduct_self_pos hne
  set unitScale : ℝ := (Real.sqrt (normalVec ⬝ᵥ normalVec))⁻¹ with hunitScale
  have hscaleNe : unitScale ≠ 0 := by
    rw [hunitScale]
    exact inv_ne_zero (ne_of_gt (Real.sqrt_pos.mpr hnormPos))
  have hscaleSq : unitScale ^ 2 = (normalVec ⬝ᵥ normalVec)⁻¹ := by
    rw [hunitScale, inv_pow, Real.sq_sqrt hnormPos.le]
  set column : Matrix (Fin 3) (Fin 1) ℝ :=
    Matrix.of (fun rowIndex _ => unitScale * normalVec rowIndex) with hcolumn
  have hcolumnGram : columnᵀ * column = 1 := by
    ext firstIndex secondIndex
    have hsame : firstIndex = secondIndex := Subsingleton.elim _ _
    subst hsame
    have hentry : (columnᵀ * column) firstIndex firstIndex
        = unitScale ^ 2 * (normalVec ⬝ᵥ normalVec) := by
      simp only [Matrix.mul_apply, Matrix.transpose_apply, hcolumn, Matrix.of_apply,
        dotProduct, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [hentry, hscaleSq, inv_mul_cancel₀ (ne_of_gt hnormPos), Matrix.one_apply_eq]
  obtain ⟨complement, hcomplementGram, hcross, hcomplete⟩ :=
    exists_orthonormal_completion column hcolumnGram
  refine ⟨complementᵀ, ?_, ?_, ?_⟩
  · rw [Matrix.transpose_transpose]; exact hcomplementGram
  · funext planeIndex
    have hzero := congrFun (congrFun hcross 0) planeIndex
    simp only [Matrix.mul_apply, Matrix.transpose_apply, hcolumn, Matrix.of_apply,
      Matrix.zero_apply] at hzero
    have hfactored : unitScale
        * ∑ innerIndex, complement innerIndex planeIndex * normalVec innerIndex = 0 := by
      rw [Finset.mul_sum, ← hzero]
      exact Finset.sum_congr rfl fun _ _ => by ring
    have hsum : ∑ innerIndex, complement innerIndex planeIndex * normalVec innerIndex = 0 := by
      rcases mul_eq_zero.mp hfactored with hbad | hgood
      · exact absurd hbad hscaleNe
      · exact hgood
    simpa only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Pi.zero_apply] using hsum
  · have hrankOne : column * columnᵀ
        = (normalVec ⬝ᵥ normalVec)⁻¹ • atomMatrix normalVec := by
      ext firstIndex secondIndex
      simp only [Matrix.mul_apply, Matrix.transpose_apply, hcolumn, Matrix.of_apply,
        Fin.sum_univ_one, Matrix.smul_apply, atomMatrix, Matrix.vecMulVec_apply, smul_eq_mul,
        ← hscaleSq]
      ring
    rw [Matrix.transpose_transpose, ← hrankOne, add_comm]
    exact hcomplete

/-! ## In the plane a pair through a zero atom never dominates

This is the step that forces the transported pair to AVOID the pole.  In `ℝ²`
every single vector has a nonzero orthogonal companion, so a pair one of whose
atoms vanishes has a common orthogonal direction and
`Gtz.not_dominates_of_commonOrthogonal` applies. -/

/-- Every planar vector has a nonzero orthogonal companion. -/
theorem exists_ne_zero_orthogonal_planar (vec : Fin 2 → ℝ) :
    ∃ direction : Fin 2 → ℝ, direction ≠ 0 ∧ vec ⬝ᵥ direction = 0 := by
  by_cases hzero : vec = 0
  · refine ⟨![1, 0], ?_, ?_⟩
    · intro hcontra
      have hfirst := congrFun hcontra 0
      simp only [Matrix.cons_val_zero, Pi.zero_apply] at hfirst
      exact one_ne_zero hfirst
    · rw [hzero]
      simp only [dotProduct, Pi.zero_apply, zero_mul, Finset.sum_const_zero]
  · have hnormEq : (![-(vec 1), vec 0] : Fin 2 → ℝ) ⬝ᵥ ![-(vec 1), vec 0] = vec ⬝ᵥ vec := by
      simp only [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
      ring
    refine ⟨![-(vec 1), vec 0], ?_, ?_⟩
    · intro hcontra
      refine hzero (eq_zero_of_dotProduct_self_eq_zero ?_)
      rw [← hnormEq, hcontra]
      simp only [dotProduct, Pi.zero_apply, zero_mul, Finset.sum_const_zero]
    · simp only [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
      ring

/-- **A planar pair carrying a zero atom never dominates.** -/
theorem not_dominates_of_zero_atom_planar {m : ℕ} (D : WeightedDesign m 2)
    (pair : Finset (Fin m)) (hcard : pair.card = 2) (zeroLabel : Fin m)
    (hmember : zeroLabel ∈ pair) (hzeroAtom : D.atom zeroLabel = 0) : ¬ Dominates D pair := by
  classical
  have hcardErase : (pair.erase zeroLabel).card = 1 := by
    rw [Finset.card_erase_of_mem hmember, hcard]
  obtain ⟨otherLabel, hErased⟩ := Finset.card_eq_one.mp hcardErase
  have hpair : pair = insert zeroLabel {otherLabel} := by
    rw [← Finset.insert_erase hmember, hErased]
  obtain ⟨direction, hdirectionNe, hperp⟩ := exists_ne_zero_orthogonal_planar (D.atom otherLabel)
  refine not_dominates_of_commonOrthogonal D pair ⟨direction, hdirectionNe, fun label hlabel => ?_⟩
  rw [hpair] at hlabel
  simp only [Finset.mem_insert, Finset.mem_singleton] at hlabel
  rcases hlabel with rfl | rfl
  · rw [hzeroAtom]
    simp only [dotProduct, Pi.zero_apply, zero_mul, Finset.sum_const_zero]
  · exact hperp

/-! ## The transport: the pole-penalized planar design

The pole's weight is dead mass on the plane, and reallocating it is exactly what
sharpens the floor.  Every label is kept — the pole's transported atom is the
zero vector because the plane kills it — so no index surgery appears anywhere. -/

/-- **The rank-two transport of a near-pencil.**  The plane's compression of the
design, with the pole's weight cut to `splitFraction` and the remaining weights
renormalized over `1 − t_pole`, all atoms rescaled by
`√((1 − t_pole)/(1 − splitFraction))`.  A genuine `WeightedDesign _ 2`: the
pole's transported atom vanishes, so its weight contributes nothing to Parseval
and is free to be any positive number below one. -/
noncomputable def rescaledPlanarDesign {m : ℕ} (D : WeightedDesign m 3) (poleLabel : Fin m)
    (plane : Matrix (Fin 2) (Fin 3) ℝ) (hOrthonormal : plane * planeᵀ = 1)
    (hPoleKilled : plane *ᵥ D.atom poleLabel = 0)
    (splitFraction : ℝ) (hsplitPos : 0 < splitFraction) (hsplitLtOne : splitFraction < 1)
    (hpoleSharePos : 0 < 1 - D.weight poleLabel) : WeightedDesign m 2 where
  atom := fun label =>
    Real.sqrt ((1 - D.weight poleLabel) / (1 - splitFraction)) • (plane *ᵥ D.atom label)
  weight := fun label =>
    if label = poleLabel then splitFraction
    else (1 - splitFraction) * D.weight label / (1 - D.weight poleLabel)
  weight_pos := by
    intro label
    by_cases hlabel : label = poleLabel
    · rw [if_pos hlabel]; exact hsplitPos
    · rw [if_neg hlabel]
      exact div_pos (mul_pos (by linarith) (D.weight_pos label)) hpoleSharePos
  weight_sum_one := by
    have hshareSum : ∑ label ∈ Finset.univ.erase poleLabel, D.weight label
        = 1 - D.weight poleLabel := by
      have hsplitOff := Finset.sum_erase_add Finset.univ D.weight (Finset.mem_univ poleLabel)
      rw [D.weight_sum_one] at hsplitOff
      linarith
    have hstep := Finset.sum_erase_add Finset.univ
      (fun label => if label = poleLabel then splitFraction
        else (1 - splitFraction) * D.weight label / (1 - D.weight poleLabel))
      (Finset.mem_univ poleLabel)
    have hplanarPart : ∑ label ∈ Finset.univ.erase poleLabel,
        (if label = poleLabel then splitFraction
          else (1 - splitFraction) * D.weight label / (1 - D.weight poleLabel))
        = 1 - splitFraction := by
      have hrewrite : ∀ label ∈ Finset.univ.erase poleLabel,
          (if label = poleLabel then splitFraction
            else (1 - splitFraction) * D.weight label / (1 - D.weight poleLabel))
          = (1 - splitFraction) / (1 - D.weight poleLabel) * D.weight label := by
        intro label hlabel
        rw [if_neg (Finset.mem_erase.mp hlabel).1]
        ring
      rw [Finset.sum_congr rfl hrewrite, ← Finset.mul_sum, hshareSum]
      field_simp
    rw [← hstep, hplanarPart, if_pos rfl]
    ring
  isParseval := by
    have hretainedPos : (0 : ℝ) < 1 - splitFraction := by linarith
    have hscaleSq : Real.sqrt ((1 - D.weight poleLabel) / (1 - splitFraction)) ^ 2
        = (1 - D.weight poleLabel) / (1 - splitFraction) :=
      Real.sq_sqrt (div_pos hpoleSharePos hretainedPos).le
    have hcompressedParseval :
        ∑ label, D.weight label • atomMatrix (plane *ᵥ D.atom label)
          = (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
      have hparseval := (compressedDesign D plane hOrthonormal).isParseval
      simp only [compressedDesign_atom] at hparseval
      exact hparseval
    rw [← hcompressedParseval]
    refine Finset.sum_congr rfl fun label _ => ?_
    by_cases hlabel : label = poleLabel
    · subst hlabel
      rw [hPoleKilled, smul_zero, atomMatrix_eq_zero, smul_zero, smul_zero]
    · rw [atomMatrix_smul, smul_smul, if_neg hlabel, hscaleSq]
      congr 1
      field_simp

@[simp] theorem rescaledPlanarDesign_atom {m : ℕ} (D : WeightedDesign m 3) (poleLabel : Fin m)
    (plane : Matrix (Fin 2) (Fin 3) ℝ) (hOrthonormal : plane * planeᵀ = 1)
    (hPoleKilled : plane *ᵥ D.atom poleLabel = 0)
    (splitFraction : ℝ) (hsplitPos : 0 < splitFraction) (hsplitLtOne : splitFraction < 1)
    (hpoleSharePos : 0 < 1 - D.weight poleLabel) (label : Fin m) :
    (rescaledPlanarDesign D poleLabel plane hOrthonormal hPoleKilled splitFraction hsplitPos
      hsplitLtOne hpoleSharePos).atom label
      = Real.sqrt ((1 - D.weight poleLabel) / (1 - splitFraction)) • (plane *ᵥ D.atom label) :=
  rfl

/-! ## The residue itself

`gtz_rank_two` applied to the transport gives a pair, and the rescaling turns its
weak planar domination into a floor strictly above one. -/

/-- **The sharpened planar pair** — the named residue, discharged.  At a design
whose pole the plane kills, some pair of NON-pole labels beats a floor strictly
greater than one on every planar probe.  The rank-two input is
`Gtz.gtz_rank_two`, a theorem, so this is unconditional. -/
theorem exists_planar_pair_strictFloor {m : ℕ} (hsize : 2 ≤ m) (D : WeightedDesign m 3)
    (poleLabel : Fin m) (plane : Matrix (Fin 2) (Fin 3) ℝ)
    (hOrthonormal : plane * planeᵀ = 1)
    (hPoleKilled : plane *ᵥ D.atom poleLabel = 0) :
    ∃ (planarFloor : ℝ) (pair : Finset (Fin m)), 1 < planarFloor ∧ pair.card = 2 ∧
      poleLabel ∉ pair ∧
      ∀ probe : Fin 2 → ℝ, planarFloor * (probe ⬝ᵥ probe)
        ≤ ∑ label ∈ pair, ((plane *ᵥ D.atom label) ⬝ᵥ probe) ^ 2 := by
  classical
  have hpoleWeightPos : 0 < D.weight poleLabel := D.weight_pos poleLabel
  have hpoleWeightLtOne : D.weight poleLabel < 1 := weight_lt_one D hsize poleLabel
  have hpoleSharePos : (0 : ℝ) < 1 - D.weight poleLabel := by linarith
  have hsplitPos : (0 : ℝ) < D.weight poleLabel / 2 := by linarith
  have hsplitLtOne : D.weight poleLabel / 2 < 1 := by linarith
  have hretainedPos : (0 : ℝ) < 1 - D.weight poleLabel / 2 := by linarith
  set scaleSquared : ℝ := (1 - D.weight poleLabel) / (1 - D.weight poleLabel / 2)
    with hscaleSquared
  have hscaleSquaredPos : 0 < scaleSquared := div_pos hpoleSharePos hretainedPos
  have hscaleSq : Real.sqrt scaleSquared ^ 2 = scaleSquared := Real.sq_sqrt hscaleSquaredPos.le
  set planarFloor : ℝ := (1 - D.weight poleLabel / 2) / (1 - D.weight poleLabel)
    with hplanarFloor
  have hfloorGtOne : 1 < planarFloor := by
    rw [hplanarFloor, lt_div_iff₀ hpoleSharePos]
    linarith
  have hfloorScale : planarFloor * scaleSquared = 1 := by
    rw [hplanarFloor, hscaleSquared, div_mul_div_comm,
      mul_comm (1 - D.weight poleLabel) (1 - D.weight poleLabel / 2)]
    exact div_self (mul_ne_zero (ne_of_gt hretainedPos) (ne_of_gt hpoleSharePos))
  set transported := rescaledPlanarDesign D poleLabel plane hOrthonormal hPoleKilled
    (D.weight poleLabel / 2) hsplitPos hsplitLtOne hpoleSharePos with htransported
  obtain ⟨pair, hcard, hdominates⟩ := gtz_rank_two m transported
  have hpoleAtomZero : transported.atom poleLabel = 0 := by
    rw [htransported, rescaledPlanarDesign_atom, hPoleKilled, smul_zero]
  have hpoleOut : poleLabel ∉ pair := fun hmember =>
    not_dominates_of_zero_atom_planar transported pair hcard poleLabel hmember hpoleAtomZero
      hdominates
  refine ⟨planarFloor, pair, hfloorGtOne, hcard, hpoleOut, fun probe => ?_⟩
  have hform : 0 ≤ probe ⬝ᵥ ((subsetSum transported pair - 1) *ᵥ probe) := by
    have hnonneg := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hdominates).2 probe
    rwa [star_trivial] at hnonneg
  rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec,
    dotProduct_subsetSum_mulVec_of_finset] at hform
  have hscaled : ∑ label ∈ pair, (transported.atom label ⬝ᵥ probe) ^ 2
      = scaleSquared * ∑ label ∈ pair, ((plane *ᵥ D.atom label) ⬝ᵥ probe) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun label _ => ?_
    rw [htransported, rescaledPlanarDesign_atom, smul_dotProduct, smul_eq_mul, mul_pow, hscaleSq]
  rw [hscaled] at hform
  have hbound : probe ⬝ᵥ probe
      ≤ scaleSquared * ∑ label ∈ pair, ((plane *ᵥ D.atom label) ⬝ᵥ probe) ^ 2 := by linarith
  calc planarFloor * (probe ⬝ᵥ probe)
      ≤ planarFloor * (scaleSquared * ∑ label ∈ pair,
          ((plane *ᵥ D.atom label) ⬝ᵥ probe) ^ 2) := by
        exact mul_le_mul_of_nonneg_left hbound (by linarith)
    _ = ∑ label ∈ pair, ((plane *ᵥ D.atom label) ⬝ᵥ probe) ^ 2 := by
        rw [← mul_assoc, hfloorScale, one_mul]

/-! ## From the shared normal to the pole axis

`soleOffPlane_normal_eq_smul_pole` says the shared normal is a multiple of the
pole's atom with a nonzero factor, so orthogonality to the normal is
orthogonality to the POLE ATOM.  That is what lets the plane be built from
`D.atom poleLabel` directly. -/

/-- **The planar atoms are orthogonal to the pole atom.** -/
theorem dotProduct_pole_eq_zero_of_solePole {m : ℕ} (D : WeightedDesign m 3)
    (poleLabel : Fin m) {normalVec : Fin 3 → ℝ} (hnormalNe : normalVec ≠ 0)
    (hplanar : ∀ label, label ≠ poleLabel → D.atom label ⬝ᵥ normalVec = 0)
    (label : Fin m) (hlabel : label ≠ poleLabel) :
    D.atom label ⬝ᵥ D.atom poleLabel = 0 := by
  obtain ⟨ratio, hratio⟩ : ∃ ratio : ℝ, normalVec = ratio • D.atom poleLabel :=
    ⟨D.weight poleLabel * (D.atom poleLabel ⬝ᵥ normalVec),
      soleOffPlane_normal_eq_smul_pole D poleLabel hplanar⟩
  have hratioNe : ratio ≠ 0 := by
    intro hratioZero
    rw [hratioZero, zero_smul] at hratio
    exact hnormalNe hratio
  have hprojected : D.atom label ⬝ᵥ normalVec
      = ratio * (D.atom label ⬝ᵥ D.atom poleLabel) := by
    rw [hratio, dotProduct_smul, smul_eq_mul]
  rw [hplanar label hlabel] at hprojected
  rcases mul_eq_zero.mp hprojected.symm with hbad | hgood
  · exact absurd hbad hratioNe
  · exact hgood

/-! ## The payload: a near-pencil has a strictly dominating triple

The gap matrix of `{pole} ∪ pair` is block diagonal with respect to the pole's
axis and the plane.  On the axis the gap is `|g_p|² − 1 > 0`
(`soleOffPlane_leverage_one_lt`); on the plane it is `planarFloor − 1 > 0`.  A
nonzero probe has a nonzero component in at least one block, so the form is
strictly positive. -/

/-- **A near-pencil design has a POSITIVE DEFINITE gap on some triple.**  So it
satisfies weighted GTZ at rank three with room to spare.  Hypotheses: at least
two atoms, one distinguished label, and a nonzero direction every other atom is
orthogonal to. -/
theorem exists_posDef_triple_of_solePole {m : ℕ} (hsize : 2 ≤ m) (D : WeightedDesign m 3)
    (poleLabel : Fin m) {normalVec : Fin 3 → ℝ} (hnormalNe : normalVec ≠ 0)
    (hplanar : ∀ label, label ≠ poleLabel → D.atom label ⬝ᵥ normalVec = 0) :
    ∃ triple : Finset (Fin m), triple.card = 3 ∧ (subsetSum D triple - 1).PosDef := by
  classical
  have hleverageGtOne : 1 < leverageOf (D.atom poleLabel) :=
    soleOffPlane_leverage_one_lt hsize D poleLabel hnormalNe hplanar
  have hpoleNormSq : D.atom poleLabel ⬝ᵥ D.atom poleLabel = leverageOf (D.atom poleLabel) :=
    (leverageOf_eq_dotProduct_self (D.atom poleLabel)).symm
  have hzeroLeverage : leverageOf (0 : Fin 3 → ℝ) = 0 := by
    simp only [leverageOf, Pi.zero_apply, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, Finset.sum_const_zero]
  have hpoleNe : D.atom poleLabel ≠ 0 := by
    intro hzero
    rw [hzero, hzeroLeverage] at hleverageGtOne
    linarith
  obtain ⟨plane, hOrthonormal, hPoleKilled, hcomplete⟩ :=
    exists_orthonormalPlane_of_ne_zero (D.atom poleLabel) hpoleNe
  obtain ⟨planarFloor, pair, hfloorGtOne, hcard, hpoleOut, hfloorBound⟩ :=
    exists_planar_pair_strictFloor hsize D poleLabel plane hOrthonormal hPoleKilled
  refine ⟨insert poleLabel pair, ?_, ?_⟩
  · rw [Finset.card_insert_of_notMem hpoleOut, hcard]
  · -- the two reconstruction identities the completeness identity provides
    have hnormSplit : ∀ probe : Fin 3 → ℝ, probe ⬝ᵥ probe
        = (plane *ᵥ probe) ⬝ᵥ (plane *ᵥ probe)
          + (leverageOf (D.atom poleLabel))⁻¹ * (D.atom poleLabel ⬝ᵥ probe) ^ 2 := by
      intro probe
      have happlied := congrArg (fun gram => probe ⬝ᵥ (gram *ᵥ probe)) hcomplete
      simp only [Matrix.add_mulVec, dotProduct_add, Matrix.smul_mulVec, dotProduct_smul,
        smul_eq_mul, Matrix.one_mulVec] at happlied
      rw [dotProduct_atomMatrix_mulVec, hpoleNormSq] at happlied
      have hplaneBlock : probe ⬝ᵥ ((planeᵀ * plane) *ᵥ probe)
          = (plane *ᵥ probe) ⬝ᵥ (plane *ᵥ probe) := by
        rw [← Matrix.mulVec_mulVec, dotProduct_comm,
          dotProduct_mulVec_transpose plane (plane *ᵥ probe) probe]
      rw [hplaneBlock] at happlied
      exact happlied.symm
    have hplanarShadow : ∀ label ∈ pair, ∀ probe : Fin 3 → ℝ,
        D.atom label ⬝ᵥ probe = (plane *ᵥ D.atom label) ⬝ᵥ (plane *ᵥ probe) := by
      intro label hlabel probe
      have hlabelNe : label ≠ poleLabel := fun hequal => hpoleOut (hequal ▸ hlabel)
      have hperp : D.atom label ⬝ᵥ D.atom poleLabel = 0 :=
        dotProduct_pole_eq_zero_of_solePole D poleLabel hnormalNe hplanar label hlabelNe
      have hrebuild : planeᵀ *ᵥ (plane *ᵥ D.atom label) = D.atom label := by
        have happlied := congrArg (fun gram => gram *ᵥ D.atom label) hcomplete
        simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] at happlied
        rw [atomMatrix_mulVec_eq_smul,
          dotProduct_comm (D.atom poleLabel) (D.atom label), hperp, zero_smul, smul_zero,
          add_zero] at happlied
        rw [Matrix.mulVec_mulVec]
        exact happlied
      calc D.atom label ⬝ᵥ probe
          = (planeᵀ *ᵥ (plane *ᵥ D.atom label)) ⬝ᵥ probe := by rw [hrebuild]
        _ = (plane *ᵥ D.atom label) ⬝ᵥ (plane *ᵥ probe) :=
            dotProduct_mulVec_transpose plane (plane *ᵥ D.atom label) probe
    -- the gap form, block by block
    have hhermitian : (subsetSum D (insert poleLabel pair) - 1).IsHermitian :=
      Matrix.IsHermitian.sub
        (Matrix.posSemidef_sum (insert poleLabel pair)
          (fun label _ => posSemidef_atomMatrix (D.atom label))).isHermitian
        Matrix.isHermitian_one
    refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨hhermitian, fun probe hprobeNe => ?_⟩
    rw [star_trivial]
    have hform : probe ⬝ᵥ ((subsetSum D (insert poleLabel pair) - 1) *ᵥ probe)
        = (D.atom poleLabel ⬝ᵥ probe) ^ 2
          + ∑ label ∈ pair, (D.atom label ⬝ᵥ probe) ^ 2 - probe ⬝ᵥ probe := by
      rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec,
        dotProduct_subsetSum_mulVec_of_finset, Finset.sum_insert hpoleOut]
    have hplanarSum : ∑ label ∈ pair, (D.atom label ⬝ᵥ probe) ^ 2
        = ∑ label ∈ pair, ((plane *ᵥ D.atom label) ⬝ᵥ (plane *ᵥ probe)) ^ 2 :=
      Finset.sum_congr rfl fun label hlabel => by rw [hplanarShadow label hlabel probe]
    have hfloorAtProbe : planarFloor * ((plane *ᵥ probe) ⬝ᵥ (plane *ᵥ probe))
        ≤ ∑ label ∈ pair, ((plane *ᵥ D.atom label) ⬝ᵥ (plane *ᵥ probe)) ^ 2 :=
      hfloorBound (plane *ᵥ probe)
    set shadowNormSq : ℝ := (plane *ᵥ probe) ⬝ᵥ (plane *ᵥ probe) with hshadowNormSq
    set axisProjection : ℝ := D.atom poleLabel ⬝ᵥ probe with haxisProjection
    have hshadowNonneg : 0 ≤ shadowNormSq := dotProduct_self_nonneg _
    have hleveragePos : 0 < leverageOf (D.atom poleLabel) := by linarith
    have hinvLtOne : (leverageOf (D.atom poleLabel))⁻¹ < 1 :=
      inv_lt_one_of_one_lt₀ hleverageGtOne
    have hsplitNorm : probe ⬝ᵥ probe
        = shadowNormSq + (leverageOf (D.atom poleLabel))⁻¹ * axisProjection ^ 2 :=
      hnormSplit probe
    have hprobePos : 0 < probe ⬝ᵥ probe := dotProduct_self_pos hprobeNe
    rw [hform, hplanarSum, hsplitNorm]
    rcases lt_or_eq_of_le hshadowNonneg with hshadowPos | hshadowZero
    · nlinarith [sq_nonneg axisProjection, hfloorAtProbe]
    · have haxisPos : 0 < axisProjection ^ 2 := by
        rw [← hshadowZero] at hsplitNorm
        nlinarith [hprobePos, hsplitNorm]
      nlinarith [hfloorAtProbe, hshadowZero]

/-- **No near-pencil design is a tie.**  A tie forbids every `k`-subset from
dominating strictly; `exists_posDef_triple_of_solePole` produces one. -/
theorem not_isTie_of_solePole {m : ℕ} (hsize : 2 ≤ m) (D : WeightedDesign m 3)
    (poleLabel : Fin m) {normalVec : Fin 3 → ℝ} (hnormalNe : normalVec ≠ 0)
    (hplanar : ∀ label, label ≠ poleLabel → D.atom label ⬝ᵥ normalVec = 0) :
    ¬ IsTie D := by
  intro htie
  obtain ⟨triple, hcard, hposDef⟩ :=
    exists_posDef_triple_of_solePole hsize D poleLabel hnormalNe hplanar
  exact htie.2 triple hcard hposDef

/-! ## The ledger form: near-pencil line patterns are tie-free

A near-pencil pattern declares every triple inside one line dependent and every
triple through the distinguished label independent.  The INEQUATION at
`(first, second, pole)` is what makes the two chosen planar atoms non-parallel,
so the shared normal is nonzero without any primitivity hypothesis. -/

/-- A bracket with a repeated slot vanishes. -/
theorem tripleBracket_eq_zero_of_repeatMid (leftVec rightVec : Fin 3 → ℝ) :
    tripleBracket leftVec rightVec leftVec = 0 := by
  simp only [tripleBracket_eq]; ring

/-- A bracket with its last two slots equal vanishes. -/
theorem tripleBracket_eq_zero_of_repeatRight (leftVec rightVec : Fin 3 → ℝ) :
    tripleBracket leftVec rightVec rightVec = 0 := by
  simp only [tripleBracket_eq]; ring

/-- **Every stratum whose pattern puts one label off a line through all the
others is tie-free.**  The two hypotheses on the pattern are its line EQUATIONS
(every triple of non-pole labels through the chosen pair is dependent) and one
INEQUATION (the chosen pair together with the pole is a basis).  The latter is
load-bearing twice over: it makes the shared normal nonzero, and it is exactly
the open condition a near-pencil stratum carries. -/
theorem stratumIsTieFree_of_solePoleOffLine {size : ℕ} (hsize : 2 ≤ size)
    (pattern : LinePattern size) (poleLabel firstLabel secondLabel : Fin size)
    (hfirstPole : firstLabel ≠ poleLabel) (hsecondPole : secondLabel ≠ poleLabel)
    (hdistinct : firstLabel ≠ secondLabel)
    (hlineDependent : ∀ label, label ≠ poleLabel → label ≠ firstLabel → label ≠ secondLabel →
      pattern firstLabel secondLabel label)
    (hpoleIndependent : ¬ pattern firstLabel secondLabel poleLabel) :
    StratumIsTieFree pattern := by
  intro D hpattern htie
  set normalVec : Fin 3 → ℝ := bracketNormal (D.atom firstLabel) (D.atom secondLabel)
    with hnormalVec
  have hpoleBracketNe : atomBracket D firstLabel secondLabel poleLabel ≠ 0 := fun hvanish =>
    hpoleIndependent
      ((hpattern firstLabel secondLabel poleLabel hdistinct hfirstPole hsecondPole).mp hvanish)
  have hnormalNe : normalVec ≠ 0 := by
    intro hzero
    refine hpoleBracketNe ?_
    rw [atomBracket, tripleBracket_eq_bracketNormal_dotProduct, ← hnormalVec, hzero]
    simp only [dotProduct, Pi.zero_apply, zero_mul, Finset.sum_const_zero]
  have hplanar : ∀ label, label ≠ poleLabel → D.atom label ⬝ᵥ normalVec = 0 := by
    intro label hlabel
    rw [hnormalVec, dotProduct_comm, ← tripleBracket_eq_bracketNormal_dotProduct]
    by_cases hfirst : label = firstLabel
    · rw [hfirst]; exact tripleBracket_eq_zero_of_repeatMid _ _
    · by_cases hsecond : label = secondLabel
      · rw [hsecond]; exact tripleBracket_eq_zero_of_repeatRight _ _
      · exact (hpattern firstLabel secondLabel label hdistinct
          (fun hequal => hfirst hequal.symm) (fun hequal => hsecond hequal.symm)).mpr
          (hlineDependent label hlabel (fun hequal => hfirst hequal)
            (fun hequal => hsecond hequal))
  exact not_isTie_of_solePole hsize D poleLabel hnormalNe hplanar htie

/-- The near-pencil pattern on `size` labels with one distinguished pole: a
triple is dependent exactly when it avoids the pole.  Manifestly symmetric in
the three slots. -/
abbrev solePoleLinePattern {size : ℕ} (poleLabel : Fin size) : LinePattern size :=
  fun leftLabel midLabel rightLabel =>
    leftLabel ≠ poleLabel ∧ midLabel ≠ poleLabel ∧ rightLabel ≠ poleLabel

/-- **The near-pencil stratum is tie-free at every size.**  The `q = 6`
five-point-line and `q = 7` six-point-line isomorphism classes are the instances
`size = 6, 7`; via `Gtz.stratumIsTieFree_comp_relabel` each covers all of its
labellings. -/
theorem stratumIsTieFree_solePoleLinePattern {size : ℕ} (hsize : 2 ≤ size)
    (poleLabel firstLabel secondLabel : Fin size)
    (hfirstPole : firstLabel ≠ poleLabel) (hsecondPole : secondLabel ≠ poleLabel)
    (hdistinct : firstLabel ≠ secondLabel) :
    StratumIsTieFree (solePoleLinePattern poleLabel) :=
  stratumIsTieFree_of_solePoleOffLine hsize _ poleLabel firstLabel secondLabel
    hfirstPole hsecondPole hdistinct
    (fun _ hlabel _ _ => ⟨hfirstPole, hsecondPole, hlabel⟩)
    (fun hpattern => hpattern.2.2 rfl)

/-! ## Non-vacuity: the two hinge near-pencil strata carry designs

`HasLinePattern` is an iff over every distinct triple, so a slot-indexing or
symmetry slip would make a line-carrying `StratumIsTieFree` vacuously true and
nothing downstream would notice.  Both hinge near-pencils are therefore witnessed
by explicit exact-rational designs whose brackets are COMPUTED here, in the shape
`Gtz.parallelPairStratum_isNonempty_and_tieFree` set at `(4,3)`. -/

/-- Five coplanar directions plus a pole on the third axis: the `q = 6`
near-pencil, with the pole's share `t · |g|² = (1/4) · 4 = 1` on the nose. -/
def nearPencilSixAtom : Fin 6 → Fin 3 → ℝ :=
  ![![2, 0, 0], ![0, 2, 0], ![1, 1, 0], ![1, -1, 0], ![1, 2, 0], ![0, 0, 2]]

/-- The `q = 6` near-pencil design.  Planar weights `13/128, 7/128, 13/64,
21/64, 1/16` total `3/4`, the pole carries `1/4`, and the planar Parseval block
is the identity of the first two coordinates. -/
noncomputable def nearPencilSixDesign : WeightedDesign 6 3 where
  atom := nearPencilSixAtom
  weight := ![13/128, 7/128, 13/64, 21/64, 1/16, 1/4]
  weight_pos := by intro label; fin_cases label <;> norm_num
  weight_sum_one := by
    simp only [Fin.sum_univ_six, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.cons_val, Matrix.tail_cons]
    norm_num
  isParseval := by
    ext rowIndex colIndex
    simp only [Matrix.sum_apply, Matrix.smul_apply, atomMatrix, Matrix.vecMulVec_apply,
      Fin.sum_univ_six, smul_eq_mul, nearPencilSixAtom, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.cons_val, Matrix.tail_cons]
    fin_cases rowIndex <;> fin_cases colIndex <;> norm_num [Matrix.one_apply]

/-- Six coplanar directions plus a pole on the third axis: the `q = 7`
near-pencil. -/
def nearPencilSevenAtom : Fin 7 → Fin 3 → ℝ :=
  ![![2, 0, 0], ![0, 2, 0], ![1, 1, 0], ![1, -1, 0], ![1, 2, 0], ![2, 1, 0], ![0, 0, 2]]

/-- The `q = 7` near-pencil design.  Planar weights `5/64, 5/64, 13/64, 21/64,
1/32, 1/32` total `3/4`, the pole carries `1/4`. -/
noncomputable def nearPencilSevenDesign : WeightedDesign 7 3 where
  atom := nearPencilSevenAtom
  weight := ![5/64, 5/64, 13/64, 21/64, 1/32, 1/32, 1/4]
  weight_pos := by intro label; fin_cases label <;> norm_num
  weight_sum_one := by
    simp only [Fin.sum_univ_seven, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.cons_val, Matrix.tail_cons]
    norm_num
  isParseval := by
    ext rowIndex colIndex
    simp only [Matrix.sum_apply, Matrix.smul_apply, atomMatrix, Matrix.vecMulVec_apply,
      Fin.sum_univ_seven, smul_eq_mul, nearPencilSevenAtom, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.cons_val, Matrix.tail_cons]
    fin_cases rowIndex <;> fin_cases colIndex <;> norm_num [Matrix.one_apply]

/-- **The `q = 6` near-pencil stratum is realized.**  All two hundred and sixteen
label triples are checked: the dependent ones are exactly those avoiding label
`5`, whose bracket is a `3 × 3` determinant with a zero third column; the others
carry the pole and evaluate to twice a nonzero planar cross product. -/
theorem nearPencilSixDesign_hasLinePattern :
    HasLinePattern nearPencilSixDesign (solePoleLinePattern 5) := by
  intro leftLabel midLabel rightLabel hleftMid hleftRight hmidRight
  fin_cases leftLabel <;> fin_cases midLabel <;> fin_cases rightLabel <;>
    simp_all [atomBracket, tripleBracket_eq, nearPencilSixDesign, nearPencilSixAtom,
      solePoleLinePattern, Matrix.cons_val] <;>
    norm_num

/-- **The `q = 7` near-pencil stratum is realized.** -/
theorem nearPencilSevenDesign_hasLinePattern :
    HasLinePattern nearPencilSevenDesign (solePoleLinePattern 6) := by
  intro leftLabel midLabel rightLabel hleftMid hleftRight hmidRight
  fin_cases leftLabel <;> fin_cases midLabel <;> fin_cases rightLabel <;>
    simp_all [atomBracket, tripleBracket_eq, nearPencilSevenDesign, nearPencilSevenAtom,
      solePoleLinePattern, Matrix.cons_val] <;>
    norm_num

/-- **The `q = 6` hinge near-pencil entry, both halves.**  The stratum is
INHABITED by an exact rational design and EMPTY of ties.  The first half rules out
the failure mode where an indexing slip makes `HasLinePattern` unsatisfiable and
the emptiness claim vacuous; the second is `stratumIsTieFree_solePoleLinePattern`. -/
theorem nearPencilSixStratum_isNonempty_and_tieFree :
    HasLinePattern nearPencilSixDesign (solePoleLinePattern 5) ∧
      StratumIsTieFree (solePoleLinePattern (5 : Fin 6)) :=
  ⟨nearPencilSixDesign_hasLinePattern,
    stratumIsTieFree_solePoleLinePattern (by omega) 5 0 1 (by decide) (by decide) (by decide)⟩

/-- **The `q = 7` hinge near-pencil entry, both halves.** -/
theorem nearPencilSevenStratum_isNonempty_and_tieFree :
    HasLinePattern nearPencilSevenDesign (solePoleLinePattern 6) ∧
      StratumIsTieFree (solePoleLinePattern (6 : Fin 7)) :=
  ⟨nearPencilSevenDesign_hasLinePattern,
    stratumIsTieFree_solePoleLinePattern (by omega) 6 0 1 (by decide) (by decide) (by decide)⟩

end Gtz
