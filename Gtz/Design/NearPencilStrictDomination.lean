/-
# Near pencils strictly dominate: the rank-two transport, and two hinge strata closed

`Gtz.Design.PrimitiveTightClassification` names ONE residue for the two
near-pencil entries of the primitive-tight ledger — the classes `q6m3` (a
five-point line among six) and `q7m4` (a six-point line among seven).  Half of
the argument was already landed there: `exists_sharedNormal_of_isPrimitiveDesign`
manufactures the shared normal, `soleOffPlane_share_eq_one` pins the pole's share
at exactly one, and `not_dominates_of_missing_pole` forces every dominating
subset through the pole.  What was missing was the RANK-TWO TRANSPORT: the
planar family, rescaled, is a genuine `WeightedDesign _ 2`, so `Gtz.gtz_rank_two`
supplies a planar pair, and the pole's own axis contributes a separate strictly
positive block.

This file supplies that transport and closes both entries.  It proves NO instance
of `GtzWeighted` at rank three in general and assumes none; every statement is
about designs carrying a shared normal on all but one atom.

## The transport, and where the strictness comes from

Let `poleLabel` be the exceptional atom and `normalVec ≠ 0` a direction
annihilated by every other atom.  Write `poleWeight = D.weight poleLabel` and
`poleShare = 1 − poleWeight` (`= Σ_{c ≠ pole} t_c`).  Then:

* the pole is PARALLEL to `normalVec` and `poleWeight · |g_pole|² = 1`
  (both landed in `PrimitiveTightClassification`), so on the pole's own axis the
  gap of any triple through the pole is already `1/poleWeight − 1 =
  poleShare/poleWeight > 0`;
* compressing along an orthonormal plane frame kills the pole's atom outright, so
  the planar atoms alone resolve the plane's identity with total weight
  `poleShare < 1`.  Reweighting the pole down to `poleWeight/2` and inflating the
  planar weights by `(1 − poleWeight/2)/poleShare` restores a genuine rank-two
  design, at the price of DEFLATING the planar atoms by
  `√(poleShare/(1 − poleWeight/2)) < 1`.  `gtz_rank_two` then produces a pair
  dominating the deflated identity, i.e. dominating
  `(1 − poleWeight/2)/poleShare · I` in the plane — and that factor is
  `> 1`.

The factor is `(1 − poleWeight/2)/(1 − poleWeight)`, i.e. it is BIGGER than one;
the reciprocal direction is the failure mode the residue note warns about.  The
`poleWeight/2` fudge is what keeps the pole's weight positive while leaving room
for a strict inequality — no limit, no compactness, and an explicit constant.

## PROVED here, kernel-checked, unconditional

* `exists_planeFrame_of_ne_zero` — for a nonzero `normalVec` of `ℝ³` a `2 × 3`
  matrix `plane` with orthonormal rows annihilating it, together with the unit
  normal and the RESOLUTION OF THE IDENTITY
  `leftVec ⬝ᵥ rightVec = (unitNormal ⬝ᵥ leftVec)(unitNormal ⬝ᵥ rightVec) +
  (plane *ᵥ leftVec) ⬝ᵥ (plane *ᵥ rightVec)`.  Rides the landed
  `Gtz.exists_orthonormal_completion`.
* `poleDeflation`, `nearPencilPlaneDesign` — the reweighted rank-two view, with
  Parseval discharged through `Gtz.compressedDesign`'s Parseval.
* `notMem_of_dominates_nearPencilPlane` — the planar pair CANNOT contain the pole:
  the pole's compressed atom is zero, so a pair through it leaves a rank-one
  `2 × 2` matrix, and no rank-one matrix dominates the identity of a plane.
* **`exists_posDef_of_soleOffPlane`** — the headline: a design whose atoms all
  but one are orthogonal to a fixed nonzero direction has a triple `{pole, c₁, c₂}`
  with `S_B − I` POSITIVE DEFINITE.  Strictly stronger than tie-freeness: such a
  design satisfies `GtzWeighted`'s conclusion with room to spare.
* `dominates_of_soleOffPlane`, `not_isTie_of_soleOffPlane` — the two readings.
* `nearPencilLinePattern`, `bracketNormal_ne_zero_of_hasNearPencilLinePattern`,
  `sharedNormal_of_hasNearPencilLinePattern` — the entry point from a LINE
  PATTERN rather than a supplied vector.  The normal's nonvanishing comes for
  free: the triple `{first, second, pole}` is NOT in the pattern, so its bracket
  — which is the normal paired against the pole's atom — is nonzero.  No
  primitivity hypothesis is needed anywhere.
* **`stratumIsTieFree_nearPencil`** — the near-pencil stratum is tie-free at
  every size `≥ 3`, for every choice of pole.
* **`stratumIsTieFree_nearPencil_sixThree`** / **`_sevenThree`** — the two hinge
  ledger entries, at the representatives `q6m3` (pole `5`) and `q7m4` (pole `6`).
  With `Gtz.stratumIsTieFree_comp_relabel` these cover the whole isomorphism
  class of each: six labelled strata at size six, seven at size seven.

## CITED, not reproved here

* `Gtz.gtz_rank_two` (`Gtz.Reduction.Reductions`) — weighted GTZ at rank two,
  a complete in-repo proof, not a literature citation.  It is the ONLY nontrivial
  input; everything else here is congruence algebra and one weight bookkeeping.
* `Gtz.soleOffPlane_normal_eq_smul_pole`, `Gtz.soleOffPlane_share_eq_one`
  (`Gtz.Design.PrimitiveTightClassification`) — the Parseval collapse at a near
  pencil.
* `Gtz.exists_orthonormal_completion` (`Gtz.LinAlg.Completion`),
  `Gtz.compressedDesign` (`Gtz.Reduction.Compression`),
  `Gtz.dotProduct_subsetSum_mulVec_of_finset` (`Gtz.Ties.TotalTieCorankOne`).
* `Gtz.LinePattern`, `Gtz.HasLinePattern`, `Gtz.StratumIsTieFree`,
  `Gtz.tripleBracket_eq_bracketNormal_dotProduct`
  (`Gtz.Design.PrimitiveTightClassification`) — the stratum vocabulary.  This
  file does not redefine any of it.

## MEASURED, outside Lean — what the transport does and does not retire

Of the thirty-two primitive isomorphism classes of the hinge (nine at six
points, twenty-three at seven; counts re-derived here by two independent
enumerations of the simple rank-three matroids, `1, 2, 4, 9, 23` at
`q = 3,4,5,6,7`, with labelled totals `352` and `8389` matching the ledger's),
`F₇ = q7m22` was already mechanized and the two near pencils are closed here.
That leaves TWENTY-NINE open, `M(K₄) = q6m8` among them.

The transport is genuinely special to ONE off-plane atom.  With two or more
atoms off the plane the compression no longer kills anything, the planar sum
carries total weight `1` rather than `poleShare`, and the rank-two theorem
returns `⪰ I` with no margin — the strictness is gone, and the pair it returns
may itself sit off the plane, so the gap matrix is no longer block diagonal.
That is why `q7m3` (a five-point line among seven, two atoms off it) is NOT
closed by this file, and why no rescaling of this argument reaches it.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Core.Sanity
import Gtz.LinAlg.Completion
import Gtz.LinAlg.PsdKit
import Gtz.Reduction.Compression
import Gtz.Reduction.Reductions
import Gtz.Certificates.ResidueDissolution
import Gtz.Ties.TotalTieCorankOne
import Gtz.Design.PrimitiveTightClassification

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

variable {m : ℕ}

/-! ## The plane frame

An orthonormal `2 × 3` frame for the orthogonal complement of a nonzero vector,
packaged with the resolution of the identity it induces.  This is
`Gtz.exists_orthonormal_completion` at `(m, k) = (3, 1)` with the single column
taken to be the normalized vector. -/

/-- **A plane frame orthogonal to a nonzero direction.**  The last component is
the resolution of the identity: every dot product splits into its pole-axis part
and its in-plane part. -/
theorem exists_planeFrame_of_ne_zero (normalVec : Fin 3 → ℝ) (hnormalNe : normalVec ≠ 0) :
    ∃ (plane : Matrix (Fin 2) (Fin 3) ℝ) (unitNormal : Fin 3 → ℝ) (unitScale : ℝ),
      plane * planeᵀ = 1 ∧
        unitNormal = unitScale • normalVec ∧ unitScale ≠ 0 ∧
        unitNormal ⬝ᵥ unitNormal = 1 ∧
        plane *ᵥ unitNormal = 0 ∧
        ∀ leftVec rightVec : Fin 3 → ℝ,
          leftVec ⬝ᵥ rightVec
            = (unitNormal ⬝ᵥ leftVec) * (unitNormal ⬝ᵥ rightVec)
              + (plane *ᵥ leftVec) ⬝ᵥ (plane *ᵥ rightVec) := by
  classical
  have hsquareNormPos : 0 < normalVec ⬝ᵥ normalVec := dotProduct_self_pos hnormalNe
  set normalLength : ℝ := Real.sqrt (normalVec ⬝ᵥ normalVec) with hnormalLength
  have hlengthPos : 0 < normalLength := Real.sqrt_pos.mpr hsquareNormPos
  have hlengthNe : normalLength ≠ 0 := hlengthPos.ne'
  have hlengthSquare : normalLength ^ 2 = normalVec ⬝ᵥ normalVec :=
    Real.sq_sqrt hsquareNormPos.le
  set unitNormal : Fin 3 → ℝ := normalLength⁻¹ • normalVec with hunitNormal
  have hunitSquare : unitNormal ⬝ᵥ unitNormal = 1 := by
    rw [hunitNormal, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul,
      ← hlengthSquare]
    field_simp
  set normalColumn : Matrix (Fin 3) (Fin 1) ℝ :=
    Matrix.of (fun coordIndex _ => unitNormal coordIndex) with hnormalColumn
  have hcolumnApply : ∀ vec : Fin 3 → ℝ, (normalColumnᵀ *ᵥ vec) 0 = unitNormal ⬝ᵥ vec := by
    intro vec
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, hnormalColumn,
      Matrix.of_apply]
  have hcolumnOrtho : normalColumnᵀ * normalColumn = 1 := by
    ext leftIndex rightIndex
    fin_cases leftIndex
    fin_cases rightIndex
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, hnormalColumn, Matrix.of_apply,
      Matrix.one_apply_eq, dotProduct] using hunitSquare
  obtain ⟨completion, hcompletionOrtho, hcolumnCompletion, hresolution⟩ :=
    exists_orthonormal_completion normalColumn hcolumnOrtho
  refine ⟨completionᵀ, unitNormal, normalLength⁻¹, ?_, rfl, inv_ne_zero hlengthNe,
    hunitSquare, ?_, ?_⟩
  · rw [Matrix.transpose_transpose]; exact hcompletionOrtho
  · funext planeIndex
    have hentry : (normalColumnᵀ * completion) 0 planeIndex = 0 := by
      rw [hcolumnCompletion]; rfl
    rw [Matrix.mul_apply] at hentry
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Pi.zero_apply]
    rw [← hentry]
    exact Finset.sum_congr rfl fun coordIndex _ => by
      simp only [hnormalColumn, Matrix.transpose_apply, Matrix.of_apply]; ring
  · intro leftVec rightVec
    have hsplit : leftVec ⬝ᵥ ((normalColumn * normalColumnᵀ
          + completion * completionᵀ) *ᵥ rightVec) = leftVec ⬝ᵥ rightVec := by
      rw [hresolution, Matrix.one_mulVec]
    rw [Matrix.add_mulVec, dotProduct_add, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      ← dotProduct_mulVec_transpose normalColumn leftVec (normalColumnᵀ *ᵥ rightVec),
      ← dotProduct_mulVec_transpose completion leftVec (completionᵀ *ᵥ rightVec)] at hsplit
    have hcolumnPair : (normalColumnᵀ *ᵥ leftVec) ⬝ᵥ (normalColumnᵀ *ᵥ rightVec)
        = (unitNormal ⬝ᵥ leftVec) * (unitNormal ⬝ᵥ rightVec) := by
      have hexpand : (normalColumnᵀ *ᵥ leftVec) ⬝ᵥ (normalColumnᵀ *ᵥ rightVec)
          = (normalColumnᵀ *ᵥ leftVec) 0 * (normalColumnᵀ *ᵥ rightVec) 0 := by
        simp only [dotProduct, Fin.sum_univ_one]
      rw [hexpand, hcolumnApply, hcolumnApply]
    rw [← hsplit, hcolumnPair]

/-! ## The reweighted rank-two view

Compression along the plane frame sends the pole's atom to zero, so the planar
atoms alone resolve the plane's identity while carrying total weight
`poleShare < 1`.  Restoring a genuine rank-two design costs a deflation of the
planar atoms, and that deflation is exactly the margin the strictness needs. -/

/-- The planar deflation factor `(1 − t_pole)/(1 − t_pole/2)`, strictly between
zero and one whenever `0 < t_pole < 1`. -/
noncomputable def poleDeflation (D : WeightedDesign m 3) (poleLabel : Fin m) : ℝ :=
  (1 - D.weight poleLabel) / (1 - D.weight poleLabel / 2)

/-- The deflation is positive. -/
theorem poleDeflation_pos (hsize : 2 ≤ m) (D : WeightedDesign m 3) (poleLabel : Fin m) :
    0 < poleDeflation D poleLabel := by
  have hupper := weight_lt_one D hsize poleLabel
  have hlower := D.weight_pos poleLabel
  exact div_pos (by linarith) (by linarith)

/-- The deflation is strictly below one — this is the whole margin. -/
theorem poleDeflation_lt_one (hsize : 2 ≤ m) (D : WeightedDesign m 3) (poleLabel : Fin m) :
    poleDeflation D poleLabel < 1 := by
  have hupper := weight_lt_one D hsize poleLabel
  have hlower := D.weight_pos poleLabel
  rw [poleDeflation, div_lt_one (by linarith)]
  linarith

/-- The deflation clears its own denominator: `deflation · (1 − t/2) = 1 − t`.
This is the only property of `poleDeflation` the strict estimate consumes. -/
theorem poleDeflation_mul_half (hsize : 2 ≤ m) (D : WeightedDesign m 3) (poleLabel : Fin m) :
    poleDeflation D poleLabel * (1 - D.weight poleLabel / 2) = 1 - D.weight poleLabel := by
  have hupper := weight_lt_one D hsize poleLabel
  have hlower := D.weight_pos poleLabel
  have hhalfNe : (1 : ℝ) - D.weight poleLabel / 2 ≠ 0 := by intro hzero; linarith
  have htwoNe : (2 : ℝ) - D.weight poleLabel ≠ 0 := by intro hzero; linarith
  rw [poleDeflation]
  field_simp

/-- **The reweighted rank-two view of a near pencil.**  The pole keeps half its
weight, every other atom's weight is inflated to restore the simplex, and all the
compressed atoms are deflated by `√(poleDeflation)` to restore Parseval. -/
noncomputable def nearPencilPlaneDesign (hsize : 2 ≤ m) (D : WeightedDesign m 3)
    (poleLabel : Fin m) (plane : Matrix (Fin 2) (Fin 3) ℝ)
    (hplaneOrtho : plane * planeᵀ = 1)
    (hpoleKilled : plane *ᵥ D.atom poleLabel = 0) : WeightedDesign m 2 where
  atom := fun label =>
    Real.sqrt (poleDeflation D poleLabel) • (plane *ᵥ D.atom label)
  weight := fun label =>
    if label = poleLabel then D.weight poleLabel / 2
    else D.weight label * (1 - D.weight poleLabel / 2) / (1 - D.weight poleLabel)
  weight_pos := by
    intro label
    have hupper := weight_lt_one D hsize poleLabel
    have hlower := D.weight_pos poleLabel
    by_cases hpole : label = poleLabel
    · rw [if_pos hpole]; linarith
    · rw [if_neg hpole]
      exact div_pos (mul_pos (D.weight_pos label) (by linarith)) (by linarith)
  weight_sum_one := by
    have hupper := weight_lt_one D hsize poleLabel
    have hlower := D.weight_pos poleLabel
    have hshareNe : (1 : ℝ) - D.weight poleLabel ≠ 0 := by intro hzero; linarith
    have hcomplement : ∑ label ∈ Finset.univ.erase poleLabel, D.weight label
        = 1 - D.weight poleLabel := by
      have hsplit := Finset.sum_erase_add Finset.univ D.weight (Finset.mem_univ poleLabel)
      rw [D.weight_sum_one] at hsplit
      linarith
    have hsplit := Finset.sum_erase_add Finset.univ
      (fun label => if label = poleLabel then D.weight poleLabel / 2
        else D.weight label * (1 - D.weight poleLabel / 2) / (1 - D.weight poleLabel))
      (Finset.mem_univ poleLabel)
    rw [← hsplit, if_pos rfl]
    have hrewrite : ∑ label ∈ Finset.univ.erase poleLabel,
          (if label = poleLabel then D.weight poleLabel / 2
            else D.weight label * (1 - D.weight poleLabel / 2) / (1 - D.weight poleLabel))
        = ((1 - D.weight poleLabel / 2) / (1 - D.weight poleLabel))
          * ∑ label ∈ Finset.univ.erase poleLabel, D.weight label := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun label hlabel => ?_
      rw [if_neg (Finset.mem_erase.mp hlabel).1]
      ring
    have hcancel : (1 - D.weight poleLabel / 2) / (1 - D.weight poleLabel)
        * (1 - D.weight poleLabel) = 1 - D.weight poleLabel / 2 := by
      field_simp
    rw [hrewrite, hcomplement, hcancel]
    ring
  isParseval := by
    have hupper := weight_lt_one D hsize poleLabel
    have hlower := D.weight_pos poleLabel
    have hshareNe : (1 : ℝ) - D.weight poleLabel ≠ 0 := by intro hzero; linarith
    have hhalfNe : (1 : ℝ) - D.weight poleLabel / 2 ≠ 0 := by intro hzero; linarith
    have htwoNe : (2 : ℝ) - D.weight poleLabel ≠ 0 := by intro hzero; linarith
    have hdeflationSq : Real.sqrt (poleDeflation D poleLabel) ^ 2
        = poleDeflation D poleLabel :=
      Real.sq_sqrt (poleDeflation_pos hsize D poleLabel).le
    have hplanarParseval : ∑ label, D.weight label • atomMatrix (plane *ᵥ D.atom label)
        = 1 := (compressedDesign D plane hplaneOrtho).isParseval
    have hpoleTermZero : atomMatrix (plane *ᵥ D.atom poleLabel)
        = (0 : Matrix (Fin 2) (Fin 2) ℝ) := by
      rw [hpoleKilled, atomMatrix]
      ext leftIndex rightIndex
      simp only [Matrix.vecMulVec_apply, Pi.zero_apply, Matrix.zero_apply, mul_zero]
    have hplanarComplement : ∑ label ∈ Finset.univ.erase poleLabel,
          D.weight label • atomMatrix (plane *ᵥ D.atom label) = 1 := by
      have hsplit := Finset.sum_erase_add Finset.univ
        (fun label => D.weight label • atomMatrix (plane *ᵥ D.atom label))
        (Finset.mem_univ poleLabel)
      rw [hplanarParseval, hpoleTermZero, smul_zero, add_zero] at hsplit
      exact hsplit
    have hsplit := Finset.sum_erase_add Finset.univ
      (fun label =>
        (if label = poleLabel then D.weight poleLabel / 2
          else D.weight label * (1 - D.weight poleLabel / 2) / (1 - D.weight poleLabel))
        • atomMatrix (Real.sqrt (poleDeflation D poleLabel) • (plane *ᵥ D.atom label)))
      (Finset.mem_univ poleLabel)
    rw [← hsplit]
    have hpoleVanishes : (D.weight poleLabel / 2)
        • atomMatrix (Real.sqrt (poleDeflation D poleLabel) • (plane *ᵥ D.atom poleLabel))
        = 0 := by
      rw [atomMatrix_smul, hpoleTermZero, smul_zero, smul_zero]
    rw [if_pos rfl, hpoleVanishes, add_zero]
    have hrewrite : ∑ label ∈ Finset.univ.erase poleLabel,
          (if label = poleLabel then D.weight poleLabel / 2
            else D.weight label * (1 - D.weight poleLabel / 2) / (1 - D.weight poleLabel))
          • atomMatrix (Real.sqrt (poleDeflation D poleLabel) • (plane *ᵥ D.atom label))
        = ((poleDeflation D poleLabel)
            * ((1 - D.weight poleLabel / 2) / (1 - D.weight poleLabel)))
          • ∑ label ∈ Finset.univ.erase poleLabel,
              D.weight label • atomMatrix (plane *ᵥ D.atom label) := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun label hlabel => ?_
      rw [if_neg (Finset.mem_erase.mp hlabel).1, atomMatrix_smul, hdeflationSq,
        smul_smul, smul_smul]
      congr 1
      ring
    have hscalarOne : poleDeflation D poleLabel
        * ((1 - D.weight poleLabel / 2) / (1 - D.weight poleLabel)) = 1 := by
      rw [poleDeflation]
      field_simp
    rw [hrewrite, hplanarComplement, hscalarOne, one_smul]

@[simp] theorem nearPencilPlaneDesign_atom (hsize : 2 ≤ m) (D : WeightedDesign m 3)
    (poleLabel : Fin m) (plane : Matrix (Fin 2) (Fin 3) ℝ)
    (hplaneOrtho : plane * planeᵀ = 1)
    (hpoleKilled : plane *ᵥ D.atom poleLabel = 0) (label : Fin m) :
    (nearPencilPlaneDesign hsize D poleLabel plane hplaneOrtho hpoleKilled).atom label
      = Real.sqrt (poleDeflation D poleLabel) • (plane *ᵥ D.atom label) := rfl

/-! ## The planar pair avoids the pole

The pole's compressed atom is zero, so a dominating PAIR containing the pole
would leave a single rank-one `2 × 2` matrix dominating the plane's identity —
impossible, because a rank-one matrix vanishes on a whole line. -/

/-- **No rank-one matrix dominates a plane's identity.**  Both probes are
explicit: the rotation of the atom kills the quadratic form, and the first basis
vector then rules out the zero atom. -/
theorem not_posSemidef_atomMatrix_sub_one (vec : Fin 2 → ℝ) :
    ¬ (atomMatrix vec - 1).PosSemidef := by
  intro hpsd
  have hquad : ∀ probe : Fin 2 → ℝ,
      0 ≤ (vec ⬝ᵥ probe) ^ 2 - probe ⬝ᵥ probe := by
    intro probe
    have hform := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hpsd).2 probe
    rw [star_trivial, Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec,
      dotProduct_atomMatrix_mulVec] at hform
    exact hform
  have hdotRotated : vec ⬝ᵥ (![-(vec 1), vec 0] : Fin 2 → ℝ) = 0 := by
    simp only [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  have hnormRotated : (![-(vec 1), vec 0] : Fin 2 → ℝ) ⬝ᵥ ![-(vec 1), vec 0]
      = vec 0 ^ 2 + vec 1 ^ 2 := by
    simp only [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  have hrotated := hquad ![-(vec 1), vec 0]
  rw [hdotRotated, hnormRotated] at hrotated
  have hvanishFirst : vec 0 ^ 2 = 0 := by
    nlinarith [sq_nonneg (vec 0), sq_nonneg (vec 1)]
  have hdotBasis : vec ⬝ᵥ (![1, 0] : Fin 2 → ℝ) = vec 0 := by
    simp only [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  have hnormBasis : (![1, 0] : Fin 2 → ℝ) ⬝ᵥ ![1, 0] = 1 := by
    simp only [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  have hbasis := hquad ![1, 0]
  rw [hdotBasis, hnormBasis] at hbasis
  linarith [hbasis, hvanishFirst]

/-- **The planar pair avoids the pole.** -/
theorem notMem_of_dominates_nearPencilPlane (hsize : 2 ≤ m) (D : WeightedDesign m 3)
    (poleLabel : Fin m) (plane : Matrix (Fin 2) (Fin 3) ℝ)
    (hplaneOrtho : plane * planeᵀ = 1)
    (hpoleKilled : plane *ᵥ D.atom poleLabel = 0)
    (pair : Finset (Fin m)) (hcard : pair.card = 2)
    (hdominates : Dominates
      (nearPencilPlaneDesign hsize D poleLabel plane hplaneOrtho hpoleKilled) pair) :
    poleLabel ∉ pair := by
  classical
  intro hmem
  have hpoleAtomZero :
      (nearPencilPlaneDesign hsize D poleLabel plane hplaneOrtho hpoleKilled).atom poleLabel
        = 0 := by
    rw [nearPencilPlaneDesign_atom, hpoleKilled, smul_zero]
  have hrest : (pair.erase poleLabel).card = 1 := by
    rw [Finset.card_erase_of_mem hmem, hcard]
  obtain ⟨otherLabel, hother⟩ := Finset.card_eq_one.mp hrest
  have hnotMem : poleLabel ∉ ({otherLabel} : Finset (Fin m)) := by
    rw [← hother]; exact Finset.notMem_erase _ _
  have hpairEq : pair = insert poleLabel {otherLabel} := by
    rw [← hother, Finset.insert_erase hmem]
  have hsubsetSum :
      subsetSum (nearPencilPlaneDesign hsize D poleLabel plane hplaneOrtho hpoleKilled) pair
        = atomMatrix
            ((nearPencilPlaneDesign hsize D poleLabel plane hplaneOrtho hpoleKilled).atom
              otherLabel) := by
    rw [hpairEq, subsetSum, Finset.sum_insert hnotMem, Finset.sum_singleton,
      hpoleAtomZero, atomMatrix]
    ext leftIndex rightIndex
    simp only [Matrix.add_apply, Matrix.vecMulVec_apply, Pi.zero_apply, mul_zero, zero_add]
  rw [Dominates, hsubsetSum] at hdominates
  exact not_posSemidef_atomMatrix_sub_one _ hdominates

/-! ## The two-block strict estimate, as arithmetic

Everything analytic is over by the time this lemma is reached: the pole's axis
carries `axisSquare = t_pole · poleSquare`, the plane carries
`planeSquare ≤ deflation · planarSum`, and `deflation · (1 − t_pole/2) =
1 − t_pole`.  The identity below splits the gap into `2(1 − t)² · axisSquare`
plus `t² · planeSquare` plus a nonnegative remainder, so a nonzero probe forces
it strictly positive. -/

/-- **The two-block estimate.**  With the pole's share pinned and the plane
dominating a deflated identity, the gap form is strictly positive. -/
theorem posDef_estimate_of_nearPencilBlocks
    {poleWeight deflation poleSquare axisSquare planeSquare planarSum : ℝ}
    (hweightPos : 0 < poleWeight) (hweightLtOne : poleWeight < 1)
    (hdeflationEq : deflation * (1 - poleWeight / 2) = 1 - poleWeight)
    (hpoleBlock : poleWeight * poleSquare = axisSquare)
    (haxisNonneg : 0 ≤ axisSquare) (hplaneNonneg : 0 ≤ planeSquare)
    (hprobePos : 0 < axisSquare + planeSquare)
    (hplaneBound : planeSquare ≤ deflation * planarSum) :
    0 < poleSquare + planarSum - (axisSquare + planeSquare) := by
  have hsharePos : (0 : ℝ) < 1 - poleWeight := by linarith
  have hdeflationScaled : (2 - poleWeight) * deflation = 2 - 2 * poleWeight := by
    linear_combination 2 * hdeflationEq
  have hplaneScaled : (2 - poleWeight) * planeSquare
      ≤ (2 - 2 * poleWeight) * planarSum := by
    have hfactorNonneg : (0 : ℝ) ≤ 2 - poleWeight := by linarith
    calc (2 - poleWeight) * planeSquare
        ≤ (2 - poleWeight) * (deflation * planarSum) :=
          mul_le_mul_of_nonneg_left hplaneBound hfactorNonneg
      _ = (2 - 2 * poleWeight) * planarSum := by rw [← mul_assoc, hdeflationScaled]
  have hmarginNonneg : 0 ≤ (2 - 2 * poleWeight) * planarSum
      - (2 - poleWeight) * planeSquare := by linarith [hplaneScaled]
  have hblocks : 2 * poleWeight * (1 - poleWeight)
        * (poleSquare + planarSum - (axisSquare + planeSquare))
      = 2 * (1 - poleWeight) ^ 2 * axisSquare
        + poleWeight * ((2 - 2 * poleWeight) * planarSum - (2 - poleWeight) * planeSquare)
        + poleWeight ^ 2 * planeSquare := by
    linear_combination (2 * (1 - poleWeight)) * hpoleBlock
  have hcoeffAxisPos : 0 < 2 * (1 - poleWeight) ^ 2 := by
    have hsquarePos := pow_pos hsharePos 2
    linarith
  have hcoeffPlanePos : 0 < poleWeight ^ 2 := pow_pos hweightPos 2
  have hmiddleNonneg : 0 ≤ poleWeight
      * ((2 - 2 * poleWeight) * planarSum - (2 - poleWeight) * planeSquare) :=
    mul_nonneg hweightPos.le hmarginNonneg
  have hpositivePart : 0 < 2 * (1 - poleWeight) ^ 2 * axisSquare
      + poleWeight * ((2 - 2 * poleWeight) * planarSum - (2 - poleWeight) * planeSquare)
      + poleWeight ^ 2 * planeSquare := by
    rcases lt_or_ge 0 axisSquare with haxisPos | haxisLe
    · have hfirstPos : 0 < 2 * (1 - poleWeight) ^ 2 * axisSquare :=
        mul_pos hcoeffAxisPos haxisPos
      have hlastNonneg : 0 ≤ poleWeight ^ 2 * planeSquare :=
        mul_nonneg hcoeffPlanePos.le hplaneNonneg
      linarith
    · have haxisZero : axisSquare = 0 := le_antisymm haxisLe haxisNonneg
      have hplanePos : 0 < planeSquare := by
        rw [haxisZero] at hprobePos; linarith
      have hfirstZero : 2 * (1 - poleWeight) ^ 2 * axisSquare = 0 := by
        rw [haxisZero, mul_zero]
      have hlastPos : 0 < poleWeight ^ 2 * planeSquare := mul_pos hcoeffPlanePos hplanePos
      linarith
  have hfactorPos : 0 < 2 * poleWeight * (1 - poleWeight) := by
    have hproduct := mul_pos hweightPos hsharePos
    linarith
  rcases le_or_gt (poleSquare + planarSum - (axisSquare + planeSquare)) 0 with hle | hpos
  · exfalso
    have hproduct : 2 * poleWeight * (1 - poleWeight)
        * (poleSquare + planarSum - (axisSquare + planeSquare)) ≤ 0 := by
      nlinarith [hfactorPos, hle]
    rw [hblocks] at hproduct
    linarith
  · exact hpos

/-! ## The headline: a near pencil strictly dominates -/

/-- **A near pencil strictly dominates.**  If every atom but one is orthogonal to
a fixed nonzero direction, some triple through the exceptional atom has a
POSITIVE DEFINITE gap matrix.  The two blocks are independent: the pole's axis
contributes `(1 − t_pole)/t_pole > 0`, the plane contributes
`t_pole/(2 (1 − t_pole)) > 0`. -/
theorem exists_posDef_of_soleOffPlane (hsize : 2 ≤ m) (D : WeightedDesign m 3)
    (poleLabel : Fin m) {normalVec : Fin 3 → ℝ} (hnormalNe : normalVec ≠ 0)
    (hplanar : ∀ label, label ≠ poleLabel → D.atom label ⬝ᵥ normalVec = 0) :
    ∃ B : Finset (Fin m), B.card = 3 ∧ (subsetSum D B - 1).PosDef := by
  classical
  have hpoleWeightPos := D.weight_pos poleLabel
  have hpoleWeightLtOne := weight_lt_one D hsize poleLabel
  obtain ⟨plane, unitNormal, unitScale, hplaneOrtho, hunitEq, hscaleNe, hunitSquare,
    hplaneKillsUnit, hresolution⟩ := exists_planeFrame_of_ne_zero normalVec hnormalNe
  -- the pole is parallel to the normal, and its share is exactly one
  obtain ⟨mixedTerm, hmixedNe, hnormalEq⟩ :
      ∃ coeff : ℝ, coeff ≠ 0 ∧ normalVec = coeff • D.atom poleLabel := by
    refine ⟨D.weight poleLabel * (D.atom poleLabel ⬝ᵥ normalVec), ?_,
      soleOffPlane_normal_eq_smul_pole D poleLabel hplanar⟩
    intro hzero
    have hcollapse := soleOffPlane_normal_eq_smul_pole D poleLabel hplanar
    rw [hzero, zero_smul] at hcollapse
    exact hnormalNe hcollapse
  obtain ⟨poleCoeff, hpoleAtomEq⟩ :
      ∃ coeff : ℝ, D.atom poleLabel = coeff • unitNormal := by
    refine ⟨mixedTerm⁻¹ * unitScale⁻¹, ?_⟩
    rw [hunitEq, smul_smul, mul_assoc, inv_mul_cancel₀ hscaleNe, mul_one, hnormalEq,
      smul_smul, inv_mul_cancel₀ hmixedNe, one_smul]
  have hpoleShareOne : D.weight poleLabel * poleCoeff ^ 2 = 1 := by
    have hshare := soleOffPlane_share_eq_one D poleLabel hnormalNe hplanar
    have hleverage : leverageOf (D.atom poleLabel) = poleCoeff ^ 2 := by
      have hdot : D.atom poleLabel ⬝ᵥ D.atom poleLabel = poleCoeff ^ 2 := by
        rw [hpoleAtomEq, smul_dotProduct, dotProduct_smul, hunitSquare, smul_eq_mul,
          smul_eq_mul, mul_one, pow_two]
      rw [← hdot]
      simp only [dotProduct, leverageOf, pow_two]
    rwa [hleverage] at hshare
  have hpoleKilled : plane *ᵥ D.atom poleLabel = 0 := by
    rw [hpoleAtomEq, Matrix.mulVec_smul, hplaneKillsUnit, smul_zero]
  -- the rank-two view and the pair it produces
  obtain ⟨pair, hpairCard, hpairDominates⟩ := gtz_rank_two m
    (nearPencilPlaneDesign hsize D poleLabel plane hplaneOrtho hpoleKilled)
  have hpoleNotMem : poleLabel ∉ pair :=
    notMem_of_dominates_nearPencilPlane hsize D poleLabel plane hplaneOrtho hpoleKilled
      pair hpairCard hpairDominates
  refine ⟨insert poleLabel pair, ?_, ?_⟩
  · rw [Finset.card_insert_of_notMem hpoleNotMem, hpairCard]
  have hdeflationPos := poleDeflation_pos hsize D poleLabel
  have hdeflationSq : Real.sqrt (poleDeflation D poleLabel) ^ 2 = poleDeflation D poleLabel :=
    Real.sq_sqrt hdeflationPos.le
  have hplanarTransfer : ∀ probe : Fin 2 → ℝ,
      probe ⬝ᵥ probe
        ≤ poleDeflation D poleLabel
          * ∑ label ∈ pair, ((plane *ᵥ D.atom label) ⬝ᵥ probe) ^ 2 := by
    intro probe
    have hform := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hpairDominates).2 probe
    rw [star_trivial, Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec,
      dotProduct_subsetSum_mulVec_of_finset] at hform
    have hrewrite : ∑ label ∈ pair,
          ((nearPencilPlaneDesign hsize D poleLabel plane hplaneOrtho hpoleKilled).atom label
            ⬝ᵥ probe) ^ 2
        = poleDeflation D poleLabel
          * ∑ label ∈ pair, ((plane *ᵥ D.atom label) ⬝ᵥ probe) ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun label _ => ?_
      rw [nearPencilPlaneDesign_atom, smul_dotProduct, smul_eq_mul, mul_pow, hdeflationSq]
    rw [hrewrite] at hform
    linarith
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨?_, fun probe hprobeNe => ?_⟩
  · refine isHermitian_of_transpose_eq ?_
    rw [Matrix.transpose_sub, Matrix.transpose_one, subsetSum, Matrix.transpose_sum]
    congr 1
    exact Finset.sum_congr rfl fun label _ => by
      rw [atomMatrix, Matrix.transpose_vecMulVec]
  · have hprobeSplit : probe ⬝ᵥ probe
        = (unitNormal ⬝ᵥ probe) ^ 2 + (plane *ᵥ probe) ⬝ᵥ (plane *ᵥ probe) := by
      rw [hresolution probe probe, pow_two]
    have hpoleBlock : D.weight poleLabel * (D.atom poleLabel ⬝ᵥ probe) ^ 2
        = (unitNormal ⬝ᵥ probe) ^ 2 := by
      rw [hpoleAtomEq, smul_dotProduct, smul_eq_mul, mul_pow]
      linear_combination ((unitNormal ⬝ᵥ probe) ^ 2) * hpoleShareOne
    have hplanarTerms : ∑ label ∈ pair, (D.atom label ⬝ᵥ probe) ^ 2
        = ∑ label ∈ pair, ((plane *ᵥ D.atom label) ⬝ᵥ (plane *ᵥ probe)) ^ 2 := by
      refine Finset.sum_congr rfl fun label hlabel => ?_
      have hlabelNe : label ≠ poleLabel := fun hequal => hpoleNotMem (hequal ▸ hlabel)
      have haxisVanishes : unitNormal ⬝ᵥ D.atom label = 0 := by
        rw [hunitEq, smul_dotProduct, smul_eq_mul, dotProduct_comm normalVec (D.atom label),
          hplanar label hlabelNe, mul_zero]
      rw [hresolution (D.atom label) probe, haxisVanishes, zero_mul, zero_add]
    have hplaneBound : (plane *ᵥ probe) ⬝ᵥ (plane *ᵥ probe)
        ≤ poleDeflation D poleLabel * ∑ label ∈ pair, (D.atom label ⬝ᵥ probe) ^ 2 := by
      rw [hplanarTerms]
      exact hplanarTransfer (plane *ᵥ probe)
    rw [star_trivial, Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec,
      dotProduct_subsetSum_mulVec_of_finset, Finset.sum_insert hpoleNotMem, hprobeSplit]
    exact posDef_estimate_of_nearPencilBlocks hpoleWeightPos hpoleWeightLtOne
      (poleDeflation_mul_half hsize D poleLabel) hpoleBlock (sq_nonneg _)
      (dotProduct_self_nonneg _)
      (by rw [← hprobeSplit]; exact dotProduct_self_pos hprobeNe) hplaneBound

/-- **A near pencil dominates.**  The weak reading of the headline. -/
theorem dominates_of_soleOffPlane (hsize : 2 ≤ m) (D : WeightedDesign m 3)
    (poleLabel : Fin m) {normalVec : Fin 3 → ℝ} (hnormalNe : normalVec ≠ 0)
    (hplanar : ∀ label, label ≠ poleLabel → D.atom label ⬝ᵥ normalVec = 0) :
    ∃ B : Finset (Fin m), B.card = 3 ∧ Dominates D B := by
  obtain ⟨B, hcard, hposDef⟩ :=
    exists_posDef_of_soleOffPlane hsize D poleLabel hnormalNe hplanar
  exact ⟨B, hcard, hposDef.posSemidef⟩

/-- **A near pencil is not a tie.**  Some triple dominates STRICTLY, which the
second clause of `IsTie` forbids. -/
theorem not_isTie_of_soleOffPlane (hsize : 2 ≤ m) (D : WeightedDesign m 3)
    (poleLabel : Fin m) {normalVec : Fin 3 → ℝ} (hnormalNe : normalVec ≠ 0)
    (hplanar : ∀ label, label ≠ poleLabel → D.atom label ⬝ᵥ normalVec = 0) :
    ¬ IsTie D := by
  intro htie
  obtain ⟨B, hcard, hposDef⟩ :=
    exists_posDef_of_soleOffPlane hsize D poleLabel hnormalNe hplanar
  exact htie.2 B hcard hposDef
/-! ## Entering from a line pattern

The near-pencil stratum is the pattern whose dependent triples are exactly those
AVOIDING one designated label.  Its normal comes out of the pattern for free:
the triple `{first, second, pole}` is not dependent, and that bracket IS the
normal paired against the pole's atom. -/

/-- The near pencil with a designated pole: a triple of distinct labels is
dependent exactly when it avoids the pole.  Manifestly slot-symmetric. -/
def nearPencilLinePattern {size : ℕ} (poleLabel : Fin size) : LinePattern size :=
  fun leftLabel midLabel rightLabel =>
    leftLabel ≠ poleLabel ∧ midLabel ≠ poleLabel ∧ rightLabel ≠ poleLabel

/-- **The near pencil's normal is nonzero, from the pattern alone.**  The bracket
of `{first, second, pole}` does not vanish because that triple meets the pole; and
that bracket is the normal paired against the pole's atom. -/
theorem bracketNormal_ne_zero_of_hasNearPencilLinePattern {size : ℕ} (poleLabel : Fin size)
    (D : WeightedDesign size 3) (hpattern : HasLinePattern D (nearPencilLinePattern poleLabel))
    (firstLabel secondLabel : Fin size) (hdistinct : firstLabel ≠ secondLabel)
    (hfirstNe : firstLabel ≠ poleLabel) (hsecondNe : secondLabel ≠ poleLabel) :
    bracketNormal (D.atom firstLabel) (D.atom secondLabel) ≠ 0 := by
  intro hnormalZero
  have hbracketZero : atomBracket D firstLabel secondLabel poleLabel = 0 := by
    rw [atomBracket, tripleBracket_eq_bracketNormal_dotProduct, hnormalZero, zero_dotProduct]
  have hdependent := (hpattern firstLabel secondLabel poleLabel hdistinct hfirstNe
    hsecondNe).mp hbracketZero
  exact hdependent.2.2 rfl

/-- **The shared normal of a near pencil, from the pattern alone.**  Every atom
but the pole is orthogonal to one fixed nonzero direction. -/
theorem sharedNormal_of_hasNearPencilLinePattern {size : ℕ} (poleLabel : Fin size)
    (D : WeightedDesign size 3) (hpattern : HasLinePattern D (nearPencilLinePattern poleLabel))
    (firstLabel secondLabel : Fin size) (hdistinct : firstLabel ≠ secondLabel)
    (hfirstNe : firstLabel ≠ poleLabel) (hsecondNe : secondLabel ≠ poleLabel) :
    ∃ normalVec : Fin 3 → ℝ, normalVec ≠ 0 ∧
      ∀ label, label ≠ poleLabel → D.atom label ⬝ᵥ normalVec = 0 := by
  refine ⟨bracketNormal (D.atom firstLabel) (D.atom secondLabel),
    bracketNormal_ne_zero_of_hasNearPencilLinePattern poleLabel D hpattern firstLabel
      secondLabel hdistinct hfirstNe hsecondNe, fun label hlabelNe => ?_⟩
  rw [dotProduct_comm, ← tripleBracket_eq_bracketNormal_dotProduct]
  by_cases hfirst : label = firstLabel
  · rw [hfirst]
    simp only [tripleBracket_eq]; ring
  · by_cases hsecond : label = secondLabel
    · rw [hsecond]
      simp only [tripleBracket_eq]; ring
    · exact (hpattern firstLabel secondLabel label hdistinct
        (fun hequal => hfirst hequal.symm) (fun hequal => hsecond hequal.symm)).mpr
        ⟨hfirstNe, hsecondNe, hlabelNe⟩

/-- **The near-pencil stratum is tie-free**, at every size `≥ 3` and every pole.
No primitivity hypothesis: the pattern itself supplies the nonvanishing normal. -/
theorem stratumIsTieFree_nearPencil {size : ℕ} (hsize : 3 ≤ size) (poleLabel : Fin size) :
    StratumIsTieFree (nearPencilLinePattern poleLabel) := by
  classical
  intro D hpattern htie
  have hcompl : 1 < ({poleLabel}ᶜ : Finset (Fin size)).card := by
    rw [Finset.card_compl, Finset.card_singleton, Fintype.card_fin]
    omega
  obtain ⟨firstLabel, hfirstMem, secondLabel, hsecondMem, hdistinct⟩ :=
    Finset.one_lt_card.mp hcompl
  have hfirstNe : firstLabel ≠ poleLabel := by
    simpa only [Finset.mem_compl, Finset.mem_singleton] using hfirstMem
  have hsecondNe : secondLabel ≠ poleLabel := by
    simpa only [Finset.mem_compl, Finset.mem_singleton] using hsecondMem
  obtain ⟨normalVec, hnormalNe, hplanar⟩ :=
    sharedNormal_of_hasNearPencilLinePattern poleLabel D hpattern firstLabel secondLabel
      hdistinct hfirstNe hsecondNe
  exact not_isTie_of_soleOffPlane (by omega) D poleLabel hnormalNe hplanar htie

/-! ## The two hinge ledger entries

`q6m3` is the five-point line among six points, `q7m4` the six-point line among
seven; in both the pole is the last label.  `Gtz.stratumIsTieFree_comp_relabel`
extends each to its whole isomorphism class — six labelled strata at size six,
seven at size seven. -/

/-- **Ledger entry `q6m3`**: the near pencil at six points is tie-free. -/
theorem stratumIsTieFree_nearPencil_sixThree :
    StratumIsTieFree (nearPencilLinePattern (5 : Fin 6)) :=
  stratumIsTieFree_nearPencil (by omega) _

/-- **Ledger entry `q7m4`**: the near pencil at seven points is tie-free. -/
theorem stratumIsTieFree_nearPencil_sevenThree :
    StratumIsTieFree (nearPencilLinePattern (6 : Fin 7)) :=
  stratumIsTieFree_nearPencil (by omega) _

/-- **Both near-pencil classes, whole isomorphism class each.**  Any relabelling
of either representative is tie-free too. -/
theorem stratumIsTieFree_nearPencil_relabelled_sixThree (relabel : Equiv.Perm (Fin 6)) :
    StratumIsTieFree (fun leftLabel midLabel rightLabel =>
      nearPencilLinePattern (5 : Fin 6) (relabel leftLabel) (relabel midLabel)
        (relabel rightLabel)) :=
  stratumIsTieFree_comp_relabel _ relabel stratumIsTieFree_nearPencil_sixThree

/-- The size-seven half of the same statement. -/
theorem stratumIsTieFree_nearPencil_relabelled_sevenThree (relabel : Equiv.Perm (Fin 7)) :
    StratumIsTieFree (fun leftLabel midLabel rightLabel =>
      nearPencilLinePattern (6 : Fin 7) (relabel leftLabel) (relabel midLabel)
        (relabel rightLabel)) :=
  stratumIsTieFree_comp_relabel _ relabel stratumIsTieFree_nearPencil_sevenThree

end Gtz
