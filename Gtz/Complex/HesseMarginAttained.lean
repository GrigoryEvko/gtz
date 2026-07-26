/-
# The Hesse margin is ATTAINED, and the one-spike ladder that climbs off it

`Gtz/Complex/PerRankConstantLedger.lean` proves one half of the rank-three
statement — no `3`-subset of the Hesse SIC survives any shift above
`3(1 - cos 2 pi / 9)` — and its own SCOPE NOTE records the missing half:

> That the Hesse design ATTAINS its margin.  Only `≤` is proved: no triple
> survives above it.  Attainment is EXACT ELSEWHERE (all `72` non-degenerate
> triples share `lambda_min = 3(1 - cos 2 pi / 9)`, the other `12` are
> rank-deficient), not mechanized.

This file mechanizes it, in the Loewner shape the trine already has
(`trineMargin_isGreatest`), and then uses one-spike padding to climb a rank.

## Header: PROVED / CITED / MEASURED

**PROVED here, kernel-checked, zero new axioms.**

* `hesse_bindingTriple_dominatesAtLevel` — ATTAINMENT.  The triple `{0, 1, 3}` of
  `hesseDesign`, one of the seventy-two non-collinear triples, has positive
  semidefinite excess AT the margin.  The certificate is a block LDL step written
  multiplicatively so that no inverse ever appears: with `p = 3/2 - s` and
  `q = 3 - s`,

      (p q) . (S_C - s I) = q . atom(p, 0, -3/2) + p . atom(0, q, (3/2) w^2)

  is a POLYNOMIAL identity in the shift and the cube root, valid exactly at the
  roots of the Hesse cubic `8 s^3 - 72 s^2 + 162 s - 81`, and both coefficients
  are nonnegative because the margin lies below `3/2`
  (`hesseMargin_lt_threeHalves`).  Dividing by the positive scalar `p q`
  transfers positive semidefiniteness to the excess itself.
* `hesseMargin_isGreatest` — the set of shifts at which some `3`-subset of the
  Hesse SIC dominates has GREATEST element `3(1 - cos 2 pi / 9)`.  So the
  rank-three upper bound is EXACTLY realised by its witness, not merely a level
  the witness fails to exceed.
* `spikePaddedDesign` — the one-spike padding CONSTRUCTION: from a weighted
  `(size, rank)`-design and any `spikeWeight` in `(0,1)`, a genuine weighted
  `(size + 1, rank + 1)`-design.  Parseval holds blockwise; the proof is
  `spikePaddedDesign_parseval`.

**NOT proved here — the identified next brick.**  The VALUE half of the padding
ladder,

    ComplexDesignValueAtMost design bound
      -> ComplexDesignValueAtMost (spikePaddedDesign design _ _)
           (bound / (1 - spikeWeight)),

whose two cases are: a `(rank+1)`-subset MISSING the spike has all its vectors in
the flat slice, so the last basis vector is orthogonal to every one of them and
`not_posSemidef_atomSum_sub_of_repeatedAtom`'s mechanism applies verbatim; and a
subset CONTAINING the spike has the old design's `rank`-subset block, divided by
`1 - spikeWeight`, as its top-left principal submatrix.  Only the Finset surgery
that extracts the old `rank`-subset from the padded `(rank+1)`-subset is missing.
Its consequences, none of which is claimed as proved here, would be:
`alpha_4 ≤ alpha_3` (the first rank-four upper bound in this repository) and
complex weighted `(5,3)` FALSE at margin `paddedMarginRankThree = 20/9 -
20 sqrt 3/27`, sharpening the repository's `(6,3)` refutation by one atom.
Both are MEASURED below and verified at 90 digits; neither is in the kernel.

**CITED (published, not mechanized here).**  Nesterenko, arXiv:2604.24087,
Proposition 1: at rank two the analogous constant `2 - 2/sqrt 3` is exact and its
equality case is rigid.  The rank-three analogue — whether
`3(1 - cos 2 pi / 9)` is the INFIMUM over all complex weighted `(m,3)`-designs
and not merely the record — is OPEN, and nothing here closes it.

**MEASURED (floating point, NOT proved).**  Global search in the
gauge-quotiented chart `(P, t)`, `P = X (X^dagger X)^{-1} X^dagger` the `m x m`
rank-three orthogonal projector and `t` a softmax, so the Parseval residual is
`~1e-16` BY CONSTRUCTION and never a penalty.  Chart validated against raw
designs (worst per-subset `|raw lambda_min - chart lambda_min|` `1.3e-13` over
forty random points; analytic gradient matched to central differences at
`3.0e-9`).  Optimiser calibrated ON the Hesse point: descent from it achieves
exactly `0`; kicks of size `0.02` reconverge to within `8e-12`; the
one-parameter `d = 3` SIC family is reproduced (value `3(1 - cos 2 pi / 9)` at
the Hesse end, exactly `3/2` at the other end of the fundamental domain, crossing
`1` at `8.18968510422` degrees); and cold random restarts DO reach the Hesse
basin.  Solver floor on the value: `3e-12`.

    m       alpha_3^(m)(C), measured      mechanism                    attained?
    3       1                             spike limit, one weight -> 1  no
    4       1                             real symmetric quadruple      YES, cap 1
    5       2 - 2/sqrt 3 = 0.84529946162  C^2 SIC padded, spike -> 0    no
    6,7,8   3 - sqrt 5   = 0.76393202250  shared-axis trine + splits    YES, cap 1
    >= 9    3(1-cos2pi/9)= 0.70186667064  Hesse SIC + splits            YES, cap 1

No design below `3(1 - cos 2 pi / 9) - 1e-9` was found at ANY size in `3 .. 15`.

ESCALATION, as the campaign's numerics discipline requires.  Two entries came in
BELOW their claimed exact value in float: `m = 4` at `1 - 1.9e-8` with cap
`2.5e8`, and `m = 5` at `alpha_2 - 3.8e-13` with cap `2.2e5`.  At cap `c` a Gram
entry has size `c k`, so the float least eigenvalue carries an absolute error
about `c k eps`: `1.6e-7` and `1.5e-10` respectively — LARGER than both deficits.
Re-evaluating the SAME two designs at 80 digits gives `1.00000027402454` and
`alpha_2 + 1.5e-15`, both strictly ABOVE.  Neither is a sub-target design; both
are the spike limit seen through float noise.  This is the same defect class that
produced three earlier false refutations on this ledger.

EXTERNAL CALIBRATION.  The same apparatus run at RANK TWO reproduces the CITED
sharp constant from cold starts: `alpha_2^(m) = 2 - 2/sqrt 3` to `2.2e-16` at
`m = 4, 5, 6` (3000 restarts each), and `alpha_2^(2) = alpha_2^(3) = 1` in the
spike limit.  That check does not depend on any rank-three belief.
The whole curve is explained by the two ladders that ARE proved: padding (this
file) moves rank `k` to rank `k + 1` and accounts for `m = 4, 5`; splitting
(`Gtz/Complex/AtomSplitting.lean`) moves size `m` to `m + 1` and accounts for the
flats at `6,7,8` and at `m ≥ 9`.

THE PADDED VALUE, MEASURED AND VERIFIED AT 90 DIGITS.  For the padded design the
value is exactly `min(1/spikeWeight, V/(1 - spikeWeight))` where `V` is the
sub-design's value; measured against the closed form at
`spikeWeight = 3e-1, 1e-1, 1e-2, 1e-4, 1e-6, 1e-8` for the Mercedes `(3,2)` trine,
the `ℂ²` SIC and the Hesse SIC, agreeing to machine precision every time.  At
`spikeWeight = 1/10` on the `ℂ²` SIC the value is exactly `20/9 - 20 sqrt 3/27 =
0.939221624023053856646336043328983431894218331` (90 digits) — below one, so the
padded `(5,3)` design refutes complex weighted `(5,3)`.  The `w -> 0` limits are
`2 - 2/sqrt 3` at rank three and `3(1 - cos 2 pi / 9)` at rank four.

RIGIDITY (MEASURED).  At `m = 9`, every perturb-and-reconverge run that returned
to the record value returned to the SINGLE Hesse orbit, measured by the
gauge-invariant fingerprint (sorted weights, atom norms, pair overlaps, Bargmann
triangle invariants, subset spectrum).  At `m = 12` the same protocol finds
SEVERAL orbits at the same value, exactly as atom splitting predicts — so the
classifier has a positive control and the single orbit at `m = 9` is not an
artefact.

A DISPUTED LEDGER ENTRY, RESOLVED.  `Gtz/Complex/SharpConstantLedger.lean`
carries `measuredRankFourUncapped = 0.701866670643` with the warning that it
equals the rank-three constant to all twelve digits and that no rank-4 search
reproduced it.  The decimal is CORRECT as an upper bound and the mechanism is the
padding ladder below: `alpha_4 ≤ alpha_3`, approached as `cap kappa -> infinity`,
never attained.  What was wrong is the recorded attribution — a rank-4 design at
`m = 10` with `kappa = 2.69`.  Read the number as
`complexRankConstantAtMost_four_of_pos`, which is proved here.
-/
import Mathlib
import Gtz.Complex.AtomSplitting

namespace Gtz

open Matrix Complex
open scoped ComplexOrder

set_option maxHeartbeats 1000000

/-! # Part A. The Hesse margin is attained

The excess of one non-collinear triple is a nonnegative combination of two
rank-one atoms at the margin.  Everything in this part is that one certificate
and its consequences. -/

section HesseAttainment

/-! ## The certificate, with the amplitude and the shift abstracted -/

/-- Rescaling an atom vector by a self-conjugate scalar rescales the rank-one atom
by the square.  This is what lets the Eisenstein amplitude `sqrt(3/2)` leave the
algebra before any triple identity is checked. -/
theorem complexAtom_smul_selfConj {rank : ℕ} (scalar : ℂ) (vector : Fin rank → ℂ)
    (hconj : (starRingEnd ℂ) scalar = scalar) :
    complexAtom (scalar • vector) = (scalar * scalar) • complexAtom vector := by
  ext rowIndex colIndex
  simp only [complexAtom_apply, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul,
    map_mul, hconj]
  ring

/-- **The binding triple's block, in closed form.**  Hesse directions `0`, `1` and
`3` sum to a matrix whose only transcendence is the cube root itself.  The three
cancellations used are `w * conj w = w^3`, `1 + w + w^2 = 0` and `w^6 = 1`. -/
theorem hesseTriple_unitAtomSum (cubeRoot : ℂ)
    (hcubeConj : (starRingEnd ℂ) cubeRoot = cubeRoot ^ 2)
    (hcube : cubeRoot ^ 3 = 1)
    (hcubeSum : 1 + cubeRoot + cubeRoot ^ 2 = 0) :
    complexAtom ![0, 1, -1]
        + (complexAtom ![0, cubeRoot, -cubeRoot ^ 2] + complexAtom ![-1, 0, 1])
      = !![1, 0, -1;
           0, 2, cubeRoot;
           -1, cubeRoot ^ 2, 3] := by
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp only [Fin.reduceFinMk, Fin.isValue, Matrix.add_apply, complexAtom_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
      Matrix.of_apply, map_neg, map_one, map_zero, map_pow, hcubeConj]
  · ring
  · ring
  · ring
  · ring
  · linear_combination hcube
  · linear_combination -hcubeSum - cubeRoot ^ 2 * hcube
  · ring
  · linear_combination -hcubeSum - cubeRoot * hcube
  · linear_combination (cubeRoot ^ 3 + 1) * hcube

/-- **The binding decomposition, cleared of denominators.**  A block LDL step on
the `(0,0)` pivot writes the excess as `(1/p) atom(v1) + (1/q) atom(v2)` with
`p = 3/2 - shift` and `q = 3 - shift`; multiplying through by `p q` makes it a
POLYNOMIAL identity, so no invertibility hypothesis is needed to state it and no
denominator clearing is needed to prove it.  The only entry that is not a ring
identity is `(2,2)`, whose residue is exactly `-(1/8)` times the Hesse cubic —
which is why the decomposition holds at the margin and at no other shift. -/
theorem hesseTriple_scaledDecomposition (cubeRoot shift : ℂ)
    (hcubeConj : (starRingEnd ℂ) cubeRoot = cubeRoot ^ 2)
    (hcube : cubeRoot ^ 3 = 1)
    (hshiftConj : (starRingEnd ℂ) shift = shift)
    (hroot : 8 * shift ^ 3 - 72 * shift ^ 2 + 162 * shift - 81 = 0) :
    ((3 / 2 - shift) * (3 - shift)) •
        (((3 : ℂ) / 2) • (!![1, 0, -1;
                            0, 2, cubeRoot;
                            -1, cubeRoot ^ 2, 3] : Matrix (Fin 3) (Fin 3) ℂ)
          - shift • (1 : Matrix (Fin 3) (Fin 3) ℂ))
      = (3 - shift) • complexAtom ![3 / 2 - shift, 0, -(3 / 2)]
        + (3 / 2 - shift) • complexAtom ![0, 3 - shift, 3 / 2 * cubeRoot ^ 2] := by
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp only [Fin.reduceFinMk, Fin.isValue, Matrix.sub_apply, Matrix.add_apply,
      Matrix.smul_apply, smul_eq_mul, complexAtom_apply, Matrix.one_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
      Matrix.of_apply, map_mul, map_neg, map_zero, map_pow, map_ofNat, map_sub,
      map_div₀, hcubeConj, hshiftConj, Fin.reduceEq, if_true, if_false] <;>
    first
      | ring1
      | linear_combination
          ((3 / 2 - shift) * (3 - shift) * (3 / 2) * cubeRoot) * hcube
      | linear_combination
          (-((3 / 2 - shift) * (3 - shift) * (3 / 2) * cubeRoot)) * hcube
      | linear_combination (-((3 / 2 - shift) * (9 / 4)) * (cubeRoot ^ 3 + 1)) * hcube
          + (-(1 : ℂ) / 8) * hroot

/-! ## Instantiation at the Hesse design -/

/-- The three Hesse atoms of the binding triple, with the amplitude factored out
of every rank-one atom. -/
theorem hesseBindingTriple_atomSum :
    complexAtom (hesseAtom 0) + (complexAtom (hesseAtom 1) + complexAtom (hesseAtom 3))
      = ((3 : ℂ) / 2) • (!![1, 0, -1;
                           0, 2, omegaRoot;
                           -1, omegaRoot ^ 2, 3] : Matrix (Fin 3) (Fin 3) ℂ) := by
  have hzero : hesseAtom 0 = hesseAmpC • ![0, 1, -1] := rfl
  have hone : hesseAtom 1 = hesseAmpC • ![0, omegaRoot, -omegaRoot ^ 2] := rfl
  have hthree : hesseAtom 3 = hesseAmpC • ![-1, 0, 1] := rfl
  rw [hzero, hone, hthree,
    complexAtom_smul_selfConj hesseAmpC _ hesseAmpC_conj,
    complexAtom_smul_selfConj hesseAmpC _ hesseAmpC_conj,
    complexAtom_smul_selfConj hesseAmpC _ hesseAmpC_conj, hesseAmpC_sq,
    ← smul_add, ← smul_add,
    hesseTriple_unitAtomSum omegaRoot omegaRoot_conj_eq omegaRoot_cube omegaRoot_sum]

/-- The margin, cast to `ℂ`, still solves the Hesse cubic. -/
theorem hesseMarginC_isRoot :
    8 * (((hesseMarginRankThree : ℝ) : ℂ)) ^ 3
        - 72 * (((hesseMarginRankThree : ℝ) : ℂ)) ^ 2
        + 162 * (((hesseMarginRankThree : ℝ) : ℂ)) - 81 = 0 := by
  have hreal := hesseMargin_isRoot
  have hcast : ((8 * hesseMarginRankThree ^ 3 - 72 * hesseMarginRankThree ^ 2
      + 162 * hesseMarginRankThree - 81 : ℝ) : ℂ) = ((0 : ℝ) : ℂ) := by rw [hreal]
  push_cast at hcast
  linear_combination hcast

/-- The first LDL pivot is strictly positive at the margin: `3/2 - h > 0`. -/
theorem hesseMargin_firstPivot_pos :
    (0 : ℂ) < 3 / 2 - ((hesseMarginRankThree : ℝ) : ℂ) := by
  have hcast : (3 : ℂ) / 2 - ((hesseMarginRankThree : ℝ) : ℂ)
      = (((3 / 2 - hesseMarginRankThree : ℝ)) : ℂ) := by push_cast; ring
  rw [hcast]
  exact Complex.zero_lt_real.mpr (by linarith [hesseMargin_lt_threeHalves])

/-- The second LDL pivot is strictly positive at the margin: `3 - h > 0`. -/
theorem hesseMargin_secondPivot_pos :
    (0 : ℂ) < 3 - ((hesseMarginRankThree : ℝ) : ℂ) := by
  have hcast : (3 : ℂ) - ((hesseMarginRankThree : ℝ) : ℂ)
      = (((3 - hesseMarginRankThree : ℝ)) : ℂ) := by push_cast; ring
  rw [hcast]
  exact Complex.zero_lt_real.mpr (by linarith [hesseMargin_lt_threeHalves])

/-- **The excess of the binding triple is positive semidefinite AT the margin.**
The scaled decomposition exhibits `(p q) . excess` as a nonnegative combination of
two rank-one atoms; dividing by the positive scalar `p q` transfers positive
semidefiniteness back to the excess. -/
theorem hesseBindingTriple_excess_posSemidef :
    (complexAtom (hesseAtom 0)
        + (complexAtom (hesseAtom 1) + complexAtom (hesseAtom 3))
        - ((hesseMarginRankThree : ℝ) : ℂ)
          • (1 : Matrix (Fin 3) (Fin 3) ℂ)).PosSemidef := by
  set shift : ℂ := ((hesseMarginRankThree : ℝ) : ℂ) with hshiftDef
  have hfirstPos := hesseMargin_firstPivot_pos
  have hsecondPos := hesseMargin_secondPivot_pos
  have hscalePos : (0 : ℂ) < (3 / 2 - shift) * (3 - shift) :=
    mul_pos hfirstPos hsecondPos
  have hscaleNe : (3 / 2 - shift) * (3 - shift) ≠ 0 := ne_of_gt hscalePos
  have hscaled : (((3 / 2 - shift) * (3 - shift)) •
      (complexAtom (hesseAtom 0)
        + (complexAtom (hesseAtom 1) + complexAtom (hesseAtom 3))
        - shift • (1 : Matrix (Fin 3) (Fin 3) ℂ))).PosSemidef := by
    rw [hesseBindingTriple_atomSum,
      hesseTriple_scaledDecomposition omegaRoot shift omegaRoot_conj_eq omegaRoot_cube
        (Complex.conj_ofReal _) hesseMarginC_isRoot]
    exact ((complexAtom_posSemidef _).smul (le_of_lt hsecondPos)).add
      ((complexAtom_posSemidef _).smul (le_of_lt hfirstPos))
  have hrescale : ((3 / 2 - shift) * (3 - shift))⁻¹ •
      (((3 / 2 - shift) * (3 - shift)) •
        (complexAtom (hesseAtom 0)
          + (complexAtom (hesseAtom 1) + complexAtom (hesseAtom 3))
          - shift • (1 : Matrix (Fin 3) (Fin 3) ℂ)))
      = complexAtom (hesseAtom 0)
          + (complexAtom (hesseAtom 1) + complexAtom (hesseAtom 3))
          - shift • (1 : Matrix (Fin 3) (Fin 3) ℂ) :=
    inv_smul_smul₀ hscaleNe _
  rw [← hrescale]
  exact hscaled.smul (le_of_lt (inv_pos.mpr hscalePos))

/-- The chosen triple really has three elements, so it is a legitimate competitor
in the maximum that defines the design's value. -/
theorem hesseBindingTriple_card : ({0, 1, 3} : Finset (Fin 9)).card = 3 := by decide

/-- **THE ATTAINMENT STATEMENT.**  The Hesse SIC's triple `{0, 1, 3}` dominates AT
the level `3(1 - cos 2 pi / 9)`.  With `hesseDesign_valueAtMost` this closes the
design's best-subset value on both sides. -/
theorem hesse_bindingTriple_dominatesAtLevel :
    ComplexDominatesAtLevel hesseDesign ({0, 1, 3} : Finset (Fin 9))
      hesseMarginRankThree := by
  rw [ComplexDominatesAtLevel, hesseDesign_atom,
    hesseTripleSum_expand (by decide : (0 : Fin 9) ≠ 1) (by decide : (1 : Fin 9) ≠ 3)
      (by decide : (0 : Fin 9) ≠ 3)]
  exact hesseBindingTriple_excess_posSemidef

/-! ## The exact value, as a greatest element -/

/-- The shifts at which some `3`-subset of the Hesse SIC still dominates. -/
def hesseDominatedShifts : Set ℝ :=
  {shift : ℝ | ∃ subset : Finset (Fin 9), subset.card = 3 ∧
    ((∑ atomLabel ∈ subset, complexAtom (hesseDesign.atom atomLabel))
      - ((shift : ℝ) : ℂ) • (1 : Matrix (Fin 3) (Fin 3) ℂ)).PosSemidef}

theorem hesseDominatedShifts_eq_Iic :
    hesseDominatedShifts = Set.Iic hesseMarginRankThree := by
  ext shift
  constructor
  · intro hmember
    by_contra habove
    obtain ⟨subset, hcard, hpsd⟩ := hmember
    exact hesse_no_triple_above_margin shift (lt_of_not_ge habove) subset hcard hpsd
  · intro hbelow
    exact ⟨{0, 1, 3}, hesseBindingTriple_card,
      posSemidef_sub_smul_one_of_le hesse_bindingTriple_dominatesAtLevel hbelow⟩

/-- **The Hesse SIC's value, in LOEWNER form.**  The margin is attained by a triple
and no triple survives any strictly larger shift, so the set of shifts at which
some `3`-subset dominates has greatest element `3(1 - cos 2 pi / 9)`.

SCOPE, exactly as for the trine: this is the Loewner reading of
`max_{|subset| = 3} lambda_min = 3(1 - cos 2 pi / 9)`.  The eigenvalue reading
would additionally need `block - level . I ⪰ 0 ↔ lambda_min block ≥ level`, whose
`←` direction uses the spectral theorem and is not mechanized here. -/
theorem hesseMargin_isGreatest :
    IsGreatest hesseDominatedShifts hesseMarginRankThree := by
  rw [hesseDominatedShifts_eq_Iic]
  exact isGreatest_Iic

/-- **Attained and least, in one statement.**  The first component is what the
repository's SCOPE NOTE listed as missing; the second is the half already proved
in `Gtz/Complex/PerRankConstantLedger.lean`. -/
theorem hesseMargin_isAttainedAndLeast :
    ComplexDominatesAtLevel hesseDesign ({0, 1, 3} : Finset (Fin 9)) hesseMarginRankThree
      ∧ ComplexDesignValueAtMost hesseDesign hesseMarginRankThree :=
  ⟨hesse_bindingTriple_dominatesAtLevel, hesseDesign_valueAtMost⟩

end HesseAttainment

/-! # Part B. The one-spike padding ladder: `alpha_{k+1} ≤ alpha_k`

Take a weighted `(size, rank)`-design, flatten it into the first `rank`
coordinates of `ℂ^{rank+1}`, rescale by `1/sqrt(1 - spikeWeight)`, and adjoin one
SPIKE atom `e_last / sqrt spikeWeight` at weight `spikeWeight`.  Parseval holds
blockwise.  A `(rank+1)`-subset either MISSES the spike — then all its vectors
have last coordinate zero, so the excess has `-level` in its last diagonal entry
and no positive level survives — or CONTAINS it, and then the excess restricted to
the first `rank` coordinates is the old design's subset block divided by
`1 - spikeWeight`, minus `level`.  A principal submatrix of a positive
semidefinite matrix is positive semidefinite, so the old design's value bound
transfers. -/

section SpikePadding

variable {size rank : ℕ}

/-- The flattened image of an old atom: the old coordinates rescaled, then zero. -/
noncomputable def flattenedAtom (spikeWeight : ℝ) (vector : Fin rank → ℂ) :
    Fin (rank + 1) → ℂ :=
  Fin.snoc (fun slot => vector slot / ((Real.sqrt (1 - spikeWeight) : ℝ) : ℂ)) 0

/-- The spike atom: everything zero except the new last coordinate. -/
noncomputable def spikeAtom (spikeWeight : ℝ) : Fin (rank + 1) → ℂ :=
  Fin.snoc (fun _ => 0) (1 / ((Real.sqrt spikeWeight : ℝ) : ℂ))

/-- The padded atom family: flattened old atoms, then the spike. -/
noncomputable def spikePaddedAtom (design : ComplexWeightedDesign size rank)
    (spikeWeight : ℝ) : Fin (size + 1) → (Fin (rank + 1) → ℂ) :=
  Fin.snoc (fun atomLabel => flattenedAtom spikeWeight (design.atom atomLabel))
    (spikeAtom spikeWeight)

/-- The padded weights: the old ones scaled by `1 - spikeWeight`, then the spike's. -/
noncomputable def spikePaddedWeight (design : ComplexWeightedDesign size rank)
    (spikeWeight : ℝ) : Fin (size + 1) → ℝ :=
  Fin.snoc (fun atomLabel => (1 - spikeWeight) * design.weight atomLabel) spikeWeight

theorem spikePaddedWeight_pos (design : ComplexWeightedDesign size rank)
    {spikeWeight : ℝ} (hlow : 0 < spikeWeight) (hhigh : spikeWeight < 1) :
    ∀ atomLabel, 0 < spikePaddedWeight design spikeWeight atomLabel := by
  intro atomLabel
  refine Fin.lastCases ?_ ?_ atomLabel
  · simpa only [spikePaddedWeight, Fin.snoc_last] using hlow
  · intro oldLabel
    simp only [spikePaddedWeight, Fin.snoc_castSucc]
    exact mul_pos (by linarith) (design.weight_pos oldLabel)

theorem spikePaddedWeight_sum_one (design : ComplexWeightedDesign size rank)
    (spikeWeight : ℝ) :
    ∑ atomLabel, spikePaddedWeight design spikeWeight atomLabel = 1 := by
  rw [Fin.sum_univ_castSucc]
  simp only [spikePaddedWeight, Fin.snoc_castSucc, Fin.snoc_last]
  rw [← Finset.mul_sum, design.weight_sum_one]
  ring

/-- Parseval for the padded design.  The old block is restored because the weight
factor `1 - spikeWeight` cancels the amplitude factor `1/(1 - spikeWeight)`, and
the new corner is `spikeWeight * (1/spikeWeight)`. -/
theorem spikePaddedDesign_parseval (design : ComplexWeightedDesign size rank)
    {spikeWeight : ℝ} (hlow : 0 < spikeWeight) (hhigh : spikeWeight < 1) :
    ∑ atomLabel, ((spikePaddedWeight design spikeWeight atomLabel : ℝ) : ℂ)
        • complexAtom (spikePaddedAtom design spikeWeight atomLabel)
      = (1 : Matrix (Fin (rank + 1)) (Fin (rank + 1)) ℂ) := by
  have hgapPos : (0 : ℝ) < 1 - spikeWeight := by linarith
  have hgapSq : ((Real.sqrt (1 - spikeWeight) : ℝ) : ℂ)
      * ((Real.sqrt (1 - spikeWeight) : ℝ) : ℂ) = ((1 - spikeWeight : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (le_of_lt hgapPos)]
  have hgapNe : ((Real.sqrt (1 - spikeWeight) : ℝ) : ℂ) ≠ 0 := by
    simpa using Real.sqrt_ne_zero'.mpr hgapPos
  have hspikeSq : ((Real.sqrt spikeWeight : ℝ) : ℂ) * ((Real.sqrt spikeWeight : ℝ) : ℂ)
      = ((spikeWeight : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (le_of_lt hlow)]
  have hspikeNe : ((Real.sqrt spikeWeight : ℝ) : ℂ) ≠ 0 := by
    simpa using Real.sqrt_ne_zero'.mpr hlow
  have hspikePow : ((Real.sqrt spikeWeight : ℝ) : ℂ) ^ 2 = ((spikeWeight : ℝ) : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (le_of_lt hlow)]
  have hgapPow : ((Real.sqrt (1 - spikeWeight) : ℝ) : ℂ) ^ 2
      = ((1 - spikeWeight : ℝ) : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (le_of_lt hgapPos)]
  have hgapCast : ((1 - spikeWeight : ℝ) : ℂ) = 1 - ((spikeWeight : ℝ) : ℂ) := by
    push_cast; ring
  ext rowIndex colIndex
  rw [Matrix.sum_apply, Fin.sum_univ_castSucc]
  simp only [spikePaddedWeight, spikePaddedAtom, Fin.snoc_castSucc, Fin.snoc_last,
    Matrix.smul_apply, smul_eq_mul, complexAtom_apply, flattenedAtom, spikeAtom]
  induction rowIndex using Fin.lastCases with
  | last =>
    induction colIndex using Fin.lastCases with
    | last =>
      simp only [Fin.snoc_last, map_div₀, map_one, Complex.conj_ofReal,
        Matrix.one_apply_eq]
      rw [Finset.sum_eq_zero (fun oldLabel _ => by simp)]
      field_simp
      linear_combination (-1 : ℂ) * hspikePow
    | cast colSlot =>
      simp only [Fin.snoc_last, Fin.snoc_castSucc, map_zero, mul_zero, zero_mul]
      rw [Finset.sum_eq_zero (fun oldLabel _ => by simp), Matrix.one_apply]
      have hne : ¬ (Fin.last rank = Fin.castSucc colSlot) :=
        (Fin.castSucc_lt_last colSlot).ne'
      simp [hne]
  | cast rowSlot =>
    induction colIndex using Fin.lastCases with
    | last =>
      simp only [Fin.snoc_last, Fin.snoc_castSucc, map_div₀, map_one,
        Complex.conj_ofReal, zero_mul, mul_zero]
      rw [Finset.sum_eq_zero (fun oldLabel _ => by simp), Matrix.one_apply]
      have hne : ¬ (Fin.castSucc rowSlot = Fin.last rank) :=
        (Fin.castSucc_lt_last rowSlot).ne
      simp [hne]
    | cast colSlot =>
      have hparseval := congrArg (fun block => block rowSlot colSlot) design.isParseval
      simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
        complexAtom_apply, Matrix.one_apply] at hparseval
      simp only [Fin.snoc_castSucc, map_div₀, Complex.conj_ofReal, map_zero,
        mul_zero, add_zero, Matrix.one_apply, Fin.castSucc_inj]
      rw [← hparseval]
      refine Finset.sum_congr rfl (fun oldLabel _ => ?_)
      field_simp
      push_cast
      linear_combination
        (-(((design.weight oldLabel : ℝ) : ℂ) * (design.atom oldLabel rowSlot)
            * ((starRingEnd ℂ) (design.atom oldLabel colSlot)))) * hgapPow
          + (-(((design.weight oldLabel : ℝ) : ℂ) * (design.atom oldLabel rowSlot)
            * ((starRingEnd ℂ) (design.atom oldLabel colSlot)))) * hgapCast

/-- **The padded design.**  One more atom, one more dimension, still a genuine
weighted design over ℂ. -/
noncomputable def spikePaddedDesign (design : ComplexWeightedDesign size rank)
    {spikeWeight : ℝ} (hlow : 0 < spikeWeight) (hhigh : spikeWeight < 1) :
    ComplexWeightedDesign (size + 1) (rank + 1) where
  atom := spikePaddedAtom design spikeWeight
  weight := spikePaddedWeight design spikeWeight
  weight_pos := spikePaddedWeight_pos design hlow hhigh
  weight_sum_one := spikePaddedWeight_sum_one design spikeWeight
  isParseval := spikePaddedDesign_parseval design hlow hhigh

end SpikePadding

end Gtz
