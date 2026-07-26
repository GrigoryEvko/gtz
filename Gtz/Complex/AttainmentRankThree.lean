/-
# The rank-three complex floor: the solve-trace refinement and the exchange step

`Gtz/Complex/PerRankConstantLedger.lean` records `alpha_3 ≥ 1/3` over ℂ, proved
from the maximal-volume subset alone.  This file is the floor attack on that
number: it replaces the constant `k` in the maximal-volume estimate by a
DESIGN-DEPENDENT quantity that is never larger, and it supplies the two
combinatorial facts an exchange argument needs, namely that the exchanged triples
are legal `k`-subsets and that the covering atom is genuinely outside the pick.

## Header: what is PROVED, what is CITED, what is MEASURED

**PROVED here (kernel-checked, zero new axioms).**

* `normSq_solveCombination_le_rowNormSq` — Cauchy–Schwarz on a single solve row,
  replacing the ledger's triangle-inequality step.  Where the ledger spends the
  bound `|gamma_cj| ≤ 1` to reach the factor `k`, this keeps the exact row norm.
* `exists_maximalVolume_solveTrace_covering` — the maximal-volume covering bound
  with the factor `solveTraceWeight = Σ_c t_c ‖gamma_c‖²` in place of `k`.
* `solveTraceWeight_le_rank` — that factor never exceeds `k`, so the statement is
  a refinement of the ledger's and re-derives `alpha_k ≥ 1/k` as a corollary
  (`exists_subset_atomSum_sub_solveLevel_posSemidef`).
* `exists_subset_atomSum_sub_capInverse_posSemidef` — the CONDITIONAL floor: a
  design whose maximal-volume solve trace is at most `cap` has value at least
  `1/cap`.  At `cap < 3` and rank three this is strictly above `1/3`.
* `exchangeSelection_card` — the exchange of one selected atom for an outside
  atom is again a `k`-subset, hence a legal competitor in the `max` defining the
  design value.
* `coveringAtom_notMem_of_undominated` — the atom Parseval hands for a direction
  the pick fails to cover lies OUTSIDE the pick, so the exchange is not vacuous.
* `exchangeFloorRankThree` — the constant `(7 - sqrt 34)/3` of the exchange
  derivation below, with its exact minimal polynomial `3x² - 14x + 5` and the
  window `1/3 < it < 2/5`, so it is strictly above the recorded floor and
  strictly below the recorded Hesse ceiling.

**CITED (not mechanized anywhere in this repository).**

* Nesterenko, arXiv:2604.24087, Proposition 1: over ℂ at rank two the sharp
  constant is `2 - 2/sqrt 3`, attained exactly at the `ℂ²` SIC.  Its proof runs
  through the Hopf image `w_i ∈ ℝ³` of the rows (`|w_i| = ‖u_i‖²`, `Σ w_i = 0`,
  `Σ |w_i| = 2`), the bridge identity `|⟨u_i,u_j⟩|² = (|w_i||w_j| + ⟨w_i,w_j⟩)/2`,
  and a spectral count: `P_{ij} = |w_i||w_j| - ⟨w_i,w_j⟩` equals `rr^T` minus a
  Gram matrix of vectors in `ℝ³`, hence has at most THREE negative eigenvalues;
  with `tr P = 0` that forces `tr(C²) ≥ s²/3` on the compression, and the
  resulting contradiction is exactly `alpha² - 4 alpha + 8/3 = 0`.
* Sengupta–Pautov, arXiv:2604.05944: the real rank-two case; they state the
  problem open for all `1 < k < n-1` except `(n,k) = (4,2)`.

**MEASURED (floating point, never used as a hypothesis below).**

* The exchange floor of the reduced problem — the exact infimum of
  `max(beta, mu_1, mu_2, mu_3)` over the relaxed data below — is `≈ 0.4213`.
  The closed-form constant proved reachable by the derivation is the smaller
  `(7 - sqrt 34)/3 ≈ 0.3896827`; the gap is looseness of the analytic chain, not
  of the method.
* The maximal-volume subset ALONE is capped at exactly `1/k`, and the witness is
  EXACT, not floating point.  Take the `(4,3)` design
    `g_0 = (487/36, -233/36, -233/36)`, `g_1, g_2` its cyclic shifts, at weight
    `1/400` each, and `g_3 = c·(1,1,1)` at weight `397/400`, `c² = 57551/171504`.
  Parseval is an exact rational identity (checked to 60 digits: residual 1.6e-61).
  Its selected triple `{g_0,g_1,g_2}` satisfies `g_0 + g_1 + g_2 = (7/12)·ones`,
  so the outside atom is `(12c/7)` times that sum — a coefficient of modulus
  `sqrt(57551/58359) < 1`, i.e. exactly the maximal-volume input — and applying
  the triple's atom sum to `ones` returns `(7/12)² · ones = (49/144)·ones`.  So
  that triple's least eigenvalue is at most `49/144 = 0.34027...`, while the four
  row volumes are `700/3` against `400c = 231.712...`, making it the STRICT
  maximal-volume pick.  Hence no argument using only the entrywise solve bound
  can certify a rank-three level above `49/144`, which is below `(7-sqrt 34)/3`.
  This member sits in the general family `g_j = s e_j + q·ones` (weight `w`),
  `g_4 = c·ones` (weight `1-3w`), `s² = 1/w`, `q = (v-s)/3`,
  `c² = (1 - w v²)/(3(1-3w))`, whose selected triple has least eigenvalue exactly
  `v²` and is strictly maximal-volume iff `v² > 1/(3-8w)`; as `w → 0` that floor
  tends to `1/3`.  Mechanizing this witness is a clean next step — the arithmetic
  is rational throughout, only the single amplitude `c` is a square root — and it
  was written and typechecked up to `simp`-normal-form friction on the
  conjugation of real-cast numerals, then withdrawn rather than shipped broken.

* Where the exchange derivation loses.  The trace criterion of step 5 is very
  nearly free: at `alpha = 0.4213` the supremum of `tr(Y⁻¹)` over the whole
  relaxed feasible set is `2.893 < 3`, so steps 1-5 alone already reach the
  measured exchange floor.  Essentially the entire gap `0.3897 -> 0.4213` is the
  Loewner relaxation of step 6, which spends `lambda_2 + lambda_3 ≤ sigma` as
  `lambda_2, lambda_3 ≤ sigma` separately.  Keeping the two residual eigenvalues
  apart is where a sharper constant lives.

## The exchange derivation, in full, for the mechanizer

Fix a design, let `T` be a maximal-`|det|` pick on the conjugated atom rows, `M`
the selected block, `S_T = MᴴM` the atom sum, `beta = lambda_min(S_T)`, `x` a unit
min-eigenvector, `gamma_c` the solve vector of atom `c` (so `g_c = Σ_j gamma_cj
g_{c_j}` with `|gamma_cj| ≤ 1`), and `Gamma = Σ_c t_c gamma_c gamma_c^H`.

1. `Gamma = (M Mᴴ)⁻¹`, so `lambda_max(Gamma) = 1/beta =: lam`.
2. `Gamma_jj = Σ_c t_c |gamma_cj|² ≤ 1`, hence `tr Gamma ≤ 3` and `lam ≤ 3`.
   (`solveTraceWeight` below is exactly `tr Gamma`.)
3. Parseval at `x` produces an atom `g_*` with `|⟨g_*,x⟩| ≥ 1`, and
   `⟨g_c,x⟩ = gamma_c^H u` for `u = M x`, which satisfies `Gamma u = lam u` and
   `‖u‖² = beta`.  Hence `|gamma_*^H uhat|² ≥ lam` and `N := ‖gamma_*‖² ∈ [lam, 3]`.
4. The exchanged triple `T \ {c_j} ∪ {*}` has atom sum `Mᴴ E_j M` with
   `E_j = I - e_j e_j^H + gamma_* gamma_*^H`, so its least eigenvalue is the
   pencil minimum `mu_j = min_z z^H E_j z / z^H Gamma z`, and `mu_j ≥ alpha` is
   exactly `Y - e_j e_j^H ⪰ 0` for `Y := I + gamma_* gamma_*^H - alpha Gamma`.
5. For `Y ≻ 0`, `Y ⪰ e_j e_j^H` iff `(Y⁻¹)_jj ≤ 1`, and `min_j (Y⁻¹)_jj ≤
   tr(Y⁻¹)/3`.  So `tr(Y⁻¹) ≤ 3` already forces some `mu_j ≥ alpha`.
6. With `sigma := 3 - lam ≥ lambda_2(Gamma)` one gets
   `Gamma ⪯ lam·uhat uhat^H + sigma(I - uhat uhat^H)`, hence `Y ⪰ Y_0 :=
   p I + gamma_* gamma_*^H - c·uhat uhat^H` where `p = 1 - alpha·sigma` and
   `c = alpha(2 lam - 3)`; and `Y ⪰ Y_0 ≻ 0` gives `tr(Y⁻¹) ≤ tr(Y_0⁻¹)`.
7. `Y_0` acts as `p` on `span{uhat, gamma_*}^perp` (dimension at least one) and as
   the 2×2 block `Z = [[p + a² - c, ab],[ab, p + b²]]` on the plane, with
   `a² = |gamma_*^H uhat|² ≥ lam` and `a² + b² = N`.  So
   `tr(Y_0⁻¹) = 1/p + tr Z / det Z`.
8. `det Z = p(p + N - c) - c b²` falls in `b²`, and `p - c = 1 - alpha·lam < 0`
   makes it fall in `N` as well, while `tr Z = 2p + N - c` rises in `N`.  The
   worst case is therefore `N = 3`, `b² = sigma`.
9. The whole obstruction collapses to one scalar inequality: for every
   `sigma ∈ [0, 3 - 1/alpha]`,
   `1/p + (2p + 3 - c)/(p(p + 3 - c) - c·sigma) ≤ 3`.
   Its worst point is the right endpoint `sigma = 3 - 1/alpha`, where `c = p =
   2 - 3 alpha` and the inequality becomes `3 alpha² - 14 alpha + 5 ≥ 0`, i.e.
   `alpha ≤ (7 - sqrt 34)/3` — the constant `exchangeFloorRankThree` below.

Steps 1–3 and the legality of step 4's triple are mechanized here; steps 5–9 are
Loewner-order and trace-of-inverse algebra on `3×3` complex matrices, stated but
NOT mechanized, and nothing in this file assumes them.  `exchangeFloorRankThree`
is therefore a NAMED CONSTANT with proved arithmetic, not a proved floor: the
proved floor exported by this file is still `alpha_3 ≥ 1/3`, now with the
conditional strengthening `alpha_3 ≥ 1/cap` whenever the solve trace is capped
below three.
-/

import Mathlib
import Gtz.Core.Basic
import Gtz.LinAlg.PsdKit
import Gtz.Complex.ComplexWitness
import Gtz.Complex.PerRankConstantLedger

namespace Gtz

open Matrix Complex
open scoped ComplexOrder

set_option maxHeartbeats 1000000

/-! # Part A. The solve-trace refinement of the maximal-volume floor -/

section SolveTrace

variable {m k : ℕ}

/-- **The squared norm of one solve row.** The ledger only ever uses that each
entry has modulus at most one; this keeps the row's actual length, which is what
the exchange step needs. -/
noncomputable def solveRowNormSq {rows cols : ℕ}
    (frame : Matrix (Fin rows) (Fin cols) ℂ) (pick : Fin cols → Fin rows)
    (rowIndex : Fin rows) : ℝ :=
  ∑ coord, Complex.normSq (complexSolveMatrix frame pick rowIndex coord)

theorem solveRowNormSq_nonneg {rows cols : ℕ}
    (frame : Matrix (Fin rows) (Fin cols) ℂ) (pick : Fin cols → Fin rows)
    (rowIndex : Fin rows) : 0 ≤ solveRowNormSq frame pick rowIndex :=
  Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

/-- Every solve row of a maximal-volume pick is short: each of its `cols` entries
has modulus at most one, so its squared length is at most `cols`. -/
theorem solveRowNormSq_le_rank {rows cols : ℕ}
    (frame : Matrix (Fin rows) (Fin cols) ℂ) (pick : Fin cols → Fin rows)
    (hbounded : ∀ rowIndex colIndex, ‖complexSolveMatrix frame pick rowIndex colIndex‖ ≤ 1)
    (rowIndex : Fin rows) : solveRowNormSq frame pick rowIndex ≤ (cols : ℝ) := by
  have hterm : ∀ coord : Fin cols,
      Complex.normSq (complexSolveMatrix frame pick rowIndex coord) ≤ 1 := by
    intro coord
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [hbounded rowIndex coord, norm_nonneg (complexSolveMatrix frame pick rowIndex coord)]
  calc solveRowNormSq frame pick rowIndex
      ≤ ∑ _coord : Fin cols, (1 : ℝ) :=
        Finset.sum_le_sum fun coord _ => hterm coord
    _ = (cols : ℝ) := by simp

/-- **Cauchy–Schwarz on one solve row.** A vector's spread through the solve
matrix costs the row's squared length, not the ambient rank. This is the single
place where this file departs from the ledger's estimate: the ledger bounds
`|Σ_j b_j u_j| ≤ Σ_j |u_j|` and then pays `Chebyshev` to reach `k`, which is
tight only when every `|b_j|` equals one AND every `|u_j|` agrees. -/
theorem normSq_solveCombination_le_rowNormSq {rows cols : ℕ}
    (solve : Matrix (Fin rows) (Fin cols) ℂ) (coefficients : Fin cols → ℂ)
    (rowIndex : Fin rows) :
    Complex.normSq ((solve *ᵥ coefficients) rowIndex)
      ≤ (∑ coord, Complex.normSq (solve rowIndex coord))
        * ∑ coord, Complex.normSq (coefficients coord) := by
  have hexpand : (solve *ᵥ coefficients) rowIndex
      = ∑ coord, solve rowIndex coord * coefficients coord := by
    simp only [Matrix.mulVec, dotProduct]
  have htriangle : ‖(solve *ᵥ coefficients) rowIndex‖
      ≤ ∑ coord, ‖solve rowIndex coord‖ * ‖coefficients coord‖ := by
    rw [hexpand]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun coord _ => ?_)
    rw [norm_mul]
  have hcauchy : (∑ coord, ‖solve rowIndex coord‖ * ‖coefficients coord‖) ^ 2
      ≤ (∑ coord, ‖solve rowIndex coord‖ ^ 2) * ∑ coord, ‖coefficients coord‖ ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin cols))
      (fun coord => ‖solve rowIndex coord‖) (fun coord => ‖coefficients coord‖)
  have hleftConvert : (∑ coord, ‖solve rowIndex coord‖ ^ 2)
      = ∑ coord, Complex.normSq (solve rowIndex coord) :=
    Finset.sum_congr rfl fun coord _ => (Complex.normSq_eq_norm_sq _).symm
  have hrightConvert : (∑ coord, ‖coefficients coord‖ ^ 2)
      = ∑ coord, Complex.normSq (coefficients coord) :=
    Finset.sum_congr rfl fun coord _ => (Complex.normSq_eq_norm_sq _).symm
  rw [Complex.normSq_eq_norm_sq, ← hleftConvert, ← hrightConvert]
  have hsumNonneg : 0 ≤ ∑ coord, ‖solve rowIndex coord‖ * ‖coefficients coord‖ :=
    Finset.sum_nonneg fun coord _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  nlinarith [htriangle, hcauchy, hsumNonneg,
    norm_nonneg ((solve *ᵥ coefficients) rowIndex)]

/-- **The solve trace of a design at a pick**: `W = Σ_c t_c ‖gamma_c‖²`, the
weighted average of the solve rows' squared lengths. Under the identification of
`Gtz/Complex/PerRankConstantLedger.lean` this is the trace of `(M Mᴴ)⁻¹`, i.e.
the sum of the reciprocal eigenvalues of the selected atom sum. -/
noncomputable def solveTraceWeight (design : ComplexWeightedDesign m k)
    (pick : Fin k → Fin m) : ℝ :=
  ∑ atomLabel, design.weight atomLabel
    * solveRowNormSq (conjugateAtomRows design) pick atomLabel

theorem solveTraceWeight_nonneg (design : ComplexWeightedDesign m k)
    (pick : Fin k → Fin m) : 0 ≤ solveTraceWeight design pick :=
  Finset.sum_nonneg fun atomLabel _ =>
    mul_nonneg (design.weight_pos atomLabel).le (solveRowNormSq_nonneg _ _ _)

/-- **The solve trace never exceeds the rank.** So every statement below with
`solveTraceWeight` in it refines the same statement with `k`. -/
theorem solveTraceWeight_le_rank (design : ComplexWeightedDesign m k)
    (pick : Fin k → Fin m)
    (hbounded : ∀ rowIndex colIndex,
      ‖complexSolveMatrix (conjugateAtomRows design) pick rowIndex colIndex‖ ≤ 1) :
    solveTraceWeight design pick ≤ (k : ℝ) := by
  have hstep : ∀ atomLabel ∈ (Finset.univ : Finset (Fin m)),
      design.weight atomLabel * solveRowNormSq (conjugateAtomRows design) pick atomLabel
        ≤ design.weight atomLabel * (k : ℝ) := fun atomLabel _ =>
    mul_le_mul_of_nonneg_left
      (solveRowNormSq_le_rank _ pick hbounded atomLabel) (design.weight_pos atomLabel).le
  calc solveTraceWeight design pick
      ≤ ∑ atomLabel, design.weight atomLabel * (k : ℝ) := Finset.sum_le_sum hstep
    _ = (k : ℝ) := by rw [← Finset.sum_mul, design.weight_sum_one, one_mul]

/-- **THE SOLVE-TRACE COVERING BOUND.** Every complex weighted design has an
injective pick whose `k` selected atoms cover every direction to within the
factor `solveTraceWeight ≤ k`:

  `|x|² ≤ (Σ_c t_c ‖gamma_c‖²) · Σ_{c ∈ T} |⟨g_c, x⟩|²`.

The pick is the maximal-`|det|` one. The proof is the ledger's, with the single
change that the spread of an atom over the selected basis is measured by
Cauchy–Schwarz against the actual solve row instead of by the triangle
inequality against the bound `1`; the weighted sum over atoms is then exactly
Parseval, with no weight splitting needed at all. -/
theorem exists_maximalVolume_solveTrace_covering (design : ComplexWeightedDesign m k) :
    ∃ pick : Fin k → Fin m, Function.Injective pick ∧
      solveTraceWeight design pick ≤ (k : ℝ) ∧
      ∀ direction : Fin k → ℂ,
        (∑ coord, Complex.normSq (direction coord))
          ≤ solveTraceWeight design pick
            * ∑ selectedIndex,
                Complex.normSq (star (design.atom (pick selectedIndex)) ⬝ᵥ direction) := by
  classical
  obtain ⟨pick, hdet, hmax⟩ := exists_maximalVolume_pick_complex design
  have hunit : IsUnit (selectedComplexRows (conjugateAtomRows design) pick).det :=
    isUnit_iff_ne_zero.mpr hdet
  have hinjective : Function.Injective pick := by
    intro leftIndex rightIndex hsame
    by_contra hne
    refine hdet (Matrix.det_zero_of_row_eq hne ?_)
    funext coord
    show conjugateAtomRows design (pick leftIndex) coord
      = conjugateAtomRows design (pick rightIndex) coord
    rw [hsame]
  have hbounded : ∀ (rowIndex : Fin m) (colIndex : Fin k),
      ‖complexSolveMatrix (conjugateAtomRows design) pick rowIndex colIndex‖ ≤ 1 :=
    fun rowIndex colIndex =>
      norm_complexSolveMatrix_le_one_of_maximalVolume _ pick hunit hmax rowIndex colIndex
  refine ⟨pick, hinjective, solveTraceWeight_le_rank design pick hbounded, fun direction => ?_⟩
  set selectedDirection : Fin k → ℂ :=
    selectedComplexRows (conjugateAtomRows design) pick *ᵥ direction with hselectedDef
  have hrecover : complexSolveMatrix (conjugateAtomRows design) pick *ᵥ selectedDirection
      = conjugateAtomRows design *ᵥ direction := by
    rw [hselectedDef, Matrix.mulVec_mulVec, complexSolveMatrix_mul_selected _ pick hunit]
  have hselectedValue : ∀ selectedIndex : Fin k,
      selectedDirection selectedIndex
        = star (design.atom (pick selectedIndex)) ⬝ᵥ direction := by
    intro selectedIndex
    rw [hselectedDef, selectedComplexRows_mulVec, conjugateAtomRows_mulVec]
  set selectedTotal : ℝ :=
    ∑ selectedIndex, Complex.normSq (selectedDirection selectedIndex) with hselectedTotalDef
  have hselectedTotalNonneg : 0 ≤ selectedTotal :=
    Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
  have hspread : ∀ atomIndex : Fin m,
      Complex.normSq (star (design.atom atomIndex) ⬝ᵥ direction)
        ≤ solveRowNormSq (conjugateAtomRows design) pick atomIndex * selectedTotal := by
    intro atomIndex
    have hstep := normSq_solveCombination_le_rowNormSq
      (complexSolveMatrix (conjugateAtomRows design) pick) selectedDirection atomIndex
    rwa [hrecover, conjugateAtomRows_mulVec] at hstep
  have hweighted :
      (∑ atomLabel, design.weight atomLabel
          * Complex.normSq (star (design.atom atomLabel) ⬝ᵥ direction))
        ≤ solveTraceWeight design pick * selectedTotal := by
    rw [solveTraceWeight, Finset.sum_mul]
    refine Finset.sum_le_sum fun atomLabel _ => ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (hspread atomLabel) (design.weight_pos atomLabel).le
  rw [complexParseval_normSq design direction] at hweighted
  have htotalValue : selectedTotal
      = ∑ selectedIndex,
          Complex.normSq (star (design.atom (pick selectedIndex)) ⬝ᵥ direction) :=
    Finset.sum_congr rfl fun selectedIndex _ => by rw [hselectedValue selectedIndex]
  rw [← htotalValue]
  exact hweighted

/-- **The refined floor in Loewner form.** Some `k`-subset dominates `level · I`
for a level at least `1/k` — the level being the reciprocal of the design's own
solve trace. This subsumes the ledger's `alpha_k ≥ 1/k` and is strictly better
whenever the solve trace is strictly below `k`. -/
theorem exists_subset_atomSum_sub_solveLevel_posSemidef (hrank : 0 < k)
    (design : ComplexWeightedDesign m k) :
    ∃ (selection : Finset (Fin m)) (level : ℝ), selection.card = k ∧
      ((k : ℝ)⁻¹ ≤ level) ∧
      ((∑ atomLabel ∈ selection, complexAtom (design.atom atomLabel)) - ((level : ℝ) : ℂ)
        • (1 : Matrix (Fin k) (Fin k) ℂ)).PosSemidef := by
  classical
  obtain ⟨pick, hinjective, hcap, hcovering⟩ :=
    exists_maximalVolume_solveTrace_covering design
  have hrankPos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hrank
  set probeDirection : Fin k → ℂ :=
    fun coord => if coord = (⟨0, hrank⟩ : Fin k) then 1 else 0 with hprobeDef
  have hprobeOne : (1 : ℝ) ≤ ∑ coord, Complex.normSq (probeDirection coord) := by
    have hentry : Complex.normSq (probeDirection (⟨0, hrank⟩ : Fin k)) = 1 := by
      simp [hprobeDef]
    calc (1 : ℝ) = Complex.normSq (probeDirection (⟨0, hrank⟩ : Fin k)) := hentry.symm
      _ ≤ ∑ coord, Complex.normSq (probeDirection coord) :=
        Finset.single_le_sum (f := fun coord => Complex.normSq (probeDirection coord))
          (fun coord _ => Complex.normSq_nonneg _) (Finset.mem_univ _)
  have htracePos : 0 < solveTraceWeight design pick := by
    rcases lt_or_eq_of_le (solveTraceWeight_nonneg design pick) with hpos | hzero
    · exact hpos
    · exfalso
      have hcover := hcovering probeDirection
      rw [← hzero, zero_mul] at hcover
      linarith
  refine ⟨Finset.image pick Finset.univ, (solveTraceWeight design pick)⁻¹, ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hinjective, Finset.card_univ, Fintype.card_fin]
  · have hscaledCap : (k : ℝ)⁻¹ * solveTraceWeight design pick ≤ (k : ℝ)⁻¹ * (k : ℝ) :=
      mul_le_mul_of_nonneg_left hcap (le_of_lt (inv_pos.mpr hrankPos))
    rw [inv_mul_cancel₀ hrankPos.ne'] at hscaledCap
    have hfinal := mul_le_mul_of_nonneg_right hscaledCap (le_of_lt (inv_pos.mpr htracePos))
    rwa [mul_assoc, mul_inv_cancel₀ htracePos.ne', mul_one, one_mul] at hfinal
  · refine posSemidef_atomSum_sub_smul_one design _ _ fun direction => ?_
    rw [Finset.sum_image fun left _ right _ hlr => hinjective hlr]
    have hscaled := mul_le_mul_of_nonneg_left (hcovering direction)
      (le_of_lt (inv_pos.mpr htracePos))
    rwa [← mul_assoc, inv_mul_cancel₀ htracePos.ne', one_mul] at hscaled

end SolveTrace

/-! # Part B. The exchange scaffolding -/

section Exchange

variable {m k : ℕ}

/-- **The exchange of one selected atom for an outside atom.** Dropping the atom
at slot `dropIndex` from a pick and inserting `enterAtom`. -/
def exchangeSelection (pick : Fin k → Fin m) (dropIndex : Fin k) (enterAtom : Fin m) :
    Finset (Fin m) :=
  insert enterAtom ((Finset.image pick Finset.univ).erase (pick dropIndex))

/-- **The exchanged set is again a `k`-subset**, hence a legal competitor in the
maximum defining a design's value. Nothing about maximal volume is used. -/
theorem exchangeSelection_card (hrank : 0 < k) {pick : Fin k → Fin m}
    (hinjective : Function.Injective pick) (dropIndex : Fin k) {enterAtom : Fin m}
    (houtside : enterAtom ∉ Finset.image pick Finset.univ) :
    (exchangeSelection pick dropIndex enterAtom).card = k := by
  classical
  have himageCard : (Finset.image pick Finset.univ).card = k := by
    rw [Finset.card_image_of_injective _ hinjective, Finset.card_univ, Fintype.card_fin]
  have hmem : pick dropIndex ∈ Finset.image pick Finset.univ :=
    Finset.mem_image_of_mem _ (Finset.mem_univ dropIndex)
  have herased : ((Finset.image pick Finset.univ).erase (pick dropIndex)).card = k - 1 := by
    rw [Finset.card_erase_of_mem hmem, himageCard]
  have hnotErased : enterAtom ∉ (Finset.image pick Finset.univ).erase (pick dropIndex) :=
    fun hcontra => houtside (Finset.mem_of_mem_erase hcontra)
  rw [exchangeSelection, Finset.card_insert_of_notMem hnotErased, herased]
  omega

/-- **The covering atom is outside the pick.** If a direction is not covered by
the selected atoms at level one, then any atom that does cover it — the one
`exists_atom_covering_direction_complex` produces — cannot itself be selected.
So the exchange step never degenerates to re-inserting an atom already present,
and by `exchangeSelection_card` it produces a genuinely new `k`-subset. -/
theorem coveringAtom_notMem_of_undominated (design : ComplexWeightedDesign m k)
    {pick : Fin k → Fin m} {direction : Fin k → ℂ} {coveringAtom : Fin m}
    (hundominated : (∑ selectedIndex,
        Complex.normSq (star (design.atom (pick selectedIndex)) ⬝ᵥ direction))
      < ∑ coord, Complex.normSq (direction coord))
    (hcovers : (∑ coord, Complex.normSq (direction coord))
      ≤ Complex.normSq (star (design.atom coveringAtom) ⬝ᵥ direction)) :
    coveringAtom ∉ Finset.image pick (Finset.univ : Finset (Fin k)) := by
  classical
  intro hmem
  obtain ⟨selectedIndex, _, hequal⟩ := Finset.mem_image.mp hmem
  have hsingle : Complex.normSq (star (design.atom coveringAtom) ⬝ᵥ direction)
      ≤ ∑ index, Complex.normSq (star (design.atom (pick index)) ⬝ᵥ direction) := by
    rw [← hequal]
    exact Finset.single_le_sum
      (f := fun index => Complex.normSq (star (design.atom (pick index)) ⬝ᵥ direction))
      (fun index _ => Complex.normSq_nonneg _) (Finset.mem_univ selectedIndex)
  exact absurd (hcovers.trans hsingle) (not_le.mpr hundominated)

/-- **The conditional floor.** A design whose maximal-volume solve trace is at
most `cap` has a `k`-subset dominating `cap⁻¹ · I`. At rank three any `cap < 3`
puts that design strictly above the recorded floor `1/3`; the exchange derivation
in this file's header is what handles the remaining regime `cap = 3`. -/
theorem exists_subset_atomSum_sub_capInverse_posSemidef {cap : ℝ} (hcap : 0 < cap)
    (design : ComplexWeightedDesign m k) {pick : Fin k → Fin m}
    (hinjective : Function.Injective pick)
    (hcovering : ∀ direction : Fin k → ℂ,
      (∑ coord, Complex.normSq (direction coord))
        ≤ solveTraceWeight design pick
          * ∑ selectedIndex,
              Complex.normSq (star (design.atom (pick selectedIndex)) ⬝ᵥ direction))
    (hle : solveTraceWeight design pick ≤ cap) :
    ∃ selection : Finset (Fin m), selection.card = k ∧
      ((∑ atomLabel ∈ selection, complexAtom (design.atom atomLabel)) - ((cap⁻¹ : ℝ) : ℂ)
        • (1 : Matrix (Fin k) (Fin k) ℂ)).PosSemidef := by
  classical
  refine ⟨Finset.image pick Finset.univ, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hinjective, Finset.card_univ, Fintype.card_fin]
  · refine posSemidef_atomSum_sub_smul_one design _ _ fun direction => ?_
    rw [Finset.sum_image fun left _ right _ hlr => hinjective hlr]
    set selectedTotal : ℝ := ∑ selectedIndex,
      Complex.normSq (star (design.atom (pick selectedIndex)) ⬝ᵥ direction) with hselected
    have hselectedNonneg : 0 ≤ selectedTotal :=
      Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
    have hchain := (hcovering direction).trans
      (mul_le_mul_of_nonneg_right hle hselectedNonneg)
    have hscaled := mul_le_mul_of_nonneg_left hchain (le_of_lt (inv_pos.mpr hcap))
    rwa [← mul_assoc, inv_mul_cancel₀ hcap.ne', one_mul] at hscaled

end Exchange

/-! # Part C. The exchange constant -/

section ExchangeConstant

/-- **The constant of the exchange derivation**, `(7 - sqrt 34)/3`. Step 9 of the
header: at the worst point of the scalar certificate the obstruction is exactly
`3 x² - 14 x + 5 ≥ 0`, whose least root this is. It is the largest level at
which that chain closes; the reduced problem's true infimum is measured at
`≈ 0.4213`, and the recorded rank-three ceiling is the Hesse value `≈ 0.70187`,
so this constant sits strictly inside the surviving window. -/
noncomputable def exchangeFloorRankThree : ℝ := (7 - Real.sqrt 34) / 3

theorem sqrt34_sq : Real.sqrt 34 ^ 2 = 34 := Real.sq_sqrt (by norm_num)

theorem sqrt34_nonneg : 0 ≤ Real.sqrt 34 := Real.sqrt_nonneg 34

/-- The constant's exact minimal polynomial. -/
theorem exchangeFloor_isRoot :
    3 * exchangeFloorRankThree ^ 2 - 14 * exchangeFloorRankThree + 5 = 0 := by
  rw [exchangeFloorRankThree]
  have hsq := sqrt34_sq
  field_simp
  nlinarith [hsq]

theorem sqrt34_window : (583 : ℝ) / 100 < Real.sqrt 34 ∧ Real.sqrt 34 < 5831 / 1000 := by
  constructor
  · nlinarith [sqrt34_sq, sqrt34_nonneg]
  · nlinarith [sqrt34_sq, sqrt34_nonneg]

/-- **The constant lies strictly above the recorded rank-three floor.** -/
theorem exchangeFloor_window :
    (1 : ℝ) / 3 < exchangeFloorRankThree ∧ exchangeFloorRankThree < 2 / 5 := by
  obtain ⟨hlow, hhigh⟩ := sqrt34_window
  constructor
  · rw [exchangeFloorRankThree]; linarith
  · rw [exchangeFloorRankThree]; linarith

/-- The constant is the LEAST root of its minimal polynomial: the other root is
`(7 + sqrt 34)/3 > 4`. -/
theorem exchangeFloor_lt_otherRoot :
    exchangeFloorRankThree < (7 + Real.sqrt 34) / 3 := by
  obtain ⟨hlow, _⟩ := sqrt34_window
  rw [exchangeFloorRankThree]
  linarith

/-- **The window is non-empty**: the exchange constant is strictly below the
recorded rank-three ceiling `3(1 - cos 2 pi / 9)` of the ledger, so nothing here
contradicts the Hesse witness. -/
theorem exchangeFloor_lt_hesseMargin :
    exchangeFloorRankThree < hesseMarginRankThree := by
  obtain ⟨_, hhigh⟩ := exchangeFloor_window
  obtain ⟨hhesseLow, _⟩ := hesseMargin_window
  linarith

/-- **The recorded floor, restated at rank three**, so this file's ledger line is
self-contained: the PROVED unconditional floor exported here is still `1/3`. -/
theorem complexRankConstantAtLeast_three_third :
    ComplexRankConstantAtLeast 3 ((3 : ℝ)⁻¹) := by
  have hbase := complexRankConstantAtLeast_rankInverse 3
  norm_num at hbase ⊢
  exact hbase

end ExchangeConstant

/-! ## SCOPE NOTE

What this file adds to the rank-three complex floor, and what it does not.

ADDS, as theorems: the solve-trace refinement of the maximal-volume covering
bound and its Loewner corollary (`exists_maximalVolume_solveTrace_covering`,
`exists_subset_atomSum_sub_solveLevel_posSemidef`), the conditional floor
`1/cap` (`exists_subset_atomSum_sub_capInverse_posSemidef`), the legality of the
exchanged subsets (`exchangeSelection_card`), the exteriority of the covering
atom (`coveringAtom_notMem_of_undominated`), and the exact arithmetic of the
exchange constant.

DOES NOT ADD: any unconditional improvement of `alpha_3 ≥ 1/3`. Steps 5–9 of the
header — the trace-of-inverse criterion, the Loewner comparison `Y ⪰ Y_0`, the
two-plane block reduction, and the scalar certificate — are stated there and
validated numerically off-repo, but they are NOT mechanized and NOT assumed
anywhere in this file. Every theorem above is unconditional or carries its
hypothesis explicitly.

The named unproved hypothesis, in one line: *at a maximal-volume pick with
`lambda_min < (7 - sqrt 34)/3`, one of the three exchanges against the covering
atom already reaches that level.* Discharging it is exactly steps 5–9. -/

end Gtz
