/-
# The sharp complex constant, per rank: witness, mechanism, ledger

FIELD IS ℂ unless a declaration says otherwise. Every margin here is an
eigenvalue of the `k × k` ATOM BLOCK `S_C = Σ_{c ∈ C} g_c g_c*` — read off its
characteristic polynomial `det(S_C − z·I)` — never `λ_min` of a squared frame
operator. Three deliverables.

**1. A strictly sharper rank-3 witness: the shared-axis trine.** Two coplanar
trines of lines in `ℂ³` sharing the third axis,

  `g_j = (√2, 0, ω^j)`,  `g_{3+j} = (0, √2, ω^j)`,  `j = 0,1,2`,  `ω = e^{2πi/3}`,

at UNIFORM weight `1/6` with every leverage exactly `3` — a unit-norm tight
frame, cap `κ = 1`, no spike and no limit argument. All twenty triples fail:
the two coplanar ones miss an axis, and the eighteen spanning ones all have the
same characteristic polynomial `(3 − z)(z² − 6z + 4)`, hence integer excess
determinant `−2` and binding root `3 − √5 ≈ 0.763932` (least-ness and
best-subset are now MECHANIZED, in `Gtz/Complex/PerRankConstantLedger.lean`;
the scope note at the end records what is still outside the kernel). That beats the repo's
padded-SIC witness (`20/9 − 20√3/27 ≈ 0.939222`) at the same size `m = 6`, and
it beats the rank-2 sharp constant `α₂ = 2 − 2/√3 ≈ 0.845299` — so
`2 − 2/√3` is a statement about `k = 2` only, not "the sharp complex constant".

**2. The separation mechanism, as a computed scalar.** For a triple,
`det(G_C − z·I)` splits as a phase-free MODULUS BUDGET plus `2·Re T`, where
`T = <g0,g1><g1,g2><g2,g0>` is the Bargmann triangle invariant. The whole field
dependence is that one real number, entering affinely. The separating scalar is
the PHASE DEFECT `|T|² − (Re T)² = (Im T)²`: exactly `0` for every real
configuration, with no hypotheses. Both `(6,3)` designs on record have a
NEGATIVE modulus budget, so moduli decide neither — the real icosahedron
(budget `−14/5`) is rescued by its extremal phase term `+2·(3/√5)³ ≈ +4.83`,
while the complex trine (budget `−2`, defect `3`) dies because its phase term is
exactly `0` even though its own moduli would permit `+2√3 ≈ +3.46`.

**3. The honest ledger.** PROVEN / PROVEN ELSEWHERE / EXACT ELSEWHERE / MEASURED,
marked per rank, with the leverage cap and digit count of every measurement. No
measurement is stated as a theorem; the measured constants are definitions used
by nothing.
-/
import Mathlib
import Gtz.Complex.ComplexWitness
import Gtz.Complex.ComplexPadding
import Gtz.Quantitative.GapStabilityFacts
import Gtz.Quantitative.RealnessEngine

namespace Gtz

open Matrix Complex
open scoped ComplexOrder

/-! ### Tools -/

/-- Entrywise reading of a rank-one complex atom. -/
theorem complexAtom_apply {k : ℕ} (vecArg : Fin k → ℂ) (rowIndex colIndex : Fin k) :
    complexAtom vecArg rowIndex colIndex
      = vecArg rowIndex * (starRingEnd ℂ) (vecArg colIndex) := by
  simp [complexAtom, Matrix.vecMulVec_apply, Pi.star_apply, RCLike.star_def]

/-- A matrix with a negative diagonal entry is not positive semidefinite. -/
theorem not_posSemidef_of_diag_re_neg {k : ℕ} {M : Matrix (Fin k) (Fin k) ℂ}
    (index : Fin k) (hneg : (M index index).re < 0) : ¬ M.PosSemidef := by
  intro hpsd
  have hre := (Complex.le_def.mp (hpsd.diag_nonneg (i := index))).1
  simp only [Complex.zero_re] at hre
  linarith

/-- A matrix whose determinant has negative real part is not positive
semidefinite (any dimension). -/
theorem not_posSemidef_of_det_re_neg_gen {k : ℕ} {M : Matrix (Fin k) (Fin k) ℂ}
    (hneg : M.det.re < 0) : ¬ M.PosSemidef := by
  intro hpsd
  have hre := (Complex.le_def.mp hpsd.det_nonneg).1
  simp only [Complex.zero_re] at hre
  linarith

/-! ### The three cube-root phases -/

/-- The three cube roots of unity, indexed by `Fin 3`. -/
noncomputable def omegaPow (phaseIndex : Fin 3) : ℂ := omegaRoot ^ (phaseIndex : ℕ)

theorem omegaPow_zero : omegaPow 0 = 1 := by simp [omegaPow]
theorem omegaPow_one : omegaPow 1 = omegaRoot := by simp [omegaPow]
theorem omegaPow_two : omegaPow 2 = omegaRoot ^ 2 := by simp [omegaPow]

/-- Every phase is a unit: `conj(ω^j)·ω^j = 1`. -/
theorem omegaPow_unit (phaseIndex : Fin 3) :
    (starRingEnd ℂ) (omegaPow phaseIndex) * omegaPow phaseIndex = 1 := by
  have hconjTwo : (starRingEnd ℂ) (omegaRoot ^ 2) = omegaRoot ^ 4 := by
    rw [map_pow, omegaRoot_conj_eq]; ring
  fin_cases phaseIndex
  · rw [show ((⟨0, by omega⟩ : Fin 3)) = 0 from rfl, omegaPow_zero]
    simp
  · rw [show ((⟨1, by omega⟩ : Fin 3)) = 1 from rfl, omegaPow_one]
    exact omegaRoot_star_mul
  · rw [show ((⟨2, by omega⟩ : Fin 3)) = 2 from rfl, omegaPow_two, hconjTwo]
    linear_combination (omegaRoot ^ 3 + 1) * omegaRoot_cube

/-- **Distinct phases pair to `−1`**: `conj(ω^a)ω^b + conj(ω^b)ω^a = ω + ω² = −1`.
This single relation is what makes every mixed trine triple fail. -/
theorem omegaPow_cross {firstPhase secondPhase : Fin 3} (hne : firstPhase ≠ secondPhase) :
    (starRingEnd ℂ) (omegaPow firstPhase) * omegaPow secondPhase
      + (starRingEnd ℂ) (omegaPow secondPhase) * omegaPow firstPhase = -1 := by
  have hconjTwo : (starRingEnd ℂ) (omegaRoot ^ 2) = omegaRoot ^ 4 := by
    rw [map_pow, omegaRoot_conj_eq]; ring
  have hpair : omegaRoot + omegaRoot ^ 2 = -1 := by linear_combination omegaRoot_sum
  fin_cases firstPhase <;> fin_cases secondPhase <;>
    simp only [show ((⟨0, by omega⟩ : Fin 3)) = 0 from rfl,
      show ((⟨1, by omega⟩ : Fin 3)) = 1 from rfl,
      show ((⟨2, by omega⟩ : Fin 3)) = 2 from rfl,
      omegaPow_zero, omegaPow_one, omegaPow_two, omegaRoot_conj_eq, hconjTwo,
      map_one] <;>
    first
      | exact absurd rfl hne
      | linear_combination hpair
      | linear_combination hpair + omegaRoot * omegaRoot_cube
      | linear_combination hpair + (omegaRoot + omegaRoot ^ 2) * omegaRoot_cube

/-! ### The `(6,3)` shared-axis trine -/

/-- A trine atom on the first axis: `√2·e₀ + ω^j·e₂`. -/
noncomputable def trineLeft (phaseIndex : Fin 3) : Fin 3 → ℂ :=
  ![topAmpC, 0, omegaPow phaseIndex]

/-- A trine atom on the second axis: `√2·e₁ + ω^j·e₂`. -/
noncomputable def trineRight (phaseIndex : Fin 3) : Fin 3 → ℂ :=
  ![0, topAmpC, omegaPow phaseIndex]

/-- The six atoms of the shared-axis trine: two coplanar trines of lines in `ℂ³`
sharing the third axis, at uniform weight `1/6` and leverage exactly `3`. -/
noncomputable def trineAtom : Fin 6 → Fin 3 → ℂ :=
  ![trineLeft 0, trineLeft 1, trineLeft 2, trineRight 0, trineRight 1, trineRight 2]

theorem trineAtom_zero : trineAtom 0 = trineLeft 0 := rfl
theorem trineAtom_one : trineAtom 1 = trineLeft 1 := rfl
theorem trineAtom_two : trineAtom 2 = trineLeft 2 := rfl
theorem trineAtom_three : trineAtom 3 = trineRight 0 := rfl
theorem trineAtom_four : trineAtom 4 = trineRight 1 := rfl
theorem trineAtom_five : trineAtom 5 = trineRight 2 := rfl

theorem trineLeft_coordZero (phaseIndex : Fin 3) : trineLeft phaseIndex 0 = topAmpC := rfl
theorem trineLeft_coordOne (phaseIndex : Fin 3) : trineLeft phaseIndex 1 = 0 := rfl
theorem trineLeft_coordTwo (phaseIndex : Fin 3) :
    trineLeft phaseIndex 2 = omegaPow phaseIndex := rfl
theorem trineRight_coordZero (phaseIndex : Fin 3) : trineRight phaseIndex 0 = 0 := rfl
theorem trineRight_coordOne (phaseIndex : Fin 3) :
    trineRight phaseIndex 1 = topAmpC := rfl
theorem trineRight_coordTwo (phaseIndex : Fin 3) :
    trineRight phaseIndex 2 = omegaPow phaseIndex := rfl

/-- Every trine atom has leverage exactly `3`: the design is a unit-norm tight
frame, cap `κ = 1`, no leverage blow-up anywhere. -/
theorem trineLeft_leverage (phaseIndex : Fin 3) :
    star (trineLeft phaseIndex) ⬝ᵥ trineLeft phaseIndex = 3 := by
  simp only [dotProduct, Fin.sum_univ_three, Pi.star_apply, RCLike.star_def,
    trineLeft_coordZero, trineLeft_coordOne, trineLeft_coordTwo, topAmpC_conj,
    map_zero]
  linear_combination topAmpC_sq + omegaPow_unit phaseIndex

theorem trineRight_leverage (phaseIndex : Fin 3) :
    star (trineRight phaseIndex) ⬝ᵥ trineRight phaseIndex = 3 := by
  simp only [dotProduct, Fin.sum_univ_three, Pi.star_apply, RCLike.star_def,
    trineRight_coordZero, trineRight_coordOne, trineRight_coordTwo, topAmpC_conj,
    map_zero]
  linear_combination topAmpC_sq + omegaPow_unit phaseIndex

/-- The three phases sum to zero — the cube-root cancellation that makes uniform
weight `1/6` resolve the identity. -/
theorem omegaPow_sum : omegaPow 0 + omegaPow 1 + omegaPow 2 = 0 := by
  rw [omegaPow_zero, omegaPow_one, omegaPow_two]
  exact omegaRoot_sum

theorem omegaPow_conj_sum :
    (starRingEnd ℂ) (omegaPow 0) + (starRingEnd ℂ) (omegaPow 1)
      + (starRingEnd ℂ) (omegaPow 2) = 0 := by
  have happly := congrArg (starRingEnd ℂ) omegaPow_sum
  simpa using happly

/-- **The trine is a weighted design over ℂ** at uniform weight `1/6`: the two
axis blocks each receive `6` from their own trine, the shared axis receives
`1 + 1 + 1` twice, and every cross term is a cube-root sum. -/
theorem trineParseval :
    ∑ c, (((1 : ℝ) / 6 : ℝ) : ℂ) • complexAtom (trineAtom c) = 1 := by
  have hunitZero := omegaPow_unit 0
  have hunitOne := omegaPow_unit 1
  have hunitTwo := omegaPow_unit 2
  have hsum := omegaPow_sum
  have hconjSum := omegaPow_conj_sum
  ext rowIndex colIndex
  rw [Matrix.sum_apply]
  simp only [Matrix.smul_apply, complexAtom_apply, smul_eq_mul, Fin.sum_univ_six,
    trineAtom_zero, trineAtom_one, trineAtom_two, trineAtom_three, trineAtom_four,
    trineAtom_five]
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp [trineLeft, trineRight, topAmpC_conj] <;>
    first
      | linear_combination (1 / 2 : ℂ) * topAmpC_sq
      | linear_combination (topAmpC / 6) * hconjSum
      | linear_combination (topAmpC / 6) * hsum
      | linear_combination (1 / 3 : ℂ) * (hunitZero + hunitOne + hunitTwo)

/-- The shared-axis trine as a complex weighted `(6,3)` design. -/
noncomputable def trineDesign : ComplexWeightedDesign 6 3 where
  atom := trineAtom
  weight := fun _ => 1 / 6
  weight_pos := fun _ => by norm_num
  weight_sum_one := by
    rw [Fin.sum_univ_six]
    norm_num
  isParseval := trineParseval

/-! ### The three-atom excess determinant -/

/-- A `3 × 3` determinant when the `(0,1)` and `(1,0)` entries vanish: the two
axis blocks decouple and only two off-diagonal PRODUCTS survive. -/
theorem det_fin_three_of_offDiag_zero {M : Matrix (Fin 3) (Fin 3) ℂ}
    (hZeroOne : M 0 1 = 0) (hOneZero : M 1 0 = 0) :
    M.det = M 0 0 * M 1 1 * M 2 2 - M 0 0 * (M 1 2 * M 2 1)
      - (M 0 2 * M 2 0) * M 1 1 := by
  rw [Matrix.det_fin_three, hZeroOne, hOneZero]
  ring

/-- Entrywise reading of a shifted three-atom excess `S_C − z·I`. -/
theorem tripleGap_apply (firstVec secondVec thirdVec : Fin 3 → ℂ) (shift : ℂ)
    (rowIndex colIndex : Fin 3) :
    (complexAtom firstVec + (complexAtom secondVec + complexAtom thirdVec)
        - shift • (1 : Matrix (Fin 3) (Fin 3) ℂ)) rowIndex colIndex
      = firstVec rowIndex * (starRingEnd ℂ) (firstVec colIndex)
        + secondVec rowIndex * (starRingEnd ℂ) (secondVec colIndex)
        + thirdVec rowIndex * (starRingEnd ℂ) (thirdVec colIndex)
        - shift * (if rowIndex = colIndex then 1 else 0) := by
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    complexAtom_apply, Matrix.one_apply]
  ring

/-- The unshifted excess is the excess at shift `1`. -/
theorem tripleGap_at_one (firstVec secondVec thirdVec : Fin 3 → ℂ) :
    complexAtom firstVec + (complexAtom secondVec + complexAtom thirdVec) - 1
      = complexAtom firstVec + (complexAtom secondVec + complexAtom thirdVec)
        - (1 : ℂ) • (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
  rw [one_smul]

/-- **The trine shape determinant.** A `3 × 3` excess with vanishing `(0,1)` /
`(1,0)` entries, third diagonal `3 − z`, first two diagonals multiplying to
`(4 − z)(2 − z)` and summing to `6 − 2z`, and both surviving off-diagonal
products equal to `2`, has determinant exactly the trine characteristic
polynomial `(3 − z)(z² − 6z + 4)`. Both mixed trine shapes (pair on either axis)
satisfy the hypotheses, which is why one lemma covers all eighteen. -/
theorem trineShape_det {excess : Matrix (Fin 3) (Fin 3) ℂ} {shift : ℂ}
    (hZeroOne : excess 0 1 = 0) (hOneZero : excess 1 0 = 0)
    (hDiagProd : excess 0 0 * excess 1 1 = (4 - shift) * (2 - shift))
    (hDiagSum : excess 0 0 + excess 1 1 = 6 - 2 * shift)
    (hTwoTwo : excess 2 2 = 3 - shift)
    (hCrossOne : excess 1 2 * excess 2 1 = 2)
    (hCrossTwo : excess 0 2 * excess 2 0 = 2) :
    excess.det = (3 - shift) * (shift ^ 2 - 6 * shift + 4) := by
  rw [det_fin_three_of_offDiag_zero hZeroOne hOneZero, hTwoTwo, hCrossOne, hCrossTwo]
  linear_combination (3 - shift) * hDiagProd - 2 * hDiagSum

set_option maxHeartbeats 1000000 in
/-- **The mixed excess, pair on the first axis**: two atoms `(t,0,p)`, `(t,0,q)`
with `t² = 2` and distinct unit phases, plus one atom `(0,t,r)`. Its shifted
determinant is the trine characteristic polynomial. -/
theorem splitPairLeft_shifted_det (legAmp firstPhase secondPhase thirdPhase shift : ℂ)
    (hlegReal : (starRingEnd ℂ) legAmp = legAmp) (hlegSq : legAmp * legAmp = 2)
    (hunitFirst : (starRingEnd ℂ) firstPhase * firstPhase = 1)
    (hunitSecond : (starRingEnd ℂ) secondPhase * secondPhase = 1)
    (hunitThird : (starRingEnd ℂ) thirdPhase * thirdPhase = 1)
    (hcross : (starRingEnd ℂ) firstPhase * secondPhase
      + (starRingEnd ℂ) secondPhase * firstPhase = -1) :
    (complexAtom ![legAmp, 0, firstPhase]
        + (complexAtom ![legAmp, 0, secondPhase] + complexAtom ![0, legAmp, thirdPhase])
        - shift • (1 : Matrix (Fin 3) (Fin 3) ℂ)).det
      = (3 - shift) * (shift ^ 2 - 6 * shift + 4) := by
  have hentry := tripleGap_apply (![legAmp, 0, firstPhase] : Fin 3 → ℂ)
    ![legAmp, 0, secondPhase] ![0, legAmp, thirdPhase] shift
  refine trineShape_det ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hentry]; simp
  · rw [hentry]; simp
  · rw [hentry, hentry]; simp [hlegReal]
    linear_combination (2 * (legAmp * legAmp) + 4 - 3 * shift) * hlegSq
  · rw [hentry, hentry]; simp [hlegReal]
    linear_combination 3 * hlegSq
  · rw [hentry]; simp
    linear_combination hunitFirst + hunitSecond + hunitThird
  · rw [hentry, hentry]; simp [hlegReal]
    linear_combination legAmp * legAmp * hunitThird + hlegSq
  · rw [hentry, hentry]; simp [hlegReal]
    linear_combination legAmp * legAmp * hunitFirst + legAmp * legAmp * hunitSecond
      + legAmp * legAmp * hcross + hlegSq

set_option maxHeartbeats 1000000 in
/-- **The mixed excess, pair on the second axis**: the mirror shape, one atom
`(t,0,p)` and two atoms `(0,t,q)`, `(0,t,r)` with distinct unit phases. Same
characteristic polynomial — the two mixed families are spectrally identical. -/
theorem splitPairRight_shifted_det (legAmp firstPhase secondPhase thirdPhase shift : ℂ)
    (hlegReal : (starRingEnd ℂ) legAmp = legAmp) (hlegSq : legAmp * legAmp = 2)
    (hunitFirst : (starRingEnd ℂ) firstPhase * firstPhase = 1)
    (hunitSecond : (starRingEnd ℂ) secondPhase * secondPhase = 1)
    (hunitThird : (starRingEnd ℂ) thirdPhase * thirdPhase = 1)
    (hcross : (starRingEnd ℂ) secondPhase * thirdPhase
      + (starRingEnd ℂ) thirdPhase * secondPhase = -1) :
    (complexAtom ![legAmp, 0, firstPhase]
        + (complexAtom ![0, legAmp, secondPhase] + complexAtom ![0, legAmp, thirdPhase])
        - shift • (1 : Matrix (Fin 3) (Fin 3) ℂ)).det
      = (3 - shift) * (shift ^ 2 - 6 * shift + 4) := by
  have hentry := tripleGap_apply (![legAmp, 0, firstPhase] : Fin 3 → ℂ)
    ![0, legAmp, secondPhase] ![0, legAmp, thirdPhase] shift
  refine trineShape_det ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hentry]; simp
  · rw [hentry]; simp
  · rw [hentry, hentry]; simp [hlegReal]
    linear_combination (2 * (legAmp * legAmp) + 4 - 3 * shift) * hlegSq
  · rw [hentry, hentry]; simp [hlegReal]
    linear_combination 3 * hlegSq
  · rw [hentry]; simp
    linear_combination hunitFirst + hunitSecond + hunitThird
  · rw [hentry, hentry]; simp [hlegReal]
    linear_combination legAmp * legAmp * hunitSecond + legAmp * legAmp * hunitThird
      + legAmp * legAmp * hcross + hlegSq
  · rw [hentry, hentry]; simp [hlegReal]
    linear_combination legAmp * legAmp * hunitFirst + hlegSq

/-! ### The trine characteristic polynomial and the eighteen mixed triples -/

/-- **The exact spectrum of a mixed trine triple**, as its characteristic
polynomial: `det(S_C − z·I) = (3 − z)(z² − 6z + 4)`. The eigenvalues are `3` and
`3 ± √5`, so `σ_min(G_C)² = λ_min(S_C) = 3 − √5` for every one of the eighteen
mixed triples — the design's value. Pair on the first axis. -/
theorem trineMixedLeftPair_charpoly {firstPhase secondPhase : Fin 3} {thirdPhase : Fin 3}
    (hne : firstPhase ≠ secondPhase) (shift : ℂ) :
    (complexAtom (trineLeft firstPhase)
        + (complexAtom (trineLeft secondPhase) + complexAtom (trineRight thirdPhase))
        - shift • (1 : Matrix (Fin 3) (Fin 3) ℂ)).det
      = (3 - shift) * (shift ^ 2 - 6 * shift + 4) :=
  splitPairLeft_shifted_det topAmpC (omegaPow firstPhase) (omegaPow secondPhase)
    (omegaPow thirdPhase) shift topAmpC_conj topAmpC_sq (omegaPow_unit _)
    (omegaPow_unit _) (omegaPow_unit _) (omegaPow_cross hne)

/-- The same characteristic polynomial with the pair on the second axis. -/
theorem trineMixedRightPair_charpoly {firstPhase : Fin 3} {secondPhase thirdPhase : Fin 3}
    (hne : secondPhase ≠ thirdPhase) (shift : ℂ) :
    (complexAtom (trineLeft firstPhase)
        + (complexAtom (trineRight secondPhase) + complexAtom (trineRight thirdPhase))
        - shift • (1 : Matrix (Fin 3) (Fin 3) ℂ)).det
      = (3 - shift) * (shift ^ 2 - 6 * shift + 4) :=
  splitPairRight_shifted_det topAmpC (omegaPow firstPhase) (omegaPow secondPhase)
    (omegaPow thirdPhase) shift topAmpC_conj topAmpC_sq (omegaPow_unit _)
    (omegaPow_unit _) (omegaPow_unit _) (omegaPow_cross hne)

/-- **The mixed excess determinant is `−2`** — the refutation certificate, an
integer, with no radicals and no leverage blow-up. -/
theorem trineMixedLeftPair_det_one {firstPhase secondPhase : Fin 3} {thirdPhase : Fin 3}
    (hne : firstPhase ≠ secondPhase) :
    (complexAtom (trineLeft firstPhase)
        + (complexAtom (trineLeft secondPhase) + complexAtom (trineRight thirdPhase))
        - 1).det = -2 := by
  rw [tripleGap_at_one, trineMixedLeftPair_charpoly hne 1]
  norm_num

theorem trineMixedRightPair_det_one {firstPhase : Fin 3} {secondPhase thirdPhase : Fin 3}
    (hne : secondPhase ≠ thirdPhase) :
    (complexAtom (trineLeft firstPhase)
        + (complexAtom (trineRight secondPhase) + complexAtom (trineRight thirdPhase))
        - 1).det = -2 := by
  rw [tripleGap_at_one, trineMixedRightPair_charpoly hne 1]
  norm_num

theorem trineMixedLeftPair_not_psd (firstPhase secondPhase thirdPhase : Fin 3)
    (hne : firstPhase ≠ secondPhase) :
    ¬ (complexAtom (trineLeft firstPhase)
        + (complexAtom (trineLeft secondPhase) + complexAtom (trineRight thirdPhase))
        - 1).PosSemidef := by
  refine not_posSemidef_of_det_re_neg_gen ?_
  rw [trineMixedLeftPair_det_one hne]
  norm_num

theorem trineMixedRightPair_not_psd (firstPhase secondPhase thirdPhase : Fin 3)
    (hne : secondPhase ≠ thirdPhase) :
    ¬ (complexAtom (trineLeft firstPhase)
        + (complexAtom (trineRight secondPhase) + complexAtom (trineRight thirdPhase))
        - 1).PosSemidef := by
  refine not_posSemidef_of_det_re_neg_gen ?_
  rw [trineMixedRightPair_det_one hne]
  norm_num

/-! ### The two coplanar triples -/

/-- A whole trine spans only a plane: the second axis is empty, so the excess
diagonal entry there is `−1`. -/
theorem trinePureLeft_not_psd :
    ¬ (complexAtom (trineLeft 0)
        + (complexAtom (trineLeft 1) + complexAtom (trineLeft 2)) - 1).PosSemidef := by
  refine not_posSemidef_of_diag_re_neg 1 ?_
  have hvalue : (complexAtom (trineLeft 0)
      + (complexAtom (trineLeft 1) + complexAtom (trineLeft 2)) - 1) 1 1 = -1 := by
    rw [tripleGap_at_one, tripleGap_apply]
    simp [trineLeft]
  rw [hvalue]
  norm_num

theorem trinePureRight_not_psd :
    ¬ (complexAtom (trineRight 0)
        + (complexAtom (trineRight 1) + complexAtom (trineRight 2)) - 1).PosSemidef := by
  refine not_posSemidef_of_diag_re_neg 0 ?_
  have hvalue : (complexAtom (trineRight 0)
      + (complexAtom (trineRight 1) + complexAtom (trineRight 2)) - 1) 0 0 = -1 := by
    rw [tripleGap_at_one, tripleGap_apply]
    simp [trineRight]
  rw [hvalue]
  norm_num

/-! ### Every one of the twenty triples fails -/

@[simp] theorem trineDesign_atom : trineDesign.atom = trineAtom := rfl

/-- The twenty `3`-subsets of `Fin 6`, in sorted form: the two coplanar trines
and the eighteen mixed triples. -/
theorem tripleSubset_enumeration (C : Finset (Fin 6)) (hcard : C.card = 3) :
    C = {0, 1, 2} ∨ C = {0, 1, 3} ∨ C = {0, 1, 4} ∨ C = {0, 1, 5}
      ∨ C = {0, 2, 3} ∨ C = {0, 2, 4} ∨ C = {0, 2, 5}
      ∨ C = {1, 2, 3} ∨ C = {1, 2, 4} ∨ C = {1, 2, 5}
      ∨ C = {0, 3, 4} ∨ C = {0, 3, 5} ∨ C = {0, 4, 5}
      ∨ C = {1, 3, 4} ∨ C = {1, 3, 5} ∨ C = {1, 4, 5}
      ∨ C = {2, 3, 4} ∨ C = {2, 3, 5} ∨ C = {2, 4, 5}
      ∨ C = {3, 4, 5} := by
  revert hcard
  revert C
  decide

set_option maxHeartbeats 1000000 in
/-- **No triple of the trine dominates.** Two coplanar triples die on the axis
they miss; the eighteen mixed triples die on the integer determinant `−2`. -/
theorem trine_no_dominating_triple (C : Finset (Fin 6)) (hcard : C.card = 3) :
    ¬ ComplexDominates trineDesign C := by
  intro hdom
  rw [ComplexDominates] at hdom
  change ((∑ c ∈ C, complexAtom (trineAtom c)) - 1).PosSemidef at hdom
  have hexpand : ∀ firstIdx secondIdx thirdIdx : Fin 6,
      firstIdx ∉ ({secondIdx, thirdIdx} : Finset (Fin 6)) →
      secondIdx ∉ ({thirdIdx} : Finset (Fin 6)) →
      ∑ c ∈ ({firstIdx, secondIdx, thirdIdx} : Finset (Fin 6)), complexAtom (trineAtom c)
        = complexAtom (trineAtom firstIdx)
          + (complexAtom (trineAtom secondIdx) + complexAtom (trineAtom thirdIdx)) := by
    intro firstIdx secondIdx thirdIdx hfirst hsecond
    rw [Finset.sum_insert hfirst, Finset.sum_insert hsecond, Finset.sum_singleton]
  rcases tripleSubset_enumeration C hcard with
    h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · rw [h, hexpand 0 1 2 (by decide) (by decide), trineAtom_zero, trineAtom_one,
      trineAtom_two] at hdom
    exact trinePureLeft_not_psd hdom
  · rw [h, hexpand 0 1 3 (by decide) (by decide), trineAtom_zero, trineAtom_one,
      trineAtom_three] at hdom
    exact trineMixedLeftPair_not_psd 0 1 0 (by decide) hdom
  · rw [h, hexpand 0 1 4 (by decide) (by decide), trineAtom_zero, trineAtom_one,
      trineAtom_four] at hdom
    exact trineMixedLeftPair_not_psd 0 1 1 (by decide) hdom
  · rw [h, hexpand 0 1 5 (by decide) (by decide), trineAtom_zero, trineAtom_one,
      trineAtom_five] at hdom
    exact trineMixedLeftPair_not_psd 0 1 2 (by decide) hdom
  · rw [h, hexpand 0 2 3 (by decide) (by decide), trineAtom_zero, trineAtom_two,
      trineAtom_three] at hdom
    exact trineMixedLeftPair_not_psd 0 2 0 (by decide) hdom
  · rw [h, hexpand 0 2 4 (by decide) (by decide), trineAtom_zero, trineAtom_two,
      trineAtom_four] at hdom
    exact trineMixedLeftPair_not_psd 0 2 1 (by decide) hdom
  · rw [h, hexpand 0 2 5 (by decide) (by decide), trineAtom_zero, trineAtom_two,
      trineAtom_five] at hdom
    exact trineMixedLeftPair_not_psd 0 2 2 (by decide) hdom
  · rw [h, hexpand 1 2 3 (by decide) (by decide), trineAtom_one, trineAtom_two,
      trineAtom_three] at hdom
    exact trineMixedLeftPair_not_psd 1 2 0 (by decide) hdom
  · rw [h, hexpand 1 2 4 (by decide) (by decide), trineAtom_one, trineAtom_two,
      trineAtom_four] at hdom
    exact trineMixedLeftPair_not_psd 1 2 1 (by decide) hdom
  · rw [h, hexpand 1 2 5 (by decide) (by decide), trineAtom_one, trineAtom_two,
      trineAtom_five] at hdom
    exact trineMixedLeftPair_not_psd 1 2 2 (by decide) hdom
  · rw [h, hexpand 0 3 4 (by decide) (by decide), trineAtom_zero, trineAtom_three,
      trineAtom_four] at hdom
    exact trineMixedRightPair_not_psd 0 0 1 (by decide) hdom
  · rw [h, hexpand 0 3 5 (by decide) (by decide), trineAtom_zero, trineAtom_three,
      trineAtom_five] at hdom
    exact trineMixedRightPair_not_psd 0 0 2 (by decide) hdom
  · rw [h, hexpand 0 4 5 (by decide) (by decide), trineAtom_zero, trineAtom_four,
      trineAtom_five] at hdom
    exact trineMixedRightPair_not_psd 0 1 2 (by decide) hdom
  · rw [h, hexpand 1 3 4 (by decide) (by decide), trineAtom_one, trineAtom_three,
      trineAtom_four] at hdom
    exact trineMixedRightPair_not_psd 1 0 1 (by decide) hdom
  · rw [h, hexpand 1 3 5 (by decide) (by decide), trineAtom_one, trineAtom_three,
      trineAtom_five] at hdom
    exact trineMixedRightPair_not_psd 1 0 2 (by decide) hdom
  · rw [h, hexpand 1 4 5 (by decide) (by decide), trineAtom_one, trineAtom_four,
      trineAtom_five] at hdom
    exact trineMixedRightPair_not_psd 1 1 2 (by decide) hdom
  · rw [h, hexpand 2 3 4 (by decide) (by decide), trineAtom_two, trineAtom_three,
      trineAtom_four] at hdom
    exact trineMixedRightPair_not_psd 2 0 1 (by decide) hdom
  · rw [h, hexpand 2 3 5 (by decide) (by decide), trineAtom_two, trineAtom_three,
      trineAtom_five] at hdom
    exact trineMixedRightPair_not_psd 2 0 2 (by decide) hdom
  · rw [h, hexpand 2 4 5 (by decide) (by decide), trineAtom_two, trineAtom_four,
      trineAtom_five] at hdom
    exact trineMixedRightPair_not_psd 2 1 2 (by decide) hdom
  · rw [h, hexpand 3 4 5 (by decide) (by decide), trineAtom_three, trineAtom_four,
      trineAtom_five] at hdom
    exact trinePureRight_not_psd hdom

/-- **Complex weighted `(6,3)` is FALSE, on a unit-norm tight frame.** A second,
strictly sharper witness than the padded SIC: uniform weights `1/6`, every
leverage exactly `3` (cap `κ = 1`, no limit argument and no leverage blow-up),
all Gram data in `ℤ[ω]`, and only two determinant values across the twenty
triples — `−2` on the eighteen that span, and a missing axis on the two that do
not. -/
theorem complexGtzWeighted_six_three_fails_via_trine : ¬ ComplexGtzWeighted 6 3 := by
  intro hcontra
  obtain ⟨C, hcard, hdom⟩ := hcontra trineDesign
  exact trine_no_dominating_triple C hcard hdom

/-! ### The exact value of the trine: `3 − √5` -/

/-- `√5` as a complex scalar. -/
noncomputable def rootFiveC : ℂ := ((Real.sqrt 5 : ℝ) : ℂ)

theorem rootFiveC_sq : rootFiveC * rootFiveC = 5 := by
  rw [rootFiveC, ← Complex.ofReal_mul,
    Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 5)]
  norm_num

/-- **The trine characteristic polynomial factors over `ℚ(√5)`**: its roots are
`3`, `3 + √5` and `3 − √5`. -/
theorem trineCharpoly_factored (shift : ℂ) :
    (3 - shift) * (shift ^ 2 - 6 * shift + 4)
      = (3 - shift) * ((shift - (3 + rootFiveC)) * (shift - (3 - rootFiveC))) := by
  linear_combination (3 - shift) * rootFiveC_sq

/-- **The eigenvalues of every mixed trine triple's atom block are exactly `3` and
`3 ± √5`.** The block `S_C = Σ_{c ∈ C} g_c g_c*` is positive semidefinite, so the
`3 − √5 ≈ 0.7639` is a ROOT of that polynomial, and informally the least
eigenvalue, hence the design's value; that it is the LEAST root, and that the two
coplanar triples contribute `λ_min = 0`, are not established in THIS file — they
are proved in `Gtz/Complex/PerRankConstantLedger.lean`
(`trineMargin_isGreatest`, `trineBinding_leastEigenvalue`,
`trinePureLeft_dominatedShifts_isGreatest_zero`). (That the value equals
`σ_min(G_C)²` for the `k × k` Gram block is the standard `AA*` / `A*A` spectral
identity, used nowhere below and NOT mechanized here — both determinants are
computed separately instead, and both are `−2`.) -/
theorem trineMixed_spectrum {firstPhase secondPhase thirdPhase : Fin 3}
    (hne : firstPhase ≠ secondPhase) (shift : ℂ) :
    (complexAtom (trineLeft firstPhase)
        + (complexAtom (trineLeft secondPhase) + complexAtom (trineRight thirdPhase))
        - shift • (1 : Matrix (Fin 3) (Fin 3) ℂ)).det = 0
      ↔ shift = 3 ∨ shift = 3 + rootFiveC ∨ shift = 3 - rootFiveC := by
  rw [trineMixedLeftPair_charpoly hne, trineCharpoly_factored]
  rw [mul_eq_zero, mul_eq_zero, sub_eq_zero, sub_eq_zero, sub_eq_zero]
  constructor
  · rintro (heq | heq | heq)
    · exact Or.inl heq.symm
    · exact Or.inr (Or.inl heq)
    · exact Or.inr (Or.inr heq)
  · rintro (heq | heq | heq)
    · exact Or.inl heq.symm
    · exact Or.inr (Or.inl heq)
    · exact Or.inr (Or.inr heq)

/-- The margin of the shared-axis trine: `3 − √5`, an eigenvalue of every one of
its eighteen spanning triples and the least one. -/
noncomputable def trineMarginRankThree : ℝ := 3 - Real.sqrt 5

/-- `3 − √5` is a root of the trine characteristic polynomial, over `ℂ`. -/
theorem trineMargin_isRoot {firstPhase secondPhase thirdPhase : Fin 3}
    (hne : firstPhase ≠ secondPhase) :
    (complexAtom (trineLeft firstPhase)
        + (complexAtom (trineLeft secondPhase) + complexAtom (trineRight thirdPhase))
        - ((trineMarginRankThree : ℝ) : ℂ) • (1 : Matrix (Fin 3) (Fin 3) ℂ)).det = 0 := by
  rw [trineMixed_spectrum hne]
  refine Or.inr (Or.inr ?_)
  rw [trineMarginRankThree, rootFiveC]
  push_cast
  ring

/-- **The trine margin, pinned to a rational window**: `3/4 < 3 − √5 < 7/9`.
Rational certificates only — `(9/4)² = 81/16 > 5` above (`81 > 80`) and
`(20/9)² = 400/81 < 5` below (`400 < 405`). Both are tight, and the window is
bounded away from `1` by more than `2/9`: the refutation is robust, not
marginal. -/
theorem trineMargin_window :
    3 / 4 < trineMarginRankThree ∧ trineMarginRankThree < 7 / 9 := by
  have hsq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hpos : (0 : ℝ) < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
  rw [trineMarginRankThree]
  refine ⟨?_, ?_⟩
  · nlinarith [hsq, hpos]
  · nlinarith [hsq, hpos]

theorem trineMargin_lt_one : trineMarginRankThree < 1 := by
  have hwindow := trineMargin_window
  linarith [hwindow.2]

/-! ### The rank-two sharp constant, as an eigenvalue -/

/-- The shifted `2 × 2` excess determinant of a pair, in Gram data: the
characteristic polynomial of the pair's Gram matrix. -/
theorem pairGap_shifted_det (firstVec secondVec : Fin 2 → ℂ) (shift : ℂ) :
    (complexAtom firstVec + complexAtom secondVec
        - shift • (1 : Matrix (Fin 2) (Fin 2) ℂ)).det
      = shift ^ 2 - shift * (star firstVec ⬝ᵥ firstVec + star secondVec ⬝ᵥ secondVec)
        + ((star firstVec ⬝ᵥ firstVec) * (star secondVec ⬝ᵥ secondVec)
          - (star firstVec ⬝ᵥ secondVec) * (star secondVec ⬝ᵥ firstVec)) := by
  simp only [Matrix.det_fin_two, Matrix.add_apply, Matrix.sub_apply,
    Matrix.smul_apply, smul_eq_mul, complexAtom_apply, Matrix.one_apply,
    dotProduct, Fin.sum_univ_two, Pi.star_apply, RCLike.star_def]
  norm_num
  ring

/-- **The SIC pair's characteristic polynomial**: `z² − 4z + 8/3`, whose roots are
`2 ± 2/√3`. Every pair of the `(4,2)` witness has the same one — equiangularity. -/
theorem sicPair_shifted_det {firstIdx secondIdx : Fin 4} (hne : firstIdx ≠ secondIdx)
    (shift : ℂ) :
    (complexAtom (sicAtom firstIdx) + complexAtom (sicAtom secondIdx)
        - shift • (1 : Matrix (Fin 2) (Fin 2) ℂ)).det
      = shift ^ 2 - 4 * shift + 8 / 3 := by
  rw [pairGap_shifted_det, sicNorm, sicNorm, sicOverlap hne]
  ring

/-- The sharp complex constant at rank two: `α₂ = 2 − 2/√3 ≈ 0.845299`. Proven
sharp for `k = 2` in the literature (Nesterenko, arXiv:2604.24087, with equality
exactly when `4 ∣ m` and the Hopf image clusters at the tetrahedron vertices);
the `m = 4` witness is `sicDesign` in `Gtz/Complex/ComplexWitness.lean`. -/
noncomputable def alphaRankTwo : ℝ := 2 - 2 / Real.sqrt 3

theorem alphaRankTwo_isRoot :
    alphaRankTwo ^ 2 - 4 * alphaRankTwo + 8 / 3 = 0 := by
  have hsq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hpos : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  rw [alphaRankTwo]
  field_simp
  nlinarith [hsq, hpos]

/-- **`α₂ = 2 − 2/√3` IS the least eigenvalue of the SIC's best pair** — the
exact algebraic value behind the repo's determinant certificate `−1/3`. Turning
the sign fact into the sharp constant. -/
theorem sicPair_det_at_alphaRankTwo {firstIdx secondIdx : Fin 4}
    (hne : firstIdx ≠ secondIdx) :
    (complexAtom (sicAtom firstIdx) + complexAtom (sicAtom secondIdx)
        - ((alphaRankTwo : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)).det = 0 := by
  rw [sicPair_shifted_det hne]
  have hcast : ((alphaRankTwo ^ 2 - 4 * alphaRankTwo + 8 / 3 : ℝ) : ℂ) = 0 := by
    rw [alphaRankTwo_isRoot]
    simp
  push_cast at hcast
  linear_combination hcast

/-- **`α₂` in a rational window**: `5/6 < α₂ < 9/10`, inherited from the repo's
`complex_sic_slack_window`. -/
theorem alphaRankTwo_window : 5 / 6 < alphaRankTwo ∧ alphaRankTwo < 9 / 10 := by
  obtain ⟨hlow, hhigh⟩ := complex_sic_slack_window
  rw [alphaRankTwo]
  exact ⟨by linarith, by linarith⟩

/-! ## The mechanism of the real-versus-complex separation

The rank-three subset test sees the ground field through exactly ONE real scalar.
Write `G_C` for the Gram matrix of a triple and `T = <g0,g1><g1,g2><g2,g0>` for its
Bargmann triangle invariant. Then

  `det(G_C − z·I) = MODULUS BUDGET(z) + 2·Re T`,

where the budget is built only from leverages and overlap MODULI — data that a
real and a complex configuration can share exactly. Over `ℝ` the invariant `T` is
a product of three reals, so `Re T = ±|T|` is forced EXTREMAL; over `ℂ` it can sit
anywhere in `[−|T|, |T|]`. The separating scalar is therefore the PHASE DEFECT
`|T|² − (Re T)² = (Im T)²`, zero for every real configuration.

Both `(6,3)` designs below have a NEGATIVE modulus budget, so neither is refuted
or rescued by moduli. The real icosahedron is rescued by its extremal phase term
`+2·(3/√5)³ ≈ +4.83`; the complex trine is killed because its phase term is
exactly `0`, even though its moduli would permit `+2√3 ≈ +3.46`. That is the
mechanism, in numbers. -/

/-- Hermitian symmetry of the overlap: reversing an overlap conjugates it. -/
theorem starDot_conj {k : ℕ} (leftVec rightVec : Fin k → ℂ) :
    (starRingEnd ℂ) (star leftVec ⬝ᵥ rightVec) = star rightVec ⬝ᵥ leftVec := by
  simp only [dotProduct, map_sum, map_mul, Pi.star_apply, RCLike.star_def,
    Complex.conj_conj]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

/-- The reversed triangle invariant is the conjugate. -/
theorem triangleBargmann_swap {k : ℕ} (firstVec secondVec thirdVec : Fin k → ℂ) :
    triangleBargmann firstVec thirdVec secondVec
      = (starRingEnd ℂ) (triangleBargmann firstVec secondVec thirdVec) := by
  rw [triangleBargmann, triangleBargmann, map_mul, map_mul, starDot_conj,
    starDot_conj, starDot_conj]
  ring

/-- The two orientations of the triangle product add to `2·Re T`. -/
theorem triangleBargmann_add_swap {k : ℕ} (firstVec secondVec thirdVec : Fin k → ℂ) :
    triangleBargmann firstVec secondVec thirdVec
        + triangleBargmann firstVec thirdVec secondVec
      = ((2 * (triangleBargmann firstVec secondVec thirdVec).re : ℝ) : ℂ) := by
  have hswap := triangleBargmann_swap firstVec secondVec thirdVec
  rw [hswap]
  exact Complex.add_conj _

/-- The Gram matrix of a triple of complex vectors. -/
noncomputable def gramTriple {k : ℕ} (firstVec secondVec thirdVec : Fin k → ℂ) :
    Matrix (Fin 3) (Fin 3) ℂ :=
  !![star firstVec ⬝ᵥ firstVec, star firstVec ⬝ᵥ secondVec, star firstVec ⬝ᵥ thirdVec;
     star secondVec ⬝ᵥ firstVec, star secondVec ⬝ᵥ secondVec, star secondVec ⬝ᵥ thirdVec;
     star thirdVec ⬝ᵥ firstVec, star thirdVec ⬝ᵥ secondVec, star thirdVec ⬝ᵥ thirdVec]

/-- The shifted Gram determinant, expanded: three leverage-and-modulus terms and
the two orientations of the triangle product. Pure ring identity. -/
theorem gramTripleExcess_det_expand {k : ℕ} (firstVec secondVec thirdVec : Fin k → ℂ)
    (shift : ℂ) :
    (gramTriple firstVec secondVec thirdVec
        - shift • (1 : Matrix (Fin 3) (Fin 3) ℂ)).det
      = (star firstVec ⬝ᵥ firstVec - shift) * (star secondVec ⬝ᵥ secondVec - shift)
          * (star thirdVec ⬝ᵥ thirdVec - shift)
        - (star firstVec ⬝ᵥ firstVec - shift)
            * ((star secondVec ⬝ᵥ thirdVec) * (star thirdVec ⬝ᵥ secondVec))
        - (star secondVec ⬝ᵥ secondVec - shift)
            * ((star firstVec ⬝ᵥ thirdVec) * (star thirdVec ⬝ᵥ firstVec))
        - (star thirdVec ⬝ᵥ thirdVec - shift)
            * ((star firstVec ⬝ᵥ secondVec) * (star secondVec ⬝ᵥ firstVec))
        + (triangleBargmann firstVec secondVec thirdVec
          + triangleBargmann firstVec thirdVec secondVec) := by
  simp [gramTriple, Matrix.det_fin_three, triangleBargmann]
  ring

/-- **THE MECHANISM.** The shifted Gram determinant of a triple is a phase-free
MODULUS BUDGET plus `2·Re T`. Every dependence on the ground field is confined to
that single real number, entering affinely with coefficient `+2`; the budget is
determined by leverages and overlap moduli alone. -/
theorem gramTripleExcess_det_split {k : ℕ} (firstVec secondVec thirdVec : Fin k → ℂ)
    (shift : ℂ) :
    (gramTriple firstVec secondVec thirdVec
        - shift • (1 : Matrix (Fin 3) (Fin 3) ℂ)).det
      = (star firstVec ⬝ᵥ firstVec - shift) * (star secondVec ⬝ᵥ secondVec - shift)
          * (star thirdVec ⬝ᵥ thirdVec - shift)
        - (star firstVec ⬝ᵥ firstVec - shift)
            * ((star secondVec ⬝ᵥ thirdVec) * (star thirdVec ⬝ᵥ secondVec))
        - (star secondVec ⬝ᵥ secondVec - shift)
            * ((star firstVec ⬝ᵥ thirdVec) * (star thirdVec ⬝ᵥ firstVec))
        - (star thirdVec ⬝ᵥ thirdVec - shift)
            * ((star firstVec ⬝ᵥ secondVec) * (star secondVec ⬝ᵥ firstVec))
        + ((2 * (triangleBargmann firstVec secondVec thirdVec).re : ℝ) : ℂ) := by
  rw [gramTripleExcess_det_expand, triangleBargmann_add_swap]

/-- **The phase defect** — the separating scalar. `|T|² − (Re T)²` for the
Bargmann triangle invariant `T` of a triple: gauge-invariant, one multiplication
off the Gram matrix, and the complete field-sensitive coordinate of the
rank-three test. -/
noncomputable def bargmannPhaseDefect {k : ℕ} (firstVec secondVec thirdVec : Fin k → ℂ) :
    ℝ :=
  Complex.normSq (triangleBargmann firstVec secondVec thirdVec)
    - (triangleBargmann firstVec secondVec thirdVec).re ^ 2

theorem bargmannPhaseDefect_eq_imSq {k : ℕ} (firstVec secondVec thirdVec : Fin k → ℂ) :
    bargmannPhaseDefect firstVec secondVec thirdVec
      = (triangleBargmann firstVec secondVec thirdVec).im ^ 2 := by
  rw [bargmannPhaseDefect, Complex.normSq_apply]
  ring

theorem bargmannPhaseDefect_nonneg {k : ℕ} (firstVec secondVec thirdVec : Fin k → ℂ) :
    0 ≤ bargmannPhaseDefect firstVec secondVec thirdVec := by
  rw [bargmannPhaseDefect_eq_imSq]
  positivity

/-- **The real side takes the separating value, with no hypotheses.** Every real
triple has phase defect exactly `0` — its invariant is real, hence phase-extremal,
hence its modulus budget is decided by the sign of `T` alone. -/
theorem realTriple_phaseDefect_zero {k : ℕ} (firstVec secondVec thirdVec : Fin k → ℝ) :
    bargmannPhaseDefect (complexify firstVec) (complexify secondVec)
      (complexify thirdVec) = 0 := by
  rw [bargmannPhaseDefect_eq_imSq, triangleBargmann, starDot_complexify,
    starDot_complexify, starDot_complexify, ← Complex.ofReal_mul,
    ← Complex.ofReal_mul, Complex.ofReal_im]
  norm_num

/-! ### The complex trine's binding triple: phase term exactly zero -/

theorem trineOverlap_leftZero_leftOne :
    star (trineLeft 0) ⬝ᵥ trineLeft 1 = 2 + omegaRoot := by
  simp [dotProduct, Fin.sum_univ_three, trineLeft, Pi.star_apply, RCLike.star_def,
    topAmpC_conj, omegaPow_zero, omegaPow_one]
  linear_combination topAmpC_sq

theorem trineOverlap_leftOne_leftZero :
    star (trineLeft 1) ⬝ᵥ trineLeft 0 = 2 + omegaRoot ^ 2 := by
  simp [dotProduct, Fin.sum_univ_three, trineLeft, Pi.star_apply, RCLike.star_def,
    topAmpC_conj, omegaPow_zero, omegaPow_one, omegaRoot_conj_eq]
  linear_combination topAmpC_sq

theorem trineOverlap_leftZero_rightZero :
    star (trineLeft 0) ⬝ᵥ trineRight 0 = 1 := by
  simp [dotProduct, Fin.sum_univ_three, trineLeft, trineRight, Pi.star_apply,
    RCLike.star_def, topAmpC_conj, omegaPow_zero]

theorem trineOverlap_rightZero_leftZero :
    star (trineRight 0) ⬝ᵥ trineLeft 0 = 1 := by
  simp [dotProduct, Fin.sum_univ_three, trineLeft, trineRight, Pi.star_apply,
    RCLike.star_def, topAmpC_conj, omegaPow_zero]

theorem trineOverlap_leftOne_rightZero :
    star (trineLeft 1) ⬝ᵥ trineRight 0 = omegaRoot ^ 2 := by
  simp [dotProduct, Fin.sum_univ_three, trineLeft, trineRight, Pi.star_apply,
    RCLike.star_def, topAmpC_conj, omegaPow_zero, omegaPow_one, omegaRoot_conj_eq]

theorem trineOverlap_rightZero_leftOne :
    star (trineRight 0) ⬝ᵥ trineLeft 1 = omegaRoot := by
  simp [dotProduct, Fin.sum_univ_three, trineLeft, trineRight, Pi.star_apply,
    RCLike.star_def, topAmpC_conj, omegaPow_zero, omegaPow_one]

/-- The within-trine overlap modulus is `3`. -/
theorem trineOverlapModulus_withinTrine :
    (star (trineLeft 0) ⬝ᵥ trineLeft 1) * (star (trineLeft 1) ⬝ᵥ trineLeft 0) = 3 := by
  rw [trineOverlap_leftZero_leftOne, trineOverlap_leftOne_leftZero]
  linear_combination (2 : ℂ) * omegaRoot_sum + omegaRoot_cube

/-- The across-trine overlap moduli are `1`. -/
theorem trineOverlapModulus_acrossFirst :
    (star (trineLeft 0) ⬝ᵥ trineRight 0) * (star (trineRight 0) ⬝ᵥ trineLeft 0) = 1 := by
  rw [trineOverlap_leftZero_rightZero, trineOverlap_rightZero_leftZero]
  norm_num

theorem trineOverlapModulus_acrossSecond :
    (star (trineLeft 1) ⬝ᵥ trineRight 0) * (star (trineRight 0) ⬝ᵥ trineLeft 1) = 1 := by
  rw [trineOverlap_leftOne_rightZero, trineOverlap_rightZero_leftOne]
  linear_combination omegaRoot_cube

/-- The binding triple's Bargmann invariant is `1 + 2ω²`. -/
theorem trineTriple_bargmann :
    triangleBargmann (trineLeft 0) (trineLeft 1) (trineRight 0) = 1 + 2 * omegaRoot ^ 2 := by
  rw [triangleBargmann, trineOverlap_leftZero_leftOne, trineOverlap_leftOne_rightZero,
    trineOverlap_rightZero_leftZero]
  linear_combination omegaRoot_cube

/-- **The phase term of the complex trine is exactly zero.** `Re(1 + 2ω²) = 0` —
the invariant sits at the exact midpoint of the phase circle, the one value a
real configuration can never take. -/
theorem trineTriple_bargmann_re :
    (triangleBargmann (trineLeft 0) (trineLeft 1) (trineRight 0)).re = 0 := by
  rw [trineTriple_bargmann, omegaRoot_sq]
  simp [Complex.add_re, Complex.mul_re, Complex.conj_re, Complex.conj_im, omegaRoot_re]

theorem trineTriple_bargmann_im :
    (triangleBargmann (trineLeft 0) (trineLeft 1) (trineRight 0)).im = -Real.sqrt 3 := by
  rw [trineTriple_bargmann, omegaRoot_sq]
  simp [Complex.add_im, Complex.mul_im, Complex.conj_re, Complex.conj_im,
    omegaRoot_re, omegaRoot_im]
  ring

/-- **The complex trine's phase defect is `3`** — maximal, since `|T|² = 3` and
`Re T = 0`. Compare `realTriple_phaseDefect_zero`: this single number is the whole
difference between the fields at the binding triple. -/
theorem trineTriple_phaseDefect :
    bargmannPhaseDefect (trineLeft 0) (trineLeft 1) (trineRight 0) = 3 := by
  rw [bargmannPhaseDefect_eq_imSq, trineTriple_bargmann_im]
  have hsq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  nlinarith [hsq]

theorem trineTriple_bargmann_normSq :
    Complex.normSq (triangleBargmann (trineLeft 0) (trineLeft 1) (trineRight 0)) = 3 := by
  have hdefect := trineTriple_phaseDefect
  rw [bargmannPhaseDefect, trineTriple_bargmann_re] at hdefect
  simpa using hdefect

/-- **The trine's binding triple, through the mechanism**: modulus budget
`8 − 2 − 2 − 6 = −2`, phase term `0`, determinant `−2`. The refutation is one
hundred per cent phase and zero per cent modulus. -/
theorem trineTriple_gramExcess_det :
    (gramTriple (trineLeft 0) (trineLeft 1) (trineRight 0)
        - (1 : ℂ) • (1 : Matrix (Fin 3) (Fin 3) ℂ)).det = -2 := by
  rw [gramTripleExcess_det_split, trineLeft_leverage, trineLeft_leverage,
    trineRight_leverage, trineOverlapModulus_acrossSecond,
    trineOverlapModulus_acrossFirst, trineOverlapModulus_withinTrine,
    trineTriple_bargmann_re]
  norm_num

/-- **Realness alone would rescue the trine's binding triple.** Its moduli permit
a phase term as large as `2|T| = 2√3 ≈ 3.464`, which is more than the modulus
deficit `2`: at the real-extremal phase the determinant obstruction is POSITIVE.
So an argument reading only leverages and overlap MODULI cannot refute this
triple — it fails for one reason only, `Re T = 0`. (A positive determinant is not
by itself domination; what is proven here is that the determinant certificate,
the one that does refute the trine, is destroyed by realness.) -/
theorem trineTriple_realAvatar_det_pos :
    0 < -2 + 2 * Real.sqrt (Complex.normSq
      (triangleBargmann (trineLeft 0) (trineLeft 1) (trineRight 0))) := by
  rw [trineTriple_bargmann_normSq]
  have hlow : (1 : ℝ) < Real.sqrt 3 := by
    rw [show (1:ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  linarith

/-! ### The real icosahedron's binding triple: rescued by its phase -/

theorem icosaDot_zeroTwo : icosaAtom 0 ⬝ᵥ icosaAtom 2 = icosaRadius := by
  simp [icosaAtom, dotProduct, Fin.sum_univ_three]
  linear_combination icosaShort_mul_icosaLong

theorem icosaDot_twoFour : icosaAtom 2 ⬝ᵥ icosaAtom 4 = icosaRadius := by
  simp [icosaAtom, dotProduct, Fin.sum_univ_three]
  linear_combination icosaShort_mul_icosaLong

theorem icosaDot_fourZero : icosaAtom 4 ⬝ᵥ icosaAtom 0 = icosaRadius := by
  simp [icosaAtom, dotProduct, Fin.sum_univ_three]
  linear_combination icosaShort_mul_icosaLong

/-- **The maximal real equiangular design's phase defect is `0`** — free, by
realness. -/
theorem icosaTriple_phaseDefect :
    bargmannPhaseDefect (complexify (icosaAtom 0)) (complexify (icosaAtom 2))
      (complexify (icosaAtom 4)) = 0 :=
  realTriple_phaseDefect_zero (icosaAtom 0) (icosaAtom 2) (icosaAtom 4)

/-- The real triple's invariant is `(3/√5)³`, extremal and positive. -/
theorem icosaTriple_bargmann :
    triangleBargmann (complexify (icosaAtom 0)) (complexify (icosaAtom 2))
      (complexify (icosaAtom 4)) = ((icosaRadius ^ 3 : ℝ) : ℂ) := by
  rw [triangleBargmann, starDot_complexify, starDot_complexify, starDot_complexify,
    icosaDot_zeroTwo, icosaDot_twoFour, icosaDot_fourZero, ← Complex.ofReal_mul,
    ← Complex.ofReal_mul]
  norm_num
  ring

theorem icosaTriple_bargmann_re :
    (triangleBargmann (complexify (icosaAtom 0)) (complexify (icosaAtom 2))
      (complexify (icosaAtom 4))).re = icosaRadius ^ 3 := by
  rw [icosaTriple_bargmann, Complex.ofReal_re]

theorem icosaTriple_leverage (index : Fin 6) :
    star (complexify (icosaAtom index)) ⬝ᵥ complexify (icosaAtom index) = 3 := by
  rw [starDot_complexify, icosaAtom_leverage]
  norm_num

theorem icosaOverlapModulus_zeroTwo :
    (star (complexify (icosaAtom 0)) ⬝ᵥ complexify (icosaAtom 2))
      * (star (complexify (icosaAtom 2)) ⬝ᵥ complexify (icosaAtom 0))
      = ((icosaRadius ^ 2 : ℝ) : ℂ) := by
  rw [starDot_complexify, starDot_complexify, icosaDot_zeroTwo,
    show icosaAtom 2 ⬝ᵥ icosaAtom 0 = icosaRadius from by
      rw [dotProduct_comm]; exact icosaDot_zeroTwo,
    ← Complex.ofReal_mul]
  norm_num
  ring

theorem icosaOverlapModulus_twoFour :
    (star (complexify (icosaAtom 2)) ⬝ᵥ complexify (icosaAtom 4))
      * (star (complexify (icosaAtom 4)) ⬝ᵥ complexify (icosaAtom 2))
      = ((icosaRadius ^ 2 : ℝ) : ℂ) := by
  rw [starDot_complexify, starDot_complexify, icosaDot_twoFour,
    show icosaAtom 4 ⬝ᵥ icosaAtom 2 = icosaRadius from by
      rw [dotProduct_comm]; exact icosaDot_twoFour,
    ← Complex.ofReal_mul]
  norm_num
  ring

theorem icosaOverlapModulus_zeroFour :
    (star (complexify (icosaAtom 0)) ⬝ᵥ complexify (icosaAtom 4))
      * (star (complexify (icosaAtom 4)) ⬝ᵥ complexify (icosaAtom 0))
      = ((icosaRadius ^ 2 : ℝ) : ℂ) := by
  rw [starDot_complexify, starDot_complexify,
    show icosaAtom 0 ⬝ᵥ icosaAtom 4 = icosaRadius from by
      rw [dotProduct_comm]; exact icosaDot_fourZero,
    icosaDot_fourZero, ← Complex.ofReal_mul]
  norm_num
  ring

/-- **The real icosahedron's binding triple, through the same mechanism**: modulus
budget `8 − 6·(9/5) = −14/5 < 0`, phase term `+2·(3/√5)³`, determinant
`−14/5 + 2·(3/√5)³ > 0`. The moduli alone would REFUTE this triple; it is the
extremal real phase, and nothing else, that makes it dominate. -/
theorem icosaTriple_gramExcess_det :
    (gramTriple (complexify (icosaAtom 0)) (complexify (icosaAtom 2))
        (complexify (icosaAtom 4)) - (1 : ℂ) • (1 : Matrix (Fin 3) (Fin 3) ℂ)).det
      = ((8 - 6 * icosaRadius ^ 2 + 2 * icosaRadius ^ 3 : ℝ) : ℂ) := by
  rw [gramTripleExcess_det_split, icosaTriple_leverage, icosaTriple_leverage,
    icosaTriple_leverage, icosaOverlapModulus_twoFour, icosaOverlapModulus_zeroFour,
    icosaOverlapModulus_zeroTwo, icosaTriple_bargmann_re]
  push_cast
  ring

/-- The real budget is negative: `8 − 6·(9/5) = −14/5`. -/
theorem icosaTriple_modulusBudget_neg : 8 - 6 * icosaRadius ^ 2 < 0 := by
  rw [icosaRadius_sq]
  norm_num

/-- The phase term overturns it. -/
theorem icosaTriple_gramExcess_det_pos :
    0 < 8 - 6 * icosaRadius ^ 2 + 2 * icosaRadius ^ 3 := by
  nlinarith [icosaRadius_sq, icosaRadius_lower, icosaRadius_pos]

/-- **THE SEPARATION, ASSEMBLED.** One named scalar, computed on both sides at the
binding triple of a `(6,3)` design:

* every real triple has phase defect `0` (no hypotheses at all);
* the maximal real equiangular design has modulus budget `−14/5 < 0` yet a
  POSITIVE excess determinant — rescued entirely by its extremal real phase;
* the complex trine has phase defect `3` and its phase term is exactly `0`, so
  its determinant is `−2 < 0` — while its own moduli would have permitted
  `−2 + 2√3 > 0`.

So the field is consumed at exactly one place, and it is not the moduli: the
`(6,3)` complex refutation is phase-mediated, and any argument that reads only
leverages and overlap moduli cannot decide it. -/
theorem realness_separation_mechanism :
    (∀ (k : ℕ) (firstVec secondVec thirdVec : Fin k → ℝ),
        bargmannPhaseDefect (complexify firstVec) (complexify secondVec)
          (complexify thirdVec) = 0)
      ∧ bargmannPhaseDefect (trineLeft 0) (trineLeft 1) (trineRight 0) = 3
      ∧ 8 - 6 * icosaRadius ^ 2 < 0
      ∧ 0 < 8 - 6 * icosaRadius ^ 2 + 2 * icosaRadius ^ 3
      ∧ (gramTriple (trineLeft 0) (trineLeft 1) (trineRight 0)
          - (1 : ℂ) • (1 : Matrix (Fin 3) (Fin 3) ℂ)).det = -2
      ∧ 0 < -2 + 2 * Real.sqrt (Complex.normSq
          (triangleBargmann (trineLeft 0) (trineLeft 1) (trineRight 0))) :=
  ⟨fun _ firstVec secondVec thirdVec =>
      realTriple_phaseDefect_zero firstVec secondVec thirdVec,
    trineTriple_phaseDefect, icosaTriple_modulusBudget_neg,
    icosaTriple_gramExcess_det_pos, trineTriple_gramExcess_det,
    trineTriple_realAvatar_det_pos⟩

/-! ## The honest ledger, per rank

Status vocabulary, used literally in the docstrings below.

* **PROVEN** — a theorem in this repository, kernel-checked.
* **PROVEN ELSEWHERE** — a published theorem, cited, not mechanized here.
* **EXACT ELSEWHERE** — an exact algebraic value certified in exact arithmetic
  (sympy / Eisenstein integers) outside the kernel, with its minimal polynomial;
  mechanizable in principle, not mechanized here.
* **MEASURED** — a floating-point optimum, re-verified at 80 working digits with
  exact Cholesky whitening. Never stated as a theorem. Every measured constant
  below records its leverage cap `κ = max_c ‖g_c‖² / k` and its digit count.

The only quantities that appear in theorems are the PROVEN ones. The measured
constants are definitions carrying documentation and are used by nothing. -/

/-- The margin of the repo's padded-SIC `(6,3)` witness: `20/9 − 20√3/27 ≈
0.939222`. **PROVEN** (this file, `paddedMargin_isRoot`) to be the least
eigenvalue of that witness's one-spike block, which is its best subset. -/
noncomputable def paddedMarginRankThree : ℝ := 20 / 9 - 20 * Real.sqrt 3 / 27

/-- The scaled SIC pair's characteristic polynomial: `z² − (40/9)z + 800/243`. -/
theorem scaledSicPair_shifted_det {firstIdx secondIdx : Fin 4}
    (hne : firstIdx ≠ secondIdx) (shift : ℂ) :
    (complexAtom (scaledSic firstIdx) + complexAtom (scaledSic secondIdx)
        - shift • (1 : Matrix (Fin 2) (Fin 2) ℂ)).det
      = shift ^ 2 - (40 / 9) * shift + 800 / 243 := by
  rw [pairGap_shifted_det, scaledSic_norm, scaledSic_norm, scaledSic_overlap hne]
  ring

theorem paddedMargin_isRoot :
    paddedMarginRankThree ^ 2 - (40 / 9) * paddedMarginRankThree + 800 / 243 = 0 := by
  have hsq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  rw [paddedMarginRankThree]
  nlinarith [hsq]

/-- **`20/9 − 20√3/27` IS the least eigenvalue of the padded witness's binding
block** — the exact value of the repo's shipped `(6,3)` complex refutation. -/
theorem scaledSicPair_det_at_paddedMargin {firstIdx secondIdx : Fin 4}
    (hne : firstIdx ≠ secondIdx) :
    (complexAtom (scaledSic firstIdx) + complexAtom (scaledSic secondIdx)
        - ((paddedMarginRankThree : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)).det = 0 := by
  rw [scaledSicPair_shifted_det hne]
  have hcast : ((paddedMarginRankThree ^ 2 - (40 / 9) * paddedMarginRankThree
      + 800 / 243 : ℝ) : ℂ) = 0 := by
    rw [paddedMargin_isRoot]
    simp
  push_cast at hcast
  linear_combination hcast

/-- The padded margin in a rational window: `9/10 < 20/9 − 20√3/27 < 20/21`, on
the certificates `(12/7)² < 3 < (7/4)²`. -/
theorem paddedMargin_window :
    9 / 10 < paddedMarginRankThree ∧ paddedMarginRankThree < 20 / 21 := by
  have hsq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hpos : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  rw [paddedMarginRankThree]
  refine ⟨?_, ?_⟩
  · nlinarith [hsq, hpos]
  · nlinarith [hsq, hpos]

/-- **The rank-3 record improves.** The shared-axis trine's margin `3 − √5` is
strictly below the padded SIC's `20/9 − 20√3/27`, at the same size `m = 6`, with
uniform weights and cap `κ = 1` instead of a leverage-`10` spike pair. -/
theorem trineMargin_lt_paddedMargin :
    trineMarginRankThree < paddedMarginRankThree := by
  obtain ⟨_, htrineHigh⟩ := trineMargin_window
  obtain ⟨hpaddedLow, _⟩ := paddedMargin_window
  linarith

/-- **`2 − 2/√3` is NOT the sharp complex constant beyond rank two.** The trine
refutes weighted `(6,3)` with margin `3 − √5 < 7/9 < 5/6 < α₂`, so the rank-3
constant is strictly smaller than the rank-2 one by more than `1/18`. Any claim
that `2 − 2/√3` is "the sharp complex constant" is a statement about `k = 2`
only. -/
theorem trineMargin_lt_alphaRankTwo : trineMarginRankThree < alphaRankTwo := by
  obtain ⟨_, htrineHigh⟩ := trineMargin_window
  obtain ⟨halphaLow, _⟩ := alphaRankTwo_window
  linarith

/-- The exact `(6,4)` value over ℂ: `6/7`. **EXACT ELSEWHERE** — the Naimark dual
of a rational `(6,2)` design, atoms `√42/14 · v_c` with `v_c ∈ ℤ[√3,√5,i]⁴`,
uniform weights, leverages `24/7` (twice) and `30/7` (four times); all fifteen
`4`-subsets have rational spectra and the four negative excess determinants are
`−425/7`, `−575/49`, `−425/49`, `−275/49`. It is the smallest complex rank-4
refutation KNOWN HERE, and the minimality argument is EQUAL-WEIGHT ONLY: at equal
weights `m = k + 1` is exactly tight at `1` (Naimark dual `(k+1,1)` plus
max-at-least-mean), so `m = k + 2` is the first refutable EQUAL-WEIGHT size.
`ComplexGtzWeighted` quantifies over arbitrary positive weights and the weighted
`m = k + 1` case is OPEN, so no minimality is claimed over the full statement.
Certified in exact arithmetic outside the kernel;
not mechanized here (Mathlib has no `det_fin_four`). -/
def exactValueRankFourAtSix : ℚ := 6 / 7

/-- **The ledger ordering of the values THIS FILE owns**, in order:

  `3 − √5  <  2 − 2/√3  <  6/7  <  20/9 − 20√3/27`
  `0.7639     0.8453       0.8571   0.9392`

trine `(6,3)` (PROVEN here) beats the rank-2 sharp constant `α₂` (PROVEN
elsewhere, sharp for `k = 2`), which beats the exact `(6,4)` value (EXACT
ELSEWHERE), which beats the repo's shipped padded `(6,3)` witness (PROVEN here).
Certificates: `√5 > 20/9`, `(12/7)² < 3 < (7/4)²`.

NOT the whole rank-3 story: the Hesse SIC's `3(1 − cos 2π/9) ≈ 0.701867` is
strictly BELOW every entry of this chain, so the rank-3 record is the Hesse SIC,
not the trine. See `rankThree_recordOrdering` in
`Gtz/Complex/PerRankConstantLedger.lean`, which opens at the record. -/
theorem ledger_ordering :
    trineMarginRankThree < alphaRankTwo
      ∧ alphaRankTwo < (exactValueRankFourAtSix : ℝ)
      ∧ (exactValueRankFourAtSix : ℝ) < paddedMarginRankThree := by
  have hsq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hpos : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hvalue : ((exactValueRankFourAtSix : ℚ) : ℝ) = 6 / 7 := by
    rw [exactValueRankFourAtSix]
    norm_num
  have hne : Real.sqrt 3 ≠ 0 := ne_of_gt hpos
  have hcancel : 2 / Real.sqrt 3 * Real.sqrt 3 = 2 := by field_simp
  have hupper : Real.sqrt 3 < 7 / 4 := by
    rw [show (7 : ℝ) / 4 = Real.sqrt ((7 / 4) ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  refine ⟨trineMargin_lt_alphaRankTwo, ?_, ?_⟩
  · rw [hvalue, alphaRankTwo]
    have hquotPos : (0 : ℝ) < 2 / Real.sqrt 3 := div_pos (by norm_num) hpos
    nlinarith [hcancel, hupper, hquotPos, hpos]
  · rw [hvalue, paddedMarginRankThree]
    nlinarith [hsq, hpos]

/-! ### The rank-3 record beyond `m = 6`, and the trine family

**EXACT ELSEWHERE.** The Hesse SIC — the Weyl–Heisenberg orbit of the fiducial
`(0,1,−1)/√2` in `ℂ³`, `m = 9 = k²`, uniform weights, leverage `3`, equiangular
at `|<u,v>|² = 1/4` — has value `3(1 − cos 2π/9) ≈ 0.701867`, the smallest known
rank-3 complex value. All eighty-four triples split into `72` with charpoly
`8x³ − 72x² + 162x − 81` and `12` rank-deficient ones (charpoly `x(2x−9)²`);
both excess determinants are negative rationals, `−17/8` and `−49/4`.

MECHANIZED SINCE, in `Gtz/Complex/PerRankConstantLedger.lean`: the design itself
(`hesseDesign`), the upper bound `α₃ ≤ 3(1 − cos 2π/9)`
(`complexRankConstantAtMost_three_hesse`), the identification of the bracketed
root with the closed form (`hesseCubicRoot_eq_hesseMargin`), and the strict
comparison with the trine (`hesseMargin_lt_trineMargin`). What remains EXACT
ELSEWHERE is only ATTAINMENT — that the `72` non-degenerate triples all sit
exactly at that value. Only the polynomial facts below are kernel-checked HERE.

Note also: at rank three `d = 3` SICs form a one-parameter family, the
Weyl–Heisenberg orbits of `(0, 1, −e^{it})/√2`, and only the Hesse member
`t = 0` is extremal — its value is the family's strict minimum, attained at the
three Hesse members and nowhere else. The value rises monotonically across the
fundamental domain `t ∈ [0, π/9]` and reaches exactly `3/2` at the far end.

MOST OF THE FAMILY DOES NOT REFUTE. The value crosses `1` at
`t ≈ 8.18968510422°`, so refutation holds only on `t < 8.19°` — about `41 %` of
the fundamental domain — and the majority of `d = 3` SICs DOMINATE. There is
likewise no single "generic" value: sampled members measure anywhere from about
`0.84` (BELOW `α₂`) to `1.5`, and the figures `0.9083` and `0.9687` recorded
earlier were two particular samples, not typical ones. For `k ≥ 4` SICs stop
refuting at all (the `d = 4` SIC measures `2.2111`, the `d = 5` SIC `1.4901` —
both DOMINATE). So "the SIC is extremal at every rank" is false, "the SIC at
rank 3" is ambiguous, and "SICs refute complex GTZ" is true only of a minority
of them — the Hesse point is load-bearing, not representative. -/

theorem hesseCubic_neg_at_seven_tenths :
    8 * (7 / 10 : ℝ) ^ 3 - 72 * (7 / 10) ^ 2 + 162 * (7 / 10) - 81 < 0 := by
  norm_num

theorem hesseCubic_pos_at_seventyOne_hundredths :
    0 < 8 * (71 / 100 : ℝ) ^ 3 - 72 * (71 / 100) ^ 2 + 162 * (71 / 100) - 81 := by
  norm_num

/-- **The Hesse cubic has a root in `(0.70, 0.71)`** — a kernel-checked fact about
the polynomial `8x³ − 72x² + 162x − 81`, bracketing `3(1 − cos 2π/9)` to two
decimals. That this root is the Hesse SIC's margin is EXACT ELSEWHERE, not proven
here. -/
theorem hesseCubic_hasRootIn :
    ∃ margin ∈ Set.Icc (7 / 10 : ℝ) (71 / 100),
      8 * margin ^ 3 - 72 * margin ^ 2 + 162 * margin - 81 = 0 := by
  have hcont : ContinuousOn
      (fun value : ℝ => 8 * value ^ 3 - 72 * value ^ 2 + 162 * value - 81)
      (Set.Icc (7 / 10 : ℝ) (71 / 100)) := by fun_prop
  have hmem : (0 : ℝ) ∈ Set.Icc
      (8 * (7 / 10 : ℝ) ^ 3 - 72 * (7 / 10) ^ 2 + 162 * (7 / 10) - 81)
      (8 * (71 / 100 : ℝ) ^ 3 - 72 * (71 / 100) ^ 2 + 162 * (71 / 100) - 81) := by
    constructor
    · exact le_of_lt hesseCubic_neg_at_seven_tenths
    · exact le_of_lt hesseCubic_pos_at_seventyOne_hundredths
  obtain ⟨margin, hrange, hroot⟩ := intermediate_value_Icc (by norm_num) hcont hmem
  exact ⟨margin, hrange, hroot⟩

/-- **The trine family cubic at general rank.** For the shared-axis trine at rank
`k` — `m = 3(k−1)` atoms `√(k−1)·e_i + ω^j·e_k`, uniform weights, leverage `k` —
the spanning `k`-subsets have charpoly
`x³ − (4k−3)x² + (4k−1)(k−1)x − 3(k−1)²` (times `(x−(k−1))^{k−3}`) and excess
determinant `−(k−1)(k−2)^{k−2}`; the values decrease strictly to `3/4`. Verified
symbolically for `k = 3..12` outside the kernel. This file PROVES the `k = 3`
member: the identity below shows the kernel-checked polynomial
`(3 − z)(z² − 6z + 4)` is exactly `−(z³ − 9z² + 22z − 12)`, the family cubic at
`k = 3`. -/
theorem trineCharpoly_matchesFamilyCubic (shift : ℂ) :
    (3 - shift) * (shift ^ 2 - 6 * shift + 4)
      = -(shift ^ 3 - 9 * shift ^ 2 + 22 * shift - 12) := by
  ring

/-- **The family cubic takes the same value `−9/64` at `x = 3/4` for every rank.**
Pure ring identity in `k`: the linear and quadratic terms in `k` cancel exactly.
This is the algebraic reason the family's values accumulate at `3/4` from above —
the accumulation itself, and the monotone descent `0.7639 → 0.7552 → 0.7527 → …`,
are EXACT ELSEWHERE. -/
theorem trineFamilyCubic_at_threeQuarters (rank : ℝ) :
    (3 / 4 : ℝ) ^ 3 - (4 * rank - 3) * (3 / 4) ^ 2
        + (4 * rank - 1) * (rank - 1) * (3 / 4) - 3 * (rank - 1) ^ 2
      = -9 / 64 := by
  ring

/-- The rank-4 trine cubic `x³ − 13x² + 45x − 27` has a root in `(3/4, 4/5)` —
bracketing the EXACT ELSEWHERE value `0.755183`. -/
theorem trineFamilyCubicRankFour_hasRootIn :
    ∃ margin ∈ Set.Icc (3 / 4 : ℝ) (4 / 5),
      margin ^ 3 - 13 * margin ^ 2 + 45 * margin - 27 = 0 := by
  have hcont : ContinuousOn
      (fun value : ℝ => value ^ 3 - 13 * value ^ 2 + 45 * value - 27)
      (Set.Icc (3 / 4 : ℝ) (4 / 5)) := by fun_prop
  have hmem : (0 : ℝ) ∈ Set.Icc
      ((3 / 4 : ℝ) ^ 3 - 13 * (3 / 4) ^ 2 + 45 * (3 / 4) - 27)
      ((4 / 5 : ℝ) ^ 3 - 13 * (4 / 5) ^ 2 + 45 * (4 / 5) - 27) := by
    constructor <;> norm_num
  obtain ⟨margin, hrange, hroot⟩ := intermediate_value_Icc (by norm_num) hcont hmem
  exact ⟨margin, hrange, hroot⟩

/-- The rank-5 trine cubic `x³ − 17x² + 76x − 48` has a root in `(3/4, 4/5)` —
bracketing the EXACT ELSEWHERE value `0.752697`. -/
theorem trineFamilyCubicRankFive_hasRootIn :
    ∃ margin ∈ Set.Icc (3 / 4 : ℝ) (4 / 5),
      margin ^ 3 - 17 * margin ^ 2 + 76 * margin - 48 = 0 := by
  have hcont : ContinuousOn
      (fun value : ℝ => value ^ 3 - 17 * value ^ 2 + 76 * value - 48)
      (Set.Icc (3 / 4 : ℝ) (4 / 5)) := by fun_prop
  have hmem : (0 : ℝ) ∈ Set.Icc
      ((3 / 4 : ℝ) ^ 3 - 17 * (3 / 4) ^ 2 + 76 * (3 / 4) - 48)
      ((4 / 5 : ℝ) ^ 3 - 17 * (4 / 5) ^ 2 + 76 * (4 / 5) - 48) := by
    constructor <;> norm_num
  obtain ⟨margin, hrange, hroot⟩ := intermediate_value_Icc (by norm_num) hcont hmem
  exact ⟨margin, hrange, hroot⟩

/-! ### Measured constants — NOT theorems

Each definition below is a rational decimal literal standing for a floating-point
optimum. Method: margin `= σ_min(G_C)²` by SVD of the whitened `k × k` block
(never `λ_min` of a squared frame operator); exact analytic gradients validated
against central differences (worst relative error `1.6e-8`); softmax homotopy to
`β = 7e5` then active-set minimax polish; every reported optimum re-verified at
80 working digits with exact Cholesky whitening (pre-whitening frame defect
`≤ 2.2e-15`, post `≈ 2e-81`); weights floored at `1e-12/m`. The underlying
optimisation converges to about `1e-12`, so at most TWELVE significant digits are
claimed for the floor even though the margin of the exhibited design is exact to
30. Each is an UPPER bound on the true rank constant, being an exhibited design.

No theorem uses any of these. -/

/-- **MEASURED, rank 4, cap `κ = 1`** (unit-norm tight frame): `0.713730091356`
at `m = 8`, uniform weights, a four-distance set with coherences
`{0.20791949, 0.31909386, 1/√3, 0.62375848}`, 54 of 70 subsets simultaneously
tight, 16 rank-deficient. 12 digits claimed, 80-digit verified, `κ = 1`. No
closed form found (PSLQ over radical and cosine bases up to tolerance `1e-12`
returned nothing), so this is a decimal, not an identity. -/
noncomputable def measuredRankFourCapOne : ℝ := 0.713730091356

/-- **MEASURED, rank 4, uncapped leverage**: `0.701866670643` — recorded as the
Hesse value reached in rank 4 at `m = 10` with `κ ≈ 2.69`.

**DISPUTED — do not build on this number.** Two independent re-derivations flag
it. (i) It equals the RANK-THREE constant `3(1 − cos 2π/9)` to all twelve
recorded digits (`|diff| = 6.6e-14`), which is the signature of a copied decimal.
(ii) The only mechanism that would make a rank-4 value equal the rank-3 constant
is one-spike padding of the Hesse design, whose value is
`min(0.7018667/(1 − w), 1/w)`; that expression is strictly ABOVE `0.7018667` for
every `w > 0`, and reaching it needs `κ → ∞`, not `κ ≈ 2.69` (at which the
padded value is `0.7738`). Neither re-derivation reproduced `0.701866670643` at
rank 4 by search. Re-derive the design or withdraw the number. -/
noncomputable def measuredRankFourUncapped : ℝ := 0.701866670643

/-- **MEASURED, rank 5, cap `κ = 1`**: `0.674033844339` at `m = 10`, uniform
weights, a three-distance set with coherences exactly
`{3^(−3/2), 1/3, 1/√3}` — an algebraic signature suggesting an exact model over
`ℚ(√3, i)` that has NOT been found. 81 of 252 subsets tight, 90 rank-deficient.
12 digits claimed, 80-digit verified, `κ = 1`. -/
noncomputable def measuredRankFiveCapOne : ℝ := 0.674033844339

/-- **MEASURED, rank 5, cap `κ = 2`**: `0.671543548931` at `m = 10`, maximum
leverage `1.0419·k`. 12 digits claimed, 80-digit verified. -/
noncomputable def measuredRankFiveCapTwo : ℝ := 0.671543548931

/-- **The `(10,5)` claims in the campaign brief are both wrong.** The exact margin
of the real Petersen conference ETF at `(10,5)` is `5 − 5√5/3 ≈ 1.273220`, which
is `> 1`: that design DOMINATES, so `0.8341` is not its best-subset value (its
252 subsets take only the three values `0`, `0.730745`, `1.273220`). The three
inequivalent complex `(10,5)` ETFs likewise dominate (`1.282103`, `1.309061`,
`1.339019`, MEASURED at equiangularity residuals `1.3e-12` and `1.5e-15`), and
the true `(10,5)` complex floor is `0.674034` at `κ = 1` (MEASURED) — `0.156`
BELOW the reported `0.8298`, which is therefore not a minimum either. The kernel
content is the inequality below; the rest of this note is measurement. -/
theorem petersenConferenceMargin_gt_one : 1 < 5 - 5 * Real.sqrt 5 / 3 := by
  have hsq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hpos : (0 : ℝ) < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
  nlinarith [hsq, hpos]

/-- **The ledger, assembled.** What this file proves about the complex side, per
rank, with nothing measured smuggled in:

* rank 2 — `α₂ = 2 − 2/√3 ∈ (5/6, 9/10)` is the least eigenvalue of the SIC's
  best pair (`sicPair_det_at_alphaRankTwo`); sharpness for `k = 2` is PROVEN
  ELSEWHERE;
* rank 3 — weighted `(6,3)` is FALSE over ℂ on a unit-norm tight frame, with
  binding root `3 − √5 ∈ (3/4, 7/9)` (`complexGtzWeighted_six_three_fails_via_trine`,
  `trineMixed_spectrum`), strictly below both the padded witness's
  `20/9 − 20√3/27` and `α₂`;
* the separation — the field is consumed at exactly one scalar, the phase defect
  (`realness_separation_mechanism`).

Ranks 4 and 5 are EXACT ELSEWHERE / MEASURED only; no rank-4 or rank-5 design is
mechanized in this file.

CORRECTION to an earlier reading of this note: a LOWER bound on `α_k` does exist,
at every rank including `k ≥ 3`. `Gtz/Complex/PerRankConstantLedger.lean` proves
`α_k ≥ 1/k` over ℂ by maximal volume, hence `α₃ ≥ 1/3`; the mechanism is
classical (Goreinov–Tyrtyshnikov pseudoskeleton theory) and field-blind. It is
simply not in THIS file. -/
theorem complexLedger_provenPart :
    (∃ firstIdx secondIdx : Fin 4, firstIdx ≠ secondIdx
        ∧ (complexAtom (sicAtom firstIdx) + complexAtom (sicAtom secondIdx)
            - ((alphaRankTwo : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)).det = 0)
      ∧ (5 / 6 < alphaRankTwo ∧ alphaRankTwo < 9 / 10)
      ∧ ¬ ComplexGtzWeighted 6 3
      ∧ (3 / 4 < trineMarginRankThree ∧ trineMarginRankThree < 7 / 9)
      ∧ trineMarginRankThree < paddedMarginRankThree
      ∧ trineMarginRankThree < alphaRankTwo :=
  ⟨⟨0, 1, by decide, sicPair_det_at_alphaRankTwo (by decide)⟩,
    alphaRankTwo_window, complexGtzWeighted_six_three_fails_via_trine,
    trineMargin_window, trineMargin_lt_paddedMargin, trineMargin_lt_alphaRankTwo⟩

/-! ## SCOPE NOTE: what the kernel here contains, and what it does not

Every non-domination claim in this file IS mechanized: a characteristic polynomial
computed by `ring`/`decide` plus a non-PSD certificate (a negative diagonal entry or
a negative determinant). That is enough to prove no subset dominates, which is what
the refutations need.

Three things were once stated here as informal reading rather than as theorems: that a
named root of a characteristic polynomial is the LEAST eigenvalue; that a given subset
is the BEST one; and that `sigma_min(G_C) ^ 2 = lambda_min(S_C)`.

The FIRST TWO are now mechanized, in `Gtz/Complex/PerRankConstantLedger.lean`:
`trineMargin_isGreatest` pins the whole set of achievable shifts at
`(-inf, 3 - sqrt 5]` for EVERY 3-subset (the Loewner form),
`trineBinding_leastEigenvalue` proves `3 - sqrt 5` is the least eigenvalue of the
binding triple in the ordinary sense with an explicit eigenvector, and
`trine_psd_at_margin_iff` characterises the best subsets as exactly the eighteen mixed
triples.

The THIRD is still outside the kernel and is used by nothing: every statement in both
files is in Loewner form, which is what `ComplexDominates` needs. Read the numeric
VALUES in this file as audited measurements attached to mechanized non-domination
facts. -/

end Gtz
