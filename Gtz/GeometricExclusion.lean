/-
# Geometric exclusion: the Nullstellensatz certificates consumed in geometry

The certificate half of the FrameEncoding bridge. The `Certs/*` payloads
exclude points of a POLYNOMIAL variety; the geometric layer speaks in conic
tightness, polar-normal criticality, and atom distinctness. This file closes
that gap from the certificate side: each exclusion is restated with
GEOMETRIC hypotheses — the tightness relation at the focal conic (gauge
`ξ = (r,0)`), the `⟨n_j, J·u_i⟩ = 0` leaf criticality that `leaf_tangency`
consumes, plain `≠` for clone-freeness, and a nonzero leverage gate — and
proved by dictionary rewriting (`FrameEncoding`) into the kernel-checked
`linear_combination` certificates. The Rabinowitsch witnesses are
CONSTRUCTED (inverse squared gap from distinctness, inverse gate value from
nondegeneracy), never assumed.

Consumers no longer see polynomials:

* `no_tight_path_four_double_tangency` — no clone-free tight P4 on the
  focal conic with both end leaves angularly critical exists;
* `no_tight_path_three_leaf_tangency_off_pole` — the leaf-corner kill: no
  clone-free tight P3 with a critical head leaf and nondegenerate middle
  gate exists;
* `no_tight_cycle_five_with_path_stress` — no clone-free tight C5 with the
  P5-stress leaf rows exists.

The remaining half of the bridge — "an equality design induces these
geometric facts" — is the open Gordan/IFT + stress-classification step.
-/
import Mathlib
import Gtz.FrameEncoding
import Gtz.Certs.PFourCertificate
import Gtz.Certs.CFiveCertificate

namespace Gtz

open Matrix

/-- Distinct planar points have a positive squared gap. -/
theorem planar_gap_pos_of_ne {firstCos firstSin secondCos secondSin : ℝ}
    (hdistinct : (firstCos, firstSin) ≠ (secondCos, secondSin)) :
    0 < (firstCos - secondCos) ^ 2 + (firstSin - secondSin) ^ 2 := by
  by_contra hnonpos
  push Not at hnonpos
  have hcosSq : (firstCos - secondCos) ^ 2 = 0 :=
    le_antisymm (by linarith [sq_nonneg (firstSin - secondSin)]) (sq_nonneg _)
  have hsinSq : (firstSin - secondSin) ^ 2 = 0 :=
    le_antisymm (by linarith [sq_nonneg (firstCos - secondCos)]) (sq_nonneg _)
  have hcosEq : firstCos = secondCos :=
    sub_eq_zero.mp (pow_eq_zero_iff (by norm_num : (2:ℕ) ≠ 0) |>.mp hcosSq)
  have hsinEq : firstSin = secondSin :=
    sub_eq_zero.mp (pow_eq_zero_iff (by norm_num : (2:ℕ) ≠ 0) |>.mp hsinSq)
  exact hdistinct (by rw [hcosEq, hsinEq])

/-- **The Rabinowitsch clone guard, constructed**: distinctness of two unit
atoms yields the certificate's inverse-gap witness row — the guard is a
theorem of the geometry, not an extra hypothesis. -/
theorem clone_guard_of_ne {firstCos firstSin secondCos secondSin : ℝ}
    (hdistinct : (firstCos, firstSin) ≠ (secondCos, secondSin)) :
    ∃ witness : ℝ,
      firstCos ^ 2 * witness - 2 * firstCos * secondCos * witness
        + firstSin ^ 2 * witness - 2 * firstSin * secondSin * witness
        + secondCos ^ 2 * witness + secondSin ^ 2 * witness - 1 = 0 := by
  have hgapPos := planar_gap_pos_of_ne hdistinct
  refine ⟨((firstCos - secondCos) ^ 2 + (firstSin - secondSin) ^ 2)⁻¹, ?_⟩
  have hcancel := mul_inv_cancel₀ (ne_of_gt hgapPos)
  linear_combination hcancel

/-- **The pole guard, constructed**: a nonzero gate value yields the
certificate's inverse witness row. -/
theorem pole_guard_of_gate {gateValue : ℝ} (hgate : gateValue ≠ 0) :
    ∃ witness : ℝ, gateValue * witness - 1 = 0 :=
  ⟨gateValue⁻¹, by rw [mul_inv_cancel₀ hgate, sub_self]⟩

/-- **No clone-free tight P4 with double leaf tangency** (geometric form).
Four unit atoms on the focal conic (gauge `ξ = (moment, 0)`), the three
path edges tight, BOTH end leaves angularly critical against their
partners, and the three guarded pairs distinct — contradiction. This is
the P4 exclusion certificate consumed through the FrameEncoding
dictionary: the kernel half of "no full-support asymmetric P4 equality
design exists", now stated without a single cleared polynomial. -/
theorem no_tight_path_four_double_tangency
    {firstCos firstSin secondCos secondSin thirdCos thirdSin fourthCos
      fourthSin moment : ℝ}
    (hfirstUnit : firstCos ^ 2 + firstSin ^ 2 = 1)
    (hsecondUnit : secondCos ^ 2 + secondSin ^ 2 = 1)
    (hthirdUnit : thirdCos ^ 2 + thirdSin ^ 2 = 1)
    (hfourthUnit : fourthCos ^ 2 + fourthSin ^ 2 = 1)
    (htightFirstSecond : (1 + (firstCos * secondCos + firstSin * secondSin)) / 2
      = (1/2 + moment * firstCos) * (1/2 + moment * secondCos))
    (htightSecondThird : (1 + (secondCos * thirdCos + secondSin * thirdSin)) / 2
      = (1/2 + moment * secondCos) * (1/2 + moment * thirdCos))
    (htightThirdFourth : (1 + (thirdCos * fourthCos + thirdSin * fourthSin)) / 2
      = (1/2 + moment * thirdCos) * (1/2 + moment * fourthCos))
    (hfirstCritical : polarNormal ![moment, 0] ![secondCos, secondSin]
        (1/2 + moment * secondCos) ⬝ᵥ rotateQuarter ![firstCos, firstSin] = 0)
    (hfourthCritical : polarNormal ![moment, 0] ![thirdCos, thirdSin]
        (1/2 + moment * thirdCos) ⬝ᵥ rotateQuarter ![fourthCos, fourthSin] = 0)
    (hfirstThirdFree : (firstCos, firstSin) ≠ (thirdCos, thirdSin))
    (hsecondThirdFree : (secondCos, secondSin) ≠ (thirdCos, thirdSin))
    (hsecondFourthFree : (secondCos, secondSin) ≠ (fourthCos, fourthSin)) :
    False := by
  obtain ⟨firstThirdWitness, hguardFirstThird⟩ :=
    clone_guard_of_ne hfirstThirdFree
  obtain ⟨secondThirdWitness, hguardSecondThird⟩ :=
    clone_guard_of_ne hsecondThirdFree
  obtain ⟨secondFourthWitness, hguardSecondFourth⟩ :=
    clone_guard_of_ne hsecondFourthFree
  refine p4_geometric_certificate_variety_empty firstCos firstSin secondCos
    secondSin thirdCos thirdSin fourthCos fourthSin moment firstThirdWitness
    secondThirdWitness secondFourthWitness ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · linear_combination hfirstUnit
  · linear_combination hsecondUnit
  · linear_combination hthirdUnit
  · linear_combination hfourthUnit
  · linear_combination 4 * htightFirstSecond
  · linear_combination 4 * htightSecondThird
  · linear_combination 4 * htightThirdFourth
  · linear_combination
      leaf_cleared_eq_criticality firstCos firstSin secondCos secondSin moment
        + 2 * hfirstCritical
  · linear_combination
      leaf_cleared_eq_criticality fourthCos fourthSin thirdCos thirdSin moment
        + 2 * hfourthCritical
  · linear_combination hguardFirstThird
  · linear_combination hguardSecondThird
  · linear_combination hguardSecondFourth

/-- **The leaf-corner kill** (geometric form): no clone-free tight P3 with
a critical head leaf and a nondegenerate middle gate (`D_2 ≠ 0`, finite
leverage at the partner) exists. The 15-term pole/nondegeneracy corner
certificate consumed through the dictionary. -/
theorem no_tight_path_three_leaf_tangency_off_pole
    {firstCos firstSin secondCos secondSin thirdCos thirdSin moment : ℝ}
    (hfirstUnit : firstCos ^ 2 + firstSin ^ 2 = 1)
    (hsecondUnit : secondCos ^ 2 + secondSin ^ 2 = 1)
    (hthirdUnit : thirdCos ^ 2 + thirdSin ^ 2 = 1)
    (htightFirstSecond : (1 + (firstCos * secondCos + firstSin * secondSin)) / 2
      = (1/2 + moment * firstCos) * (1/2 + moment * secondCos))
    (htightSecondThird : (1 + (secondCos * thirdCos + secondSin * thirdSin)) / 2
      = (1/2 + moment * secondCos) * (1/2 + moment * thirdCos))
    (hfirstCritical : polarNormal ![moment, 0] ![secondCos, secondSin]
        (1/2 + moment * secondCos) ⬝ᵥ rotateQuarter ![firstCos, firstSin] = 0)
    (hfirstThirdFree : (firstCos, firstSin) ≠ (thirdCos, thirdSin))
    (hsecondGate : 1 - 2 * moment * secondCos ≠ 0) :
    False := by
  obtain ⟨firstThirdWitness, hguardFirstThird⟩ :=
    clone_guard_of_ne hfirstThirdFree
  obtain ⟨poleWitness, hpoleGuard⟩ := pole_guard_of_gate hsecondGate
  refine leaf_tangency_corner_certificate firstCos firstSin secondCos
    secondSin thirdCos thirdSin moment firstThirdWitness poleWitness
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · linear_combination hfirstUnit
  · linear_combination hsecondUnit
  · linear_combination hthirdUnit
  · linear_combination 4 * htightFirstSecond
  · linear_combination 4 * htightSecondThird
  · linear_combination
      leaf_cleared_eq_criticality firstCos firstSin secondCos secondSin moment
        + 2 * hfirstCritical
  · linear_combination hguardFirstThird
  · linear_combination hpoleGuard

/-- **No clone-free tight C5 with P5-stress leaf rows** (geometric form).
Five unit atoms, the five cycle edges tight, the two P5-stress leaf rows
critical (`g(1,2)` and `g(5,4)`), and the five guarded pairs distinct —
contradiction. The second flagged stratum of the zero-set classification,
consumed through the dictionary. -/
theorem no_tight_cycle_five_with_path_stress
    {firstCos firstSin secondCos secondSin thirdCos thirdSin fourthCos
      fourthSin fifthCos fifthSin moment : ℝ}
    (hfirstUnit : firstCos ^ 2 + firstSin ^ 2 = 1)
    (hsecondUnit : secondCos ^ 2 + secondSin ^ 2 = 1)
    (hthirdUnit : thirdCos ^ 2 + thirdSin ^ 2 = 1)
    (hfourthUnit : fourthCos ^ 2 + fourthSin ^ 2 = 1)
    (hfifthUnit : fifthCos ^ 2 + fifthSin ^ 2 = 1)
    (htightFirstSecond : (1 + (firstCos * secondCos + firstSin * secondSin)) / 2
      = (1/2 + moment * firstCos) * (1/2 + moment * secondCos))
    (htightSecondThird : (1 + (secondCos * thirdCos + secondSin * thirdSin)) / 2
      = (1/2 + moment * secondCos) * (1/2 + moment * thirdCos))
    (htightThirdFourth : (1 + (thirdCos * fourthCos + thirdSin * fourthSin)) / 2
      = (1/2 + moment * thirdCos) * (1/2 + moment * fourthCos))
    (htightFourthFifth : (1 + (fourthCos * fifthCos + fourthSin * fifthSin)) / 2
      = (1/2 + moment * fourthCos) * (1/2 + moment * fifthCos))
    (htightFirstFifth : (1 + (firstCos * fifthCos + firstSin * fifthSin)) / 2
      = (1/2 + moment * firstCos) * (1/2 + moment * fifthCos))
    (hfirstCritical : polarNormal ![moment, 0] ![secondCos, secondSin]
        (1/2 + moment * secondCos) ⬝ᵥ rotateQuarter ![firstCos, firstSin] = 0)
    (hfifthCritical : polarNormal ![moment, 0] ![fourthCos, fourthSin]
        (1/2 + moment * fourthCos) ⬝ᵥ rotateQuarter ![fifthCos, fifthSin] = 0)
    (hfirstThirdFree : (firstCos, firstSin) ≠ (thirdCos, thirdSin))
    (hsecondFourthFree : (secondCos, secondSin) ≠ (fourthCos, fourthSin))
    (hsecondFifthFree : (secondCos, secondSin) ≠ (fifthCos, fifthSin))
    (hthirdFourthFree : (thirdCos, thirdSin) ≠ (fourthCos, fourthSin))
    (hthirdFifthFree : (thirdCos, thirdSin) ≠ (fifthCos, fifthSin)) :
    False := by
  obtain ⟨firstThirdWitness, hguardFirstThird⟩ :=
    clone_guard_of_ne hfirstThirdFree
  obtain ⟨secondFourthWitness, hguardSecondFourth⟩ :=
    clone_guard_of_ne hsecondFourthFree
  obtain ⟨secondFifthWitness, hguardSecondFifth⟩ :=
    clone_guard_of_ne hsecondFifthFree
  obtain ⟨thirdFourthWitness, hguardThirdFourth⟩ :=
    clone_guard_of_ne hthirdFourthFree
  obtain ⟨thirdFifthWitness, hguardThirdFifth⟩ :=
    clone_guard_of_ne hthirdFifthFree
  refine c5_p5stress_geometric_certificate_variety_empty firstCos firstSin
    secondCos secondSin thirdCos thirdSin fourthCos fourthSin fifthCos
    fifthSin moment firstThirdWitness secondFourthWitness secondFifthWitness
    thirdFourthWitness thirdFifthWitness
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · linear_combination hfirstUnit
  · linear_combination hsecondUnit
  · linear_combination hthirdUnit
  · linear_combination hfourthUnit
  · linear_combination hfifthUnit
  · linear_combination 4 * htightFirstSecond
  · linear_combination 4 * htightSecondThird
  · linear_combination 4 * htightThirdFourth
  · linear_combination 4 * htightFourthFifth
  · linear_combination 4 * htightFirstFifth
  · linear_combination
      leaf_cleared_eq_criticality firstCos firstSin secondCos secondSin moment
        + 2 * hfirstCritical
  · linear_combination
      leaf_cleared_eq_criticality fifthCos fifthSin fourthCos fourthSin moment
        + 2 * hfifthCritical
  · linear_combination hguardFirstThird
  · linear_combination hguardSecondFourth
  · linear_combination hguardSecondFifth
  · linear_combination hguardThirdFourth
  · linear_combination hguardThirdFifth

/-- Two planar vectors with equal components are equal. -/
theorem planar_eq_of_components {firstVec secondVec : Fin 2 → ℝ}
    (hzero : firstVec 0 = secondVec 0) (hone : firstVec 1 = secondVec 1) :
    firstVec = secondVec := by
  funext index
  fin_cases index
  · exact hzero
  · exact hone

/-- **The P4 exclusion in direction-vector form** — the face the design-side
machinery (`TightGraph`, `StressFrame`) actually speaks. Atoms are
`Fin 2 → ℝ` unit directions, the moment is a gauge-aligned vector
(`moment 1 = 0`, the `ξ = (r,0)` gauge as an explicit HYPOTHESIS), tightness
and criticality are the native dot-product relations. Reduces to the scalar
form by component expansion. -/
theorem no_tight_path_four_double_tangency_of_directions
    {firstDir secondDir thirdDir fourthDir moment : Fin 2 → ℝ}
    (hgauge : moment 1 = 0)
    (hfirstUnit : firstDir ⬝ᵥ firstDir = 1)
    (hsecondUnit : secondDir ⬝ᵥ secondDir = 1)
    (hthirdUnit : thirdDir ⬝ᵥ thirdDir = 1)
    (hfourthUnit : fourthDir ⬝ᵥ fourthDir = 1)
    (htightFirstSecond : (1 + firstDir ⬝ᵥ secondDir) / 2
      = (1/2 + moment ⬝ᵥ firstDir) * (1/2 + moment ⬝ᵥ secondDir))
    (htightSecondThird : (1 + secondDir ⬝ᵥ thirdDir) / 2
      = (1/2 + moment ⬝ᵥ secondDir) * (1/2 + moment ⬝ᵥ thirdDir))
    (htightThirdFourth : (1 + thirdDir ⬝ᵥ fourthDir) / 2
      = (1/2 + moment ⬝ᵥ thirdDir) * (1/2 + moment ⬝ᵥ fourthDir))
    (hfirstCritical : polarNormal moment secondDir
        (1/2 + moment ⬝ᵥ secondDir) ⬝ᵥ rotateQuarter firstDir = 0)
    (hfourthCritical : polarNormal moment thirdDir
        (1/2 + moment ⬝ᵥ thirdDir) ⬝ᵥ rotateQuarter fourthDir = 0)
    (hfirstThirdFree : firstDir ≠ thirdDir)
    (hsecondThirdFree : secondDir ≠ thirdDir)
    (hsecondFourthFree : secondDir ≠ fourthDir) :
    False := by
  -- component expansion of every vector-form hypothesis
  have hdotExpand : ∀ leftVec rightVec : Fin 2 → ℝ,
      leftVec ⬝ᵥ rightVec
        = leftVec 0 * rightVec 0 + leftVec 1 * rightVec 1 := by
    intro leftVec rightVec
    simp [dotProduct, Fin.sum_univ_two]
  have hmomentDot : ∀ ownDir : Fin 2 → ℝ,
      moment ⬝ᵥ ownDir = moment 0 * ownDir 0 := by
    intro ownDir
    rw [hdotExpand, hgauge]
    ring
  have hcritExpand : ∀ leafDir partnerDir : Fin 2 → ℝ,
      polarNormal ![moment 0, 0] ![partnerDir 0, partnerDir 1]
          (1/2 + moment 0 * partnerDir 0) ⬝ᵥ
          rotateQuarter ![leafDir 0, leafDir 1]
        = polarNormal moment partnerDir
          (1/2 + moment ⬝ᵥ partnerDir) ⬝ᵥ rotateQuarter leafDir := by
    intro leafDir partnerDir
    simp only [polarNormal, rotateQuarter, dotProduct, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [hgauge]
    ring
  have hpairFree : ∀ {leftVec rightVec : Fin 2 → ℝ}, leftVec ≠ rightVec →
      (leftVec 0, leftVec 1) ≠ (rightVec 0, rightVec 1) := by
    intro leftVec rightVec hvecFree hpairEq
    exact hvecFree (planar_eq_of_components
      (congrArg Prod.fst hpairEq) (congrArg Prod.snd hpairEq))
  refine no_tight_path_four_double_tangency
    (firstCos := firstDir 0) (firstSin := firstDir 1)
    (secondCos := secondDir 0) (secondSin := secondDir 1)
    (thirdCos := thirdDir 0) (thirdSin := thirdDir 1)
    (fourthCos := fourthDir 0) (fourthSin := fourthDir 1)
    (moment := moment 0)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    (hpairFree hfirstThirdFree) (hpairFree hsecondThirdFree)
    (hpairFree hsecondFourthFree)
  · rw [hdotExpand] at hfirstUnit; linear_combination hfirstUnit
  · rw [hdotExpand] at hsecondUnit; linear_combination hsecondUnit
  · rw [hdotExpand] at hthirdUnit; linear_combination hthirdUnit
  · rw [hdotExpand] at hfourthUnit; linear_combination hfourthUnit
  · rw [hdotExpand, hmomentDot, hmomentDot] at htightFirstSecond
    linear_combination htightFirstSecond
  · rw [hdotExpand, hmomentDot, hmomentDot] at htightSecondThird
    linear_combination htightSecondThird
  · rw [hdotExpand, hmomentDot, hmomentDot] at htightThirdFourth
    linear_combination htightThirdFourth
  · rw [hcritExpand]; exact hfirstCritical
  · rw [hcritExpand]; exact hfourthCritical

end Gtz
