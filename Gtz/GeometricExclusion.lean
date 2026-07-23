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

end Gtz
