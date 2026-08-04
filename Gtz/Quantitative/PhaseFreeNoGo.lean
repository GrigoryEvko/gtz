/-
# The phase-free no-go: one relation carries all of rank three

The DISC-QE legs (`discriminantTrace`, `discriminantTie`) are polynomials in the
Gram entries, but they do not see those entries individually. Writing

  `excess c   = |g_c|² − 1`,
  `pairing c d = ⟨g_c, g_d⟩²`,
  `triangle a b c = ⟨g_a,g_b⟩⟨g_b,g_c⟩⟨g_a,g_c⟩`,

both legs become polynomials in `excess`, `pairing`, `triangle` alone. These
three families are exactly the invariants of the SIGN GAUGE `g_c ↦ ±g_c`; over
`ℂ` the same three formulas are the invariants of the strictly larger TORUS
gauge `g_c ↦ z_c g_c`, `|z_c| = 1`, with `pairing c d = |⟨g_c,g_d⟩|²` and
`triangle a b c = Re(⟨g_a,g_b⟩⟨g_b,g_c⟩⟨g_c,g_a⟩)` — the Bargmann invariant of
`Gtz.RealnessEngine`. Call a certificate PHASE-FREE when every polynomial in it
is built from these coordinates and every relation it invokes is one that holds
over `ℂ` as well as over `ℝ`.

`isPhaseFreeAdmissible_of_design` lists fifteen such relations and proves that
every all-heavy real design satisfies all of them. Exactly one of them is
weakened on the way: over `ℝ` the triangle invariant obeys the EQUALITY

  `triangle a b c ² = pairing a b · pairing b c · pairing a c`,

whereas over `ℂ` only `≤` survives, the deficit being the squared imaginary part
of the Bargmann invariant. `triangleCap` records the inequality.

**The theorem.** That single weakening is already fatal.
`trineSixData` and `trineSevenData` are explicit RATIONAL points — every
coordinate is one of `1/12, 1/6, 0, 1, 2, 3, 9` — which satisfy all fifteen
relations and at which EVERY ordered triple has `determinantLeg < 0`. So the
phase-free relaxation of `DiscriminantCovering 6` and of `DiscriminantCovering 7`
is FALSE. A Positivstellensatz certificate proves the emptiness of a
semialgebraic set; these points are members of the corresponding set; hence

  **no phase-free certificate of `GtzWeighted 6 3` or `GtzWeighted 7 3` exists,
  at any degree, in any coordinate system.**

The points are not invented: they are the phase-free image of the shared-axis
trine of `Gtz/Complex/SharpConstantLedger.lean` (and of its atom split), whose
twenty triples all fail over `ℂ`. That is what makes them satisfy every relation
valid over `ℂ` — including relations far beyond the fifteen listed here, such as
every higher Bargmann invariant and every rank condition. Enlarging the list
cannot repair the obstruction; only re-imposing the phase defect can.

The obstruction is SHARP, and the argument is two lines. At `trineSixData` every
weight is `1/6` and every excess is `2`, so `parsevalPair` reduces to
`∑_{e ∉ {c,d}} triangle c d e = 0`, while `determinantLeg < 0` at a triple forces
`triangle < pairing-sum − 4`, i.e. `< 5` where `triangle² = 27` and `< 1` where
`triangle² = 3`. Re-imposing `triangle² = pairing·pairing·pairing` therefore
pins every triangle to the NEGATIVE root, and a sum of four strictly negative
numbers is not zero. So at these moduli the phase defect is not merely one of
several missing relations — it is the only one missing.
-/
import Mathlib
import Gtz.Core.Sanity
import Gtz.Quantitative.DiscriminantSystem
import Gtz.Reduction.Reductions

namespace Gtz

open Finset Matrix

/-! ### Phase-free coordinates -/

/-- The sign-gauge (over `ℂ`: torus-gauge) invariants of a weighted design's
Gram matrix, up to triangles. `pairing` is the squared overlap and `triangle`
the Bargmann triangle invariant; both are insensitive to `g_c ↦ ±g_c`. -/
structure PhaseFreeData (size : ℕ) where
  weight : Fin size → ℝ
  excess : Fin size → ℝ
  pairing : Fin size → Fin size → ℝ
  triangle : Fin size → Fin size → Fin size → ℝ

namespace PhaseFreeData

variable {size : ℕ}

/-- The trace leg of DISC-QE, read in phase-free coordinates. Compare
`Gtz.discriminantTrace`, which is this expression with `pairing = ⟨·,·⟩²`. -/
def traceLeg (point : PhaseFreeData size) (pivot pairFirst pairSecond : Fin size) : ℝ :=
  (point.excess pivot * point.excess pairFirst - point.pairing pivot pairFirst)
    + (point.excess pivot * point.excess pairSecond - point.pairing pivot pairSecond)

/-- The determinant leg of DISC-QE, read in phase-free coordinates. Compare
`Gtz.discriminantTie`; the cross term `2⟨g_p,g_a⟩⟨g_a,g_b⟩⟨g_p,g_b⟩` is exactly
`2 · triangle`, and it is the ONLY place a Gram entry survives unsquared. -/
def determinantLeg (point : PhaseFreeData size) (pivot pairFirst pairSecond : Fin size) : ℝ :=
  point.excess pivot
      * (point.excess pairFirst * point.excess pairSecond
          - point.pairing pairFirst pairSecond)
    - (point.excess pairSecond * point.pairing pivot pairFirst
        - 2 * point.triangle pivot pairFirst pairSecond
        + point.excess pairFirst * point.pairing pivot pairSecond)

end PhaseFreeData

/-- **The phase-free relaxation.** Fifteen relations, every one of them valid
for every all-heavy weighted `(size,3)` design over `ℝ` — and, with `pairing` and
`triangle` read as squared modulus and real part of the Bargmann invariant, valid
over `ℂ` as well. The real system satisfies `triangleCap` with EQUALITY; asking
only for the inequality is the whole of the relaxation. -/
structure IsPhaseFreeAdmissible {size : ℕ} (point : PhaseFreeData size) : Prop where
  weightPos : ∀ atomIndex, 0 < point.weight atomIndex
  weightSumOne : ∑ atomIndex, point.weight atomIndex = 1
  excessPos : ∀ atomIndex, 0 < point.excess atomIndex
  traceEqRank : ∑ atomIndex, point.weight atomIndex * (point.excess atomIndex + 1) = 3
  pairingSymm : ∀ first second, point.pairing first second = point.pairing second first
  pairingDiag : ∀ atomIndex, point.pairing atomIndex atomIndex = (point.excess atomIndex + 1) ^ 2
  pairingNonneg : ∀ first second, 0 ≤ point.pairing first second
  pairingCap : ∀ first second,
    point.pairing first second ≤ (point.excess first + 1) * (point.excess second + 1)
  triangleSwap : ∀ first second third,
    point.triangle first second third = point.triangle second first third
  triangleRotate : ∀ first second third,
    point.triangle first second third = point.triangle second third first
  triangleCollapse : ∀ first second,
    point.triangle first first second = (point.excess first + 1) * point.pairing first second
  /-- The diagonal of `Gram · diag(weight) · Gram = Gram`. -/
  parsevalDiag : ∀ atomIndex,
    ∑ other, point.weight other * point.pairing atomIndex other = point.excess atomIndex + 1
  /-- The off-diagonal of `Gram · diag(weight) · Gram = Gram`, multiplied through
  by the pair overlap so as to become phase-free. -/
  parsevalPair : ∀ first second,
    ∑ other, point.weight other * point.triangle first second other
      = point.pairing first second
  /-- The relaxed relation. Over `ℝ` this holds with equality; over `ℂ` the
  deficit is the squared imaginary part of the Bargmann invariant. -/
  triangleCap : ∀ first second third,
    point.triangle first second third ^ 2
      ≤ point.pairing first second * point.pairing second third * point.pairing first third
  /-- Each atom carries at most unit mass: `weight c · |g_c|² ≤ 1`. -/
  leverageCap : ∀ atomIndex, point.weight atomIndex * (point.excess atomIndex + 1) ≤ 1

/-- The phase-free relaxation of `DiscriminantCovering size`: the SAME sentence,
asserted about every admissible phase-free point rather than about every design.
Every certificate that reads the Gram only through the three gauge invariants,
and invokes only relations valid over `ℂ`, proves this stronger statement. -/
def PhaseFreeCovering (size : ℕ) : Prop :=
  ∀ point : PhaseFreeData size, IsPhaseFreeAdmissible point →
    ∃ pivot pairFirst pairSecond : Fin size,
      pivot ≠ pairFirst ∧ pivot ≠ pairSecond ∧ pairFirst ≠ pairSecond
        ∧ 0 ≤ point.traceLeg pivot pairFirst pairSecond
        ∧ 0 ≤ point.determinantLeg pivot pairFirst pairSecond

/-! ### Soundness: every all-heavy real design is an admissible phase-free point -/

variable {size : ℕ}

/-- **Parseval as a bilinear form.** The polarised companion of
`dotProduct_self_eq_sum_weight_mul_sq`: the overlap of any two directions is the
weighted average of the products of their atom projections. -/
theorem dotProduct_eq_sum_weight_mul_pair {rank : ℕ} (D : WeightedDesign size rank)
    (leftVec rightVec : Fin rank → ℝ) :
    leftVec ⬝ᵥ rightVec
      = ∑ atomIndex, D.weight atomIndex
          * ((D.atom atomIndex ⬝ᵥ leftVec) * (D.atom atomIndex ⬝ᵥ rightVec)) := by
  have hidentity : leftVec ⬝ᵥ ((1 : Matrix (Fin rank) (Fin rank) ℝ) *ᵥ rightVec)
      = leftVec ⬝ᵥ rightVec := by rw [Matrix.one_mulVec]
  rw [← hidentity, ← D.isParseval, Matrix.sum_mulVec, dotProduct_sum]
  refine Finset.sum_congr rfl fun atomIndex _ => ?_
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  congr 1
  simp only [atomMatrix, Matrix.vecMulVec, Matrix.mulVec, dotProduct, Matrix.of_apply,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun leftCoord _ =>
    Finset.sum_congr rfl fun rightCoord _ => by ring

/-- The phase-free coordinates of a real design. -/
noncomputable def phaseFreeOfDesign (D : WeightedDesign size 3) : PhaseFreeData size where
  weight := D.weight
  excess := heavyExcess D
  pairing := fun first second => atomPairing D first second ^ 2
  triangle := fun first second third =>
    atomPairing D first second * atomPairing D second third * atomPairing D first third

@[simp] theorem phaseFreeOfDesign_weight (D : WeightedDesign size 3) (atomIndex : Fin size) :
    (phaseFreeOfDesign D).weight atomIndex = D.weight atomIndex := rfl

@[simp] theorem phaseFreeOfDesign_excess (D : WeightedDesign size 3) (atomIndex : Fin size) :
    (phaseFreeOfDesign D).excess atomIndex = heavyExcess D atomIndex := rfl

@[simp] theorem phaseFreeOfDesign_pairing (D : WeightedDesign size 3)
    (first second : Fin size) :
    (phaseFreeOfDesign D).pairing first second = atomPairing D first second ^ 2 := rfl

@[simp] theorem phaseFreeOfDesign_triangle (D : WeightedDesign size 3)
    (first second third : Fin size) :
    (phaseFreeOfDesign D).triangle first second third
      = atomPairing D first second * atomPairing D second third
          * atomPairing D first third := rfl

theorem phaseFreeOfDesign_excess_add_one (D : WeightedDesign size 3) (atomIndex : Fin size) :
    heavyExcess D atomIndex + 1 = leverageOf (D.atom atomIndex) := by
  rw [heavyExcess]; ring

/-- **The trace leg is phase-free.** -/
theorem discriminantTrace_eq_traceLeg (D : WeightedDesign size 3)
    (pivot pairFirst pairSecond : Fin size) :
    discriminantTrace D pivot pairFirst pairSecond
      = (phaseFreeOfDesign D).traceLeg pivot pairFirst pairSecond := rfl

/-- **The determinant leg is phase-free.** The unsquared Gram entries occur only
inside the Bargmann triangle. -/
theorem discriminantTie_eq_determinantLeg (D : WeightedDesign size 3)
    (pivot pairFirst pairSecond : Fin size) :
    discriminantTie D pivot pairFirst pairSecond
      = (phaseFreeOfDesign D).determinantLeg pivot pairFirst pairSecond := by
  simp only [discriminantTie, PhaseFreeData.determinantLeg, phaseFreeOfDesign_excess,
    phaseFreeOfDesign_pairing, phaseFreeOfDesign_triangle]
  ring

/-- **Soundness.** Every all-heavy real design lands in the phase-free
relaxation. This is the direction that makes the no-go below bite: any argument
excluding all admissible phase-free points would in particular exclude every real
design. -/
theorem isPhaseFreeAdmissible_of_design (D : WeightedDesign size 3) (hheavy : AllHeavy D) :
    IsPhaseFreeAdmissible (phaseFreeOfDesign D) := by
  have hlev : ∀ atomIndex : Fin size,
      heavyExcess D atomIndex + 1 = leverageOf (D.atom atomIndex) :=
    phaseFreeOfDesign_excess_add_one D
  have hpairSelf : ∀ atomIndex : Fin size,
      atomPairing D atomIndex atomIndex = heavyExcess D atomIndex + 1 := by
    intro atomIndex; rw [atomPairing_self, hlev]
  -- the bilinear Parseval identity, read on two atoms
  have hbilinear : ∀ first second : Fin size,
      ∑ other, D.weight other * (atomPairing D first other * atomPairing D second other)
        = atomPairing D first second := by
    intro first second
    rw [atomPairing, dotProduct_eq_sum_weight_mul_pair D (D.atom first) (D.atom second)]
    exact Finset.sum_congr rfl fun other _ => by
      rw [atomPairing, atomPairing, dotProduct_comm (D.atom first) (D.atom other),
        dotProduct_comm (D.atom second) (D.atom other)]
  have hparsevalDiag : ∀ atomIndex : Fin size,
      ∑ other, D.weight other * atomPairing D atomIndex other ^ 2
        = heavyExcess D atomIndex + 1 := by
    intro atomIndex
    rw [← hpairSelf atomIndex, ← hbilinear atomIndex atomIndex]
    exact Finset.sum_congr rfl fun other _ => by ring
  refine
    { weightPos := D.weight_pos
      weightSumOne := D.weight_sum_one
      excessPos := fun atomIndex => by
        have := hheavy atomIndex
        simp only [phaseFreeOfDesign_excess, heavyExcess]; linarith
      traceEqRank := ?_
      pairingSymm := fun first second => by
        simp only [phaseFreeOfDesign_pairing, atomPairing_comm D first second]
      pairingDiag := fun atomIndex => by
        simp only [phaseFreeOfDesign_pairing, phaseFreeOfDesign_excess]
        rw [hpairSelf atomIndex]
      pairingNonneg := fun _ _ => sq_nonneg _
      pairingCap := ?_
      triangleSwap := fun first second third => by
        simp only [phaseFreeOfDesign_triangle]
        rw [atomPairing_comm D second first]; ring
      triangleRotate := fun first second third => by
        simp only [phaseFreeOfDesign_triangle]
        rw [atomPairing_comm D third first, atomPairing_comm D second first]; ring
      triangleCollapse := fun first second => by
        simp only [phaseFreeOfDesign_triangle, phaseFreeOfDesign_pairing,
          phaseFreeOfDesign_excess]
        rw [hpairSelf first]; ring
      parsevalDiag := by
        intro atomIndex
        simpa only [phaseFreeOfDesign_weight, phaseFreeOfDesign_pairing,
          phaseFreeOfDesign_excess] using hparsevalDiag atomIndex
      parsevalPair := ?_
      triangleCap := fun first second third => le_of_eq (by
        simp only [phaseFreeOfDesign_triangle, phaseFreeOfDesign_pairing]; ring)
      leverageCap := ?_ }
  · -- traceEqRank
    have hsum := sum_weighted_leverage D
    simp only [phaseFreeOfDesign_weight, phaseFreeOfDesign_excess]
    rw [show (∑ atomIndex, D.weight atomIndex * (heavyExcess D atomIndex + 1))
          = ∑ atomIndex, D.weight atomIndex * leverageOf (D.atom atomIndex) from
        Finset.sum_congr rfl fun atomIndex _ => by rw [hlev]]
    exact_mod_cast hsum
  · -- pairingCap : Cauchy-Schwarz
    intro first second
    simp only [phaseFreeOfDesign_pairing, phaseFreeOfDesign_excess]
    rw [hlev, hlev]
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (D.atom first) (D.atom second)
    rw [atomPairing, dotProduct, leverageOf, leverageOf]
    simp only [pow_two] at hcs ⊢
    nlinarith [hcs]
  · -- parsevalPair
    intro first second
    simp only [phaseFreeOfDesign_weight, phaseFreeOfDesign_triangle,
      phaseFreeOfDesign_pairing]
    rw [show (∑ other, D.weight other * (atomPairing D first second
              * atomPairing D second other * atomPairing D first other))
          = atomPairing D first second
              * ∑ other, D.weight other
                  * (atomPairing D second other * atomPairing D first other) from by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun other _ => by ring]
    rw [hbilinear second first, atomPairing_comm D second first]
    ring
  · -- leverageCap : drop every term but the diagonal one in parsevalDiag
    intro atomIndex
    simp only [phaseFreeOfDesign_weight, phaseFreeOfDesign_excess]
    have hexcess : 0 < heavyExcess D atomIndex + 1 := by
      have := hheavy atomIndex; simp only [heavyExcess]; linarith
    have hdiag := hparsevalDiag atomIndex
    have hsingle : D.weight atomIndex * atomPairing D atomIndex atomIndex ^ 2
        ≤ ∑ other, D.weight other * atomPairing D atomIndex other ^ 2 :=
      Finset.single_le_sum
        (f := fun other => D.weight other * atomPairing D atomIndex other ^ 2)
        (fun other _ => mul_nonneg (D.weight_pos other).le (sq_nonneg _))
        (Finset.mem_univ atomIndex)
    rw [hpairSelf atomIndex, hdiag] at hsingle
    nlinarith [hsingle, hexcess]

/-- **The relaxation really is a relaxation.** If the phase-free covering holds
at some size, so does the real discriminant covering — hence, at size seven, so
does `GtzWeightedAll 3`. Every phase-free certificate proves the left side. -/
theorem discriminantCovering_of_phaseFreeCovering {size : ℕ}
    (hphaseFree : PhaseFreeCovering size) : DiscriminantCovering size := by
  intro D hheavy
  obtain ⟨pivot, pairFirst, pairSecond, hpivotFirst, hpivotSecond, hpairDistinct,
    htrace, htie⟩ :=
    hphaseFree (phaseFreeOfDesign D) (isPhaseFreeAdmissible_of_design D hheavy)
  exact ⟨pivot, pairFirst, pairSecond, hpivotFirst, hpivotSecond, hpairDistinct,
    by rw [discriminantTrace_eq_traceLeg]; exact htrace,
    by rw [discriminantTie_eq_determinantLeg]; exact htie⟩

/-! ### The witness: the shared-axis trine, in phase-free coordinates

Six directions in `ℂ³`: `g_j = (√2, 0, ω^j)` and `g_{3+j} = (0, √2, ω^j)` for
`j = 0,1,2` (`Gtz/Complex/SharpConstantLedger.lean`). Every leverage is `3`, so
every excess is `2`. Squared overlaps take three values: `9` on the diagonal,
`|2 + ω|² = 3` inside a coplanar trine, `|ω^{j-i}|² = 1` across the two trines.
Every Bargmann triangle of three DISTINCT directions is purely imaginary —
`(2 + ω)³ = 3√3·i` and its relatives — so every such `triangle` is `0`. -/

/-- Which of the two coplanar trines a direction belongs to. -/
def trineFamily (direction : Fin 6) : Bool := direction.val < 3

/-- The squared-overlap table of the six trine directions. -/
def trineOverlap (firstDirection secondDirection : Fin 6) : ℝ :=
  if firstDirection = secondDirection then 9
  else if trineFamily firstDirection = trineFamily secondDirection then 3
  else 1

/-- **A trine point at any size.** `atomDirection` assigns each atom one of the
six trine directions; repeating a direction is the atom split, which is a genuine
design operation and lifts the witness from six atoms to seven. -/
def trinePoint {size : ℕ} (atomWeight : Fin size → ℝ) (atomDirection : Fin size → Fin 6) :
    PhaseFreeData size where
  weight := atomWeight
  excess := fun _ => 2
  pairing := fun first second => trineOverlap (atomDirection first) (atomDirection second)
  triangle := fun first second third =>
    if atomDirection first = atomDirection second then
      3 * trineOverlap (atomDirection first) (atomDirection third)
    else if atomDirection second = atomDirection third then
      3 * trineOverlap (atomDirection first) (atomDirection second)
    else if atomDirection first = atomDirection third then
      3 * trineOverlap (atomDirection first) (atomDirection second)
    else 0

/-- The bare triangle table on directions, extracted so the finite checks below
run over `Fin 6` rather than over the atom index. -/
def trineTriangleTable (firstDirection secondDirection thirdDirection : Fin 6) : ℝ :=
  if firstDirection = secondDirection then 3 * trineOverlap firstDirection thirdDirection
  else if secondDirection = thirdDirection then 3 * trineOverlap firstDirection secondDirection
  else if firstDirection = thirdDirection then 3 * trineOverlap firstDirection secondDirection
  else 0

@[simp] theorem trinePoint_triangle {size : ℕ} (atomWeight : Fin size → ℝ)
    (atomDirection : Fin size → Fin 6) (first second third : Fin size) :
    (trinePoint atomWeight atomDirection).triangle first second third
      = trineTriangleTable (atomDirection first) (atomDirection second)
          (atomDirection third) := rfl

@[simp] theorem trinePoint_weight {size : ℕ} (atomWeight : Fin size → ℝ)
    (atomDirection : Fin size → Fin 6) (atomIndex : Fin size) :
    (trinePoint atomWeight atomDirection).weight atomIndex = atomWeight atomIndex := rfl

@[simp] theorem trinePoint_excess {size : ℕ} (atomWeight : Fin size → ℝ)
    (atomDirection : Fin size → Fin 6) (atomIndex : Fin size) :
    (trinePoint atomWeight atomDirection).excess atomIndex = 2 := rfl

@[simp] theorem trinePoint_pairing {size : ℕ} (atomWeight : Fin size → ℝ)
    (atomDirection : Fin size → Fin 6) (first second : Fin size) :
    (trinePoint atomWeight atomDirection).pairing first second
      = trineOverlap (atomDirection first) (atomDirection second) := rfl

/-! #### The finite direction-level facts, checked once over `Fin 6` -/

theorem trineOverlap_symm (firstDirection secondDirection : Fin 6) :
    trineOverlap firstDirection secondDirection = trineOverlap secondDirection firstDirection := by
  fin_cases firstDirection <;> fin_cases secondDirection <;>
    norm_num [trineOverlap, trineFamily, Fin.ext_iff]

theorem trineOverlap_self (direction : Fin 6) : trineOverlap direction direction = 9 := by
  simp [trineOverlap]

theorem trineOverlap_nonneg (firstDirection secondDirection : Fin 6) :
    0 ≤ trineOverlap firstDirection secondDirection := by
  fin_cases firstDirection <;> fin_cases secondDirection <;>
    norm_num [trineOverlap, trineFamily, Fin.ext_iff]

theorem trineOverlap_le_nine (firstDirection secondDirection : Fin 6) :
    trineOverlap firstDirection secondDirection ≤ 9 := by
  fin_cases firstDirection <;> fin_cases secondDirection <;>
    norm_num [trineOverlap, trineFamily, Fin.ext_iff]

theorem trineTriangleTable_swap (firstDirection secondDirection thirdDirection : Fin 6) :
    trineTriangleTable firstDirection secondDirection thirdDirection
      = trineTriangleTable secondDirection firstDirection thirdDirection := by
  fin_cases firstDirection <;> fin_cases secondDirection <;> fin_cases thirdDirection <;>
    norm_num [trineTriangleTable, trineOverlap, trineFamily, Fin.ext_iff]

theorem trineTriangleTable_rotate (firstDirection secondDirection thirdDirection : Fin 6) :
    trineTriangleTable firstDirection secondDirection thirdDirection
      = trineTriangleTable secondDirection thirdDirection firstDirection := by
  fin_cases firstDirection <;> fin_cases secondDirection <;> fin_cases thirdDirection <;>
    norm_num [trineTriangleTable, trineOverlap, trineFamily, Fin.ext_iff]

/-- **The relaxed relation, at the witness.** Over `ℝ` this would be an equality;
here it is strict at every triple of distinct directions, where the left side is
`0` and the right side is `27` or `3`. That gap IS the phase defect. -/
theorem trineTriangleTable_cap (firstDirection secondDirection thirdDirection : Fin 6) :
    trineTriangleTable firstDirection secondDirection thirdDirection ^ 2
      ≤ trineOverlap firstDirection secondDirection
          * trineOverlap secondDirection thirdDirection
          * trineOverlap firstDirection thirdDirection := by
  fin_cases firstDirection <;> fin_cases secondDirection <;> fin_cases thirdDirection <;>
    norm_num [trineTriangleTable, trineOverlap, trineFamily, Fin.ext_iff]

/-- **Every triple fails**, provided no direction is used three times. The value
is `8 - 2·(sum of the three overlaps) + 2·triangle`, which is `-2` or `-10` at
three distinct directions and `-4` or `-8` when exactly two coincide. -/
theorem trineTriangleTable_determinant_neg (firstDirection secondDirection thirdDirection : Fin 6)
    (hnotAllEqual : ¬ (firstDirection = secondDirection ∧ secondDirection = thirdDirection)) :
    (2 : ℝ) * (2 * 2 - trineOverlap secondDirection thirdDirection)
        - (2 * trineOverlap firstDirection secondDirection
            - 2 * trineTriangleTable firstDirection secondDirection thirdDirection
            + 2 * trineOverlap firstDirection thirdDirection) < 0 := by
  fin_cases firstDirection <;> fin_cases secondDirection <;> fin_cases thirdDirection <;>
    simp_all [trineTriangleTable, trineOverlap, trineFamily, Fin.ext_iff] <;> norm_num

/-! #### Pushforward to the six directions

Every sum against a trine point depends on the atoms only through the mass each
DIRECTION carries. That is what makes the atom split free: splitting an atom
redistributes mass inside one direction and changes no sum. All the finite
checking therefore happens once, over `Fin 6`. -/

/-- Total weight carried by a direction. -/
noncomputable def directionMass {size : ℕ} (atomWeight : Fin size → ℝ)
    (atomDirection : Fin size → Fin 6) (direction : Fin 6) : ℝ :=
  ∑ atomIndex ∈ Finset.univ.filter (fun atomIndex => atomDirection atomIndex = direction),
    atomWeight atomIndex

theorem sum_eq_sum_directionMass {size : ℕ} (atomWeight : Fin size → ℝ)
    (atomDirection : Fin size → Fin 6) (valueOfDirection : Fin 6 → ℝ) :
    ∑ atomIndex, atomWeight atomIndex * valueOfDirection (atomDirection atomIndex)
      = ∑ direction, directionMass atomWeight atomDirection direction
          * valueOfDirection direction := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (g := atomDirection) (t := (Finset.univ : Finset (Fin 6)))
        (fun atomIndex _ => Finset.mem_univ _)
        (f := fun atomIndex => atomWeight atomIndex * valueOfDirection (atomDirection atomIndex))]
  refine Finset.sum_congr rfl fun direction _ => ?_
  rw [directionMass, Finset.sum_mul]
  exact Finset.sum_congr rfl fun atomIndex hmem => by rw [(Finset.mem_filter.mp hmem).2]

/-- The direction-level Parseval diagonal: uniform mass `1/6` on six directions. -/
theorem trineOverlap_uniform_sum (direction : Fin 6) :
    ∑ other, (1 / 6 : ℝ) * trineOverlap direction other = 3 := by
  fin_cases direction <;>
    norm_num [trineOverlap, trineFamily, Fin.sum_univ_six, Fin.ext_iff]

/-- The direction-level Parseval pair identity. -/
theorem trineTriangleTable_uniform_sum (firstDirection secondDirection : Fin 6) :
    ∑ other, (1 / 6 : ℝ) * trineTriangleTable firstDirection secondDirection other
      = trineOverlap firstDirection secondDirection := by
  fin_cases firstDirection <;> fin_cases secondDirection <;>
    norm_num [trineTriangleTable, trineOverlap, trineFamily, Fin.sum_univ_six, Fin.ext_iff]

/-! #### Generic admissibility of a trine point -/

/-- Everything except the three weight-dependent relations, for any trine point. -/
theorem trinePoint_generic {size : ℕ} (atomWeight : Fin size → ℝ)
    (atomDirection : Fin size → Fin 6)
    (hweightPos : ∀ atomIndex, 0 < atomWeight atomIndex)
    (hweightSum : ∑ atomIndex, atomWeight atomIndex = 1)
    (hleverage : ∀ atomIndex, atomWeight atomIndex * 3 ≤ 1)
    (hmass : ∀ direction, directionMass atomWeight atomDirection direction = 1 / 6) :
    IsPhaseFreeAdmissible (trinePoint atomWeight atomDirection) where
  weightPos := hweightPos
  weightSumOne := hweightSum
  excessPos := fun _ => by norm_num
  traceEqRank := by
    simp only [trinePoint_weight, trinePoint_excess]
    rw [show (∑ atomIndex, atomWeight atomIndex * ((2 : ℝ) + 1))
          = (∑ atomIndex, atomWeight atomIndex) * 3 from by rw [Finset.sum_mul]; norm_num,
      hweightSum]
    norm_num
  pairingSymm := fun first second => trineOverlap_symm _ _
  pairingDiag := fun atomIndex => by
    simp only [trinePoint_pairing, trinePoint_excess]; rw [trineOverlap_self]; norm_num
  pairingNonneg := fun _ _ => trineOverlap_nonneg _ _
  pairingCap := fun first second => by
    simp only [trinePoint_pairing, trinePoint_excess]
    have := trineOverlap_le_nine (atomDirection first) (atomDirection second)
    linarith
  triangleSwap := fun first second third => trineTriangleTable_swap _ _ _
  triangleRotate := fun first second third => trineTriangleTable_rotate _ _ _
  triangleCollapse := fun first second => by
    simp only [trinePoint_triangle, trinePoint_pairing, trinePoint_excess,
      trineTriangleTable]
    norm_num
  parsevalDiag := fun atomIndex => by
    simp only [trinePoint_weight, trinePoint_pairing, trinePoint_excess]
    rw [show ((2 : ℝ) + 1) = 3 from by norm_num,
      sum_eq_sum_directionMass atomWeight atomDirection
        (trineOverlap (atomDirection atomIndex)),
      show (∑ direction, directionMass atomWeight atomDirection direction
              * trineOverlap (atomDirection atomIndex) direction)
            = ∑ direction, (1 / 6 : ℝ) * trineOverlap (atomDirection atomIndex) direction from
        Finset.sum_congr rfl fun direction _ => by rw [hmass direction]]
    exact trineOverlap_uniform_sum (atomDirection atomIndex)
  parsevalPair := fun first second => by
    simp only [trinePoint_weight, trinePoint_triangle, trinePoint_pairing]
    rw [sum_eq_sum_directionMass atomWeight atomDirection
        (trineTriangleTable (atomDirection first) (atomDirection second)),
      show (∑ direction, directionMass atomWeight atomDirection direction
              * trineTriangleTable (atomDirection first) (atomDirection second) direction)
            = ∑ direction, (1 / 6 : ℝ)
                * trineTriangleTable (atomDirection first) (atomDirection second) direction from
        Finset.sum_congr rfl fun direction _ => by rw [hmass direction]]
    exact trineTriangleTable_uniform_sum _ _
  triangleCap := fun first second third => by
    simp only [trinePoint_triangle, trinePoint_pairing]; exact trineTriangleTable_cap _ _ _
  leverageCap := fun atomIndex => by
    simp only [trinePoint_weight, trinePoint_excess]
    rw [show ((2 : ℝ) + 1) = 3 from by norm_num]
    exact hleverage atomIndex

/-- The determinant leg of a trine point, at any triple of atoms carrying not-all-
equal directions, is strictly negative. -/
theorem trinePoint_determinantLeg_neg {size : ℕ} (atomWeight : Fin size → ℝ)
    (atomDirection : Fin size → Fin 6) (pivot pairFirst pairSecond : Fin size)
    (hnotAllEqual : ¬ (atomDirection pivot = atomDirection pairFirst
      ∧ atomDirection pairFirst = atomDirection pairSecond)) :
    (trinePoint atomWeight atomDirection).determinantLeg pivot pairFirst pairSecond < 0 := by
  simp only [PhaseFreeData.determinantLeg, trinePoint_excess, trinePoint_pairing,
    trinePoint_triangle]
  exact trineTriangleTable_determinant_neg (atomDirection pivot) (atomDirection pairFirst)
    (atomDirection pairSecond) hnotAllEqual

/-! #### Size six: the trine itself -/

/-- The shared-axis trine as a phase-free point: six atoms, one per direction,
all of weight `1/6`. -/
noncomputable def trineSixData : PhaseFreeData 6 := trinePoint (fun _ => 1 / 6) id

theorem trineSixData_isPhaseFreeAdmissible : IsPhaseFreeAdmissible trineSixData := by
  refine trinePoint_generic _ _ (fun _ => by norm_num) (by norm_num [Fin.sum_univ_six])
    (fun _ => by norm_num) (fun direction => ?_)
  simp [directionMass, Finset.filter_eq']

/-- **No triple of the six-atom trine covers.** All six directions are distinct,
so the not-all-equal hypothesis is automatic from `pivot ≠ pairFirst`. -/
theorem trineSixData_determinantLeg_neg (pivot pairFirst pairSecond : Fin 6)
    (hpivotFirst : pivot ≠ pairFirst) :
    trineSixData.determinantLeg pivot pairFirst pairSecond < 0 :=
  trinePoint_determinantLeg_neg _ _ _ _ _ (fun hpair => hpivotFirst hpair.1)

/-! #### Size seven: the trine with one atom split -/

/-- Atom `6` repeats direction `0`; the weight `1/6` of direction `0` is split
evenly between atoms `0` and `6`. Splitting an atom preserves Parseval, preserves
every leverage, and can only destroy domination, so this is the standard lift of
a witness to the next size. -/
def trineSevenDirection (atomIndex : Fin 7) : Fin 6 :=
  ⟨atomIndex.val % 6, Nat.mod_lt _ (by norm_num)⟩

/-- Atoms `0` and `6` share direction `0`, so they share direction `0`'s weight. -/
noncomputable def trineSevenWeight (atomIndex : Fin 7) : ℝ :=
  if atomIndex.val = 0 ∨ atomIndex.val = 6 then 1 / 12 else 1 / 6

/-- The split trine as a phase-free point at size seven — the size that decides
rank three (`discriminantCovering_seven_iff_rank_three`). -/
noncomputable def trineSevenData : PhaseFreeData 7 :=
  trinePoint trineSevenWeight trineSevenDirection

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1000000 in
theorem trineSevenData_isPhaseFreeAdmissible : IsPhaseFreeAdmissible trineSevenData := by
  refine trinePoint_generic _ _ (fun atomIndex => ?_) ?_
    (fun atomIndex => ?_) (fun direction => ?_)
  · fin_cases atomIndex <;> norm_num [trineSevenWeight]
  · rw [Fin.sum_univ_seven]; norm_num [trineSevenWeight, Fin.ext_iff]
  · fin_cases atomIndex <;> norm_num [trineSevenWeight]
  · simp only [directionMass, Finset.sum_filter, Fin.sum_univ_seven]
    fin_cases direction <;>
      norm_num [trineSevenWeight, trineSevenDirection, Fin.ext_iff, Fin.val_ofNat]

set_option maxRecDepth 20000 in
/-- **Direction `0` is the only collision.** Two distinct atoms carry the same
direction exactly when they are the two halves of the split atom. -/
theorem trineSevenDirection_collision (first second : Fin 7) (hne : first ≠ second)
    (heq : trineSevenDirection first = trineSevenDirection second) :
    (first = 0 ∧ second = 6) ∨ (first = 6 ∧ second = 0) := by
  revert hne heq
  fin_cases first <;> fin_cases second <;> simp_all [trineSevenDirection, Fin.ext_iff]

/-- **No triple of the split trine covers.** Direction `0` is carried by exactly
two atoms, so three pairwise distinct atoms never carry three equal directions. -/
theorem trineSevenData_determinantLeg_neg (pivot pairFirst pairSecond : Fin 7)
    (hpivotFirst : pivot ≠ pairFirst) (hpivotSecond : pivot ≠ pairSecond)
    (hpairDistinct : pairFirst ≠ pairSecond) :
    trineSevenData.determinantLeg pivot pairFirst pairSecond < 0 := by
  refine trinePoint_determinantLeg_neg _ _ _ _ _ (fun hpair => ?_)
  obtain ⟨hleft, hright⟩ := hpair
  rcases trineSevenDirection_collision pivot pairFirst hpivotFirst hleft with
    ⟨hpivotZero, hfirstSix⟩ | ⟨hpivotSix, hfirstZero⟩ <;>
  rcases trineSevenDirection_collision pairFirst pairSecond hpairDistinct hright with
    ⟨hfirstZero', hsecondSix⟩ | ⟨hfirstSix', hsecondZero⟩ <;>
    simp_all

/-! ### The no-go -/

/-- **The phase-free relaxation of rank three is FALSE at size six.** -/
theorem not_phaseFreeCovering_six : ¬ PhaseFreeCovering 6 := by
  intro hcover
  obtain ⟨pivot, pairFirst, pairSecond, hpivotFirst, _, _, _, htie⟩ :=
    hcover trineSixData trineSixData_isPhaseFreeAdmissible
  exact absurd htie (not_le.mpr (trineSixData_determinantLeg_neg pivot pairFirst pairSecond
    hpivotFirst))

/-- **The phase-free relaxation of rank three is FALSE at size seven** — the size
that decides rank three for every `n`. -/
theorem not_phaseFreeCovering_seven : ¬ PhaseFreeCovering 7 := by
  intro hcover
  obtain ⟨pivot, pairFirst, pairSecond, hpivotFirst, hpivotSecond, hpairDistinct, _, htie⟩ :=
    hcover trineSevenData trineSevenData_isPhaseFreeAdmissible
  exact absurd htie (not_le.mpr (trineSevenData_determinantLeg_neg pivot pairFirst pairSecond
    hpivotFirst hpivotSecond hpairDistinct))

/-- **THE OBSTRUCTION.** The phase-free relaxation is strictly weaker than the
real system: it is implied by every phase-free certificate
(`discriminantCovering_of_phaseFreeCovering`) and it is false
(`not_phaseFreeCovering_seven`). A Positivstellensatz certificate is a witness
that a semialgebraic set is EMPTY; `trineSevenData` is an explicit rational
member of the set the relaxation would have to exclude. Hence no certificate of
`GtzWeighted 7 3` — equivalently of `GtzWeightedAll 3` — can be phase-free, AT
ANY DEGREE. Every certificate must invoke a relation separating `ℝ` from `ℂ`,
and by `IsPhaseFreeAdmissible` there is exactly one candidate on the list: the
vanishing of the phase defect in `triangleCap`. -/
theorem phaseFree_certificates_cannot_prove_rank_three :
    (¬ PhaseFreeCovering 7) ∧ (PhaseFreeCovering 7 → GtzWeightedAll 3) :=
  ⟨not_phaseFreeCovering_seven, fun hcover =>
    discriminantCovering_seven_iff_rank_three.mp
      (discriminantCovering_of_phaseFreeCovering hcover)⟩

end Gtz
