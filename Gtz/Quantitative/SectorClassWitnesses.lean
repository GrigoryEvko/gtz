import Gtz.Quantitative.TwoGraphCollision
import Gtz.Ties.SelectionObstruction
import Gtz.Quantitative.EdgeOrbitSectors

/-! # The eight sign-class realizability witnesses

`Gtz.card_residualSectors` says `842` of the `1024` two-graphs on six atoms survive
every proved sign-layer lever, and `Gtz.sectorSurvives_survivingClassRepresentatives`
names one representative link in each of the eight surviving `S6` isomorphism classes:
`19, 20, 21, 23, 55, 58, 185, 220`.  Until now the SHARPNESS of that residue -- that
every one of the eight is realised by a genuine `(6,3)` design, so no correct sign-only
argument cuts any of them -- was an attribution to an out-of-kernel enumeration.

This file makes it a theorem.  For each of the eight representatives there is an
explicit rational `Gtz.WeightedDesign 6 3` whose `Gtz.linkWordOf` is exactly that
representative.  Every witness is moreover ALL-HEAVY, has all fifteen pairings nonzero,
has no parallel pair (its six atoms span six distinct lines) and is off the equal-share
stratum -- so the sign-blind crux fields remove no class either.

The generic half is `Gtz.linkWordOf_eq_packTenBits_of_negTable`: it reads the link word
of ANY `(6,3)` design off a Boolean table of pairing signs, so a witness never touches
`Gtz.tripleParity` or `Gtz.packTenBits` directly.  It is reusable at any design.

WHAT THIS DOES NOT DO.  It does not shrink the residue and does not approach
`IsEmpty Gtz.SixThreeCrux`.  It closes the sharpness question in the negative
direction: the sign lane is exactly as far as the levers take it. -/

namespace Gtz

open Matrix

/-! ## 1. The generic bridge -/

/-- One bit of the link word, from a Boolean table of pairing signs. -/
theorem decide_tripleParity_eq_xor_of_negTable (design : WeightedDesign 6 3)
    (negTable : Fin 6 → Fin 6 → Bool)
    (htable : ∀ atomFirst atomSecond : Fin 6,
      edgeSign design atomFirst atomSecond = if negTable atomFirst atomSecond then -1 else 1)
    (first second third : Fin 6) :
    decide (tripleParity design first second third = -1)
      = xor (xor (negTable first second) (negTable first third)) (negTable second third) := by
  rw [tripleParity, htable, htable, htable]
  cases hfirstSecond : negTable first second <;> cases hfirstThird : negTable first third <;>
    cases hsecondThird : negTable second third <;> norm_num

/-- **THE BRIDGE.**  The link word of a design is the exclusive-or closure of any
correct Boolean table of its pairing signs.  Stated for an arbitrary design, so any
later witness at this cell reuses it verbatim. -/
theorem linkWordOf_eq_packTenBits_of_negTable (design : WeightedDesign 6 3)
    (negTable : Fin 6 → Fin 6 → Bool)
    (htable : ∀ atomFirst atomSecond : Fin 6,
      edgeSign design atomFirst atomSecond = if negTable atomFirst atomSecond then -1 else 1) :
    linkWordOf design = packTenBits
      (xor (xor (negTable 0 1) (negTable 0 2)) (negTable 1 2))
      (xor (xor (negTable 0 1) (negTable 0 3)) (negTable 1 3))
      (xor (xor (negTable 0 1) (negTable 0 4)) (negTable 1 4))
      (xor (xor (negTable 0 1) (negTable 0 5)) (negTable 1 5))
      (xor (xor (negTable 0 2) (negTable 0 3)) (negTable 2 3))
      (xor (xor (negTable 0 2) (negTable 0 4)) (negTable 2 4))
      (xor (xor (negTable 0 2) (negTable 0 5)) (negTable 2 5))
      (xor (xor (negTable 0 3) (negTable 0 4)) (negTable 3 4))
      (xor (xor (negTable 0 3) (negTable 0 5)) (negTable 3 5))
      (xor (xor (negTable 0 4) (negTable 0 5)) (negTable 4 5)) := by
  rw [linkWordOf, decide_tripleParity_eq_xor_of_negTable design negTable htable,
    decide_tripleParity_eq_xor_of_negTable design negTable htable,
    decide_tripleParity_eq_xor_of_negTable design negTable htable,
    decide_tripleParity_eq_xor_of_negTable design negTable htable,
    decide_tripleParity_eq_xor_of_negTable design negTable htable,
    decide_tripleParity_eq_xor_of_negTable design negTable htable,
    decide_tripleParity_eq_xor_of_negTable design negTable htable,
    decide_tripleParity_eq_xor_of_negTable design negTable htable,
    decide_tripleParity_eq_xor_of_negTable design negTable htable,
    decide_tripleParity_eq_xor_of_negTable design negTable htable]

/-! ## 2. The eight witnesses -/


/-! ### SectorTriangle: link `19`, the class `Delta(K3), a triangle -- self-complementary`

Leverages `3/2, 6, 3/2, 6, 6, 6`, shares `1/6, 5/6, 5/6, 5/6, 1/6, 1/6`; all-heavy, no parallel pair, every pairing
nonzero, off the equal-share stratum.  Its two-graph has `10` incoherent
triples and per-vertex coherent profile `[3, 3, 3, 7, 7, 7]`. -/
noncomputable def sectorTriangleAtom : Fin 6 → Fin 3 → ℝ :=
  ![![1/2, 1/2, -1], ![1, -1, 2], ![1/2, 1, 1/2],
    ![2, -1, -1], ![1, 2, -1], ![2, 1, -1]]

/-- A genuine `(6,3)` design realising the class `Delta(K3), a triangle -- self-complementary`. -/
noncomputable def sectorTriangleDesign : WeightedDesign 6 3 where
  atom := sectorTriangleAtom
  weight := ![1/9, 5/36, 5/9, 5/36, 1/36, 1/36]
  weight_pos := by intro atomIndex; fin_cases atomIndex <;> norm_num
  weight_sum_one := by
    simp only [Fin.sum_univ_six, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four, Matrix.cons_val, Matrix.tail_cons]
    norm_num
  isParseval := by
    ext rowIndex colIndex
    simp only [Matrix.sum_apply, Matrix.smul_apply, atomMatrix,
      Matrix.vecMulVec_apply, Fin.sum_univ_six, smul_eq_mul, sectorTriangleAtom,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.cons_val, Matrix.tail_cons]
    fin_cases rowIndex <;> fin_cases colIndex <;> norm_num [Matrix.one_apply]

/-- Its fifteen pairing signs, `true` where the pairing is negative. -/
def sectorTriangleNeg : Fin 6 → Fin 6 → Bool :=
  ![![false, true, false, false, false, false],
    ![true, false, false, false, true, true],
    ![false, false, false, true, false, false],
    ![false, false, true, false, false, false],
    ![false, true, false, false, false, false],
    ![false, true, false, false, false, false]]

theorem sectorTriangleDesign_edgeSign (atomFirst atomSecond : Fin 6) :
    edgeSign sectorTriangleDesign atomFirst atomSecond
      = if sectorTriangleNeg atomFirst atomSecond then -1 else 1 := by
  fin_cases atomFirst <;> fin_cases atomSecond <;>
    norm_num [edgeSign, atomPairing, sectorTriangleDesign, sectorTriangleAtom, sectorTriangleNeg, dotProduct,
      Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]

/-- **Its two-graph is the class representative `19`.** -/
theorem sectorTriangleDesign_linkWordOf : linkWordOf sectorTriangleDesign = 19 := by
  rw [linkWordOf_eq_packTenBits_of_negTable sectorTriangleDesign sectorTriangleNeg sectorTriangleDesign_edgeSign]
  decide

/-- **The class survives every lever, and this design realises it.** -/
theorem sectorTriangleDesign_linkWord_mem_residualSectors :
    linkWordOf sectorTriangleDesign ∈ residualSectors := by
  rw [sectorTriangleDesign_linkWordOf, mem_residualSectors_iff]
  exact ⟨by norm_num, by decide +kernel⟩

/-- The witness is ALL-HEAVY, so the crux field `isAllHeavy` removes no class. -/
theorem sectorTriangleDesign_allHeavy : AllHeavy sectorTriangleDesign := by
  intro atomIndex
  fin_cases atomIndex <;>
    norm_num [leverageOf, sectorTriangleDesign, sectorTriangleAtom, Fin.sum_univ_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]

/-- No two of its atoms are parallel: it really spans six distinct lines, so the
crux field `hasNoParallelPair` removes no class either. -/
theorem sectorTriangleDesign_hasNoParallelPair : ¬ HasParallelPair sectorTriangleDesign := by
  rintro ⟨keptLabel, dropLabel, ratio, hne, hparallel⟩
  have hzero := pairGramMinor_eq_zero_of_smul sectorTriangleDesign hparallel
  rw [pairGramMinor] at hzero
  revert hzero
  fin_cases keptLabel <;> fin_cases dropLabel <;>
    first
      | exact fun _ => hne rfl
      | norm_num [sectorTriangleDesign, sectorTriangleAtom, leverageOf, dotProduct,
          Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]

/-- Its weights are not uniform, so it is off the equal-share stratum and the crux
field `avoidsEqualShareStratum` removes no class. -/
theorem sectorTriangleDesign_not_isEqualShare : ¬ IsEqualShare sectorTriangleDesign := by
  intro hequalShare
  have hweight := hequalShare.weight_eq 0
  norm_num [sectorTriangleDesign] at hweight

/-- Every one of its fifteen pairings is nonzero, so it is a witness for the
NONVANISHING branch that `Gtz.SixThreeCrux.linkWord_mem_residualSectors` needs. -/
theorem sectorTriangleDesign_atomPairing_ne_zero (atomFirst atomSecond : Fin 6)
    (hne : atomFirst ≠ atomSecond) :
    atomPairing sectorTriangleDesign atomFirst atomSecond ≠ 0 := by
  fin_cases atomFirst <;> fin_cases atomSecond <;>
    first
      | exact absurd rfl hne
      | norm_num [atomPairing, sectorTriangleDesign, sectorTriangleAtom, dotProduct,
          Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]

/-! ### SectorTwoKTwo: link `20`, the class `Delta(2K2), two disjoint edges`

Leverages `5/4, 9/4, 6, 9/4, 6, 3/2`, shares `5/36, 7/12, 2/3, 7/10, 4/5, 1/9`; all-heavy, no parallel pair, every pairing
nonzero, off the equal-share stratum.  Its two-graph has `8` incoherent
triples and per-vertex coherent profile `[5, 5, 5, 5, 8, 8]`. -/
noncomputable def sectorTwoKTwoAtom : Fin 6 → Fin 3 → ℝ :=
  ![![1/2, -1, 0], ![1/2, -1, -1], ![2, -1, 1],
    ![1, 1, 1/2], ![1, 1, -2], ![1/2, -1, 1/2]]

/-- A genuine `(6,3)` design realising the class `Delta(2K2), two disjoint edges`. -/
noncomputable def sectorTwoKTwoDesign : WeightedDesign 6 3 where
  atom := sectorTwoKTwoAtom
  weight := ![1/9, 7/27, 1/9, 14/45, 2/15, 2/27]
  weight_pos := by intro atomIndex; fin_cases atomIndex <;> norm_num
  weight_sum_one := by
    simp only [Fin.sum_univ_six, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four, Matrix.cons_val, Matrix.tail_cons]
    norm_num
  isParseval := by
    ext rowIndex colIndex
    simp only [Matrix.sum_apply, Matrix.smul_apply, atomMatrix,
      Matrix.vecMulVec_apply, Fin.sum_univ_six, smul_eq_mul, sectorTwoKTwoAtom,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.cons_val, Matrix.tail_cons]
    fin_cases rowIndex <;> fin_cases colIndex <;> norm_num [Matrix.one_apply]

/-- Its fifteen pairing signs, `true` where the pairing is negative. -/
def sectorTwoKTwoNeg : Fin 6 → Fin 6 → Bool :=
  ![![false, false, false, true, true, false],
    ![false, false, false, true, false, false],
    ![false, false, false, false, true, false],
    ![true, true, false, false, false, true],
    ![true, false, true, false, false, true],
    ![false, false, false, true, true, false]]

theorem sectorTwoKTwoDesign_edgeSign (atomFirst atomSecond : Fin 6) :
    edgeSign sectorTwoKTwoDesign atomFirst atomSecond
      = if sectorTwoKTwoNeg atomFirst atomSecond then -1 else 1 := by
  fin_cases atomFirst <;> fin_cases atomSecond <;>
    norm_num [edgeSign, atomPairing, sectorTwoKTwoDesign, sectorTwoKTwoAtom, sectorTwoKTwoNeg, dotProduct,
      Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]

/-- **Its two-graph is the class representative `20`.** -/
theorem sectorTwoKTwoDesign_linkWordOf : linkWordOf sectorTwoKTwoDesign = 20 := by
  rw [linkWordOf_eq_packTenBits_of_negTable sectorTwoKTwoDesign sectorTwoKTwoNeg sectorTwoKTwoDesign_edgeSign]
  decide

/-- **The class survives every lever, and this design realises it.** -/
theorem sectorTwoKTwoDesign_linkWord_mem_residualSectors :
    linkWordOf sectorTwoKTwoDesign ∈ residualSectors := by
  rw [sectorTwoKTwoDesign_linkWordOf, mem_residualSectors_iff]
  exact ⟨by norm_num, by decide +kernel⟩

/-- The witness is ALL-HEAVY, so the crux field `isAllHeavy` removes no class. -/
theorem sectorTwoKTwoDesign_allHeavy : AllHeavy sectorTwoKTwoDesign := by
  intro atomIndex
  fin_cases atomIndex <;>
    norm_num [leverageOf, sectorTwoKTwoDesign, sectorTwoKTwoAtom, Fin.sum_univ_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]

/-- No two of its atoms are parallel: it really spans six distinct lines, so the
crux field `hasNoParallelPair` removes no class either. -/
theorem sectorTwoKTwoDesign_hasNoParallelPair : ¬ HasParallelPair sectorTwoKTwoDesign := by
  rintro ⟨keptLabel, dropLabel, ratio, hne, hparallel⟩
  have hzero := pairGramMinor_eq_zero_of_smul sectorTwoKTwoDesign hparallel
  rw [pairGramMinor] at hzero
  revert hzero
  fin_cases keptLabel <;> fin_cases dropLabel <;>
    first
      | exact fun _ => hne rfl
      | norm_num [sectorTwoKTwoDesign, sectorTwoKTwoAtom, leverageOf, dotProduct,
          Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]

/-- Its weights are not uniform, so it is off the equal-share stratum and the crux
field `avoidsEqualShareStratum` removes no class. -/
theorem sectorTwoKTwoDesign_not_isEqualShare : ¬ IsEqualShare sectorTwoKTwoDesign := by
  intro hequalShare
  have hweight := hequalShare.weight_eq 0
  norm_num [sectorTwoKTwoDesign] at hweight

/-- Every one of its fifteen pairings is nonzero, so it is a witness for the
NONVANISHING branch that `Gtz.SixThreeCrux.linkWord_mem_residualSectors` needs. -/
theorem sectorTwoKTwoDesign_atomPairing_ne_zero (atomFirst atomSecond : Fin 6)
    (hne : atomFirst ≠ atomSecond) :
    atomPairing sectorTwoKTwoDesign atomFirst atomSecond ≠ 0 := by
  fin_cases atomFirst <;> fin_cases atomSecond <;>
    first
      | exact absurd rfl hne
      | norm_num [atomPairing, sectorTwoKTwoDesign, sectorTwoKTwoAtom, dotProduct,
          Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]

/-! ### SectorPathFour: link `21`, the class `Delta(P4), a path with three edges`

Leverages `9/4, 9/4, 2, 13/4, 5, 6`, shares `9/32, 21/32, 1/3, 13/16, 5/12, 1/2`; all-heavy, no parallel pair, every pairing
nonzero, off the equal-share stratum.  Its two-graph has `8` incoherent
triples and per-vertex coherent profile `[5, 5, 6, 6, 7, 7]`. -/
noncomputable def sectorPathFourAtom : Fin 6 → Fin 3 → ℝ :=
  ![![1/2, -1, -1], ![1/2, -1, 1], ![1, 0, -1],
    ![3/2, 1, 0], ![1, 0, 2], ![1, -2, -1]]

/-- A genuine `(6,3)` design realising the class `Delta(P4), a path with three edges`. -/
noncomputable def sectorPathFourDesign : WeightedDesign 6 3 where
  atom := sectorPathFourAtom
  weight := ![1/8, 7/24, 1/6, 1/4, 1/12, 1/12]
  weight_pos := by intro atomIndex; fin_cases atomIndex <;> norm_num
  weight_sum_one := by
    simp only [Fin.sum_univ_six, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four, Matrix.cons_val, Matrix.tail_cons]
    norm_num
  isParseval := by
    ext rowIndex colIndex
    simp only [Matrix.sum_apply, Matrix.smul_apply, atomMatrix,
      Matrix.vecMulVec_apply, Fin.sum_univ_six, smul_eq_mul, sectorPathFourAtom,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.cons_val, Matrix.tail_cons]
    fin_cases rowIndex <;> fin_cases colIndex <;> norm_num [Matrix.one_apply]

/-- Its fifteen pairing signs, `true` where the pairing is negative. -/
def sectorPathFourNeg : Fin 6 → Fin 6 → Bool :=
  ![![false, false, false, true, true, false],
    ![false, false, true, true, false, false],
    ![false, true, false, false, true, false],
    ![true, true, false, false, false, true],
    ![true, false, true, false, false, true],
    ![false, false, false, true, true, false]]

theorem sectorPathFourDesign_edgeSign (atomFirst atomSecond : Fin 6) :
    edgeSign sectorPathFourDesign atomFirst atomSecond
      = if sectorPathFourNeg atomFirst atomSecond then -1 else 1 := by
  fin_cases atomFirst <;> fin_cases atomSecond <;>
    norm_num [edgeSign, atomPairing, sectorPathFourDesign, sectorPathFourAtom, sectorPathFourNeg, dotProduct,
      Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]

/-- **Its two-graph is the class representative `21`.** -/
theorem sectorPathFourDesign_linkWordOf : linkWordOf sectorPathFourDesign = 21 := by
  rw [linkWordOf_eq_packTenBits_of_negTable sectorPathFourDesign sectorPathFourNeg sectorPathFourDesign_edgeSign]
  decide

/-- **The class survives every lever, and this design realises it.** -/
theorem sectorPathFourDesign_linkWord_mem_residualSectors :
    linkWordOf sectorPathFourDesign ∈ residualSectors := by
  rw [sectorPathFourDesign_linkWordOf, mem_residualSectors_iff]
  exact ⟨by norm_num, by decide +kernel⟩

/-- The witness is ALL-HEAVY, so the crux field `isAllHeavy` removes no class. -/
theorem sectorPathFourDesign_allHeavy : AllHeavy sectorPathFourDesign := by
  intro atomIndex
  fin_cases atomIndex <;>
    norm_num [leverageOf, sectorPathFourDesign, sectorPathFourAtom, Fin.sum_univ_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]

/-- No two of its atoms are parallel: it really spans six distinct lines, so the
crux field `hasNoParallelPair` removes no class either. -/
theorem sectorPathFourDesign_hasNoParallelPair : ¬ HasParallelPair sectorPathFourDesign := by
  rintro ⟨keptLabel, dropLabel, ratio, hne, hparallel⟩
  have hzero := pairGramMinor_eq_zero_of_smul sectorPathFourDesign hparallel
  rw [pairGramMinor] at hzero
  revert hzero
  fin_cases keptLabel <;> fin_cases dropLabel <;>
    first
      | exact fun _ => hne rfl
      | norm_num [sectorPathFourDesign, sectorPathFourAtom, leverageOf, dotProduct,
          Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]

/-- Its weights are not uniform, so it is off the equal-share stratum and the crux
field `avoidsEqualShareStratum` removes no class. -/
theorem sectorPathFourDesign_not_isEqualShare : ¬ IsEqualShare sectorPathFourDesign := by
  intro hequalShare
  have hweight := hequalShare.weight_eq 0
  norm_num [sectorPathFourDesign] at hweight

/-- Every one of its fifteen pairings is nonzero, so it is a witness for the
NONVANISHING branch that `Gtz.SixThreeCrux.linkWord_mem_residualSectors` needs. -/
theorem sectorPathFourDesign_atomPairing_ne_zero (atomFirst atomSecond : Fin 6)
    (hne : atomFirst ≠ atomSecond) :
    atomPairing sectorPathFourDesign atomFirst atomSecond ≠ 0 := by
  fin_cases atomFirst <;> fin_cases atomSecond <;>
    first
      | exact absurd rfl hne
      | norm_num [atomPairing, sectorPathFourDesign, sectorPathFourAtom, dotProduct,
          Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]

/-! ### SectorPaw: link `23`, the class `Delta(paw), a triangle with a pendant edge -- self-complementary`

Leverages `9/4, 2, 9, 6, 3/2, 3/2`, shares `9/20, 1/2, 3/4, 4/5, 1/4, 1/4`; all-heavy, no parallel pair, every pairing
nonzero, off the equal-share stratum.  Its two-graph has `10` incoherent
triples and per-vertex coherent profile `[3, 4, 4, 6, 6, 7]`. -/
noncomputable def sectorPawAtom : Fin 6 → Fin 3 → ℝ :=
  ![![1/2, -1, -1], ![1, 0, -1], ![1, -2, 2],
    ![2, 1, 1], ![1/2, 1, -1/2], ![1/2, -1, -1/2]]

/-- A genuine `(6,3)` design realising the class `Delta(paw), a triangle with a pendant edge -- self-complementary`. -/
noncomputable def sectorPawDesign : WeightedDesign 6 3 where
  atom := sectorPawAtom
  weight := ![1/5, 1/4, 1/12, 2/15, 1/6, 1/6]
  weight_pos := by intro atomIndex; fin_cases atomIndex <;> norm_num
  weight_sum_one := by
    simp only [Fin.sum_univ_six, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four, Matrix.cons_val, Matrix.tail_cons]
    norm_num
  isParseval := by
    ext rowIndex colIndex
    simp only [Matrix.sum_apply, Matrix.smul_apply, atomMatrix,
      Matrix.vecMulVec_apply, Fin.sum_univ_six, smul_eq_mul, sectorPawAtom,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.cons_val, Matrix.tail_cons]
    fin_cases rowIndex <;> fin_cases colIndex <;> norm_num [Matrix.one_apply]

/-- Its fifteen pairing signs, `true` where the pairing is negative. -/
def sectorPawNeg : Fin 6 → Fin 6 → Bool :=
  ![![false, false, false, true, true, false],
    ![false, false, true, false, false, false],
    ![false, true, false, false, true, false],
    ![true, false, false, false, false, true],
    ![true, false, true, false, false, true],
    ![false, false, false, true, true, false]]

theorem sectorPawDesign_edgeSign (atomFirst atomSecond : Fin 6) :
    edgeSign sectorPawDesign atomFirst atomSecond
      = if sectorPawNeg atomFirst atomSecond then -1 else 1 := by
  fin_cases atomFirst <;> fin_cases atomSecond <;>
    norm_num [edgeSign, atomPairing, sectorPawDesign, sectorPawAtom, sectorPawNeg, dotProduct,
      Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]

/-- **Its two-graph is the class representative `23`.** -/
theorem sectorPawDesign_linkWordOf : linkWordOf sectorPawDesign = 23 := by
  rw [linkWordOf_eq_packTenBits_of_negTable sectorPawDesign sectorPawNeg sectorPawDesign_edgeSign]
  decide

/-- **The class survives every lever, and this design realises it.** -/
theorem sectorPawDesign_linkWord_mem_residualSectors :
    linkWordOf sectorPawDesign ∈ residualSectors := by
  rw [sectorPawDesign_linkWordOf, mem_residualSectors_iff]
  exact ⟨by norm_num, by decide +kernel⟩

/-- The witness is ALL-HEAVY, so the crux field `isAllHeavy` removes no class. -/
theorem sectorPawDesign_allHeavy : AllHeavy sectorPawDesign := by
  intro atomIndex
  fin_cases atomIndex <;>
    norm_num [leverageOf, sectorPawDesign, sectorPawAtom, Fin.sum_univ_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]

/-- No two of its atoms are parallel: it really spans six distinct lines, so the
crux field `hasNoParallelPair` removes no class either. -/
theorem sectorPawDesign_hasNoParallelPair : ¬ HasParallelPair sectorPawDesign := by
  rintro ⟨keptLabel, dropLabel, ratio, hne, hparallel⟩
  have hzero := pairGramMinor_eq_zero_of_smul sectorPawDesign hparallel
  rw [pairGramMinor] at hzero
  revert hzero
  fin_cases keptLabel <;> fin_cases dropLabel <;>
    first
      | exact fun _ => hne rfl
      | norm_num [sectorPawDesign, sectorPawAtom, leverageOf, dotProduct,
          Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]

/-- Its weights are not uniform, so it is off the equal-share stratum and the crux
field `avoidsEqualShareStratum` removes no class. -/
theorem sectorPawDesign_not_isEqualShare : ¬ IsEqualShare sectorPawDesign := by
  intro hequalShare
  have hweight := hequalShare.weight_eq 0
  norm_num [sectorPawDesign] at hweight

/-- Every one of its fifteen pairings is nonzero, so it is a witness for the
NONVANISHING branch that `Gtz.SixThreeCrux.linkWord_mem_residualSectors` needs. -/
theorem sectorPawDesign_atomPairing_ne_zero (atomFirst atomSecond : Fin 6)
    (hne : atomFirst ≠ atomSecond) :
    atomPairing sectorPawDesign atomFirst atomSecond ≠ 0 := by
  fin_cases atomFirst <;> fin_cases atomSecond <;>
    first
      | exact absurd rfl hne
      | norm_num [atomPairing, sectorPawDesign, sectorPawAtom, dotProduct,
          Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]

/-! ### SectorPathFive: link `58`, the class `Delta(P5), a path with four edges -- self-complementary`

Leverages `3/2, 6, 6, 3/2, 6, 3/2`, shares `1/4, 1/2, 3/4, 1/4, 3/4, 1/2`; all-heavy, no parallel pair, every pairing
nonzero, off the equal-share stratum.  Its two-graph has `10` incoherent
triples and per-vertex coherent profile `[4, 4, 5, 5, 6, 6]`. -/
noncomputable def sectorPathFiveAtom : Fin 6 → Fin 3 → ℝ :=
  ![![1/2, -1/2, -1], ![1, 2, -1], ![2, -1, -1],
    ![1, 1/2, 1/2], ![1, -1, 2], ![1/2, 1, 1/2]]

/-- A genuine `(6,3)` design realising the class `Delta(P5), a path with four edges -- self-complementary`. -/
noncomputable def sectorPathFiveDesign : WeightedDesign 6 3 where
  atom := sectorPathFiveAtom
  weight := ![1/6, 1/12, 1/8, 1/6, 1/8, 1/3]
  weight_pos := by intro atomIndex; fin_cases atomIndex <;> norm_num
  weight_sum_one := by
    simp only [Fin.sum_univ_six, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four, Matrix.cons_val, Matrix.tail_cons]
    norm_num
  isParseval := by
    ext rowIndex colIndex
    simp only [Matrix.sum_apply, Matrix.smul_apply, atomMatrix,
      Matrix.vecMulVec_apply, Fin.sum_univ_six, smul_eq_mul, sectorPathFiveAtom,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.cons_val, Matrix.tail_cons]
    fin_cases rowIndex <;> fin_cases colIndex <;> norm_num [Matrix.one_apply]

/-- Its fifteen pairing signs, `true` where the pairing is negative. -/
def sectorPathFiveNeg : Fin 6 → Fin 6 → Bool :=
  ![![false, false, false, true, true, true],
    ![false, false, false, false, true, false],
    ![false, false, false, false, false, true],
    ![true, false, false, false, false, false],
    ![true, true, false, false, false, false],
    ![true, false, true, false, false, false]]

theorem sectorPathFiveDesign_edgeSign (atomFirst atomSecond : Fin 6) :
    edgeSign sectorPathFiveDesign atomFirst atomSecond
      = if sectorPathFiveNeg atomFirst atomSecond then -1 else 1 := by
  fin_cases atomFirst <;> fin_cases atomSecond <;>
    norm_num [edgeSign, atomPairing, sectorPathFiveDesign, sectorPathFiveAtom, sectorPathFiveNeg, dotProduct,
      Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]

/-- **Its two-graph is the class representative `58`.** -/
theorem sectorPathFiveDesign_linkWordOf : linkWordOf sectorPathFiveDesign = 58 := by
  rw [linkWordOf_eq_packTenBits_of_negTable sectorPathFiveDesign sectorPathFiveNeg sectorPathFiveDesign_edgeSign]
  decide

/-- **The class survives every lever, and this design realises it.** -/
theorem sectorPathFiveDesign_linkWord_mem_residualSectors :
    linkWordOf sectorPathFiveDesign ∈ residualSectors := by
  rw [sectorPathFiveDesign_linkWordOf, mem_residualSectors_iff]
  exact ⟨by norm_num, by decide +kernel⟩

/-- The witness is ALL-HEAVY, so the crux field `isAllHeavy` removes no class. -/
theorem sectorPathFiveDesign_allHeavy : AllHeavy sectorPathFiveDesign := by
  intro atomIndex
  fin_cases atomIndex <;>
    norm_num [leverageOf, sectorPathFiveDesign, sectorPathFiveAtom, Fin.sum_univ_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]

/-- No two of its atoms are parallel: it really spans six distinct lines, so the
crux field `hasNoParallelPair` removes no class either. -/
theorem sectorPathFiveDesign_hasNoParallelPair : ¬ HasParallelPair sectorPathFiveDesign := by
  rintro ⟨keptLabel, dropLabel, ratio, hne, hparallel⟩
  have hzero := pairGramMinor_eq_zero_of_smul sectorPathFiveDesign hparallel
  rw [pairGramMinor] at hzero
  revert hzero
  fin_cases keptLabel <;> fin_cases dropLabel <;>
    first
      | exact fun _ => hne rfl
      | norm_num [sectorPathFiveDesign, sectorPathFiveAtom, leverageOf, dotProduct,
          Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]

/-- Its weights are not uniform, so it is off the equal-share stratum and the crux
field `avoidsEqualShareStratum` removes no class. -/
theorem sectorPathFiveDesign_not_isEqualShare : ¬ IsEqualShare sectorPathFiveDesign := by
  intro hequalShare
  have hweight := hequalShare.weight_eq 1
  norm_num [sectorPathFiveDesign] at hweight

/-- Every one of its fifteen pairings is nonzero, so it is a witness for the
NONVANISHING branch that `Gtz.SixThreeCrux.linkWord_mem_residualSectors` needs. -/
theorem sectorPathFiveDesign_atomPairing_ne_zero (atomFirst atomSecond : Fin 6)
    (hne : atomFirst ≠ atomSecond) :
    atomPairing sectorPathFiveDesign atomFirst atomSecond ≠ 0 := by
  fin_cases atomFirst <;> fin_cases atomSecond <;>
    first
      | exact absurd rfl hne
      | norm_num [atomPairing, sectorPathFiveDesign, sectorPathFiveAtom, dotProduct,
          Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]

/-! ### SectorDiamond: link `55`, the class `Delta(diamond), K4 minus an edge`

Leverages `9/4, 9/4, 6, 2, 3/2, 6`, shares `3/80, 9/16, 9/10, 1/4, 1/2, 3/4`; all-heavy, no parallel pair, every pairing
nonzero, off the equal-share stratum.  Its two-graph has `12` incoherent
triples and per-vertex coherent profile `[2, 2, 5, 5, 5, 5]`. -/
noncomputable def sectorDiamondAtom : Fin 6 → Fin 3 → ℝ :=
  ![![1/2, -1, -1], ![1/2, -1, 1], ![2, 1, 1],
    ![1, 0, -1], ![1/2, 1/2, -1], ![1, -2, -1]]

/-- A genuine `(6,3)` design realising the class `Delta(diamond), K4 minus an edge`. -/
noncomputable def sectorDiamondDesign : WeightedDesign 6 3 where
  atom := sectorDiamondAtom
  weight := ![1/60, 1/4, 3/20, 1/8, 1/3, 1/8]
  weight_pos := by intro atomIndex; fin_cases atomIndex <;> norm_num
  weight_sum_one := by
    simp only [Fin.sum_univ_six, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four, Matrix.cons_val, Matrix.tail_cons]
    norm_num
  isParseval := by
    ext rowIndex colIndex
    simp only [Matrix.sum_apply, Matrix.smul_apply, atomMatrix,
      Matrix.vecMulVec_apply, Fin.sum_univ_six, smul_eq_mul, sectorDiamondAtom,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.cons_val, Matrix.tail_cons]
    fin_cases rowIndex <;> fin_cases colIndex <;> norm_num [Matrix.one_apply]

/-- Its fifteen pairing signs, `true` where the pairing is negative. -/
def sectorDiamondNeg : Fin 6 → Fin 6 → Bool :=
  ![![false, false, true, false, false, false],
    ![false, false, false, true, true, false],
    ![true, false, false, false, false, true],
    ![false, true, false, false, false, false],
    ![false, true, false, false, false, false],
    ![false, false, true, false, false, false]]

theorem sectorDiamondDesign_edgeSign (atomFirst atomSecond : Fin 6) :
    edgeSign sectorDiamondDesign atomFirst atomSecond
      = if sectorDiamondNeg atomFirst atomSecond then -1 else 1 := by
  fin_cases atomFirst <;> fin_cases atomSecond <;>
    norm_num [edgeSign, atomPairing, sectorDiamondDesign, sectorDiamondAtom, sectorDiamondNeg, dotProduct,
      Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]

/-- **Its two-graph is the class representative `55`.** -/
theorem sectorDiamondDesign_linkWordOf : linkWordOf sectorDiamondDesign = 55 := by
  rw [linkWordOf_eq_packTenBits_of_negTable sectorDiamondDesign sectorDiamondNeg sectorDiamondDesign_edgeSign]
  decide

/-- **The class survives every lever, and this design realises it.** -/
theorem sectorDiamondDesign_linkWord_mem_residualSectors :
    linkWordOf sectorDiamondDesign ∈ residualSectors := by
  rw [sectorDiamondDesign_linkWordOf, mem_residualSectors_iff]
  exact ⟨by norm_num, by decide +kernel⟩

/-- The witness is ALL-HEAVY, so the crux field `isAllHeavy` removes no class. -/
theorem sectorDiamondDesign_allHeavy : AllHeavy sectorDiamondDesign := by
  intro atomIndex
  fin_cases atomIndex <;>
    norm_num [leverageOf, sectorDiamondDesign, sectorDiamondAtom, Fin.sum_univ_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]

/-- No two of its atoms are parallel: it really spans six distinct lines, so the
crux field `hasNoParallelPair` removes no class either. -/
theorem sectorDiamondDesign_hasNoParallelPair : ¬ HasParallelPair sectorDiamondDesign := by
  rintro ⟨keptLabel, dropLabel, ratio, hne, hparallel⟩
  have hzero := pairGramMinor_eq_zero_of_smul sectorDiamondDesign hparallel
  rw [pairGramMinor] at hzero
  revert hzero
  fin_cases keptLabel <;> fin_cases dropLabel <;>
    first
      | exact fun _ => hne rfl
      | norm_num [sectorDiamondDesign, sectorDiamondAtom, leverageOf, dotProduct,
          Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]

/-- Its weights are not uniform, so it is off the equal-share stratum and the crux
field `avoidsEqualShareStratum` removes no class. -/
theorem sectorDiamondDesign_not_isEqualShare : ¬ IsEqualShare sectorDiamondDesign := by
  intro hequalShare
  have hweight := hequalShare.weight_eq 0
  norm_num [sectorDiamondDesign] at hweight

/-- Every one of its fifteen pairings is nonzero, so it is a witness for the
NONVANISHING branch that `Gtz.SixThreeCrux.linkWord_mem_residualSectors` needs. -/
theorem sectorDiamondDesign_atomPairing_ne_zero (atomFirst atomSecond : Fin 6)
    (hne : atomFirst ≠ atomSecond) :
    atomPairing sectorDiamondDesign atomFirst atomSecond ≠ 0 := by
  fin_cases atomFirst <;> fin_cases atomSecond <;>
    first
      | exact absurd rfl hne
      | norm_num [atomPairing, sectorDiamondDesign, sectorDiamondAtom, dotProduct,
          Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]

/-! ### SectorTadpole: link `185`, the class `Delta(tadpole), a triangle with a two-edge tail`

Leverages `6, 9/4, 2, 9/4, 6, 9/4`, shares `3/7, 9/28, 3/7, 9/14, 6/7, 9/28`; all-heavy, no parallel pair, every pairing
nonzero, off the equal-share stratum.  Its two-graph has `12` incoherent
triples and per-vertex coherent profile `[3, 3, 4, 4, 5, 5]`. -/
noncomputable def sectorTadpoleAtom : Fin 6 → Fin 3 → ℝ :=
  ![![1, -2, -1], ![1/2, 1, -1], ![1, 0, -1],
    ![1/2, -1, 1], ![2, 1, 1], ![1/2, -1, -1]]

/-- A genuine `(6,3)` design realising the class `Delta(tadpole), a triangle with a two-edge tail`. -/
noncomputable def sectorTadpoleDesign : WeightedDesign 6 3 where
  atom := sectorTadpoleAtom
  weight := ![1/14, 1/7, 3/14, 2/7, 1/7, 1/7]
  weight_pos := by intro atomIndex; fin_cases atomIndex <;> norm_num
  weight_sum_one := by
    simp only [Fin.sum_univ_six, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four, Matrix.cons_val, Matrix.tail_cons]
    norm_num
  isParseval := by
    ext rowIndex colIndex
    simp only [Matrix.sum_apply, Matrix.smul_apply, atomMatrix,
      Matrix.vecMulVec_apply, Fin.sum_univ_six, smul_eq_mul, sectorTadpoleAtom,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.cons_val, Matrix.tail_cons]
    fin_cases rowIndex <;> fin_cases colIndex <;> norm_num [Matrix.one_apply]

/-- Its fifteen pairing signs, `true` where the pairing is negative. -/
def sectorTadpoleNeg : Fin 6 → Fin 6 → Bool :=
  ![![false, true, false, false, true, false],
    ![true, false, false, true, false, false],
    ![false, false, false, true, false, false],
    ![false, true, true, false, false, false],
    ![true, false, false, false, false, true],
    ![false, false, false, false, true, false]]

theorem sectorTadpoleDesign_edgeSign (atomFirst atomSecond : Fin 6) :
    edgeSign sectorTadpoleDesign atomFirst atomSecond
      = if sectorTadpoleNeg atomFirst atomSecond then -1 else 1 := by
  fin_cases atomFirst <;> fin_cases atomSecond <;>
    norm_num [edgeSign, atomPairing, sectorTadpoleDesign, sectorTadpoleAtom, sectorTadpoleNeg, dotProduct,
      Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]

/-- **Its two-graph is the class representative `185`.** -/
theorem sectorTadpoleDesign_linkWordOf : linkWordOf sectorTadpoleDesign = 185 := by
  rw [linkWordOf_eq_packTenBits_of_negTable sectorTadpoleDesign sectorTadpoleNeg sectorTadpoleDesign_edgeSign]
  decide

/-- **The class survives every lever, and this design realises it.** -/
theorem sectorTadpoleDesign_linkWord_mem_residualSectors :
    linkWordOf sectorTadpoleDesign ∈ residualSectors := by
  rw [sectorTadpoleDesign_linkWordOf, mem_residualSectors_iff]
  exact ⟨by norm_num, by decide +kernel⟩

/-- The witness is ALL-HEAVY, so the crux field `isAllHeavy` removes no class. -/
theorem sectorTadpoleDesign_allHeavy : AllHeavy sectorTadpoleDesign := by
  intro atomIndex
  fin_cases atomIndex <;>
    norm_num [leverageOf, sectorTadpoleDesign, sectorTadpoleAtom, Fin.sum_univ_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]

/-- No two of its atoms are parallel: it really spans six distinct lines, so the
crux field `hasNoParallelPair` removes no class either. -/
theorem sectorTadpoleDesign_hasNoParallelPair : ¬ HasParallelPair sectorTadpoleDesign := by
  rintro ⟨keptLabel, dropLabel, ratio, hne, hparallel⟩
  have hzero := pairGramMinor_eq_zero_of_smul sectorTadpoleDesign hparallel
  rw [pairGramMinor] at hzero
  revert hzero
  fin_cases keptLabel <;> fin_cases dropLabel <;>
    first
      | exact fun _ => hne rfl
      | norm_num [sectorTadpoleDesign, sectorTadpoleAtom, leverageOf, dotProduct,
          Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]

/-- Its weights are not uniform, so it is off the equal-share stratum and the crux
field `avoidsEqualShareStratum` removes no class. -/
theorem sectorTadpoleDesign_not_isEqualShare : ¬ IsEqualShare sectorTadpoleDesign := by
  intro hequalShare
  have hweight := hequalShare.weight_eq 0
  norm_num [sectorTadpoleDesign] at hweight

/-- Every one of its fifteen pairings is nonzero, so it is a witness for the
NONVANISHING branch that `Gtz.SixThreeCrux.linkWord_mem_residualSectors` needs. -/
theorem sectorTadpoleDesign_atomPairing_ne_zero (atomFirst atomSecond : Fin 6)
    (hne : atomFirst ≠ atomSecond) :
    atomPairing sectorTadpoleDesign atomFirst atomSecond ≠ 0 := by
  fin_cases atomFirst <;> fin_cases atomSecond <;>
    first
      | exact absurd rfl hne
      | norm_num [atomPairing, sectorTadpoleDesign, sectorTadpoleAtom, dotProduct,
          Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]

/-! ### SectorIcosahedral: link `220`, the class `Delta(C5), the ICOSAHEDRAL two-graph -- self-complementary`

Leverages `4, 2, 2, 9/4, 9/4, 9`, shares `2/5, 2/5, 2/5, 9/20, 9/20, 9/10`; all-heavy, no parallel pair, every pairing
nonzero, off the equal-share stratum.  Its two-graph has `10` incoherent
triples and per-vertex coherent profile `[5, 5, 5, 5, 5, 5]`. -/
noncomputable def sectorIcosahedralAtom : Fin 6 → Fin 3 → ℝ :=
  ![![0, 0, 2], ![0, 1, -1], ![1, 0, -1],
    ![1, -1, 1/2], ![1, -1, -1/2], ![2, 2, 1]]

/-- A genuine `(6,3)` design realising the class `Delta(C5), the ICOSAHEDRAL two-graph -- self-complementary`. -/
noncomputable def sectorIcosahedralDesign : WeightedDesign 6 3 where
  atom := sectorIcosahedralAtom
  weight := ![1/10, 1/5, 1/5, 1/5, 1/5, 1/10]
  weight_pos := by intro atomIndex; fin_cases atomIndex <;> norm_num
  weight_sum_one := by
    simp only [Fin.sum_univ_six, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four, Matrix.cons_val, Matrix.tail_cons]
    norm_num
  isParseval := by
    ext rowIndex colIndex
    simp only [Matrix.sum_apply, Matrix.smul_apply, atomMatrix,
      Matrix.vecMulVec_apply, Fin.sum_univ_six, smul_eq_mul, sectorIcosahedralAtom,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.cons_val, Matrix.tail_cons]
    fin_cases rowIndex <;> fin_cases colIndex <;> norm_num [Matrix.one_apply]

/-- Its fifteen pairing signs, `true` where the pairing is negative. -/
def sectorIcosahedralNeg : Fin 6 → Fin 6 → Bool :=
  ![![false, true, true, false, true, false],
    ![true, false, false, true, true, false],
    ![true, false, false, false, false, false],
    ![false, true, false, false, false, false],
    ![true, true, false, false, false, true],
    ![false, false, false, false, true, false]]

theorem sectorIcosahedralDesign_edgeSign (atomFirst atomSecond : Fin 6) :
    edgeSign sectorIcosahedralDesign atomFirst atomSecond
      = if sectorIcosahedralNeg atomFirst atomSecond then -1 else 1 := by
  fin_cases atomFirst <;> fin_cases atomSecond <;>
    norm_num [edgeSign, atomPairing, sectorIcosahedralDesign, sectorIcosahedralAtom, sectorIcosahedralNeg, dotProduct,
      Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]

/-- **Its two-graph is the class representative `220`.** -/
theorem sectorIcosahedralDesign_linkWordOf : linkWordOf sectorIcosahedralDesign = 220 := by
  rw [linkWordOf_eq_packTenBits_of_negTable sectorIcosahedralDesign sectorIcosahedralNeg sectorIcosahedralDesign_edgeSign]
  decide

/-- **The class survives every lever, and this design realises it.** -/
theorem sectorIcosahedralDesign_linkWord_mem_residualSectors :
    linkWordOf sectorIcosahedralDesign ∈ residualSectors := by
  rw [sectorIcosahedralDesign_linkWordOf, mem_residualSectors_iff]
  exact ⟨by norm_num, by decide +kernel⟩

/-- The witness is ALL-HEAVY, so the crux field `isAllHeavy` removes no class. -/
theorem sectorIcosahedralDesign_allHeavy : AllHeavy sectorIcosahedralDesign := by
  intro atomIndex
  fin_cases atomIndex <;>
    norm_num [leverageOf, sectorIcosahedralDesign, sectorIcosahedralAtom, Fin.sum_univ_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]

/-- No two of its atoms are parallel: it really spans six distinct lines, so the
crux field `hasNoParallelPair` removes no class either. -/
theorem sectorIcosahedralDesign_hasNoParallelPair : ¬ HasParallelPair sectorIcosahedralDesign := by
  rintro ⟨keptLabel, dropLabel, ratio, hne, hparallel⟩
  have hzero := pairGramMinor_eq_zero_of_smul sectorIcosahedralDesign hparallel
  rw [pairGramMinor] at hzero
  revert hzero
  fin_cases keptLabel <;> fin_cases dropLabel <;>
    first
      | exact fun _ => hne rfl
      | norm_num [sectorIcosahedralDesign, sectorIcosahedralAtom, leverageOf, dotProduct,
          Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]

/-- Its weights are not uniform, so it is off the equal-share stratum and the crux
field `avoidsEqualShareStratum` removes no class. -/
theorem sectorIcosahedralDesign_not_isEqualShare : ¬ IsEqualShare sectorIcosahedralDesign := by
  intro hequalShare
  have hweight := hequalShare.weight_eq 0
  norm_num [sectorIcosahedralDesign] at hweight

/-- Every one of its fifteen pairings is nonzero, so it is a witness for the
NONVANISHING branch that `Gtz.SixThreeCrux.linkWord_mem_residualSectors` needs. -/
theorem sectorIcosahedralDesign_atomPairing_ne_zero (atomFirst atomSecond : Fin 6)
    (hne : atomFirst ≠ atomSecond) :
    atomPairing sectorIcosahedralDesign atomFirst atomSecond ≠ 0 := by
  fin_cases atomFirst <;> fin_cases atomSecond <;>
    first
      | exact absurd rfl hne
      | norm_num [atomPairing, sectorIcosahedralDesign, sectorIcosahedralAtom, dotProduct,
          Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]

/-! ## 3. Relabelling transport for the sign layer: SHIPPED

The harvested prototype carried four transport lemmas here -- `atomPairing`,
`edgeSign` and `tripleParity` along `Gtz.relabelDesign`, all three `rfl`, plus the
sector decode that follows from them.  All four are now in
`Gtz/Quantitative/EdgeOrbitSectors.lean` under the SAME NAMES and with the SAME
statements and proofs, so the block is gone and that module is imported instead;
every use below resolves to the shipped versions.

Nothing hard-errored while the duplicates were still present, because a duplicate
`Gtz`-level name in a different module is kept silently.  They were found by a kernel
`env.contains` scan of every name this module declares, not by the build. -/

/-! ## 4. The isomorphism invariant -/

/-- How many ORDERED pairs of other atoms make a COHERENT triple through this one.
Ordered rather than unordered so that relabelling acts by a product bijection. -/
def coherentDegree (link : Nat) (vertex : Fin 6) : Nat :=
  ∑ first : Fin 6, ∑ second : Fin 6,
    if vertex ≠ first ∧ vertex ≠ second ∧ first ≠ second
        ∧ sectorIncoherent link vertex first second = false then 1 else 0

/-- **THE INVARIANT.**  The sum of the squares of the coherent degrees.  It is a
symmetric function of the degree multiset, hence invariant under relabelling. -/
def coherentDegreeSquareSum (link : Nat) : Nat :=
  ∑ vertex : Fin 6, coherentDegree link vertex ^ 2

theorem coherentDegree_linkWordOf_relabelDesign (design : WeightedDesign 6 3)
    (relabel : Equiv.Perm (Fin 6)) (vertex : Fin 6) :
    coherentDegree (linkWordOf (relabelDesign design relabel)) vertex
      = coherentDegree (linkWordOf design) (relabel vertex) := by
  rw [coherentDegree, coherentDegree]
  rw [← Equiv.sum_comp relabel fun first =>
        ∑ second : Fin 6,
          if relabel vertex ≠ first ∧ relabel vertex ≠ second ∧ first ≠ second
              ∧ sectorIncoherent (linkWordOf design) (relabel vertex) first second = false
            then 1 else 0]
  refine Finset.sum_congr rfl fun first _ => ?_
  rw [← Equiv.sum_comp relabel fun second =>
        if relabel vertex ≠ relabel first ∧ relabel vertex ≠ second ∧ relabel first ≠ second
            ∧ sectorIncoherent (linkWordOf design) (relabel vertex) (relabel first) second
              = false then 1 else 0]
  refine Finset.sum_congr rfl fun second _ => ?_
  rw [sectorIncoherent_linkWordOf_relabelDesign]
  simp only [ne_eq, EmbeddingLike.apply_eq_iff_eq]

/-- **THE TRANSPORT.**  Relabelling a design does not move the invariant. -/
theorem coherentDegreeSquareSum_linkWordOf_relabelDesign (design : WeightedDesign 6 3)
    (relabel : Equiv.Perm (Fin 6)) :
    coherentDegreeSquareSum (linkWordOf (relabelDesign design relabel))
      = coherentDegreeSquareSum (linkWordOf design) := by
  rw [coherentDegreeSquareSum, coherentDegreeSquareSum]
  rw [← Equiv.sum_comp relabel fun vertex => coherentDegree (linkWordOf design) vertex ^ 2]
  exact Finset.sum_congr rfl fun vertex _ => by
    rw [coherentDegree_linkWordOf_relabelDesign]

/-- **THE SEPARATION CRITERION.**  Two designs whose invariants differ have two-graphs
that no relabelling identifies. -/
theorem linkWordOf_relabelDesign_ne_of_invariant_ne (designFirst designSecond : WeightedDesign 6 3)
    (relabel : Equiv.Perm (Fin 6))
    (hne : coherentDegreeSquareSum (linkWordOf designFirst)
      ≠ coherentDegreeSquareSum (linkWordOf designSecond)) :
    linkWordOf (relabelDesign designFirst relabel) ≠ linkWordOf designSecond := by
  intro hcontra
  exact hne ((coherentDegreeSquareSum_linkWordOf_relabelDesign designFirst relabel).symm.trans
    (congrArg coherentDegreeSquareSum hcontra))

/-! ## 5. The eight invariant values -/

/-- **THE EIGHT SURVIVING LINKS CARRY EIGHT DIFFERENT INVARIANTS**, so they really are
one representative per isomorphism class. -/
theorem coherentDegreeSquareSum_survivingClassRepresentatives :
    coherentDegreeSquareSum 19 = 696 ∧ coherentDegreeSquareSum 20 = 912
      ∧ coherentDegreeSquareSum 21 = 880 ∧ coherentDegreeSquareSum 23 = 648
      ∧ coherentDegreeSquareSum 55 = 432 ∧ coherentDegreeSquareSum 58 = 616
      ∧ coherentDegreeSquareSum 185 = 400 ∧ coherentDegreeSquareSum 220 = 600 := by
  decide +kernel


/-! ## 6. The eight witnesses as one indexed family -/

/-- The eight witnesses, in the order of `Gtz.sectorSurvives_survivingClassRepresentatives`. -/
noncomputable def sectorClassWitness : Fin 8 → WeightedDesign 6 3 :=
  ![sectorTriangleDesign, sectorTwoKTwoDesign, sectorPathFourDesign, sectorPawDesign,
    sectorDiamondDesign, sectorPathFiveDesign, sectorTadpoleDesign, sectorIcosahedralDesign]

/-- The eight class representatives, in the same order. -/
def sectorClassRepresentative : Fin 8 → Nat :=
  ![19, 20, 21, 23, 55, 58, 185, 220]

theorem sectorClassWitness_linkWordOf (classIndex : Fin 8) :
    linkWordOf (sectorClassWitness classIndex) = sectorClassRepresentative classIndex := by
  fin_cases classIndex <;>
    first
      | exact sectorTriangleDesign_linkWordOf
      | exact sectorTwoKTwoDesign_linkWordOf
      | exact sectorPathFourDesign_linkWordOf
      | exact sectorPawDesign_linkWordOf
      | exact sectorDiamondDesign_linkWordOf
      | exact sectorPathFiveDesign_linkWordOf
      | exact sectorTadpoleDesign_linkWordOf
      | exact sectorIcosahedralDesign_linkWordOf

/-- **THE RESIDUE IS SHARP.**  Each of the eight surviving representatives is the
two-graph of an explicit rational `(6,3)` design, so no correct sign-only argument
cuts any of the eight classes. -/
theorem sectorClassWitness_linkWord_mem_residualSectors (classIndex : Fin 8) :
    linkWordOf (sectorClassWitness classIndex) ∈ residualSectors := by
  rw [sectorClassWitness_linkWordOf]
  fin_cases classIndex <;> rw [mem_residualSectors_iff] <;>
    exact ⟨by decide, by decide +kernel⟩

/-- Every witness is ALL-HEAVY. -/
theorem sectorClassWitness_allHeavy (classIndex : Fin 8) :
    AllHeavy (sectorClassWitness classIndex) := by
  fin_cases classIndex <;>
    first
      | exact sectorTriangleDesign_allHeavy
      | exact sectorTwoKTwoDesign_allHeavy
      | exact sectorPathFourDesign_allHeavy
      | exact sectorPawDesign_allHeavy
      | exact sectorDiamondDesign_allHeavy
      | exact sectorPathFiveDesign_allHeavy
      | exact sectorTadpoleDesign_allHeavy
      | exact sectorIcosahedralDesign_allHeavy

/-- No witness has a parallel pair. -/
theorem sectorClassWitness_hasNoParallelPair (classIndex : Fin 8) :
    ¬ HasParallelPair (sectorClassWitness classIndex) := by
  fin_cases classIndex <;>
    first
      | exact sectorTriangleDesign_hasNoParallelPair
      | exact sectorTwoKTwoDesign_hasNoParallelPair
      | exact sectorPathFourDesign_hasNoParallelPair
      | exact sectorPawDesign_hasNoParallelPair
      | exact sectorDiamondDesign_hasNoParallelPair
      | exact sectorPathFiveDesign_hasNoParallelPair
      | exact sectorTadpoleDesign_hasNoParallelPair
      | exact sectorIcosahedralDesign_hasNoParallelPair

/-- No witness is on the equal-share stratum. -/
theorem sectorClassWitness_not_isEqualShare (classIndex : Fin 8) :
    ¬ IsEqualShare (sectorClassWitness classIndex) := by
  fin_cases classIndex <;>
    first
      | exact sectorTriangleDesign_not_isEqualShare
      | exact sectorTwoKTwoDesign_not_isEqualShare
      | exact sectorPathFourDesign_not_isEqualShare
      | exact sectorPawDesign_not_isEqualShare
      | exact sectorDiamondDesign_not_isEqualShare
      | exact sectorPathFiveDesign_not_isEqualShare
      | exact sectorTadpoleDesign_not_isEqualShare
      | exact sectorIcosahedralDesign_not_isEqualShare

/-- **AND THE EIGHT ARE PAIRWISE NON-ISOMORPHIC**: no relabelling of one witness has
the two-graph of another, so they really do occupy eight DIFFERENT classes.  This turns
the phrase "eight of the sixteen isomorphism classes" from an attribution to an
out-of-kernel `S6` enumeration into a theorem. -/
theorem sectorClassWitness_pairwise_nonisomorphic (classFirst classSecond : Fin 8)
    (hne : classFirst ≠ classSecond) (relabel : Equiv.Perm (Fin 6)) :
    linkWordOf (relabelDesign (sectorClassWitness classFirst) relabel)
      ≠ linkWordOf (sectorClassWitness classSecond) := by
  refine linkWordOf_relabelDesign_ne_of_invariant_ne _ _ relabel ?_
  rw [sectorClassWitness_linkWordOf, sectorClassWitness_linkWordOf]
  revert hne
  fin_cases classFirst <;> fin_cases classSecond <;> decide +kernel

end Gtz
