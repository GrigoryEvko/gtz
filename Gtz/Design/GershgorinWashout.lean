import Gtz.Wave.KFourPolynomialBudgetCells

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3200000

/-!
# The Gershgorin washout

The bad-edge pigeonhole route reads, from each failed tree cell, one
diagonally non-dominant row of the unsigned cell.  This module refutes the
route.  One rational chart point satisfies the bad-row condition of ALL
sixteen spanning trees at one time, and nine trees are strictly dominating
there.  Thus the sixteen-row necessary system cannot imply non-coverage, and
a covering proof must consume more of each dual witness than its Gershgorin
row.

The point puts the soft budget on the star of one vertex.  The masses are
`(1/100, 1/100, 1, 1/100, 1, 1)` and the weights are
`(8/25, 8/25, 1/75, 8/25, 1/75, 1/75)` in the edge labelling of
`Gtz.kFourDirection`.  The exact floors are `17/800` on the soft labels
`{0, 1, 3}` and `74` on the hard labels `{2, 4, 5}`.

* `KFourGershgorinRowSystem` — the conjunction of one `ZThreeBadRow` per
  spanning tree, on the exact unsigned cell entries.  The seven ledger paths
  use their committed `KFourPath*BadRow` forms.
* `gershgorinWashoutPoint_rowSystem` — the point satisfies the full system.
* `gershgorinWashoutPoint_pathCell025Fires` — the `{0, 2, 5}` minor cell
  fires there, with exact minors `1/800`, `3633/40000`, `52962717/8000000`.
* `kFourGershgorinRow_washout` — the package: the full necessary system and
  a strict spanning tree hold at one point.
-/

namespace Gtz

/-- The washout masses: soft star `{0, 1, 3}` at `1/100`, triangle at one. -/
noncomputable def gershgorinWashoutMass : Fin 6 → ℝ
  | 0 => 1 / 100
  | 1 => 1 / 100
  | 2 => 1
  | 3 => 1 / 100
  | 4 => 1
  | 5 => 1

/-- The washout weights: the star carries `24/25`, the triangle `1/25`. -/
noncomputable def gershgorinWashoutWeight : Fin 6 → ℝ
  | 0 => 8 / 25
  | 1 => 8 / 25
  | 2 => 1 / 75
  | 3 => 8 / 25
  | 4 => 1 / 75
  | 5 => 1 / 75

/-- The washout chart point. -/
noncomputable def gershgorinWashoutPoint : DirectionChartPoint 6 where
  mass := gershgorinWashoutMass
  weight := gershgorinWashoutWeight
  mass_pos := by intro label; fin_cases label <;> norm_num [gershgorinWashoutMass]
  weight_pos := by intro label; fin_cases label <;> norm_num [gershgorinWashoutWeight]
  weight_sum_one := by rw [Fin.sum_univ_six]; norm_num [gershgorinWashoutWeight]

@[simp] theorem gershgorinWashoutPoint_mass_eq :
    gershgorinWashoutPoint.mass = gershgorinWashoutMass := rfl

@[simp] theorem gershgorinWashoutPoint_weight_eq :
    gershgorinWashoutPoint.weight = gershgorinWashoutWeight := rfl

/-- **The sixteen-row Gershgorin system.**  For each spanning tree, the
`ZThreeBadRow` alternative of its exact unsigned cell: the diagonal carries
the exact floor minus the demand diagonal, and the off entries are the
negative unsigned demand sums.  The seven ledger paths appear through their
committed `KFourPath*BadRow` forms; the four stars, the band tree, and the
four pendant trees appear with the same entry convention written out.  Each
conjunct is the necessary Gershgorin consequence of the failure of that
tree's cell, through the Z-matrix dual witness. -/
def KFourGershgorinRowSystem (point : DirectionChartPoint 6) : Prop :=
  KFourPath015BadRow point ∧ KFourPath025BadRow point ∧ KFourPath035BadRow point ∧
  KFourPath045BadRow point ∧ KFourPath014BadRow point ∧ KFourPath124BadRow point ∧
  KFourPath145BadRow point ∧
  ZThreeBadRow
    (directionChartExactFloor point 0 - (point.mass 2 + point.mass 4))
    (-point.mass 2) (-point.mass 4)
    (directionChartExactFloor point 1 - (point.mass 2 + point.mass 5))
    (-point.mass 5)
    (directionChartExactFloor point 3 - (point.mass 4 + point.mass 5)) ∧
  ZThreeBadRow
    (directionChartExactFloor point 0 - (point.mass 1 + point.mass 3))
    (-point.mass 1) (-point.mass 3)
    (directionChartExactFloor point 2 - (point.mass 1 + point.mass 5))
    (-point.mass 5)
    (directionChartExactFloor point 4 - (point.mass 3 + point.mass 5)) ∧
  ZThreeBadRow
    (directionChartExactFloor point 1 - (point.mass 0 + point.mass 3))
    (-point.mass 0) (-point.mass 3)
    (directionChartExactFloor point 2 - (point.mass 0 + point.mass 4))
    (-point.mass 4)
    (directionChartExactFloor point 5 - (point.mass 3 + point.mass 4)) ∧
  ZThreeBadRow
    (directionChartExactFloor point 3 - (point.mass 0 + point.mass 1))
    (-point.mass 0) (-point.mass 1)
    (directionChartExactFloor point 4 - (point.mass 0 + point.mass 2))
    (-point.mass 2)
    (directionChartExactFloor point 5 - (point.mass 1 + point.mass 2)) ∧
  ZThreeBadRow
    (directionChartExactFloor point 1 - (point.mass 2 + point.mass 5))
    (-(point.mass 2 + point.mass 5)) (-point.mass 2)
    (directionChartExactFloor point 3 - (point.mass 0 + point.mass 2 + point.mass 5))
    (-(point.mass 0 + point.mass 2))
    (directionChartExactFloor point 4 - (point.mass 0 + point.mass 2)) ∧
  ZThreeBadRow
    (directionChartExactFloor point 0 - (point.mass 1 + point.mass 4 + point.mass 5))
    (-(point.mass 1 + point.mass 5)) (-(point.mass 4 + point.mass 5))
    (directionChartExactFloor point 2 - (point.mass 1 + point.mass 5))
    (-point.mass 5)
    (directionChartExactFloor point 3 - (point.mass 4 + point.mass 5)) ∧
  ZThreeBadRow
    (directionChartExactFloor point 1 - (point.mass 0 + point.mass 4 + point.mass 5))
    (-(point.mass 0 + point.mass 4)) (-(point.mass 4 + point.mass 5))
    (directionChartExactFloor point 2 - (point.mass 0 + point.mass 4))
    (-point.mass 4)
    (directionChartExactFloor point 3 - (point.mass 4 + point.mass 5)) ∧
  ZThreeBadRow
    (directionChartExactFloor point 2 - (point.mass 1 + point.mass 5))
    (-point.mass 1) (-(point.mass 1 + point.mass 5))
    (directionChartExactFloor point 3 - (point.mass 0 + point.mass 1))
    (-(point.mass 0 + point.mass 1))
    (directionChartExactFloor point 4 - (point.mass 0 + point.mass 1 + point.mass 5)) ∧
  ZThreeBadRow
    (directionChartExactFloor point 2 - (point.mass 0 + point.mass 4))
    (-point.mass 0) (-(point.mass 0 + point.mass 4))
    (directionChartExactFloor point 3 - (point.mass 0 + point.mass 1))
    (-(point.mass 0 + point.mass 1))
    (directionChartExactFloor point 5 - (point.mass 0 + point.mass 1 + point.mass 4))

/-- The washout point satisfies every one of the sixteen bad rows.  The four
star rows and the ledger row of the two light paths sit at the soft floor
`17/800` against the bound `1/25`; every other row has a hard mass in its
bound.  The two `{2,3}` pendant trees read their middle row. -/
theorem gershgorinWashoutPoint_rowSystem :
    KFourGershgorinRowSystem gershgorinWashoutPoint := by
  refine ⟨Or.inl ?_, Or.inl ?_, Or.inl ?_, Or.inl ?_, Or.inl ?_, Or.inl ?_,
    Or.inl ?_, Or.inl ?_, Or.inl ?_, Or.inl ?_, Or.inl ?_, Or.inl ?_,
    Or.inl ?_, Or.inl ?_, Or.inr (Or.inl ?_), Or.inr (Or.inl ?_)⟩ <;>
  · simp only [directionChartExactFloor,
      gershgorinWashoutPoint_mass_eq, gershgorinWashoutPoint_weight_eq]
    norm_num [gershgorinWashoutMass, gershgorinWashoutWeight]

/-- The `{0, 2, 5}` path minor cell fires at the washout point, with the
exact floors and the exact minors `1/800`, `3633/40000`, `52962717/8000000`. -/
theorem gershgorinWashoutPoint_pathCell025Fires :
    KFourPathCell025Fires gershgorinWashoutPoint := by
  refine ⟨17 / 800, 74, 74, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [gershgorinWashoutMass, gershgorinWashoutWeight]

/-- A strict spanning tree at the washout point. -/
theorem gershgorinWashoutPoint_hasStrictTree :
    ∃ tree ∈ kFourSpanningTreeList,
      (directionChartGap kFourDirection gershgorinWashoutPoint.mass
        gershgorinWashoutPoint.weight tree).PosDef :=
  kFourAtlas_hasStrictTree_of_pathCell025 gershgorinWashoutPoint
    gershgorinWashoutPoint_pathCell025Fires

/-- **THE WASHOUT.**  The full sixteen-row Gershgorin system and a strict
spanning tree hold at one chart point.  No argument from the sixteen bad
rows and the chart laws can conclude that no tree is strict. -/
theorem kFourGershgorinRow_washout :
    KFourGershgorinRowSystem gershgorinWashoutPoint ∧
      ∃ tree ∈ kFourSpanningTreeList,
        (directionChartGap kFourDirection gershgorinWashoutPoint.mass
          gershgorinWashoutPoint.weight tree).PosDef :=
  ⟨gershgorinWashoutPoint_rowSystem, gershgorinWashoutPoint_hasStrictTree⟩

/-- The route form of the washout: the Gershgorin row system does not force
the absence of a strict tree. -/
theorem kFourGershgorinRowSystem_not_forces_noStrict :
    ¬ ∀ point : DirectionChartPoint 6, KFourGershgorinRowSystem point →
      ¬ ∃ tree ∈ kFourSpanningTreeList,
        (directionChartGap kFourDirection point.mass point.weight tree).PosDef := by
  intro hforce
  exact hforce gershgorinWashoutPoint gershgorinWashoutPoint_rowSystem
    gershgorinWashoutPoint_hasStrictTree

end Gtz
