/-
# The fallback selector for branch (ii) is also FALSE — kernel-checked

After `pureTripleZeroSumSelection_refuted` killed the pure-triple selection on
the interior residual stratum, one fallback remained: on the zero-sum slice the
stress walk is free (gaps are walk-invariant), so a closing selector may also
consult the free-mass budget at the WALKED weight stations — in particular at
both walk ENDPOINTS, where the p16 endpoint gauge lives.  At the first exact
witness the budget indeed fires at the walked `+` endpoint.

This file refutes the union selector outright: an exact rational configuration
in the diagonal two-frame gauge, primitive, full-support zero-sum stress, with
the free-mass budget failing at ALL twenty triples at the interior weights AND
at BOTH exact walk endpoints, no stress mass gap in either orientation at any
of the three stations — and BOTH pure triples still fail to dominate.  Any
selector closing branch (ii) must therefore output MIXED triples on the
residual stratum; neither pure sides nor walked-budget firing can cover it. -/
import Mathlib
import Gtz.Core.Basic
import Gtz.LinAlg.SchurRankOne
import Gtz.Reduction.StressMassGap

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 4000000

namespace Gtz
namespace OrbitPureTripleRefutation

open Matrix

/-! ## The certificates at raw level -/

/-- The free-mass budget of `Gtz.HasFreeMassBudget`, phrased on a raw weighted
family (the walked stations carry a zero weight, so they are not designs). -/
def RawFreeMassBudget (baseAtom : Fin 6 → Fin 3 → ℝ) (weight : Fin 6 → ℝ)
    (selected : Finset (Fin 6)) : Prop :=
  (∑ d ∈ selected, (1 - weight d) • atomMatrix (baseAtom d)).PosDef
  ∧ ∑ c ∈ selectedᶜ, weight c
      * (baseAtom c ⬝ᵥ ((∑ d ∈ selected,
          (1 - weight d) • atomMatrix (baseAtom d))⁻¹ *ᵥ baseAtom c)) < 1

/-- The stress mass gap of `Gtz.HasStressMassGap`, phrased on raw weights. -/
def RawStressMassGap (weight stressCoeff : Fin 6 → ℝ) : Prop :=
  ∃ freeFloor boundCeiling : ℝ,
    (∀ c, 0 < stressCoeff c → freeFloor * stressCoeff c ≤ 1 - weight c)
    ∧ (∀ c, stressCoeff c < 0 → weight c ≤ boundCeiling * (-stressCoeff c))
    ∧ boundCeiling < freeFloor

/-! ## The fallback conjecture under refutation -/

/-- **The orbit-union selection conjecture.**  In the diagonal two-frame gauge,
if the residual hypotheses hold at the interior weights AND at both walked
endpoints of the zero-sum stress walk, then a pure stress side dominates. -/
def PureTripleOrbitSelectionSixThree : Prop :=
  ∀ (baseAtom : Fin 6 → Fin 3 → ℝ)
    (weight stressCoeff walkedPos walkedNeg : Fin 6 → ℝ) (stepPos stepNeg : ℝ),
    (∀ c, 0 < weight c) → (∑ c, weight c = 1) →
    (∀ c, stressCoeff c ≠ 0) → (∑ c, stressCoeff c) = 0 →
    (∑ c, stressCoeff c • atomMatrix (baseAtom c)) = 0 →
    (∀ c : Fin 6, c.val < 3 → 0 < stressCoeff c) →
    (∀ c : Fin 6, 3 ≤ c.val → stressCoeff c < 0) →
    (∀ (c : Fin 6) (coord : Fin 3), c.val < 3 → coord.val ≠ c.val →
      baseAtom c coord = 0) →
    (∑ c ∈ ({0, 1, 2} : Finset (Fin 6)),
      stressCoeff c • atomMatrix (baseAtom c)) = 1 →
    (∑ c ∈ ({3, 4, 5} : Finset (Fin 6)),
      (-stressCoeff c) • atomMatrix (baseAtom c)) = 1 →
    (∀ (keptLabel dropLabel : Fin 6) (ratio : ℝ), keptLabel ≠ dropLabel →
      baseAtom dropLabel ≠ ratio • baseAtom keptLabel) →
    0 ≤ stepPos → 0 ≤ stepNeg →
    walkedPos = (fun c => weight c - stepPos * stressCoeff c) →
    walkedNeg = (fun c => weight c + stepNeg * stressCoeff c) →
    (∀ c, 0 ≤ walkedPos c) → (∀ c, 0 ≤ walkedNeg c) →
    (∃ c, 0 < stressCoeff c ∧ walkedPos c = 0) →
    (∃ c, stressCoeff c < 0 ∧ walkedNeg c = 0) →
    (∀ station : Fin 6 → ℝ,
      station = weight ∨ station = walkedPos ∨ station = walkedNeg →
      ¬ RawStressMassGap station stressCoeff
      ∧ ¬ RawStressMassGap station (-stressCoeff)
      ∧ ∀ triple : Finset (Fin 6), triple.card = 3 →
          ¬ RawFreeMassBudget baseAtom station triple) →
    ((∑ c ∈ ({0, 1, 2} : Finset (Fin 6)), atomMatrix (baseAtom c))
        - ∑ c, weight c • atomMatrix (baseAtom c)).PosDef
      ∨ ((∑ c ∈ ({3, 4, 5} : Finset (Fin 6)), atomMatrix (baseAtom c))
        - ∑ c, weight c • atomMatrix (baseAtom c)).PosDef

/-! ## General lemmas (self-contained duplicates of the sibling file's kit) -/

theorem two_mul_dot_sub_form_le_inverseForm {rank : ℕ}
    {gramMat : Matrix (Fin rank) (Fin rank) ℝ} (hposDef : gramMat.PosDef)
    (source multiplier : Fin rank → ℝ) :
    2 * (source ⬝ᵥ multiplier) - multiplier ⬝ᵥ (gramMat *ᵥ multiplier)
      ≤ source ⬝ᵥ (gramMat⁻¹ *ᵥ source) := by
  have hdet : IsUnit gramMat.det := isUnit_iff_ne_zero.mpr (ne_of_gt hposDef.det_pos)
  have htranspose : gramMatᵀ = gramMat := transpose_eq_of_isHermitian hposDef.1
  set dual : Fin rank → ℝ := gramMat⁻¹ *ᵥ source with hdual
  have hmulDual : gramMat *ᵥ dual = source := by
    rw [hdual, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv gramMat hdet,
      Matrix.one_mulVec]
  have hformNonneg : 0 ≤ (multiplier - dual) ⬝ᵥ (gramMat *ᵥ (multiplier - dual)) := by
    have hstep := (Matrix.posSemidef_iff_dotProduct_mulVec.mp
      hposDef.posSemidef).2 (multiplier - dual)
    rwa [star_trivial] at hstep
  have hexpand : (multiplier - dual) ⬝ᵥ (gramMat *ᵥ (multiplier - dual))
      = multiplier ⬝ᵥ (gramMat *ᵥ multiplier) - multiplier ⬝ᵥ (gramMat *ᵥ dual)
        - dual ⬝ᵥ (gramMat *ᵥ multiplier) + dual ⬝ᵥ (gramMat *ᵥ dual) := by
    rw [Matrix.mulVec_sub, dotProduct_sub, sub_dotProduct, sub_dotProduct]
    ring
  have hcross : multiplier ⬝ᵥ (gramMat *ᵥ dual) = source ⬝ᵥ multiplier := by
    rw [hmulDual, dotProduct_comm]
  have hcross' : dual ⬝ᵥ (gramMat *ᵥ multiplier) = source ⬝ᵥ multiplier := by
    rw [dot_mulVec_comm htranspose, hmulDual, dotProduct_comm]
  have hself : dual ⬝ᵥ (gramMat *ᵥ dual) = source ⬝ᵥ (gramMat⁻¹ *ᵥ source) := by
    rw [hmulDual, dotProduct_comm, hdual]
  rw [hexpand, hcross, hcross', hself] at hformNonneg
  linarith [hformNonneg]

theorem sum_tripleFinset_eq {carrier : Type*} [AddCommMonoid carrier]
    {first second third : Fin 6} (hfs : first ≠ second) (hft : first ≠ third)
    (hst : second ≠ third) (summand : Fin 6 → carrier) :
    ∑ label ∈ ({first, second, third} : Finset (Fin 6)), summand label
      = summand first + summand second + summand third := by
  rw [show ({first, second, third} : Finset (Fin 6))
      = insert first (insert second {third}) from rfl,
    Finset.sum_insert (by simp [Finset.mem_insert, hfs, hft]),
    Finset.sum_insert (by simp [hst]), Finset.sum_singleton, add_assoc]

/-- Budget failure from a rational variational bound (nonnegative weights
suffice, so it applies at the walked endpoints). -/
theorem not_rawFreeMassBudget_of_bound (baseAtom : Fin 6 → Fin 3 → ℝ)
    (weight : Fin 6 → ℝ) (hweightNonneg : ∀ c, 0 ≤ weight c)
    (selected : Finset (Fin 6)) (multiplier : Fin 6 → Fin 3 → ℝ)
    (hbound : 1 ≤ ∑ c ∈ selectedᶜ, weight c
        * (2 * (baseAtom c ⬝ᵥ multiplier c)
          - ∑ d ∈ selected, (1 - weight d) * (baseAtom d ⬝ᵥ multiplier c) ^ 2)) :
    ¬ RawFreeMassBudget baseAtom weight selected := by
  rintro ⟨hfreePosDef, hspend⟩
  have hlower : ∀ c ∈ selectedᶜ,
      weight c * (2 * (baseAtom c ⬝ᵥ multiplier c)
          - ∑ d ∈ selected, (1 - weight d) * (baseAtom d ⬝ᵥ multiplier c) ^ 2)
        ≤ weight c * (baseAtom c ⬝ᵥ ((∑ d ∈ selected,
            (1 - weight d) • atomMatrix (baseAtom d))⁻¹ *ᵥ baseAtom c)) := by
    intro c _
    refine mul_le_mul_of_nonneg_left ?_ (hweightNonneg c)
    have hform : multiplier c ⬝ᵥ ((∑ d ∈ selected,
        (1 - weight d) • atomMatrix (baseAtom d)) *ᵥ multiplier c)
        = ∑ d ∈ selected, (1 - weight d) * (baseAtom d ⬝ᵥ multiplier c) ^ 2 :=
      atomForm_eq_on_subset selected (fun d => 1 - weight d) baseAtom (multiplier c)
    have hstep := two_mul_dot_sub_form_le_inverseForm hfreePosDef (baseAtom c)
      (multiplier c)
    rw [hform] at hstep
    exact hstep
  have hchain := Finset.sum_le_sum hlower
  linarith [hbound, hchain, hspend]

/-- Mass-gap failure from one crossing pair, raw weights. -/
theorem not_rawStressMassGap_of_crossing {weight stressCoeff : Fin 6 → ℝ}
    (posLabel negLabel : Fin 6)
    (hpos : 0 < stressCoeff posLabel) (hneg : stressCoeff negLabel < 0)
    (hcross : (1 - weight posLabel) * (-stressCoeff negLabel)
      ≤ weight negLabel * stressCoeff posLabel) :
    ¬ RawStressMassGap weight stressCoeff := by
  rintro ⟨freeFloor, boundCeiling, hfree, hbound, hlt⟩
  have h1 := hfree posLabel hpos
  have h2 := hbound negLabel hneg
  have hnegPos : 0 < -stressCoeff negLabel := neg_pos.mpr hneg
  nlinarith [mul_le_mul_of_nonneg_right h1 hnegPos.le,
    mul_le_mul_of_nonneg_right h2 hpos.le, hcross,
    mul_pos hpos hnegPos, hlt]

/-- A raw witness vector refutes domination of a subset. -/
theorem raw_gap_not_posDef_of_witnessVec (baseAtom : Fin 6 → Fin 3 → ℝ)
    (baseWeight : Fin 6 → ℝ) (selected : Finset (Fin 6))
    (witnessVec : Fin 3 → ℝ) (hne : witnessVec ≠ 0)
    (hval : (∑ c ∈ selected, (baseAtom c ⬝ᵥ witnessVec) ^ 2)
        - (∑ c, baseWeight c * (baseAtom c ⬝ᵥ witnessVec) ^ 2) ≤ 0) :
    ¬ ((∑ c ∈ selected, atomMatrix (baseAtom c))
        - ∑ c, baseWeight c • atomMatrix (baseAtom c)).PosDef := by
  intro hposDef
  have hstep := (Matrix.posDef_iff_dotProduct_mulVec.mp hposDef).2 hne
  rw [star_trivial, Matrix.sub_mulVec, dotProduct_sub] at hstep
  have hleft : witnessVec ⬝ᵥ ((∑ c ∈ selected, atomMatrix (baseAtom c)) *ᵥ witnessVec)
      = ∑ c ∈ selected, (baseAtom c ⬝ᵥ witnessVec) ^ 2 := by
    have hstep' := atomForm_eq_on_subset selected (fun _ => (1 : ℝ)) baseAtom witnessVec
    simpa using hstep'
  have hright : witnessVec ⬝ᵥ ((∑ c, baseWeight c • atomMatrix (baseAtom c))
        *ᵥ witnessVec)
      = ∑ c, baseWeight c * (baseAtom c ⬝ᵥ witnessVec) ^ 2 :=
    atomForm_eq_on_subset Finset.univ baseWeight baseAtom witnessVec
  rw [hleft, hright] at hstep
  linarith [hstep, hval]

/-! ## The exact rational witness -/

/-- The six base atoms. -/
noncomputable def orbAtom : Fin 6 → Fin 3 → ℝ :=
  ![![(3558589414710400/6741036383772813 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(0 : ℝ), (24/131 : ℝ), (0 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (1 : ℝ)],
    ![(-104477880295/2810625863669 : ℝ), (-554488704000/2810625863669 : ℝ), (-1068336978000/2810625863669 : ℝ)],
    ![(-193995244800/241637517691 : ℝ), (-881248504717/2899650212292 : ℝ), (57087237760/241637517691 : ℝ)],
    ![(-57514467296447818433280000/714688623645309793334195729 : ℝ), (111370734851411582410752000/714688623645309793334195729 : ℝ), (-52179065173065528251836800/714688623645309793334195729 : ℝ)]]

/-- The interior weights. -/
noncomputable def orbWeight : Fin 6 → ℝ :=
  ![(62/243 : ℝ), (1/9 : ℝ), (37/486 : ℝ), (92/217 : ℝ), (54/505 : ℝ), (1423027/53258310 : ℝ)]

/-- The full-support zero-sum stress. -/
noncomputable def orbStress : Fin 6 → ℝ :=
  ![(45441571527348843790107997932969/12663558622488907235915868160000 : ℝ),
    (17161/576 : ℝ),
    (1 : ℝ),
    (-48841/9025 : ℝ),
    (-51984/41209 : ℝ),
    (-3158000604648360117368150090331121/113972027602400165123242813440000 : ℝ)]

/-- The walked weights at the `+` endpoint (a positive-side weight vanishes). -/
noncomputable def orbWalkPos : Fin 6 → ℝ :=
  ![(199485798591869738750944963324368533/825134329273270457958737310609120000 : ℝ), (0 : ℝ), (603853/8340246 : ℝ), (14927082108/33608531425 : ℝ), (39868255926/357129762745 : ℝ), (335997199242304465096016446979041799977/2583495584954609803868806519517154720000 : ℝ)]

/-- The walked weights at the `-` endpoint (a negative-side weight vanishes). -/
noncomputable def orbWalkNeg : Fin 6 → ℝ :=
  ![(43494598785141065177450756354239082647807/168189775182549804122429321637382844865510 : ℝ), (335997199242304465096016446979041799977/2402711074036425773177561737676897783793 : ℝ), (370478760975926023081743307831191742487/4805422148072851546355123475353795567586 : ℝ), (782539541892605429562426718226435769284/1868775279806108934693659129304253831839 : ℝ), (15679062650754432909857137195890569662/148315498397310232912195168992401097765 : ℝ), (0 : ℝ)]

/-- Witness vector against the positive pure triple. -/
noncomputable def orbWitnessPos : Fin 3 → ℝ := ![(29/164 : ℝ), (1 : ℝ), (5/221 : ℝ)]

/-- Witness vector against the negative pure triple. -/
noncomputable def orbWitnessNeg : Fin 3 → ℝ := ![(158/251 : ℝ), (-188/231 : ℝ), (1 : ℝ)]

/-- Budget multipliers, station `Int`, triple `{0, 1, 2}`. -/
noncomputable def orbMultInt0 : Fin 6 → Fin 3 → ℝ :=
  ![![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(-12/67 : ℝ), (-1382/209 : ℝ), (-72/175 : ℝ)],
    ![(-731/189 : ℝ), (-2567/252 : ℝ), (56/219 : ℝ)],
    ![(-88/227 : ℝ), (679/130 : ℝ), (-20/253 : ℝ)]]

/-- Budget multipliers, station `Int`, triple `{0, 1, 3}`. -/
noncomputable def orbMultInt1 : Fin 6 → Fin 3 → ℝ :=
  ![![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(-106/225 : ℝ), (-3775/217 : ℝ), (5125/243 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(-947/238 : ℝ), (-3617/253 : ℝ), (756/71 : ℝ)],
    ![(-59/167 : ℝ), (474/73 : ℝ), (-198/47 : ℝ)]]

/-- Budget multipliers, station `Int`, triple `{0, 1, 4}`. -/
noncomputable def orbMultInt2 : Fin 6 → Fin 3 → ℝ :=
  ![![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(2603/159 : ℝ), (6252/145 : ℝ), (24527/187 : ℝ)],
    ![(-1402/219 : ℝ), (-23 : ℝ), (-13681/232 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(-334/211 : ℝ), (442/213 : ℝ), (-359/86 : ℝ)]]

/-- Budget multipliers, station `Int`, triple `{0, 1, 5}`. -/
noncomputable def orbMultInt3 : Fin 6 → Fin 3 → ℝ :=
  ![![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(-839/158 : ℝ), (17098/239 : ℝ), (68855/196 : ℝ)],
    ![(458/249 : ℝ), (-2603/77 : ℝ), (-32586/221 : ℝ)],
    ![(-461/90 : ℝ), (1672/249 : ℝ), (9893/151 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)]]

/-- Budget multipliers, station `Int`, triple `{0, 2, 3}`. -/
noncomputable def orbMultInt4 : Fin 6 → Fin 3 → ℝ :=
  ![![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(-42/253 : ℝ), (1028/115 : ℝ), (-81/212 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(-176/49 : ℝ), (-2437/167 : ℝ), (153/172 : ℝ)],
    ![(-118/223 : ℝ), (1417/181 : ℝ), (-101/250 : ℝ)]]

/-- Budget multipliers, station `Int`, triple `{0, 2, 4}`. -/
noncomputable def orbMultInt5 : Fin 6 → Fin 3 → ℝ :=
  ![![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(-429/184 : ℝ), (17/2 : ℝ), (39/253 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(443/190 : ℝ), (-9 : ℝ), (-138/239 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(-569/240 : ℝ), (1532/187 : ℝ), (5/96 : ℝ)]]

/-- Budget multipliers, station `Int`, triple `{0, 2, 5}`. -/
noncomputable def orbMultInt6 : Fin 6 → Fin 3 → ℝ :=
  ![![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(67/147 : ℝ), (1052/131 : ℝ), (21/226 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(-69/103 : ℝ), (-1197/134 : ℝ), (-89/174 : ℝ)],
    ![(-971/210 : ℝ), (-3891/256 : ℝ), (19/187 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)]]

/-- Budget multipliers, station `Int`, triple `{0, 3, 4}`. -/
noncomputable def orbMultInt7 : Fin 6 → Fin 3 → ℝ :=
  ![![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(-94/55 : ℝ), (455/89 : ℝ), (-261/206 : ℝ)],
    ![(625/143 : ℝ), (-1231/178 : ℝ), (1313/112 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(-175/81 : ℝ), (1373/245 : ℝ), (-585/256 : ℝ)]]

/-- Budget multipliers, station `Int`, triple `{0, 3, 5}`. -/
noncomputable def orbMultInt8 : Fin 6 → Fin 3 → ℝ :=
  ![![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(85/254 : ℝ), (1391/255 : ℝ), (-297/146 : ℝ)],
    ![(-353/249 : ℝ), (-2787/251 : ℝ), (3845/247 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(-1213/255 : ℝ), (-3087/235 : ℝ), (2023/247 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)]]

/-- Budget multipliers, station `Int`, triple `{0, 4, 5}`. -/
noncomputable def orbMultInt9 : Fin 6 → Fin 3 → ℝ :=
  ![![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(89/19 : ℝ), (6880/87 : ℝ), (26714/219 : ℝ)],
    ![(5271/107 : ℝ), (54597/82 : ℝ), (223477/208 : ℝ)],
    ![(-5053/211 : ℝ), (-64785/191 : ℝ), (-61198/113 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)]]

/-- Budget multipliers, station `Int`, triple `{1, 2, 3}`. -/
noncomputable def orbMultInt10 : Fin 6 → Fin 3 → ℝ :=
  ![![(267475/219 : ℝ), (-17936/191 : ℝ), (-409/70 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(-218525/121 : ℝ), (11008/83 : ℝ), (1033/113 : ℝ)],
    ![(-43259/203 : ℝ), (254/13 : ℝ), (125/154 : ℝ)]]

/-- Budget multipliers, station `Int`, triple `{1, 2, 4}`. -/
noncomputable def orbMultInt11 : Fin 6 → Fin 3 → ℝ :=
  ![![(816/233 : ℝ), (-1708/255 : ℝ), (19/113 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(331/155 : ℝ), (-1265/206 : ℝ), (-80/189 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(-332/131 : ℝ), (537/86 : ℝ), (-9/86 : ℝ)]]

/-- Budget multipliers, station `Int`, triple `{1, 2, 5}`. -/
noncomputable def orbMultInt12 : Fin 6 → Fin 3 → ℝ :=
  ![![(21230/141 : ℝ), (4831/141 : ℝ), (-127/245 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(-691/30 : ℝ), (-2157/239 : ℝ), (-3/8 : ℝ)],
    ![(-25641/103 : ℝ), (-15511/249 : ℝ), (71/68 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)]]

/-- Budget multipliers, station `Int`, triple `{1, 3, 4}`. -/
noncomputable def orbMultInt13 : Fin 6 → Fin 3 → ℝ :=
  ![![(995/163 : ℝ), (-1727/189 : ℝ), (149/25 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(2687/238 : ℝ), (-3973/253 : ℝ), (2116/113 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(-512/115 : ℝ), (1700/219 : ℝ), (-869/184 : ℝ)]]

/-- Budget multipliers, station `Int`, triple `{1, 3, 5}`. -/
noncomputable def orbMultInt14 : Fin 6 → Fin 3 → ℝ :=
  ![![(17296/75 : ℝ), (7759/166 : ℝ), (-6269/118 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(-15599/155 : ℝ), (-4247/163 : ℝ), (4715/129 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(-86302/215 : ℝ), (-16611/190 : ℝ), (1947/20 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)]]

/-- Budget multipliers, station `Int`, triple `{1, 4, 5}`. -/
noncomputable def orbMultInt15 : Fin 6 → Fin 3 → ℝ :=
  ![![(1377/223 : ℝ), (10/3 : ℝ), (1421/62 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(6469/149 : ℝ), (7814/121 : ℝ), (13896/59 : ℝ)],
    ![(-1982/109 : ℝ), (-1036/33 : ℝ), (-26593/256 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)]]

/-- Budget multipliers, station `Int`, triple `{2, 3, 4}`. -/
noncomputable def orbMultInt16 : Fin 6 → Fin 3 → ℝ :=
  ![![(1117/197 : ℝ), (-297/25 : ℝ), (114/181 : ℝ)],
    ![(-738/179 : ℝ), (1486/143 : ℝ), (-91/215 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(-107/24 : ℝ), (2445/226 : ℝ), (-84/157 : ℝ)]]

/-- Budget multipliers, station `Int`, triple `{2, 3, 5}`. -/
noncomputable def orbMultInt17 : Fin 6 → Fin 3 → ℝ :=
  ![![(18801/190 : ℝ), (3608/195 : ℝ), (-200/103 : ℝ)],
    ![(1631/254 : ℝ), (1333/253 : ℝ), (-25/98 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(-34508/213 : ℝ), (-6437/173 : ℝ), (523/144 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)]]

/-- Budget multipliers, station `Int`, triple `{2, 4, 5}`. -/
noncomputable def orbMultInt18 : Fin 6 → Fin 3 → ℝ :=
  ![![(586/203 : ℝ), (-50/9 : ℝ), (10/179 : ℝ)],
    ![(-295/153 : ℝ), (227/41 : ℝ), (7/68 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(460/251 : ℝ), (-295/51 : ℝ), (-131/249 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)]]

/-- Budget multipliers, station `Int`, triple `{3, 4, 5}`. -/
noncomputable def orbMultInt19 : Fin 6 → Fin 3 → ℝ :=
  ![![(805/241 : ℝ), (-235/49 : ℝ), (323/122 : ℝ)],
    ![(-243/146 : ℝ), (917/235 : ℝ), (-220/227 : ℝ)],
    ![(988/197 : ℝ), (-857/162 : ℝ), (233/20 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)]]

/-- Budget multipliers, station `WPos`, triple `{0, 1, 2}`. -/
noncomputable def orbMultWPos0 : Fin 6 → Fin 3 → ℝ :=
  ![![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(-19/108 : ℝ), (-1346/229 : ℝ), (-84/205 : ℝ)],
    ![(-965/254 : ℝ), (-1159/128 : ℝ), (27/106 : ℝ)],
    ![(-91/239 : ℝ), (65/14 : ℝ), (-17/216 : ℝ)]]

/-- Budget multipliers, station `WPos`, triple `{0, 1, 3}`. -/
noncomputable def orbMultWPos1 : Fin 6 → Fin 3 → ℝ :=
  ![![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(-56/121 : ℝ), (-634/41 : ℝ), (903/44 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(-985/252 : ℝ), (-2567/202 : ℝ), (2470/249 : ℝ)],
    ![(-59/170 : ℝ), (1264/219 : ℝ), (-689/178 : ℝ)]]

/-- Budget multipliers, station `WPos`, triple `{0, 1, 4}`. -/
noncomputable def orbMultWPos2 : Fin 6 → Fin 3 → ℝ :=
  ![![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(3329/207 : ℝ), (7397/193 : ℝ), (5089/41 : ℝ)],
    ![(-283/45 : ℝ), (-3210/157 : ℝ), (-3597/65 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(-311/200 : ℝ), (439/238 : ℝ), (-434/99 : ℝ)]]

/-- Budget multipliers, station `WPos`, triple `{0, 1, 5}`. -/
noncomputable def orbMultWPos3 : Fin 6 → Fin 3 → ℝ :=
  ![![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(-699/134 : ℝ), (1399/22 : ℝ), (30713/86 : ℝ)],
    ![(421/233 : ℝ), (-3065/102 : ℝ), (-31693/214 : ℝ)],
    ![(-1107/220 : ℝ), (191/32 : ℝ), (12739/184 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)]]

/-- Budget multipliers, station `WPos`, triple `{0, 2, 3}`. -/
noncomputable def orbMultWPos4 : Fin 6 → Fin 3 → ℝ :=
  ![![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(-33/202 : ℝ), (914/99 : ℝ), (-43/113 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(-621/176 : ℝ), (-1675/111 : ℝ), (101/114 : ℝ)],
    ![(-105/202 : ℝ), (1801/223 : ℝ), (-101/251 : ℝ)]]

/-- Budget multipliers, station `WPos`, triple `{0, 2, 4}`. -/
noncomputable def orbMultWPos5 : Fin 6 → Fin 3 → ℝ :=
  ![![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(-71/31 : ℝ), (689/82 : ℝ), (37/241 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(552/241 : ℝ), (-1905/214 : ℝ), (-134/233 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(-538/231 : ℝ), (793/98 : ℝ), (11/212 : ℝ)]]

/-- Budget multipliers, station `WPos`, triple `{0, 2, 5}`. -/
noncomputable def orbMultWPos6 : Fin 6 → Fin 3 → ℝ :=
  ![![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(30/67 : ℝ), (1351/151 : ℝ), (21/227 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(-102/155 : ℝ), (-1319/133 : ℝ), (-27/53 : ℝ)],
    ![(-377/83 : ℝ), (-1852/111 : ℝ), (17/168 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)]]

/-- Budget multipliers, station `WPos`, triple `{0, 3, 4}`. -/
noncomputable def orbMultWPos7 : Fin 6 → Fin 3 → ℝ :=
  ![![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(-183/109 : ℝ), (783/154 : ℝ), (-195/161 : ℝ)],
    ![(395/92 : ℝ), (-119/18 : ℝ), (2959/249 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(-503/237 : ℝ), (804/145 : ℝ), (-507/226 : ℝ)]]

/-- Budget multipliers, station `WPos`, triple `{0, 3, 5}`. -/
noncomputable def orbMultWPos8 : Fin 6 → Fin 3 → ℝ :=
  ![![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(64/195 : ℝ), (1521/251 : ℝ), (-489/211 : ℝ)],
    ![(-227/163 : ℝ), (-2239/177 : ℝ), (2073/124 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(-500/107 : ℝ), (-695/48 : ℝ), (811/91 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)]]

/-- Budget multipliers, station `WPos`, triple `{0, 4, 5}`. -/
noncomputable def orbMultWPos9 : Fin 6 → Fin 3 → ℝ :=
  ![![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(612/133 : ℝ), (19351/229 : ℝ), (14929/116 : ℝ)],
    ![(11227/232 : ℝ), (176322/251 : ℝ), (276364/247 : ℝ)],
    ![(-3270/139 : ℝ), (-58867/164 : ℝ), (-69013/122 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)]]

/-- Budget multipliers, station `WPos`, triple `{1, 2, 3}`. -/
noncomputable def orbMultWPos10 : Fin 6 → Fin 3 → ℝ :=
  ![![(196319/165 : ℝ), (-20701/248 : ℝ), (-902/155 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(-418075/237 : ℝ), (30062/255 : ℝ), (1129/124 : ℝ)],
    ![(-50688/247 : ℝ), (2883/166 : ℝ), (173/214 : ℝ)]]

/-- Budget multipliers, station `WPos`, triple `{1, 2, 4}`. -/
noncomputable def orbMultWPos11 : Fin 6 → Fin 3 → ℝ :=
  ![![(745/231 : ℝ), (-387/65 : ℝ), (35/209 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(199/106 : ℝ), (-1381/253 : ℝ), (-43/102 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(-509/224 : ℝ), (716/129 : ℝ), (-22/211 : ℝ)]]

/-- Budget multipliers, station `WPos`, triple `{1, 2, 5}`. -/
noncomputable def orbMultWPos12 : Fin 6 → Fin 3 → ℝ :=
  ![![(30169/197 : ℝ), (3076/101 : ℝ), (-95/184 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(-2005/92 : ℝ), (-1797/224 : ℝ), (-59/158 : ℝ)],
    ![(-46373/185 : ℝ), (-10576/191 : ℝ), (261/251 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)]]

/-- Budget multipliers, station `WPos`, triple `{1, 3, 4}`. -/
noncomputable def orbMultWPos13 : Fin 6 → Fin 3 → ℝ :=
  ![![(325/58 : ℝ), (-1860/229 : ℝ), (638/115 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(1135/108 : ℝ), (-3043/218 : ℝ), (1429/78 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(-631/157 : ℝ), (69/10 : ℝ), (-231/53 : ℝ)]]

/-- Budget multipliers, station `WPos`, triple `{1, 3, 5}`. -/
noncomputable def orbMultWPos14 : Fin 6 → Fin 3 → ℝ :=
  ![![(20161/88 : ℝ), (9182/221 : ℝ), (-9648/191 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(-12535/131 : ℝ), (-5350/231 : ℝ), (6623/189 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(-81754/207 : ℝ), (-16475/212 : ℝ), (21284/231 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)]]

/-- Budget multipliers, station `WPos`, triple `{1, 4, 5}`. -/
noncomputable def orbMultWPos15 : Fin 6 → Fin 3 → ℝ :=
  ![![(1589/237 : ℝ), (649/219 : ℝ), (6203/256 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(459/10 : ℝ), (10964/191 : ℝ), (26528/113 : ℝ)],
    ![(-4319/227 : ℝ), (-6809/244 : ℝ), (-8488/83 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)]]

/-- Budget multipliers, station `WPos`, triple `{2, 3, 4}`. -/
noncomputable def orbMultWPos16 : Fin 6 → Fin 3 → ℝ :=
  ![![(1477/254 : ℝ), (-3124/255 : ℝ), (69/110 : ℝ)],
    ![(-659/155 : ℝ), (601/56 : ℝ), (-43/102 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(-615/134 : ℝ), (1429/128 : ℝ), (-81/152 : ℝ)]]

/-- Budget multipliers, station `WPos`, triple `{2, 3, 5}`. -/
noncomputable def orbMultWPos17 : Fin 6 → Fin 3 → ℝ :=
  ![![(16852/159 : ℝ), (147/8 : ℝ), (-205/106 : ℝ)],
    ![(1607/252 : ℝ), (368/67 : ℝ), (-47/185 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(-32282/187 : ℝ), (-4187/112 : ℝ), (709/196 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)]]

/-- Budget multipliers, station `WPos`, triple `{2, 4, 5}`. -/
noncomputable def orbMultWPos18 : Fin 6 → Fin 3 → ℝ :=
  ![![(647/205 : ℝ), (-1145/183 : ℝ), (1/18 : ℝ)],
    ![(-76/35 : ℝ), (1230/199 : ℝ), (25/244 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(164/79 : ℝ), (-1427/222 : ℝ), (-98/187 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)]]

/-- Budget multipliers, station `WPos`, triple `{3, 4, 5}`. -/
noncomputable def orbMultWPos19 : Fin 6 → Fin 3 → ℝ :=
  ![![(810/221 : ℝ), (-1379/255 : ℝ), (301/102 : ℝ)],
    ![(-396/211 : ℝ), (1109/256 : ℝ), (-90/79 : ℝ)],
    ![(559/100 : ℝ), (-1281/206 : ℝ), (149/12 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)]]

/-- Budget multipliers, station `WNeg`, triple `{0, 1, 2}`. -/
noncomputable def orbMultWNeg0 : Fin 6 → Fin 3 → ℝ :=
  ![![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(-43/239 : ℝ), (-41/6 : ℝ), (-7/17 : ℝ)],
    ![(-136/35 : ℝ), (-2558/243 : ℝ), (32/125 : ℝ)],
    ![(-37/95 : ℝ), (1317/244 : ℝ), (-14/177 : ℝ)]]

/-- Budget multipliers, station `WNeg`, triple `{0, 1, 3}`. -/
noncomputable def orbMultWNeg1 : Fin 6 → Fin 3 → ℝ :=
  ![![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(-71/150 : ℝ), (-3973/221 : ℝ), (4789/225 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(-1023/256 : ℝ), (-1699/115 : ℝ), (935/86 : ℝ)],
    ![(-82/231 : ℝ), (1134/169 : ℝ), (-449/104 : ℝ)]]

/-- Budget multipliers, station `WNeg`, triple `{0, 1, 4}`. -/
noncomputable def orbMultWNeg2 : Fin 6 → Fin 3 → ℝ :=
  ![![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(3602/219 : ℝ), (2718/61 : ℝ), (21719/163 : ℝ)],
    ![(-1460/227 : ℝ), (-2995/126 : ℝ), (-12190/203 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(-361/227 : ℝ), (193/90 : ℝ), (-834/203 : ℝ)]]

/-- Budget multipliers, station `WNeg`, triple `{0, 1, 5}`. -/
noncomputable def orbMultWNeg3 : Fin 6 → Fin 3 → ℝ :=
  ![![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(-1115/209 : ℝ), (8354/113 : ℝ), (53043/151 : ℝ)],
    ![(401/217 : ℝ), (-7441/213 : ℝ), (-19672/133 : ℝ)],
    ![(-1127/219 : ℝ), (798/115 : ℝ), (2657/41 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)]]

/-- Budget multipliers, station `WNeg`, triple `{0, 2, 3}`. -/
noncomputable def orbMultWNeg4 : Fin 6 → Fin 3 → ℝ :=
  ![![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(-42/251 : ℝ), (133/15 : ℝ), (-96/251 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(-848/235 : ℝ), (-3111/215 : ℝ), (187/210 : ℝ)],
    ![(-42/79 : ℝ), (1103/142 : ℝ), (-91/225 : ℝ)]]

/-- Budget multipliers, station `WNeg`, triple `{0, 2, 4}`. -/
noncomputable def orbMultWNeg5 : Fin 6 → Fin 3 → ℝ :=
  ![![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(-431/184 : ℝ), (1492/175 : ℝ), (25/162 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(171/73 : ℝ), (-2103/233 : ℝ), (-100/173 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(-605/254 : ℝ), (1537/187 : ℝ), (11/211 : ℝ)]]

/-- Budget multipliers, station `WNeg`, triple `{0, 2, 5}`. -/
noncomputable def orbMultWNeg6 : Fin 6 → Fin 3 → ℝ :=
  ![![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(49/107 : ℝ), (446/57 : ℝ), (4/43 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(-142/211 : ℝ), (-1420/163 : ℝ), (-64/125 : ℝ)],
    ![(-655/141 : ℝ), (-223/15 : ℝ), (6/59 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)]]

/-- Budget multipliers, station `WNeg`, triple `{0, 3, 4}`. -/
noncomputable def orbMultWNeg7 : Fin 6 → Fin 3 → ℝ :=
  ![![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(-352/205 : ℝ), (1065/208 : ℝ), (-41/32 : ℝ)],
    ![(685/156 : ℝ), (-1070/153 : ℝ), (2372/203 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(-369/170 : ℝ), (1242/221 : ℝ), (-62/27 : ℝ)]]

/-- Budget multipliers, station `WNeg`, triple `{0, 3, 5}`. -/
noncomputable def orbMultWNeg8 : Fin 6 → Fin 3 → ℝ :=
  ![![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(48/143 : ℝ), (1085/204 : ℝ), (-205/104 : ℝ)],
    ![(-47/33 : ℝ), (-1474/137 : ℝ), (811/53 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(-411/86 : ℝ), (-1797/140 : ℝ), (1413/176 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)]]

/-- Budget multipliers, station `WNeg`, triple `{0, 4, 5}`. -/
noncomputable def orbMultWNeg9 : Fin 6 → Fin 3 → ℝ :=
  ![![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(1153/245 : ℝ), (8255/106 : ℝ), (24221/201 : ℝ)],
    ![(11779/238 : ℝ), (158516/241 : ℝ), (68143/64 : ℝ)],
    ![(-5245/218 : ℝ), (-33148/99 : ℝ), (-90637/169 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)]]

/-- Budget multipliers, station `WNeg`, triple `{1, 2, 3}`. -/
noncomputable def orbMultWNeg10 : Fin 6 → Fin 3 → ℝ :=
  ![![(109657/89 : ℝ), (-6890/71 : ℝ), (-1123/192 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(-395058/217 : ℝ), (31660/231 : ℝ), (787/86 : ℝ)],
    ![(-19194/89 : ℝ), (1797/89 : ℝ), (13/16 : ℝ)]]

/-- Budget multipliers, station `WNeg`, triple `{1, 2, 4}`. -/
noncomputable def orbMultWNeg11 : Fin 6 → Fin 3 → ℝ :=
  ![![(649/181 : ℝ), (-1239/179 : ℝ), (17/101 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(135/61 : ℝ), (-1009/159 : ℝ), (-25/59 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(-358/137 : ℝ), (955/148 : ℝ), (-11/105 : ℝ)]]

/-- Budget multipliers, station `WNeg`, triple `{1, 2, 5}`. -/
noncomputable def orbMultWNeg12 : Fin 6 → Fin 3 → ℝ :=
  ![![(22883/152 : ℝ), (2089/59 : ℝ), (-96/185 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(-3730/159 : ℝ), (-457/49 : ℝ), (-95/253 : ℝ)],
    ![(-23709/95 : ℝ), (-13261/206 : ℝ), (185/177 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)]]

/-- Budget multipliers, station `WNeg`, triple `{1, 3, 4}`. -/
noncomputable def orbMultWNeg13 : Fin 6 → Fin 3 → ℝ :=
  ![![(513/82 : ℝ), (-1237/131 : ℝ), (1047/172 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(1303/113 : ℝ), (-925/57 : ℝ), (434/23 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(-1132/247 : ℝ), (1837/229 : ℝ), (-730/151 : ℝ)]]

/-- Budget multipliers, station `WNeg`, triple `{1, 3, 5}`. -/
noncomputable def orbMultWNeg14 : Fin 6 → Fin 3 → ℝ :=
  ![![(50573/218 : ℝ), (6714/139 : ℝ), (-10803/200 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(-21385/209 : ℝ), (-4335/161 : ℝ), (3075/83 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(-78529/194 : ℝ), (-13823/153 : ℝ), (8422/85 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)]]

/-- Budget multipliers, station `WNeg`, triple `{1, 4, 5}`. -/
noncomputable def orbMultWNeg15 : Fin 6 → Fin 3 → ℝ :=
  ![![(497/82 : ℝ), (472/137 : ℝ), (635/28 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(10697/249 : ℝ), (10344/155 : ℝ), (43324/183 : ℝ)],
    ![(-4132/229 : ℝ), (-3666/113 : ℝ), (-419/4 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)]]

/-- Budget multipliers, station `WNeg`, triple `{2, 3, 4}`. -/
noncomputable def orbMultWNeg16 : Fin 6 → Fin 3 → ℝ :=
  ![![(1217/216 : ℝ), (-2617/222 : ℝ), (157/249 : ℝ)],
    ![(-1031/252 : ℝ), (2515/244 : ℝ), (-25/59 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(-239/54 : ℝ), (161/15 : ℝ), (-128/239 : ℝ)]]

/-- Budget multipliers, station `WNeg`, triple `{2, 3, 5}`. -/
noncomputable def orbMultWNeg17 : Fin 6 → Fin 3 → ℝ :=
  ![![(292/3 : ℝ), (3147/170 : ℝ), (-484/249 : ℝ)],
    ![(893/139 : ℝ), (1189/228 : ℝ), (-12/47 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(-15317/96 : ℝ), (-9209/248 : ℝ), (509/140 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)]]

/-- Budget multipliers, station `WNeg`, triple `{2, 4, 5}`. -/
noncomputable def orbMultWNeg18 : Fin 6 → Fin 3 → ℝ :=
  ![![(698/247 : ℝ), (-556/103 : ℝ), (8/143 : ℝ)],
    ![(-429/229 : ℝ), (771/143 : ℝ), (17/165 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(441/248 : ℝ), (-485/86 : ℝ), (-128/243 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)]]

/-- Budget multipliers, station `WNeg`, triple `{3, 4, 5}`. -/
noncomputable def orbMultWNeg19 : Fin 6 → Fin 3 → ℝ :=
  ![![(575/176 : ℝ), (-1132/243 : ℝ), (49/19 : ℝ)],
    ![(-97/60 : ℝ), (449/118 : ℝ), (-68/73 : ℝ)],
    ![(1236/253 : ℝ), (-1205/237 : ℝ), (2019/176 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)],
    ![(0 : ℝ), (0 : ℝ), (0 : ℝ)]]

/-! ### Evaluation lemmas -/

@[simp] theorem finSix_mk_two (h : 2 < 6) : (⟨2, h⟩ : Fin 6) = 2 := rfl
@[simp] theorem finSix_mk_three (h : 3 < 6) : (⟨3, h⟩ : Fin 6) = 3 := rfl
@[simp] theorem finSix_mk_four (h : 4 < 6) : (⟨4, h⟩ : Fin 6) = 4 := rfl
@[simp] theorem finSix_mk_five (h : 5 < 6) : (⟨5, h⟩ : Fin 6) = 5 := rfl
@[simp] theorem finThree_mk_two (h : 2 < 3) : (⟨2, h⟩ : Fin 3) = 2 := rfl

@[simp] theorem orbAtom_eval_0_0 : orbAtom 0 0 = (3558589414710400/6741036383772813 : ℝ) := rfl
@[simp] theorem orbAtom_eval_0_1 : orbAtom 0 1 = (0 : ℝ) := rfl
@[simp] theorem orbAtom_eval_0_2 : orbAtom 0 2 = (0 : ℝ) := rfl
@[simp] theorem orbAtom_eval_1_0 : orbAtom 1 0 = (0 : ℝ) := rfl
@[simp] theorem orbAtom_eval_1_1 : orbAtom 1 1 = (24/131 : ℝ) := rfl
@[simp] theorem orbAtom_eval_1_2 : orbAtom 1 2 = (0 : ℝ) := rfl
@[simp] theorem orbAtom_eval_2_0 : orbAtom 2 0 = (0 : ℝ) := rfl
@[simp] theorem orbAtom_eval_2_1 : orbAtom 2 1 = (0 : ℝ) := rfl
@[simp] theorem orbAtom_eval_2_2 : orbAtom 2 2 = (1 : ℝ) := rfl
@[simp] theorem orbAtom_eval_3_0 : orbAtom 3 0 = (-104477880295/2810625863669 : ℝ) := rfl
@[simp] theorem orbAtom_eval_3_1 : orbAtom 3 1 = (-554488704000/2810625863669 : ℝ) := rfl
@[simp] theorem orbAtom_eval_3_2 : orbAtom 3 2 = (-1068336978000/2810625863669 : ℝ) := rfl
@[simp] theorem orbAtom_eval_4_0 : orbAtom 4 0 = (-193995244800/241637517691 : ℝ) := rfl
@[simp] theorem orbAtom_eval_4_1 : orbAtom 4 1 = (-881248504717/2899650212292 : ℝ) := rfl
@[simp] theorem orbAtom_eval_4_2 : orbAtom 4 2 = (57087237760/241637517691 : ℝ) := rfl
@[simp] theorem orbAtom_eval_5_0 : orbAtom 5 0 = (-57514467296447818433280000/714688623645309793334195729 : ℝ) := rfl
@[simp] theorem orbAtom_eval_5_1 : orbAtom 5 1 = (111370734851411582410752000/714688623645309793334195729 : ℝ) := rfl
@[simp] theorem orbAtom_eval_5_2 : orbAtom 5 2 = (-52179065173065528251836800/714688623645309793334195729 : ℝ) := rfl
@[simp] theorem orbWeight_eval_0 : orbWeight 0 = (62/243 : ℝ) := rfl
@[simp] theorem orbWeight_eval_1 : orbWeight 1 = (1/9 : ℝ) := rfl
@[simp] theorem orbWeight_eval_2 : orbWeight 2 = (37/486 : ℝ) := rfl
@[simp] theorem orbWeight_eval_3 : orbWeight 3 = (92/217 : ℝ) := rfl
@[simp] theorem orbWeight_eval_4 : orbWeight 4 = (54/505 : ℝ) := rfl
@[simp] theorem orbWeight_eval_5 : orbWeight 5 = (1423027/53258310 : ℝ) := rfl
@[simp] theorem orbStress_eval_0 : orbStress 0 = (45441571527348843790107997932969/12663558622488907235915868160000 : ℝ) := rfl
@[simp] theorem orbStress_eval_1 : orbStress 1 = (17161/576 : ℝ) := rfl
@[simp] theorem orbStress_eval_2 : orbStress 2 = (1 : ℝ) := rfl
@[simp] theorem orbStress_eval_3 : orbStress 3 = (-48841/9025 : ℝ) := rfl
@[simp] theorem orbStress_eval_4 : orbStress 4 = (-51984/41209 : ℝ) := rfl
@[simp] theorem orbStress_eval_5 : orbStress 5 = (-3158000604648360117368150090331121/113972027602400165123242813440000 : ℝ) := rfl
@[simp] theorem orbWalkPos_eval_0 : orbWalkPos 0 = (199485798591869738750944963324368533/825134329273270457958737310609120000 : ℝ) := rfl
@[simp] theorem orbWalkPos_eval_1 : orbWalkPos 1 = (0 : ℝ) := rfl
@[simp] theorem orbWalkPos_eval_2 : orbWalkPos 2 = (603853/8340246 : ℝ) := rfl
@[simp] theorem orbWalkPos_eval_3 : orbWalkPos 3 = (14927082108/33608531425 : ℝ) := rfl
@[simp] theorem orbWalkPos_eval_4 : orbWalkPos 4 = (39868255926/357129762745 : ℝ) := rfl
@[simp] theorem orbWalkPos_eval_5 : orbWalkPos 5 = (335997199242304465096016446979041799977/2583495584954609803868806519517154720000 : ℝ) := rfl
@[simp] theorem orbWalkNeg_eval_0 : orbWalkNeg 0 = (43494598785141065177450756354239082647807/168189775182549804122429321637382844865510 : ℝ) := rfl
@[simp] theorem orbWalkNeg_eval_1 : orbWalkNeg 1 = (335997199242304465096016446979041799977/2402711074036425773177561737676897783793 : ℝ) := rfl
@[simp] theorem orbWalkNeg_eval_2 : orbWalkNeg 2 = (370478760975926023081743307831191742487/4805422148072851546355123475353795567586 : ℝ) := rfl
@[simp] theorem orbWalkNeg_eval_3 : orbWalkNeg 3 = (782539541892605429562426718226435769284/1868775279806108934693659129304253831839 : ℝ) := rfl
@[simp] theorem orbWalkNeg_eval_4 : orbWalkNeg 4 = (15679062650754432909857137195890569662/148315498397310232912195168992401097765 : ℝ) := rfl
@[simp] theorem orbWalkNeg_eval_5 : orbWalkNeg 5 = (0 : ℝ) := rfl
@[simp] theorem orbWitnessPos_eval_0 : orbWitnessPos 0 = (29/164 : ℝ) := rfl
@[simp] theorem orbWitnessPos_eval_1 : orbWitnessPos 1 = (1 : ℝ) := rfl
@[simp] theorem orbWitnessPos_eval_2 : orbWitnessPos 2 = (5/221 : ℝ) := rfl
@[simp] theorem orbWitnessNeg_eval_0 : orbWitnessNeg 0 = (158/251 : ℝ) := rfl
@[simp] theorem orbWitnessNeg_eval_1 : orbWitnessNeg 1 = (-188/231 : ℝ) := rfl
@[simp] theorem orbWitnessNeg_eval_2 : orbWitnessNeg 2 = (1 : ℝ) := rfl
@[simp] theorem orbMultInt0_eval_3_0 : orbMultInt0 3 0 = (-12/67 : ℝ) := rfl
@[simp] theorem orbMultInt0_eval_3_1 : orbMultInt0 3 1 = (-1382/209 : ℝ) := rfl
@[simp] theorem orbMultInt0_eval_3_2 : orbMultInt0 3 2 = (-72/175 : ℝ) := rfl
@[simp] theorem orbMultInt0_eval_4_0 : orbMultInt0 4 0 = (-731/189 : ℝ) := rfl
@[simp] theorem orbMultInt0_eval_4_1 : orbMultInt0 4 1 = (-2567/252 : ℝ) := rfl
@[simp] theorem orbMultInt0_eval_4_2 : orbMultInt0 4 2 = (56/219 : ℝ) := rfl
@[simp] theorem orbMultInt0_eval_5_0 : orbMultInt0 5 0 = (-88/227 : ℝ) := rfl
@[simp] theorem orbMultInt0_eval_5_1 : orbMultInt0 5 1 = (679/130 : ℝ) := rfl
@[simp] theorem orbMultInt0_eval_5_2 : orbMultInt0 5 2 = (-20/253 : ℝ) := rfl
@[simp] theorem orbMultInt1_eval_2_0 : orbMultInt1 2 0 = (-106/225 : ℝ) := rfl
@[simp] theorem orbMultInt1_eval_2_1 : orbMultInt1 2 1 = (-3775/217 : ℝ) := rfl
@[simp] theorem orbMultInt1_eval_2_2 : orbMultInt1 2 2 = (5125/243 : ℝ) := rfl
@[simp] theorem orbMultInt1_eval_4_0 : orbMultInt1 4 0 = (-947/238 : ℝ) := rfl
@[simp] theorem orbMultInt1_eval_4_1 : orbMultInt1 4 1 = (-3617/253 : ℝ) := rfl
@[simp] theorem orbMultInt1_eval_4_2 : orbMultInt1 4 2 = (756/71 : ℝ) := rfl
@[simp] theorem orbMultInt1_eval_5_0 : orbMultInt1 5 0 = (-59/167 : ℝ) := rfl
@[simp] theorem orbMultInt1_eval_5_1 : orbMultInt1 5 1 = (474/73 : ℝ) := rfl
@[simp] theorem orbMultInt1_eval_5_2 : orbMultInt1 5 2 = (-198/47 : ℝ) := rfl
@[simp] theorem orbMultInt2_eval_2_0 : orbMultInt2 2 0 = (2603/159 : ℝ) := rfl
@[simp] theorem orbMultInt2_eval_2_1 : orbMultInt2 2 1 = (6252/145 : ℝ) := rfl
@[simp] theorem orbMultInt2_eval_2_2 : orbMultInt2 2 2 = (24527/187 : ℝ) := rfl
@[simp] theorem orbMultInt2_eval_3_0 : orbMultInt2 3 0 = (-1402/219 : ℝ) := rfl
@[simp] theorem orbMultInt2_eval_3_1 : orbMultInt2 3 1 = (-23 : ℝ) := rfl
@[simp] theorem orbMultInt2_eval_3_2 : orbMultInt2 3 2 = (-13681/232 : ℝ) := rfl
@[simp] theorem orbMultInt2_eval_5_0 : orbMultInt2 5 0 = (-334/211 : ℝ) := rfl
@[simp] theorem orbMultInt2_eval_5_1 : orbMultInt2 5 1 = (442/213 : ℝ) := rfl
@[simp] theorem orbMultInt2_eval_5_2 : orbMultInt2 5 2 = (-359/86 : ℝ) := rfl
@[simp] theorem orbMultInt3_eval_2_0 : orbMultInt3 2 0 = (-839/158 : ℝ) := rfl
@[simp] theorem orbMultInt3_eval_2_1 : orbMultInt3 2 1 = (17098/239 : ℝ) := rfl
@[simp] theorem orbMultInt3_eval_2_2 : orbMultInt3 2 2 = (68855/196 : ℝ) := rfl
@[simp] theorem orbMultInt3_eval_3_0 : orbMultInt3 3 0 = (458/249 : ℝ) := rfl
@[simp] theorem orbMultInt3_eval_3_1 : orbMultInt3 3 1 = (-2603/77 : ℝ) := rfl
@[simp] theorem orbMultInt3_eval_3_2 : orbMultInt3 3 2 = (-32586/221 : ℝ) := rfl
@[simp] theorem orbMultInt3_eval_4_0 : orbMultInt3 4 0 = (-461/90 : ℝ) := rfl
@[simp] theorem orbMultInt3_eval_4_1 : orbMultInt3 4 1 = (1672/249 : ℝ) := rfl
@[simp] theorem orbMultInt3_eval_4_2 : orbMultInt3 4 2 = (9893/151 : ℝ) := rfl
@[simp] theorem orbMultInt4_eval_1_0 : orbMultInt4 1 0 = (-42/253 : ℝ) := rfl
@[simp] theorem orbMultInt4_eval_1_1 : orbMultInt4 1 1 = (1028/115 : ℝ) := rfl
@[simp] theorem orbMultInt4_eval_1_2 : orbMultInt4 1 2 = (-81/212 : ℝ) := rfl
@[simp] theorem orbMultInt4_eval_4_0 : orbMultInt4 4 0 = (-176/49 : ℝ) := rfl
@[simp] theorem orbMultInt4_eval_4_1 : orbMultInt4 4 1 = (-2437/167 : ℝ) := rfl
@[simp] theorem orbMultInt4_eval_4_2 : orbMultInt4 4 2 = (153/172 : ℝ) := rfl
@[simp] theorem orbMultInt4_eval_5_0 : orbMultInt4 5 0 = (-118/223 : ℝ) := rfl
@[simp] theorem orbMultInt4_eval_5_1 : orbMultInt4 5 1 = (1417/181 : ℝ) := rfl
@[simp] theorem orbMultInt4_eval_5_2 : orbMultInt4 5 2 = (-101/250 : ℝ) := rfl
@[simp] theorem orbMultInt5_eval_1_0 : orbMultInt5 1 0 = (-429/184 : ℝ) := rfl
@[simp] theorem orbMultInt5_eval_1_1 : orbMultInt5 1 1 = (17/2 : ℝ) := rfl
@[simp] theorem orbMultInt5_eval_1_2 : orbMultInt5 1 2 = (39/253 : ℝ) := rfl
@[simp] theorem orbMultInt5_eval_3_0 : orbMultInt5 3 0 = (443/190 : ℝ) := rfl
@[simp] theorem orbMultInt5_eval_3_1 : orbMultInt5 3 1 = (-9 : ℝ) := rfl
@[simp] theorem orbMultInt5_eval_3_2 : orbMultInt5 3 2 = (-138/239 : ℝ) := rfl
@[simp] theorem orbMultInt5_eval_5_0 : orbMultInt5 5 0 = (-569/240 : ℝ) := rfl
@[simp] theorem orbMultInt5_eval_5_1 : orbMultInt5 5 1 = (1532/187 : ℝ) := rfl
@[simp] theorem orbMultInt5_eval_5_2 : orbMultInt5 5 2 = (5/96 : ℝ) := rfl
@[simp] theorem orbMultInt6_eval_1_0 : orbMultInt6 1 0 = (67/147 : ℝ) := rfl
@[simp] theorem orbMultInt6_eval_1_1 : orbMultInt6 1 1 = (1052/131 : ℝ) := rfl
@[simp] theorem orbMultInt6_eval_1_2 : orbMultInt6 1 2 = (21/226 : ℝ) := rfl
@[simp] theorem orbMultInt6_eval_3_0 : orbMultInt6 3 0 = (-69/103 : ℝ) := rfl
@[simp] theorem orbMultInt6_eval_3_1 : orbMultInt6 3 1 = (-1197/134 : ℝ) := rfl
@[simp] theorem orbMultInt6_eval_3_2 : orbMultInt6 3 2 = (-89/174 : ℝ) := rfl
@[simp] theorem orbMultInt6_eval_4_0 : orbMultInt6 4 0 = (-971/210 : ℝ) := rfl
@[simp] theorem orbMultInt6_eval_4_1 : orbMultInt6 4 1 = (-3891/256 : ℝ) := rfl
@[simp] theorem orbMultInt6_eval_4_2 : orbMultInt6 4 2 = (19/187 : ℝ) := rfl
@[simp] theorem orbMultInt7_eval_1_0 : orbMultInt7 1 0 = (-94/55 : ℝ) := rfl
@[simp] theorem orbMultInt7_eval_1_1 : orbMultInt7 1 1 = (455/89 : ℝ) := rfl
@[simp] theorem orbMultInt7_eval_1_2 : orbMultInt7 1 2 = (-261/206 : ℝ) := rfl
@[simp] theorem orbMultInt7_eval_2_0 : orbMultInt7 2 0 = (625/143 : ℝ) := rfl
@[simp] theorem orbMultInt7_eval_2_1 : orbMultInt7 2 1 = (-1231/178 : ℝ) := rfl
@[simp] theorem orbMultInt7_eval_2_2 : orbMultInt7 2 2 = (1313/112 : ℝ) := rfl
@[simp] theorem orbMultInt7_eval_5_0 : orbMultInt7 5 0 = (-175/81 : ℝ) := rfl
@[simp] theorem orbMultInt7_eval_5_1 : orbMultInt7 5 1 = (1373/245 : ℝ) := rfl
@[simp] theorem orbMultInt7_eval_5_2 : orbMultInt7 5 2 = (-585/256 : ℝ) := rfl
@[simp] theorem orbMultInt8_eval_1_0 : orbMultInt8 1 0 = (85/254 : ℝ) := rfl
@[simp] theorem orbMultInt8_eval_1_1 : orbMultInt8 1 1 = (1391/255 : ℝ) := rfl
@[simp] theorem orbMultInt8_eval_1_2 : orbMultInt8 1 2 = (-297/146 : ℝ) := rfl
@[simp] theorem orbMultInt8_eval_2_0 : orbMultInt8 2 0 = (-353/249 : ℝ) := rfl
@[simp] theorem orbMultInt8_eval_2_1 : orbMultInt8 2 1 = (-2787/251 : ℝ) := rfl
@[simp] theorem orbMultInt8_eval_2_2 : orbMultInt8 2 2 = (3845/247 : ℝ) := rfl
@[simp] theorem orbMultInt8_eval_4_0 : orbMultInt8 4 0 = (-1213/255 : ℝ) := rfl
@[simp] theorem orbMultInt8_eval_4_1 : orbMultInt8 4 1 = (-3087/235 : ℝ) := rfl
@[simp] theorem orbMultInt8_eval_4_2 : orbMultInt8 4 2 = (2023/247 : ℝ) := rfl
@[simp] theorem orbMultInt9_eval_1_0 : orbMultInt9 1 0 = (89/19 : ℝ) := rfl
@[simp] theorem orbMultInt9_eval_1_1 : orbMultInt9 1 1 = (6880/87 : ℝ) := rfl
@[simp] theorem orbMultInt9_eval_1_2 : orbMultInt9 1 2 = (26714/219 : ℝ) := rfl
@[simp] theorem orbMultInt9_eval_2_0 : orbMultInt9 2 0 = (5271/107 : ℝ) := rfl
@[simp] theorem orbMultInt9_eval_2_1 : orbMultInt9 2 1 = (54597/82 : ℝ) := rfl
@[simp] theorem orbMultInt9_eval_2_2 : orbMultInt9 2 2 = (223477/208 : ℝ) := rfl
@[simp] theorem orbMultInt9_eval_3_0 : orbMultInt9 3 0 = (-5053/211 : ℝ) := rfl
@[simp] theorem orbMultInt9_eval_3_1 : orbMultInt9 3 1 = (-64785/191 : ℝ) := rfl
@[simp] theorem orbMultInt9_eval_3_2 : orbMultInt9 3 2 = (-61198/113 : ℝ) := rfl
@[simp] theorem orbMultInt10_eval_0_0 : orbMultInt10 0 0 = (267475/219 : ℝ) := rfl
@[simp] theorem orbMultInt10_eval_0_1 : orbMultInt10 0 1 = (-17936/191 : ℝ) := rfl
@[simp] theorem orbMultInt10_eval_0_2 : orbMultInt10 0 2 = (-409/70 : ℝ) := rfl
@[simp] theorem orbMultInt10_eval_4_0 : orbMultInt10 4 0 = (-218525/121 : ℝ) := rfl
@[simp] theorem orbMultInt10_eval_4_1 : orbMultInt10 4 1 = (11008/83 : ℝ) := rfl
@[simp] theorem orbMultInt10_eval_4_2 : orbMultInt10 4 2 = (1033/113 : ℝ) := rfl
@[simp] theorem orbMultInt10_eval_5_0 : orbMultInt10 5 0 = (-43259/203 : ℝ) := rfl
@[simp] theorem orbMultInt10_eval_5_1 : orbMultInt10 5 1 = (254/13 : ℝ) := rfl
@[simp] theorem orbMultInt10_eval_5_2 : orbMultInt10 5 2 = (125/154 : ℝ) := rfl
@[simp] theorem orbMultInt11_eval_0_0 : orbMultInt11 0 0 = (816/233 : ℝ) := rfl
@[simp] theorem orbMultInt11_eval_0_1 : orbMultInt11 0 1 = (-1708/255 : ℝ) := rfl
@[simp] theorem orbMultInt11_eval_0_2 : orbMultInt11 0 2 = (19/113 : ℝ) := rfl
@[simp] theorem orbMultInt11_eval_3_0 : orbMultInt11 3 0 = (331/155 : ℝ) := rfl
@[simp] theorem orbMultInt11_eval_3_1 : orbMultInt11 3 1 = (-1265/206 : ℝ) := rfl
@[simp] theorem orbMultInt11_eval_3_2 : orbMultInt11 3 2 = (-80/189 : ℝ) := rfl
@[simp] theorem orbMultInt11_eval_5_0 : orbMultInt11 5 0 = (-332/131 : ℝ) := rfl
@[simp] theorem orbMultInt11_eval_5_1 : orbMultInt11 5 1 = (537/86 : ℝ) := rfl
@[simp] theorem orbMultInt11_eval_5_2 : orbMultInt11 5 2 = (-9/86 : ℝ) := rfl
@[simp] theorem orbMultInt12_eval_0_0 : orbMultInt12 0 0 = (21230/141 : ℝ) := rfl
@[simp] theorem orbMultInt12_eval_0_1 : orbMultInt12 0 1 = (4831/141 : ℝ) := rfl
@[simp] theorem orbMultInt12_eval_0_2 : orbMultInt12 0 2 = (-127/245 : ℝ) := rfl
@[simp] theorem orbMultInt12_eval_3_0 : orbMultInt12 3 0 = (-691/30 : ℝ) := rfl
@[simp] theorem orbMultInt12_eval_3_1 : orbMultInt12 3 1 = (-2157/239 : ℝ) := rfl
@[simp] theorem orbMultInt12_eval_3_2 : orbMultInt12 3 2 = (-3/8 : ℝ) := rfl
@[simp] theorem orbMultInt12_eval_4_0 : orbMultInt12 4 0 = (-25641/103 : ℝ) := rfl
@[simp] theorem orbMultInt12_eval_4_1 : orbMultInt12 4 1 = (-15511/249 : ℝ) := rfl
@[simp] theorem orbMultInt12_eval_4_2 : orbMultInt12 4 2 = (71/68 : ℝ) := rfl
@[simp] theorem orbMultInt13_eval_0_0 : orbMultInt13 0 0 = (995/163 : ℝ) := rfl
@[simp] theorem orbMultInt13_eval_0_1 : orbMultInt13 0 1 = (-1727/189 : ℝ) := rfl
@[simp] theorem orbMultInt13_eval_0_2 : orbMultInt13 0 2 = (149/25 : ℝ) := rfl
@[simp] theorem orbMultInt13_eval_2_0 : orbMultInt13 2 0 = (2687/238 : ℝ) := rfl
@[simp] theorem orbMultInt13_eval_2_1 : orbMultInt13 2 1 = (-3973/253 : ℝ) := rfl
@[simp] theorem orbMultInt13_eval_2_2 : orbMultInt13 2 2 = (2116/113 : ℝ) := rfl
@[simp] theorem orbMultInt13_eval_5_0 : orbMultInt13 5 0 = (-512/115 : ℝ) := rfl
@[simp] theorem orbMultInt13_eval_5_1 : orbMultInt13 5 1 = (1700/219 : ℝ) := rfl
@[simp] theorem orbMultInt13_eval_5_2 : orbMultInt13 5 2 = (-869/184 : ℝ) := rfl
@[simp] theorem orbMultInt14_eval_0_0 : orbMultInt14 0 0 = (17296/75 : ℝ) := rfl
@[simp] theorem orbMultInt14_eval_0_1 : orbMultInt14 0 1 = (7759/166 : ℝ) := rfl
@[simp] theorem orbMultInt14_eval_0_2 : orbMultInt14 0 2 = (-6269/118 : ℝ) := rfl
@[simp] theorem orbMultInt14_eval_2_0 : orbMultInt14 2 0 = (-15599/155 : ℝ) := rfl
@[simp] theorem orbMultInt14_eval_2_1 : orbMultInt14 2 1 = (-4247/163 : ℝ) := rfl
@[simp] theorem orbMultInt14_eval_2_2 : orbMultInt14 2 2 = (4715/129 : ℝ) := rfl
@[simp] theorem orbMultInt14_eval_4_0 : orbMultInt14 4 0 = (-86302/215 : ℝ) := rfl
@[simp] theorem orbMultInt14_eval_4_1 : orbMultInt14 4 1 = (-16611/190 : ℝ) := rfl
@[simp] theorem orbMultInt14_eval_4_2 : orbMultInt14 4 2 = (1947/20 : ℝ) := rfl
@[simp] theorem orbMultInt15_eval_0_0 : orbMultInt15 0 0 = (1377/223 : ℝ) := rfl
@[simp] theorem orbMultInt15_eval_0_1 : orbMultInt15 0 1 = (10/3 : ℝ) := rfl
@[simp] theorem orbMultInt15_eval_0_2 : orbMultInt15 0 2 = (1421/62 : ℝ) := rfl
@[simp] theorem orbMultInt15_eval_2_0 : orbMultInt15 2 0 = (6469/149 : ℝ) := rfl
@[simp] theorem orbMultInt15_eval_2_1 : orbMultInt15 2 1 = (7814/121 : ℝ) := rfl
@[simp] theorem orbMultInt15_eval_2_2 : orbMultInt15 2 2 = (13896/59 : ℝ) := rfl
@[simp] theorem orbMultInt15_eval_3_0 : orbMultInt15 3 0 = (-1982/109 : ℝ) := rfl
@[simp] theorem orbMultInt15_eval_3_1 : orbMultInt15 3 1 = (-1036/33 : ℝ) := rfl
@[simp] theorem orbMultInt15_eval_3_2 : orbMultInt15 3 2 = (-26593/256 : ℝ) := rfl
@[simp] theorem orbMultInt16_eval_0_0 : orbMultInt16 0 0 = (1117/197 : ℝ) := rfl
@[simp] theorem orbMultInt16_eval_0_1 : orbMultInt16 0 1 = (-297/25 : ℝ) := rfl
@[simp] theorem orbMultInt16_eval_0_2 : orbMultInt16 0 2 = (114/181 : ℝ) := rfl
@[simp] theorem orbMultInt16_eval_1_0 : orbMultInt16 1 0 = (-738/179 : ℝ) := rfl
@[simp] theorem orbMultInt16_eval_1_1 : orbMultInt16 1 1 = (1486/143 : ℝ) := rfl
@[simp] theorem orbMultInt16_eval_1_2 : orbMultInt16 1 2 = (-91/215 : ℝ) := rfl
@[simp] theorem orbMultInt16_eval_5_0 : orbMultInt16 5 0 = (-107/24 : ℝ) := rfl
@[simp] theorem orbMultInt16_eval_5_1 : orbMultInt16 5 1 = (2445/226 : ℝ) := rfl
@[simp] theorem orbMultInt16_eval_5_2 : orbMultInt16 5 2 = (-84/157 : ℝ) := rfl
@[simp] theorem orbMultInt17_eval_0_0 : orbMultInt17 0 0 = (18801/190 : ℝ) := rfl
@[simp] theorem orbMultInt17_eval_0_1 : orbMultInt17 0 1 = (3608/195 : ℝ) := rfl
@[simp] theorem orbMultInt17_eval_0_2 : orbMultInt17 0 2 = (-200/103 : ℝ) := rfl
@[simp] theorem orbMultInt17_eval_1_0 : orbMultInt17 1 0 = (1631/254 : ℝ) := rfl
@[simp] theorem orbMultInt17_eval_1_1 : orbMultInt17 1 1 = (1333/253 : ℝ) := rfl
@[simp] theorem orbMultInt17_eval_1_2 : orbMultInt17 1 2 = (-25/98 : ℝ) := rfl
@[simp] theorem orbMultInt17_eval_4_0 : orbMultInt17 4 0 = (-34508/213 : ℝ) := rfl
@[simp] theorem orbMultInt17_eval_4_1 : orbMultInt17 4 1 = (-6437/173 : ℝ) := rfl
@[simp] theorem orbMultInt17_eval_4_2 : orbMultInt17 4 2 = (523/144 : ℝ) := rfl
@[simp] theorem orbMultInt18_eval_0_0 : orbMultInt18 0 0 = (586/203 : ℝ) := rfl
@[simp] theorem orbMultInt18_eval_0_1 : orbMultInt18 0 1 = (-50/9 : ℝ) := rfl
@[simp] theorem orbMultInt18_eval_0_2 : orbMultInt18 0 2 = (10/179 : ℝ) := rfl
@[simp] theorem orbMultInt18_eval_1_0 : orbMultInt18 1 0 = (-295/153 : ℝ) := rfl
@[simp] theorem orbMultInt18_eval_1_1 : orbMultInt18 1 1 = (227/41 : ℝ) := rfl
@[simp] theorem orbMultInt18_eval_1_2 : orbMultInt18 1 2 = (7/68 : ℝ) := rfl
@[simp] theorem orbMultInt18_eval_3_0 : orbMultInt18 3 0 = (460/251 : ℝ) := rfl
@[simp] theorem orbMultInt18_eval_3_1 : orbMultInt18 3 1 = (-295/51 : ℝ) := rfl
@[simp] theorem orbMultInt18_eval_3_2 : orbMultInt18 3 2 = (-131/249 : ℝ) := rfl
@[simp] theorem orbMultInt19_eval_0_0 : orbMultInt19 0 0 = (805/241 : ℝ) := rfl
@[simp] theorem orbMultInt19_eval_0_1 : orbMultInt19 0 1 = (-235/49 : ℝ) := rfl
@[simp] theorem orbMultInt19_eval_0_2 : orbMultInt19 0 2 = (323/122 : ℝ) := rfl
@[simp] theorem orbMultInt19_eval_1_0 : orbMultInt19 1 0 = (-243/146 : ℝ) := rfl
@[simp] theorem orbMultInt19_eval_1_1 : orbMultInt19 1 1 = (917/235 : ℝ) := rfl
@[simp] theorem orbMultInt19_eval_1_2 : orbMultInt19 1 2 = (-220/227 : ℝ) := rfl
@[simp] theorem orbMultInt19_eval_2_0 : orbMultInt19 2 0 = (988/197 : ℝ) := rfl
@[simp] theorem orbMultInt19_eval_2_1 : orbMultInt19 2 1 = (-857/162 : ℝ) := rfl
@[simp] theorem orbMultInt19_eval_2_2 : orbMultInt19 2 2 = (233/20 : ℝ) := rfl
@[simp] theorem orbMultWPos0_eval_3_0 : orbMultWPos0 3 0 = (-19/108 : ℝ) := rfl
@[simp] theorem orbMultWPos0_eval_3_1 : orbMultWPos0 3 1 = (-1346/229 : ℝ) := rfl
@[simp] theorem orbMultWPos0_eval_3_2 : orbMultWPos0 3 2 = (-84/205 : ℝ) := rfl
@[simp] theorem orbMultWPos0_eval_4_0 : orbMultWPos0 4 0 = (-965/254 : ℝ) := rfl
@[simp] theorem orbMultWPos0_eval_4_1 : orbMultWPos0 4 1 = (-1159/128 : ℝ) := rfl
@[simp] theorem orbMultWPos0_eval_4_2 : orbMultWPos0 4 2 = (27/106 : ℝ) := rfl
@[simp] theorem orbMultWPos0_eval_5_0 : orbMultWPos0 5 0 = (-91/239 : ℝ) := rfl
@[simp] theorem orbMultWPos0_eval_5_1 : orbMultWPos0 5 1 = (65/14 : ℝ) := rfl
@[simp] theorem orbMultWPos0_eval_5_2 : orbMultWPos0 5 2 = (-17/216 : ℝ) := rfl
@[simp] theorem orbMultWPos1_eval_2_0 : orbMultWPos1 2 0 = (-56/121 : ℝ) := rfl
@[simp] theorem orbMultWPos1_eval_2_1 : orbMultWPos1 2 1 = (-634/41 : ℝ) := rfl
@[simp] theorem orbMultWPos1_eval_2_2 : orbMultWPos1 2 2 = (903/44 : ℝ) := rfl
@[simp] theorem orbMultWPos1_eval_4_0 : orbMultWPos1 4 0 = (-985/252 : ℝ) := rfl
@[simp] theorem orbMultWPos1_eval_4_1 : orbMultWPos1 4 1 = (-2567/202 : ℝ) := rfl
@[simp] theorem orbMultWPos1_eval_4_2 : orbMultWPos1 4 2 = (2470/249 : ℝ) := rfl
@[simp] theorem orbMultWPos1_eval_5_0 : orbMultWPos1 5 0 = (-59/170 : ℝ) := rfl
@[simp] theorem orbMultWPos1_eval_5_1 : orbMultWPos1 5 1 = (1264/219 : ℝ) := rfl
@[simp] theorem orbMultWPos1_eval_5_2 : orbMultWPos1 5 2 = (-689/178 : ℝ) := rfl
@[simp] theorem orbMultWPos2_eval_2_0 : orbMultWPos2 2 0 = (3329/207 : ℝ) := rfl
@[simp] theorem orbMultWPos2_eval_2_1 : orbMultWPos2 2 1 = (7397/193 : ℝ) := rfl
@[simp] theorem orbMultWPos2_eval_2_2 : orbMultWPos2 2 2 = (5089/41 : ℝ) := rfl
@[simp] theorem orbMultWPos2_eval_3_0 : orbMultWPos2 3 0 = (-283/45 : ℝ) := rfl
@[simp] theorem orbMultWPos2_eval_3_1 : orbMultWPos2 3 1 = (-3210/157 : ℝ) := rfl
@[simp] theorem orbMultWPos2_eval_3_2 : orbMultWPos2 3 2 = (-3597/65 : ℝ) := rfl
@[simp] theorem orbMultWPos2_eval_5_0 : orbMultWPos2 5 0 = (-311/200 : ℝ) := rfl
@[simp] theorem orbMultWPos2_eval_5_1 : orbMultWPos2 5 1 = (439/238 : ℝ) := rfl
@[simp] theorem orbMultWPos2_eval_5_2 : orbMultWPos2 5 2 = (-434/99 : ℝ) := rfl
@[simp] theorem orbMultWPos3_eval_2_0 : orbMultWPos3 2 0 = (-699/134 : ℝ) := rfl
@[simp] theorem orbMultWPos3_eval_2_1 : orbMultWPos3 2 1 = (1399/22 : ℝ) := rfl
@[simp] theorem orbMultWPos3_eval_2_2 : orbMultWPos3 2 2 = (30713/86 : ℝ) := rfl
@[simp] theorem orbMultWPos3_eval_3_0 : orbMultWPos3 3 0 = (421/233 : ℝ) := rfl
@[simp] theorem orbMultWPos3_eval_3_1 : orbMultWPos3 3 1 = (-3065/102 : ℝ) := rfl
@[simp] theorem orbMultWPos3_eval_3_2 : orbMultWPos3 3 2 = (-31693/214 : ℝ) := rfl
@[simp] theorem orbMultWPos3_eval_4_0 : orbMultWPos3 4 0 = (-1107/220 : ℝ) := rfl
@[simp] theorem orbMultWPos3_eval_4_1 : orbMultWPos3 4 1 = (191/32 : ℝ) := rfl
@[simp] theorem orbMultWPos3_eval_4_2 : orbMultWPos3 4 2 = (12739/184 : ℝ) := rfl
@[simp] theorem orbMultWPos4_eval_1_0 : orbMultWPos4 1 0 = (-33/202 : ℝ) := rfl
@[simp] theorem orbMultWPos4_eval_1_1 : orbMultWPos4 1 1 = (914/99 : ℝ) := rfl
@[simp] theorem orbMultWPos4_eval_1_2 : orbMultWPos4 1 2 = (-43/113 : ℝ) := rfl
@[simp] theorem orbMultWPos4_eval_4_0 : orbMultWPos4 4 0 = (-621/176 : ℝ) := rfl
@[simp] theorem orbMultWPos4_eval_4_1 : orbMultWPos4 4 1 = (-1675/111 : ℝ) := rfl
@[simp] theorem orbMultWPos4_eval_4_2 : orbMultWPos4 4 2 = (101/114 : ℝ) := rfl
@[simp] theorem orbMultWPos4_eval_5_0 : orbMultWPos4 5 0 = (-105/202 : ℝ) := rfl
@[simp] theorem orbMultWPos4_eval_5_1 : orbMultWPos4 5 1 = (1801/223 : ℝ) := rfl
@[simp] theorem orbMultWPos4_eval_5_2 : orbMultWPos4 5 2 = (-101/251 : ℝ) := rfl
@[simp] theorem orbMultWPos5_eval_1_0 : orbMultWPos5 1 0 = (-71/31 : ℝ) := rfl
@[simp] theorem orbMultWPos5_eval_1_1 : orbMultWPos5 1 1 = (689/82 : ℝ) := rfl
@[simp] theorem orbMultWPos5_eval_1_2 : orbMultWPos5 1 2 = (37/241 : ℝ) := rfl
@[simp] theorem orbMultWPos5_eval_3_0 : orbMultWPos5 3 0 = (552/241 : ℝ) := rfl
@[simp] theorem orbMultWPos5_eval_3_1 : orbMultWPos5 3 1 = (-1905/214 : ℝ) := rfl
@[simp] theorem orbMultWPos5_eval_3_2 : orbMultWPos5 3 2 = (-134/233 : ℝ) := rfl
@[simp] theorem orbMultWPos5_eval_5_0 : orbMultWPos5 5 0 = (-538/231 : ℝ) := rfl
@[simp] theorem orbMultWPos5_eval_5_1 : orbMultWPos5 5 1 = (793/98 : ℝ) := rfl
@[simp] theorem orbMultWPos5_eval_5_2 : orbMultWPos5 5 2 = (11/212 : ℝ) := rfl
@[simp] theorem orbMultWPos6_eval_1_0 : orbMultWPos6 1 0 = (30/67 : ℝ) := rfl
@[simp] theorem orbMultWPos6_eval_1_1 : orbMultWPos6 1 1 = (1351/151 : ℝ) := rfl
@[simp] theorem orbMultWPos6_eval_1_2 : orbMultWPos6 1 2 = (21/227 : ℝ) := rfl
@[simp] theorem orbMultWPos6_eval_3_0 : orbMultWPos6 3 0 = (-102/155 : ℝ) := rfl
@[simp] theorem orbMultWPos6_eval_3_1 : orbMultWPos6 3 1 = (-1319/133 : ℝ) := rfl
@[simp] theorem orbMultWPos6_eval_3_2 : orbMultWPos6 3 2 = (-27/53 : ℝ) := rfl
@[simp] theorem orbMultWPos6_eval_4_0 : orbMultWPos6 4 0 = (-377/83 : ℝ) := rfl
@[simp] theorem orbMultWPos6_eval_4_1 : orbMultWPos6 4 1 = (-1852/111 : ℝ) := rfl
@[simp] theorem orbMultWPos6_eval_4_2 : orbMultWPos6 4 2 = (17/168 : ℝ) := rfl
@[simp] theorem orbMultWPos7_eval_1_0 : orbMultWPos7 1 0 = (-183/109 : ℝ) := rfl
@[simp] theorem orbMultWPos7_eval_1_1 : orbMultWPos7 1 1 = (783/154 : ℝ) := rfl
@[simp] theorem orbMultWPos7_eval_1_2 : orbMultWPos7 1 2 = (-195/161 : ℝ) := rfl
@[simp] theorem orbMultWPos7_eval_2_0 : orbMultWPos7 2 0 = (395/92 : ℝ) := rfl
@[simp] theorem orbMultWPos7_eval_2_1 : orbMultWPos7 2 1 = (-119/18 : ℝ) := rfl
@[simp] theorem orbMultWPos7_eval_2_2 : orbMultWPos7 2 2 = (2959/249 : ℝ) := rfl
@[simp] theorem orbMultWPos7_eval_5_0 : orbMultWPos7 5 0 = (-503/237 : ℝ) := rfl
@[simp] theorem orbMultWPos7_eval_5_1 : orbMultWPos7 5 1 = (804/145 : ℝ) := rfl
@[simp] theorem orbMultWPos7_eval_5_2 : orbMultWPos7 5 2 = (-507/226 : ℝ) := rfl
@[simp] theorem orbMultWPos8_eval_1_0 : orbMultWPos8 1 0 = (64/195 : ℝ) := rfl
@[simp] theorem orbMultWPos8_eval_1_1 : orbMultWPos8 1 1 = (1521/251 : ℝ) := rfl
@[simp] theorem orbMultWPos8_eval_1_2 : orbMultWPos8 1 2 = (-489/211 : ℝ) := rfl
@[simp] theorem orbMultWPos8_eval_2_0 : orbMultWPos8 2 0 = (-227/163 : ℝ) := rfl
@[simp] theorem orbMultWPos8_eval_2_1 : orbMultWPos8 2 1 = (-2239/177 : ℝ) := rfl
@[simp] theorem orbMultWPos8_eval_2_2 : orbMultWPos8 2 2 = (2073/124 : ℝ) := rfl
@[simp] theorem orbMultWPos8_eval_4_0 : orbMultWPos8 4 0 = (-500/107 : ℝ) := rfl
@[simp] theorem orbMultWPos8_eval_4_1 : orbMultWPos8 4 1 = (-695/48 : ℝ) := rfl
@[simp] theorem orbMultWPos8_eval_4_2 : orbMultWPos8 4 2 = (811/91 : ℝ) := rfl
@[simp] theorem orbMultWPos9_eval_1_0 : orbMultWPos9 1 0 = (612/133 : ℝ) := rfl
@[simp] theorem orbMultWPos9_eval_1_1 : orbMultWPos9 1 1 = (19351/229 : ℝ) := rfl
@[simp] theorem orbMultWPos9_eval_1_2 : orbMultWPos9 1 2 = (14929/116 : ℝ) := rfl
@[simp] theorem orbMultWPos9_eval_2_0 : orbMultWPos9 2 0 = (11227/232 : ℝ) := rfl
@[simp] theorem orbMultWPos9_eval_2_1 : orbMultWPos9 2 1 = (176322/251 : ℝ) := rfl
@[simp] theorem orbMultWPos9_eval_2_2 : orbMultWPos9 2 2 = (276364/247 : ℝ) := rfl
@[simp] theorem orbMultWPos9_eval_3_0 : orbMultWPos9 3 0 = (-3270/139 : ℝ) := rfl
@[simp] theorem orbMultWPos9_eval_3_1 : orbMultWPos9 3 1 = (-58867/164 : ℝ) := rfl
@[simp] theorem orbMultWPos9_eval_3_2 : orbMultWPos9 3 2 = (-69013/122 : ℝ) := rfl
@[simp] theorem orbMultWPos10_eval_0_0 : orbMultWPos10 0 0 = (196319/165 : ℝ) := rfl
@[simp] theorem orbMultWPos10_eval_0_1 : orbMultWPos10 0 1 = (-20701/248 : ℝ) := rfl
@[simp] theorem orbMultWPos10_eval_0_2 : orbMultWPos10 0 2 = (-902/155 : ℝ) := rfl
@[simp] theorem orbMultWPos10_eval_4_0 : orbMultWPos10 4 0 = (-418075/237 : ℝ) := rfl
@[simp] theorem orbMultWPos10_eval_4_1 : orbMultWPos10 4 1 = (30062/255 : ℝ) := rfl
@[simp] theorem orbMultWPos10_eval_4_2 : orbMultWPos10 4 2 = (1129/124 : ℝ) := rfl
@[simp] theorem orbMultWPos10_eval_5_0 : orbMultWPos10 5 0 = (-50688/247 : ℝ) := rfl
@[simp] theorem orbMultWPos10_eval_5_1 : orbMultWPos10 5 1 = (2883/166 : ℝ) := rfl
@[simp] theorem orbMultWPos10_eval_5_2 : orbMultWPos10 5 2 = (173/214 : ℝ) := rfl
@[simp] theorem orbMultWPos11_eval_0_0 : orbMultWPos11 0 0 = (745/231 : ℝ) := rfl
@[simp] theorem orbMultWPos11_eval_0_1 : orbMultWPos11 0 1 = (-387/65 : ℝ) := rfl
@[simp] theorem orbMultWPos11_eval_0_2 : orbMultWPos11 0 2 = (35/209 : ℝ) := rfl
@[simp] theorem orbMultWPos11_eval_3_0 : orbMultWPos11 3 0 = (199/106 : ℝ) := rfl
@[simp] theorem orbMultWPos11_eval_3_1 : orbMultWPos11 3 1 = (-1381/253 : ℝ) := rfl
@[simp] theorem orbMultWPos11_eval_3_2 : orbMultWPos11 3 2 = (-43/102 : ℝ) := rfl
@[simp] theorem orbMultWPos11_eval_5_0 : orbMultWPos11 5 0 = (-509/224 : ℝ) := rfl
@[simp] theorem orbMultWPos11_eval_5_1 : orbMultWPos11 5 1 = (716/129 : ℝ) := rfl
@[simp] theorem orbMultWPos11_eval_5_2 : orbMultWPos11 5 2 = (-22/211 : ℝ) := rfl
@[simp] theorem orbMultWPos12_eval_0_0 : orbMultWPos12 0 0 = (30169/197 : ℝ) := rfl
@[simp] theorem orbMultWPos12_eval_0_1 : orbMultWPos12 0 1 = (3076/101 : ℝ) := rfl
@[simp] theorem orbMultWPos12_eval_0_2 : orbMultWPos12 0 2 = (-95/184 : ℝ) := rfl
@[simp] theorem orbMultWPos12_eval_3_0 : orbMultWPos12 3 0 = (-2005/92 : ℝ) := rfl
@[simp] theorem orbMultWPos12_eval_3_1 : orbMultWPos12 3 1 = (-1797/224 : ℝ) := rfl
@[simp] theorem orbMultWPos12_eval_3_2 : orbMultWPos12 3 2 = (-59/158 : ℝ) := rfl
@[simp] theorem orbMultWPos12_eval_4_0 : orbMultWPos12 4 0 = (-46373/185 : ℝ) := rfl
@[simp] theorem orbMultWPos12_eval_4_1 : orbMultWPos12 4 1 = (-10576/191 : ℝ) := rfl
@[simp] theorem orbMultWPos12_eval_4_2 : orbMultWPos12 4 2 = (261/251 : ℝ) := rfl
@[simp] theorem orbMultWPos13_eval_0_0 : orbMultWPos13 0 0 = (325/58 : ℝ) := rfl
@[simp] theorem orbMultWPos13_eval_0_1 : orbMultWPos13 0 1 = (-1860/229 : ℝ) := rfl
@[simp] theorem orbMultWPos13_eval_0_2 : orbMultWPos13 0 2 = (638/115 : ℝ) := rfl
@[simp] theorem orbMultWPos13_eval_2_0 : orbMultWPos13 2 0 = (1135/108 : ℝ) := rfl
@[simp] theorem orbMultWPos13_eval_2_1 : orbMultWPos13 2 1 = (-3043/218 : ℝ) := rfl
@[simp] theorem orbMultWPos13_eval_2_2 : orbMultWPos13 2 2 = (1429/78 : ℝ) := rfl
@[simp] theorem orbMultWPos13_eval_5_0 : orbMultWPos13 5 0 = (-631/157 : ℝ) := rfl
@[simp] theorem orbMultWPos13_eval_5_1 : orbMultWPos13 5 1 = (69/10 : ℝ) := rfl
@[simp] theorem orbMultWPos13_eval_5_2 : orbMultWPos13 5 2 = (-231/53 : ℝ) := rfl
@[simp] theorem orbMultWPos14_eval_0_0 : orbMultWPos14 0 0 = (20161/88 : ℝ) := rfl
@[simp] theorem orbMultWPos14_eval_0_1 : orbMultWPos14 0 1 = (9182/221 : ℝ) := rfl
@[simp] theorem orbMultWPos14_eval_0_2 : orbMultWPos14 0 2 = (-9648/191 : ℝ) := rfl
@[simp] theorem orbMultWPos14_eval_2_0 : orbMultWPos14 2 0 = (-12535/131 : ℝ) := rfl
@[simp] theorem orbMultWPos14_eval_2_1 : orbMultWPos14 2 1 = (-5350/231 : ℝ) := rfl
@[simp] theorem orbMultWPos14_eval_2_2 : orbMultWPos14 2 2 = (6623/189 : ℝ) := rfl
@[simp] theorem orbMultWPos14_eval_4_0 : orbMultWPos14 4 0 = (-81754/207 : ℝ) := rfl
@[simp] theorem orbMultWPos14_eval_4_1 : orbMultWPos14 4 1 = (-16475/212 : ℝ) := rfl
@[simp] theorem orbMultWPos14_eval_4_2 : orbMultWPos14 4 2 = (21284/231 : ℝ) := rfl
@[simp] theorem orbMultWPos15_eval_0_0 : orbMultWPos15 0 0 = (1589/237 : ℝ) := rfl
@[simp] theorem orbMultWPos15_eval_0_1 : orbMultWPos15 0 1 = (649/219 : ℝ) := rfl
@[simp] theorem orbMultWPos15_eval_0_2 : orbMultWPos15 0 2 = (6203/256 : ℝ) := rfl
@[simp] theorem orbMultWPos15_eval_2_0 : orbMultWPos15 2 0 = (459/10 : ℝ) := rfl
@[simp] theorem orbMultWPos15_eval_2_1 : orbMultWPos15 2 1 = (10964/191 : ℝ) := rfl
@[simp] theorem orbMultWPos15_eval_2_2 : orbMultWPos15 2 2 = (26528/113 : ℝ) := rfl
@[simp] theorem orbMultWPos15_eval_3_0 : orbMultWPos15 3 0 = (-4319/227 : ℝ) := rfl
@[simp] theorem orbMultWPos15_eval_3_1 : orbMultWPos15 3 1 = (-6809/244 : ℝ) := rfl
@[simp] theorem orbMultWPos15_eval_3_2 : orbMultWPos15 3 2 = (-8488/83 : ℝ) := rfl
@[simp] theorem orbMultWPos16_eval_0_0 : orbMultWPos16 0 0 = (1477/254 : ℝ) := rfl
@[simp] theorem orbMultWPos16_eval_0_1 : orbMultWPos16 0 1 = (-3124/255 : ℝ) := rfl
@[simp] theorem orbMultWPos16_eval_0_2 : orbMultWPos16 0 2 = (69/110 : ℝ) := rfl
@[simp] theorem orbMultWPos16_eval_1_0 : orbMultWPos16 1 0 = (-659/155 : ℝ) := rfl
@[simp] theorem orbMultWPos16_eval_1_1 : orbMultWPos16 1 1 = (601/56 : ℝ) := rfl
@[simp] theorem orbMultWPos16_eval_1_2 : orbMultWPos16 1 2 = (-43/102 : ℝ) := rfl
@[simp] theorem orbMultWPos16_eval_5_0 : orbMultWPos16 5 0 = (-615/134 : ℝ) := rfl
@[simp] theorem orbMultWPos16_eval_5_1 : orbMultWPos16 5 1 = (1429/128 : ℝ) := rfl
@[simp] theorem orbMultWPos16_eval_5_2 : orbMultWPos16 5 2 = (-81/152 : ℝ) := rfl
@[simp] theorem orbMultWPos17_eval_0_0 : orbMultWPos17 0 0 = (16852/159 : ℝ) := rfl
@[simp] theorem orbMultWPos17_eval_0_1 : orbMultWPos17 0 1 = (147/8 : ℝ) := rfl
@[simp] theorem orbMultWPos17_eval_0_2 : orbMultWPos17 0 2 = (-205/106 : ℝ) := rfl
@[simp] theorem orbMultWPos17_eval_1_0 : orbMultWPos17 1 0 = (1607/252 : ℝ) := rfl
@[simp] theorem orbMultWPos17_eval_1_1 : orbMultWPos17 1 1 = (368/67 : ℝ) := rfl
@[simp] theorem orbMultWPos17_eval_1_2 : orbMultWPos17 1 2 = (-47/185 : ℝ) := rfl
@[simp] theorem orbMultWPos17_eval_4_0 : orbMultWPos17 4 0 = (-32282/187 : ℝ) := rfl
@[simp] theorem orbMultWPos17_eval_4_1 : orbMultWPos17 4 1 = (-4187/112 : ℝ) := rfl
@[simp] theorem orbMultWPos17_eval_4_2 : orbMultWPos17 4 2 = (709/196 : ℝ) := rfl
@[simp] theorem orbMultWPos18_eval_0_0 : orbMultWPos18 0 0 = (647/205 : ℝ) := rfl
@[simp] theorem orbMultWPos18_eval_0_1 : orbMultWPos18 0 1 = (-1145/183 : ℝ) := rfl
@[simp] theorem orbMultWPos18_eval_0_2 : orbMultWPos18 0 2 = (1/18 : ℝ) := rfl
@[simp] theorem orbMultWPos18_eval_1_0 : orbMultWPos18 1 0 = (-76/35 : ℝ) := rfl
@[simp] theorem orbMultWPos18_eval_1_1 : orbMultWPos18 1 1 = (1230/199 : ℝ) := rfl
@[simp] theorem orbMultWPos18_eval_1_2 : orbMultWPos18 1 2 = (25/244 : ℝ) := rfl
@[simp] theorem orbMultWPos18_eval_3_0 : orbMultWPos18 3 0 = (164/79 : ℝ) := rfl
@[simp] theorem orbMultWPos18_eval_3_1 : orbMultWPos18 3 1 = (-1427/222 : ℝ) := rfl
@[simp] theorem orbMultWPos18_eval_3_2 : orbMultWPos18 3 2 = (-98/187 : ℝ) := rfl
@[simp] theorem orbMultWPos19_eval_0_0 : orbMultWPos19 0 0 = (810/221 : ℝ) := rfl
@[simp] theorem orbMultWPos19_eval_0_1 : orbMultWPos19 0 1 = (-1379/255 : ℝ) := rfl
@[simp] theorem orbMultWPos19_eval_0_2 : orbMultWPos19 0 2 = (301/102 : ℝ) := rfl
@[simp] theorem orbMultWPos19_eval_1_0 : orbMultWPos19 1 0 = (-396/211 : ℝ) := rfl
@[simp] theorem orbMultWPos19_eval_1_1 : orbMultWPos19 1 1 = (1109/256 : ℝ) := rfl
@[simp] theorem orbMultWPos19_eval_1_2 : orbMultWPos19 1 2 = (-90/79 : ℝ) := rfl
@[simp] theorem orbMultWPos19_eval_2_0 : orbMultWPos19 2 0 = (559/100 : ℝ) := rfl
@[simp] theorem orbMultWPos19_eval_2_1 : orbMultWPos19 2 1 = (-1281/206 : ℝ) := rfl
@[simp] theorem orbMultWPos19_eval_2_2 : orbMultWPos19 2 2 = (149/12 : ℝ) := rfl
@[simp] theorem orbMultWNeg0_eval_3_0 : orbMultWNeg0 3 0 = (-43/239 : ℝ) := rfl
@[simp] theorem orbMultWNeg0_eval_3_1 : orbMultWNeg0 3 1 = (-41/6 : ℝ) := rfl
@[simp] theorem orbMultWNeg0_eval_3_2 : orbMultWNeg0 3 2 = (-7/17 : ℝ) := rfl
@[simp] theorem orbMultWNeg0_eval_4_0 : orbMultWNeg0 4 0 = (-136/35 : ℝ) := rfl
@[simp] theorem orbMultWNeg0_eval_4_1 : orbMultWNeg0 4 1 = (-2558/243 : ℝ) := rfl
@[simp] theorem orbMultWNeg0_eval_4_2 : orbMultWNeg0 4 2 = (32/125 : ℝ) := rfl
@[simp] theorem orbMultWNeg0_eval_5_0 : orbMultWNeg0 5 0 = (-37/95 : ℝ) := rfl
@[simp] theorem orbMultWNeg0_eval_5_1 : orbMultWNeg0 5 1 = (1317/244 : ℝ) := rfl
@[simp] theorem orbMultWNeg0_eval_5_2 : orbMultWNeg0 5 2 = (-14/177 : ℝ) := rfl
@[simp] theorem orbMultWNeg1_eval_2_0 : orbMultWNeg1 2 0 = (-71/150 : ℝ) := rfl
@[simp] theorem orbMultWNeg1_eval_2_1 : orbMultWNeg1 2 1 = (-3973/221 : ℝ) := rfl
@[simp] theorem orbMultWNeg1_eval_2_2 : orbMultWNeg1 2 2 = (4789/225 : ℝ) := rfl
@[simp] theorem orbMultWNeg1_eval_4_0 : orbMultWNeg1 4 0 = (-1023/256 : ℝ) := rfl
@[simp] theorem orbMultWNeg1_eval_4_1 : orbMultWNeg1 4 1 = (-1699/115 : ℝ) := rfl
@[simp] theorem orbMultWNeg1_eval_4_2 : orbMultWNeg1 4 2 = (935/86 : ℝ) := rfl
@[simp] theorem orbMultWNeg1_eval_5_0 : orbMultWNeg1 5 0 = (-82/231 : ℝ) := rfl
@[simp] theorem orbMultWNeg1_eval_5_1 : orbMultWNeg1 5 1 = (1134/169 : ℝ) := rfl
@[simp] theorem orbMultWNeg1_eval_5_2 : orbMultWNeg1 5 2 = (-449/104 : ℝ) := rfl
@[simp] theorem orbMultWNeg2_eval_2_0 : orbMultWNeg2 2 0 = (3602/219 : ℝ) := rfl
@[simp] theorem orbMultWNeg2_eval_2_1 : orbMultWNeg2 2 1 = (2718/61 : ℝ) := rfl
@[simp] theorem orbMultWNeg2_eval_2_2 : orbMultWNeg2 2 2 = (21719/163 : ℝ) := rfl
@[simp] theorem orbMultWNeg2_eval_3_0 : orbMultWNeg2 3 0 = (-1460/227 : ℝ) := rfl
@[simp] theorem orbMultWNeg2_eval_3_1 : orbMultWNeg2 3 1 = (-2995/126 : ℝ) := rfl
@[simp] theorem orbMultWNeg2_eval_3_2 : orbMultWNeg2 3 2 = (-12190/203 : ℝ) := rfl
@[simp] theorem orbMultWNeg2_eval_5_0 : orbMultWNeg2 5 0 = (-361/227 : ℝ) := rfl
@[simp] theorem orbMultWNeg2_eval_5_1 : orbMultWNeg2 5 1 = (193/90 : ℝ) := rfl
@[simp] theorem orbMultWNeg2_eval_5_2 : orbMultWNeg2 5 2 = (-834/203 : ℝ) := rfl
@[simp] theorem orbMultWNeg3_eval_2_0 : orbMultWNeg3 2 0 = (-1115/209 : ℝ) := rfl
@[simp] theorem orbMultWNeg3_eval_2_1 : orbMultWNeg3 2 1 = (8354/113 : ℝ) := rfl
@[simp] theorem orbMultWNeg3_eval_2_2 : orbMultWNeg3 2 2 = (53043/151 : ℝ) := rfl
@[simp] theorem orbMultWNeg3_eval_3_0 : orbMultWNeg3 3 0 = (401/217 : ℝ) := rfl
@[simp] theorem orbMultWNeg3_eval_3_1 : orbMultWNeg3 3 1 = (-7441/213 : ℝ) := rfl
@[simp] theorem orbMultWNeg3_eval_3_2 : orbMultWNeg3 3 2 = (-19672/133 : ℝ) := rfl
@[simp] theorem orbMultWNeg3_eval_4_0 : orbMultWNeg3 4 0 = (-1127/219 : ℝ) := rfl
@[simp] theorem orbMultWNeg3_eval_4_1 : orbMultWNeg3 4 1 = (798/115 : ℝ) := rfl
@[simp] theorem orbMultWNeg3_eval_4_2 : orbMultWNeg3 4 2 = (2657/41 : ℝ) := rfl
@[simp] theorem orbMultWNeg4_eval_1_0 : orbMultWNeg4 1 0 = (-42/251 : ℝ) := rfl
@[simp] theorem orbMultWNeg4_eval_1_1 : orbMultWNeg4 1 1 = (133/15 : ℝ) := rfl
@[simp] theorem orbMultWNeg4_eval_1_2 : orbMultWNeg4 1 2 = (-96/251 : ℝ) := rfl
@[simp] theorem orbMultWNeg4_eval_4_0 : orbMultWNeg4 4 0 = (-848/235 : ℝ) := rfl
@[simp] theorem orbMultWNeg4_eval_4_1 : orbMultWNeg4 4 1 = (-3111/215 : ℝ) := rfl
@[simp] theorem orbMultWNeg4_eval_4_2 : orbMultWNeg4 4 2 = (187/210 : ℝ) := rfl
@[simp] theorem orbMultWNeg4_eval_5_0 : orbMultWNeg4 5 0 = (-42/79 : ℝ) := rfl
@[simp] theorem orbMultWNeg4_eval_5_1 : orbMultWNeg4 5 1 = (1103/142 : ℝ) := rfl
@[simp] theorem orbMultWNeg4_eval_5_2 : orbMultWNeg4 5 2 = (-91/225 : ℝ) := rfl
@[simp] theorem orbMultWNeg5_eval_1_0 : orbMultWNeg5 1 0 = (-431/184 : ℝ) := rfl
@[simp] theorem orbMultWNeg5_eval_1_1 : orbMultWNeg5 1 1 = (1492/175 : ℝ) := rfl
@[simp] theorem orbMultWNeg5_eval_1_2 : orbMultWNeg5 1 2 = (25/162 : ℝ) := rfl
@[simp] theorem orbMultWNeg5_eval_3_0 : orbMultWNeg5 3 0 = (171/73 : ℝ) := rfl
@[simp] theorem orbMultWNeg5_eval_3_1 : orbMultWNeg5 3 1 = (-2103/233 : ℝ) := rfl
@[simp] theorem orbMultWNeg5_eval_3_2 : orbMultWNeg5 3 2 = (-100/173 : ℝ) := rfl
@[simp] theorem orbMultWNeg5_eval_5_0 : orbMultWNeg5 5 0 = (-605/254 : ℝ) := rfl
@[simp] theorem orbMultWNeg5_eval_5_1 : orbMultWNeg5 5 1 = (1537/187 : ℝ) := rfl
@[simp] theorem orbMultWNeg5_eval_5_2 : orbMultWNeg5 5 2 = (11/211 : ℝ) := rfl
@[simp] theorem orbMultWNeg6_eval_1_0 : orbMultWNeg6 1 0 = (49/107 : ℝ) := rfl
@[simp] theorem orbMultWNeg6_eval_1_1 : orbMultWNeg6 1 1 = (446/57 : ℝ) := rfl
@[simp] theorem orbMultWNeg6_eval_1_2 : orbMultWNeg6 1 2 = (4/43 : ℝ) := rfl
@[simp] theorem orbMultWNeg6_eval_3_0 : orbMultWNeg6 3 0 = (-142/211 : ℝ) := rfl
@[simp] theorem orbMultWNeg6_eval_3_1 : orbMultWNeg6 3 1 = (-1420/163 : ℝ) := rfl
@[simp] theorem orbMultWNeg6_eval_3_2 : orbMultWNeg6 3 2 = (-64/125 : ℝ) := rfl
@[simp] theorem orbMultWNeg6_eval_4_0 : orbMultWNeg6 4 0 = (-655/141 : ℝ) := rfl
@[simp] theorem orbMultWNeg6_eval_4_1 : orbMultWNeg6 4 1 = (-223/15 : ℝ) := rfl
@[simp] theorem orbMultWNeg6_eval_4_2 : orbMultWNeg6 4 2 = (6/59 : ℝ) := rfl
@[simp] theorem orbMultWNeg7_eval_1_0 : orbMultWNeg7 1 0 = (-352/205 : ℝ) := rfl
@[simp] theorem orbMultWNeg7_eval_1_1 : orbMultWNeg7 1 1 = (1065/208 : ℝ) := rfl
@[simp] theorem orbMultWNeg7_eval_1_2 : orbMultWNeg7 1 2 = (-41/32 : ℝ) := rfl
@[simp] theorem orbMultWNeg7_eval_2_0 : orbMultWNeg7 2 0 = (685/156 : ℝ) := rfl
@[simp] theorem orbMultWNeg7_eval_2_1 : orbMultWNeg7 2 1 = (-1070/153 : ℝ) := rfl
@[simp] theorem orbMultWNeg7_eval_2_2 : orbMultWNeg7 2 2 = (2372/203 : ℝ) := rfl
@[simp] theorem orbMultWNeg7_eval_5_0 : orbMultWNeg7 5 0 = (-369/170 : ℝ) := rfl
@[simp] theorem orbMultWNeg7_eval_5_1 : orbMultWNeg7 5 1 = (1242/221 : ℝ) := rfl
@[simp] theorem orbMultWNeg7_eval_5_2 : orbMultWNeg7 5 2 = (-62/27 : ℝ) := rfl
@[simp] theorem orbMultWNeg8_eval_1_0 : orbMultWNeg8 1 0 = (48/143 : ℝ) := rfl
@[simp] theorem orbMultWNeg8_eval_1_1 : orbMultWNeg8 1 1 = (1085/204 : ℝ) := rfl
@[simp] theorem orbMultWNeg8_eval_1_2 : orbMultWNeg8 1 2 = (-205/104 : ℝ) := rfl
@[simp] theorem orbMultWNeg8_eval_2_0 : orbMultWNeg8 2 0 = (-47/33 : ℝ) := rfl
@[simp] theorem orbMultWNeg8_eval_2_1 : orbMultWNeg8 2 1 = (-1474/137 : ℝ) := rfl
@[simp] theorem orbMultWNeg8_eval_2_2 : orbMultWNeg8 2 2 = (811/53 : ℝ) := rfl
@[simp] theorem orbMultWNeg8_eval_4_0 : orbMultWNeg8 4 0 = (-411/86 : ℝ) := rfl
@[simp] theorem orbMultWNeg8_eval_4_1 : orbMultWNeg8 4 1 = (-1797/140 : ℝ) := rfl
@[simp] theorem orbMultWNeg8_eval_4_2 : orbMultWNeg8 4 2 = (1413/176 : ℝ) := rfl
@[simp] theorem orbMultWNeg9_eval_1_0 : orbMultWNeg9 1 0 = (1153/245 : ℝ) := rfl
@[simp] theorem orbMultWNeg9_eval_1_1 : orbMultWNeg9 1 1 = (8255/106 : ℝ) := rfl
@[simp] theorem orbMultWNeg9_eval_1_2 : orbMultWNeg9 1 2 = (24221/201 : ℝ) := rfl
@[simp] theorem orbMultWNeg9_eval_2_0 : orbMultWNeg9 2 0 = (11779/238 : ℝ) := rfl
@[simp] theorem orbMultWNeg9_eval_2_1 : orbMultWNeg9 2 1 = (158516/241 : ℝ) := rfl
@[simp] theorem orbMultWNeg9_eval_2_2 : orbMultWNeg9 2 2 = (68143/64 : ℝ) := rfl
@[simp] theorem orbMultWNeg9_eval_3_0 : orbMultWNeg9 3 0 = (-5245/218 : ℝ) := rfl
@[simp] theorem orbMultWNeg9_eval_3_1 : orbMultWNeg9 3 1 = (-33148/99 : ℝ) := rfl
@[simp] theorem orbMultWNeg9_eval_3_2 : orbMultWNeg9 3 2 = (-90637/169 : ℝ) := rfl
@[simp] theorem orbMultWNeg10_eval_0_0 : orbMultWNeg10 0 0 = (109657/89 : ℝ) := rfl
@[simp] theorem orbMultWNeg10_eval_0_1 : orbMultWNeg10 0 1 = (-6890/71 : ℝ) := rfl
@[simp] theorem orbMultWNeg10_eval_0_2 : orbMultWNeg10 0 2 = (-1123/192 : ℝ) := rfl
@[simp] theorem orbMultWNeg10_eval_4_0 : orbMultWNeg10 4 0 = (-395058/217 : ℝ) := rfl
@[simp] theorem orbMultWNeg10_eval_4_1 : orbMultWNeg10 4 1 = (31660/231 : ℝ) := rfl
@[simp] theorem orbMultWNeg10_eval_4_2 : orbMultWNeg10 4 2 = (787/86 : ℝ) := rfl
@[simp] theorem orbMultWNeg10_eval_5_0 : orbMultWNeg10 5 0 = (-19194/89 : ℝ) := rfl
@[simp] theorem orbMultWNeg10_eval_5_1 : orbMultWNeg10 5 1 = (1797/89 : ℝ) := rfl
@[simp] theorem orbMultWNeg10_eval_5_2 : orbMultWNeg10 5 2 = (13/16 : ℝ) := rfl
@[simp] theorem orbMultWNeg11_eval_0_0 : orbMultWNeg11 0 0 = (649/181 : ℝ) := rfl
@[simp] theorem orbMultWNeg11_eval_0_1 : orbMultWNeg11 0 1 = (-1239/179 : ℝ) := rfl
@[simp] theorem orbMultWNeg11_eval_0_2 : orbMultWNeg11 0 2 = (17/101 : ℝ) := rfl
@[simp] theorem orbMultWNeg11_eval_3_0 : orbMultWNeg11 3 0 = (135/61 : ℝ) := rfl
@[simp] theorem orbMultWNeg11_eval_3_1 : orbMultWNeg11 3 1 = (-1009/159 : ℝ) := rfl
@[simp] theorem orbMultWNeg11_eval_3_2 : orbMultWNeg11 3 2 = (-25/59 : ℝ) := rfl
@[simp] theorem orbMultWNeg11_eval_5_0 : orbMultWNeg11 5 0 = (-358/137 : ℝ) := rfl
@[simp] theorem orbMultWNeg11_eval_5_1 : orbMultWNeg11 5 1 = (955/148 : ℝ) := rfl
@[simp] theorem orbMultWNeg11_eval_5_2 : orbMultWNeg11 5 2 = (-11/105 : ℝ) := rfl
@[simp] theorem orbMultWNeg12_eval_0_0 : orbMultWNeg12 0 0 = (22883/152 : ℝ) := rfl
@[simp] theorem orbMultWNeg12_eval_0_1 : orbMultWNeg12 0 1 = (2089/59 : ℝ) := rfl
@[simp] theorem orbMultWNeg12_eval_0_2 : orbMultWNeg12 0 2 = (-96/185 : ℝ) := rfl
@[simp] theorem orbMultWNeg12_eval_3_0 : orbMultWNeg12 3 0 = (-3730/159 : ℝ) := rfl
@[simp] theorem orbMultWNeg12_eval_3_1 : orbMultWNeg12 3 1 = (-457/49 : ℝ) := rfl
@[simp] theorem orbMultWNeg12_eval_3_2 : orbMultWNeg12 3 2 = (-95/253 : ℝ) := rfl
@[simp] theorem orbMultWNeg12_eval_4_0 : orbMultWNeg12 4 0 = (-23709/95 : ℝ) := rfl
@[simp] theorem orbMultWNeg12_eval_4_1 : orbMultWNeg12 4 1 = (-13261/206 : ℝ) := rfl
@[simp] theorem orbMultWNeg12_eval_4_2 : orbMultWNeg12 4 2 = (185/177 : ℝ) := rfl
@[simp] theorem orbMultWNeg13_eval_0_0 : orbMultWNeg13 0 0 = (513/82 : ℝ) := rfl
@[simp] theorem orbMultWNeg13_eval_0_1 : orbMultWNeg13 0 1 = (-1237/131 : ℝ) := rfl
@[simp] theorem orbMultWNeg13_eval_0_2 : orbMultWNeg13 0 2 = (1047/172 : ℝ) := rfl
@[simp] theorem orbMultWNeg13_eval_2_0 : orbMultWNeg13 2 0 = (1303/113 : ℝ) := rfl
@[simp] theorem orbMultWNeg13_eval_2_1 : orbMultWNeg13 2 1 = (-925/57 : ℝ) := rfl
@[simp] theorem orbMultWNeg13_eval_2_2 : orbMultWNeg13 2 2 = (434/23 : ℝ) := rfl
@[simp] theorem orbMultWNeg13_eval_5_0 : orbMultWNeg13 5 0 = (-1132/247 : ℝ) := rfl
@[simp] theorem orbMultWNeg13_eval_5_1 : orbMultWNeg13 5 1 = (1837/229 : ℝ) := rfl
@[simp] theorem orbMultWNeg13_eval_5_2 : orbMultWNeg13 5 2 = (-730/151 : ℝ) := rfl
@[simp] theorem orbMultWNeg14_eval_0_0 : orbMultWNeg14 0 0 = (50573/218 : ℝ) := rfl
@[simp] theorem orbMultWNeg14_eval_0_1 : orbMultWNeg14 0 1 = (6714/139 : ℝ) := rfl
@[simp] theorem orbMultWNeg14_eval_0_2 : orbMultWNeg14 0 2 = (-10803/200 : ℝ) := rfl
@[simp] theorem orbMultWNeg14_eval_2_0 : orbMultWNeg14 2 0 = (-21385/209 : ℝ) := rfl
@[simp] theorem orbMultWNeg14_eval_2_1 : orbMultWNeg14 2 1 = (-4335/161 : ℝ) := rfl
@[simp] theorem orbMultWNeg14_eval_2_2 : orbMultWNeg14 2 2 = (3075/83 : ℝ) := rfl
@[simp] theorem orbMultWNeg14_eval_4_0 : orbMultWNeg14 4 0 = (-78529/194 : ℝ) := rfl
@[simp] theorem orbMultWNeg14_eval_4_1 : orbMultWNeg14 4 1 = (-13823/153 : ℝ) := rfl
@[simp] theorem orbMultWNeg14_eval_4_2 : orbMultWNeg14 4 2 = (8422/85 : ℝ) := rfl
@[simp] theorem orbMultWNeg15_eval_0_0 : orbMultWNeg15 0 0 = (497/82 : ℝ) := rfl
@[simp] theorem orbMultWNeg15_eval_0_1 : orbMultWNeg15 0 1 = (472/137 : ℝ) := rfl
@[simp] theorem orbMultWNeg15_eval_0_2 : orbMultWNeg15 0 2 = (635/28 : ℝ) := rfl
@[simp] theorem orbMultWNeg15_eval_2_0 : orbMultWNeg15 2 0 = (10697/249 : ℝ) := rfl
@[simp] theorem orbMultWNeg15_eval_2_1 : orbMultWNeg15 2 1 = (10344/155 : ℝ) := rfl
@[simp] theorem orbMultWNeg15_eval_2_2 : orbMultWNeg15 2 2 = (43324/183 : ℝ) := rfl
@[simp] theorem orbMultWNeg15_eval_3_0 : orbMultWNeg15 3 0 = (-4132/229 : ℝ) := rfl
@[simp] theorem orbMultWNeg15_eval_3_1 : orbMultWNeg15 3 1 = (-3666/113 : ℝ) := rfl
@[simp] theorem orbMultWNeg15_eval_3_2 : orbMultWNeg15 3 2 = (-419/4 : ℝ) := rfl
@[simp] theorem orbMultWNeg16_eval_0_0 : orbMultWNeg16 0 0 = (1217/216 : ℝ) := rfl
@[simp] theorem orbMultWNeg16_eval_0_1 : orbMultWNeg16 0 1 = (-2617/222 : ℝ) := rfl
@[simp] theorem orbMultWNeg16_eval_0_2 : orbMultWNeg16 0 2 = (157/249 : ℝ) := rfl
@[simp] theorem orbMultWNeg16_eval_1_0 : orbMultWNeg16 1 0 = (-1031/252 : ℝ) := rfl
@[simp] theorem orbMultWNeg16_eval_1_1 : orbMultWNeg16 1 1 = (2515/244 : ℝ) := rfl
@[simp] theorem orbMultWNeg16_eval_1_2 : orbMultWNeg16 1 2 = (-25/59 : ℝ) := rfl
@[simp] theorem orbMultWNeg16_eval_5_0 : orbMultWNeg16 5 0 = (-239/54 : ℝ) := rfl
@[simp] theorem orbMultWNeg16_eval_5_1 : orbMultWNeg16 5 1 = (161/15 : ℝ) := rfl
@[simp] theorem orbMultWNeg16_eval_5_2 : orbMultWNeg16 5 2 = (-128/239 : ℝ) := rfl
@[simp] theorem orbMultWNeg17_eval_0_0 : orbMultWNeg17 0 0 = (292/3 : ℝ) := rfl
@[simp] theorem orbMultWNeg17_eval_0_1 : orbMultWNeg17 0 1 = (3147/170 : ℝ) := rfl
@[simp] theorem orbMultWNeg17_eval_0_2 : orbMultWNeg17 0 2 = (-484/249 : ℝ) := rfl
@[simp] theorem orbMultWNeg17_eval_1_0 : orbMultWNeg17 1 0 = (893/139 : ℝ) := rfl
@[simp] theorem orbMultWNeg17_eval_1_1 : orbMultWNeg17 1 1 = (1189/228 : ℝ) := rfl
@[simp] theorem orbMultWNeg17_eval_1_2 : orbMultWNeg17 1 2 = (-12/47 : ℝ) := rfl
@[simp] theorem orbMultWNeg17_eval_4_0 : orbMultWNeg17 4 0 = (-15317/96 : ℝ) := rfl
@[simp] theorem orbMultWNeg17_eval_4_1 : orbMultWNeg17 4 1 = (-9209/248 : ℝ) := rfl
@[simp] theorem orbMultWNeg17_eval_4_2 : orbMultWNeg17 4 2 = (509/140 : ℝ) := rfl
@[simp] theorem orbMultWNeg18_eval_0_0 : orbMultWNeg18 0 0 = (698/247 : ℝ) := rfl
@[simp] theorem orbMultWNeg18_eval_0_1 : orbMultWNeg18 0 1 = (-556/103 : ℝ) := rfl
@[simp] theorem orbMultWNeg18_eval_0_2 : orbMultWNeg18 0 2 = (8/143 : ℝ) := rfl
@[simp] theorem orbMultWNeg18_eval_1_0 : orbMultWNeg18 1 0 = (-429/229 : ℝ) := rfl
@[simp] theorem orbMultWNeg18_eval_1_1 : orbMultWNeg18 1 1 = (771/143 : ℝ) := rfl
@[simp] theorem orbMultWNeg18_eval_1_2 : orbMultWNeg18 1 2 = (17/165 : ℝ) := rfl
@[simp] theorem orbMultWNeg18_eval_3_0 : orbMultWNeg18 3 0 = (441/248 : ℝ) := rfl
@[simp] theorem orbMultWNeg18_eval_3_1 : orbMultWNeg18 3 1 = (-485/86 : ℝ) := rfl
@[simp] theorem orbMultWNeg18_eval_3_2 : orbMultWNeg18 3 2 = (-128/243 : ℝ) := rfl
@[simp] theorem orbMultWNeg19_eval_0_0 : orbMultWNeg19 0 0 = (575/176 : ℝ) := rfl
@[simp] theorem orbMultWNeg19_eval_0_1 : orbMultWNeg19 0 1 = (-1132/243 : ℝ) := rfl
@[simp] theorem orbMultWNeg19_eval_0_2 : orbMultWNeg19 0 2 = (49/19 : ℝ) := rfl
@[simp] theorem orbMultWNeg19_eval_1_0 : orbMultWNeg19 1 0 = (-97/60 : ℝ) := rfl
@[simp] theorem orbMultWNeg19_eval_1_1 : orbMultWNeg19 1 1 = (449/118 : ℝ) := rfl
@[simp] theorem orbMultWNeg19_eval_1_2 : orbMultWNeg19 1 2 = (-68/73 : ℝ) := rfl
@[simp] theorem orbMultWNeg19_eval_2_0 : orbMultWNeg19 2 0 = (1236/253 : ℝ) := rfl
@[simp] theorem orbMultWNeg19_eval_2_1 : orbMultWNeg19 2 1 = (-1205/237 : ℝ) := rfl
@[simp] theorem orbMultWNeg19_eval_2_2 : orbMultWNeg19 2 2 = (2019/176 : ℝ) := rfl

/-! ### Elementary facts -/

theorem orbWeight_pos : ∀ c, 0 < orbWeight c := by
  intro c; fin_cases c <;> norm_num

theorem orbWeight_sum : ∑ c, orbWeight c = 1 := by
  norm_num [Fin.sum_univ_six]

theorem orbStress_full : ∀ c, orbStress c ≠ 0 := by
  intro c; fin_cases c <;> norm_num

theorem orbStress_zeroSum : ∑ c, orbStress c = 0 := by
  norm_num [Fin.sum_univ_six]

theorem orbStress_kills : ∑ c, orbStress c • atomMatrix (orbAtom c) = 0 := by
  ext rowIdx colIdx
  fin_cases rowIdx <;> fin_cases colIdx <;>
    norm_num [Fin.sum_univ_six, atomMatrix, Matrix.vecMulVec_apply,
      Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply]

theorem orbStress_posSide : ∀ c : Fin 6, c.val < 3 → 0 < orbStress c := by
  intro c hc; fin_cases c <;> first | exact absurd hc (by decide) | norm_num

theorem orbStress_negSide : ∀ c : Fin 6, 3 ≤ c.val → orbStress c < 0 := by
  intro c hc; fin_cases c <;> first | exact absurd hc (by decide) | norm_num

theorem orbAtom_diagonal : ∀ (c : Fin 6) (coord : Fin 3), c.val < 3 →
    coord.val ≠ c.val → orbAtom c coord = 0 := by
  intro c coord hc hne
  fin_cases c <;> fin_cases coord <;>
    first | exact absurd rfl hne | exact absurd hc (by decide) | norm_num

theorem orbPos_resolution : (∑ c ∈ ({0, 1, 2} : Finset (Fin 6)),
    orbStress c • atomMatrix (orbAtom c)) = 1 := by
  rw [sum_tripleFinset_eq (by decide) (by decide) (by decide)]
  ext rowIdx colIdx
  fin_cases rowIdx <;> fin_cases colIdx <;>
    norm_num [atomMatrix, Matrix.vecMulVec_apply, Matrix.add_apply,
      Matrix.smul_apply, smul_eq_mul, Matrix.one_apply] <;> decide

theorem orbNeg_resolution : (∑ c ∈ ({3, 4, 5} : Finset (Fin 6)),
    (-orbStress c) • atomMatrix (orbAtom c)) = 1 := by
  rw [sum_tripleFinset_eq (by decide) (by decide) (by decide)]
  ext rowIdx colIdx
  fin_cases rowIdx <;> fin_cases colIdx <;>
    norm_num [atomMatrix, Matrix.vecMulVec_apply, Matrix.add_apply,
      Matrix.smul_apply, smul_eq_mul, Matrix.one_apply] <;> decide

theorem orbPrimitive : ∀ (keptLabel dropLabel : Fin 6) (ratio : ℝ),
    keptLabel ≠ dropLabel → orbAtom dropLabel ≠ ratio • orbAtom keptLabel := by
  intro keptLabel dropLabel ratio hne heq
  have h0 := congrFun heq 0
  have h1 := congrFun heq 1
  have h2 := congrFun heq 2
  simp only [Pi.smul_apply, smul_eq_mul] at h0 h1 h2
  fin_cases keptLabel <;> fin_cases dropLabel <;>
    first
      | exact hne rfl
      | ((try norm_num at h0)
         (try norm_num at h1)
         (try norm_num at h2)
         all_goals (first
           | linarith [h0, h1, h2]
           | linarith [h0, h1]
           | linarith [h0, h2]
           | linarith [h1, h2]))

theorem orbStepPos_nonneg : (0 : ℝ) ≤ (64/17161 : ℝ) := by norm_num
theorem orbStepNeg_nonneg : (0 : ℝ) ≤ (257436940512636031388623573144576000/266967897115158419241951304186321975977 : ℝ) := by norm_num

theorem orbWalkPos_eq :
    orbWalkPos = (fun c => orbWeight c - (64/17161 : ℝ) * orbStress c) := by
  funext c; fin_cases c <;> norm_num

theorem orbWalkNeg_eq :
    orbWalkNeg = (fun c => orbWeight c + (257436940512636031388623573144576000/266967897115158419241951304186321975977 : ℝ) * orbStress c) := by
  funext c; fin_cases c <;> norm_num

theorem orbWalkPos_nonneg : ∀ c, 0 ≤ orbWalkPos c := by
  intro c; fin_cases c <;> norm_num

theorem orbWalkNeg_nonneg : ∀ c, 0 ≤ orbWalkNeg c := by
  intro c; fin_cases c <;> norm_num

theorem orbWalkPos_vanish : ∃ c, 0 < orbStress c ∧ orbWalkPos c = 0 :=
  ⟨1, by norm_num, by norm_num⟩

theorem orbWalkNeg_vanish : ∃ c, orbStress c < 0 ∧ orbWalkNeg c = 0 :=
  ⟨5, by norm_num, by norm_num⟩

theorem orbWitnessPos_ne : orbWitnessPos ≠ 0 := by
  intro hzero
  have hentry := congrFun hzero 1
  norm_num at hentry

theorem orbPosGap_value :
    (∑ c ∈ ({0, 1, 2} : Finset (Fin 6)),
        (orbAtom c ⬝ᵥ orbWitnessPos) ^ 2)
      - (∑ c, orbWeight c * (orbAtom c ⬝ᵥ orbWitnessPos) ^ 2) ≤ 0 := by
  rw [sum_tripleFinset_eq (by decide) (by decide) (by decide), Fin.sum_univ_six]
  norm_num [dotProduct, Fin.sum_univ_three]

theorem orbWitnessNeg_ne : orbWitnessNeg ≠ 0 := by
  intro hzero
  have hentry := congrFun hzero 2
  norm_num at hentry

theorem orbNegGap_value :
    (∑ c ∈ ({3, 4, 5} : Finset (Fin 6)),
        (orbAtom c ⬝ᵥ orbWitnessNeg) ^ 2)
      - (∑ c, orbWeight c * (orbAtom c ⬝ᵥ orbWitnessNeg) ^ 2) ≤ 0 := by
  rw [sum_tripleFinset_eq (by decide) (by decide) (by decide), Fin.sum_univ_six]
  norm_num [dotProduct, Fin.sum_univ_three]

theorem orbBudgetBoundInt0 :
    1 ≤ ∑ c ∈ (({0, 1, 2} : Finset (Fin 6)))ᶜ, orbWeight c
        * (2 * (orbAtom c ⬝ᵥ orbMultInt0 c)
          - ∑ d ∈ ({0, 1, 2} : Finset (Fin 6)), (1 - orbWeight d)
              * (orbAtom d ⬝ᵥ orbMultInt0 c) ^ 2) := by
  rw [show (({0, 1, 2} : Finset (Fin 6)))ᶜ
      = ({3, 4, 5} : Finset (Fin 6)) from by decide]
  rw [sum_tripleFinset_eq (by decide) (by decide) (by decide)]
  simp only [sum_tripleFinset_eq (show (0 : Fin 6) ≠ 1 by decide)
    (show (0 : Fin 6) ≠ 2 by decide) (show (1 : Fin 6) ≠ 2 by decide)]
  norm_num [dotProduct, Fin.sum_univ_three]

theorem orbBudgetBoundInt1 :
    1 ≤ ∑ c ∈ (({0, 1, 3} : Finset (Fin 6)))ᶜ, orbWeight c
        * (2 * (orbAtom c ⬝ᵥ orbMultInt1 c)
          - ∑ d ∈ ({0, 1, 3} : Finset (Fin 6)), (1 - orbWeight d)
              * (orbAtom d ⬝ᵥ orbMultInt1 c) ^ 2) := by
  rw [show (({0, 1, 3} : Finset (Fin 6)))ᶜ
      = ({2, 4, 5} : Finset (Fin 6)) from by decide]
  rw [sum_tripleFinset_eq (by decide) (by decide) (by decide)]
  simp only [sum_tripleFinset_eq (show (0 : Fin 6) ≠ 1 by decide)
    (show (0 : Fin 6) ≠ 3 by decide) (show (1 : Fin 6) ≠ 3 by decide)]
  norm_num [dotProduct, Fin.sum_univ_three]

theorem orbBudgetBoundInt2 :
    1 ≤ ∑ c ∈ (({0, 1, 4} : Finset (Fin 6)))ᶜ, orbWeight c
        * (2 * (orbAtom c ⬝ᵥ orbMultInt2 c)
          - ∑ d ∈ ({0, 1, 4} : Finset (Fin 6)), (1 - orbWeight d)
              * (orbAtom d ⬝ᵥ orbMultInt2 c) ^ 2) := by
  rw [show (({0, 1, 4} : Finset (Fin 6)))ᶜ
      = ({2, 3, 5} : Finset (Fin 6)) from by decide]
  rw [sum_tripleFinset_eq (by decide) (by decide) (by decide)]
  simp only [sum_tripleFinset_eq (show (0 : Fin 6) ≠ 1 by decide)
    (show (0 : Fin 6) ≠ 4 by decide) (show (1 : Fin 6) ≠ 4 by decide)]
  norm_num [dotProduct, Fin.sum_univ_three]

theorem orbBudgetBoundInt3 :
    1 ≤ ∑ c ∈ (({0, 1, 5} : Finset (Fin 6)))ᶜ, orbWeight c
        * (2 * (orbAtom c ⬝ᵥ orbMultInt3 c)
          - ∑ d ∈ ({0, 1, 5} : Finset (Fin 6)), (1 - orbWeight d)
              * (orbAtom d ⬝ᵥ orbMultInt3 c) ^ 2) := by
  rw [show (({0, 1, 5} : Finset (Fin 6)))ᶜ
      = ({2, 3, 4} : Finset (Fin 6)) from by decide]
  rw [sum_tripleFinset_eq (by decide) (by decide) (by decide)]
  simp only [sum_tripleFinset_eq (show (0 : Fin 6) ≠ 1 by decide)
    (show (0 : Fin 6) ≠ 5 by decide) (show (1 : Fin 6) ≠ 5 by decide)]
  norm_num [dotProduct, Fin.sum_univ_three]

theorem orbBudgetBoundInt4 :
    1 ≤ ∑ c ∈ (({0, 2, 3} : Finset (Fin 6)))ᶜ, orbWeight c
        * (2 * (orbAtom c ⬝ᵥ orbMultInt4 c)
          - ∑ d ∈ ({0, 2, 3} : Finset (Fin 6)), (1 - orbWeight d)
              * (orbAtom d ⬝ᵥ orbMultInt4 c) ^ 2) := by
  rw [show (({0, 2, 3} : Finset (Fin 6)))ᶜ
      = ({1, 4, 5} : Finset (Fin 6)) from by decide]
  rw [sum_tripleFinset_eq (by decide) (by decide) (by decide)]
  simp only [sum_tripleFinset_eq (show (0 : Fin 6) ≠ 2 by decide)
    (show (0 : Fin 6) ≠ 3 by decide) (show (2 : Fin 6) ≠ 3 by decide)]
  norm_num [dotProduct, Fin.sum_univ_three]

theorem orbBudgetBoundInt5 :
    1 ≤ ∑ c ∈ (({0, 2, 4} : Finset (Fin 6)))ᶜ, orbWeight c
        * (2 * (orbAtom c ⬝ᵥ orbMultInt5 c)
          - ∑ d ∈ ({0, 2, 4} : Finset (Fin 6)), (1 - orbWeight d)
              * (orbAtom d ⬝ᵥ orbMultInt5 c) ^ 2) := by
  rw [show (({0, 2, 4} : Finset (Fin 6)))ᶜ
      = ({1, 3, 5} : Finset (Fin 6)) from by decide]
  rw [sum_tripleFinset_eq (by decide) (by decide) (by decide)]
  simp only [sum_tripleFinset_eq (show (0 : Fin 6) ≠ 2 by decide)
    (show (0 : Fin 6) ≠ 4 by decide) (show (2 : Fin 6) ≠ 4 by decide)]
  norm_num [dotProduct, Fin.sum_univ_three]

theorem orbBudgetBoundInt6 :
    1 ≤ ∑ c ∈ (({0, 2, 5} : Finset (Fin 6)))ᶜ, orbWeight c
        * (2 * (orbAtom c ⬝ᵥ orbMultInt6 c)
          - ∑ d ∈ ({0, 2, 5} : Finset (Fin 6)), (1 - orbWeight d)
              * (orbAtom d ⬝ᵥ orbMultInt6 c) ^ 2) := by
  rw [show (({0, 2, 5} : Finset (Fin 6)))ᶜ
      = ({1, 3, 4} : Finset (Fin 6)) from by decide]
  rw [sum_tripleFinset_eq (by decide) (by decide) (by decide)]
  simp only [sum_tripleFinset_eq (show (0 : Fin 6) ≠ 2 by decide)
    (show (0 : Fin 6) ≠ 5 by decide) (show (2 : Fin 6) ≠ 5 by decide)]
  norm_num [dotProduct, Fin.sum_univ_three]

theorem orbBudgetBoundInt7 :
    1 ≤ ∑ c ∈ (({0, 3, 4} : Finset (Fin 6)))ᶜ, orbWeight c
        * (2 * (orbAtom c ⬝ᵥ orbMultInt7 c)
          - ∑ d ∈ ({0, 3, 4} : Finset (Fin 6)), (1 - orbWeight d)
              * (orbAtom d ⬝ᵥ orbMultInt7 c) ^ 2) := by
  rw [show (({0, 3, 4} : Finset (Fin 6)))ᶜ
      = ({1, 2, 5} : Finset (Fin 6)) from by decide]
  rw [sum_tripleFinset_eq (by decide) (by decide) (by decide)]
  simp only [sum_tripleFinset_eq (show (0 : Fin 6) ≠ 3 by decide)
    (show (0 : Fin 6) ≠ 4 by decide) (show (3 : Fin 6) ≠ 4 by decide)]
  norm_num [dotProduct, Fin.sum_univ_three]

theorem orbBudgetBoundInt8 :
    1 ≤ ∑ c ∈ (({0, 3, 5} : Finset (Fin 6)))ᶜ, orbWeight c
        * (2 * (orbAtom c ⬝ᵥ orbMultInt8 c)
          - ∑ d ∈ ({0, 3, 5} : Finset (Fin 6)), (1 - orbWeight d)
              * (orbAtom d ⬝ᵥ orbMultInt8 c) ^ 2) := by
  rw [show (({0, 3, 5} : Finset (Fin 6)))ᶜ
      = ({1, 2, 4} : Finset (Fin 6)) from by decide]
  rw [sum_tripleFinset_eq (by decide) (by decide) (by decide)]
  simp only [sum_tripleFinset_eq (show (0 : Fin 6) ≠ 3 by decide)
    (show (0 : Fin 6) ≠ 5 by decide) (show (3 : Fin 6) ≠ 5 by decide)]
  norm_num [dotProduct, Fin.sum_univ_three]

theorem orbBudgetBoundInt9 :
    1 ≤ ∑ c ∈ (({0, 4, 5} : Finset (Fin 6)))ᶜ, orbWeight c
        * (2 * (orbAtom c ⬝ᵥ orbMultInt9 c)
          - ∑ d ∈ ({0, 4, 5} : Finset (Fin 6)), (1 - orbWeight d)
              * (orbAtom d ⬝ᵥ orbMultInt9 c) ^ 2) := by
  rw [show (({0, 4, 5} : Finset (Fin 6)))ᶜ
      = ({1, 2, 3} : Finset (Fin 6)) from by decide]
  rw [sum_tripleFinset_eq (by decide) (by decide) (by decide)]
  simp only [sum_tripleFinset_eq (show (0 : Fin 6) ≠ 4 by decide)
    (show (0 : Fin 6) ≠ 5 by decide) (show (4 : Fin 6) ≠ 5 by decide)]
  norm_num [dotProduct, Fin.sum_univ_three]

theorem orbBudgetBoundInt10 :
    1 ≤ ∑ c ∈ (({1, 2, 3} : Finset (Fin 6)))ᶜ, orbWeight c
        * (2 * (orbAtom c ⬝ᵥ orbMultInt10 c)
          - ∑ d ∈ ({1, 2, 3} : Finset (Fin 6)), (1 - orbWeight d)
              * (orbAtom d ⬝ᵥ orbMultInt10 c) ^ 2) := by
  rw [show (({1, 2, 3} : Finset (Fin 6)))ᶜ
      = ({0, 4, 5} : Finset (Fin 6)) from by decide]
  rw [sum_tripleFinset_eq (by decide) (by decide) (by decide)]
  simp only [sum_tripleFinset_eq (show (1 : Fin 6) ≠ 2 by decide)
    (show (1 : Fin 6) ≠ 3 by decide) (show (2 : Fin 6) ≠ 3 by decide)]
  norm_num [dotProduct, Fin.sum_univ_three]

theorem orbBudgetBoundInt11 :
    1 ≤ ∑ c ∈ (({1, 2, 4} : Finset (Fin 6)))ᶜ, orbWeight c
        * (2 * (orbAtom c ⬝ᵥ orbMultInt11 c)
          - ∑ d ∈ ({1, 2, 4} : Finset (Fin 6)), (1 - orbWeight d)
              * (orbAtom d ⬝ᵥ orbMultInt11 c) ^ 2) := by
  rw [show (({1, 2, 4} : Finset (Fin 6)))ᶜ
      = ({0, 3, 5} : Finset (Fin 6)) from by decide]
  rw [sum_tripleFinset_eq (by decide) (by decide) (by decide)]
  simp only [sum_tripleFinset_eq (show (1 : Fin 6) ≠ 2 by decide)
    (show (1 : Fin 6) ≠ 4 by decide) (show (2 : Fin 6) ≠ 4 by decide)]
  norm_num [dotProduct, Fin.sum_univ_three]

theorem orbBudgetBoundInt12 :
    1 ≤ ∑ c ∈ (({1, 2, 5} : Finset (Fin 6)))ᶜ, orbWeight c
        * (2 * (orbAtom c ⬝ᵥ orbMultInt12 c)
          - ∑ d ∈ ({1, 2, 5} : Finset (Fin 6)), (1 - orbWeight d)
              * (orbAtom d ⬝ᵥ orbMultInt12 c) ^ 2) := by
  rw [show (({1, 2, 5} : Finset (Fin 6)))ᶜ
      = ({0, 3, 4} : Finset (Fin 6)) from by decide]
  rw [sum_tripleFinset_eq (by decide) (by decide) (by decide)]
  simp only [sum_tripleFinset_eq (show (1 : Fin 6) ≠ 2 by decide)
    (show (1 : Fin 6) ≠ 5 by decide) (show (2 : Fin 6) ≠ 5 by decide)]
  norm_num [dotProduct, Fin.sum_univ_three]

theorem orbBudgetBoundInt13 :
    1 ≤ ∑ c ∈ (({1, 3, 4} : Finset (Fin 6)))ᶜ, orbWeight c
        * (2 * (orbAtom c ⬝ᵥ orbMultInt13 c)
          - ∑ d ∈ ({1, 3, 4} : Finset (Fin 6)), (1 - orbWeight d)
              * (orbAtom d ⬝ᵥ orbMultInt13 c) ^ 2) := by
  rw [show (({1, 3, 4} : Finset (Fin 6)))ᶜ
      = ({0, 2, 5} : Finset (Fin 6)) from by decide]
  rw [sum_tripleFinset_eq (by decide) (by decide) (by decide)]
  simp only [sum_tripleFinset_eq (show (1 : Fin 6) ≠ 3 by decide)
    (show (1 : Fin 6) ≠ 4 by decide) (show (3 : Fin 6) ≠ 4 by decide)]
  norm_num [dotProduct, Fin.sum_univ_three]

theorem orbBudgetBoundInt14 :
    1 ≤ ∑ c ∈ (({1, 3, 5} : Finset (Fin 6)))ᶜ, orbWeight c
        * (2 * (orbAtom c ⬝ᵥ orbMultInt14 c)
          - ∑ d ∈ ({1, 3, 5} : Finset (Fin 6)), (1 - orbWeight d)
              * (orbAtom d ⬝ᵥ orbMultInt14 c) ^ 2) := by
  rw [show (({1, 3, 5} : Finset (Fin 6)))ᶜ
      = ({0, 2, 4} : Finset (Fin 6)) from by decide]
  rw [sum_tripleFinset_eq (by decide) (by decide) (by decide)]
  simp only [sum_tripleFinset_eq (show (1 : Fin 6) ≠ 3 by decide)
    (show (1 : Fin 6) ≠ 5 by decide) (show (3 : Fin 6) ≠ 5 by decide)]
  norm_num [dotProduct, Fin.sum_univ_three]

theorem orbBudgetBoundInt15 :
    1 ≤ ∑ c ∈ (({1, 4, 5} : Finset (Fin 6)))ᶜ, orbWeight c
        * (2 * (orbAtom c ⬝ᵥ orbMultInt15 c)
          - ∑ d ∈ ({1, 4, 5} : Finset (Fin 6)), (1 - orbWeight d)
              * (orbAtom d ⬝ᵥ orbMultInt15 c) ^ 2) := by
  rw [show (({1, 4, 5} : Finset (Fin 6)))ᶜ
      = ({0, 2, 3} : Finset (Fin 6)) from by decide]
  rw [sum_tripleFinset_eq (by decide) (by decide) (by decide)]
  simp only [sum_tripleFinset_eq (show (1 : Fin 6) ≠ 4 by decide)
    (show (1 : Fin 6) ≠ 5 by decide) (show (4 : Fin 6) ≠ 5 by decide)]
  norm_num [dotProduct, Fin.sum_univ_three]

theorem orbBudgetBoundInt16 :
    1 ≤ ∑ c ∈ (({2, 3, 4} : Finset (Fin 6)))ᶜ, orbWeight c
        * (2 * (orbAtom c ⬝ᵥ orbMultInt16 c)
          - ∑ d ∈ ({2, 3, 4} : Finset (Fin 6)), (1 - orbWeight d)
              * (orbAtom d ⬝ᵥ orbMultInt16 c) ^ 2) := by
  rw [show (({2, 3, 4} : Finset (Fin 6)))ᶜ
      = ({0, 1, 5} : Finset (Fin 6)) from by decide]
  rw [sum_tripleFinset_eq (by decide) (by decide) (by decide)]
  simp only [sum_tripleFinset_eq (show (2 : Fin 6) ≠ 3 by decide)
    (show (2 : Fin 6) ≠ 4 by decide) (show (3 : Fin 6) ≠ 4 by decide)]
  norm_num [dotProduct, Fin.sum_univ_three]

theorem orbBudgetBoundInt17 :
    1 ≤ ∑ c ∈ (({2, 3, 5} : Finset (Fin 6)))ᶜ, orbWeight c
        * (2 * (orbAtom c ⬝ᵥ orbMultInt17 c)
          - ∑ d ∈ ({2, 3, 5} : Finset (Fin 6)), (1 - orbWeight d)
              * (orbAtom d ⬝ᵥ orbMultInt17 c) ^ 2) := by
  rw [show (({2, 3, 5} : Finset (Fin 6)))ᶜ
      = ({0, 1, 4} : Finset (Fin 6)) from by decide]
  rw [sum_tripleFinset_eq (by decide) (by decide) (by decide)]
  simp only [sum_tripleFinset_eq (show (2 : Fin 6) ≠ 3 by decide)
    (show (2 : Fin 6) ≠ 5 by decide) (show (3 : Fin 6) ≠ 5 by decide)]
  norm_num [dotProduct, Fin.sum_univ_three]

theorem orbBudgetBoundInt18 :
    1 ≤ ∑ c ∈ (({2, 4, 5} : Finset (Fin 6)))ᶜ, orbWeight c
        * (2 * (orbAtom c ⬝ᵥ orbMultInt18 c)
          - ∑ d ∈ ({2, 4, 5} : Finset (Fin 6)), (1 - orbWeight d)
              * (orbAtom d ⬝ᵥ orbMultInt18 c) ^ 2) := by
  rw [show (({2, 4, 5} : Finset (Fin 6)))ᶜ
      = ({0, 1, 3} : Finset (Fin 6)) from by decide]
  rw [sum_tripleFinset_eq (by decide) (by decide) (by decide)]
  simp only [sum_tripleFinset_eq (show (2 : Fin 6) ≠ 4 by decide)
    (show (2 : Fin 6) ≠ 5 by decide) (show (4 : Fin 6) ≠ 5 by decide)]
  norm_num [dotProduct, Fin.sum_univ_three]

theorem orbBudgetBoundInt19 :
    1 ≤ ∑ c ∈ (({3, 4, 5} : Finset (Fin 6)))ᶜ, orbWeight c
        * (2 * (orbAtom c ⬝ᵥ orbMultInt19 c)
          - ∑ d ∈ ({3, 4, 5} : Finset (Fin 6)), (1 - orbWeight d)
              * (orbAtom d ⬝ᵥ orbMultInt19 c) ^ 2) := by
  rw [show (({3, 4, 5} : Finset (Fin 6)))ᶜ
      = ({0, 1, 2} : Finset (Fin 6)) from by decide]
  rw [sum_tripleFinset_eq (by decide) (by decide) (by decide)]
  simp only [sum_tripleFinset_eq (show (3 : Fin 6) ≠ 4 by decide)
    (show (3 : Fin 6) ≠ 5 by decide) (show (4 : Fin 6) ≠ 5 by decide)]
  norm_num [dotProduct, Fin.sum_univ_three]

theorem orbBudgetBoundWPos0 :
    1 ≤ ∑ c ∈ (({0, 1, 2} : Finset (Fin 6)))ᶜ, orbWalkPos c
        * (2 * (orbAtom c ⬝ᵥ orbMultWPos0 c)
          - ∑ d ∈ ({0, 1, 2} : Finset (Fin 6)), (1 - orbWalkPos d)
              * (orbAtom d ⬝ᵥ orbMultWPos0 c) ^ 2) := by
  rw [show (({0, 1, 2} : Finset (Fin 6)))ᶜ
      = ({3, 4, 5} : Finset (Fin 6)) from by decide]
  rw [sum_tripleFinset_eq (by decide) (by decide) (by decide)]
  simp only [sum_tripleFinset_eq (show (0 : Fin 6) ≠ 1 by decide)
    (show (0 : Fin 6) ≠ 2 by decide) (show (1 : Fin 6) ≠ 2 by decide)]
  norm_num [dotProduct, Fin.sum_univ_three]

theorem orbBudgetBoundWPos1 :
    1 ≤ ∑ c ∈ (({0, 1, 3} : Finset (Fin 6)))ᶜ, orbWalkPos c
        * (2 * (orbAtom c ⬝ᵥ orbMultWPos1 c)
          - ∑ d ∈ ({0, 1, 3} : Finset (Fin 6)), (1 - orbWalkPos d)
              * (orbAtom d ⬝ᵥ orbMultWPos1 c) ^ 2) := by
  rw [show (({0, 1, 3} : Finset (Fin 6)))ᶜ
      = ({2, 4, 5} : Finset (Fin 6)) from by decide]
  rw [sum_tripleFinset_eq (by decide) (by decide) (by decide)]
  simp only [sum_tripleFinset_eq (show (0 : Fin 6) ≠ 1 by decide)
    (show (0 : Fin 6) ≠ 3 by decide) (show (1 : Fin 6) ≠ 3 by decide)]
  norm_num [dotProduct, Fin.sum_univ_three]

theorem orbBudgetBoundWPos2 :
    1 ≤ ∑ c ∈ (({0, 1, 4} : Finset (Fin 6)))ᶜ, orbWalkPos c
        * (2 * (orbAtom c ⬝ᵥ orbMultWPos2 c)
          - ∑ d ∈ ({0, 1, 4} : Finset (Fin 6)), (1 - orbWalkPos d)
              * (orbAtom d ⬝ᵥ orbMultWPos2 c) ^ 2) := by
  rw [show (({0, 1, 4} : Finset (Fin 6)))ᶜ
      = ({2, 3, 5} : Finset (Fin 6)) from by decide]
  rw [sum_tripleFinset_eq (by decide) (by decide) (by decide)]
  simp only [sum_tripleFinset_eq (show (0 : Fin 6) ≠ 1 by decide)
    (show (0 : Fin 6) ≠ 4 by decide) (show (1 : Fin 6) ≠ 4 by decide)]
  norm_num [dotProduct, Fin.sum_univ_three]

theorem orbBudgetBoundWPos3 :
    1 ≤ ∑ c ∈ (({0, 1, 5} : Finset (Fin 6)))ᶜ, orbWalkPos c
        * (2 * (orbAtom c ⬝ᵥ orbMultWPos3 c)
          - ∑ d ∈ ({0, 1, 5} : Finset (Fin 6)), (1 - orbWalkPos d)
              * (orbAtom d ⬝ᵥ orbMultWPos3 c) ^ 2) := by
  rw [show (({0, 1, 5} : Finset (Fin 6)))ᶜ
      = ({2, 3, 4} : Finset (Fin 6)) from by decide]
  rw [sum_tripleFinset_eq (by decide) (by decide) (by decide)]
  simp only [sum_tripleFinset_eq (show (0 : Fin 6) ≠ 1 by decide)
    (show (0 : Fin 6) ≠ 5 by decide) (show (1 : Fin 6) ≠ 5 by decide)]
  norm_num [dotProduct, Fin.sum_univ_three]

theorem orbBudgetBoundWPos4 :
    1 ≤ ∑ c ∈ (({0, 2, 3} : Finset (Fin 6)))ᶜ, orbWalkPos c
        * (2 * (orbAtom c ⬝ᵥ orbMultWPos4 c)
          - ∑ d ∈ ({0, 2, 3} : Finset (Fin 6)), (1 - orbWalkPos d)
              * (orbAtom d ⬝ᵥ orbMultWPos4 c) ^ 2) := by
  rw [show (({0, 2, 3} : Finset (Fin 6)))ᶜ
      = ({1, 4, 5} : Finset (Fin 6)) from by decide]
  rw [sum_tripleFinset_eq (by decide) (by decide) (by decide)]
  simp only [sum_tripleFinset_eq (show (0 : Fin 6) ≠ 2 by decide)
    (show (0 : Fin 6) ≠ 3 by decide) (show (2 : Fin 6) ≠ 3 by decide)]
  norm_num [dotProduct, Fin.sum_univ_three]

theorem orbBudgetBoundWPos5 :
    1 ≤ ∑ c ∈ (({0, 2, 4} : Finset (Fin 6)))ᶜ, orbWalkPos c
        * (2 * (orbAtom c ⬝ᵥ orbMultWPos5 c)
          - ∑ d ∈ ({0, 2, 4} : Finset (Fin 6)), (1 - orbWalkPos d)
              * (orbAtom d ⬝ᵥ orbMultWPos5 c) ^ 2) := by
  rw [show (({0, 2, 4} : Finset (Fin 6)))ᶜ
      = ({1, 3, 5} : Finset (Fin 6)) from by decide]
  rw [sum_tripleFinset_eq (by decide) (by decide) (by decide)]
  simp only [sum_tripleFinset_eq (show (0 : Fin 6) ≠ 2 by decide)
    (show (0 : Fin 6) ≠ 4 by decide) (show (2 : Fin 6) ≠ 4 by decide)]
  norm_num [dotProduct, Fin.sum_univ_three]

theorem orbBudgetBoundWPos6 :
    1 ≤ ∑ c ∈ (({0, 2, 5} : Finset (Fin 6)))ᶜ, orbWalkPos c
        * (2 * (orbAtom c ⬝ᵥ orbMultWPos6 c)
          - ∑ d ∈ ({0, 2, 5} : Finset (Fin 6)), (1 - orbWalkPos d)
              * (orbAtom d ⬝ᵥ orbMultWPos6 c) ^ 2) := by
  rw [show (({0, 2, 5} : Finset (Fin 6)))ᶜ
      = ({1, 3, 4} : Finset (Fin 6)) from by decide]
  rw [sum_tripleFinset_eq (by decide) (by decide) (by decide)]
  simp only [sum_tripleFinset_eq (show (0 : Fin 6) ≠ 2 by decide)
    (show (0 : Fin 6) ≠ 5 by decide) (show (2 : Fin 6) ≠ 5 by decide)]
  norm_num [dotProduct, Fin.sum_univ_three]

theorem orbBudgetBoundWPos7 :
    1 ≤ ∑ c ∈ (({0, 3, 4} : Finset (Fin 6)))ᶜ, orbWalkPos c
        * (2 * (orbAtom c ⬝ᵥ orbMultWPos7 c)
          - ∑ d ∈ ({0, 3, 4} : Finset (Fin 6)), (1 - orbWalkPos d)
              * (orbAtom d ⬝ᵥ orbMultWPos7 c) ^ 2) := by
  rw [show (({0, 3, 4} : Finset (Fin 6)))ᶜ
      = ({1, 2, 5} : Finset (Fin 6)) from by decide]
  rw [sum_tripleFinset_eq (by decide) (by decide) (by decide)]
  simp only [sum_tripleFinset_eq (show (0 : Fin 6) ≠ 3 by decide)
    (show (0 : Fin 6) ≠ 4 by decide) (show (3 : Fin 6) ≠ 4 by decide)]
  norm_num [dotProduct, Fin.sum_univ_three]

theorem orbBudgetBoundWPos8 :
    1 ≤ ∑ c ∈ (({0, 3, 5} : Finset (Fin 6)))ᶜ, orbWalkPos c
        * (2 * (orbAtom c ⬝ᵥ orbMultWPos8 c)
          - ∑ d ∈ ({0, 3, 5} : Finset (Fin 6)), (1 - orbWalkPos d)
              * (orbAtom d ⬝ᵥ orbMultWPos8 c) ^ 2) := by
  rw [show (({0, 3, 5} : Finset (Fin 6)))ᶜ
      = ({1, 2, 4} : Finset (Fin 6)) from by decide]
  rw [sum_tripleFinset_eq (by decide) (by decide) (by decide)]
  simp only [sum_tripleFinset_eq (show (0 : Fin 6) ≠ 3 by decide)
    (show (0 : Fin 6) ≠ 5 by decide) (show (3 : Fin 6) ≠ 5 by decide)]
  norm_num [dotProduct, Fin.sum_univ_three]

theorem orbBudgetBoundWPos9 :
    1 ≤ ∑ c ∈ (({0, 4, 5} : Finset (Fin 6)))ᶜ, orbWalkPos c
        * (2 * (orbAtom c ⬝ᵥ orbMultWPos9 c)
          - ∑ d ∈ ({0, 4, 5} : Finset (Fin 6)), (1 - orbWalkPos d)
              * (orbAtom d ⬝ᵥ orbMultWPos9 c) ^ 2) := by
  rw [show (({0, 4, 5} : Finset (Fin 6)))ᶜ
      = ({1, 2, 3} : Finset (Fin 6)) from by decide]
  rw [sum_tripleFinset_eq (by decide) (by decide) (by decide)]
  simp only [sum_tripleFinset_eq (show (0 : Fin 6) ≠ 4 by decide)
    (show (0 : Fin 6) ≠ 5 by decide) (show (4 : Fin 6) ≠ 5 by decide)]
  norm_num [dotProduct, Fin.sum_univ_three]

theorem orbBudgetBoundWPos10 :
    1 ≤ ∑ c ∈ (({1, 2, 3} : Finset (Fin 6)))ᶜ, orbWalkPos c
        * (2 * (orbAtom c ⬝ᵥ orbMultWPos10 c)
          - ∑ d ∈ ({1, 2, 3} : Finset (Fin 6)), (1 - orbWalkPos d)
              * (orbAtom d ⬝ᵥ orbMultWPos10 c) ^ 2) := by
  rw [show (({1, 2, 3} : Finset (Fin 6)))ᶜ
      = ({0, 4, 5} : Finset (Fin 6)) from by decide]
  rw [sum_tripleFinset_eq (by decide) (by decide) (by decide)]
  simp only [sum_tripleFinset_eq (show (1 : Fin 6) ≠ 2 by decide)
    (show (1 : Fin 6) ≠ 3 by decide) (show (2 : Fin 6) ≠ 3 by decide)]
  norm_num [dotProduct, Fin.sum_univ_three]

theorem orbBudgetBoundWPos11 :
    1 ≤ ∑ c ∈ (({1, 2, 4} : Finset (Fin 6)))ᶜ, orbWalkPos c
        * (2 * (orbAtom c ⬝ᵥ orbMultWPos11 c)
          - ∑ d ∈ ({1, 2, 4} : Finset (Fin 6)), (1 - orbWalkPos d)
              * (orbAtom d ⬝ᵥ orbMultWPos11 c) ^ 2) := by
  rw [show (({1, 2, 4} : Finset (Fin 6)))ᶜ
      = ({0, 3, 5} : Finset (Fin 6)) from by decide]
  rw [sum_tripleFinset_eq (by decide) (by decide) (by decide)]
  simp only [sum_tripleFinset_eq (show (1 : Fin 6) ≠ 2 by decide)
    (show (1 : Fin 6) ≠ 4 by decide) (show (2 : Fin 6) ≠ 4 by decide)]
  norm_num [dotProduct, Fin.sum_univ_three]

theorem orbBudgetBoundWPos12 :
    1 ≤ ∑ c ∈ (({1, 2, 5} : Finset (Fin 6)))ᶜ, orbWalkPos c
        * (2 * (orbAtom c ⬝ᵥ orbMultWPos12 c)
          - ∑ d ∈ ({1, 2, 5} : Finset (Fin 6)), (1 - orbWalkPos d)
              * (orbAtom d ⬝ᵥ orbMultWPos12 c) ^ 2) := by
  rw [show (({1, 2, 5} : Finset (Fin 6)))ᶜ
      = ({0, 3, 4} : Finset (Fin 6)) from by decide]
  rw [sum_tripleFinset_eq (by decide) (by decide) (by decide)]
  simp only [sum_tripleFinset_eq (show (1 : Fin 6) ≠ 2 by decide)
    (show (1 : Fin 6) ≠ 5 by decide) (show (2 : Fin 6) ≠ 5 by decide)]
  norm_num [dotProduct, Fin.sum_univ_three]

theorem orbBudgetBoundWPos13 :
    1 ≤ ∑ c ∈ (({1, 3, 4} : Finset (Fin 6)))ᶜ, orbWalkPos c
        * (2 * (orbAtom c ⬝ᵥ orbMultWPos13 c)
          - ∑ d ∈ ({1, 3, 4} : Finset (Fin 6)), (1 - orbWalkPos d)
              * (orbAtom d ⬝ᵥ orbMultWPos13 c) ^ 2) := by
  rw [show (({1, 3, 4} : Finset (Fin 6)))ᶜ
      = ({0, 2, 5} : Finset (Fin 6)) from by decide]
  rw [sum_tripleFinset_eq (by decide) (by decide) (by decide)]
  simp only [sum_tripleFinset_eq (show (1 : Fin 6) ≠ 3 by decide)
    (show (1 : Fin 6) ≠ 4 by decide) (show (3 : Fin 6) ≠ 4 by decide)]
  norm_num [dotProduct, Fin.sum_univ_three]

theorem orbBudgetBoundWPos14 :
    1 ≤ ∑ c ∈ (({1, 3, 5} : Finset (Fin 6)))ᶜ, orbWalkPos c
        * (2 * (orbAtom c ⬝ᵥ orbMultWPos14 c)
          - ∑ d ∈ ({1, 3, 5} : Finset (Fin 6)), (1 - orbWalkPos d)
              * (orbAtom d ⬝ᵥ orbMultWPos14 c) ^ 2) := by
  rw [show (({1, 3, 5} : Finset (Fin 6)))ᶜ
      = ({0, 2, 4} : Finset (Fin 6)) from by decide]
  rw [sum_tripleFinset_eq (by decide) (by decide) (by decide)]
  simp only [sum_tripleFinset_eq (show (1 : Fin 6) ≠ 3 by decide)
    (show (1 : Fin 6) ≠ 5 by decide) (show (3 : Fin 6) ≠ 5 by decide)]
  norm_num [dotProduct, Fin.sum_univ_three]

theorem orbBudgetBoundWPos15 :
    1 ≤ ∑ c ∈ (({1, 4, 5} : Finset (Fin 6)))ᶜ, orbWalkPos c
        * (2 * (orbAtom c ⬝ᵥ orbMultWPos15 c)
          - ∑ d ∈ ({1, 4, 5} : Finset (Fin 6)), (1 - orbWalkPos d)
              * (orbAtom d ⬝ᵥ orbMultWPos15 c) ^ 2) := by
  rw [show (({1, 4, 5} : Finset (Fin 6)))ᶜ
      = ({0, 2, 3} : Finset (Fin 6)) from by decide]
  rw [sum_tripleFinset_eq (by decide) (by decide) (by decide)]
  simp only [sum_tripleFinset_eq (show (1 : Fin 6) ≠ 4 by decide)
    (show (1 : Fin 6) ≠ 5 by decide) (show (4 : Fin 6) ≠ 5 by decide)]
  norm_num [dotProduct, Fin.sum_univ_three]

theorem orbBudgetBoundWPos16 :
    1 ≤ ∑ c ∈ (({2, 3, 4} : Finset (Fin 6)))ᶜ, orbWalkPos c
        * (2 * (orbAtom c ⬝ᵥ orbMultWPos16 c)
          - ∑ d ∈ ({2, 3, 4} : Finset (Fin 6)), (1 - orbWalkPos d)
              * (orbAtom d ⬝ᵥ orbMultWPos16 c) ^ 2) := by
  rw [show (({2, 3, 4} : Finset (Fin 6)))ᶜ
      = ({0, 1, 5} : Finset (Fin 6)) from by decide]
  rw [sum_tripleFinset_eq (by decide) (by decide) (by decide)]
  simp only [sum_tripleFinset_eq (show (2 : Fin 6) ≠ 3 by decide)
    (show (2 : Fin 6) ≠ 4 by decide) (show (3 : Fin 6) ≠ 4 by decide)]
  norm_num [dotProduct, Fin.sum_univ_three]

theorem orbBudgetBoundWPos17 :
    1 ≤ ∑ c ∈ (({2, 3, 5} : Finset (Fin 6)))ᶜ, orbWalkPos c
        * (2 * (orbAtom c ⬝ᵥ orbMultWPos17 c)
          - ∑ d ∈ ({2, 3, 5} : Finset (Fin 6)), (1 - orbWalkPos d)
              * (orbAtom d ⬝ᵥ orbMultWPos17 c) ^ 2) := by
  rw [show (({2, 3, 5} : Finset (Fin 6)))ᶜ
      = ({0, 1, 4} : Finset (Fin 6)) from by decide]
  rw [sum_tripleFinset_eq (by decide) (by decide) (by decide)]
  simp only [sum_tripleFinset_eq (show (2 : Fin 6) ≠ 3 by decide)
    (show (2 : Fin 6) ≠ 5 by decide) (show (3 : Fin 6) ≠ 5 by decide)]
  norm_num [dotProduct, Fin.sum_univ_three]

theorem orbBudgetBoundWPos18 :
    1 ≤ ∑ c ∈ (({2, 4, 5} : Finset (Fin 6)))ᶜ, orbWalkPos c
        * (2 * (orbAtom c ⬝ᵥ orbMultWPos18 c)
          - ∑ d ∈ ({2, 4, 5} : Finset (Fin 6)), (1 - orbWalkPos d)
              * (orbAtom d ⬝ᵥ orbMultWPos18 c) ^ 2) := by
  rw [show (({2, 4, 5} : Finset (Fin 6)))ᶜ
      = ({0, 1, 3} : Finset (Fin 6)) from by decide]
  rw [sum_tripleFinset_eq (by decide) (by decide) (by decide)]
  simp only [sum_tripleFinset_eq (show (2 : Fin 6) ≠ 4 by decide)
    (show (2 : Fin 6) ≠ 5 by decide) (show (4 : Fin 6) ≠ 5 by decide)]
  norm_num [dotProduct, Fin.sum_univ_three]

theorem orbBudgetBoundWPos19 :
    1 ≤ ∑ c ∈ (({3, 4, 5} : Finset (Fin 6)))ᶜ, orbWalkPos c
        * (2 * (orbAtom c ⬝ᵥ orbMultWPos19 c)
          - ∑ d ∈ ({3, 4, 5} : Finset (Fin 6)), (1 - orbWalkPos d)
              * (orbAtom d ⬝ᵥ orbMultWPos19 c) ^ 2) := by
  rw [show (({3, 4, 5} : Finset (Fin 6)))ᶜ
      = ({0, 1, 2} : Finset (Fin 6)) from by decide]
  rw [sum_tripleFinset_eq (by decide) (by decide) (by decide)]
  simp only [sum_tripleFinset_eq (show (3 : Fin 6) ≠ 4 by decide)
    (show (3 : Fin 6) ≠ 5 by decide) (show (4 : Fin 6) ≠ 5 by decide)]
  norm_num [dotProduct, Fin.sum_univ_three]

theorem orbBudgetBoundWNeg0 :
    1 ≤ ∑ c ∈ (({0, 1, 2} : Finset (Fin 6)))ᶜ, orbWalkNeg c
        * (2 * (orbAtom c ⬝ᵥ orbMultWNeg0 c)
          - ∑ d ∈ ({0, 1, 2} : Finset (Fin 6)), (1 - orbWalkNeg d)
              * (orbAtom d ⬝ᵥ orbMultWNeg0 c) ^ 2) := by
  rw [show (({0, 1, 2} : Finset (Fin 6)))ᶜ
      = ({3, 4, 5} : Finset (Fin 6)) from by decide]
  rw [sum_tripleFinset_eq (by decide) (by decide) (by decide)]
  simp only [sum_tripleFinset_eq (show (0 : Fin 6) ≠ 1 by decide)
    (show (0 : Fin 6) ≠ 2 by decide) (show (1 : Fin 6) ≠ 2 by decide)]
  norm_num [dotProduct, Fin.sum_univ_three]

theorem orbBudgetBoundWNeg1 :
    1 ≤ ∑ c ∈ (({0, 1, 3} : Finset (Fin 6)))ᶜ, orbWalkNeg c
        * (2 * (orbAtom c ⬝ᵥ orbMultWNeg1 c)
          - ∑ d ∈ ({0, 1, 3} : Finset (Fin 6)), (1 - orbWalkNeg d)
              * (orbAtom d ⬝ᵥ orbMultWNeg1 c) ^ 2) := by
  rw [show (({0, 1, 3} : Finset (Fin 6)))ᶜ
      = ({2, 4, 5} : Finset (Fin 6)) from by decide]
  rw [sum_tripleFinset_eq (by decide) (by decide) (by decide)]
  simp only [sum_tripleFinset_eq (show (0 : Fin 6) ≠ 1 by decide)
    (show (0 : Fin 6) ≠ 3 by decide) (show (1 : Fin 6) ≠ 3 by decide)]
  norm_num [dotProduct, Fin.sum_univ_three]

theorem orbBudgetBoundWNeg2 :
    1 ≤ ∑ c ∈ (({0, 1, 4} : Finset (Fin 6)))ᶜ, orbWalkNeg c
        * (2 * (orbAtom c ⬝ᵥ orbMultWNeg2 c)
          - ∑ d ∈ ({0, 1, 4} : Finset (Fin 6)), (1 - orbWalkNeg d)
              * (orbAtom d ⬝ᵥ orbMultWNeg2 c) ^ 2) := by
  rw [show (({0, 1, 4} : Finset (Fin 6)))ᶜ
      = ({2, 3, 5} : Finset (Fin 6)) from by decide]
  rw [sum_tripleFinset_eq (by decide) (by decide) (by decide)]
  simp only [sum_tripleFinset_eq (show (0 : Fin 6) ≠ 1 by decide)
    (show (0 : Fin 6) ≠ 4 by decide) (show (1 : Fin 6) ≠ 4 by decide)]
  norm_num [dotProduct, Fin.sum_univ_three]

theorem orbBudgetBoundWNeg3 :
    1 ≤ ∑ c ∈ (({0, 1, 5} : Finset (Fin 6)))ᶜ, orbWalkNeg c
        * (2 * (orbAtom c ⬝ᵥ orbMultWNeg3 c)
          - ∑ d ∈ ({0, 1, 5} : Finset (Fin 6)), (1 - orbWalkNeg d)
              * (orbAtom d ⬝ᵥ orbMultWNeg3 c) ^ 2) := by
  rw [show (({0, 1, 5} : Finset (Fin 6)))ᶜ
      = ({2, 3, 4} : Finset (Fin 6)) from by decide]
  rw [sum_tripleFinset_eq (by decide) (by decide) (by decide)]
  simp only [sum_tripleFinset_eq (show (0 : Fin 6) ≠ 1 by decide)
    (show (0 : Fin 6) ≠ 5 by decide) (show (1 : Fin 6) ≠ 5 by decide)]
  norm_num [dotProduct, Fin.sum_univ_three]

theorem orbBudgetBoundWNeg4 :
    1 ≤ ∑ c ∈ (({0, 2, 3} : Finset (Fin 6)))ᶜ, orbWalkNeg c
        * (2 * (orbAtom c ⬝ᵥ orbMultWNeg4 c)
          - ∑ d ∈ ({0, 2, 3} : Finset (Fin 6)), (1 - orbWalkNeg d)
              * (orbAtom d ⬝ᵥ orbMultWNeg4 c) ^ 2) := by
  rw [show (({0, 2, 3} : Finset (Fin 6)))ᶜ
      = ({1, 4, 5} : Finset (Fin 6)) from by decide]
  rw [sum_tripleFinset_eq (by decide) (by decide) (by decide)]
  simp only [sum_tripleFinset_eq (show (0 : Fin 6) ≠ 2 by decide)
    (show (0 : Fin 6) ≠ 3 by decide) (show (2 : Fin 6) ≠ 3 by decide)]
  norm_num [dotProduct, Fin.sum_univ_three]

theorem orbBudgetBoundWNeg5 :
    1 ≤ ∑ c ∈ (({0, 2, 4} : Finset (Fin 6)))ᶜ, orbWalkNeg c
        * (2 * (orbAtom c ⬝ᵥ orbMultWNeg5 c)
          - ∑ d ∈ ({0, 2, 4} : Finset (Fin 6)), (1 - orbWalkNeg d)
              * (orbAtom d ⬝ᵥ orbMultWNeg5 c) ^ 2) := by
  rw [show (({0, 2, 4} : Finset (Fin 6)))ᶜ
      = ({1, 3, 5} : Finset (Fin 6)) from by decide]
  rw [sum_tripleFinset_eq (by decide) (by decide) (by decide)]
  simp only [sum_tripleFinset_eq (show (0 : Fin 6) ≠ 2 by decide)
    (show (0 : Fin 6) ≠ 4 by decide) (show (2 : Fin 6) ≠ 4 by decide)]
  norm_num [dotProduct, Fin.sum_univ_three]

theorem orbBudgetBoundWNeg6 :
    1 ≤ ∑ c ∈ (({0, 2, 5} : Finset (Fin 6)))ᶜ, orbWalkNeg c
        * (2 * (orbAtom c ⬝ᵥ orbMultWNeg6 c)
          - ∑ d ∈ ({0, 2, 5} : Finset (Fin 6)), (1 - orbWalkNeg d)
              * (orbAtom d ⬝ᵥ orbMultWNeg6 c) ^ 2) := by
  rw [show (({0, 2, 5} : Finset (Fin 6)))ᶜ
      = ({1, 3, 4} : Finset (Fin 6)) from by decide]
  rw [sum_tripleFinset_eq (by decide) (by decide) (by decide)]
  simp only [sum_tripleFinset_eq (show (0 : Fin 6) ≠ 2 by decide)
    (show (0 : Fin 6) ≠ 5 by decide) (show (2 : Fin 6) ≠ 5 by decide)]
  norm_num [dotProduct, Fin.sum_univ_three]

theorem orbBudgetBoundWNeg7 :
    1 ≤ ∑ c ∈ (({0, 3, 4} : Finset (Fin 6)))ᶜ, orbWalkNeg c
        * (2 * (orbAtom c ⬝ᵥ orbMultWNeg7 c)
          - ∑ d ∈ ({0, 3, 4} : Finset (Fin 6)), (1 - orbWalkNeg d)
              * (orbAtom d ⬝ᵥ orbMultWNeg7 c) ^ 2) := by
  rw [show (({0, 3, 4} : Finset (Fin 6)))ᶜ
      = ({1, 2, 5} : Finset (Fin 6)) from by decide]
  rw [sum_tripleFinset_eq (by decide) (by decide) (by decide)]
  simp only [sum_tripleFinset_eq (show (0 : Fin 6) ≠ 3 by decide)
    (show (0 : Fin 6) ≠ 4 by decide) (show (3 : Fin 6) ≠ 4 by decide)]
  norm_num [dotProduct, Fin.sum_univ_three]

theorem orbBudgetBoundWNeg8 :
    1 ≤ ∑ c ∈ (({0, 3, 5} : Finset (Fin 6)))ᶜ, orbWalkNeg c
        * (2 * (orbAtom c ⬝ᵥ orbMultWNeg8 c)
          - ∑ d ∈ ({0, 3, 5} : Finset (Fin 6)), (1 - orbWalkNeg d)
              * (orbAtom d ⬝ᵥ orbMultWNeg8 c) ^ 2) := by
  rw [show (({0, 3, 5} : Finset (Fin 6)))ᶜ
      = ({1, 2, 4} : Finset (Fin 6)) from by decide]
  rw [sum_tripleFinset_eq (by decide) (by decide) (by decide)]
  simp only [sum_tripleFinset_eq (show (0 : Fin 6) ≠ 3 by decide)
    (show (0 : Fin 6) ≠ 5 by decide) (show (3 : Fin 6) ≠ 5 by decide)]
  norm_num [dotProduct, Fin.sum_univ_three]

theorem orbBudgetBoundWNeg9 :
    1 ≤ ∑ c ∈ (({0, 4, 5} : Finset (Fin 6)))ᶜ, orbWalkNeg c
        * (2 * (orbAtom c ⬝ᵥ orbMultWNeg9 c)
          - ∑ d ∈ ({0, 4, 5} : Finset (Fin 6)), (1 - orbWalkNeg d)
              * (orbAtom d ⬝ᵥ orbMultWNeg9 c) ^ 2) := by
  rw [show (({0, 4, 5} : Finset (Fin 6)))ᶜ
      = ({1, 2, 3} : Finset (Fin 6)) from by decide]
  rw [sum_tripleFinset_eq (by decide) (by decide) (by decide)]
  simp only [sum_tripleFinset_eq (show (0 : Fin 6) ≠ 4 by decide)
    (show (0 : Fin 6) ≠ 5 by decide) (show (4 : Fin 6) ≠ 5 by decide)]
  norm_num [dotProduct, Fin.sum_univ_three]

theorem orbBudgetBoundWNeg10 :
    1 ≤ ∑ c ∈ (({1, 2, 3} : Finset (Fin 6)))ᶜ, orbWalkNeg c
        * (2 * (orbAtom c ⬝ᵥ orbMultWNeg10 c)
          - ∑ d ∈ ({1, 2, 3} : Finset (Fin 6)), (1 - orbWalkNeg d)
              * (orbAtom d ⬝ᵥ orbMultWNeg10 c) ^ 2) := by
  rw [show (({1, 2, 3} : Finset (Fin 6)))ᶜ
      = ({0, 4, 5} : Finset (Fin 6)) from by decide]
  rw [sum_tripleFinset_eq (by decide) (by decide) (by decide)]
  simp only [sum_tripleFinset_eq (show (1 : Fin 6) ≠ 2 by decide)
    (show (1 : Fin 6) ≠ 3 by decide) (show (2 : Fin 6) ≠ 3 by decide)]
  norm_num [dotProduct, Fin.sum_univ_three]

theorem orbBudgetBoundWNeg11 :
    1 ≤ ∑ c ∈ (({1, 2, 4} : Finset (Fin 6)))ᶜ, orbWalkNeg c
        * (2 * (orbAtom c ⬝ᵥ orbMultWNeg11 c)
          - ∑ d ∈ ({1, 2, 4} : Finset (Fin 6)), (1 - orbWalkNeg d)
              * (orbAtom d ⬝ᵥ orbMultWNeg11 c) ^ 2) := by
  rw [show (({1, 2, 4} : Finset (Fin 6)))ᶜ
      = ({0, 3, 5} : Finset (Fin 6)) from by decide]
  rw [sum_tripleFinset_eq (by decide) (by decide) (by decide)]
  simp only [sum_tripleFinset_eq (show (1 : Fin 6) ≠ 2 by decide)
    (show (1 : Fin 6) ≠ 4 by decide) (show (2 : Fin 6) ≠ 4 by decide)]
  norm_num [dotProduct, Fin.sum_univ_three]

theorem orbBudgetBoundWNeg12 :
    1 ≤ ∑ c ∈ (({1, 2, 5} : Finset (Fin 6)))ᶜ, orbWalkNeg c
        * (2 * (orbAtom c ⬝ᵥ orbMultWNeg12 c)
          - ∑ d ∈ ({1, 2, 5} : Finset (Fin 6)), (1 - orbWalkNeg d)
              * (orbAtom d ⬝ᵥ orbMultWNeg12 c) ^ 2) := by
  rw [show (({1, 2, 5} : Finset (Fin 6)))ᶜ
      = ({0, 3, 4} : Finset (Fin 6)) from by decide]
  rw [sum_tripleFinset_eq (by decide) (by decide) (by decide)]
  simp only [sum_tripleFinset_eq (show (1 : Fin 6) ≠ 2 by decide)
    (show (1 : Fin 6) ≠ 5 by decide) (show (2 : Fin 6) ≠ 5 by decide)]
  norm_num [dotProduct, Fin.sum_univ_three]

theorem orbBudgetBoundWNeg13 :
    1 ≤ ∑ c ∈ (({1, 3, 4} : Finset (Fin 6)))ᶜ, orbWalkNeg c
        * (2 * (orbAtom c ⬝ᵥ orbMultWNeg13 c)
          - ∑ d ∈ ({1, 3, 4} : Finset (Fin 6)), (1 - orbWalkNeg d)
              * (orbAtom d ⬝ᵥ orbMultWNeg13 c) ^ 2) := by
  rw [show (({1, 3, 4} : Finset (Fin 6)))ᶜ
      = ({0, 2, 5} : Finset (Fin 6)) from by decide]
  rw [sum_tripleFinset_eq (by decide) (by decide) (by decide)]
  simp only [sum_tripleFinset_eq (show (1 : Fin 6) ≠ 3 by decide)
    (show (1 : Fin 6) ≠ 4 by decide) (show (3 : Fin 6) ≠ 4 by decide)]
  norm_num [dotProduct, Fin.sum_univ_three]

theorem orbBudgetBoundWNeg14 :
    1 ≤ ∑ c ∈ (({1, 3, 5} : Finset (Fin 6)))ᶜ, orbWalkNeg c
        * (2 * (orbAtom c ⬝ᵥ orbMultWNeg14 c)
          - ∑ d ∈ ({1, 3, 5} : Finset (Fin 6)), (1 - orbWalkNeg d)
              * (orbAtom d ⬝ᵥ orbMultWNeg14 c) ^ 2) := by
  rw [show (({1, 3, 5} : Finset (Fin 6)))ᶜ
      = ({0, 2, 4} : Finset (Fin 6)) from by decide]
  rw [sum_tripleFinset_eq (by decide) (by decide) (by decide)]
  simp only [sum_tripleFinset_eq (show (1 : Fin 6) ≠ 3 by decide)
    (show (1 : Fin 6) ≠ 5 by decide) (show (3 : Fin 6) ≠ 5 by decide)]
  norm_num [dotProduct, Fin.sum_univ_three]

theorem orbBudgetBoundWNeg15 :
    1 ≤ ∑ c ∈ (({1, 4, 5} : Finset (Fin 6)))ᶜ, orbWalkNeg c
        * (2 * (orbAtom c ⬝ᵥ orbMultWNeg15 c)
          - ∑ d ∈ ({1, 4, 5} : Finset (Fin 6)), (1 - orbWalkNeg d)
              * (orbAtom d ⬝ᵥ orbMultWNeg15 c) ^ 2) := by
  rw [show (({1, 4, 5} : Finset (Fin 6)))ᶜ
      = ({0, 2, 3} : Finset (Fin 6)) from by decide]
  rw [sum_tripleFinset_eq (by decide) (by decide) (by decide)]
  simp only [sum_tripleFinset_eq (show (1 : Fin 6) ≠ 4 by decide)
    (show (1 : Fin 6) ≠ 5 by decide) (show (4 : Fin 6) ≠ 5 by decide)]
  norm_num [dotProduct, Fin.sum_univ_three]

theorem orbBudgetBoundWNeg16 :
    1 ≤ ∑ c ∈ (({2, 3, 4} : Finset (Fin 6)))ᶜ, orbWalkNeg c
        * (2 * (orbAtom c ⬝ᵥ orbMultWNeg16 c)
          - ∑ d ∈ ({2, 3, 4} : Finset (Fin 6)), (1 - orbWalkNeg d)
              * (orbAtom d ⬝ᵥ orbMultWNeg16 c) ^ 2) := by
  rw [show (({2, 3, 4} : Finset (Fin 6)))ᶜ
      = ({0, 1, 5} : Finset (Fin 6)) from by decide]
  rw [sum_tripleFinset_eq (by decide) (by decide) (by decide)]
  simp only [sum_tripleFinset_eq (show (2 : Fin 6) ≠ 3 by decide)
    (show (2 : Fin 6) ≠ 4 by decide) (show (3 : Fin 6) ≠ 4 by decide)]
  norm_num [dotProduct, Fin.sum_univ_three]

theorem orbBudgetBoundWNeg17 :
    1 ≤ ∑ c ∈ (({2, 3, 5} : Finset (Fin 6)))ᶜ, orbWalkNeg c
        * (2 * (orbAtom c ⬝ᵥ orbMultWNeg17 c)
          - ∑ d ∈ ({2, 3, 5} : Finset (Fin 6)), (1 - orbWalkNeg d)
              * (orbAtom d ⬝ᵥ orbMultWNeg17 c) ^ 2) := by
  rw [show (({2, 3, 5} : Finset (Fin 6)))ᶜ
      = ({0, 1, 4} : Finset (Fin 6)) from by decide]
  rw [sum_tripleFinset_eq (by decide) (by decide) (by decide)]
  simp only [sum_tripleFinset_eq (show (2 : Fin 6) ≠ 3 by decide)
    (show (2 : Fin 6) ≠ 5 by decide) (show (3 : Fin 6) ≠ 5 by decide)]
  norm_num [dotProduct, Fin.sum_univ_three]

theorem orbBudgetBoundWNeg18 :
    1 ≤ ∑ c ∈ (({2, 4, 5} : Finset (Fin 6)))ᶜ, orbWalkNeg c
        * (2 * (orbAtom c ⬝ᵥ orbMultWNeg18 c)
          - ∑ d ∈ ({2, 4, 5} : Finset (Fin 6)), (1 - orbWalkNeg d)
              * (orbAtom d ⬝ᵥ orbMultWNeg18 c) ^ 2) := by
  rw [show (({2, 4, 5} : Finset (Fin 6)))ᶜ
      = ({0, 1, 3} : Finset (Fin 6)) from by decide]
  rw [sum_tripleFinset_eq (by decide) (by decide) (by decide)]
  simp only [sum_tripleFinset_eq (show (2 : Fin 6) ≠ 4 by decide)
    (show (2 : Fin 6) ≠ 5 by decide) (show (4 : Fin 6) ≠ 5 by decide)]
  norm_num [dotProduct, Fin.sum_univ_three]

theorem orbBudgetBoundWNeg19 :
    1 ≤ ∑ c ∈ (({3, 4, 5} : Finset (Fin 6)))ᶜ, orbWalkNeg c
        * (2 * (orbAtom c ⬝ᵥ orbMultWNeg19 c)
          - ∑ d ∈ ({3, 4, 5} : Finset (Fin 6)), (1 - orbWalkNeg d)
              * (orbAtom d ⬝ᵥ orbMultWNeg19 c) ^ 2) := by
  rw [show (({3, 4, 5} : Finset (Fin 6)))ᶜ
      = ({0, 1, 2} : Finset (Fin 6)) from by decide]
  rw [sum_tripleFinset_eq (by decide) (by decide) (by decide)]
  simp only [sum_tripleFinset_eq (show (3 : Fin 6) ≠ 4 by decide)
    (show (3 : Fin 6) ≠ 5 by decide) (show (4 : Fin 6) ≠ 5 by decide)]
  norm_num [dotProduct, Fin.sum_univ_three]

theorem triple_cases : ∀ s : Finset (Fin 6), s.card = 3 →
    s = {0, 1, 2} ∨ s = {0, 1, 3} ∨ s = {0, 1, 4} ∨ s = {0, 1, 5} ∨ s = {0, 2, 3} ∨ s = {0, 2, 4} ∨ s = {0, 2, 5} ∨ s = {0, 3, 4} ∨ s = {0, 3, 5} ∨ s = {0, 4, 5} ∨ s = {1, 2, 3} ∨ s = {1, 2, 4} ∨ s = {1, 2, 5} ∨ s = {1, 3, 4} ∨ s = {1, 3, 5} ∨ s = {1, 4, 5} ∨ s = {2, 3, 4} ∨ s = {2, 3, 5} ∨ s = {2, 4, 5} ∨ s = {3, 4, 5} := by
  decide

/-! ## The refutation -/

/-- **THE ORBIT-UNION FALLBACK IS FALSE.**  Neither pure triple dominates the
witness even though the budget fails at all twenty triples at the interior
point and at both exact walk endpoints, and no mass gap fires anywhere. -/
theorem pureTripleOrbitSelection_refuted :
    ¬ PureTripleOrbitSelectionSixThree := by
  intro hconjecture
  have hstations : ∀ station : Fin 6 → ℝ,
      station = orbWeight ∨ station = orbWalkPos ∨ station = orbWalkNeg →
      ¬ RawStressMassGap station orbStress
      ∧ ¬ RawStressMassGap station (-orbStress)
      ∧ ∀ triple : Finset (Fin 6), triple.card = 3 →
          ¬ RawFreeMassBudget orbAtom station triple := by
    intro station hstation
    rcases hstation with rfl | rfl | rfl
    · refine ⟨?_, ?_, ?_⟩
      · refine not_rawStressMassGap_of_crossing 1 4
          (by norm_num) (by norm_num) ?_
        norm_num
      · refine not_rawStressMassGap_of_crossing 5 2
          (by norm_num) (by norm_num) ?_
        norm_num
      · intro triple hcard
        rcases triple_cases triple hcard with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact not_rawFreeMassBudget_of_bound orbAtom orbWeight
            (fun c => (orbWeight_pos c).le) _
            orbMultInt0 orbBudgetBoundInt0
        · exact not_rawFreeMassBudget_of_bound orbAtom orbWeight
            (fun c => (orbWeight_pos c).le) _
            orbMultInt1 orbBudgetBoundInt1
        · exact not_rawFreeMassBudget_of_bound orbAtom orbWeight
            (fun c => (orbWeight_pos c).le) _
            orbMultInt2 orbBudgetBoundInt2
        · exact not_rawFreeMassBudget_of_bound orbAtom orbWeight
            (fun c => (orbWeight_pos c).le) _
            orbMultInt3 orbBudgetBoundInt3
        · exact not_rawFreeMassBudget_of_bound orbAtom orbWeight
            (fun c => (orbWeight_pos c).le) _
            orbMultInt4 orbBudgetBoundInt4
        · exact not_rawFreeMassBudget_of_bound orbAtom orbWeight
            (fun c => (orbWeight_pos c).le) _
            orbMultInt5 orbBudgetBoundInt5
        · exact not_rawFreeMassBudget_of_bound orbAtom orbWeight
            (fun c => (orbWeight_pos c).le) _
            orbMultInt6 orbBudgetBoundInt6
        · exact not_rawFreeMassBudget_of_bound orbAtom orbWeight
            (fun c => (orbWeight_pos c).le) _
            orbMultInt7 orbBudgetBoundInt7
        · exact not_rawFreeMassBudget_of_bound orbAtom orbWeight
            (fun c => (orbWeight_pos c).le) _
            orbMultInt8 orbBudgetBoundInt8
        · exact not_rawFreeMassBudget_of_bound orbAtom orbWeight
            (fun c => (orbWeight_pos c).le) _
            orbMultInt9 orbBudgetBoundInt9
        · exact not_rawFreeMassBudget_of_bound orbAtom orbWeight
            (fun c => (orbWeight_pos c).le) _
            orbMultInt10 orbBudgetBoundInt10
        · exact not_rawFreeMassBudget_of_bound orbAtom orbWeight
            (fun c => (orbWeight_pos c).le) _
            orbMultInt11 orbBudgetBoundInt11
        · exact not_rawFreeMassBudget_of_bound orbAtom orbWeight
            (fun c => (orbWeight_pos c).le) _
            orbMultInt12 orbBudgetBoundInt12
        · exact not_rawFreeMassBudget_of_bound orbAtom orbWeight
            (fun c => (orbWeight_pos c).le) _
            orbMultInt13 orbBudgetBoundInt13
        · exact not_rawFreeMassBudget_of_bound orbAtom orbWeight
            (fun c => (orbWeight_pos c).le) _
            orbMultInt14 orbBudgetBoundInt14
        · exact not_rawFreeMassBudget_of_bound orbAtom orbWeight
            (fun c => (orbWeight_pos c).le) _
            orbMultInt15 orbBudgetBoundInt15
        · exact not_rawFreeMassBudget_of_bound orbAtom orbWeight
            (fun c => (orbWeight_pos c).le) _
            orbMultInt16 orbBudgetBoundInt16
        · exact not_rawFreeMassBudget_of_bound orbAtom orbWeight
            (fun c => (orbWeight_pos c).le) _
            orbMultInt17 orbBudgetBoundInt17
        · exact not_rawFreeMassBudget_of_bound orbAtom orbWeight
            (fun c => (orbWeight_pos c).le) _
            orbMultInt18 orbBudgetBoundInt18
        · exact not_rawFreeMassBudget_of_bound orbAtom orbWeight
            (fun c => (orbWeight_pos c).le) _
            orbMultInt19 orbBudgetBoundInt19
    · refine ⟨?_, ?_, ?_⟩
      · refine not_rawStressMassGap_of_crossing 1 4
          (by norm_num) (by norm_num) ?_
        norm_num
      · refine not_rawStressMassGap_of_crossing 5 2
          (by norm_num) (by norm_num) ?_
        norm_num
      · intro triple hcard
        rcases triple_cases triple hcard with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact not_rawFreeMassBudget_of_bound orbAtom orbWalkPos
            orbWalkPos_nonneg _
            orbMultWPos0 orbBudgetBoundWPos0
        · exact not_rawFreeMassBudget_of_bound orbAtom orbWalkPos
            orbWalkPos_nonneg _
            orbMultWPos1 orbBudgetBoundWPos1
        · exact not_rawFreeMassBudget_of_bound orbAtom orbWalkPos
            orbWalkPos_nonneg _
            orbMultWPos2 orbBudgetBoundWPos2
        · exact not_rawFreeMassBudget_of_bound orbAtom orbWalkPos
            orbWalkPos_nonneg _
            orbMultWPos3 orbBudgetBoundWPos3
        · exact not_rawFreeMassBudget_of_bound orbAtom orbWalkPos
            orbWalkPos_nonneg _
            orbMultWPos4 orbBudgetBoundWPos4
        · exact not_rawFreeMassBudget_of_bound orbAtom orbWalkPos
            orbWalkPos_nonneg _
            orbMultWPos5 orbBudgetBoundWPos5
        · exact not_rawFreeMassBudget_of_bound orbAtom orbWalkPos
            orbWalkPos_nonneg _
            orbMultWPos6 orbBudgetBoundWPos6
        · exact not_rawFreeMassBudget_of_bound orbAtom orbWalkPos
            orbWalkPos_nonneg _
            orbMultWPos7 orbBudgetBoundWPos7
        · exact not_rawFreeMassBudget_of_bound orbAtom orbWalkPos
            orbWalkPos_nonneg _
            orbMultWPos8 orbBudgetBoundWPos8
        · exact not_rawFreeMassBudget_of_bound orbAtom orbWalkPos
            orbWalkPos_nonneg _
            orbMultWPos9 orbBudgetBoundWPos9
        · exact not_rawFreeMassBudget_of_bound orbAtom orbWalkPos
            orbWalkPos_nonneg _
            orbMultWPos10 orbBudgetBoundWPos10
        · exact not_rawFreeMassBudget_of_bound orbAtom orbWalkPos
            orbWalkPos_nonneg _
            orbMultWPos11 orbBudgetBoundWPos11
        · exact not_rawFreeMassBudget_of_bound orbAtom orbWalkPos
            orbWalkPos_nonneg _
            orbMultWPos12 orbBudgetBoundWPos12
        · exact not_rawFreeMassBudget_of_bound orbAtom orbWalkPos
            orbWalkPos_nonneg _
            orbMultWPos13 orbBudgetBoundWPos13
        · exact not_rawFreeMassBudget_of_bound orbAtom orbWalkPos
            orbWalkPos_nonneg _
            orbMultWPos14 orbBudgetBoundWPos14
        · exact not_rawFreeMassBudget_of_bound orbAtom orbWalkPos
            orbWalkPos_nonneg _
            orbMultWPos15 orbBudgetBoundWPos15
        · exact not_rawFreeMassBudget_of_bound orbAtom orbWalkPos
            orbWalkPos_nonneg _
            orbMultWPos16 orbBudgetBoundWPos16
        · exact not_rawFreeMassBudget_of_bound orbAtom orbWalkPos
            orbWalkPos_nonneg _
            orbMultWPos17 orbBudgetBoundWPos17
        · exact not_rawFreeMassBudget_of_bound orbAtom orbWalkPos
            orbWalkPos_nonneg _
            orbMultWPos18 orbBudgetBoundWPos18
        · exact not_rawFreeMassBudget_of_bound orbAtom orbWalkPos
            orbWalkPos_nonneg _
            orbMultWPos19 orbBudgetBoundWPos19
    · refine ⟨?_, ?_, ?_⟩
      · refine not_rawStressMassGap_of_crossing 1 4
          (by norm_num) (by norm_num) ?_
        norm_num
      · refine not_rawStressMassGap_of_crossing 5 2
          (by norm_num) (by norm_num) ?_
        norm_num
      · intro triple hcard
        rcases triple_cases triple hcard with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact not_rawFreeMassBudget_of_bound orbAtom orbWalkNeg
            orbWalkNeg_nonneg _
            orbMultWNeg0 orbBudgetBoundWNeg0
        · exact not_rawFreeMassBudget_of_bound orbAtom orbWalkNeg
            orbWalkNeg_nonneg _
            orbMultWNeg1 orbBudgetBoundWNeg1
        · exact not_rawFreeMassBudget_of_bound orbAtom orbWalkNeg
            orbWalkNeg_nonneg _
            orbMultWNeg2 orbBudgetBoundWNeg2
        · exact not_rawFreeMassBudget_of_bound orbAtom orbWalkNeg
            orbWalkNeg_nonneg _
            orbMultWNeg3 orbBudgetBoundWNeg3
        · exact not_rawFreeMassBudget_of_bound orbAtom orbWalkNeg
            orbWalkNeg_nonneg _
            orbMultWNeg4 orbBudgetBoundWNeg4
        · exact not_rawFreeMassBudget_of_bound orbAtom orbWalkNeg
            orbWalkNeg_nonneg _
            orbMultWNeg5 orbBudgetBoundWNeg5
        · exact not_rawFreeMassBudget_of_bound orbAtom orbWalkNeg
            orbWalkNeg_nonneg _
            orbMultWNeg6 orbBudgetBoundWNeg6
        · exact not_rawFreeMassBudget_of_bound orbAtom orbWalkNeg
            orbWalkNeg_nonneg _
            orbMultWNeg7 orbBudgetBoundWNeg7
        · exact not_rawFreeMassBudget_of_bound orbAtom orbWalkNeg
            orbWalkNeg_nonneg _
            orbMultWNeg8 orbBudgetBoundWNeg8
        · exact not_rawFreeMassBudget_of_bound orbAtom orbWalkNeg
            orbWalkNeg_nonneg _
            orbMultWNeg9 orbBudgetBoundWNeg9
        · exact not_rawFreeMassBudget_of_bound orbAtom orbWalkNeg
            orbWalkNeg_nonneg _
            orbMultWNeg10 orbBudgetBoundWNeg10
        · exact not_rawFreeMassBudget_of_bound orbAtom orbWalkNeg
            orbWalkNeg_nonneg _
            orbMultWNeg11 orbBudgetBoundWNeg11
        · exact not_rawFreeMassBudget_of_bound orbAtom orbWalkNeg
            orbWalkNeg_nonneg _
            orbMultWNeg12 orbBudgetBoundWNeg12
        · exact not_rawFreeMassBudget_of_bound orbAtom orbWalkNeg
            orbWalkNeg_nonneg _
            orbMultWNeg13 orbBudgetBoundWNeg13
        · exact not_rawFreeMassBudget_of_bound orbAtom orbWalkNeg
            orbWalkNeg_nonneg _
            orbMultWNeg14 orbBudgetBoundWNeg14
        · exact not_rawFreeMassBudget_of_bound orbAtom orbWalkNeg
            orbWalkNeg_nonneg _
            orbMultWNeg15 orbBudgetBoundWNeg15
        · exact not_rawFreeMassBudget_of_bound orbAtom orbWalkNeg
            orbWalkNeg_nonneg _
            orbMultWNeg16 orbBudgetBoundWNeg16
        · exact not_rawFreeMassBudget_of_bound orbAtom orbWalkNeg
            orbWalkNeg_nonneg _
            orbMultWNeg17 orbBudgetBoundWNeg17
        · exact not_rawFreeMassBudget_of_bound orbAtom orbWalkNeg
            orbWalkNeg_nonneg _
            orbMultWNeg18 orbBudgetBoundWNeg18
        · exact not_rawFreeMassBudget_of_bound orbAtom orbWalkNeg
            orbWalkNeg_nonneg _
            orbMultWNeg19 orbBudgetBoundWNeg19
  rcases hconjecture orbAtom orbWeight orbStress orbWalkPos orbWalkNeg
      (64/17161 : ℝ) (257436940512636031388623573144576000/266967897115158419241951304186321975977 : ℝ)
      orbWeight_pos orbWeight_sum orbStress_full orbStress_zeroSum orbStress_kills
      orbStress_posSide orbStress_negSide orbAtom_diagonal
      orbPos_resolution orbNeg_resolution orbPrimitive
      orbStepPos_nonneg orbStepNeg_nonneg orbWalkPos_eq orbWalkNeg_eq
      orbWalkPos_nonneg orbWalkNeg_nonneg orbWalkPos_vanish orbWalkNeg_vanish
      hstations with hposSide | hnegSide
  · exact raw_gap_not_posDef_of_witnessVec orbAtom orbWeight _ orbWitnessPos
      orbWitnessPos_ne orbPosGap_value hposSide
  · exact raw_gap_not_posDef_of_witnessVec orbAtom orbWeight _ orbWitnessNeg
      orbWitnessNeg_ne orbNegGap_value hnegSide

end OrbitPureTripleRefutation
end Gtz
