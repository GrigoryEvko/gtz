/-
# The (7,3) middle band: fence, sandwich, five-set floors, and the sigma gate

Frontier lane B of the July 2026 workflow.  The battlefield after the two
gates is `m ∈ (1/9, 4/9)`, where `m` is the best triple's worst edge weight
(`max` over the 35 triples of the `min` edge).  This module lands the exact
bookkeeping layer every middle-band argument stands on, the (7,3)
starve-feed sandwich, the five-set coherent floors, and one genuinely new
per-triple domination gate — all on the uniform-share stratum
`atomShare ≡ 3/7` of `Gtz.WeightedDesign 7 3`, with the leverage-3
hypothesis added exactly where `Gtz.Dominates` is touched.

Everything is stated in the landed scalars `Gtz.directionTripleSigma`
(`σ_T`), `Gtz.directionTripleProduct` (`P_T`),
`Gtz.orientedTripleResidual` (`r_T = σ_T − 3 P_T`), `Gtz.edgeWeight`
(`w = γ²`), and `Gtz.slackDeterminantThree` at the criterion slack `2/3`
(`Δ_T = 8/27 − (2/3) σ_T + 2 P_T = 8/27 − (2/3) r_T`).  On the stratum a
triple of distinct atoms dominates exactly when `r_T ≤ 4/9`
(equivalently `Δ_T ≥ 0`); a *failing configuration* is one where no triple
dominates, carried as the hypothesis `hfail` below.

## The layer landed here

* **Task 1, the fence.**  Per-pair completion identities: over the five
  completions of a pair, `Σ σ = 3w + 8/3`, `Σ P = w/3` (the positive
  supply, C-P1), `Σ r = 2w + 8/3`, and `Σ Δ = −8/27 − (4/3) w` (C-PAIR).
  The honest vacuity record: the per-pair mean `(2w + 8/3)/5` exceeds the
  criterion `4/9` for EVERY `w ≥ 0`, so the pair aggregate can never
  certify a dominating completion by averaging.  Global ordered forms:
  `Σ over the 210 ordered distinct triples of r = 392/3` (the unordered
  35-triple total is one sixth of it, `196/9`), and the mean pigeonhole
  `∃ T, r_T ≤ 28/45` — again strictly above `4/9`, as P2 predicted.

* **Task 2, the sandwich.**  On a failing configuration every triple obeys
  the residual window
  `4/9 < r_T < 8/9 + 2 min(w_ab, w_ac, w_bc)`
  (stated with all three edges); the upper half is the starve-feed bound:
  a hub above the threshold `8/9 + 2 w_ab` would feed a nonnegative clause
  to one of the four sibling completions of `{a,b}`.  The gate itself is
  landed clause-free: on the stratum a starved hub produces an actual
  dominating completion (`exists_dominates_completion_of_starvedHub_...`),
  with no pairwise-clause side conditions — the cap criterion absorbs
  them.  In `Δ`-coordinates the window reads
  `−8/27 − (4/3) w_min < Δ_T < 0`, the (7,3) analogue of the (6,3)
  residual window.

* **Task 3, five-set floors.**  For every pair `{e,f}` the ordered sum of
  `P` over the complementary five-set is exactly `4/9 + 2 w_ef` (C-5SET,
  strictly positive), so some triple avoiding the pair carries
  `P ≥ 1/135 + w_ef/30`; on a failing configuration that coherent carrier
  further satisfies `σ > 7/15 + w_ef/10`.

* **The sigma gate (new).**  `σ_T ≤ 1/3` forces domination of `T` itself —
  one inequality, subsuming the all-edges-`≤ 1/9` light gate.  Engine: the
  landed AM-GM `27 P² ≤ σ³` plus the exact factorisation
  `27 σ³ − 81 σ² + 72 σ − 16 = (3σ − 1)(3σ − 4)²` (the σ-form of the
  campaign's endpoint cubic `ρ(m) = 9(m − 1/9)(m − 4/9)²`, via `σ = 3m`).
  Contrapositive: every triple of a failing configuration has
  `σ_T > 1/3`.  Sharp: the basis+tetrapod witness's tetrapod triple ties
  at exactly `σ = 1/3`.

* **Task 4, the sevenths/4-set view.**  What the frozen block spectra give
  at trace level, landed exactly: the doubled pair mass of the complement
  4-set of a triple is `4/3 + 2 σ_T` (row law only), so the sigma gate
  reads: a triple dominates as soon as its complementary four atoms carry
  doubled pair mass `≤ 2`, and on a failing configuration EVERY 4-set is
  hot (doubled mass `> 2`, i.e. mass `> 1`).  This is the honest yield of
  the `λmax(M[F]) > 1` reading: the eigenvalue route (kernel vector of the
  singular `Γ[F]` plus a Rayleigh test vector, Frobenius bound
  `tr M[F]² > 2`) produces the SAME constant `σ > 1/3`, so the module
  lands the scalar route and records the spectral reading here.  Beyond
  trace level the 5/6-block freezes yield only the mass laws
  `2 + w_ef` and `10/3`, which are row-law consequences — nothing extra.

* **Band brackets.**  Unconditionally on the stratum no triple has all
  edges `> 4/9` (coherent-cap freeze), and any triple with all edges
  `≥ μ > 1/4` is coherent (`P > 0`; frustrated triples live at
  `w_min ≤ 1/4`, by `(1 − 3μ)² − 4μ³ = (1 − μ)²(1 − 4μ)`).  On a failing
  configuration every triple has an edge `< 4/9`, and — by the
  Ramsey `R(3,3) ≤ 6` pigeonhole on seven atoms — some triple has ALL
  edges `> 1/9`.  So a failing configuration has `m ∈ (1/9, 4/9)`
  exactly: both gate endpoints are kernel facts.

## THE HONEST LEDGER (task 5)

No sub-band of `(1/9, 4/9)` is closed outright by this module.  What is
proved about a hypothetical failing configuration at uniform share 3/7 and
leverage 3:

* `m ∈ (1/9, 4/9)` strictly (heavy triangle exists; every min-edge `< 4/9`);
* every triple: `σ > 1/3`, `4/9 < σ − 3P < 8/9 + 2 w_min(T)`, `P < 8/27`;
* every coherent triple: `σ > 4/9 + 3P`;
* every triple with all edges above `1/4` is coherent;
* every pair: its five completions carry `P`-mass `w/3 > 0` and
  `r`-mass `2w + 8/3`; no hub reaches the starvation threshold
  `8/9 + 2w`;
* every five-set: a coherent triple with `P ≥ 1/135 + w_ef/30` and
  `σ > 7/15 + w_ef/10`;
* every four-set: doubled pair mass `> 2`.

The reason no interior sub-band falls to this layer: the per-triple scalar
system (fence + caps + window) admits failing-shaped solutions throughout
the band — e.g. lopsided coherent data `w ≈ (1/2, 1/100, 1/100)` passes
every listed inequality — so interior closures need cross-triple
realizability (the chart structure `Γ² = (7/3)Γ` beyond its row/supply/cap
shadows), which is exactly the open content of R3.  The residual after
this module is the full open band `m ∈ (1/9, 4/9)`, now fenced by the
list above.

Numerically pre-verified in exact arithmetic (474 checks: sympy rationals
on the basis+tetrapod witness, symbolic ring identities, 40-digit lifted
heptagon), scripts under the workflow scratchpad.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Design.FrameConservation
import Gtz.LinAlg.PsdKit
import Gtz.LinAlg.ProjectionForm
import Gtz.Quantitative.WeightProductFloor
import Gtz.Quantitative.MirrorLaw
import Gtz.Quantitative.MinorSumIdentities
import Gtz.Quantitative.HollowInvolution
import Gtz.Quantitative.TripleCubicCriterion
import Gtz.Quantitative.GTransformGate
import Gtz.Quantitative.WeightedTripleCriterion

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace Gtz

open Matrix

variable {m k : ℕ}

/-! ## 0. Private stratum plumbing

Local re-derivations from the landed generic laws, kept `private` because
sibling modules of this workflow land public versions under their own
names; the integrator deduplicates.  Everything below `## 1` is public and
new. -/

/-- A share of `3/7` forces a positive leverage. -/
private theorem bandLeveragePos (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7) (atomIndex : Fin 7) :
    0 < leverageOf (D.atom atomIndex) :=
  leverageOf_pos_of_atomShare_pos D (by rw [huniform atomIndex]; norm_num)

/-- The direction Gram is symmetric. -/
private theorem bandGramSymm (D : WeightedDesign m k) :
    (directionGramMatrix D)ᵀ = directionGramMatrix D := by
  ext rowIndex colIndex
  exact directionGram_comm D colIndex rowIndex

/-- The row law at the (7,3) stratum: every vertex sum of edge weights is `4/3`. -/
private theorem bandRowLaw (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7) (atomIndex : Fin 7) :
    ∑ otherIndex ∈ Finset.univ.erase atomIndex, edgeWeight D atomIndex otherIndex = 4 / 3 := by
  rw [sum_erase_edgeWeight_eq_of_atomShare_eq D huniform (bandLeveragePos D huniform atomIndex)]
  norm_num

/-- The supply chain at the (7,3) stratum:
`Σ_{c ∉ {a,b}} γ_ac γ_cb = (1/3) γ_ab` — POSITIVE supply, where (6,3) has zero. -/
private theorem bandSupply (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7)
    {firstIndex secondIndex : Fin 7} (hdistinct : firstIndex ≠ secondIndex) :
    ∑ otherIndex ∈ Finset.univ \ ({firstIndex, secondIndex} : Finset (Fin 7)),
        directionGram D firstIndex otherIndex * directionGram D otherIndex secondIndex
      = 1 / 3 * directionGram D firstIndex secondIndex := by
  have hweighted := sum_sdiff_atomShare_mul_directionGram_mul_directionGram D hdistinct
    (bandLeveragePos D huniform firstIndex) (bandLeveragePos D huniform secondIndex)
  rw [Finset.sum_congr rfl fun otherIndex _ => by rw [huniform otherIndex],
    ← Finset.mul_sum, huniform firstIndex, huniform secondIndex] at hweighted
  linarith [hweighted]

/-- Row law with an arbitrary dropped set: summing the edge weights at `a` over
everything outside `insert a dropped` costs exactly the dropped weights. -/
private theorem bandRowDrop (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7) (atomIndex : Fin 7)
    (dropped : Finset (Fin 7)) (hnotMem : atomIndex ∉ dropped) :
    ∑ otherIndex ∈ Finset.univ \ insert atomIndex dropped, edgeWeight D atomIndex otherIndex
      = 4 / 3 - ∑ otherIndex ∈ dropped, edgeWeight D atomIndex otherIndex := by
  have hset : Finset.univ \ insert atomIndex dropped
      = (Finset.univ.erase atomIndex) \ dropped := by
    ext member
    simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert, Finset.mem_erase, true_and]
    tauto
  have hsubset : dropped ⊆ Finset.univ.erase atomIndex := by
    intro member hmember
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    intro hcontra
    exact hnotMem (hcontra ▸ hmember)
  rw [hset, Finset.sum_sdiff_eq_sub hsubset, bandRowLaw D huniform atomIndex]

/-- Supply chain with an arbitrary dropped set. -/
private theorem bandSupplyDrop (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7)
    {firstIndex secondIndex : Fin 7} (hdistinct : firstIndex ≠ secondIndex)
    (dropped : Finset (Fin 7)) (hfirstNot : firstIndex ∉ dropped)
    (hsecondNot : secondIndex ∉ dropped) :
    ∑ otherIndex ∈ Finset.univ \ insert firstIndex (insert secondIndex dropped),
        directionGram D firstIndex otherIndex * directionGram D otherIndex secondIndex
      = 1 / 3 * directionGram D firstIndex secondIndex
        - ∑ otherIndex ∈ dropped,
            directionGram D firstIndex otherIndex * directionGram D otherIndex secondIndex := by
  have hset : Finset.univ \ insert firstIndex (insert secondIndex dropped)
      = (Finset.univ \ ({firstIndex, secondIndex} : Finset (Fin 7))) \ dropped := by
    ext member
    simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton,
      true_and]
    tauto
  have hsubset : dropped ⊆ Finset.univ \ ({firstIndex, secondIndex} : Finset (Fin 7)) := by
    intro member hmember
    simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton,
      true_and, not_or]
    exact ⟨fun hcontra => hfirstNot (hcontra ▸ hmember),
      fun hcontra => hsecondNot (hcontra ▸ hmember)⟩
  rw [hset, Finset.sum_sdiff_eq_sub hsubset, bandSupply D huniform hdistinct]

/-- The one-line cap: `(7/3)·1 − Γ ⪰ 0` from the landed square law
`Γ² = (7/3)Γ`, because the gap is `3/7` of its own square. -/
private theorem bandCapPsd (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7) :
    ((7 / 3 : ℝ) • (1 : Matrix (Fin 7) (Fin 7) ℝ) - directionGramMatrix D).PosSemidef := by
  have hsq := directionGramMatrix_sq_of_uniformShare D huniform (by norm_num : (0 : ℝ) < 3 / 7)
  rw [show ((3 : ℝ) / 7)⁻¹ = 7 / 3 by norm_num] at hsq
  have hconj : ((7 / 3 : ℝ) • (1 : Matrix (Fin 7) (Fin 7) ℝ) - directionGramMatrix D)ᴴ
      = (7 / 3 : ℝ) • (1 : Matrix (Fin 7) (Fin 7) ℝ) - directionGramMatrix D := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
      star_trivial, isHermitian_of_transpose_eq (bandGramSymm D)]
  have hsquare : ((7 / 3 : ℝ) • (1 : Matrix (Fin 7) (Fin 7) ℝ) - directionGramMatrix D)
      * ((7 / 3 : ℝ) • (1 : Matrix (Fin 7) (Fin 7) ℝ) - directionGramMatrix D)
      = (7 / 3 : ℝ) • ((7 / 3 : ℝ) • (1 : Matrix (Fin 7) (Fin 7) ℝ) - directionGramMatrix D) := by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, hsq]
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
    module
  have hthird : (7 / 3 : ℝ) • (1 : Matrix (Fin 7) (Fin 7) ℝ) - directionGramMatrix D
      = (3 / 7 : ℝ) • (((7 / 3 : ℝ) • (1 : Matrix (Fin 7) (Fin 7) ℝ) - directionGramMatrix D)ᴴ
          * ((7 / 3 : ℝ) • (1 : Matrix (Fin 7) (Fin 7) ℝ) - directionGramMatrix D)) := by
    rw [hconj, hsquare, smul_smul]
    norm_num
  rw [hthird]
  exact (Matrix.posSemidef_conjTranspose_mul_self _).smul (by norm_num)

/-- The triple pick is injective. -/
private theorem bandPickInjective {firstIndex secondIndex thirdIndex : Fin 7}
    (hfirstSecond : firstIndex ≠ secondIndex) (hfirstThird : firstIndex ≠ thirdIndex)
    (hsecondThird : secondIndex ≠ thirdIndex) :
    Function.Injective ![firstIndex, secondIndex, thirdIndex] := by
  intro leftSlot rightSlot hvalue
  fin_cases leftSlot <;> fin_cases rightSlot <;>
    first
      | rfl
      | exact absurd hvalue (by assumption)
      | exact absurd hvalue.symm (by assumption)

/-- The Gram block of a triple, as `1 + N` with `N` the hollow block of the
three cosines.  Needs only nondegenerate atoms and distinctness. -/
private theorem bandGramSubmatrix (D : WeightedDesign m k)
    {firstIndex secondIndex thirdIndex : Fin m}
    (hfirstPos : 0 < leverageOf (D.atom firstIndex))
    (hsecondPos : 0 < leverageOf (D.atom secondIndex))
    (hthirdPos : 0 < leverageOf (D.atom thirdIndex)) :
    (directionGramMatrix D).submatrix ![firstIndex, secondIndex, thirdIndex]
        ![firstIndex, secondIndex, thirdIndex]
      = (1 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ)
        + hollowSymmetricThree (directionGram D firstIndex secondIndex)
            (directionGram D firstIndex thirdIndex)
            (directionGram D secondIndex thirdIndex) := by
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.submatrix_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
      hollowSymmetricThree, Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one,
      Matrix.head_fin_const, Matrix.of_apply, Fin.reduceEq, if_true, if_false, mul_one,
      mul_zero, add_zero, zero_add] <;>
    first
      | exact directionGram_self D hfirstPos
      | exact directionGram_self D hsecondPos
      | exact directionGram_self D hthirdPos
      | rfl
      | exact directionGram_comm D secondIndex firstIndex
      | exact directionGram_comm D thirdIndex firstIndex
      | exact directionGram_comm D thirdIndex secondIndex

/-- The compressed cap `(4/3)·1 − N[T] ⪰ 0` at any triple of distinct atoms of
the stratum — the `hcap` feeder of the landed cap-`4/3` criterion. -/
private theorem bandTripleCapPsd (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7)
    {firstIndex secondIndex thirdIndex : Fin 7}
    (hfirstSecond : firstIndex ≠ secondIndex) (hfirstThird : firstIndex ≠ thirdIndex)
    (hsecondThird : secondIndex ≠ thirdIndex) :
    ((4 / 3 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ)
      - hollowSymmetricThree (directionGram D firstIndex secondIndex)
          (directionGram D firstIndex thirdIndex)
          (directionGram D secondIndex thirdIndex)).PosSemidef := by
  have hcompressed := (bandCapPsd D huniform).submatrix
    ![firstIndex, secondIndex, thirdIndex]
  have hshape : ((7 / 3 : ℝ) • (1 : Matrix (Fin 7) (Fin 7) ℝ)
        - directionGramMatrix D).submatrix ![firstIndex, secondIndex, thirdIndex]
        ![firstIndex, secondIndex, thirdIndex]
      = (4 / 3 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ)
        - hollowSymmetricThree (directionGram D firstIndex secondIndex)
            (directionGram D firstIndex thirdIndex)
            (directionGram D secondIndex thirdIndex) := by
    have hsplit : ((7 / 3 : ℝ) • (1 : Matrix (Fin 7) (Fin 7) ℝ)
          - directionGramMatrix D).submatrix ![firstIndex, secondIndex, thirdIndex]
          ![firstIndex, secondIndex, thirdIndex]
        = (7 / 3 : ℝ) • ((1 : Matrix (Fin 7) (Fin 7) ℝ).submatrix
            ![firstIndex, secondIndex, thirdIndex] ![firstIndex, secondIndex, thirdIndex])
          - (directionGramMatrix D).submatrix ![firstIndex, secondIndex, thirdIndex]
              ![firstIndex, secondIndex, thirdIndex] := rfl
    rw [hsplit,
      Matrix.submatrix_one _ (bandPickInjective hfirstSecond hfirstThird hsecondThird),
      bandGramSubmatrix D (bandLeveragePos D huniform firstIndex)
        (bandLeveragePos D huniform secondIndex) (bandLeveragePos D huniform thirdIndex)]
    module
  rwa [hshape] at hcompressed

/-- The frustrated cap at a triple: `0 ≤ 1 − σ + 2P` (the Gram determinant),
share-free — any design, any rank, three nondegenerate distinct atoms. -/
private theorem bandDetCap (D : WeightedDesign m k)
    {firstIndex secondIndex thirdIndex : Fin m}
    (hfirstPos : 0 < leverageOf (D.atom firstIndex))
    (hsecondPos : 0 < leverageOf (D.atom secondIndex))
    (hthirdPos : 0 < leverageOf (D.atom thirdIndex)) :
    0 ≤ 1 - directionTripleSigma D firstIndex secondIndex thirdIndex
        + 2 * directionTripleProduct D firstIndex secondIndex thirdIndex := by
  have hdet := ((posSemidef_directionGramMatrix D).submatrix
    ![firstIndex, secondIndex, thirdIndex]).det_nonneg
  rw [bandGramSubmatrix D hfirstPos hsecondPos hthirdPos,
    det_smul_one_add_hollowSymmetricThree] at hdet
  simp only [directionTripleSigma, directionTripleProduct]
  nlinarith [hdet]

/-- The coherent cap at a stratum triple: `σ + (3/2) P ≤ 16/9`
(the determinant of the compressed `4/3` cap). -/
private theorem bandCoherentCap (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7)
    {firstIndex secondIndex thirdIndex : Fin 7}
    (hfirstSecond : firstIndex ≠ secondIndex) (hfirstThird : firstIndex ≠ thirdIndex)
    (hsecondThird : secondIndex ≠ thirdIndex) :
    directionTripleSigma D firstIndex secondIndex thirdIndex
        + 3 / 2 * directionTripleProduct D firstIndex secondIndex thirdIndex ≤ 16 / 9 := by
  have hdet := (bandTripleCapPsd D huniform hfirstSecond hfirstThird hsecondThird).det_nonneg
  rw [det_smul_one_sub_hollowSymmetricThree] at hdet
  simp only [directionTripleSigma, directionTripleProduct]
  nlinarith [hdet]

/-- The square of the oriented product is the product of the three edge
weights. -/
private theorem bandProductSq (D : WeightedDesign m k)
    (firstIndex secondIndex thirdIndex : Fin m) :
    directionTripleProduct D firstIndex secondIndex thirdIndex ^ 2
      = edgeWeight D firstIndex secondIndex * edgeWeight D firstIndex thirdIndex
        * edgeWeight D secondIndex thirdIndex := by
  simp only [directionTripleProduct, edgeWeight]
  ring

/-- **The stratum domination dictionary (C1-IFF)**: on uniform share `3/7`
with uniform leverage `3`, a triple of distinct atoms dominates exactly when
`σ − 3P ≤ 4/9`.  Private: three sibling modules of this workflow land public
versions; this one exists so the module is self-contained. -/
private theorem bandDominatesIff (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7)
    (hleverage : ∀ atomIndex, leverageOf (D.atom atomIndex) = 3)
    {firstIndex secondIndex thirdIndex : Fin 7}
    (hfirstSecond : firstIndex ≠ secondIndex) (hfirstThird : firstIndex ≠ thirdIndex)
    (hsecondThird : secondIndex ≠ thirdIndex) :
    Dominates D {firstIndex, secondIndex, thirdIndex}
      ↔ orientedTripleResidual D firstIndex secondIndex thirdIndex ≤ 4 / 9 := by
  have hcriterion := posSemidef_smul_one_add_hollowSymmetricThree_iff_of_spectralCapFourThirds
    (le_refl ((2 : ℝ) / 3))
    (bandTripleCapPsd D huniform hfirstSecond hfirstThird hsecondThird)
  rw [dominates_triple_iff_posSemidef_hollowShift D hleverage hfirstSecond hfirstThird
    hsecondThird, hollowMatrixThree_eq_hollowSymmetricThree, add_comm, hcriterion]
  simp only [orientedTripleResidual, edgeWeight]
  constructor <;> intro hbound <;> nlinarith [hbound]

/-- Nonstrict pigeonhole, lower side: if a sum is at most `card • bound`, some
term is at most `bound`. -/
private theorem bandPigeonholeLe {indexSet : Finset (Fin 7)} {values : Fin 7 → ℝ}
    {bound : ℝ} (hnonempty : indexSet.Nonempty)
    (hsum : ∑ index ∈ indexSet, values index ≤ (indexSet.card : ℝ) * bound) :
    ∃ index ∈ indexSet, values index ≤ bound := by
  by_contra hcontra
  have hstrict : ∀ index ∈ indexSet, bound < values index := by
    intro index hmem
    rcases lt_or_ge bound (values index) with hgt | hle
    · exact hgt
    · exact absurd ⟨index, hmem, hle⟩ hcontra
  have hlt : ∑ _index ∈ indexSet, bound < ∑ index ∈ indexSet, values index :=
    Finset.sum_lt_sum_of_nonempty hnonempty hstrict
  rw [Finset.sum_const, nsmul_eq_mul] at hlt
  linarith

/-- Nonstrict pigeonhole, upper side: if a sum is at least `card • bound`, some
term is at least `bound`. -/
private theorem bandPigeonholeGe {indexSet : Finset (Fin 7)} {values : Fin 7 → ℝ}
    {bound : ℝ} (hnonempty : indexSet.Nonempty)
    (hsum : (indexSet.card : ℝ) * bound ≤ ∑ index ∈ indexSet, values index) :
    ∃ index ∈ indexSet, bound ≤ values index := by
  by_contra hcontra
  have hstrict : ∀ index ∈ indexSet, values index < bound := by
    intro index hmem
    rcases lt_or_ge (values index) bound with hgt | hle
    · exact hgt
    · exact absurd ⟨index, hmem, hle⟩ hcontra
  have hlt : ∑ index ∈ indexSet, values index < ∑ _index ∈ indexSet, bound :=
    Finset.sum_lt_sum_of_nonempty hnonempty hstrict
  rw [Finset.sum_const, nsmul_eq_mul] at hlt
  linarith

/-- The five-element completion set of a pair. -/
private theorem bandCardPairCompl {pairFirst pairSecond : Fin 7}
    (hpairNe : pairFirst ≠ pairSecond) :
    (Finset.univ \ ({pairFirst, pairSecond} : Finset (Fin 7))).card = 5 := by
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin,
    Finset.card_insert_of_notMem (by simp [hpairNe]), Finset.card_singleton]

/-- The residual is invariant under swapping the last two slots. -/
private theorem bandResidualSwapLast (D : WeightedDesign m k)
    (firstIndex secondIndex thirdIndex : Fin m) :
    orientedTripleResidual D firstIndex secondIndex thirdIndex
      = orientedTripleResidual D firstIndex thirdIndex secondIndex := by
  simp only [orientedTripleResidual, edgeWeight]
  rw [directionGram_comm D thirdIndex secondIndex]
  ring

/-- The residual is invariant under swapping the first two slots. -/
private theorem bandResidualSwapFirst (D : WeightedDesign m k)
    (firstIndex secondIndex thirdIndex : Fin m) :
    orientedTripleResidual D firstIndex secondIndex thirdIndex
      = orientedTripleResidual D secondIndex firstIndex thirdIndex := by
  simp only [orientedTripleResidual, edgeWeight]
  rw [directionGram_comm D secondIndex firstIndex]
  ring

/-! ## 1. The failure fence: exact per-pair bookkeeping (task 1)

The five completions of a pair `{a, b}` carry exact totals of `σ`, `P`, the
residual `r = σ − 3P`, and the criterion clause `Δ`.  These are the (7,3)
row/supply laws read at triple level, and every later section spends them. -/

/-- **Per-pair σ-total.**  The five completions of a pair carry
`Σ σ = 3 w_ab + 8/3`. -/
theorem sum_tripleSigma_pairCompletions_bandSeven (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7)
    {pairFirst pairSecond : Fin 7} (hpairNe : pairFirst ≠ pairSecond) :
    ∑ outer ∈ Finset.univ \ ({pairFirst, pairSecond} : Finset (Fin 7)),
        directionTripleSigma D pairFirst pairSecond outer
      = 3 * edgeWeight D pairFirst pairSecond + 8 / 3 := by
  have hpoint : ∀ outer ∈ Finset.univ \ ({pairFirst, pairSecond} : Finset (Fin 7)),
      directionTripleSigma D pairFirst pairSecond outer
        = edgeWeight D pairFirst pairSecond + edgeWeight D pairFirst outer
          + edgeWeight D pairSecond outer := by
    intro outer _
    simp only [directionTripleSigma, edgeWeight]
  have hrowFirst : ∑ outer ∈ Finset.univ \ ({pairFirst, pairSecond} : Finset (Fin 7)),
      edgeWeight D pairFirst outer = 4 / 3 - edgeWeight D pairFirst pairSecond := by
    have hdrop := bandRowDrop D huniform pairFirst {pairSecond} (by simp [hpairNe])
    rwa [Finset.sum_singleton] at hdrop
  have hrowSecond : ∑ outer ∈ Finset.univ \ ({pairFirst, pairSecond} : Finset (Fin 7)),
      edgeWeight D pairSecond outer = 4 / 3 - edgeWeight D pairSecond pairFirst := by
    have hdrop := bandRowDrop D huniform pairSecond {pairFirst} (by simp [hpairNe.symm])
    rw [Finset.sum_singleton] at hdrop
    rwa [show insert pairSecond ({pairFirst} : Finset (Fin 7)) = {pairFirst, pairSecond} from
      Finset.pair_comm pairSecond pairFirst] at hdrop
  rw [Finset.sum_congr rfl hpoint, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_const, bandCardPairCompl hpairNe, hrowFirst, hrowSecond,
    edgeWeight_comm D pairSecond pairFirst, nsmul_eq_mul]
  push_cast
  ring

/-- **Per-pair P-total (C-P1, the positive supply).**  The five completions of a
pair carry `Σ P = w_ab / 3 ≥ 0`: around every pair, coherence wins on
aggregate.  The (6,3) analogue is zero. -/
theorem sum_tripleProduct_pairCompletions_bandSeven (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7)
    {pairFirst pairSecond : Fin 7} (hpairNe : pairFirst ≠ pairSecond) :
    ∑ outer ∈ Finset.univ \ ({pairFirst, pairSecond} : Finset (Fin 7)),
        directionTripleProduct D pairFirst pairSecond outer
      = edgeWeight D pairFirst pairSecond / 3 := by
  have hpoint : ∀ outer ∈ Finset.univ \ ({pairFirst, pairSecond} : Finset (Fin 7)),
      directionTripleProduct D pairFirst pairSecond outer
        = directionGram D pairFirst pairSecond
            * (directionGram D pairFirst outer * directionGram D outer pairSecond) := by
    intro outer _
    simp only [directionTripleProduct]
    rw [directionGram_comm D pairSecond outer]
    ring
  rw [Finset.sum_congr rfl hpoint, ← Finset.mul_sum, bandSupply D huniform hpairNe, edgeWeight]
  ring

/-- **Per-pair residual total.**  The five completions of a pair carry
`Σ (σ − 3P) = 2 w_ab + 8/3`. -/
theorem sum_orientedResidual_pairCompletions_bandSeven (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7)
    {pairFirst pairSecond : Fin 7} (hpairNe : pairFirst ≠ pairSecond) :
    ∑ outer ∈ Finset.univ \ ({pairFirst, pairSecond} : Finset (Fin 7)),
        orientedTripleResidual D pairFirst pairSecond outer
      = 2 * edgeWeight D pairFirst pairSecond + 8 / 3 := by
  have hpoint : ∀ outer ∈ Finset.univ \ ({pairFirst, pairSecond} : Finset (Fin 7)),
      orientedTripleResidual D pairFirst pairSecond outer
        = directionTripleSigma D pairFirst pairSecond outer
          - 3 * directionTripleProduct D pairFirst pairSecond outer := by
    intro outer _
    exact orientedTripleResidual_eq_sigma_sub D pairFirst pairSecond outer
  rw [Finset.sum_congr rfl hpoint, Finset.sum_sub_distrib, ← Finset.mul_sum,
    sum_tripleSigma_pairCompletions_bandSeven D huniform hpairNe,
    sum_tripleProduct_pairCompletions_bandSeven D huniform hpairNe]
  ring

/-- **Per-pair clause total (C-PAIR).**  At the criterion slack `2/3` the five
determinant clauses through a pair total `−8/27 − (4/3) w_ab < 0`: the pair
aggregate is always in deficit, positive supply notwithstanding. -/
theorem sum_slackDeterminantThree_pairCompletions_bandSeven (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7)
    {pairFirst pairSecond : Fin 7} (hpairNe : pairFirst ≠ pairSecond) :
    ∑ outer ∈ Finset.univ \ ({pairFirst, pairSecond} : Finset (Fin 7)),
        slackDeterminantThree (2 / 3) (2 / 3) (2 / 3)
          (directionGram D pairFirst pairSecond) (directionGram D pairFirst outer)
          (directionGram D pairSecond outer)
      = -(8 / 27) - 4 / 3 * edgeWeight D pairFirst pairSecond := by
  have hpoint : ∀ outer ∈ Finset.univ \ ({pairFirst, pairSecond} : Finset (Fin 7)),
      slackDeterminantThree (2 / 3) (2 / 3) (2 / 3)
          (directionGram D pairFirst pairSecond) (directionGram D pairFirst outer)
          (directionGram D pairSecond outer)
        = 8 / 27 - 2 / 3 * directionTripleSigma D pairFirst pairSecond outer
          + 2 * directionTripleProduct D pairFirst pairSecond outer := by
    intro outer _
    simp only [slackDeterminantThree, directionTripleSigma, directionTripleProduct]
    ring
  rw [Finset.sum_congr rfl hpoint, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_const, ← Finset.mul_sum, ← Finset.mul_sum, bandCardPairCompl hpairNe,
    sum_tripleSigma_pairCompletions_bandSeven D huniform hpairNe,
    sum_tripleProduct_pairCompletions_bandSeven D huniform hpairNe, nsmul_eq_mul]
  push_cast
  ring

/-- **The honest vacuity of the pair aggregate.**  The per-pair mean residual
`(2w + 8/3)/5` exceeds the criterion `4/9` for every admissible edge weight, so
averaging over a pair's completions can never certify a dominating triple.
This is why the sandwich below extracts information from the DEVIATION of a
hub, not from the mean. -/
theorem pairCompletions_mean_exceeds_criterion_bandSeven {pairWeight : ℝ}
    (hnonneg : 0 ≤ pairWeight) :
    4 / 9 < (2 * pairWeight + 8 / 3) / 5 := by
  linarith

/-- **The global ordered residual total.**  Over all `210 = 7·6·5` ordered
distinct triples, `Σ (σ − 3P) = 392/3`.  Each unordered triple appears six
times and the residual is permutation-invariant, so the 35-triple total is
`196/9`, against a total demand of `35 · 4/9 = 140/9` on a failing
configuration: the global slack is `56/9`, and the aggregate is loose exactly
as P2 predicts. -/
theorem sum_ordered_orientedResidual_bandSeven (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7) :
    ∑ first : Fin 7, ∑ second ∈ Finset.univ.erase first,
        ∑ third ∈ Finset.univ \ ({first, second} : Finset (Fin 7)),
          orientedTripleResidual D first second third
      = 392 / 3 := by
  have hinner : ∀ first : Fin 7, ∀ second ∈ Finset.univ.erase first,
      ∑ third ∈ Finset.univ \ ({first, second} : Finset (Fin 7)),
          orientedTripleResidual D first second third
        = 2 * edgeWeight D first second + 8 / 3 := by
    intro first second hsecond
    have hne : first ≠ second := fun hcontra =>
      (Finset.mem_erase.mp hsecond).1 hcontra.symm
    exact sum_orientedResidual_pairCompletions_bandSeven D huniform hne
  have hmiddle : ∀ first : Fin 7,
      ∑ second ∈ Finset.univ.erase first,
          (2 * edgeWeight D first second + 8 / 3) = 56 / 3 := by
    intro first
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, bandRowLaw D huniform first,
      Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ first),
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    norm_num
  rw [Finset.sum_congr rfl fun first _ =>
    (Finset.sum_congr rfl (hinner first)).trans (hmiddle first), Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  norm_num

/-- **The mean does not certify.**  Some ordered distinct triple has residual at
most the mean `28/45` — which sits strictly ABOVE the criterion `4/9 = 20/45`.
The exact gap `28/45 − 20/45 = 8/45` is the per-triple share of the global
slack `56/9`. -/
theorem exists_orientedResidual_le_mean_bandSeven (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7) :
    ∃ first second third : Fin 7, first ≠ second ∧ first ≠ third ∧ second ≠ third
      ∧ orientedTripleResidual D first second third ≤ 28 / 45 := by
  have htotal := sum_ordered_orientedResidual_bandSeven D huniform
  have hfirst : ∃ first ∈ (Finset.univ : Finset (Fin 7)),
      ∑ second ∈ Finset.univ.erase first,
          ∑ third ∈ Finset.univ \ ({first, second} : Finset (Fin 7)),
            orientedTripleResidual D first second third ≤ 56 / 3 := by
    refine bandPigeonholeLe Finset.univ_nonempty ?_
    rw [htotal, Finset.card_univ, Fintype.card_fin]
    norm_num
  obtain ⟨first, _, hfirstSum⟩ := hfirst
  have hsecond : ∃ second ∈ Finset.univ.erase first,
      ∑ third ∈ Finset.univ \ ({first, second} : Finset (Fin 7)),
          orientedTripleResidual D first second third ≤ 28 / 9 := by
    refine bandPigeonholeLe (Finset.card_pos.mp ?_) ?_
    · rw [Finset.card_erase_of_mem (Finset.mem_univ first), Finset.card_univ,
        Fintype.card_fin]
      norm_num
    · rw [Finset.card_erase_of_mem (Finset.mem_univ first), Finset.card_univ,
        Fintype.card_fin]
      push_cast
      linarith
  obtain ⟨second, hsecondMem, hsecondSum⟩ := hsecond
  have hne : first ≠ second := fun hcontra => (Finset.mem_erase.mp hsecondMem).1 hcontra.symm
  have hthird : ∃ third ∈ Finset.univ \ ({first, second} : Finset (Fin 7)),
      orientedTripleResidual D first second third ≤ 28 / 45 := by
    refine bandPigeonholeLe ?_ ?_
    · rw [← Finset.card_pos, bandCardPairCompl hne]
      norm_num
    · rw [bandCardPairCompl hne]
      push_cast
      linarith
  obtain ⟨third, hthirdMem, hthirdBound⟩ := hthird
  have hthirdNe := Finset.mem_sdiff.mp hthirdMem
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hthirdNe
  exact ⟨first, second, third, hne, fun hcontra => hthirdNe.2.1 hcontra.symm,
    fun hcontra => hthirdNe.2.2 hcontra.symm, hthirdBound⟩

/-! ## 2. The fence and the sandwich (task 2)

`Δ = 8/27 − (2/3) r`, so `Δ < 0 ↔ r > 4/9` and the C-PAIR deficit turns every
failing configuration's clauses into a two-sided window. -/

/-- **The fence.**  On the stratum a triple that does not dominate has residual
strictly above the criterion: `σ − 3P > 4/9`. -/
theorem four_ninths_lt_orientedResidual_of_not_dominates_bandSeven (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7)
    (hleverage : ∀ atomIndex, leverageOf (D.atom atomIndex) = 3)
    {tripleFirst tripleSecond tripleThird : Fin 7}
    (hfirstSecond : tripleFirst ≠ tripleSecond) (hfirstThird : tripleFirst ≠ tripleThird)
    (hsecondThird : tripleSecond ≠ tripleThird)
    (hnot : ¬ Dominates D {tripleFirst, tripleSecond, tripleThird}) :
    4 / 9 < orientedTripleResidual D tripleFirst tripleSecond tripleThird := by
  by_contra hcontra
  exact hnot ((bandDominatesIff D huniform hleverage hfirstSecond hfirstThird
    hsecondThird).mpr (not_lt.mp hcontra))

/-- **Task 1(a): coherent failing triples are heavy in σ.**  A coherent triple
(`P ≥ 0`) that does not dominate has `σ > 4/9 + 3P ≥ 4/9`. -/
theorem four_ninths_lt_tripleSigma_of_coherent_not_dominates_bandSeven (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7)
    (hleverage : ∀ atomIndex, leverageOf (D.atom atomIndex) = 3)
    {tripleFirst tripleSecond tripleThird : Fin 7}
    (hfirstSecond : tripleFirst ≠ tripleSecond) (hfirstThird : tripleFirst ≠ tripleThird)
    (hsecondThird : tripleSecond ≠ tripleThird)
    (hcoherent : 0 ≤ directionTripleProduct D tripleFirst tripleSecond tripleThird)
    (hnot : ¬ Dominates D {tripleFirst, tripleSecond, tripleThird}) :
    4 / 9 < directionTripleSigma D tripleFirst tripleSecond tripleThird := by
  have hfence := four_ninths_lt_orientedResidual_of_not_dominates_bandSeven D huniform
    hleverage hfirstSecond hfirstThird hsecondThird hnot
  rw [orientedTripleResidual_eq_sigma_sub] at hfence
  linarith

/-- **The product cap on failing triples.**  A triple that does not dominate
has `P < 8/27` (fence against the coherent cap — no sign hypothesis needed).
`8/27` is the frozen heavy-gate value, approached only at the `w ≡ 4/9`
tie. -/
theorem tripleProduct_lt_of_not_dominates_bandSeven (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7)
    (hleverage : ∀ atomIndex, leverageOf (D.atom atomIndex) = 3)
    {tripleFirst tripleSecond tripleThird : Fin 7}
    (hfirstSecond : tripleFirst ≠ tripleSecond) (hfirstThird : tripleFirst ≠ tripleThird)
    (hsecondThird : tripleSecond ≠ tripleThird)
    (hnot : ¬ Dominates D {tripleFirst, tripleSecond, tripleThird}) :
    directionTripleProduct D tripleFirst tripleSecond tripleThird < 8 / 27 := by
  have hfence := four_ninths_lt_orientedResidual_of_not_dominates_bandSeven D huniform
    hleverage hfirstSecond hfirstThird hsecondThird hnot
  rw [orientedTripleResidual_eq_sigma_sub] at hfence
  have hcap := bandCoherentCap D huniform hfirstSecond hfirstThird hsecondThird
  linarith

/-- The upper half of the sandwich, engine form: on a failing configuration the
residual of any triple is below `8/9 + 2 w` at ITS FIRST PAIR, because the
other four completions of that pair each spend more than `4/9` of the pair's
exact residual budget `2w + 8/3`. -/
private theorem bandUpperEngine (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7)
    (hleverage : ∀ atomIndex, leverageOf (D.atom atomIndex) = 3)
    (hfail : ∀ first second third : Fin 7, first ≠ second → first ≠ third →
      second ≠ third → ¬ Dominates D {first, second, third})
    {pairFirst pairSecond hub : Fin 7} (hpairNe : pairFirst ≠ pairSecond)
    (hfirstHub : pairFirst ≠ hub) (hsecondHub : pairSecond ≠ hub) :
    orientedTripleResidual D pairFirst pairSecond hub
      < 8 / 9 + 2 * edgeWeight D pairFirst pairSecond := by
  have htotal := sum_orientedResidual_pairCompletions_bandSeven D huniform hpairNe
  have hhubMem : hub ∈ Finset.univ \ ({pairFirst, pairSecond} : Finset (Fin 7)) := by
    simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton,
      true_and, not_or]
    exact ⟨fun hcontra => hfirstHub hcontra.symm, fun hcontra => hsecondHub hcontra.symm⟩
  have hsplit := Finset.sum_erase_add
    (Finset.univ \ ({pairFirst, pairSecond} : Finset (Fin 7)))
    (fun outer => orientedTripleResidual D pairFirst pairSecond outer) hhubMem
  have hothers : 16 / 9 < ∑ outer ∈ (Finset.univ
      \ ({pairFirst, pairSecond} : Finset (Fin 7))).erase hub,
        orientedTripleResidual D pairFirst pairSecond outer := by
    have hcard : ((Finset.univ \ ({pairFirst, pairSecond} : Finset (Fin 7))).erase hub).card
        = 4 := by
      rw [Finset.card_erase_of_mem hhubMem, bandCardPairCompl hpairNe]
    have hpointwise : ∀ outer ∈ (Finset.univ
        \ ({pairFirst, pairSecond} : Finset (Fin 7))).erase hub,
        (4 : ℝ) / 9 < orientedTripleResidual D pairFirst pairSecond outer := by
      intro outer houter
      have houterNe := Finset.mem_erase.mp houter
      have houterCompl := Finset.mem_sdiff.mp houterNe.2
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at houterCompl
      exact four_ninths_lt_orientedResidual_of_not_dominates_bandSeven D huniform hleverage
        hpairNe (fun hcontra => houterCompl.2.1 hcontra.symm)
        (fun hcontra => houterCompl.2.2 hcontra.symm)
        (hfail pairFirst pairSecond outer hpairNe
          (fun hcontra => houterCompl.2.1 hcontra.symm)
          (fun hcontra => houterCompl.2.2 hcontra.symm))
    have hconst := Finset.sum_lt_sum_of_nonempty
      (Finset.card_pos.mp (by rw [hcard]; norm_num)) hpointwise
    rw [Finset.sum_const, hcard, nsmul_eq_mul] at hconst
    push_cast at hconst
    linarith
  linarith [hsplit, htotal, hothers]

/-- **THE SANDWICH (task 2iii).**  On a failing configuration every triple's
residual sits in the exact window

  `4/9 < σ − 3P < 8/9 + 2 w_e`  for EACH edge `e` of the triple,

hence below `8/9 + 2 min-edge`.  In clause coordinates:
`−8/27 − (4/3) w_e < Δ < 0`.  This is the (7,3) residual window, the exact
analogue of the (6,3) Brick window, and every triple of a failing
configuration lives inside it. -/
theorem orientedResidual_window_of_allFailing_bandSeven (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7)
    (hleverage : ∀ atomIndex, leverageOf (D.atom atomIndex) = 3)
    (hfail : ∀ first second third : Fin 7, first ≠ second → first ≠ third →
      second ≠ third → ¬ Dominates D {first, second, third})
    {tripleFirst tripleSecond tripleThird : Fin 7}
    (hfirstSecond : tripleFirst ≠ tripleSecond) (hfirstThird : tripleFirst ≠ tripleThird)
    (hsecondThird : tripleSecond ≠ tripleThird) :
    4 / 9 < orientedTripleResidual D tripleFirst tripleSecond tripleThird
      ∧ orientedTripleResidual D tripleFirst tripleSecond tripleThird
          < 8 / 9 + 2 * edgeWeight D tripleFirst tripleSecond
      ∧ orientedTripleResidual D tripleFirst tripleSecond tripleThird
          < 8 / 9 + 2 * edgeWeight D tripleFirst tripleThird
      ∧ orientedTripleResidual D tripleFirst tripleSecond tripleThird
          < 8 / 9 + 2 * edgeWeight D tripleSecond tripleThird := by
  refine ⟨four_ninths_lt_orientedResidual_of_not_dominates_bandSeven D huniform hleverage
    hfirstSecond hfirstThird hsecondThird
    (hfail tripleFirst tripleSecond tripleThird hfirstSecond hfirstThird hsecondThird),
    bandUpperEngine D huniform hleverage hfail hfirstSecond hfirstThird hsecondThird, ?_, ?_⟩
  · have hengine := bandUpperEngine D huniform hleverage hfail hfirstThird hfirstSecond
      hsecondThird.symm
    rwa [bandResidualSwapLast D tripleFirst tripleThird tripleSecond] at hengine
  · have hengine := bandUpperEngine D huniform hleverage hfail hsecondThird
      hfirstSecond.symm hfirstThird.symm
    rw [bandResidualSwapLast D tripleSecond tripleThird tripleFirst,
      bandResidualSwapFirst D tripleSecond tripleFirst tripleThird] at hengine
    exact hengine

/-- **THE STARVE-FEED GATE (task 2ii), clause-free.**  If a hub triple
`{a, b, c}` is starved — its residual at least the threshold `8/9 + 2 w_ab` —
then one of the four other completions of `{a, b}` DOMINATES outright.  The
budget arithmetic is exact: the four siblings retain at most
`(2w + 8/3) − (8/9 + 2w) = 16/9`, whose quarter is precisely the criterion
`4/9`.  Unlike the (6,3) gate no pairwise clauses are carried: the cap
criterion absorbs them on the stratum. -/
theorem exists_dominates_completion_of_starvedHub_bandSeven (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7)
    (hleverage : ∀ atomIndex, leverageOf (D.atom atomIndex) = 3)
    {pairFirst pairSecond hub : Fin 7} (hpairNe : pairFirst ≠ pairSecond)
    (hfirstHub : pairFirst ≠ hub) (hsecondHub : pairSecond ≠ hub)
    (hstarved : 8 / 9 + 2 * edgeWeight D pairFirst pairSecond
      ≤ orientedTripleResidual D pairFirst pairSecond hub) :
    ∃ outer : Fin 7, outer ≠ pairFirst ∧ outer ≠ pairSecond ∧ outer ≠ hub
      ∧ Dominates D {pairFirst, pairSecond, outer} := by
  have htotal := sum_orientedResidual_pairCompletions_bandSeven D huniform hpairNe
  have hhubMem : hub ∈ Finset.univ \ ({pairFirst, pairSecond} : Finset (Fin 7)) := by
    simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton,
      true_and, not_or]
    exact ⟨fun hcontra => hfirstHub hcontra.symm, fun hcontra => hsecondHub hcontra.symm⟩
  have hsplit := Finset.sum_erase_add
    (Finset.univ \ ({pairFirst, pairSecond} : Finset (Fin 7)))
    (fun outer => orientedTripleResidual D pairFirst pairSecond outer) hhubMem
  have hcard : ((Finset.univ \ ({pairFirst, pairSecond} : Finset (Fin 7))).erase hub).card
      = 4 := by
    rw [Finset.card_erase_of_mem hhubMem, bandCardPairCompl hpairNe]
  have hpigeon : ∃ outer ∈ (Finset.univ
      \ ({pairFirst, pairSecond} : Finset (Fin 7))).erase hub,
      orientedTripleResidual D pairFirst pairSecond outer ≤ 4 / 9 := by
    refine bandPigeonholeLe (Finset.card_pos.mp (by rw [hcard]; norm_num)) ?_
    rw [hcard]
    push_cast
    linarith [hsplit, htotal, hstarved]
  obtain ⟨outer, houterMem, houterBound⟩ := hpigeon
  have houterNe := Finset.mem_erase.mp houterMem
  have houterCompl := Finset.mem_sdiff.mp houterNe.2
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at houterCompl
  exact ⟨outer, houterCompl.2.1, houterCompl.2.2, houterNe.1,
    (bandDominatesIff D huniform hleverage hpairNe
      (fun hcontra => houterCompl.2.1 hcontra.symm)
      (fun hcontra => houterCompl.2.2 hcontra.symm)).mpr houterBound⟩

/-! ## 3. The five-set coherence floor (task 3)

C-5SET: the ordered `P`-mass of the five-set avoiding a pair is exactly
`4/9 + 2 w_ef > 0`, so every five-set contains a strictly coherent triple, and
on a failing configuration that carrier is trapped from below in `σ`. -/

/-- **C-5SET, ordered form.**  For every pair `{e, f}` the sum of the oriented
triple product over all ordered distinct triples inside the complementary
five-set equals `4/9 + 2 w_ef`.  (Each unordered triple appears six times, so
the unordered total is `2/27 + w_ef/3` — strictly positive coherent mass on
every five-set, where the (6,3) analogue vanishes.) -/
theorem sum_ordered_tripleProduct_avoidingPair_bandSeven (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7)
    {avoidFirst avoidSecond : Fin 7} (havoidNe : avoidFirst ≠ avoidSecond) :
    ∑ first ∈ Finset.univ \ ({avoidFirst, avoidSecond} : Finset (Fin 7)),
        ∑ second ∈ Finset.univ \ ({avoidFirst, avoidSecond, first} : Finset (Fin 7)),
          ∑ third ∈ Finset.univ
              \ ({avoidFirst, avoidSecond, first, second} : Finset (Fin 7)),
            directionTripleProduct D first second third
      = 4 / 9 + 2 * edgeWeight D avoidFirst avoidSecond := by
  -- Innermost layer: the third-atom sum is the twice-clipped supply chain.
  have hinner : ∀ first ∈ Finset.univ \ ({avoidFirst, avoidSecond} : Finset (Fin 7)),
      ∀ second ∈ Finset.univ \ ({avoidFirst, avoidSecond, first} : Finset (Fin 7)),
      ∑ third ∈ Finset.univ \ ({avoidFirst, avoidSecond, first, second} : Finset (Fin 7)),
          directionTripleProduct D first second third
        = directionGram D first second
            * (1 / 3 * directionGram D first second
              - directionGram D first avoidFirst * directionGram D avoidFirst second
              - directionGram D first avoidSecond * directionGram D avoidSecond second) := by
    intro first hfirst second hsecond
    have hfirstMem := Finset.mem_sdiff.mp hfirst
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hfirstMem
    have hsecondMem := Finset.mem_sdiff.mp hsecond
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hsecondMem
    have hfsNe : first ≠ second := fun hcontra => hsecondMem.2.2.2 hcontra.symm
    have hpoint : ∀ third ∈ Finset.univ
        \ ({avoidFirst, avoidSecond, first, second} : Finset (Fin 7)),
        directionTripleProduct D first second third
          = directionGram D first second
            * (directionGram D first third * directionGram D third second) := by
      intro third _
      simp only [directionTripleProduct]
      rw [directionGram_comm D second third]
      ring
    rw [Finset.sum_congr rfl hpoint, ← Finset.mul_sum]
    congr 1
    have hset : Finset.univ \ ({avoidFirst, avoidSecond, first, second} : Finset (Fin 7))
        = Finset.univ
          \ insert first (insert second ({avoidFirst, avoidSecond} : Finset (Fin 7))) := by
      ext member
      simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton,
        true_and]
      tauto
    have hdropped := bandSupplyDrop D huniform hfsNe
      ({avoidFirst, avoidSecond} : Finset (Fin 7))
      (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨hfirstMem.2.1, hfirstMem.2.2⟩)
      (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨hsecondMem.2.1, hsecondMem.2.2.1⟩)
    rw [hset, hdropped, Finset.sum_pair havoidNe]
    ring
  -- Middle layer: the second-atom sum in closed form.
  have hmiddle : ∀ first ∈ Finset.univ \ ({avoidFirst, avoidSecond} : Finset (Fin 7)),
      ∑ second ∈ Finset.univ \ ({avoidFirst, avoidSecond, first} : Finset (Fin 7)),
          (directionGram D first second
            * (1 / 3 * directionGram D first second
              - directionGram D first avoidFirst * directionGram D avoidFirst second
              - directionGram D first avoidSecond * directionGram D avoidSecond second))
        = 4 / 9 - 2 / 3 * edgeWeight D first avoidFirst
          - 2 / 3 * edgeWeight D first avoidSecond
          + 2 * (directionGram D first avoidFirst * directionGram D first avoidSecond
              * directionGram D avoidFirst avoidSecond) := by
    intro first hfirst
    have hfirstMem := Finset.mem_sdiff.mp hfirst
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hfirstMem
    have hpoint : ∀ second ∈ Finset.univ
        \ ({avoidFirst, avoidSecond, first} : Finset (Fin 7)),
        directionGram D first second
            * (1 / 3 * directionGram D first second
              - directionGram D first avoidFirst * directionGram D avoidFirst second
              - directionGram D first avoidSecond * directionGram D avoidSecond second)
          = 1 / 3 * directionGram D first second ^ 2
            - directionGram D first avoidFirst
                * (directionGram D first second * directionGram D second avoidFirst)
            - directionGram D first avoidSecond
                * (directionGram D first second * directionGram D second avoidSecond) := by
      intro second _
      rw [directionGram_comm D avoidFirst second, directionGram_comm D avoidSecond second]
      ring
    rw [Finset.sum_congr rfl hpoint, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
    -- the squared-cosine row, clipped at the two avoided atoms
    have hrowSet : Finset.univ \ ({avoidFirst, avoidSecond, first} : Finset (Fin 7))
        = Finset.univ
          \ insert first ({avoidFirst, avoidSecond} : Finset (Fin 7)) := by
      ext member
      simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton,
        true_and]
      tauto
    have hrow : ∑ second ∈ Finset.univ
        \ ({avoidFirst, avoidSecond, first} : Finset (Fin 7)),
        directionGram D first second ^ 2
          = 4 / 3 - edgeWeight D first avoidFirst - edgeWeight D first avoidSecond := by
      have hdrop := bandRowDrop D huniform first ({avoidFirst, avoidSecond} : Finset (Fin 7))
        (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
            exact ⟨hfirstMem.2.1, hfirstMem.2.2⟩)
      rw [Finset.sum_pair havoidNe] at hdrop
      have hconvert : ∀ second ∈ Finset.univ
          \ insert first ({avoidFirst, avoidSecond} : Finset (Fin 7)),
          edgeWeight D first second = directionGram D first second ^ 2 := fun second _ => rfl
      rw [Finset.sum_congr rfl hconvert] at hdrop
      rw [hrowSet, hdrop]
      ring
    -- the two clipped supply chains through the avoided atoms
    have hchainFirst : ∑ second ∈ Finset.univ
        \ ({avoidFirst, avoidSecond, first} : Finset (Fin 7)),
        directionGram D first second * directionGram D second avoidFirst
          = 1 / 3 * directionGram D first avoidFirst
            - directionGram D first avoidSecond
              * directionGram D avoidSecond avoidFirst := by
      have hset : Finset.univ \ ({avoidFirst, avoidSecond, first} : Finset (Fin 7))
          = Finset.univ
            \ insert first (insert avoidFirst ({avoidSecond} : Finset (Fin 7))) := by
        ext member
        simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton,
          true_and]
        tauto
      have hdrop := bandSupplyDrop D huniform
        (show first ≠ avoidFirst from hfirstMem.2.1) ({avoidSecond} : Finset (Fin 7))
        (by simp only [Finset.mem_singleton]; exact hfirstMem.2.2)
        (by simp only [Finset.mem_singleton]; exact havoidNe)
      rw [hset, hdrop, Finset.sum_singleton]
    have hchainSecond : ∑ second ∈ Finset.univ
        \ ({avoidFirst, avoidSecond, first} : Finset (Fin 7)),
        directionGram D first second * directionGram D second avoidSecond
          = 1 / 3 * directionGram D first avoidSecond
            - directionGram D first avoidFirst
              * directionGram D avoidFirst avoidSecond := by
      have hset : Finset.univ \ ({avoidFirst, avoidSecond, first} : Finset (Fin 7))
          = Finset.univ
            \ insert first (insert avoidSecond ({avoidFirst} : Finset (Fin 7))) := by
        ext member
        simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton,
          true_and]
        tauto
      have hdrop := bandSupplyDrop D huniform
        (show first ≠ avoidSecond from hfirstMem.2.2) ({avoidFirst} : Finset (Fin 7))
        (by simp only [Finset.mem_singleton]; exact hfirstMem.2.1)
        (by simp only [Finset.mem_singleton]; exact havoidNe.symm)
      rw [hset, hdrop, Finset.sum_singleton]
    rw [hrow, hchainFirst, hchainSecond]
    simp only [edgeWeight]
    rw [directionGram_comm D avoidSecond avoidFirst]
    ring
  -- Outer layer: sum the closed form over the five-set.
  rw [Finset.sum_congr rfl fun first hfirst =>
    (Finset.sum_congr rfl (hinner first hfirst)).trans (hmiddle first hfirst)]
  have houterRowFirst : ∑ first ∈ Finset.univ
      \ ({avoidFirst, avoidSecond} : Finset (Fin 7)),
      edgeWeight D first avoidFirst = 4 / 3 - edgeWeight D avoidFirst avoidSecond := by
    have hdrop := bandRowDrop D huniform avoidFirst ({avoidSecond} : Finset (Fin 7))
      (by simp only [Finset.mem_singleton]; exact havoidNe)
    rw [Finset.sum_singleton] at hdrop
    have hconvert : ∀ first ∈ Finset.univ \ ({avoidFirst, avoidSecond} : Finset (Fin 7)),
        edgeWeight D first avoidFirst = edgeWeight D avoidFirst first := fun first _ =>
      edgeWeight_comm D first avoidFirst
    rw [Finset.sum_congr rfl hconvert, hdrop]
  have houterRowSecond : ∑ first ∈ Finset.univ
      \ ({avoidFirst, avoidSecond} : Finset (Fin 7)),
      edgeWeight D first avoidSecond = 4 / 3 - edgeWeight D avoidFirst avoidSecond := by
    have hdrop := bandRowDrop D huniform avoidSecond ({avoidFirst} : Finset (Fin 7))
      (by simp only [Finset.mem_singleton]; exact havoidNe.symm)
    rw [Finset.sum_singleton] at hdrop
    have hconvert : ∀ first ∈ Finset.univ \ ({avoidFirst, avoidSecond} : Finset (Fin 7)),
        edgeWeight D first avoidSecond = edgeWeight D avoidSecond first := fun first _ =>
      edgeWeight_comm D first avoidSecond
    rw [Finset.sum_congr rfl hconvert,
      show (Finset.univ \ ({avoidFirst, avoidSecond} : Finset (Fin 7)))
          = Finset.univ \ insert avoidSecond ({avoidFirst} : Finset (Fin 7)) from by
        ext member
        simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton,
          true_and]
        tauto,
      hdrop, edgeWeight_comm D avoidSecond avoidFirst]
  have houterChain : ∑ first ∈ Finset.univ
      \ ({avoidFirst, avoidSecond} : Finset (Fin 7)),
      directionGram D first avoidFirst * directionGram D first avoidSecond
        * directionGram D avoidFirst avoidSecond
      = 1 / 3 * edgeWeight D avoidFirst avoidSecond := by
    have hconvert : ∀ first ∈ Finset.univ \ ({avoidFirst, avoidSecond} : Finset (Fin 7)),
        directionGram D first avoidFirst * directionGram D first avoidSecond
            * directionGram D avoidFirst avoidSecond
          = directionGram D avoidFirst avoidSecond
            * (directionGram D avoidFirst first * directionGram D first avoidSecond) := by
      intro first _
      rw [directionGram_comm D first avoidFirst]
      ring
    rw [Finset.sum_congr rfl hconvert, ← Finset.mul_sum, bandSupply D huniform havoidNe,
      edgeWeight]
    ring
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    Finset.sum_const, bandCardPairCompl havoidNe, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.mul_sum, houterRowFirst, houterRowSecond, houterChain, nsmul_eq_mul]
  push_cast
  ring

/-- **The five-set coherent floor.**  Every five-set (complement of a pair)
contains a triple of pairwise distinct atoms with
`P ≥ 1/135 + w_ef/30 > 0` — the ordered C-5SET mass divided by the sixty
ordered slots. -/
theorem exists_tripleProduct_ge_floor_avoidingPair_bandSeven (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7)
    {avoidFirst avoidSecond : Fin 7} (havoidNe : avoidFirst ≠ avoidSecond) :
    ∃ first second third : Fin 7,
      first ≠ avoidFirst ∧ first ≠ avoidSecond ∧ second ≠ avoidFirst ∧ second ≠ avoidSecond
        ∧ third ≠ avoidFirst ∧ third ≠ avoidSecond
        ∧ first ≠ second ∧ first ≠ third ∧ second ≠ third
        ∧ 1 / 135 + edgeWeight D avoidFirst avoidSecond / 30
            ≤ directionTripleProduct D first second third := by
  have htotal := sum_ordered_tripleProduct_avoidingPair_bandSeven D huniform havoidNe
  set floorValue : ℝ := 1 / 135 + edgeWeight D avoidFirst avoidSecond / 30 with hfloorDef
  -- level 1: some first atom carries a fifth of the mass
  have hfirst : ∃ first ∈ Finset.univ \ ({avoidFirst, avoidSecond} : Finset (Fin 7)),
      12 * floorValue ≤ ∑ second ∈ Finset.univ
          \ ({avoidFirst, avoidSecond, first} : Finset (Fin 7)),
        ∑ third ∈ Finset.univ
            \ ({avoidFirst, avoidSecond, first, second} : Finset (Fin 7)),
          directionTripleProduct D first second third := by
    refine bandPigeonholeGe (Finset.card_pos.mp (by rw [bandCardPairCompl havoidNe]; norm_num))
      ?_
    rw [bandCardPairCompl havoidNe, htotal, hfloorDef]
    push_cast
    ring_nf
    linarith
  obtain ⟨first, hfirstMemFull, hfirstSum⟩ := hfirst
  have hfirstMem := Finset.mem_sdiff.mp hfirstMemFull
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hfirstMem
  have hcardThree : (Finset.univ
      \ ({avoidFirst, avoidSecond, first} : Finset (Fin 7))).card = 4 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin,
      Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨havoidNe, fun hcontra => hfirstMem.2.1 hcontra.symm⟩),
      Finset.card_insert_of_notMem (by
        simp only [Finset.mem_singleton]
        exact fun hcontra => hfirstMem.2.2 hcontra.symm),
      Finset.card_singleton]
  -- level 2: some second atom carries a quarter of that
  have hsecond : ∃ second ∈ Finset.univ
      \ ({avoidFirst, avoidSecond, first} : Finset (Fin 7)),
      3 * floorValue ≤ ∑ third ∈ Finset.univ
          \ ({avoidFirst, avoidSecond, first, second} : Finset (Fin 7)),
        directionTripleProduct D first second third := by
    refine bandPigeonholeGe (Finset.card_pos.mp (by rw [hcardThree]; norm_num)) ?_
    rw [hcardThree]
    push_cast
    linarith
  obtain ⟨second, hsecondMemFull, hsecondSum⟩ := hsecond
  have hsecondMem := Finset.mem_sdiff.mp hsecondMemFull
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hsecondMem
  have hcardFour : (Finset.univ
      \ ({avoidFirst, avoidSecond, first, second} : Finset (Fin 7))).card = 3 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin,
      Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨havoidNe, fun hcontra => hfirstMem.2.1 hcontra.symm,
          fun hcontra => hsecondMem.2.1 hcontra.symm⟩),
      Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨fun hcontra => hfirstMem.2.2 hcontra.symm,
          fun hcontra => hsecondMem.2.2.1 hcontra.symm⟩),
      Finset.card_insert_of_notMem (by
        simp only [Finset.mem_singleton]
        exact fun hcontra => hsecondMem.2.2.2 hcontra.symm),
      Finset.card_singleton]
  -- level 3: some third atom carries a third of that
  have hthird : ∃ third ∈ Finset.univ
      \ ({avoidFirst, avoidSecond, first, second} : Finset (Fin 7)),
      floorValue ≤ directionTripleProduct D first second third := by
    refine bandPigeonholeGe (Finset.card_pos.mp (by rw [hcardFour]; norm_num)) ?_
    rw [hcardFour]
    push_cast
    linarith
  obtain ⟨third, hthirdMemFull, hthirdBound⟩ := hthird
  have hthirdMem := Finset.mem_sdiff.mp hthirdMemFull
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hthirdMem
  exact ⟨first, second, third, hfirstMem.2.1, hfirstMem.2.2, hsecondMem.2.1,
    hsecondMem.2.2.1, hthirdMem.2.1, hthirdMem.2.2.1,
    fun hcontra => hsecondMem.2.2.2 hcontra.symm,
    fun hcontra => hthirdMem.2.2.2.1 hcontra.symm,
    fun hcontra => hthirdMem.2.2.2.2 hcontra.symm, hthirdBound⟩

/-- **The coherent carrier of a failing configuration (task 3).**  For every
pair `{e, f}` of a failing configuration, the complementary five-set contains a
coherent triple with `P ≥ 1/135 + w_ef/30` AND `σ > 7/15 + w_ef/10`: the
five-set floor fed through the fence.  Both constants are exact
(`7/15 + w/10 = 4/9 + 3·(1/135 + w/30)`). -/
theorem exists_coherentCarrier_of_allFailing_avoidingPair_bandSeven (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7)
    (hleverage : ∀ atomIndex, leverageOf (D.atom atomIndex) = 3)
    (hfail : ∀ first second third : Fin 7, first ≠ second → first ≠ third →
      second ≠ third → ¬ Dominates D {first, second, third})
    {avoidFirst avoidSecond : Fin 7} (havoidNe : avoidFirst ≠ avoidSecond) :
    ∃ first second third : Fin 7,
      first ≠ avoidFirst ∧ first ≠ avoidSecond ∧ second ≠ avoidFirst ∧ second ≠ avoidSecond
        ∧ third ≠ avoidFirst ∧ third ≠ avoidSecond
        ∧ first ≠ second ∧ first ≠ third ∧ second ≠ third
        ∧ 1 / 135 + edgeWeight D avoidFirst avoidSecond / 30
            ≤ directionTripleProduct D first second third
        ∧ 7 / 15 + edgeWeight D avoidFirst avoidSecond / 10
            < directionTripleSigma D first second third := by
  obtain ⟨first, second, third, hfa, hfb, hsa, hsb, hta, htb, hfs, hft, hst, hfloor⟩ :=
    exists_tripleProduct_ge_floor_avoidingPair_bandSeven D huniform havoidNe
  have hfence := four_ninths_lt_orientedResidual_of_not_dominates_bandSeven D huniform
    hleverage hfs hft hst (hfail first second third hfs hft hst)
  rw [orientedTripleResidual_eq_sigma_sub] at hfence
  exact ⟨first, second, third, hfa, hfb, hsa, hsb, hta, htb, hfs, hft, hst, hfloor,
    by linarith⟩

/-! ## 4. The sigma gate and the four-set view (task 4)

The new per-triple gate `σ ≤ 1/3 ⟹ dominates`, its failing contrapositive,
and its complement reading: on a failing configuration every four-set is hot.
The engine is the landed AM-GM `27 P² ≤ σ³` against the factorisation
`27 σ³ − 81 σ² + 72 σ − 16 = (3σ − 1)(3σ − 4)²` — the σ-form of the
campaign's endpoint cubic `ρ(m) = 9 (m − 1/9)(m − 4/9)²` under `σ = 3m`. -/

/-- **THE SIGMA GATE.**  On the stratum a triple with `σ ≤ 1/3` dominates —
one scalar inequality, no sign information.  It subsumes the all-edges-`≤ 1/9`
light gate (`σ ≤ 3 · 1/9`) and is sharp: the basis+tetrapod witness's tetrapod
triple has `σ = 1/3` exactly and ties. -/
theorem dominates_triple_of_tripleSigma_le_third_bandSeven (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7)
    (hleverage : ∀ atomIndex, leverageOf (D.atom atomIndex) = 3)
    {tripleFirst tripleSecond tripleThird : Fin 7}
    (hfirstSecond : tripleFirst ≠ tripleSecond) (hfirstThird : tripleFirst ≠ tripleThird)
    (hsecondThird : tripleSecond ≠ tripleThird)
    (hsigma : directionTripleSigma D tripleFirst tripleSecond tripleThird ≤ 1 / 3) :
    Dominates D {tripleFirst, tripleSecond, tripleThird} := by
  refine (bandDominatesIff D huniform hleverage hfirstSecond hfirstThird hsecondThird).mpr ?_
  by_contra hcontra
  have hresidual : 4 / 9
      < orientedTripleResidual D tripleFirst tripleSecond tripleThird := not_le.mp hcontra
  have hamgm := twentySeven_mul_sq_tripleProduct_le_cube_squareSum
    (directionGram D tripleFirst tripleSecond) (directionGram D tripleFirst tripleThird)
    (directionGram D tripleSecond tripleThird)
  rw [orientedTripleResidual_eq_sigma_sub] at hresidual
  set sigmaValue := directionTripleSigma D tripleFirst tripleSecond tripleThird with hsigmaDef
  set productValue := directionTripleProduct D tripleFirst tripleSecond tripleThird
    with hproductDef
  have hsigmaExpand : sigmaValue = directionGram D tripleFirst tripleSecond ^ 2
      + directionGram D tripleFirst tripleThird ^ 2
      + directionGram D tripleSecond tripleThird ^ 2 := rfl
  have hproductExpand : productValue = directionGram D tripleFirst tripleSecond
      * directionGram D tripleFirst tripleThird
      * directionGram D tripleSecond tripleThird := rfl
  have hamgmSigma : 27 * productValue ^ 2 ≤ sigmaValue ^ 3 := by
    rw [hsigmaExpand, hproductExpand]
    exact hamgm
  -- the residual pushes 3P strictly below σ − 4/9 ≤ −1/9 < 0
  have hproductNeg : 3 * productValue < sigmaValue - 4 / 9 := by linarith
  have hgapNeg : sigmaValue - 4 / 9 < 0 := by linarith
  -- squares flip: (σ − 4/9)² < 9 P²
  have hsquareFlip : (sigmaValue - 4 / 9) ^ 2 < 9 * productValue ^ 2 := by
    nlinarith [mul_pos (show (0 : ℝ) < (sigmaValue - 4 / 9) - 3 * productValue by linarith)
      (show (0 : ℝ) < -(3 * productValue + (sigmaValue - 4 / 9)) by linarith)]
  -- the factorised endpoint cubic closes the trap
  have hkey : 0 ≤ (1 - 3 * sigmaValue) * (3 * sigmaValue - 4) ^ 2 :=
    mul_nonneg (by linarith) (sq_nonneg _)
  nlinarith [hkey, hsquareFlip, hamgmSigma]

/-- **The sigma floor of a failing configuration.**  A triple that does not
dominate has `σ > 1/3` — the contrapositive of the sigma gate, and the exact
constant at which the tetrapod tie sits. -/
theorem third_lt_tripleSigma_of_not_dominates_bandSeven (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7)
    (hleverage : ∀ atomIndex, leverageOf (D.atom atomIndex) = 3)
    {tripleFirst tripleSecond tripleThird : Fin 7}
    (hfirstSecond : tripleFirst ≠ tripleSecond) (hfirstThird : tripleFirst ≠ tripleThird)
    (hsecondThird : tripleSecond ≠ tripleThird)
    (hnot : ¬ Dominates D {tripleFirst, tripleSecond, tripleThird}) :
    1 / 3 < directionTripleSigma D tripleFirst tripleSecond tripleThird := by
  by_contra hcontra
  exact hnot (dominates_triple_of_tripleSigma_le_third_bandSeven D huniform hleverage
    hfirstSecond hfirstThird hsecondThird (not_lt.mp hcontra))

/-- **The four-set mass identity (task 4, trace level).**  The doubled pair
mass of the complementary four-set of a triple is `4/3 + 2 σ_T` — row law
only, no spectra.  It converts the sigma gate into a statement about the
OTHER four atoms: hot complement ⟺ heavy triple. -/
theorem sum_sum_edgeWeight_complementFourSet_bandSeven (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7)
    {tripleFirst tripleSecond tripleThird : Fin 7}
    (hfirstSecond : tripleFirst ≠ tripleSecond) (hfirstThird : tripleFirst ≠ tripleThird)
    (hsecondThird : tripleSecond ≠ tripleThird) :
    ∑ outerFirst ∈ Finset.univ
        \ ({tripleFirst, tripleSecond, tripleThird} : Finset (Fin 7)),
        ∑ outerSecond ∈ (Finset.univ
            \ ({tripleFirst, tripleSecond, tripleThird} : Finset (Fin 7))).erase outerFirst,
          edgeWeight D outerFirst outerSecond
      = 4 / 3 + 2 * directionTripleSigma D tripleFirst tripleSecond tripleThird := by
  have hinner : ∀ outerFirst ∈ Finset.univ
      \ ({tripleFirst, tripleSecond, tripleThird} : Finset (Fin 7)),
      ∑ outerSecond ∈ (Finset.univ
          \ ({tripleFirst, tripleSecond, tripleThird} : Finset (Fin 7))).erase outerFirst,
        edgeWeight D outerFirst outerSecond
      = 4 / 3 - edgeWeight D outerFirst tripleFirst - edgeWeight D outerFirst tripleSecond
        - edgeWeight D outerFirst tripleThird := by
    intro outerFirst houter
    have houterMem := Finset.mem_sdiff.mp houter
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at houterMem
    have hset : (Finset.univ
        \ ({tripleFirst, tripleSecond, tripleThird} : Finset (Fin 7))).erase outerFirst
        = Finset.univ \ insert outerFirst
            ({tripleFirst, tripleSecond, tripleThird} : Finset (Fin 7)) := by
      ext member
      simp only [Finset.mem_erase, Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert,
        Finset.mem_singleton, true_and]
      tauto
    have hdrop := bandRowDrop D huniform outerFirst
      ({tripleFirst, tripleSecond, tripleThird} : Finset (Fin 7))
      (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨houterMem.2.1, houterMem.2.2.1, houterMem.2.2.2⟩)
    rw [hset, hdrop, Finset.sum_insert (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hfirstSecond, hfirstThird⟩),
      Finset.sum_insert (by simp only [Finset.mem_singleton]; exact hsecondThird),
      Finset.sum_singleton]
    ring
  rw [Finset.sum_congr rfl hinner]
  have hcolumn : ∀ tripleAtom : Fin 7, tripleAtom = tripleFirst ∨ tripleAtom = tripleSecond
      ∨ tripleAtom = tripleThird →
      ∑ outerFirst ∈ Finset.univ
          \ ({tripleFirst, tripleSecond, tripleThird} : Finset (Fin 7)),
        edgeWeight D outerFirst tripleAtom
      = 4 / 3 - ∑ other ∈ ({tripleFirst, tripleSecond, tripleThird} :
          Finset (Fin 7)).erase tripleAtom, edgeWeight D tripleAtom other := by
    intro tripleAtom hcases
    have hmemTriple : tripleAtom ∈ ({tripleFirst, tripleSecond, tripleThird} :
        Finset (Fin 7)) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      exact hcases
    have hset : Finset.univ \ ({tripleFirst, tripleSecond, tripleThird} : Finset (Fin 7))
        = Finset.univ \ insert tripleAtom
            (({tripleFirst, tripleSecond, tripleThird} : Finset (Fin 7)).erase tripleAtom) := by
      rw [Finset.insert_erase hmemTriple]
    have hdrop := bandRowDrop D huniform tripleAtom
      (({tripleFirst, tripleSecond, tripleThird} : Finset (Fin 7)).erase tripleAtom)
      (Finset.notMem_erase tripleAtom _)
    rw [Finset.sum_congr rfl fun outerFirst _ => edgeWeight_comm D outerFirst tripleAtom,
      hset, hdrop]
  have hcolFirst := hcolumn tripleFirst (Or.inl rfl)
  have hcolSecond := hcolumn tripleSecond (Or.inr (Or.inl rfl))
  have hcolThird := hcolumn tripleThird (Or.inr (Or.inr rfl))
  have heraseFirst : ({tripleFirst, tripleSecond, tripleThird} :
      Finset (Fin 7)).erase tripleFirst = {tripleSecond, tripleThird} := by
    ext member
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hne, rfl | rfl | rfl⟩
      · exact absurd rfl hne
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rintro (rfl | rfl)
      · exact ⟨hfirstSecond.symm, Or.inr (Or.inl rfl)⟩
      · exact ⟨hfirstThird.symm, Or.inr (Or.inr rfl)⟩
  have heraseSecond : ({tripleFirst, tripleSecond, tripleThird} :
      Finset (Fin 7)).erase tripleSecond = {tripleFirst, tripleThird} := by
    ext member
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hne, rfl | rfl | rfl⟩
      · exact Or.inl rfl
      · exact absurd rfl hne
      · exact Or.inr rfl
    · rintro (rfl | rfl)
      · exact ⟨hfirstSecond, Or.inl rfl⟩
      · exact ⟨hsecondThird.symm, Or.inr (Or.inr rfl)⟩
  have heraseThird : ({tripleFirst, tripleSecond, tripleThird} :
      Finset (Fin 7)).erase tripleThird = {tripleFirst, tripleSecond} := by
    ext member
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hne, rfl | rfl | rfl⟩
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact absurd rfl hne
    · rintro (rfl | rfl)
      · exact ⟨hfirstThird, Or.inl rfl⟩
      · exact ⟨hsecondThird, Or.inr (Or.inl rfl)⟩
  rw [heraseFirst, Finset.sum_pair hsecondThird] at hcolFirst
  rw [heraseSecond, Finset.sum_pair hfirstThird] at hcolSecond
  rw [heraseThird, Finset.sum_pair hfirstSecond] at hcolThird
  have hcardCompl : (Finset.univ
      \ ({tripleFirst, tripleSecond, tripleThird} : Finset (Fin 7))).card = 4 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin,
      Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hfirstSecond, hfirstThird⟩),
      Finset.card_insert_of_notMem (by simp only [Finset.mem_singleton]; exact hsecondThird),
      Finset.card_singleton]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    Finset.sum_const, hcardCompl, hcolFirst, hcolSecond, hcolThird, nsmul_eq_mul]
  simp only [directionTripleSigma, edgeWeight]
  rw [directionGram_comm D tripleSecond tripleFirst,
    directionGram_comm D tripleThird tripleFirst,
    directionGram_comm D tripleThird tripleSecond]
  push_cast
  ring

/-- **Every four-set of a failing configuration is hot.**  If a triple does not
dominate, its complementary four atoms carry doubled pair mass strictly above
`2` (mass above `1`).  This is the trace-level content of
"`λmax(M[F]) > 1` at every four-set"; the constant is sharp at the tetrapod
tie, whose complement carries mass exactly `1`. -/
theorem two_lt_sum_sum_edgeWeight_complementFourSet_of_not_dominates_bandSeven
    (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7)
    (hleverage : ∀ atomIndex, leverageOf (D.atom atomIndex) = 3)
    {tripleFirst tripleSecond tripleThird : Fin 7}
    (hfirstSecond : tripleFirst ≠ tripleSecond) (hfirstThird : tripleFirst ≠ tripleThird)
    (hsecondThird : tripleSecond ≠ tripleThird)
    (hnot : ¬ Dominates D {tripleFirst, tripleSecond, tripleThird}) :
    2 < ∑ outerFirst ∈ Finset.univ
        \ ({tripleFirst, tripleSecond, tripleThird} : Finset (Fin 7)),
        ∑ outerSecond ∈ (Finset.univ
            \ ({tripleFirst, tripleSecond, tripleThird} : Finset (Fin 7))).erase outerFirst,
          edgeWeight D outerFirst outerSecond := by
  rw [sum_sum_edgeWeight_complementFourSet_bandSeven D huniform hfirstSecond hfirstThird
    hsecondThird]
  have hsigma := third_lt_tripleSigma_of_not_dominates_bandSeven D huniform hleverage
    hfirstSecond hfirstThird hsecondThird hnot
  linarith

/-- **The cold-complement gate.**  A triple whose complementary four-set
carries doubled pair mass at most `2` dominates. -/
theorem dominates_triple_of_sum_sum_edgeWeight_complementFourSet_le_bandSeven
    (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7)
    (hleverage : ∀ atomIndex, leverageOf (D.atom atomIndex) = 3)
    {tripleFirst tripleSecond tripleThird : Fin 7}
    (hfirstSecond : tripleFirst ≠ tripleSecond) (hfirstThird : tripleFirst ≠ tripleThird)
    (hsecondThird : tripleSecond ≠ tripleThird)
    (hcold : ∑ outerFirst ∈ Finset.univ
        \ ({tripleFirst, tripleSecond, tripleThird} : Finset (Fin 7)),
        ∑ outerSecond ∈ (Finset.univ
            \ ({tripleFirst, tripleSecond, tripleThird} : Finset (Fin 7))).erase outerFirst,
          edgeWeight D outerFirst outerSecond ≤ 2) :
    Dominates D {tripleFirst, tripleSecond, tripleThird} := by
  rw [sum_sum_edgeWeight_complementFourSet_bandSeven D huniform hfirstSecond hfirstThird
    hsecondThird] at hcold
  exact dominates_triple_of_tripleSigma_le_third_bandSeven D huniform hleverage hfirstSecond
    hfirstThird hsecondThird (by linarith)

/-! ## 5. Band brackets: min-edge caps and the Ramsey bottom

The exact endpoints of the middle band, as kernel facts about (hypothetical)
failing configurations. -/

/-- **The frustration cap** `(1 − 3μ)² − 4μ³ = (1 − μ)²(1 − 4μ)`: a triple of
nonpositive oriented product whose edges all reach `μ` has `μ ≤ 1/4`.
Share-free and rank-generic — only the Gram determinant cap is used.  Hence
on ANY design the min-edge range `(1/4, 1]` is coherent-only territory. -/
theorem edgeWeight_floor_le_quarter_of_tripleProduct_nonpos (D : WeightedDesign m k)
    {firstIndex secondIndex thirdIndex : Fin m}
    (hfirstPos : 0 < leverageOf (D.atom firstIndex))
    (hsecondPos : 0 < leverageOf (D.atom secondIndex))
    (hthirdPos : 0 < leverageOf (D.atom thirdIndex)) {floorValue : ℝ}
    (hfloorAB : floorValue ≤ edgeWeight D firstIndex secondIndex)
    (hfloorAC : floorValue ≤ edgeWeight D firstIndex thirdIndex)
    (hfloorBC : floorValue ≤ edgeWeight D secondIndex thirdIndex)
    (hfrustrated : directionTripleProduct D firstIndex secondIndex thirdIndex ≤ 0) :
    floorValue ≤ 1 / 4 := by
  rcases le_or_gt floorValue (1 / 4) with hdone | hquarter
  · exact hdone
  exfalso
  have hfloorPos : 0 < floorValue := by linarith
  have hdetCap := bandDetCap D hfirstPos hsecondPos hthirdPos
  set sigmaValue := directionTripleSigma D firstIndex secondIndex thirdIndex with hsigmaDef
  set productValue := directionTripleProduct D firstIndex secondIndex thirdIndex
    with hproductDef
  have hsigmaFloor : 3 * floorValue ≤ sigmaValue := by
    have hexpand : sigmaValue = edgeWeight D firstIndex secondIndex
        + edgeWeight D firstIndex thirdIndex + edgeWeight D secondIndex thirdIndex := rfl
    linarith [hexpand]
  have hproductSq := bandProductSq D firstIndex secondIndex thirdIndex
  have hcube : floorValue ^ 3 ≤ productValue ^ 2 := by
    rw [hproductSq]
    have hstepOne : floorValue * floorValue
        ≤ edgeWeight D firstIndex secondIndex * edgeWeight D firstIndex thirdIndex :=
      mul_le_mul hfloorAB hfloorAC hfloorPos.le
        (le_trans hfloorPos.le hfloorAB)
    have hstepTwo : floorValue * floorValue * floorValue
        ≤ edgeWeight D firstIndex secondIndex * edgeWeight D firstIndex thirdIndex
          * edgeWeight D secondIndex thirdIndex :=
      mul_le_mul hstepOne hfloorBC hfloorPos.le
        (mul_nonneg (edgeWeight_nonneg D _ _) (edgeWeight_nonneg D _ _))
    calc floorValue ^ 3 = floorValue * floorValue * floorValue := by ring
      _ ≤ _ := hstepTwo
  -- the deficit is squeezed: 0 ≤ −2P ≤ 1 − σ ≤ 1 − 3μ, so 4μ³ ≤ 4P² ≤ (1 − 3μ)²
  have hdeficit : -(2 * productValue) ≤ 1 - 3 * floorValue := by linarith
  have hdeficitNonneg : 0 ≤ -(2 * productValue) := by linarith
  have hsquare : 4 * productValue ^ 2 ≤ (1 - 3 * floorValue) ^ 2 := by
    have hmul := mul_self_le_mul_self hdeficitNonneg hdeficit
    nlinarith [hmul]
  -- factorised: 0 ≤ (1 − 3μ)² − 4μ³ = (1 − μ)²(1 − 4μ) with 1 − 4μ < 0
  have hfactor : 0 ≤ (1 - floorValue) ^ 2 * (1 - 4 * floorValue) := by
    nlinarith [hsquare, hcube]
  have hnegative : 1 - 4 * floorValue < 0 := by linarith
  have hvanishes : (1 - floorValue) ^ 2 = 0 := by
    have hnonpos : (1 - floorValue) ^ 2 * (1 - 4 * floorValue) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hnegative.le
    have hzero : (1 - floorValue) ^ 2 * (1 - 4 * floorValue) = 0 :=
      le_antisymm hnonpos hfactor
    rcases mul_eq_zero.mp hzero with hsq | hlin
    · exact hsq
    · exact absurd hlin hnegative.ne
  have hone : floorValue = 1 := by
    have hbase : 1 - floorValue = 0 := by
      have := sq_eq_zero_iff.mp hvanishes
      exact this
    linarith
  -- μ = 1 forces σ ≥ 3 against the determinant cap σ ≤ 1 + 2P ≤ 1
  rw [hone] at hsigmaFloor
  linarith

/-- **No stratum triple has all edges above `4/9`** — unconditionally, no
failing hypothesis, share `3/7` only.  All-heavy forces coherence
(`P > 8/27`), which the coherent cap `σ + (3/2)P ≤ 16/9` cannot carry at
`σ > 4/3`.  So `m ≤ 4/9` on the whole stratum, and the campaign's heavy gate
boundary is a structural ceiling, not just a domination fact. -/
theorem exists_edgeWeight_le_four_ninths_bandSeven (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7)
    {tripleFirst tripleSecond tripleThird : Fin 7}
    (hfirstSecond : tripleFirst ≠ tripleSecond) (hfirstThird : tripleFirst ≠ tripleThird)
    (hsecondThird : tripleSecond ≠ tripleThird) :
    edgeWeight D tripleFirst tripleSecond ≤ 4 / 9
      ∨ edgeWeight D tripleFirst tripleThird ≤ 4 / 9
      ∨ edgeWeight D tripleSecond tripleThird ≤ 4 / 9 := by
  by_contra hcontra
  simp only [not_or, not_le] at hcontra
  obtain ⟨hheavyAB, hheavyAC, hheavyBC⟩ := hcontra
  set sigmaValue := directionTripleSigma D tripleFirst tripleSecond tripleThird with hsigmaDef
  set productValue := directionTripleProduct D tripleFirst tripleSecond tripleThird
    with hproductDef
  have hsigmaExpand : sigmaValue = edgeWeight D tripleFirst tripleSecond
      + edgeWeight D tripleFirst tripleThird + edgeWeight D tripleSecond tripleThird := rfl
  have hsigmaHeavy : 4 / 3 < sigmaValue := by
    rw [hsigmaExpand]; linarith
  have hdetCap := bandDetCap D (bandLeveragePos D huniform tripleFirst)
    (bandLeveragePos D huniform tripleSecond) (bandLeveragePos D huniform tripleThird)
  have hproductPos : 0 < productValue := by linarith
  have hproductSq := bandProductSq D tripleFirst tripleSecond tripleThird
  have hcube : (64 : ℝ) / 729 ≤ productValue ^ 2 := by
    rw [hproductSq]
    have hstepOne : (4 : ℝ) / 9 * (4 / 9)
        ≤ edgeWeight D tripleFirst tripleSecond * edgeWeight D tripleFirst tripleThird :=
      mul_le_mul hheavyAB.le hheavyAC.le (by norm_num) (le_trans (by norm_num) hheavyAB.le)
    have hstepTwo : (4 : ℝ) / 9 * (4 / 9) * (4 / 9)
        ≤ edgeWeight D tripleFirst tripleSecond * edgeWeight D tripleFirst tripleThird
          * edgeWeight D tripleSecond tripleThird :=
      mul_le_mul hstepOne hheavyBC.le (by norm_num)
        (mul_nonneg (edgeWeight_nonneg D _ _) (edgeWeight_nonneg D _ _))
    linarith [hstepTwo]
  have hproductLarge : 8 / 27 ≤ productValue := by
    by_contra hcontraProduct
    have hproductSmall : productValue < 8 / 27 := not_le.mp hcontraProduct
    nlinarith [hcube,
      mul_pos (show (0 : ℝ) < 8 / 27 - productValue by linarith) hproductPos]
  have hcoherent := bandCoherentCap D huniform hfirstSecond hfirstThird hsecondThird
  linarith

/-- **On a failing configuration every triple has an edge strictly below
`4/9`.**  All edges `≥ 4/9` would freeze the triple to the `w ≡ 4/9`,
`P = 8/27` tie, which DOMINATES.  Together with the Ramsey bottom below this
pins the failing band to `m ∈ (1/9, 4/9)` exactly. -/
theorem exists_edgeWeight_lt_four_ninths_of_not_dominates_bandSeven (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7)
    (hleverage : ∀ atomIndex, leverageOf (D.atom atomIndex) = 3)
    {tripleFirst tripleSecond tripleThird : Fin 7}
    (hfirstSecond : tripleFirst ≠ tripleSecond) (hfirstThird : tripleFirst ≠ tripleThird)
    (hsecondThird : tripleSecond ≠ tripleThird)
    (hnot : ¬ Dominates D {tripleFirst, tripleSecond, tripleThird}) :
    edgeWeight D tripleFirst tripleSecond < 4 / 9
      ∨ edgeWeight D tripleFirst tripleThird < 4 / 9
      ∨ edgeWeight D tripleSecond tripleThird < 4 / 9 := by
  by_contra hcontra
  simp only [not_or, not_lt] at hcontra
  obtain ⟨hheavyAB, hheavyAC, hheavyBC⟩ := hcontra
  apply hnot
  refine (bandDominatesIff D huniform hleverage hfirstSecond hfirstThird hsecondThird).mpr ?_
  rw [orientedTripleResidual_eq_sigma_sub]
  set sigmaValue := directionTripleSigma D tripleFirst tripleSecond tripleThird with hsigmaDef
  set productValue := directionTripleProduct D tripleFirst tripleSecond tripleThird
    with hproductDef
  have hsigmaExpand : sigmaValue = edgeWeight D tripleFirst tripleSecond
      + edgeWeight D tripleFirst tripleThird + edgeWeight D tripleSecond tripleThird := rfl
  have hsigmaHeavy : 4 / 3 ≤ sigmaValue := by
    rw [hsigmaExpand]; linarith
  have hdetCap := bandDetCap D (bandLeveragePos D huniform tripleFirst)
    (bandLeveragePos D huniform tripleSecond) (bandLeveragePos D huniform tripleThird)
  have hproductPos : 0 < productValue := by linarith
  have hproductSq := bandProductSq D tripleFirst tripleSecond tripleThird
  have hcube : (64 : ℝ) / 729 ≤ productValue ^ 2 := by
    rw [hproductSq]
    have hstepOne : (4 : ℝ) / 9 * (4 / 9)
        ≤ edgeWeight D tripleFirst tripleSecond * edgeWeight D tripleFirst tripleThird :=
      mul_le_mul hheavyAB hheavyAC (by norm_num) (le_trans (by norm_num) hheavyAB)
    have hstepTwo : (4 : ℝ) / 9 * (4 / 9) * (4 / 9)
        ≤ edgeWeight D tripleFirst tripleSecond * edgeWeight D tripleFirst tripleThird
          * edgeWeight D tripleSecond tripleThird :=
      mul_le_mul hstepOne hheavyBC (by norm_num)
        (mul_nonneg (edgeWeight_nonneg D _ _) (edgeWeight_nonneg D _ _))
    linarith [hstepTwo]
  have hproductLarge : 8 / 27 ≤ productValue := by
    by_contra hcontraProduct
    have hproductSmall : productValue < 8 / 27 := not_le.mp hcontraProduct
    nlinarith [hcube,
      mul_pos (show (0 : ℝ) < 8 / 27 - productValue by linarith) hproductPos]
  have hcoherent := bandCoherentCap D huniform hfirstSecond hfirstThird hsecondThird
  -- σ ≤ 16/9 − (3/2)·(8/27) = 4/3 and 3P ≥ 8/9, so σ − 3P ≤ 4/9
  linarith

/-- **The Ramsey bottom of the band.**  A failing configuration contains a
triangle with ALL THREE edges strictly above `1/9`, i.e. `m > 1/9`.
`R(3,3) ≤ 6` on the seven atoms: either three light edges meet at an atom —
then two of their far ends join lightly into an all-light triple (`σ ≤ 1/3`,
dominates by the sigma gate) or that pair is the heavy triangle's base — or
four heavy edges meet at an atom and any light inner pair rebuilds an
all-light triple the same way. -/
theorem exists_heavyTriangle_of_allFailing_bandSeven (D : WeightedDesign 7 3)
    (huniform : ∀ atomIndex, atomShare D atomIndex = 3 / 7)
    (hleverage : ∀ atomIndex, leverageOf (D.atom atomIndex) = 3)
    (hfail : ∀ first second third : Fin 7, first ≠ second → first ≠ third →
      second ≠ third → ¬ Dominates D {first, second, third}) :
    ∃ first second third : Fin 7, first ≠ second ∧ first ≠ third ∧ second ≠ third
      ∧ 1 / 9 < edgeWeight D first second ∧ 1 / 9 < edgeWeight D first third
      ∧ 1 / 9 < edgeWeight D second third := by
  -- no all-light triple survives on a failing configuration
  have hnoLight : ∀ first second third : Fin 7, first ≠ second → first ≠ third →
      second ≠ third → edgeWeight D first second ≤ 1 / 9 →
      edgeWeight D first third ≤ 1 / 9 → edgeWeight D second third ≤ 1 / 9 → False := by
    intro first second third hfs hft hst hlightAB hlightAC hlightBC
    have hsigma : directionTripleSigma D first second third ≤ 1 / 3 := by
      have hexpand : directionTripleSigma D first second third
          = edgeWeight D first second + edgeWeight D first third
            + edgeWeight D second third := rfl
      linarith [hexpand]
    exact hfail first second third hfs hft hst
      (dominates_triple_of_tripleSigma_le_third_bandSeven D huniform hleverage hfs hft hst
        hsigma)
  classical
  set hub : Fin 7 := 0 with hhubDef
  set lightSet : Finset (Fin 7) :=
    (Finset.univ.erase hub).filter (fun other => edgeWeight D hub other ≤ 1 / 9)
    with hlightDef
  have hmemLight : ∀ other ∈ lightSet, other ≠ hub ∧ edgeWeight D hub other ≤ 1 / 9 := by
    intro other hother
    have hmem := Finset.mem_filter.mp hother
    exact ⟨(Finset.mem_erase.mp hmem.1).1, hmem.2⟩
  rcases le_or_gt 3 lightSet.card with hbig | hsmall
  · -- three light edges at the hub
    obtain ⟨lightTriple, hsubset, hcardThree⟩ := Finset.exists_subset_card_eq hbig
    obtain ⟨endFirst, endSecond, endThird, hFS, hFT, hST, hset⟩ :=
      Finset.card_eq_three.mp hcardThree
    have hmemFirst := hmemLight endFirst (hsubset (hset ▸ Finset.mem_insert_self _ _))
    have hmemSecond := hmemLight endSecond (hsubset (hset ▸ Finset.mem_insert_of_mem
      (Finset.mem_insert_self _ _)))
    have hmemThird := hmemLight endThird (hsubset (hset ▸ Finset.mem_insert_of_mem
      (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))))
    -- if any far edge is light, an all-light triple appears; otherwise heavy triangle
    rcases le_or_gt (edgeWeight D endFirst endSecond) (1 / 9) with hlightFS | hheavyFS
    · exact absurd (hnoLight hub endFirst endSecond hmemFirst.1.symm hmemSecond.1.symm hFS
        hmemFirst.2 hmemSecond.2 hlightFS) not_false
    rcases le_or_gt (edgeWeight D endFirst endThird) (1 / 9) with hlightFT | hheavyFT
    · exact absurd (hnoLight hub endFirst endThird hmemFirst.1.symm hmemThird.1.symm hFT
        hmemFirst.2 hmemThird.2 hlightFT) not_false
    rcases le_or_gt (edgeWeight D endSecond endThird) (1 / 9) with hlightST | hheavyST
    · exact absurd (hnoLight hub endSecond endThird hmemSecond.1.symm hmemThird.1.symm hST
        hmemSecond.2 hmemThird.2 hlightST) not_false
    exact ⟨endFirst, endSecond, endThird, hFS, hFT, hST, hheavyFS, hheavyFT, hheavyST⟩
  · -- at least four heavy edges at the hub
    set heavySet : Finset (Fin 7) :=
      (Finset.univ.erase hub).filter (fun other => ¬ edgeWeight D hub other ≤ 1 / 9)
      with hheavyDef
    have hsplit : lightSet.card + heavySet.card = 6 := by
      rw [hlightDef, hheavyDef, Finset.card_filter_add_card_filter_not,
        Finset.card_erase_of_mem (Finset.mem_univ hub), Finset.card_univ, Fintype.card_fin]
    have hheavyBig : 3 ≤ heavySet.card := by omega
    obtain ⟨heavyTriple, hsubset, hcardThree⟩ := Finset.exists_subset_card_eq hheavyBig
    obtain ⟨endFirst, endSecond, endThird, hFS, hFT, hST, hset⟩ :=
      Finset.card_eq_three.mp hcardThree
    have hmemHeavy : ∀ other ∈ heavySet, other ≠ hub ∧ 1 / 9 < edgeWeight D hub other := by
      intro other hother
      have hmem := Finset.mem_filter.mp hother
      exact ⟨(Finset.mem_erase.mp hmem.1).1, not_le.mp hmem.2⟩
    have hmemFirst := hmemHeavy endFirst (hsubset (hset ▸ Finset.mem_insert_self _ _))
    have hmemSecond := hmemHeavy endSecond (hsubset (hset ▸ Finset.mem_insert_of_mem
      (Finset.mem_insert_self _ _)))
    have hmemThird := hmemHeavy endThird (hsubset (hset ▸ Finset.mem_insert_of_mem
      (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))))
    -- a heavy inner edge closes a heavy triangle with the hub; all-light is impossible
    rcases lt_or_ge (1 / 9 : ℝ) (edgeWeight D endFirst endSecond) with hheavyFS | hlightFS
    · exact ⟨hub, endFirst, endSecond, hmemFirst.1.symm, hmemSecond.1.symm, hFS,
        hmemFirst.2, hmemSecond.2, hheavyFS⟩
    rcases lt_or_ge (1 / 9 : ℝ) (edgeWeight D endFirst endThird) with hheavyFT | hlightFT
    · exact ⟨hub, endFirst, endThird, hmemFirst.1.symm, hmemThird.1.symm, hFT,
        hmemFirst.2, hmemThird.2, hheavyFT⟩
    rcases lt_or_ge (1 / 9 : ℝ) (edgeWeight D endSecond endThird) with hheavyST | hlightST
    · exact ⟨hub, endSecond, endThird, hmemSecond.1.symm, hmemThird.1.symm, hST,
        hmemSecond.2, hmemThird.2, hheavyST⟩
    exact absurd (hnoLight endFirst endSecond endThird hFS hFT hST hlightFS hlightFT
      hlightST) not_false

end Gtz
