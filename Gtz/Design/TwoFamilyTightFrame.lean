/-
# The one-frame gate system at a tie: the coupling floor, the equality law,
and the dual-conic polarity of the stress-free `(6,3)` stratum

Everything here lives on a single frame.  Split each atom `g` along a unit
axis, `g = a . axis + u` with `u` in the axis plane; the gate form of a
`rank`-subset `C` at that axis is `(A_C - 1) (P_C - I) - d_C d_C^T` with axis
mass `A_C = sum a^2`, plane block `P_C = sum u u^T`, and coupling vector
`d_C = sum_{x in C} a_x u_x`.

* **The master extraction** (`exists_axisGateFailure_of_isTie`): at a tie,
  every `rank`-subset with axis mass above one fails its gate somewhere on
  the axis plane.  The tight-plane exchange system
  (`exists_gateFailure_of_isTie`) and the insert-plane pair completion
  (`exists_insertGateFailure_of_isTie`) are both instances — the former at
  the tight axis of a dominating triple, the latter at a normalized insert
  atom.

* **The eigenvector collapse** (`sum_axisPairing_smul_atom_eq_axis_of_tight`):
  a weakly dominating subset's coupling vector at its own tight axis is the
  axis itself — the tight subset has coupling shadow exactly zero, which is
  why it can dominate its plane with margin and still fail to be PD.

* **The coupling floor** (`couplingShadow_floor_of_isTie_of_planarMargin`):
  at a tie, a `rank`-subset with axis mass `A > 1` whose atoms dominate the
  axis plane with margin ratio `mu` must have coupling shadow of squared
  length at least `mu (A - 1)`:  `mu (A - 1) + A^2 <= |sum (g.axis) g|^2`.

* **The equality law** (`exists_axisGateEquality_of_isTie_of_dominates`): at
  a tie every WEAKLY DOMINATING `rank`-subset sits exactly ON the gate
  boundary of every unit axis whose mass differs from one — the tie makes its
  gap singular, and the kernel vector's plane shadow witnesses
  `(A - 1) excess = coupling^2` with equality.

* **The dual-conic instrument.**  On the stress-free `(6,3)` stratum the six
  atom matrices are a basis of `Sym(3)`, so each atom `x` owns a UNIQUE conic
  `K_x` with `g_c^T K_x g_c = delta_cx` — the conic through the OTHER FIVE
  atom directions, normalized at `x`: existence
  (`exists_dualConic_of_stressFree`, one Veronese-grid inversion), uniqueness
  (`dualConic_unique_of_stressFree`, the difference is a conic through all
  six directions), the trace law `tr K_x = t_x` (Parseval,
  `trace_eq_weight_of_atomPairing` — any size, any rank), and the gap pairing
  `tr((S_C - 1) K_x) = 1_C(x) - t_x` for EVERY subset
  (`trace_gapPairing_of_atomPairing`).

* **The polarity law**
  (`sixThree_exists_dominating_with_indefinite_outsider_conics_of_isTie`): at
  a stress-free `(6,3)` tie, every outsider of a dominating triple has its
  dual conic INDEFINITE, with the negative direction ORTHOGONAL TO THE TIGHT
  KERNEL — negative on the tight range itself: the gap is PSD while its
  pairing against the outsider conic is `-t_x < 0`, so a factorization
  `S_Q - 1 = F^T F` (the C*-square-root pattern of `Gtz.LinAlg.PsdKit`)
  locates a negative diagonal entry of `F K_x F^T`
  (`exists_negDirection_orthKernel_of_trace_mul_neg`), while
  `tr K_x = t_x > 0` supplies the positive direction.

* **The five-point degeneracy** (`exists_conic_through_five`,
  `dualConic_never_unique_fivePoints`): five directions always lie on a
  nonzero conic, so a pairing-normalized conic of a five-atom family shifts
  freely along it — the dual frame exists canonically ONLY at six stress-free
  atoms, and every dual-frame statement degenerates at `(5,3)`.

* **The dominating-stratum overlap law**
  (`frameOverlap_floor_of_dominates_pair`): any two weakly dominating subsets
  satisfy `sum (g_c . g_c')^2 >= sum_C lev + sum_C' lev - rank` — the
  pairwise quadratic constraint on the tie's equality stratum.

* **The outsider deficiency**
  (`exists_deficientDirection_outsiderTriple_of_isTie`): at a `(6,3)` tie the
  complement of every dominating triple admits a jointly deficient direction.
  The statement's arity needs six atoms — at five points the complement of a
  triple is a pair.

* **The gate trichotomy** (`dominates_or_strictGateOvershoot_of_axisMassExcess`,
  `sixThree_complementaryTightPair_or_overshoot_of_isTie`): a subset with
  axis mass above one is PD (gate strict everywhere), weakly dominating (gate
  `<=` everywhere, with equality somewhere by the equality law), or
  overshoots the gate strictly somewhere
  (`exists_strictGateOvershoot_of_not_dominates`).

* **The collar criteria** (`posDef_insertCompletion_of_planeMargin`,
  `posDef_insertCompletion_of_leverage_gt`): a pair dominating an insert's
  orthogonal plane with margin ratio `m` completes to a strictly dominating
  triple as soon as the coupling is below `m lev (lev - 1)` — equivalently
  whenever the insert's leverage exceeds `1 + coupling / m`.  Leverage grows
  like `1/w` as the insert's weight `w` tends to zero, so this covers an
  explicit collar near every light-weight boundary face.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.LinAlg.PsdKit
import Gtz.Certificates.ResidueDissolution
import Gtz.Design.StressFreeNormalizer
import Gtz.Design.StressFreeStratum
import Gtz.Design.TightAxisPairBudget
import Gtz.Design.InsertPlaneCompletion
import Gtz.Ties.TieBasisWindow

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace Gtz

open Matrix

variable {size rank : ℕ}

/-! ## Part 1: the master gate-failure extraction — the two families as one -/

/-- **THE MASTER EXTRACTION.**  At a tie, for every `rank`-subset and every unit
axis along which the subset carries axis mass above one, some direction of the
axis plane defeats the axis-split coupling gate.  The tight-plane exchange
system and the insert-plane pair-completion system are both instances: the
former at the tight axis of a dominating triple, the latter at the normalized
insert atom. -/
theorem exists_axisGateFailure_of_isTie (design : WeightedDesign size rank)
    (htie : IsTie design) {selected : Finset (Fin size)} (hcard : selected.card = rank)
    {axis : Fin rank → ℝ} (hunit : axis ⬝ᵥ axis = 1)
    (haxisExcess : 1 < ∑ atomIndex ∈ selected, (design.atom atomIndex ⬝ᵥ axis) ^ 2) :
    ∃ planar : Fin rank → ℝ, planar ⬝ᵥ axis = 0 ∧ planar ≠ 0
      ∧ ((∑ atomIndex ∈ selected, (design.atom atomIndex ⬝ᵥ axis) ^ 2) - 1)
            * ((∑ atomIndex ∈ selected, (design.atom atomIndex ⬝ᵥ planar) ^ 2)
              - planar ⬝ᵥ planar)
          ≤ (∑ atomIndex ∈ selected,
              (design.atom atomIndex ⬝ᵥ axis) * (design.atom atomIndex ⬝ᵥ planar)) ^ 2 := by
  by_contra hnoWitness
  push Not at hnoWitness
  exact htie.2 selected hcard
    (posDef_gap_of_axisSplit_coupling design selected hunit haxisExcess
      (fun planar hplanarOrth hplanarNe => hnoWitness planar hplanarOrth hplanarNe))

/-- **THE EIGENVECTOR COLLAPSE OF THE TIGHT COUPLING.**  The coupling vector
`sum (g . axis) g` of a weakly dominating subset at its own tight axis is the
axis itself — the coupling shadow of the tight subset is exactly zero, which is
why a tight triple can dominate its plane with margin and still fail to be PD
while every other subset pays the coupling floor below. -/
theorem sum_axisPairing_smul_atom_eq_axis_of_tight (design : WeightedDesign size rank)
    {selected : Finset (Fin size)} (hdominates : Dominates design selected)
    {axis : Fin rank → ℝ}
    (htight : axis ⬝ᵥ ((subsetSum design selected - 1) *ᵥ axis) = 0) :
    ∑ atomIndex ∈ selected, (design.atom atomIndex ⬝ᵥ axis) • design.atom atomIndex
      = axis := by
  rw [← subsetSum_mulVec_eq_sum]
  exact tightDirection_isEigenvector design hdominates htight

/-- **THE COUPLING FLOOR.**  At a tie, a `rank`-subset with unit-axis mass
`A > 1` whose atoms dominate the axis plane with margin ratio `mu` must carry a
coupling vector `sum (g . axis) g` of squared length at least `mu (A - 1) + A^2`
— equivalently, coupling shadow (component orthogonal to the axis) of squared
length at least `mu (A - 1)`.  Cauchy–Schwarz scalarization of the master gate
failure: at the witness direction the plane excess is at least `mu |planar|^2`
while the gate's coupling is the linear pairing of the coupling vector with the
witness. -/
theorem couplingShadow_floor_of_isTie_of_planarMargin (design : WeightedDesign size rank)
    (htie : IsTie design) {selected : Finset (Fin size)} (hcard : selected.card = rank)
    {axis : Fin rank → ℝ} (hunit : axis ⬝ᵥ axis = 1)
    (haxisExcess : 1 < ∑ atomIndex ∈ selected, (design.atom atomIndex ⬝ᵥ axis) ^ 2)
    {marginRatio : ℝ}
    (hmargin : ∀ planar : Fin rank → ℝ, planar ⬝ᵥ axis = 0 →
      (1 + marginRatio) * (planar ⬝ᵥ planar)
        ≤ ∑ atomIndex ∈ selected, (design.atom atomIndex ⬝ᵥ planar) ^ 2) :
    marginRatio * ((∑ atomIndex ∈ selected, (design.atom atomIndex ⬝ᵥ axis) ^ 2) - 1)
        + (∑ atomIndex ∈ selected, (design.atom atomIndex ⬝ᵥ axis) ^ 2) ^ 2
      ≤ (∑ atomIndex ∈ selected, (design.atom atomIndex ⬝ᵥ axis) • design.atom atomIndex)
          ⬝ᵥ (∑ atomIndex ∈ selected,
              (design.atom atomIndex ⬝ᵥ axis) • design.atom atomIndex) := by
  obtain ⟨planar, hplanarOrth, hplanarNe, hgate⟩ :=
    exists_axisGateFailure_of_isTie design htie hcard hunit haxisExcess
  set axisMass : ℝ := ∑ atomIndex ∈ selected, (design.atom atomIndex ⬝ᵥ axis) ^ 2
    with haxisMassDef
  set couplingVec : Fin rank → ℝ :=
    ∑ atomIndex ∈ selected, (design.atom atomIndex ⬝ᵥ axis) • design.atom atomIndex
    with hcouplingVecDef
  have hcouplingEq : ∑ atomIndex ∈ selected,
      (design.atom atomIndex ⬝ᵥ axis) * (design.atom atomIndex ⬝ᵥ planar)
        = couplingVec ⬝ᵥ planar := by
    rw [hcouplingVecDef, sum_dotProduct]
    exact Finset.sum_congr rfl fun atomIndex _ => by
      rw [smul_dotProduct, smul_eq_mul]
  have hmassEq : couplingVec ⬝ᵥ axis = axisMass := by
    rw [hcouplingVecDef, sum_dotProduct, haxisMassDef]
    exact Finset.sum_congr rfl fun atomIndex _ => by
      rw [smul_dotProduct, smul_eq_mul, pow_two]
  have hexcessFloor : marginRatio * (planar ⬝ᵥ planar)
      ≤ (∑ atomIndex ∈ selected, (design.atom atomIndex ⬝ᵥ planar) ^ 2)
        - planar ⬝ᵥ planar := by
    linarith [hmargin planar hplanarOrth]
  have hchain : marginRatio * (axisMass - 1) * (planar ⬝ᵥ planar)
      ≤ (couplingVec ⬝ᵥ planar) ^ 2 := by
    calc marginRatio * (axisMass - 1) * (planar ⬝ᵥ planar)
        = (axisMass - 1) * (marginRatio * (planar ⬝ᵥ planar)) := by ring
      _ ≤ (axisMass - 1)
            * ((∑ atomIndex ∈ selected, (design.atom atomIndex ⬝ᵥ planar) ^ 2)
              - planar ⬝ᵥ planar) :=
          mul_le_mul_of_nonneg_left hexcessFloor (by linarith)
      _ ≤ (∑ atomIndex ∈ selected,
            (design.atom atomIndex ⬝ᵥ axis) * (design.atom atomIndex ⬝ᵥ planar)) ^ 2 :=
          hgate
      _ = (couplingVec ⬝ᵥ planar) ^ 2 := by rw [hcouplingEq]
  set shadowVec : Fin rank → ℝ := couplingVec - axisMass • axis with hshadowDef
  have hshadowPairing : shadowVec ⬝ᵥ planar = couplingVec ⬝ᵥ planar := by
    rw [hshadowDef, sub_dotProduct, smul_dotProduct, smul_eq_mul,
      dotProduct_comm axis planar, hplanarOrth, mul_zero, sub_zero]
  have hshadowNorm : shadowVec ⬝ᵥ shadowVec
      = couplingVec ⬝ᵥ couplingVec - axisMass ^ 2 := by
    have haxisCoupling : axis ⬝ᵥ couplingVec = axisMass := by
      rw [dotProduct_comm]
      exact hmassEq
    rw [hshadowDef, sub_dotProduct, dotProduct_sub, dotProduct_sub, smul_dotProduct,
      dotProduct_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul,
      smul_eq_mul, smul_eq_mul, hmassEq, haxisCoupling, hunit]
    ring
  have hplanarPos : 0 < planar ⬝ᵥ planar := dotProduct_self_pos hplanarNe
  have hcancel : marginRatio * (axisMass - 1) ≤ shadowVec ⬝ᵥ shadowVec := by
    have hproduct : marginRatio * (axisMass - 1) * (planar ⬝ᵥ planar)
        ≤ (shadowVec ⬝ᵥ shadowVec) * (planar ⬝ᵥ planar) := by
      calc marginRatio * (axisMass - 1) * (planar ⬝ᵥ planar)
          ≤ (couplingVec ⬝ᵥ planar) ^ 2 := hchain
        _ = (shadowVec ⬝ᵥ planar) ^ 2 := by rw [hshadowPairing]
        _ ≤ (shadowVec ⬝ᵥ shadowVec) * (planar ⬝ᵥ planar) :=
            dotProduct_sq_le_mul shadowVec planar
    exact le_of_mul_le_mul_right hproduct hplanarPos
  have hfinal : marginRatio * (axisMass - 1)
      ≤ couplingVec ⬝ᵥ couplingVec - axisMass ^ 2 := by
    rw [← hshadowNorm]
    exact hcancel
  linarith [hfinal]

/-! ## Part 1e: the equality law on the dominating stratum

At a tie every weakly dominating `rank`-subset has a SINGULAR gap
(`det_gap_eq_zero_of_isTie_of_dominates`), and singularity read in any axis
frame is gate failure WITH EQUALITY: the kernel vector's plane shadow
witnesses `(A - 1) * excess = coupling^2` exactly.  The one-frame tie system
is therefore `spend_C >= A_C - 1` for every frame-visible triple, with
equality precisely on the dominating stratum. -/

/-- The bilinear gap pairing: `axis^T (S_C - 1) w` in dot-product vocabulary. -/
theorem gapPairing_bilinear (design : WeightedDesign size rank)
    (selected : Finset (Fin size)) (leftProbe rightProbe : Fin rank → ℝ) :
    leftProbe ⬝ᵥ ((subsetSum design selected - 1) *ᵥ rightProbe)
      = (∑ atomIndex ∈ selected,
          (design.atom atomIndex ⬝ᵥ leftProbe) * (design.atom atomIndex ⬝ᵥ rightProbe))
        - leftProbe ⬝ᵥ rightProbe := by
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub,
    subsetSum_mulVec_eq_sum, dotProduct_sum]
  congr 1
  exact Finset.sum_congr rfl fun atomIndex _ => by
    rw [dotProduct_smul, smul_eq_mul, dotProduct_comm leftProbe (design.atom atomIndex),
      mul_comm]

/-- **THE EQUALITY LAW.**  At a tie, every weakly dominating `rank`-subset
sits EXACTLY on the axis-split gate boundary of every unit axis along which
its mass differs from one: some nonzero plane direction — the plane shadow of
the gap's kernel vector — satisfies `(A - 1) * excess = coupling^2` with
equality.  The master extraction gives `<=` for every above-mass subset; the
dominating stratum is pinned to `=`. -/
theorem exists_axisGateEquality_of_isTie_of_dominates (design : WeightedDesign size rank)
    (htie : IsTie design) {selected : Finset (Fin size)} (hcard : selected.card = rank)
    (hdominates : Dominates design selected) {axis : Fin rank → ℝ}
    (hunit : axis ⬝ᵥ axis = 1)
    (haxisMassNeOne : (∑ atomIndex ∈ selected, (design.atom atomIndex ⬝ᵥ axis) ^ 2) ≠ 1) :
    ∃ planar : Fin rank → ℝ, planar ⬝ᵥ axis = 0 ∧ planar ≠ 0
      ∧ ((∑ atomIndex ∈ selected, (design.atom atomIndex ⬝ᵥ axis) ^ 2) - 1)
            * ((∑ atomIndex ∈ selected, (design.atom atomIndex ⬝ᵥ planar) ^ 2)
              - planar ⬝ᵥ planar)
          = (∑ atomIndex ∈ selected,
              (design.atom atomIndex ⬝ᵥ axis) * (design.atom atomIndex ⬝ᵥ planar)) ^ 2 := by
  have hdetZero : (subsetSum design selected - 1).det = 0 :=
    det_gap_eq_zero_of_isTie_of_dominates design htie hcard hdominates
  obtain ⟨kernelVec, hkernelNe, hkernelZero⟩ :=
    Matrix.exists_mulVec_eq_zero_iff.mpr hdetZero
  set axisCoord : ℝ := kernelVec ⬝ᵥ axis with haxisCoordDef
  set planar : Fin rank → ℝ := kernelVec - axisCoord • axis with hplanarDef
  have hplanarOrth : planar ⬝ᵥ axis = 0 := by
    rw [hplanarDef, sub_dotProduct, smul_dotProduct, smul_eq_mul, hunit, haxisCoordDef]
    ring
  set gapMatrix : Matrix (Fin rank) (Fin rank) ℝ := subsetSum design selected - 1
    with hgapDef
  have haxisSelf : axis ⬝ᵥ (gapMatrix *ᵥ axis)
      = (∑ atomIndex ∈ selected, (design.atom atomIndex ⬝ᵥ axis) ^ 2) - 1 := by
    rw [hgapDef, gapPairing_bilinear, hunit]
    congr 1
    exact Finset.sum_congr rfl fun atomIndex _ => (pow_two _).symm
  have hpairKernel : ∀ probe : Fin rank → ℝ, probe ⬝ᵥ (gapMatrix *ᵥ kernelVec) = 0 := by
    intro probe
    rw [hgapDef, hkernelZero, dotProduct_zero]
  have hgapSymm : ∀ leftProbe rightProbe : Fin rank → ℝ,
      leftProbe ⬝ᵥ (gapMatrix *ᵥ rightProbe) = rightProbe ⬝ᵥ (gapMatrix *ᵥ leftProbe) := by
    intro leftProbe rightProbe
    rw [hgapDef, gapPairing_bilinear, gapPairing_bilinear, dotProduct_comm]
    congr 1
    exact Finset.sum_congr rfl fun atomIndex _ => by ring
  have hplanarNe : planar ≠ 0 := by
    intro hplanarZero
    have hkernelIsAxis : kernelVec = axisCoord • axis := by
      have hrecover : kernelVec = planar + axisCoord • axis := by
        rw [hplanarDef]
        abel
      rw [hrecover, hplanarZero, zero_add]
    have haxisCoordNe : axisCoord ≠ 0 := by
      intro hzero
      exact hkernelNe (by rw [hkernelIsAxis, hzero, zero_smul])
    have haxisKernel : gapMatrix *ᵥ axis = 0 := by
      have hscaled : gapMatrix *ᵥ (axisCoord • axis) = 0 := by
        rw [← hkernelIsAxis, hgapDef, hkernelZero]
      rw [Matrix.mulVec_smul] at hscaled
      exact smul_eq_zero_iff_right haxisCoordNe |>.mp hscaled
    have hmassOne : (∑ atomIndex ∈ selected, (design.atom atomIndex ⬝ᵥ axis) ^ 2) - 1
        = 0 := by
      rw [← haxisSelf, haxisKernel, dotProduct_zero]
    exact haxisMassNeOne (by linarith)
  -- the coupling collapses to the kernel relation
  have hcouplingValue : (∑ atomIndex ∈ selected,
      (design.atom atomIndex ⬝ᵥ axis) * (design.atom atomIndex ⬝ᵥ planar))
        = axis ⬝ᵥ (gapMatrix *ᵥ planar) := by
    rw [hgapDef, gapPairing_bilinear, dotProduct_comm axis planar, hplanarOrth,
      sub_zero]
  have hcouplingKernel : axis ⬝ᵥ (gapMatrix *ᵥ planar)
      = -(axisCoord
          * ((∑ atomIndex ∈ selected, (design.atom atomIndex ⬝ᵥ axis) ^ 2) - 1)) := by
    have hsplit : gapMatrix *ᵥ planar
        = gapMatrix *ᵥ kernelVec - axisCoord • (gapMatrix *ᵥ axis) := by
      rw [hplanarDef, Matrix.mulVec_sub, Matrix.mulVec_smul]
    rw [hsplit, dotProduct_sub, dotProduct_smul, smul_eq_mul, hpairKernel axis,
      zero_sub, haxisSelf]
  -- the plane excess collapses to the kernel relation
  have hexcessValue : (∑ atomIndex ∈ selected, (design.atom atomIndex ⬝ᵥ planar) ^ 2)
      - planar ⬝ᵥ planar = planar ⬝ᵥ (gapMatrix *ᵥ planar) := by
    rw [hgapDef, gapPairing_bilinear]
    congr 1
    exact Finset.sum_congr rfl fun atomIndex _ => pow_two _
  have hexcessKernel : planar ⬝ᵥ (gapMatrix *ᵥ planar)
      = axisCoord ^ 2
          * ((∑ atomIndex ∈ selected, (design.atom atomIndex ⬝ᵥ axis) ^ 2) - 1) := by
    have hsplit : gapMatrix *ᵥ planar
        = gapMatrix *ᵥ kernelVec - axisCoord • (gapMatrix *ᵥ axis) := by
      rw [hplanarDef, Matrix.mulVec_sub, Matrix.mulVec_smul]
    rw [hsplit, dotProduct_sub, dotProduct_smul, smul_eq_mul, hpairKernel planar,
      zero_sub]
    have hswap : planar ⬝ᵥ (gapMatrix *ᵥ axis) = axis ⬝ᵥ (gapMatrix *ᵥ planar) :=
      hgapSymm planar axis
    rw [hswap, hcouplingKernel]
    ring
  refine ⟨planar, hplanarOrth, hplanarNe, ?_⟩
  rw [hexcessValue, hexcessKernel, hcouplingValue, hcouplingKernel]
  ring

/-- **THE FRAME-OVERLAP FLOOR** — the pullback-cone polarity in scalar form:
every atom of the design pairs with a weakly dominating subset's gap
nonnegatively, `lev_x <= sum_{c in C} (g_x . g_c)^2`.  These are exactly the
K-frame coordinates `sigma_x(C)` of the gap being componentwise nonnegative
on the dominating stratum (`S_C - 1 = sum_x sigma_x(C) K_x`). -/
theorem leverage_le_frameOverlap_of_dominates (design : WeightedDesign size rank)
    {selected : Finset (Fin size)} (hdominates : Dominates design selected)
    (probeIndex : Fin size) :
    leverageOf (design.atom probeIndex)
      ≤ ∑ atomIndex ∈ selected,
          (design.atom probeIndex ⬝ᵥ design.atom atomIndex) ^ 2 := by
  have hpsd := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hdominates).2
    (design.atom probeIndex)
  rw [star_trivial, gapPairing_bilinear] at hpsd
  have hlev : design.atom probeIndex ⬝ᵥ design.atom probeIndex
      = leverageOf (design.atom probeIndex) := by
    rw [leverageOf, dotProduct]
    exact Finset.sum_congr rfl fun coordIndex _ => (pow_two _).symm
  have hsymmetrize : ∑ atomIndex ∈ selected,
      (design.atom atomIndex ⬝ᵥ design.atom probeIndex)
        * (design.atom atomIndex ⬝ᵥ design.atom probeIndex)
      = ∑ atomIndex ∈ selected,
          (design.atom probeIndex ⬝ᵥ design.atom atomIndex) ^ 2 :=
    Finset.sum_congr rfl fun atomIndex _ => by
      rw [dotProduct_comm, pow_two]
  rw [hsymmetrize, hlev] at hpsd
  linarith

/-! ## Part 2: locating a negative direction on the range of a PSD gap

The C*-square-root pattern of `Gtz.LinAlg.PsdKit.exists_congruence_to_one`,
consumed at the PSD (not PD) level: a factorization `M = Fᵀ F` turns a negative
trace pairing `tr (M K) < 0` into a negative diagonal entry of `F K Fᵀ`, whose
row is automatically orthogonal to every kernel vector of `M`. -/

open scoped MatrixOrder in
/-- **A NEGATIVE TRACE PAIRING AGAINST A PSD MATRIX HAS A WITNESS ON ITS
RANGE.**  If `M` is positive semidefinite and `tr (M K) < 0`, some direction
`w` orthogonal to the whole kernel of `M` has `w ⬝ K w < 0`. -/
theorem exists_negDirection_orthKernel_of_trace_mul_neg {dim : ℕ}
    {gapMatrix conic : Matrix (Fin dim) (Fin dim) ℝ}
    (hgapPsd : gapMatrix.PosSemidef)
    (htraceNeg : Matrix.trace (gapMatrix * conic) < 0) :
    ∃ witness : Fin dim → ℝ, witness ⬝ᵥ (conic *ᵥ witness) < 0
      ∧ ∀ kernelVec : Fin dim → ℝ,
          gapMatrix *ᵥ kernelVec = 0 → witness ⬝ᵥ kernelVec = 0 := by
  obtain ⟨factor, hfactorStar⟩ :=
    CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hgapPsd.nonneg
  have hfactorization : gapMatrix = factorᵀ * factor := by
    rw [hfactorStar, Matrix.star_eq_conjTranspose]
    congr 1
  have htraceSlab : Matrix.trace (factor * conic * factorᵀ) < 0 := by
    have hcycle : Matrix.trace (gapMatrix * conic)
        = Matrix.trace (factor * conic * factorᵀ) := by
      rw [hfactorization, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]
    linarith [hcycle ▸ htraceNeg]
  have hdiagNeg : ∃ rowIndex : Fin dim,
      (factor * conic * factorᵀ) rowIndex rowIndex < 0 := by
    by_contra hallNonneg
    push Not at hallNonneg
    have hsumNonneg : 0 ≤ Matrix.trace (factor * conic * factorᵀ) :=
      Finset.sum_nonneg fun rowIndex _ => hallNonneg rowIndex
    linarith
  obtain ⟨rowIndex, hrowNeg⟩ := hdiagNeg
  set witness : Fin dim → ℝ := fun colIndex => factor rowIndex colIndex
    with hwitnessDef
  have hformValue : witness ⬝ᵥ (conic *ᵥ witness)
      = (factor * conic * factorᵀ) rowIndex rowIndex := by
    simp only [hwitnessDef, dotProduct, Matrix.mulVec, Matrix.mul_apply,
      Matrix.transpose_apply, dotProduct, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun leftIndex _ =>
      Finset.sum_congr rfl fun rightIndex _ => by ring
  refine ⟨witness, by rw [hformValue]; exact hrowNeg, fun kernelVec hkernel => ?_⟩
  have hfactorKernel : factor *ᵥ kernelVec = 0 := by
    have hselfZero : (factor *ᵥ kernelVec) ⬝ᵥ (factor *ᵥ kernelVec) = 0 := by
      have hpull : (factor *ᵥ kernelVec) ⬝ᵥ (factor *ᵥ kernelVec)
          = kernelVec ⬝ᵥ (gapMatrix *ᵥ kernelVec) := by
        rw [hfactorization, ← Matrix.mulVec_mulVec,
          ← dotProduct_mulVec_transpose factorᵀ kernelVec (factor *ᵥ kernelVec),
          Matrix.transpose_transpose]
      rw [hpull, hkernel, dotProduct_zero]
    exact eq_zero_of_dotProduct_self_eq_zero hselfZero
  have hwitnessEntry : witness ⬝ᵥ kernelVec = (factor *ᵥ kernelVec) rowIndex := rfl
  rw [hwitnessEntry, hfactorKernel]
  rfl

/-! ## Part 2b: the dominating-stratum overlap law and the outsider deficiency

Two exact consequences of the tie that exist only at size six.  The overlap
law pairs the PSD gaps of two dominating subsets against each other; the
outsider deficiency extracts a jointly deficient direction for the COMPLEMENT
of a dominating triple — a statement whose very arity needs six atoms: at
`(5,3)` the complement of a triple is a pair. -/

open scoped MatrixOrder in
/-- The trace of a product of two positive semidefinite matrices is
nonnegative: factor one of them and read the diagonal. -/
theorem trace_mul_nonneg_of_posSemidef {dim : ℕ}
    {leftMatrix rightMatrix : Matrix (Fin dim) (Fin dim) ℝ}
    (hleftPsd : leftMatrix.PosSemidef) (hrightPsd : rightMatrix.PosSemidef) :
    0 ≤ Matrix.trace (leftMatrix * rightMatrix) := by
  by_contra hnegative
  push Not at hnegative
  obtain ⟨witness, hwitnessNeg, _⟩ :=
    exists_negDirection_orthKernel_of_trace_mul_neg hleftPsd hnegative
  have hwitnessNonneg := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hrightPsd).2 witness
  rw [star_trivial] at hwitnessNonneg
  linarith

/-- **THE DOMINATING-STRATUM OVERLAP LAW.**  Any two weakly dominating
subsets of a design pair their PSD gaps nonnegatively, which reads as an
exact squared-Gram floor:

    `sum_{c in C, c' in C'} (g_c . g_c')^2  >=  sum_C lev + sum_C' lev - rank.`

At a tie EVERY pair of dominating triples obeys it — the quadratic
constraint the equality stratum must satisfy jointly, invisible to any
single-triple analysis. -/
theorem frameOverlap_floor_of_dominates_pair (design : WeightedDesign size rank)
    {selectedLeft selectedRight : Finset (Fin size)}
    (hdominatesLeft : Dominates design selectedLeft)
    (hdominatesRight : Dominates design selectedRight) :
    (∑ leftIndex ∈ selectedLeft, leverageOf (design.atom leftIndex))
        + (∑ rightIndex ∈ selectedRight, leverageOf (design.atom rightIndex))
        - rank
      ≤ ∑ leftIndex ∈ selectedLeft, ∑ rightIndex ∈ selectedRight,
          (design.atom leftIndex ⬝ᵥ design.atom rightIndex) ^ 2 := by
  have htracePairing := trace_mul_nonneg_of_posSemidef hdominatesLeft hdominatesRight
  have hexpand : Matrix.trace
      ((subsetSum design selectedLeft - 1) * (subsetSum design selectedRight - 1))
      = (∑ leftIndex ∈ selectedLeft, ∑ rightIndex ∈ selectedRight,
          (design.atom leftIndex ⬝ᵥ design.atom rightIndex) ^ 2)
        - (∑ leftIndex ∈ selectedLeft, leverageOf (design.atom leftIndex))
        - (∑ rightIndex ∈ selectedRight, leverageOf (design.atom rightIndex))
        + rank := by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub]
    simp only [Matrix.one_mul, Matrix.mul_one]
    rw [Matrix.trace_sub, Matrix.trace_sub, Matrix.trace_sub, Matrix.trace_one]
    have hcross : Matrix.trace (subsetSum design selectedLeft
        * subsetSum design selectedRight)
        = ∑ leftIndex ∈ selectedLeft, ∑ rightIndex ∈ selectedRight,
            (design.atom leftIndex ⬝ᵥ design.atom rightIndex) ^ 2 := by
      rw [subsetSum, subsetSum, Finset.sum_mul_sum, Matrix.trace_sum]
      refine Finset.sum_congr rfl fun leftIndex _ => ?_
      rw [Matrix.trace_sum]
      exact Finset.sum_congr rfl fun rightIndex _ =>
        trace_atomMatrix_mul_atomMatrix _ _
    have hleftTrace : Matrix.trace (subsetSum design selectedLeft)
        = ∑ leftIndex ∈ selectedLeft, leverageOf (design.atom leftIndex) := by
      rw [subsetSum, Matrix.trace_sum]
      exact Finset.sum_congr rfl fun leftIndex _ => trace_atomMatrix _
    have hrightTrace : Matrix.trace (subsetSum design selectedRight)
        = ∑ rightIndex ∈ selectedRight, leverageOf (design.atom rightIndex) := by
      rw [subsetSum, Matrix.trace_sum]
      exact Finset.sum_congr rfl fun rightIndex _ => trace_atomMatrix _
    rw [hcross, hleftTrace, hrightTrace, Fintype.card_fin]
    ring
  rw [hexpand] at htracePairing
  linarith

/-- **THE OUTSIDER DEFICIENCY.**  At a `(6,3)` tie, the COMPLEMENT of every
dominating triple — the three outsiders as a triple of their own — admits a
jointly deficient direction: some nonzero `v` with
`sum_{e outside} (g_e . v)^2 <= |v|^2`.  The statement's arity is six-only:
at five points the complement of a triple is a pair and no such triple
exists.  Together with the eigenvector collapse of the tight triple this is
the pincer the one-frame system closes around: insiders resolve the tight
axis exactly, outsiders are deficient somewhere. -/
theorem exists_deficientDirection_outsiderTriple_of_isTie (design : WeightedDesign 6 3)
    (htie : IsTie design) {selected : Finset (Fin 6)} (hcard : selected.card = 3) :
    ∃ deficientDir : Fin 3 → ℝ, deficientDir ≠ 0
      ∧ ∑ outsideIndex ∈ selectedᶜ, (design.atom outsideIndex ⬝ᵥ deficientDir) ^ 2
          ≤ deficientDir ⬝ᵥ deficientDir := by
  have hcardCompl : selectedᶜ.card = 3 := by
    rw [Finset.card_compl, Fintype.card_fin, hcard]
  have hnotPosDef : ¬ (subsetSum design selectedᶜ - 1).PosDef :=
    htie.2 selectedᶜ hcardCompl
  rw [Matrix.posDef_iff_dotProduct_mulVec] at hnotPosDef
  push Not at hnotPosDef
  obtain ⟨deficientDir, hdirNe, hform⟩ :=
    hnotPosDef (isHermitian_subsetSum_sub_one design selectedᶜ)
  rw [star_trivial, gapPairing_bilinear] at hform
  refine ⟨deficientDir, hdirNe, ?_⟩
  have hsquare : ∑ outsideIndex ∈ selectedᶜ,
      (design.atom outsideIndex ⬝ᵥ deficientDir)
        * (design.atom outsideIndex ⬝ᵥ deficientDir)
      = ∑ outsideIndex ∈ selectedᶜ,
          (design.atom outsideIndex ⬝ᵥ deficientDir) ^ 2 :=
    Finset.sum_congr rfl fun outsideIndex _ => (pow_two _).symm
  rw [hsquare] at hform
  linarith

/-! ## Part 3: the dual-conic instrument of the stress-free stratum -/

/-- **THE TRACE OF A DUAL CONIC IS ITS ATOM'S WEIGHT** — Parseval read through
the pairing normalization, at any size and any rank.  A symmetric form whose
value is one at the chosen atom and zero at every other has trace exactly the
chosen atom's weight; in particular every dual conic has strictly positive
trace, hence a positive direction. -/
theorem trace_eq_weight_of_atomPairing (design : WeightedDesign size rank)
    {conic : Matrix (Fin rank) (Fin rank) ℝ} {chosen : Fin size}
    (hpairing : ∀ atomIndex : Fin size,
      design.atom atomIndex ⬝ᵥ (conic *ᵥ design.atom atomIndex)
        = if atomIndex = chosen then 1 else 0) :
    Matrix.trace conic = design.weight chosen := by
  calc Matrix.trace conic
      = Matrix.trace (conic * 1) := by rw [Matrix.mul_one]
    _ = Matrix.trace (conic
          * ∑ atomIndex, design.weight atomIndex • atomMatrix (design.atom atomIndex)) := by
        rw [design.isParseval]
    _ = ∑ atomIndex, design.weight atomIndex
          * (design.atom atomIndex ⬝ᵥ (conic *ᵥ design.atom atomIndex)) := by
        rw [Matrix.mul_sum, Matrix.trace_sum]
        exact Finset.sum_congr rfl fun atomIndex _ => by
          rw [Matrix.mul_smul, Matrix.trace_smul, trace_mul_atomMatrix, smul_eq_mul]
    _ = ∑ atomIndex, design.weight atomIndex
          * (if atomIndex = chosen then (1 : ℝ) else 0) :=
        Finset.sum_congr rfl fun atomIndex _ => by rw [hpairing]
    _ = design.weight chosen := by
        simp only [mul_ite, mul_one, mul_zero]
        rw [Finset.sum_ite_eq' Finset.univ chosen design.weight]
        simp

/-- **THE GAP PAIRING LAW.**  A dual conic pairs with the gap of EVERY subset to
the indicator minus the weight: `tr ((S_C - 1) K_x) = 1_C(x) - t_x`.  Strictly
positive for insiders, strictly negative for outsiders, for every subset at
once — the exact identity the polarity law feeds to the PSD gap of a dominating
triple. -/
theorem trace_gapPairing_of_atomPairing (design : WeightedDesign size rank)
    {conic : Matrix (Fin rank) (Fin rank) ℝ} {chosen : Fin size}
    (hpairing : ∀ atomIndex : Fin size,
      design.atom atomIndex ⬝ᵥ (conic *ᵥ design.atom atomIndex)
        = if atomIndex = chosen then 1 else 0)
    (anySubset : Finset (Fin size)) :
    Matrix.trace ((subsetSum design anySubset - 1) * conic)
      = (if chosen ∈ anySubset then (1 : ℝ) else 0) - design.weight chosen := by
  have hsubsetTrace : Matrix.trace (subsetSum design anySubset * conic)
      = if chosen ∈ anySubset then (1 : ℝ) else 0 := by
    calc Matrix.trace (subsetSum design anySubset * conic)
        = ∑ atomIndex ∈ anySubset,
            Matrix.trace (atomMatrix (design.atom atomIndex) * conic) := by
          rw [subsetSum, Matrix.sum_mul, Matrix.trace_sum]
      _ = ∑ atomIndex ∈ anySubset,
            (if atomIndex = chosen then (1 : ℝ) else 0) :=
          Finset.sum_congr rfl fun atomIndex _ => by
            rw [Matrix.trace_mul_comm, trace_mul_atomMatrix, hpairing]
      _ = if chosen ∈ anySubset then (1 : ℝ) else 0 := by
          rw [Finset.sum_ite_eq' anySubset chosen (fun _ => (1 : ℝ))]
  rw [Matrix.sub_mul, Matrix.trace_sub, Matrix.one_mul, hsubsetTrace,
    trace_eq_weight_of_atomPairing design hpairing]

/-- **THE OUTSIDER POLARITY, at any weakly dominating subset.**  The dual conic
of an atom OUTSIDE a weakly dominating subset pairs with the subset's PSD gap
to `-t_x < 0`, so it carries a negative direction orthogonal to the whole
kernel of the gap — negative ON THE TIGHT RANGE, not merely somewhere. -/
theorem exists_negDirection_conic_of_dominates_of_atomPairing
    (design : WeightedDesign size rank) {selected : Finset (Fin size)}
    (hdominates : Dominates design selected)
    {conic : Matrix (Fin rank) (Fin rank) ℝ} {chosen : Fin size}
    (houtside : chosen ∉ selected)
    (hpairing : ∀ atomIndex : Fin size,
      design.atom atomIndex ⬝ᵥ (conic *ᵥ design.atom atomIndex)
        = if atomIndex = chosen then 1 else 0) :
    ∃ witness : Fin rank → ℝ, witness ⬝ᵥ (conic *ᵥ witness) < 0
      ∧ ∀ kernelVec : Fin rank → ℝ,
          (subsetSum design selected - 1) *ᵥ kernelVec = 0 →
            witness ⬝ᵥ kernelVec = 0 := by
  have htraceNeg : Matrix.trace ((subsetSum design selected - 1) * conic) < 0 := by
    rw [trace_gapPairing_of_atomPairing design hpairing selected, if_neg houtside]
    linarith [design.weight_pos chosen]
  exact exists_negDirection_orthKernel_of_trace_mul_neg hdominates htraceNeg

open scoped MatrixOrder in
/-- The positive mirror: a positive trace pairing against a PSD matrix has a
positive witness orthogonal to the whole kernel — the negative law at the
negated form. -/
theorem exists_posDirection_orthKernel_of_trace_mul_pos {dim : ℕ}
    {gapMatrix conic : Matrix (Fin dim) (Fin dim) ℝ}
    (hgapPsd : gapMatrix.PosSemidef)
    (htracePos : 0 < Matrix.trace (gapMatrix * conic)) :
    ∃ witness : Fin dim → ℝ, 0 < witness ⬝ᵥ (conic *ᵥ witness)
      ∧ ∀ kernelVec : Fin dim → ℝ,
          gapMatrix *ᵥ kernelVec = 0 → witness ⬝ᵥ kernelVec = 0 := by
  have hnegTrace : Matrix.trace (gapMatrix * (-conic)) < 0 := by
    rw [Matrix.mul_neg, Matrix.trace_neg]
    linarith
  obtain ⟨witness, hwitnessNeg, horthKernel⟩ :=
    exists_negDirection_orthKernel_of_trace_mul_neg hgapPsd hnegTrace
  refine ⟨witness, ?_, horthKernel⟩
  rw [Matrix.neg_mulVec, dotProduct_neg] at hwitnessNeg
  linarith

/-- **THE INSIDER POLARITY.**  The dual conic of an atom INSIDE a weakly
dominating subset pairs with the subset's PSD gap to `1 - t_x > 0`, so it is
strictly positive somewhere on the orthogonal complement of the tight kernel.
Together with the outsider law the tie polarizes the whole conic frame along
every dominating triple: insiders positive on the tight range, outsiders
negative on it. -/
theorem exists_posDirection_conic_of_dominates_of_atomPairing
    (design : WeightedDesign size rank) (hsize : 2 ≤ size)
    {selected : Finset (Fin size)} (hdominates : Dominates design selected)
    {conic : Matrix (Fin rank) (Fin rank) ℝ} {chosen : Fin size}
    (hinside : chosen ∈ selected)
    (hpairing : ∀ atomIndex : Fin size,
      design.atom atomIndex ⬝ᵥ (conic *ᵥ design.atom atomIndex)
        = if atomIndex = chosen then 1 else 0) :
    ∃ witness : Fin rank → ℝ, 0 < witness ⬝ᵥ (conic *ᵥ witness)
      ∧ ∀ kernelVec : Fin rank → ℝ,
          (subsetSum design selected - 1) *ᵥ kernelVec = 0 →
            witness ⬝ᵥ kernelVec = 0 := by
  have htracePos : 0 < Matrix.trace ((subsetSum design selected - 1) * conic) := by
    rw [trace_gapPairing_of_atomPairing design hpairing selected, if_pos hinside]
    linarith [weight_lt_one design hsize chosen]
  exact exists_posDirection_orthKernel_of_trace_mul_pos hdominates htracePos

/-- A matrix of positive trace has a positive direction — the coordinate
direction of a positive diagonal entry. -/
theorem exists_posDirection_of_trace_pos {dim : ℕ}
    {conic : Matrix (Fin dim) (Fin dim) ℝ} (htracePos : 0 < Matrix.trace conic) :
    ∃ witness : Fin dim → ℝ, 0 < witness ⬝ᵥ (conic *ᵥ witness) := by
  have hdiagPos : ∃ diagIndex : Fin dim, 0 < conic diagIndex diagIndex := by
    by_contra hallNonpos
    push Not at hallNonpos
    have hsumNonpos : Matrix.trace conic ≤ 0 :=
      Finset.sum_nonpos fun diagIndex _ => hallNonpos diagIndex
    linarith
  obtain ⟨diagIndex, hdiagValue⟩ := hdiagPos
  refine ⟨Pi.single diagIndex 1, ?_⟩
  have hformValue : (Pi.single diagIndex 1 : Fin dim → ℝ)
      ⬝ᵥ (conic *ᵥ Pi.single diagIndex 1) = conic diagIndex diagIndex := by
    simp [dotProduct, Matrix.mulVec, Pi.single_apply]
  rw [hformValue]
  exact hdiagValue

/-! ## Part 4: existence and uniqueness of dual conics on the stress-free
stratum — the six-ness that the `(5,3)` diamond lacks -/

/-- **EVERY ATOM OF A STRESS-FREE `(6,3)` DESIGN OWNS A DUAL CONIC**: a
symmetric form of value one at the chosen atom and zero at the five others —
the conic through the other five directions, normalized at the chosen one.
One Veronese-grid inversion; existence is exactly the stress-free hypothesis. -/
theorem exists_dualConic_of_stressFree (design : WeightedDesign 6 3)
    (hstressFree : ∀ stress : Fin 6 → ℝ,
      (∑ atomIndex, stress atomIndex • atomMatrix (design.atom atomIndex)) = 0 →
        stress = 0)
    (chosen : Fin 6) :
    ∃ conic : Matrix (Fin 3) (Fin 3) ℝ, conicᵀ = conic
      ∧ ∀ atomIndex : Fin 6,
          design.atom atomIndex ⬝ᵥ (conic *ᵥ design.atom atomIndex)
            = if atomIndex = chosen then 1 else 0 := by
  have hdetNe : (veroneseGrid design.atom).det ≠ 0 :=
    (stressFree_iff_veroneseGrid_det_ne_zero design.atom).mp hstressFree
  have hdetUnit : IsUnit (veroneseGrid design.atom).det := isUnit_iff_ne_zero.mpr hdetNe
  set coordsVec : Fin 6 → ℝ := (veroneseGrid design.atom)⁻¹ *ᵥ Pi.single chosen 1
    with hcoordsVecDef
  set conic : Matrix (Fin 3) (Fin 3) ℝ :=
    Matrix.of ![![coordsVec 0, coordsVec 3 / 2, coordsVec 4 / 2],
                ![coordsVec 3 / 2, coordsVec 1, coordsVec 5 / 2],
                ![coordsVec 4 / 2, coordsVec 5 / 2, coordsVec 2]] with hconicDef
  have hsymm : conicᵀ = conic := by
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;> simp [hconicDef]
  have hcoords : conicCoords conic = coordsVec := by
    funext coordIndex
    fin_cases coordIndex <;> simp [conicCoords, hconicDef] <;> ring
  refine ⟨conic, hsymm, fun atomIndex => ?_⟩
  have hrow : veroneseCoords (design.atom atomIndex) ⬝ᵥ coordsVec
      = (veroneseGrid design.atom *ᵥ coordsVec) atomIndex := rfl
  have hresolve : veroneseGrid design.atom *ᵥ coordsVec = Pi.single chosen 1 := by
    rw [hcoordsVecDef, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdetUnit,
      Matrix.one_mulVec]
  rw [conic_form_eq_veronese_dotProduct hsymm, hcoords, hrow, hresolve,
    Pi.single_apply]

/-- **THE DUAL CONIC IS UNIQUE** on the stress-free stratum: two solutions
differ by a conic through all six directions, and stress-freeness is exactly
"the six directions lie on no conic".  This is the six-ness the `(5,3)`
diamond lacks — at five points the analogous system is underdetermined and
the "conic through the others" is a pencil, pinned by nothing. -/
theorem dualConic_unique_of_stressFree (design : WeightedDesign 6 3)
    (hstressFree : ∀ stress : Fin 6 → ℝ,
      (∑ atomIndex, stress atomIndex • atomMatrix (design.atom atomIndex)) = 0 →
        stress = 0)
    {chosen : Fin 6} {conicA conicB : Matrix (Fin 3) (Fin 3) ℝ}
    (hsymmA : conicAᵀ = conicA) (hsymmB : conicBᵀ = conicB)
    (hpairA : ∀ atomIndex : Fin 6,
      design.atom atomIndex ⬝ᵥ (conicA *ᵥ design.atom atomIndex)
        = if atomIndex = chosen then 1 else 0)
    (hpairB : ∀ atomIndex : Fin 6,
      design.atom atomIndex ⬝ᵥ (conicB *ᵥ design.atom atomIndex)
        = if atomIndex = chosen then 1 else 0) :
    conicA = conicB := by
  have hdiffSymm : (conicA - conicB)ᵀ = conicA - conicB := by
    rw [Matrix.transpose_sub, hsymmA, hsymmB]
  have hvanishes : ∀ atomIndex : Fin 6,
      design.atom atomIndex ⬝ᵥ ((conicA - conicB) *ᵥ design.atom atomIndex) = 0 := by
    intro atomIndex
    rw [Matrix.sub_mulVec, dotProduct_sub, hpairA, hpairB, sub_self]
  have hdiffZero := (stressFree_iff_no_conic_sixThree design.atom).mp hstressFree
    (conicA - conicB) hdiffSymm hvanishes
  exact sub_eq_zero.mp hdiffZero

/-! ## Part 4b: the six-ness lever, stated as a five-point degeneracy

The dual-conic instrument is pinned at six stress-free atoms and NEVER pinned
at five: the space of conics is six-dimensional, so five directions always
lie on a common nonzero conic, and any pairing-normalized conic of a
five-atom family can be shifted along that conic freely.  This is the exact
degeneracy that makes every dual-frame argument automatically pass the
`(5,3)` diamond filter: at five points there is no canonical conic frame to
consume. -/

/-- **FIVE DIRECTIONS ALWAYS LIE ON A CONIC.**  For any five vectors of
`ℝ³` some nonzero symmetric form vanishes on all of them: five linear
conditions cannot pin the six-dimensional space of conics.  Mechanized by
padding the five-row Veronese grid with a zero row and taking a kernel
vector of the resulting singular square matrix. -/
theorem exists_conic_through_five (atomFamily : Fin 5 → Fin 3 → ℝ) :
    ∃ conic : Matrix (Fin 3) (Fin 3) ℝ, conicᵀ = conic ∧ conic ≠ 0
      ∧ ∀ atomIndex : Fin 5,
          atomFamily atomIndex ⬝ᵥ (conic *ᵥ atomFamily atomIndex) = 0 := by
  set paddedGrid : Matrix (Fin 6) (Fin 6) ℝ :=
    Matrix.of fun rowIndex colIndex =>
      if hrow : (rowIndex : ℕ) < 5
        then veroneseCoords (atomFamily ⟨rowIndex, hrow⟩) colIndex else 0
    with hpaddedDef
  have hlastRowZero : ∀ colIndex : Fin 6, paddedGrid 5 colIndex = 0 := by
    intro colIndex
    rw [hpaddedDef]
    simp
  have hdetZero : paddedGrid.det = 0 :=
    Matrix.det_eq_zero_of_row_eq_zero 5 hlastRowZero
  obtain ⟨coordsVec, hcoordsNe, hkernel⟩ :=
    Matrix.exists_mulVec_eq_zero_iff.mpr hdetZero
  set conic : Matrix (Fin 3) (Fin 3) ℝ :=
    Matrix.of ![![coordsVec 0, coordsVec 3 / 2, coordsVec 4 / 2],
                ![coordsVec 3 / 2, coordsVec 1, coordsVec 5 / 2],
                ![coordsVec 4 / 2, coordsVec 5 / 2, coordsVec 2]] with hconicDef
  have hsymm : conicᵀ = conic := by
    ext rowIndex colIndex
    fin_cases rowIndex <;> fin_cases colIndex <;> simp [hconicDef]
  have hcoords : conicCoords conic = coordsVec := by
    funext coordIndex
    fin_cases coordIndex <;> simp [conicCoords, hconicDef] <;> ring
  refine ⟨conic, hsymm, ?_, fun atomIndex => ?_⟩
  · intro hconicZero
    exact hcoordsNe (by rw [← hcoords, hconicZero]
                        exact (conicCoords_eq_zero_iff (by rw [Matrix.transpose_zero])).mpr rfl)
  · have hrowValue : (paddedGrid *ᵥ coordsVec) ⟨atomIndex, by omega⟩ = 0 := by
      rw [hkernel]
      rfl
    have hrowExpand : (paddedGrid *ᵥ coordsVec) ⟨atomIndex, by omega⟩
        = veroneseCoords (atomFamily atomIndex) ⬝ᵥ coordsVec := by
      rw [Matrix.mulVec]
      congr 1
      funext colIndex
      rw [hpaddedDef]
      simp
    rw [conic_form_eq_veronese_dotProduct hsymm, hcoords, ← hrowExpand, hrowValue]

/-- **THE DUAL CONIC IS NEVER UNIQUE AT FIVE POINTS** — the exact contrast to
`dualConic_unique_of_stressFree`.  Any pairing-normalized conic of a
five-atom family shifts freely along the conic through all five directions,
so the `(5,3)` cell has no canonical conic frame: the six-ness consumed by
the dual-frame instrument is precisely this pinning. -/
theorem dualConic_never_unique_fivePoints (atomFamily : Fin 5 → Fin 3 → ℝ)
    {chosen : Fin 5} {conicA : Matrix (Fin 3) (Fin 3) ℝ}
    (hsymmA : conicAᵀ = conicA)
    (hpairA : ∀ atomIndex : Fin 5,
      atomFamily atomIndex ⬝ᵥ (conicA *ᵥ atomFamily atomIndex)
        = if atomIndex = chosen then 1 else 0) :
    ∃ conicB : Matrix (Fin 3) (Fin 3) ℝ, conicB ≠ conicA ∧ conicBᵀ = conicB
      ∧ ∀ atomIndex : Fin 5,
          atomFamily atomIndex ⬝ᵥ (conicB *ᵥ atomFamily atomIndex)
            = if atomIndex = chosen then 1 else 0 := by
  obtain ⟨sharedConic, hsharedSymm, hsharedNe, hsharedVanishes⟩ :=
    exists_conic_through_five atomFamily
  refine ⟨conicA + sharedConic, ?_, ?_, fun atomIndex => ?_⟩
  · intro hshiftEq
    exact hsharedNe (by
      have hcancel := congrArg (fun formValue => formValue - conicA) hshiftEq
      simpa using hcancel)
  · rw [Matrix.transpose_add, hsymmA, hsharedSymm]
  · rw [Matrix.add_mulVec, dotProduct_add, hpairA, hsharedVanishes, add_zero]

/-! ## Part 5: the polarity law at a stress-free `(6,3)` tie -/

/-- **THE POLARITY LAW.**  At a stress-free `(6,3)` tie there is a dominating
triple such that EVERY outsider owns a dual conic — symmetric, value one at
the outsider, zero at the five others — that the tie forces to be indefinite
in a located way: its trace is the outsider's weight (positive, hence a
positive direction exists), while it is strictly negative somewhere on the
orthogonal complement of the tight kernel.  The six atoms hand the tie a
six-fold conic frame, and the tie must bend the three outsider conics against
their own positive traces.  On the `(5,3)` diamond the frame does not exist:
its dual system is underdetermined and nothing normalizes the pencil. -/
theorem sixThree_exists_dominating_with_indefinite_outsider_conics_of_isTie
    (design : WeightedDesign 6 3)
    (hstressFree : ∀ stress : Fin 6 → ℝ,
      (∑ atomIndex, stress atomIndex • atomMatrix (design.atom atomIndex)) = 0 →
        stress = 0)
    (htie : IsTie design) :
    ∃ selected : Finset (Fin 6), selected.card = 3 ∧ Dominates design selected
      ∧ ∀ chosen : Fin 6, chosen ∉ selected →
          ∃ conic : Matrix (Fin 3) (Fin 3) ℝ, conicᵀ = conic
            ∧ (∀ atomIndex : Fin 6,
                design.atom atomIndex ⬝ᵥ (conic *ᵥ design.atom atomIndex)
                  = if atomIndex = chosen then 1 else 0)
            ∧ Matrix.trace conic = design.weight chosen
            ∧ (∃ witness : Fin 3 → ℝ, witness ⬝ᵥ (conic *ᵥ witness) < 0
                ∧ ∀ kernelVec : Fin 3 → ℝ,
                    (subsetSum design selected - 1) *ᵥ kernelVec = 0 →
                      witness ⬝ᵥ kernelVec = 0) := by
  obtain ⟨⟨selected, hcard, hdominates⟩, _⟩ := htie
  refine ⟨selected, hcard, hdominates, fun chosen houtside => ?_⟩
  obtain ⟨conic, hsymm, hpairing⟩ := exists_dualConic_of_stressFree design hstressFree chosen
  exact ⟨conic, hsymm, hpairing, trace_eq_weight_of_atomPairing design hpairing,
    exists_negDirection_conic_of_dominates_of_atomPairing design hdominates houtside
      hpairing⟩

/-! ## Part 6: the gate trichotomy

The axis-split gate classifies every subset carrying axis mass above one, at
any design:

  * PD               ⟺  gate strict everywhere,
  * weakly dominating ⟹  gate `<=` everywhere        (PSD Cauchy-Schwarz)
                          with equality somewhere     (the equality law),
  * not dominating with axis mass above one
                      ⟹  STRICT overshoot somewhere  (below).

Everything holds at any design — the trichotomy is classification, not
tie-specific. -/

/-- **CAUCHY-SCHWARZ FOR A PSD FORM.**  `(u M v)^2 <= (u M u)(v M v)` for
positive semidefinite `M` — the reason a weakly dominating subset satisfies
the axis-split gate non-strictly in every frame. -/
theorem sq_dotProduct_mulVec_le_of_posSemidef {dim : ℕ}
    {formMatrix : Matrix (Fin dim) (Fin dim) ℝ} (hpsd : formMatrix.PosSemidef)
    (leftProbe rightProbe : Fin dim → ℝ) :
    (leftProbe ⬝ᵥ (formMatrix *ᵥ rightProbe)) ^ 2
      ≤ (leftProbe ⬝ᵥ (formMatrix *ᵥ leftProbe))
        * (rightProbe ⬝ᵥ (formMatrix *ᵥ rightProbe)) := by
  set leftValue : ℝ := leftProbe ⬝ᵥ (formMatrix *ᵥ leftProbe) with hleftDef
  set crossValue : ℝ := leftProbe ⬝ᵥ (formMatrix *ᵥ rightProbe) with hcrossDef
  set rightValue : ℝ := rightProbe ⬝ᵥ (formMatrix *ᵥ rightProbe) with hrightDef
  have hentrySymm : ∀ rowIndex colIndex : Fin dim,
      formMatrix colIndex rowIndex = formMatrix rowIndex colIndex := by
    intro rowIndex colIndex
    have happly := hpsd.1.apply rowIndex colIndex
    rwa [star_trivial] at happly
  have hcrossSwap : rightProbe ⬝ᵥ (formMatrix *ᵥ leftProbe) = crossValue := by
    rw [hcrossDef]
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun rowIndex _ =>
      Finset.sum_congr rfl fun colIndex _ => by
        rw [hentrySymm colIndex rowIndex]
        ring
  have hcombination : ∀ leftScale rightScale : ℝ,
      0 ≤ leftScale ^ 2 * leftValue + 2 * leftScale * rightScale * crossValue
        + rightScale ^ 2 * rightValue := by
    intro leftScale rightScale
    have hvalue := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hpsd).2
      (leftScale • leftProbe + rightScale • rightProbe)
    rw [star_trivial, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
      dotProduct_add, add_dotProduct, add_dotProduct] at hvalue
    simp only [dotProduct_smul, smul_dotProduct, smul_eq_mul] at hvalue
    rw [hcrossSwap] at hvalue
    nlinarith [hvalue]
  have hleftNonneg : 0 ≤ leftValue := by
    have hvalue := hcombination 1 0
    linarith
  have hrightNonneg : 0 ≤ rightValue := by
    have hvalue := hcombination 0 1
    linarith
  rcases eq_or_lt_of_le hrightNonneg with hrightZero | hrightPos
  · rcases eq_or_lt_of_le hleftNonneg with hleftZero | hleftPos
    · have hcrossZero := hcombination 1 (-crossValue)
      nlinarith [hcrossZero]
    · have hkey := hcombination (-crossValue) leftValue
      nlinarith [hkey, hleftPos]
  · have hkey := hcombination rightValue (-crossValue)
    nlinarith [hkey, hrightPos]

/-- **THE STRICT OVERSHOOT.**  A `rank`-subset that does NOT weakly dominate
yet carries axis mass above one along a unit axis overshoots the gate
STRICTLY somewhere on the axis plane: the negative direction of its gap
decomposes into an axis part and a nonzero plane shadow whose discriminant is
positive.  Third leg of the gate trichotomy. -/
theorem exists_strictGateOvershoot_of_not_dominates (design : WeightedDesign size rank)
    {selected : Finset (Fin size)} (hnotDominates : ¬ Dominates design selected)
    {axis : Fin rank → ℝ} (hunit : axis ⬝ᵥ axis = 1)
    (haxisExcess : 1 < ∑ atomIndex ∈ selected, (design.atom atomIndex ⬝ᵥ axis) ^ 2) :
    ∃ planar : Fin rank → ℝ, planar ⬝ᵥ axis = 0 ∧ planar ≠ 0
      ∧ ((∑ atomIndex ∈ selected, (design.atom atomIndex ⬝ᵥ axis) ^ 2) - 1)
            * ((∑ atomIndex ∈ selected, (design.atom atomIndex ⬝ᵥ planar) ^ 2)
              - planar ⬝ᵥ planar)
          < (∑ atomIndex ∈ selected,
              (design.atom atomIndex ⬝ᵥ axis) * (design.atom atomIndex ⬝ᵥ planar)) ^ 2 := by
  have hnegDirection : ∃ negProbe : Fin rank → ℝ,
      negProbe ⬝ᵥ ((subsetSum design selected - 1) *ᵥ negProbe) < 0 := by
    by_contra hallNonneg
    push Not at hallNonneg
    exact hnotDominates (Matrix.posSemidef_iff_dotProduct_mulVec.mpr
      ⟨isHermitian_subsetSum_sub_one design selected, fun probe => by
        rw [star_trivial]
        exact hallNonneg probe⟩)
  obtain ⟨negProbe, hnegValue⟩ := hnegDirection
  set axisCoord : ℝ := negProbe ⬝ᵥ axis with haxisCoordDef
  set planar : Fin rank → ℝ := negProbe - axisCoord • axis with hplanarDef
  have hplanarOrth : planar ⬝ᵥ axis = 0 := by
    rw [hplanarDef, sub_dotProduct, smul_dotProduct, smul_eq_mul, hunit, haxisCoordDef]
    ring
  set axisMass : ℝ := ∑ atomIndex ∈ selected, (design.atom atomIndex ⬝ᵥ axis) ^ 2
    with haxisMassDef
  set couplingValue : ℝ := ∑ atomIndex ∈ selected,
    (design.atom atomIndex ⬝ᵥ axis) * (design.atom atomIndex ⬝ᵥ planar)
    with hcouplingDef
  set excessValue : ℝ := (∑ atomIndex ∈ selected,
    (design.atom atomIndex ⬝ᵥ planar) ^ 2) - planar ⬝ᵥ planar with hexcessDef
  -- the split of the negative form value
  have hrecover : negProbe = axisCoord • axis + planar := by
    rw [hplanarDef]
    abel
  have hpairSplit : ∀ atomIndex : Fin size,
      design.atom atomIndex ⬝ᵥ negProbe
        = axisCoord * (design.atom atomIndex ⬝ᵥ axis)
          + design.atom atomIndex ⬝ᵥ planar := by
    intro atomIndex
    conv_lhs => rw [hrecover]
    rw [dotProduct_add, dotProduct_smul, smul_eq_mul]
  have hnormSplit : negProbe ⬝ᵥ negProbe = axisCoord ^ 2 + planar ⬝ᵥ planar := by
    conv_lhs => rw [hrecover]
    rw [dotProduct_add, add_dotProduct, add_dotProduct, smul_dotProduct,
      dotProduct_smul, smul_dotProduct, dotProduct_smul]
    simp only [smul_eq_mul]
    rw [hunit, dotProduct_comm axis planar, hplanarOrth]
    ring
  have hsplitValue : negProbe ⬝ᵥ ((subsetSum design selected - 1) *ᵥ negProbe)
      = (axisMass - 1) * axisCoord ^ 2 + 2 * axisCoord * couplingValue
        + excessValue := by
    rw [gapPairing_bilinear, Finset.sum_congr rfl fun atomIndex _ => by
        rw [hpairSplit atomIndex],
      hnormSplit]
    have hexpandSquare : ∀ atomIndex ∈ selected,
        (axisCoord * (design.atom atomIndex ⬝ᵥ axis)
            + design.atom atomIndex ⬝ᵥ planar)
          * (axisCoord * (design.atom atomIndex ⬝ᵥ axis)
            + design.atom atomIndex ⬝ᵥ planar)
        = axisCoord ^ 2 * (design.atom atomIndex ⬝ᵥ axis) ^ 2
          + 2 * axisCoord * ((design.atom atomIndex ⬝ᵥ axis)
              * (design.atom atomIndex ⬝ᵥ planar))
          + (design.atom atomIndex ⬝ᵥ planar) ^ 2 := fun atomIndex _ => by ring
    rw [Finset.sum_congr rfl hexpandSquare, Finset.sum_add_distrib,
      Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      haxisMassDef, hcouplingDef, hexcessDef]
    ring
  have hnegSplit : (axisMass - 1) * axisCoord ^ 2 + 2 * axisCoord * couplingValue
      + excessValue < 0 := by
    rw [← hsplitValue]
    exact hnegValue
  have hplanarNe : planar ≠ 0 := by
    intro hplanarZero
    have hcoupZero : couplingValue = 0 := by
      rw [hcouplingDef, hplanarZero]
      simp
    have hexcZero : excessValue = 0 := by
      rw [hexcessDef, hplanarZero]
      simp
    rw [hcoupZero, hexcZero] at hnegSplit
    nlinarith [hnegSplit, sq_nonneg axisCoord, haxisExcess]
  refine ⟨planar, hplanarOrth, hplanarNe, ?_⟩
  by_contra hgateHolds
  push Not at hgateHolds
  nlinarith [hnegSplit, haxisExcess, sq_nonneg ((axisMass - 1) * axisCoord
    + couplingValue), hgateHolds]

/-- Plane excess is monotone in the subset: a plane-strict PAIR makes every
superset plane-strict.  In particular a plane-strict outsider pair forces the
whole outsider triple's excess to be plane-positive — contrapositively, where
the outsider triple's excess is not plane-positive, NO outsider pair strictly
dominates the tight plane. -/
theorem planarExcess_mono_of_subset (design : WeightedDesign size rank)
    {smallSubset largeSubset : Finset (Fin size)} (hsubset : smallSubset ⊆ largeSubset)
    (planar : Fin rank → ℝ) :
    (∑ atomIndex ∈ smallSubset, (design.atom atomIndex ⬝ᵥ planar) ^ 2)
        - planar ⬝ᵥ planar
      ≤ (∑ atomIndex ∈ largeSubset, (design.atom atomIndex ⬝ᵥ planar) ^ 2)
        - planar ⬝ᵥ planar := by
  have hmono : ∑ atomIndex ∈ smallSubset, (design.atom atomIndex ⬝ᵥ planar) ^ 2
      ≤ ∑ atomIndex ∈ largeSubset, (design.atom atomIndex ⬝ᵥ planar) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun atomIndex _ _ => sq_nonneg _)
  linarith

/-- The tie-free classification: any subset with unit-axis mass above one
either weakly dominates or overshoots its gate strictly.  Pure excluded
middle over the overshoot extraction — recorded so the tie corollary below
can cite one name per branch. -/
theorem dominates_or_strictGateOvershoot_of_axisMassExcess
    (design : WeightedDesign size rank) (selected : Finset (Fin size))
    {axis : Fin rank → ℝ} (hunit : axis ⬝ᵥ axis = 1)
    (haxisExcess : 1 < ∑ atomIndex ∈ selected, (design.atom atomIndex ⬝ᵥ axis) ^ 2) :
    Dominates design selected
      ∨ ∃ planar : Fin rank → ℝ, planar ⬝ᵥ axis = 0 ∧ planar ≠ 0
          ∧ ((∑ atomIndex ∈ selected, (design.atom atomIndex ⬝ᵥ axis) ^ 2) - 1)
                * ((∑ atomIndex ∈ selected, (design.atom atomIndex ⬝ᵥ planar) ^ 2)
                  - planar ⬝ᵥ planar)
              < (∑ atomIndex ∈ selected,
                  (design.atom atomIndex ⬝ᵥ axis)
                    * (design.atom atomIndex ⬝ᵥ planar)) ^ 2 := by
  by_cases hdominates : Dominates design selected
  · exact Or.inl hdominates
  · exact Or.inr (exists_strictGateOvershoot_of_not_dominates design hdominates hunit
      haxisExcess)

/-- **THE COMPLEMENTARY-PAIR DICHOTOMY.**  At a `(6,3)` tie with a
dominating triple whose OUTSIDERS carry axis mass above one along a unit
axis, either the outsider triple weakly dominates too — and then BOTH triples
are tight (singular gaps): a COMPLEMENTARY TIGHT PAIR, to which the equality
law and the overlap law apply on both sides — or the outsider triple
overshoots its gate strictly, quantifying how far it sits from domination.
At five points the outsider set of a triple is a pair, so the hypothesis is
six-only. -/
theorem sixThree_complementaryTightPair_or_overshoot_of_isTie
    (design : WeightedDesign 6 3) (htie : IsTie design)
    {selected : Finset (Fin 6)} (hcard : selected.card = 3)
    (hdominates : Dominates design selected)
    {axis : Fin 3 → ℝ} (hunit : axis ⬝ᵥ axis = 1)
    (haxisExcessOutside : 1 < ∑ atomIndex ∈ selectedᶜ,
      (design.atom atomIndex ⬝ᵥ axis) ^ 2) :
    (Dominates design selectedᶜ
        ∧ (subsetSum design selected - 1).det = 0
        ∧ (subsetSum design selectedᶜ - 1).det = 0)
      ∨ ∃ planar : Fin 3 → ℝ, planar ⬝ᵥ axis = 0 ∧ planar ≠ 0
          ∧ ((∑ atomIndex ∈ selectedᶜ, (design.atom atomIndex ⬝ᵥ axis) ^ 2) - 1)
                * ((∑ atomIndex ∈ selectedᶜ, (design.atom atomIndex ⬝ᵥ planar) ^ 2)
                  - planar ⬝ᵥ planar)
              < (∑ atomIndex ∈ selectedᶜ,
                  (design.atom atomIndex ⬝ᵥ axis)
                    * (design.atom atomIndex ⬝ᵥ planar)) ^ 2 := by
  have hcardCompl : selectedᶜ.card = 3 := by
    rw [Finset.card_compl, Fintype.card_fin, hcard]
  rcases dominates_or_strictGateOvershoot_of_axisMassExcess design selectedᶜ hunit
    haxisExcessOutside with hdomCompl | hovershoot
  · exact Or.inl ⟨hdomCompl,
      det_gap_eq_zero_of_isTie_of_dominates design htie hcard hdominates,
      det_gap_eq_zero_of_isTie_of_dominates design htie hcardCompl hdomCompl⟩
  · exact Or.inr hovershoot

/-- **THE INSIDER-CARRYING PAIR.**  If every outsider pair of a triple `Q`
fails to dominate the tight plane strictly (each carries an exact deficiency
witness), then any plane-strict pair the rank-two hinge produces must CONTAIN
AN INSIDER.  The hinge's pair is not confined to the transversal quadruple,
so the elimination goes through the witnesses: an outsider-outsider strict
pair would contradict its own deficiency direction.  Together with the
on-plane-drop exclusion this says the tight plane is dominated only through
the insiders. -/
theorem exists_insiderCarrying_strictPair_of_outsiderDeficiencies
    (design : WeightedDesign 6 3) {selected : Finset (Fin 6)}
    {axis : Fin 3 → ℝ}
    {strongLabel otherLabel : Fin 6} (hlabelNe : strongLabel ≠ otherLabel)
    (hpairStrict : ∀ planar : Fin 3 → ℝ, planar ⬝ᵥ axis = 0 → planar ≠ 0 →
      planar ⬝ᵥ planar
        < (design.atom strongLabel ⬝ᵥ planar) ^ 2
          + (design.atom otherLabel ⬝ᵥ planar) ^ 2)
    (hdeficiency : ∀ leftOutside rightOutside : Fin 6,
      leftOutside ∉ selected → rightOutside ∉ selected →
      leftOutside ≠ rightOutside →
      ∃ planar : Fin 3 → ℝ, planar ⬝ᵥ axis = 0 ∧ planar ≠ 0
        ∧ (design.atom leftOutside ⬝ᵥ planar) ^ 2
            + (design.atom rightOutside ⬝ᵥ planar) ^ 2
          ≤ planar ⬝ᵥ planar) :
    strongLabel ∈ selected ∨ otherLabel ∈ selected := by
  by_contra hbothOutside
  push Not at hbothOutside
  obtain ⟨hstrongOut, hotherOut⟩ := hbothOutside
  obtain ⟨planar, hplanarOrth, hplanarNe, hdeficient⟩ :=
    hdeficiency strongLabel otherLabel hstrongOut hotherOut hlabelNe
  linarith [hpairStrict planar hplanarOrth hplanarNe, hdeficient]

/-! ## Part 7: the collar -- an explicit sqrt-free width from the plane margin

In the weight chart the six directions are fixed and the weights run over
the open simplex; as a weight `w_i` tends to zero its atom
`g_i = sqrt(mu_i/w_i) u_i` BLOWS UP (the face is NOT a five-atom design at
those directions, so no corank descent reaches it).  What does reach it is
the insert-plane transport: for a heavy insert the completion gate is
implied by a plain margin condition, with an explicit sqrt-free threshold.

`posDef_insertCompletion_of_planeMargin`: if the kept pair dominates the
insert's orthogonal plane with margin ratio `m > 0` and the insert's leverage
satisfies

    (g_1 . g_i)^2 + (g_2 . g_i)^2  <  m * lev_i * (lev_i - 1),

then the triple dominates strictly.  Since `lev_i` grows like `1/w_i` in the
weight chart, this is exactly a COLLAR: every weight vector whose lightest
atom is light enough is covered by a triple containing that atom, with the
width available in closed rational form.  The proof is two Cauchy-Schwarz
steps against `posDef_insertCompletion_of_insertPlaneGate` -- no square
roots, no compactness. -/

/-- **THE COLLAR CRITERION.**  A heavy insert plus a pair that dominates the
insert's orthogonal plane with margin ratio `m` completes to a strictly
dominating triple as soon as the pair's coupling to the insert is below
`m * lev * (lev - 1)`.  This is `posDef_insertCompletion_of_insertPlaneGate`
with the per-direction gate discharged once and for all by the margin. -/
theorem posDef_insertCompletion_of_planeMargin (design : WeightedDesign size rank)
    {keptOne keptTwo insertLabel : Fin size}
    (hneKepts : keptOne ≠ keptTwo) (hneOneInsert : keptOne ≠ insertLabel)
    (hneTwoInsert : keptTwo ≠ insertLabel)
    (hinsertHeavy : 1 < design.atom insertLabel ⬝ᵥ design.atom insertLabel)
    {marginRatio : ℝ} (hmarginPos : 0 < marginRatio)
    (hmargin : ∀ planar : Fin rank → ℝ, design.atom insertLabel ⬝ᵥ planar = 0 →
      (1 + marginRatio) * (planar ⬝ᵥ planar)
        ≤ (design.atom keptOne ⬝ᵥ planar) ^ 2
          + (design.atom keptTwo ⬝ᵥ planar) ^ 2)
    (hcollar : (design.atom keptOne ⬝ᵥ design.atom insertLabel) ^ 2
        + (design.atom keptTwo ⬝ᵥ design.atom insertLabel) ^ 2
      < marginRatio * ((design.atom insertLabel ⬝ᵥ design.atom insertLabel)
          * ((design.atom insertLabel ⬝ᵥ design.atom insertLabel) - 1))) :
    (subsetSum design ({keptOne, keptTwo, insertLabel} : Finset (Fin size))
        - 1).PosDef := by
  refine posDef_insertCompletion_of_insertPlaneGate design hneKepts hneOneInsert
    hneTwoInsert hinsertHeavy ?_
  intro planar hplanarOrth hplanarNe
  set leverage : ℝ := design.atom insertLabel ⬝ᵥ design.atom insertLabel
    with hleverageDef
  set crossOne : ℝ := design.atom keptOne ⬝ᵥ design.atom insertLabel
    with hcrossOneDef
  set crossTwo : ℝ := design.atom keptTwo ⬝ᵥ design.atom insertLabel
    with hcrossTwoDef
  set planeOne : ℝ := design.atom keptOne ⬝ᵥ planar with hplaneOneDef
  set planeTwo : ℝ := design.atom keptTwo ⬝ᵥ planar with hplaneTwoDef
  set planeNorm : ℝ := planar ⬝ᵥ planar with hplaneNormDef
  set coupling : ℝ := crossOne ^ 2 + crossTwo ^ 2 with hcouplingDef
  set planeMass : ℝ := planeOne ^ 2 + planeTwo ^ 2 with hplaneMassDef
  have hnormPos : 0 < planeNorm := dotProduct_self_pos hplanarNe
  have hmarginAt : (1 + marginRatio) * planeNorm ≤ planeMass :=
    hmargin planar hplanarOrth
  have hmassPos : 0 < planeMass := by nlinarith [hnormPos, hmarginPos]
  -- Cauchy-Schwarz on the two-term coupling
  have hcauchy : (crossOne * planeOne + crossTwo * planeTwo) ^ 2
      ≤ coupling * planeMass := by
    rw [hcouplingDef, hplaneMassDef]
    nlinarith [sq_nonneg (crossOne * planeTwo - crossTwo * planeOne)]
  -- the excess is a definite fraction of the plane mass
  have hexcess : planeMass * marginRatio ≤ (1 + marginRatio)
      * (planeMass - planeNorm) := by nlinarith [hmarginAt, hmarginPos]
  have hcouplingNonneg : 0 ≤ coupling := by positivity
  have hfactorPos : 0 < leverage ^ 2 + coupling - leverage := by
    nlinarith [hinsertHeavy, hcouplingNonneg]
  -- the collar inequality, scaled by the plane mass
  have hscaled : coupling * planeMass * (1 + marginRatio)
      < (leverage ^ 2 + coupling - leverage) * (planeMass * marginRatio) := by
    have hkey : coupling * (1 + marginRatio)
        < (leverage ^ 2 + coupling - leverage) * marginRatio := by
      nlinarith [hcollar, hmarginPos]
    nlinarith [hkey, hmassPos]
  have hchain : (leverage ^ 2 + coupling - leverage) * (planeMass * marginRatio)
      ≤ (leverage ^ 2 + coupling - leverage)
        * ((1 + marginRatio) * (planeMass - planeNorm)) :=
    mul_le_mul_of_nonneg_left hexcess hfactorPos.le
  have hpositiveFactor : 0 < 1 + marginRatio := by linarith
  nlinarith [hcauchy, hscaled, hchain, hpositiveFactor]

/-- **THE COLLAR, IN LEVERAGE FORM.**  With a fixed plane margin, ANY insert
whose leverage exceeds `1 + coupling / margin` completes the pair.  In the
weight chart `lev = mu * |u|^2 / w`, so this reads as an explicit rational
width in the lightest weight: every weight vector with
`w_i < mu_i |u_i|^2 / (1 + coupling/margin)` is covered by a triple through
the light atom. -/
theorem posDef_insertCompletion_of_leverage_gt (design : WeightedDesign size rank)
    {keptOne keptTwo insertLabel : Fin size}
    (hneKepts : keptOne ≠ keptTwo) (hneOneInsert : keptOne ≠ insertLabel)
    (hneTwoInsert : keptTwo ≠ insertLabel)
    {marginRatio : ℝ} (hmarginPos : 0 < marginRatio)
    (hmargin : ∀ planar : Fin rank → ℝ, design.atom insertLabel ⬝ᵥ planar = 0 →
      (1 + marginRatio) * (planar ⬝ᵥ planar)
        ≤ (design.atom keptOne ⬝ᵥ planar) ^ 2
          + (design.atom keptTwo ⬝ᵥ planar) ^ 2)
    (hleverageBig : 1 + ((design.atom keptOne ⬝ᵥ design.atom insertLabel) ^ 2
          + (design.atom keptTwo ⬝ᵥ design.atom insertLabel) ^ 2) / marginRatio
        < design.atom insertLabel ⬝ᵥ design.atom insertLabel) :
    (subsetSum design ({keptOne, keptTwo, insertLabel} : Finset (Fin size))
        - 1).PosDef := by
  set leverage : ℝ := design.atom insertLabel ⬝ᵥ design.atom insertLabel
    with hleverageDef
  set coupling : ℝ := (design.atom keptOne ⬝ᵥ design.atom insertLabel) ^ 2
      + (design.atom keptTwo ⬝ᵥ design.atom insertLabel) ^ 2 with hcouplingDef
  have hcouplingNonneg : 0 ≤ coupling := by positivity
  have hquotientNonneg : 0 ≤ coupling / marginRatio :=
    div_nonneg hcouplingNonneg hmarginPos.le
  have hheavy : 1 < leverage := by linarith
  refine posDef_insertCompletion_of_planeMargin design hneKepts hneOneInsert
    hneTwoInsert hheavy hmarginPos hmargin ?_
  have hgap : coupling / marginRatio < leverage - 1 := by linarith
  have hproduct : coupling < marginRatio * (leverage - 1) := by
    rw [div_lt_iff₀ hmarginPos] at hgap
    linarith
  nlinarith [hproduct, hheavy, hmarginPos, hcouplingNonneg]

end Gtz
