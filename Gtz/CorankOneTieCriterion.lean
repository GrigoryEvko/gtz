/-
# The corank-one tie criterion: `IsTie` decided by the weighted leverages

`Gtz.IsTie` is consumed as a hypothesis (`isTie_yields_tightDirection`,
`isTie_yields_unitEigenvector`, the zero-set-confinement interface) and it is witnessed
(`tetraDesign_isTie`, `sharpDesign_isTie`, `splitTetraDesign_isTie`), but no theorem in
this library said which designs are ties. At corank one (`m = k+1`) this file gives the
characterisation, in two equivalent shapes:

    IsTie D  ↔  ∀ c, pivot D univ c = 1                (resolvent shape)
             ↔  ∀ c, k · t_c · |g_c|² = (k−1) + t_c    (design-data shape)

The second reads off weights and leverages alone — no inverse, no eigenvalue, no subset
search. Both landed corank-one witnesses satisfy it: `tetraDesign` has `t = 1/4`, `ℓ = 3`
and `3·(1/4)·3 = 9/4 = 2 + 1/4`; `sharpDesign` has `t₀ = 2/3`, `ℓ₀ = 4/3` and
`3·(2/3)·(4/3) = 8/3 = 2 + 2/3` — the criterion does not force equal leverages.

PROVENANCE. The criterion itself is not new. At `k = 2` it reads `ℓ_c = 1/2 + 1/(2 t_c)`,
which at `t = p/n` is Nesterenko (arXiv:2604.14050) Proposition 1. The general-`k`
statement was derived by hand in this campaign and recorded in the `sharpDesign`
docstring in its `ρ` form. What is new here is the mechanization, in both directions,
for every rank.

SCOPE. The identity is exactly a corank-one law: summed over the atoms against
Parseval's trace it forces `m = k + 1` whenever `k ≥ 2`
(`leverage_identity_forces_corank_one`) — no design of any other size satisfies it at
every atom, tie or not. In particular no `(6,3)` design does
(`no_leverage_identity_at_six_three`), and the landed split-tetrahedron ties witness
exact ties beyond corank one violating it (`exists_isTie_leverage_identity_fails`).
Any general-`(m,k)` tie equation must therefore have a different shape.

SHARPNESS. `1 ≤ k` is necessary: the one-atom rank-zero design satisfies the identity
(it reads `0 = −1 + 1`) yet is not a tie, because the empty subset's `0 × 0` gap matrix
is vacuously positive definite (`exists_leverage_identity_not_isTie_rank_zero`). And
the identity genuinely discriminates at corank one: `unevenPairDesign` fails it at its
first atom and carries an explicit strictly dominating singleton, so criterion and
ground truth agree on a falsifying instance.

Two ingredients carry the proof; everything else is already landed.

* the STRICT rank-one Schur step `posDef_sub_vecMulVec_iff` (`Gtz.SchurRankOne`, the
  strict twin of the weak form). With it, `erase_strictDominates_iff_pivot_lt_one` is the strict
  twin of the landed `erase_dominates_iff_pivot_le_one`, and `IsTie` becomes readable off
  the pivots: at corank one every `k`-subset IS an erasure, `descent_identity` says the
  co-weighted pivots sum to `k`, `sum_one_sub_weight` says the co-weights do too, so the
  pivots have co-weighted mean exactly one — and a mean-one family bounded below by one
  is constant.

* the corank-one DEPENDENCY LINE. `k+1` atoms spanning `ℝᵏ` make the combination map
  `a ↦ Σ a_c g_c` onto, so rank-nullity pins its kernel at dimension one. Two symmetric
  matrices have every row in that kernel — the Parseval rows
  `Z_cd = t_c t_d ⟨g_c,g_d⟩ − t_c[c=d]` and the resolvent rows
  `Z'_cd = (1−t_c)(1−t_d)⟨g_c,W⁻¹g_d⟩ − (1−t_c)[c=d]`, `W = S_[m] − 1`. Proportionality of
  the rows plus symmetry gives `Z_cc Z'_dd = Z_dd Z'_cc`, and that single cross identity
  converts the pivot shape into the leverage shape in both directions.

A corollary worth stating separately: `gtzWeighted_corank_one` asserts a dominating
`k`-subset exists, by duality; here the atom to drop is exhibited — a minimiser of the
pivot — and `not_isTie_of_pivot_lt_one` turns a single pivot below one into a certificate
of non-tieness.
-/
import Mathlib
import Gtz.Basic
import Gtz.Sanity
import Gtz.SchurRankOne
import Gtz.MarginTransfer
import Gtz.TraceIdentity
import Gtz.LeverageBound
import Gtz.Reductions
import Gtz.DescentLadder
import Gtz.ResidueDissolution
import Gtz.TetrahedronCertifiedTie
import Gtz.NonTetrahedralTie
import Gtz.SplitTetrahedronTie

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace Gtz

open Matrix

/-! ### Strict domination of an erasure -/

/-- **The strict pigeonhole step**: with a positive definite base, dropping an insider
dominates STRICTLY exactly when its pivot is `< 1`. Strict twin of the landed
`erase_dominates_iff_pivot_le_one`. -/
theorem erase_strictDominates_iff_pivot_lt_one {m k : ℕ} (D : WeightedDesign m k)
    (Q : Finset (Fin m)) (hQ : (subsetSum D Q - 1).PosDef) {d : Fin m} (hd : d ∈ Q) :
    (subsetSum D (Q.erase d) - 1).PosDef ↔ pivot D Q d < 1 := by
  have hsub : subsetSum D (Q.erase d) - 1
      = (subsetSum D Q - 1) - Matrix.vecMulVec (D.atom d) (D.atom d) := by
    have h := Finset.sum_erase_add Q (fun c => atomMatrix (D.atom c)) hd
    rw [subsetSum, subsetSum, ← h, atomMatrix]
    abel
  rw [hsub, posDef_sub_vecMulVec_iff _ hQ, pivot_eq_dot]

/-! ### At corank one every k-subset is an erasure -/

/-- In `Fin (k+1)` a subset of size `k` is the complement of a single point. -/
theorem exists_erase_eq_of_card_eq {k : ℕ} (C : Finset (Fin (k + 1))) (hC : C.card = k) :
    ∃ c : Fin (k + 1), C = Finset.univ.erase c := by
  have hcompl : Cᶜ.card = 1 := by
    rw [Finset.card_compl, Fintype.card_fin, hC]
    omega
  obtain ⟨c, hc⟩ := Finset.card_eq_one.mp hcompl
  refine ⟨c, ?_⟩
  have hback : C = Cᶜᶜ := (compl_compl C).symm
  rw [hback, hc]
  ext x
  simp only [Finset.mem_compl, Finset.mem_singleton, Finset.mem_erase, Finset.mem_univ,
    and_true]

/-- Erasing one point of `Fin (k+1)` leaves exactly `k` points. -/
theorem card_erase_univ {k : ℕ} (c : Fin (k + 1)) : (Finset.univ.erase c).card = k := by
  rw [Finset.card_erase_of_mem (Finset.mem_univ c), Finset.card_univ, Fintype.card_fin]
  omega

/-! ### The corank-one selector -/

/-- **The corank-one selector, constructively**: at `m = k+1` some atom has pivot `≤ 1`,
and dropping it leaves a dominating `k`-subset. The landed `gtzWeighted_corank_one`
asserts existence by duality; here the dropped atom is NAMED — it is any minimiser of
`pivot D univ`, because the co-weights `1 − t_c` sum to `k` and the co-weighted pivots
sum to `k` (`descent_identity`), so the pivots have co-weighted mean exactly one. -/
theorem corank_one_dominating_erasure {k : ℕ} (hk : 1 ≤ k) (D : WeightedDesign (k + 1) k) :
    ∃ c : Fin (k + 1), pivot D Finset.univ c ≤ 1 ∧
      (Finset.univ.erase c).card = k ∧ Dominates D (Finset.univ.erase c) := by
  have hm : 2 ≤ k + 1 := by omega
  obtain ⟨c, hc⟩ := exists_pivot_le_average D hm
  have hle : pivot D Finset.univ c ≤ 1 := by
    have hcast : ((k + 1 : ℕ) : ℝ) - 1 = (k : ℝ) := by push_cast; ring
    rw [hcast] at hc
    have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
    rwa [div_self (ne_of_gt hkpos)] at hc
  exact ⟨c, hle, card_erase_univ c,
    (erase_dominates_iff_pivot_le_one D Finset.univ (posDef_fullExcess D hm)
      (Finset.mem_univ c)).mpr hle⟩

/-! ### The tie criterion -/

/-- The rigidity behind the criterion: at corank one the pivots have co-weighted mean
exactly one, so if every pivot is at least one then every pivot IS one. -/
theorem forall_pivot_eq_one_of_one_le {k : ℕ} (hk : 1 ≤ k) (D : WeightedDesign (k + 1) k)
    (hall : ∀ c, 1 ≤ pivot D Finset.univ c) : ∀ c, pivot D Finset.univ c = 1 := by
  have hm : 2 ≤ k + 1 := by omega
  have hexcess : ∑ c, (1 - D.weight c) * (pivot D Finset.univ c - 1) = 0 := by
    have hsplit : ∀ c : Fin (k + 1), (1 - D.weight c) * (pivot D Finset.univ c - 1)
        = (1 - D.weight c) * pivot D Finset.univ c - (1 - D.weight c) :=
      fun c => by ring
    simp only [hsplit]
    rw [Finset.sum_sub_distrib, descent_identity D hm, sum_one_sub_weight]
    push_cast
    ring
  have hnonneg : ∀ c ∈ Finset.univ,
      0 ≤ (1 - D.weight c) * (pivot D Finset.univ c - 1) := by
    intro c _
    exact mul_nonneg (one_sub_weight_mem D hm c).1.le (by linarith [hall c])
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hexcess
  intro c
  have hterm := hzero c (Finset.mem_univ c)
  have hpos := (one_sub_weight_mem D hm c).1
  rcases mul_eq_zero.mp hterm with hbad | hgood
  · exact absurd hbad (ne_of_gt hpos)
  · linarith

/-- **THE CORANK-ONE TIE CRITERION.** A design with `m = k+1` is an exact tie
(`Φ = 1`: some `k`-subset dominates, none dominates strictly) if and only if EVERY
pivot against the full excess equals one.

This is the first characterisation of `Gtz.IsTie` in the library: elsewhere `IsTie` is
either hypothesised or witnessed. Both directions are cheap once the strict rank-one
Schur step exists — forward is the rigidity of a mean-one family bounded below by one,
backward is the observation that `q_c = 1` is simultaneously `≤ 1` (weak domination of
the erasure) and not `< 1` (no strict domination), and at corank one there are no other
`k`-subsets to check. -/
theorem isTie_iff_forall_pivot_eq_one {k : ℕ} (hk : 1 ≤ k) (D : WeightedDesign (k + 1) k) :
    IsTie D ↔ ∀ c, pivot D Finset.univ c = 1 := by
  have hm : 2 ≤ k + 1 := by omega
  have hbase : (subsetSum D Finset.univ - 1).PosDef := posDef_fullExcess D hm
  constructor
  · intro htie
    refine forall_pivot_eq_one_of_one_le hk D fun c => ?_
    by_contra hnotle
    rw [not_le] at hnotle
    have hlt : pivot D Finset.univ c < 1 := hnotle
    have hstrict : (subsetSum D (Finset.univ.erase c) - 1).PosDef :=
      (erase_strictDominates_iff_pivot_lt_one D Finset.univ hbase (Finset.mem_univ c)).mpr hlt
    exact htie.2 (Finset.univ.erase c) (card_erase_univ c) hstrict
  · intro hall
    constructor
    · obtain ⟨c, _, hcard, hdom⟩ := corank_one_dominating_erasure hk D
      exact ⟨Finset.univ.erase c, hcard, hdom⟩
    · intro C hcard hstrict
      obtain ⟨c, rfl⟩ := exists_erase_eq_of_card_eq C hcard
      have hlt := (erase_strictDominates_iff_pivot_lt_one D Finset.univ hbase
        (Finset.mem_univ c)).mp hstrict
      rw [hall c] at hlt
      exact lt_irrefl 1 hlt

/-- A one-atom certificate of NON-tieness at corank one: a single pivot below one
already exhibits a strictly dominating `k`-subset, hence refutes `IsTie`. -/
theorem not_isTie_of_pivot_lt_one {k : ℕ} (hk : 1 ≤ k) (D : WeightedDesign (k + 1) k)
    {c : Fin (k + 1)} (hlt : pivot D Finset.univ c < 1) : ¬ IsTie D := by
  intro htie
  have hall := (isTie_iff_forall_pivot_eq_one hk D).mp htie
  rw [hall c] at hlt
  exact lt_irrefl 1 hlt

/-- The tie locus is exactly where the corank-one selector has no slack: at a tie EVERY
erasure dominates, and none does so strictly. -/
theorem forall_dominates_erase_of_isTie {k : ℕ} (hk : 1 ≤ k) (D : WeightedDesign (k + 1) k)
    (htie : IsTie D) (c : Fin (k + 1)) : Dominates D (Finset.univ.erase c) := by
  have hm : 2 ≤ k + 1 := by omega
  have hall := (isTie_iff_forall_pivot_eq_one hk D).mp htie
  exact (erase_dominates_iff_pivot_le_one D Finset.univ (posDef_fullExcess D hm)
    (Finset.mem_univ c)).mpr (le_of_eq (hall c))


/-! ### Parseval and co-Parseval as reproducing identities -/

variable {m k : ℕ}

/-- Parseval reproduces every vector from the atoms: `Σ_c t_c ⟨g_c, x⟩ g_c = x`. -/
theorem parseval_reproduces (D : WeightedDesign m k) (x : Fin k → ℝ) :
    ∑ c, (D.weight c * (D.atom c ⬝ᵥ x)) • D.atom c = x := by
  have hparseval := congrArg (fun M : Matrix (Fin k) (Fin k) ℝ => M *ᵥ x) D.isParseval
  simp only [Matrix.one_mulVec, Matrix.sum_mulVec, Matrix.smul_mulVec] at hparseval
  calc ∑ c, (D.weight c * (D.atom c ⬝ᵥ x)) • D.atom c
      = ∑ c, D.weight c • (atomMatrix (D.atom c) *ᵥ x) := by
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [atomMatrix, vecMulVec_mulVec_eq, smul_smul]
    _ = x := hparseval

/-- The co-Parseval operator reproduces through itself:
`Σ_c (1−t_c) ⟨g_c, x⟩ g_c = (S_[m] − 1) x`. -/
theorem coParseval_reproduces (D : WeightedDesign m k) (x : Fin k → ℝ) :
    ∑ c, ((1 - D.weight c) * (D.atom c ⬝ᵥ x)) • D.atom c
      = (subsetSum D Finset.univ - 1) *ᵥ x := by
  have hco := congrArg (fun M : Matrix (Fin k) (Fin k) ℝ => M *ᵥ x)
    (fullExcess_eq_coParseval D)
  simp only [Matrix.sum_mulVec, Matrix.smul_mulVec] at hco
  calc ∑ c, ((1 - D.weight c) * (D.atom c ⬝ᵥ x)) • D.atom c
      = ∑ c, (1 - D.weight c) • (atomMatrix (D.atom c) *ᵥ x) := by
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [atomMatrix, vecMulVec_mulVec_eq, smul_smul]
    _ = (subsetSum D Finset.univ - 1) *ᵥ x := hco.symm

/-! ### At corank one the dependency space is a line -/

/-- The atom-combination map `a ↦ Σ_c a_c g_c` of a corank-one design. -/
noncomputable def atomCombination (D : WeightedDesign (k + 1) k) :
    (Fin (k + 1) → ℝ) →ₗ[ℝ] (Fin k → ℝ) where
  toFun a := ∑ c, a c • D.atom c
  map_add' a b := by
    simp only [Pi.add_apply, add_smul]
    rw [Finset.sum_add_distrib]
  map_smul' r a := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, ← smul_smul]
    rw [Finset.smul_sum]

theorem atomCombination_apply (D : WeightedDesign (k + 1) k) (a : Fin (k + 1) → ℝ) :
    atomCombination D a = ∑ c, a c • D.atom c := rfl

/-- Parseval makes the atoms span, so the combination map is onto. -/
theorem atomCombination_surjective (D : WeightedDesign (k + 1) k) :
    Function.Surjective (atomCombination D) := fun x =>
  ⟨fun c => D.weight c * (D.atom c ⬝ᵥ x), parseval_reproduces D x⟩

/-- **The dependency line.** At corank one the kernel of the combination map has
dimension exactly one — rank-nullity against the surjectivity above. -/
theorem finrank_ker_atomCombination (D : WeightedDesign (k + 1) k) :
    Module.finrank ℝ (LinearMap.ker (atomCombination D)) = 1 := by
  have hrange : LinearMap.range (atomCombination D) = ⊤ :=
    LinearMap.range_eq_top.mpr (atomCombination_surjective D)
  have hsum := LinearMap.finrank_range_add_finrank_ker (atomCombination D)
  rw [hrange] at hsum
  have hdomain : Module.finrank ℝ (Fin (k + 1) → ℝ) = k + 1 := by
    simp
  have hcodomain : Module.finrank ℝ (⊤ : Submodule ℝ (Fin k → ℝ)) = k := by
    rw [finrank_top]
    simp
  rw [hdomain, hcodomain] at hsum
  omega

/-- **Any two dependencies are proportional** — the corank-one rigidity, in the only
form the argument needs: all `2 × 2` minors of the pair vanish. -/
theorem dependency_cross (D : WeightedDesign (k + 1) k)
    {firstVec secondVec : Fin (k + 1) → ℝ}
    (hfirst : ∑ c, firstVec c • D.atom c = 0)
    (hsecond : ∑ c, secondVec c • D.atom c = 0)
    (indexOne indexTwo : Fin (k + 1)) :
    firstVec indexOne * secondVec indexTwo = firstVec indexTwo * secondVec indexOne := by
  have hmemFirst : firstVec ∈ LinearMap.ker (atomCombination D) := by
    rw [LinearMap.mem_ker, atomCombination_apply]; exact hfirst
  have hmemSecond : secondVec ∈ LinearMap.ker (atomCombination D) := by
    rw [LinearMap.mem_ker, atomCombination_apply]; exact hsecond
  obtain ⟨generator, _, hspan⟩ :=
    finrank_eq_one_iff'.mp (finrank_ker_atomCombination D)
  obtain ⟨scaleFirst, hscaleFirst⟩ := hspan ⟨firstVec, hmemFirst⟩
  obtain ⟨scaleSecond, hscaleSecond⟩ := hspan ⟨secondVec, hmemSecond⟩
  have hfirstEq : firstVec = scaleFirst • (generator : Fin (k + 1) → ℝ) := by
    have := congrArg (fun z : LinearMap.ker (atomCombination D) =>
      (z : Fin (k + 1) → ℝ)) hscaleFirst
    simpa using this.symm
  have hsecondEq : secondVec = scaleSecond • (generator : Fin (k + 1) → ℝ) := by
    have := congrArg (fun z : LinearMap.ker (atomCombination D) =>
      (z : Fin (k + 1) → ℝ)) hscaleSecond
    simpa using this.symm
  rw [hfirstEq, hsecondEq]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-! ### The two dependency families -/

/-- The Parseval row: `Z_c` with `Z_cd = t_c t_d ⟨g_c,g_d⟩ − t_c [c=d]`. -/
noncomputable def parsevalRow (D : WeightedDesign m k) (c d : Fin m) : ℝ :=
  D.weight c * D.weight d * (D.atom c ⬝ᵥ D.atom d)
    - D.weight c * (if c = d then 1 else 0)

/-- The co-Parseval row: `Z'_c` with
`Z'_cd = (1−t_c)(1−t_d) ⟨g_c, W⁻¹ g_d⟩ − (1−t_c)[c=d]`, `W = S_[m] − 1`. -/
noncomputable def resolventRow (D : WeightedDesign m k) (c d : Fin m) : ℝ :=
  (1 - D.weight c) * (1 - D.weight d)
      * (D.atom c ⬝ᵥ ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ D.atom d))
    - (1 - D.weight c) * (if c = d then 1 else 0)

/-- Every Parseval row is a dependency of the atoms. -/
theorem parsevalRow_isDependency (D : WeightedDesign m k) (c : Fin m) :
    ∑ d, parsevalRow D c d • D.atom d = 0 := by
  have hsplit : ∀ d : Fin m, parsevalRow D c d • D.atom d
      = D.weight c • ((D.weight d * (D.atom d ⬝ᵥ D.atom c)) • D.atom d)
        - D.weight c • ((if c = d then (1 : ℝ) else 0) • D.atom d) := by
    intro d
    have hassoc : D.weight c * D.weight d * (D.atom c ⬝ᵥ D.atom d)
        = D.weight c * (D.weight d * (D.atom d ⬝ᵥ D.atom c)) := by
      rw [dotProduct_comm (D.atom d) (D.atom c)]; ring
    rw [parsevalRow, sub_smul, smul_smul, smul_smul, hassoc]
  simp only [hsplit]
  rw [Finset.sum_sub_distrib, ← Finset.smul_sum, ← Finset.smul_sum,
    parseval_reproduces D (D.atom c)]
  have hsingle : ∑ d, (if c = d then (1 : ℝ) else 0) • D.atom d = D.atom c := by
    rw [Finset.sum_eq_single c]
    · simp
    · intro d _ hne
      rw [if_neg (Ne.symm hne), zero_smul]
    · intro hc
      exact absurd (Finset.mem_univ c) hc
  rw [hsingle, sub_self]

/-- Every co-Parseval row is a dependency of the atoms. -/
theorem resolventRow_isDependency (D : WeightedDesign m k) (hm : 2 ≤ m) (c : Fin m) :
    ∑ d, resolventRow D c d • D.atom d = 0 := by
  have hposDef : (subsetSum D Finset.univ - 1).PosDef := posDef_fullExcess D hm
  have hdet : IsUnit (subsetSum D Finset.univ - 1).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt hposDef.det_pos)
  have hsymm : ((subsetSum D Finset.univ - 1)⁻¹)ᵀ = (subsetSum D Finset.univ - 1)⁻¹ :=
    PosDef.transpose_eq hposDef.inv
  have hswap : ∀ d : Fin m,
      D.atom c ⬝ᵥ ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ D.atom d)
        = D.atom d ⬝ᵥ ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ D.atom c) :=
    fun d => dot_mulVec_comm hsymm (D.atom c) (D.atom d)
  have hsplit : ∀ d : Fin m, resolventRow D c d • D.atom d
      = (1 - D.weight c) • (((1 - D.weight d)
            * (D.atom d ⬝ᵥ ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ D.atom c))) • D.atom d)
        - (1 - D.weight c) • ((if c = d then (1 : ℝ) else 0) • D.atom d) := by
    intro d
    have hassoc : (1 - D.weight c) * (1 - D.weight d)
          * (D.atom d ⬝ᵥ ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ D.atom c))
        = (1 - D.weight c) * ((1 - D.weight d)
          * (D.atom d ⬝ᵥ ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ D.atom c))) := by ring
    rw [resolventRow, hswap d, sub_smul, smul_smul, smul_smul, hassoc]
  simp only [hsplit]
  rw [Finset.sum_sub_distrib, ← Finset.smul_sum, ← Finset.smul_sum,
    coParseval_reproduces D ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ D.atom c),
    Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  have hsingle : ∑ d, (if c = d then (1 : ℝ) else 0) • D.atom d = D.atom c := by
    rw [Finset.sum_eq_single c]
    · simp
    · intro d _ hne
      rw [if_neg (Ne.symm hne), zero_smul]
    · intro hc
      exact absurd (Finset.mem_univ c) hc
  rw [hsingle, sub_self]

/-- Both row families are symmetric in their two indices. -/
theorem parsevalRow_symm (D : WeightedDesign m k) (c d : Fin m) :
    parsevalRow D c d = parsevalRow D d c := by
  rw [parsevalRow, parsevalRow, dotProduct_comm]
  rcases eq_or_ne c d with rfl | hne
  · ring
  · rw [if_neg hne, if_neg (Ne.symm hne)]
    ring

theorem resolventRow_symm (D : WeightedDesign m k) (hm : 2 ≤ m) (c d : Fin m) :
    resolventRow D c d = resolventRow D d c := by
  have hposDef : (subsetSum D Finset.univ - 1).PosDef := posDef_fullExcess D hm
  have hsymm : ((subsetSum D Finset.univ - 1)⁻¹)ᵀ = (subsetSum D Finset.univ - 1)⁻¹ :=
    PosDef.transpose_eq hposDef.inv
  rw [resolventRow, resolventRow, dot_mulVec_comm hsymm (D.atom c) (D.atom d)]
  rcases eq_or_ne c d with rfl | hne
  · ring
  · rw [if_neg hne, if_neg (Ne.symm hne)]
    ring

/-! ### The cross identity -/

/-- **The corank-one cross identity**: the two row families have all their rows on one
line, so their diagonals satisfy `Z_cc Z'_dd = Z_dd Z'_cc`. -/
theorem row_cross_identity (D : WeightedDesign (k + 1) k) (hk : 1 ≤ k)
    (c d : Fin (k + 1)) :
    parsevalRow D c c * resolventRow D d d = parsevalRow D d d * resolventRow D c c := by
  have hm : 2 ≤ k + 1 := by omega
  -- rows `Z_c` and `Z'_d`, read at the index pair `(d, c)`
  have hfirst := dependency_cross D (parsevalRow_isDependency D c)
    (resolventRow_isDependency D hm d) d c
  -- rows `Z_d` and `Z'_c`, read at the index pair `(c, d)`
  have hsecond := dependency_cross D (parsevalRow_isDependency D d)
    (resolventRow_isDependency D hm c) c d
  rw [← hfirst, ← hsecond, parsevalRow_symm D c d, resolventRow_symm D hm d c]

/-! ### The leverage form of the tie criterion -/

/-- At a corank-one tie, the co-Parseval diagonal collapses: `Z'_cc = −t_c(1−t_c)`. -/
theorem resolventRow_diag_of_pivot_eq_one (D : WeightedDesign m k)
    {c : Fin m} (hpivot : pivot D Finset.univ c = 1) :
    resolventRow D c c = -(D.weight c * (1 - D.weight c)) := by
  have hdot : D.atom c ⬝ᵥ ((subsetSum D Finset.univ - 1)⁻¹ *ᵥ D.atom c) = 1 := by
    rw [← pivot_eq_dot]; exact hpivot
  rw [resolventRow, hdot, if_pos rfl]
  ring

/-- The Parseval diagonal is the leverage defect: `Z_cc = −t_c(1 − t_c ℓ_c)`. -/
theorem parsevalRow_diag (D : WeightedDesign m k) (c : Fin m) :
    parsevalRow D c c = -(D.weight c * (1 - D.weight c * leverageOf (D.atom c))) := by
  rw [parsevalRow, if_pos rfl, ← leverageOf_eq_dotProduct]
  ring

/-- **THE LEVERAGE FORM.** Pivots all equal to one force, at every atom,
`k · t_c · ℓ_c = (k − 1) + t_c`. Weights and leverages alone decide it: no resolvent, no
inverse, no eigenvalue. -/
theorem leverage_identity_of_forall_pivot_eq_one {k : ℕ} (hk : 1 ≤ k)
    (D : WeightedDesign (k + 1) k)
    (hpivot : ∀ c, pivot D Finset.univ c = 1) (c : Fin (k + 1)) :
    (k : ℝ) * D.weight c * leverageOf (D.atom c) = ((k : ℝ) - 1) + D.weight c := by
  have hm : 2 ≤ k + 1 := by omega
  -- the cross identity, with both diagonals evaluated
  have hratio : ∀ e f : Fin (k + 1),
      (1 - D.weight e * leverageOf (D.atom e)) * (1 - D.weight f)
        = (1 - D.weight f * leverageOf (D.atom f)) * (1 - D.weight e) := by
    intro e f
    have hcross := row_cross_identity D hk e f
    rw [parsevalRow_diag D e, parsevalRow_diag D f,
      resolventRow_diag_of_pivot_eq_one D (hpivot f),
      resolventRow_diag_of_pivot_eq_one D (hpivot e)] at hcross
    have hepos := D.weight_pos e
    have hfpos := D.weight_pos f
    have hexpand : D.weight e * D.weight f
        * ((1 - D.weight e * leverageOf (D.atom e)) * (1 - D.weight f))
        = D.weight e * D.weight f
        * ((1 - D.weight f * leverageOf (D.atom f)) * (1 - D.weight e)) := by
      nlinarith [hcross]
    have hprodpos : 0 < D.weight e * D.weight f := mul_pos hepos hfpos
    exact mul_left_cancel₀ (ne_of_gt hprodpos) hexpand
  -- sum the ratio identity over the first index
  have hsumLeverage : ∑ e, (1 - D.weight e * leverageOf (D.atom e)) = 1 := by
    have hlev := sum_weighted_leverage D
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one, hlev]
    push_cast
    ring
  have hsumWeight : ∑ e, (1 - D.weight e) = (k : ℝ) := by
    have hone := sum_one_sub_weight D
    rw [hone]
    push_cast
    ring
  have hsummed : (1 - D.weight c) = (1 - D.weight c * leverageOf (D.atom c)) * (k : ℝ) := by
    have hstep : ∑ e, (1 - D.weight e * leverageOf (D.atom e)) * (1 - D.weight c)
        = ∑ e, (1 - D.weight c * leverageOf (D.atom c)) * (1 - D.weight e) :=
      Finset.sum_congr rfl fun e _ => hratio e c
    rw [← Finset.sum_mul, ← Finset.mul_sum, hsumLeverage, hsumWeight, one_mul] at hstep
    exact hstep
  linarith [hsummed]

/-! ### The criterion, both shapes -/

/-- The converse leg: the leverage relation forces every pivot to one. Same cross
identity, run the other way — the relation makes `k · Z_cc = −t_c(1−t_c)`, so the cross
identity says `t_c u_d = t_d u_c` for `u_c = (1−t_c) q_c − 1`, and `Σ u_c = −1`
(`descent_identity`) then pins `u_c = −t_c`, i.e. `q_c = 1`. -/
theorem forall_pivot_eq_one_of_leverage_identity {k : ℕ} (hk : 1 ≤ k)
    (D : WeightedDesign (k + 1) k)
    (hleverage : ∀ c, (k : ℝ) * D.weight c * leverageOf (D.atom c)
      = ((k : ℝ) - 1) + D.weight c) (c : Fin (k + 1)) :
    pivot D Finset.univ c = 1 := by
  have hm : 2 ≤ k + 1 := by omega
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  -- abbreviation for the resolvent defect
  set defect : Fin (k + 1) → ℝ :=
    fun e => (1 - D.weight e) * pivot D Finset.univ e - 1 with hdefect
  have hresolventDiag : ∀ e, resolventRow D e e = (1 - D.weight e) * defect e := by
    intro e
    rw [resolventRow, if_pos rfl, hdefect, ← pivot_eq_dot]
    ring
  have hparsevalDiag : ∀ e, (k : ℝ) * parsevalRow D e e
      = -(D.weight e * (1 - D.weight e)) := by
    intro e
    rw [parsevalRow_diag D e]
    linear_combination D.weight e * hleverage e
  -- the cross identity, divided by the positive co-weights
  have hpair : ∀ e f : Fin (k + 1), D.weight e * defect f = D.weight f * defect e := by
    intro e f
    have hcross := row_cross_identity D hk e f
    have hscaled : ((k : ℝ) * parsevalRow D e e) * resolventRow D f f
        = ((k : ℝ) * parsevalRow D f f) * resolventRow D e e := by
      rw [mul_assoc, mul_assoc, hcross]
    rw [hparsevalDiag e, hparsevalDiag f, hresolventDiag e, hresolventDiag f] at hscaled
    have hepos := (one_sub_weight_mem D hm e).1
    have hfpos := (one_sub_weight_mem D hm f).1
    have hprod : (1 - D.weight e) * (1 - D.weight f)
        * (D.weight e * defect f) = (1 - D.weight e) * (1 - D.weight f)
        * (D.weight f * defect e) := by nlinarith [hscaled]
    exact mul_left_cancel₀ (ne_of_gt (mul_pos hepos hfpos)) hprod
  -- the defects sum to −1
  have hsumDefect : ∑ e, defect e = -1 := by
    have hsplit : ∀ e : Fin (k + 1), defect e
        = (1 - D.weight e) * pivot D Finset.univ e - 1 := fun e => rfl
    simp only [hsplit]
    rw [Finset.sum_sub_distrib, descent_identity D hm, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    push_cast
    ring
  -- summing the pairing over the second index pins the defect
  have hpinned : defect c = -D.weight c := by
    have hstep : ∑ f, D.weight c * defect f = ∑ f, D.weight f * defect c :=
      Finset.sum_congr rfl fun f _ => hpair c f
    rw [← Finset.mul_sum, ← Finset.sum_mul, hsumDefect, D.weight_sum_one, one_mul] at hstep
    linarith [hstep]
  have hcopos := (one_sub_weight_mem D hm c).1
  have hfinal : (1 - D.weight c) * pivot D Finset.univ c = 1 - D.weight c := by
    have := hpinned
    rw [hdefect] at this
    simp only at this
    linarith [this]
  exact mul_left_cancel₀ (ne_of_gt hcopos) (by rw [hfinal, mul_one])

/-- **THE CORANK-ONE TIE CRITERION.** At `m = k+1` a design is an exact tie exactly when
its weighted leverages satisfy the affine relation `k t_c ℓ_c = (k−1) + t_c` at every
atom. Ties are therefore a graph over the open weight simplex: the relation determines
`t_c ℓ_c` from `t_c` alone, atom by atom. -/
theorem isTie_iff_leverage_identity {k : ℕ} (hk : 1 ≤ k) (D : WeightedDesign (k + 1) k) :
    IsTie D ↔ ∀ c, (k : ℝ) * D.weight c * leverageOf (D.atom c)
      = ((k : ℝ) - 1) + D.weight c := by
  constructor
  · intro htie
    exact leverage_identity_of_forall_pivot_eq_one hk D
      ((isTie_iff_forall_pivot_eq_one hk D).mp htie)
  · intro hleverage
    exact (isTie_iff_forall_pivot_eq_one hk D).mpr
      (forall_pivot_eq_one_of_leverage_identity hk D hleverage)

/-! ### Regression against the landed tie witnesses

The criterion must FIRE on the repository's own exact ties. It does, and on the
non-tetrahedral one it delivers a fact that was previously only hand-checkable: at
`sharpDesign` the leverages are UNEQUAL (`4/3` against `19/3`) yet each sits on the
affine relation, because each weight is different too. -/

/-- `tetraDesign` (uniform weights `1/4`, leverages `3`) obeys the criterion. -/
theorem tetraDesign_leverage_identity (c : Fin 4) :
    (3 : ℝ) * tetraDesign.weight c * leverageOf (tetraDesign.atom c)
      = ((3 : ℝ) - 1) + tetraDesign.weight c :=
  (isTie_iff_leverage_identity (k := 3) (by omega) tetraDesign).mp tetraDesign_isTie c

/-- `sharpDesign` (weights `2/3, 1/9, 1/9, 1/9`; leverages `4/3, 19/3, 19/3, 19/3`)
obeys the criterion — the tie locus is NOT confined to equal leverages. -/
theorem sharpDesign_leverage_identity (c : Fin 4) :
    (3 : ℝ) * sharpDesign.weight c * leverageOf (sharpDesign.atom c)
      = ((3 : ℝ) - 1) + sharpDesign.weight c :=
  (isTie_iff_leverage_identity (k := 3) (by omega) sharpDesign).mp sharpDesign_isTie c

/-! ### The identity forces corank one -/

/-- **The leverage identity forces `m = k + 1`** (for `k ≥ 2`). Summing it over the
atoms gives `k · Σ_c t_c ℓ_c = m(k−1) + 1`, and Parseval's trace
(`sum_weighted_leverage`) makes the left side `k²`, so `m(k−1) = (k−1)(k+1)`. No design
of any other size — tie or not — satisfies the identity at every atom. -/
theorem leverage_identity_forces_corank_one (D : WeightedDesign m k) (hk : 2 ≤ k)
    (hlaw : ∀ c, (k : ℝ) * D.weight c * leverageOf (D.atom c)
      = ((k : ℝ) - 1) + D.weight c) :
    m = k + 1 := by
  have hsummed : ∑ c, ((k : ℝ) * D.weight c * leverageOf (D.atom c))
      = ∑ c, (((k : ℝ) - 1) + D.weight c) :=
    Finset.sum_congr rfl fun c _ => hlaw c
  have hleft : ∑ c, ((k : ℝ) * D.weight c * leverageOf (D.atom c))
      = (k : ℝ) * (k : ℝ) := by
    have hpull : ∑ c, ((k : ℝ) * D.weight c * leverageOf (D.atom c))
        = (k : ℝ) * ∑ c, (D.weight c * leverageOf (D.atom c)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun c _ => by ring
    rw [hpull, sum_weighted_leverage]
  have hright : ∑ c, (((k : ℝ) - 1) + D.weight c) = (m : ℝ) * ((k : ℝ) - 1) + 1 := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      D.weight_sum_one, nsmul_eq_mul]
  rw [hleft, hright] at hsummed
  have hklower : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hne : (k : ℝ) - 1 ≠ 0 := by linarith
  have hcast : (m : ℝ) = (k : ℝ) + 1 := by
    have hfactored : ((m : ℝ) - ((k : ℝ) + 1)) * ((k : ℝ) - 1) = 0 := by
      nlinarith [hsummed]
    rcases mul_eq_zero.mp hfactored with hzero | hzero
    · linarith
    · exact absurd hzero hne
  have hnat : ((m : ℕ) : ℝ) = ((k + 1 : ℕ) : ℝ) := by push_cast; exact hcast
  exact_mod_cast hnat

/-- No `(6,3)` design satisfies the identity at every atom — the two open residuals
live strictly beyond its reach. -/
theorem no_leverage_identity_at_six_three (D : WeightedDesign 6 3) :
    ¬ ∀ c, ((3 : ℕ) : ℝ) * D.weight c * leverageOf (D.atom c)
      = (((3 : ℕ) : ℝ) - 1) + D.weight c := by
  intro hlaw
  have hforced := leverage_identity_forces_corank_one D (by norm_num) hlaw
  omega

/-- No corank-two design carries the identity either. -/
theorem no_leverage_identity_at_corank_two (rank : ℕ) (hrank : 2 ≤ rank)
    (D : WeightedDesign (rank + 2) rank) :
    ¬ ∀ c, (rank : ℝ) * D.weight c * leverageOf (D.atom c)
      = ((rank : ℝ) - 1) + D.weight c := by
  intro hlaw
  have hforced := leverage_identity_forces_corank_one D hrank hlaw
  omega

/-- **Ties beyond corank one exist and violate the identity**: the landed `(6,3)`
split-tetrahedron tie at split `(1/8, 1/8)` is an exact tie and — like every `(6,3)`
design — fails the identity. The corank-one classification does not see the open
residuals. -/
theorem exists_isTie_leverage_identity_fails :
    ∃ D : WeightedDesign 6 3, IsTie D ∧
      ¬ ∀ c, ((3 : ℕ) : ℝ) * D.weight c * leverageOf (D.atom c)
        = (((3 : ℕ) : ℝ) - 1) + D.weight c :=
  ⟨splitTetraDesign (1/8) (1/8) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    splitTetraDesign_isTie (1/8) (1/8) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num),
    no_leverage_identity_at_six_three _⟩

/-! ### Sharpness: the identity discriminates, and the rank hypothesis is necessary -/

/-- A corank-one design OFF the tie locus: atoms `(2)` and `(1/2)` on the line with
weights `(1/5, 4/5)` — Parseval reads `(1/5)·4 + (4/5)·(1/4) = 1`. At `k = 1` the
identity forces unit atoms; the first atom has leverage `4`. -/
noncomputable def unevenPairDesign : WeightedDesign 2 1 where
  atom := ![![2], ![1/2]]
  weight := ![1/5, 4/5]
  weight_pos := by
    intro atomIndex
    fin_cases atomIndex
    · exact (by norm_num : (0 : ℝ) < 1/5)
    · exact (by norm_num : (0 : ℝ) < 4/5)
  weight_sum_one := by
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    norm_num
  isParseval := by
    ext row col
    fin_cases row
    fin_cases col
    simp only [Matrix.sum_apply, Matrix.smul_apply, atomMatrix, Matrix.vecMulVec_apply,
      Fin.sum_univ_two, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.one_apply_eq]
    norm_num

theorem unevenPairDesign_leverage_identity_fails :
    ¬ ∀ c, ((1 : ℕ) : ℝ) * unevenPairDesign.weight c * leverageOf (unevenPairDesign.atom c)
      = (((1 : ℕ) : ℝ) - 1) + unevenPairDesign.weight c := by
  intro hall
  have hviolated := hall 0
  norm_num [unevenPairDesign, leverageOf, Fin.sum_univ_one, Matrix.cons_val_zero]
    at hviolated

/-- The classification rules the design out: it is not a tie. -/
theorem unevenPairDesign_not_isTie : ¬ IsTie unevenPairDesign := fun htie =>
  unevenPairDesign_leverage_identity_fails
    ((isTie_iff_leverage_identity (k := 1) (by omega) unevenPairDesign).mp htie)

/-- Independently of the classification, the singleton `{0}` strictly dominates — its
gap matrix is the `1 × 1` matrix `(3)`. Criterion and ground truth agree on a
discriminating instance. -/
theorem unevenPairDesign_strictDominator :
    (subsetSum unevenPairDesign {0} - 1).PosDef := by
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨?_, fun probe hprobe => ?_⟩
  · exact ((Matrix.posSemidef_sum ({0} : Finset (Fin 2)) fun atomIndex _ =>
      posSemidef_atomMatrix (unevenPairDesign.atom atomIndex)).1).sub
      Matrix.isHermitian_one
  · have hentry : probe 0 ≠ 0 := by
      intro hzero
      exact hprobe (funext fun index => (Subsingleton.elim index 0) ▸ hzero)
    have hexpand : star probe ⬝ᵥ ((subsetSum unevenPairDesign {0} - 1) *ᵥ probe)
        = 3 * (probe 0 * probe 0) := by
      simp only [star_trivial, subsetSum, Finset.sum_singleton, dotProduct,
        Matrix.sub_apply, Matrix.mulVec, atomMatrix, Matrix.vecMulVec_apply,
        Matrix.one_apply, Fin.sum_univ_one, unevenPairDesign, Matrix.cons_val_zero]
      norm_num
      ring
    rw [hexpand]
    have hsq : 0 < probe 0 * probe 0 := mul_self_pos.mpr hentry
    linarith

/-- **The rank hypothesis is necessary.** At `k = 0` the unique one-atom design
satisfies the identity — it reads `0 = −1 + 1` — yet it is not a tie: the empty subset
has cardinality `k`, and its `0 × 0` gap matrix is vacuously positive definite. -/
theorem exists_leverage_identity_not_isTie_rank_zero :
    ∃ D : WeightedDesign 1 0,
      (∀ c, ((0 : ℕ) : ℝ) * D.weight c * leverageOf (D.atom c)
        = (((0 : ℕ) : ℝ) - 1) + D.weight c) ∧ ¬ IsTie D := by
  refine ⟨{ atom := fun _ => ![]
            weight := fun _ => 1
            weight_pos := fun _ => one_pos
            weight_sum_one := by simp
            isParseval := by ext i; exact absurd i.isLt (Nat.not_lt_zero _) }, ?_, ?_⟩
  · intro c
    show ((0 : ℕ) : ℝ) * 1 * leverageOf ![] = (((0 : ℕ) : ℝ) - 1) + 1
    norm_num
  · intro htie
    refine htie.2 (∅ : Finset (Fin 1)) rfl
      (Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨?_, fun x hx => ?_⟩)
    · ext i
      exact absurd i.isLt (Nat.not_lt_zero _)
    · exfalso
      apply hx
      funext i
      exact absurd i.isLt (Nat.not_lt_zero _)

end Gtz
