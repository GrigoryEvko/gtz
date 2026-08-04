import Mathlib
import Gtz.Reduction.ConnectednessRoute
import Gtz.Design.MarginTransfer

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-
# The forced stress sign-split

Foundation of the (7,3) syzygy lane.  At size seven and rank three every
design carries a stress -- `7 > 6 = dim Sym²(ℝ³)` -- and this file proves the
structural law that makes the stress USABLE as a selector rather than as a
weight walk: a full-support stress of a spanning atom family has at least
`rank` atoms on EACH sign side.  At `(7,3)` that forces the sign split to be
exactly `(3,4)` up to global sign, with both sides spanning; the positive
side of the (unique up to scale) syzygy is therefore a canonical triple.

The statements are rank-uniform on purpose: the k = N program needs the same
law at `(k(k+1)/2 + 1, k)` for every `k`, where a stress is forced over ℝ but
not over ℂ (`k(k+1)/2 + 1 ≤ k²` for `k ≥ 2`) -- the realness consumption is
the dimension count itself.

Vocabulary matches the shipped stress layer verbatim: a stress is
`∑ c, z c • Gtz.atomMatrix (v c) = 0`, exactly the hypothesis of
`Gtz.exists_rescaledReducedDesign_of_stress` (StressConditionalWalk.lean).
That walk REDUCES a stressed design; nothing in the tree reads the sign
split of the stress, which is what this file supplies.
-/

namespace Gtz

open Gtz Matrix Finset

variable {n k : ℕ}

/-- The quadratic form of a coefficient combination of atom matrices is the
coefficient-weighted sum of squared atom pairings.  Shared engine for the
stress law (coefficients summing to the zero matrix) and the Parseval law
(coefficients `weight` summing to `1`). -/
theorem weighted_atomForm_eq (coeff : Fin n → ℝ) (v : Fin n → Fin k → ℝ)
    (x : Fin k → ℝ) :
    x ⬝ᵥ ((∑ c, coeff c • Gtz.atomMatrix (v c)) *ᵥ x)
      = ∑ c, coeff c * (v c ⬝ᵥ x) ^ 2 := by
  rw [Matrix.sum_mulVec, dotProduct_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Gtz.atom_form_eq_sq]

/-- A stress annihilates the weighted squares along every probe direction. -/
theorem stress_kills_weighted_squares {v : Fin n → Fin k → ℝ} {z : Fin n → ℝ}
    (hstress : ∑ c, z c • Gtz.atomMatrix (v c) = 0) (x : Fin k → ℝ) :
    ∑ c, z c * (v c ⬝ᵥ x) ^ 2 = 0 := by
  have happlied := congrArg (fun M : Matrix (Fin k) (Fin k) ℝ => x ⬝ᵥ (M *ᵥ x)) hstress
  simpa [weighted_atomForm_eq, Matrix.zero_mulVec, dotProduct_zero] using happlied

/-- **The transfer law of a stress.**  A probe direction orthogonal to every
positive-side atom is orthogonal to every negative-side atom: the two sides
of a stress span the same space, seen dually.  This is the coupling the
`(7,3)` selector rides -- failure data on the canonical triple transfers
through the syzygy to the complementary four atoms. -/
theorem neg_side_orthogonal_of_pos_side {v : Fin n → Fin k → ℝ} {z : Fin n → ℝ}
    (hstress : ∑ c, z c • Gtz.atomMatrix (v c) = 0) {x : Fin k → ℝ}
    (hposSide : ∀ c, 0 < z c → v c ⬝ᵥ x = 0) :
    ∀ c, z c < 0 → v c ⬝ᵥ x = 0 := by
  have hsum := stress_kills_weighted_squares hstress x
  have hterm : ∀ c ∈ Finset.univ, 0 ≤ -(z c * (v c ⬝ᵥ x) ^ 2) := by
    intro c _
    rcases lt_trichotomy (z c) 0 with hneg | hzero | hpos
    · have hnonpos : z c * (v c ⬝ᵥ x) ^ 2 ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hneg.le (sq_nonneg _)
      linarith
    · simp [hzero]
    · rw [hposSide c hpos]
      simp
  have hnegsum : ∑ c, -(z c * (v c ⬝ᵥ x) ^ 2) = 0 := by
    have hdistrib : ∑ c, -(z c * (v c ⬝ᵥ x) ^ 2)
        = -∑ c, z c * (v c ⬝ᵥ x) ^ 2 := by
      simp
    rw [hdistrib, hsum, neg_zero]
  have hall := (Finset.sum_eq_zero_iff_of_nonneg hterm).mp hnegsum
  intro c hc
  have hvanish : z c * (v c ⬝ᵥ x) ^ 2 = 0 :=
    neg_eq_zero.mp (hall c (Finset.mem_univ c))
  rcases mul_eq_zero.mp hvanish with hcoeff | hsquare
  · exact absurd hcoeff (ne_of_lt hc)
  · exact (pow_eq_zero_iff two_ne_zero).mp hsquare

/-- Fewer than `k` prescribed atoms leave a nonzero orthogonal probe
direction in `ℝᵏ`: the evaluation map into `↥S → ℝ` cannot be injective when
`S.card < k`.  Rank-nullity packaged for the split law. -/
theorem exists_ne_zero_orthogonal_of_card_lt (v : Fin n → Fin k → ℝ)
    (S : Finset (Fin n)) (hcard : S.card < k) :
    ∃ x : Fin k → ℝ, x ≠ 0 ∧ ∀ c ∈ S, v c ⬝ᵥ x = 0 := by
  by_contra hcontra
  push Not at hcontra
  let evalMap : (Fin k → ℝ) →ₗ[ℝ] (↥S → ℝ) :=
    { toFun := fun x memb => v memb.1 ⬝ᵥ x
      map_add' := fun x y => by
        funext memb
        simp [dotProduct_add]
      map_smul' := fun a x => by
        funext memb
        simp [dotProduct_smul] }
  have hker : ∀ x, evalMap x = 0 → x = 0 := by
    intro x hx
    by_contra hxne
    obtain ⟨c, hcS, hcne⟩ := hcontra x hxne
    exact hcne (by simpa [evalMap] using congrFun hx ⟨c, hcS⟩)
  have hinj : Function.Injective evalMap :=
    LinearMap.ker_eq_bot.mp (LinearMap.ker_eq_bot'.mpr hker)
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card,
    Fintype.card_fin, Fintype.card_coe] at hle
  omega

/-- **The split law, positive side, rank-uniform.**  A full-support stress of
a spanning atom family carries at least `rank` atoms of positive stress
coefficient.  At `(k(k+1)/2 + 1, k)` -- where a stress is FORCED over ℝ --
this is the structural half of the canonical-selector construction. -/
theorem rank_le_card_pos_side (v : Fin n → Fin k → ℝ)
    (hspan : ∀ x : Fin k → ℝ, (∀ c, v c ⬝ᵥ x = 0) → x = 0)
    {z : Fin n → ℝ} (hstress : ∑ c, z c • Gtz.atomMatrix (v c) = 0)
    (hfull : ∀ c, z c ≠ 0) :
    k ≤ (Finset.univ.filter fun c => 0 < z c).card := by
  by_contra hnot
  push Not at hnot
  obtain ⟨x, hxne, hxorth⟩ :=
    exists_ne_zero_orthogonal_of_card_lt v (Finset.univ.filter fun c => 0 < z c) hnot
  have hposSide : ∀ c, 0 < z c → v c ⬝ᵥ x = 0 := fun c hc =>
    hxorth c (Finset.mem_filter.mpr ⟨Finset.mem_univ c, hc⟩)
  have hnegSide := neg_side_orthogonal_of_pos_side hstress hposSide
  refine hxne (hspan x fun c => ?_)
  rcases lt_or_lt_iff_ne.mpr (hfull c) with hlt | hgt
  · exact hnegSide c hlt
  · exact hposSide c hgt

/-- The split law, negative side, by applying the positive side to `-z`. -/
theorem rank_le_card_neg_side (v : Fin n → Fin k → ℝ)
    (hspan : ∀ x : Fin k → ℝ, (∀ c, v c ⬝ᵥ x = 0) → x = 0)
    {z : Fin n → ℝ} (hstress : ∑ c, z c • Gtz.atomMatrix (v c) = 0)
    (hfull : ∀ c, z c ≠ 0) :
    k ≤ (Finset.univ.filter fun c => z c < 0).card := by
  have hstressNeg : ∑ c, (-z) c • Gtz.atomMatrix (v c) = 0 := by
    have hpointwise : ∀ c ∈ Finset.univ,
        (-z) c • Gtz.atomMatrix (v c) = -(z c • Gtz.atomMatrix (v c)) := by
      intro c _
      rw [Pi.neg_apply, neg_smul]
    rw [Finset.sum_congr rfl hpointwise]
    simp [hstress]
  have hfullNeg : ∀ c, (-z) c ≠ 0 := fun c => by
    simpa using neg_ne_zero.mpr (hfull c)
  have hcard := rank_le_card_pos_side v hspan hstressNeg hfullNeg
  have hfilter : (Finset.univ.filter fun c => 0 < (-z) c)
      = (Finset.univ.filter fun c => z c < 0) := by
    ext c
    simp
  rwa [hfilter] at hcard

/-- Both sign sides of a full-support stress span, stated dually: a probe
direction orthogonal to the positive side alone is already zero. -/
theorem pos_side_spans (v : Fin n → Fin k → ℝ)
    (hspan : ∀ x : Fin k → ℝ, (∀ c, v c ⬝ᵥ x = 0) → x = 0)
    {z : Fin n → ℝ} (hstress : ∑ c, z c • Gtz.atomMatrix (v c) = 0)
    (hfull : ∀ c, z c ≠ 0) :
    ∀ x : Fin k → ℝ, (∀ c, 0 < z c → v c ⬝ᵥ x = 0) → x = 0 := by
  intro x hposSide
  have hnegSide := neg_side_orthogonal_of_pos_side hstress hposSide
  refine hspan x fun c => ?_
  rcases lt_or_lt_iff_ne.mpr (hfull c) with hlt | hgt
  · exact hnegSide c hlt
  · exact hposSide c hgt

/-- No spanning family carries an all-positive full-support stress: the
trace argument, subsumed by the split law.  (`0 < k` rules out the empty
rank, where everything spans vacuously.) -/
theorem no_all_positive_stress (v : Fin n → Fin k → ℝ)
    (hspan : ∀ x : Fin k → ℝ, (∀ c, v c ⬝ᵥ x = 0) → x = 0)
    {z : Fin n → ℝ} (hstress : ∑ c, z c • Gtz.atomMatrix (v c) = 0)
    (hallpos : ∀ c, 0 < z c) (hk : 0 < k) : False := by
  have hcard := rank_le_card_neg_side v hspan hstress (fun c => ne_of_gt (hallpos c))
  have hempty : (Finset.univ.filter fun c : Fin n => z c < 0) = ∅ :=
    Finset.filter_false_of_mem fun c _ => asymm (hallpos c)
  rw [hempty, Finset.card_empty] at hcard
  omega

/-- **The `(7,3)` forced split.**  A full-support stress of a spanning
seven-atom rank-three family splits exactly `(3,4)` or `(4,3)` by sign.
The impossible splits die structurally: `(0,7)` and `(7,0)` by the trace,
`(1,6)`/`(2,5)` and mirrors because a side of fewer than three atoms would
confine every atom to a proper subspace through the transfer law. -/
theorem sevenThree_stress_split (v : Fin 7 → Fin 3 → ℝ)
    (hspan : ∀ x : Fin 3 → ℝ, (∀ c, v c ⬝ᵥ x = 0) → x = 0)
    {z : Fin 7 → ℝ} (hstress : ∑ c, z c • Gtz.atomMatrix (v c) = 0)
    (hfull : ∀ c, z c ≠ 0) :
    ((Finset.univ.filter fun c => 0 < z c).card = 3
        ∧ (Finset.univ.filter fun c => z c < 0).card = 4)
      ∨ ((Finset.univ.filter fun c => 0 < z c).card = 4
        ∧ (Finset.univ.filter fun c => z c < 0).card = 3) := by
  have hposCard := rank_le_card_pos_side v hspan hstress hfull
  have hnegCard := rank_le_card_neg_side v hspan hstress hfull
  have hdisjoint : Disjoint (Finset.univ.filter fun c => 0 < z c)
      (Finset.univ.filter fun c => z c < 0) := by
    rw [Finset.disjoint_left]
    intro c hcPos hcNeg
    exact absurd (Finset.mem_filter.mp hcNeg).2 (asymm (Finset.mem_filter.mp hcPos).2)
  have hcover : (Finset.univ.filter fun c => 0 < z c)
      ∪ (Finset.univ.filter fun c => z c < 0) = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro c
    rcases lt_or_lt_iff_ne.mpr (hfull c) with hlt | hgt
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ c, hlt⟩)
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ c, hgt⟩)
  have hsum : (Finset.univ.filter fun c => 0 < z c).card
      + (Finset.univ.filter fun c => z c < 0).card = 7 := by
    rw [← Finset.card_union_of_disjoint hdisjoint, hcover, Finset.card_univ,
      Fintype.card_fin]
  omega

/-- Parseval forces the atoms of a weighted design to span, stated dually.
Rides the shipped `Gtz.selfDotProduct_pos` and the shared quadratic engine. -/
theorem weightedDesign_atoms_span {m k : ℕ} (D : Gtz.WeightedDesign m k)
    {x : Fin k → ℝ} (horth : ∀ c, D.atom c ⬝ᵥ x = 0) : x = 0 := by
  by_contra hxne
  have hposSelf : 0 < x ⬝ᵥ x := Gtz.selfDotProduct_pos hxne
  have hform : x ⬝ᵥ ((1 : Matrix (Fin k) (Fin k) ℝ) *ᵥ x)
      = ∑ c, D.weight c * (D.atom c ⬝ᵥ x) ^ 2 := by
    rw [← D.isParseval]
    exact weighted_atomForm_eq D.weight D.atom x
  rw [Matrix.one_mulVec] at hform
  have hvanish : x ⬝ᵥ x = 0 := by
    rw [hform]
    exact Finset.sum_eq_zero fun c _ => by rw [horth c]; ring
  exact absurd hvanish (ne_of_gt hposSelf)

/-- The split law at design level, rank-uniform: every full-support stress
of a weighted design has at least `rank` atoms on each sign side. -/
theorem design_rank_le_card_sides {m k : ℕ} (D : Gtz.WeightedDesign m k)
    {z : Fin m → ℝ} (hstress : ∑ c, z c • Gtz.atomMatrix (D.atom c) = 0)
    (hfull : ∀ c, z c ≠ 0) :
    k ≤ (Finset.univ.filter fun c => 0 < z c).card
      ∧ k ≤ (Finset.univ.filter fun c => z c < 0).card :=
  ⟨rank_le_card_pos_side D.atom (fun _ hx => weightedDesign_atoms_span D hx)
      hstress hfull,
    rank_le_card_neg_side D.atom (fun _ hx => weightedDesign_atoms_span D hx)
      hstress hfull⟩

/-- **The `(7,3)` design split, the lane's capstone.**  Every full-support
stress of a `(7,3)` weighted design -- and at size seven a stress always
exists -- splits `(3,4)` up to sign: the smaller side is a TRIPLE, the
canonical candidate the syzygy hands to the domination question.  The
hypothesis shape matches `Gtz.exists_rescaledReducedDesign_of_stress`
verbatim, so the two consumers share their stress supply. -/
theorem sevenThree_design_stress_split (D : Gtz.WeightedDesign 7 3)
    {z : Fin 7 → ℝ} (hstress : ∑ c, z c • Gtz.atomMatrix (D.atom c) = 0)
    (hfull : ∀ c, z c ≠ 0) :
    ((Finset.univ.filter fun c => 0 < z c).card = 3
        ∧ (Finset.univ.filter fun c => z c < 0).card = 4)
      ∨ ((Finset.univ.filter fun c => 0 < z c).card = 4
        ∧ (Finset.univ.filter fun c => z c < 0).card = 3) :=
  sevenThree_stress_split D.atom (fun _ hx => weightedDesign_atoms_span D hx)
    hstress hfull

end Gtz
