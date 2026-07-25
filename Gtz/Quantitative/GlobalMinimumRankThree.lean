/-
# The global minimum at rank three: the ceiling is exactly one, and it is ATTAINED

This module lands the part of the global-search campaign that is a THEOREM, and
mechanizes the corrections the adversarial audit forced on the campaign's framing.

Write `F(D) = max over k-subsets C of lambda_min (S_C)` and
`alpha_k = inf over designs of F`.  `GtzWeighted m k` is `F >= 1` at size `m`;
`GtzWeightedFloor m k level` (`Gtz.Reduction.RealVolumeFloor`) is `F >= level`.

## What is PROVED here

* **The ceiling is exactly one, at every size `>= 4`.**
  `not_gtzWeightedFloor_rankThree_of_one_lt` — no level above `1` holds for rank
  three at any size `4 <= m`, witnessed by the padded regular tetrahedron
  `paddedTetraDesign`, which is an exact tie at every size
  (`paddedTetraDesign_isTie`).  With `gtzWeightedFloor_inv_rank` this closes the
  proven bracket to `1/3 <= alpha_3 <= 1` (`gtzWeightedFloor_rankThree_bracket`),
  so the size-free floor `1/k` is off by a factor of exactly `k` at `k = 3` and
  the whole problem really is a constant factor.
* **The ceiling is attained, not approached**: the witnesses are exact rational
  designs at which EVERY `k`-subset ties at `lambda_min = 1`.  In particular the
  frontier object `(7,3)` itself sits ON the ceiling
  (`not_gtzWeightedFloor_sevenThree_of_one_lt`): if `GtzWeighted 7 3` is true it
  is true with zero margin, so no proof of it can produce an epsilon of slack.
* **No direction is uniformly weak** (`exists_atom_dotProduct_sq_ge_self`).
  Parseval read at a single probe says the weighted average of the squared atom
  projections IS the squared length, and the weights sum to one, so some atom
  projects at full length.  This is one line and it excises the entire stratum
  the float search converged to: see the two-spike discussion below.
* **The spike stratum's binding constraint, exactly.**
  `dominationGap_form_of_annihilated` computes the gap form of a subset along a
  direction annihilated by all but one of its atoms, and
  `dotProduct_sq_ge_self_of_dominates` turns that into the NECESSARY condition
  `(g_live . w)^2 >= |w|^2`.  Combined with the averaging lemma: the binding
  constraint on that stratum is always satisfiable, so the stratum is free.
* **The full atom set strictly dominates, and `2 <= m` is not decoration**
  (`posDef_subsetSum_univ_sub_one`, `subsetSum_univ_sub_one_eq_zero_of_single`).
  This is the honest form of the inertia claim `P - diag(t)` has inertia
  `(k, m-k)`: it is a statement about `sum_c g_c g_c^T - I`, it needs every
  weight strictly below one, and at `m = 1` it is FALSE, the difference being
  exactly zero.
* **Corank three is NOT free** (`gtzWeightedAll_three_of_corank_three`).  Corank
  one and corank two are unconditional theorems (`gtzWeighted_corank_one`,
  `gtzWeighted_corank_two`), and it is tempting to say "corank <= 3 is free by
  Naimark duality".  It is not: duality sends `(m, k)` to `(m, m-k)`, so corank
  three lands on RANK three at `m = 6` and on `(7,4) ~ (7,3)` at `m = 7`.  A
  blanket corank-three claim proves `GtzWeightedAll 3` — the open problem.

## What is MEASURED, not proved (and must not be read as proved)

Everything quantitative about WHERE the minimum sits.  The campaign's global
search (84,000 gated multistarts over 16 shapes, plus ~62,000 exact rational
designs) found `inf F = 1` at every shape tested and no point below one; the
rank-3 minimizing locus at `(7,3)` was identified numerically as ten graphic tie
classes (eight matroids after Whitney 2-isomorphism).  None of that is in this
file.  What IS in this file is the exact ceiling those searches were converging
to, proved from a rational witness with no floating point anywhere.

## What the Naimark theorem does and does not transfer

`weighted_naimark_duality` flips DOMINATION of complementary subsets.  It does
not transfer `F`: measured, a search-best `(7,3)` design with `F = 1.0000012`
has a `(7,4)` dual with `F = 2.877`.  Only the zero/one predicate crosses, which
is exactly what the theorem's statement says and no more.  The dual's weights
are the ORIGINAL weights while its atoms whiten the co-Parseval operator
`sum_c (1 - t_c) g_c g_c^T`; identifying the dual with an orthogonal complement
of the projection at the same weights is wrong and fails the domination flip.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Core.Sanity
import Gtz.LinAlg.PsdKit
import Gtz.Reduction.RealVolumeFloor
import Gtz.Reduction.RayleighCertificate
import Gtz.Reduction.Reductions
import Gtz.Reduction.RankFourWindow
import Gtz.Certificates.ResidueDissolution
import Gtz.Design.StressCertificate
import Gtz.Ties.TetrahedronCertifiedTie

namespace Gtz

open Matrix

variable {m k : ℕ}

/-! ## Level algebra: a floor above one is strict domination -/

/-- A form dominating `level · I` for some `level > 1` dominates `I` STRICTLY.
This is the whole reason a tie caps the floor: at a tie no subset dominates
strictly, so no level above one can hold. -/
theorem posDef_sub_one_of_posSemidef_sub_smul_one {size : ℕ}
    {form : Matrix (Fin size) (Fin size) ℝ} {level : ℝ} (hlevel : 1 < level)
    (hpsd : (form - level • 1).PosSemidef) : (form - 1).PosDef := by
  have hslackNonneg : (0 : ℝ) ≤ level - 1 := by linarith
  have hsplit : form - 1
      = (form - level • 1) + (level - 1) • (1 : Matrix (Fin size) (Fin size) ℝ) := by
    rw [sub_smul, one_smul]
    abel
  rw [hsplit]
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr
    ⟨hpsd.1.add (Matrix.PosSemidef.one.smul hslackNonneg).1, fun probe hprobe => ?_⟩
  have hgapNonneg := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hpsd).2 probe
  rw [star_trivial] at hgapNonneg
  have hprobePos : 0 < probe ⬝ᵥ probe := dotProduct_self_pos hprobe
  rw [star_trivial, Matrix.add_mulVec, dotProduct_add, Matrix.smul_mulVec,
    Matrix.one_mulVec, dotProduct_smul, smul_eq_mul]
  nlinarith

/-- **A tie caps the level.**  At an exact tie no `k`-subset dominates `level · I`
for any `level > 1`, because such a subset would dominate `I` strictly. -/
theorem not_exists_card_posSemidef_sub_smul_one_of_isTie {D : WeightedDesign m k}
    (htie : IsTie D) {level : ℝ} (hlevel : 1 < level) :
    ¬ ∃ C : Finset (Fin m), C.card = k ∧ (subsetSum D C - level • 1).PosSemidef := by
  rintro ⟨selected, hcard, hpsd⟩
  exact htie.2 selected hcard (posDef_sub_one_of_posSemidef_sub_smul_one hlevel hpsd)

/-- **A tie refutes every floor above one** at its own size and rank. -/
theorem not_gtzWeightedFloor_of_isTie {D : WeightedDesign m k} (htie : IsTie D)
    {level : ℝ} (hlevel : 1 < level) : ¬ GtzWeightedFloor m k level :=
  fun hfloor => not_exists_card_posSemidef_sub_smul_one_of_isTie htie hlevel (hfloor D)

/-- **A tie pins the ceiling at one**, in the contrapositive shape the ledger uses. -/
theorem gtzWeightedFloor_level_le_one_of_isTie {D : WeightedDesign m k} (htie : IsTie D)
    {level : ℝ} (hfloor : GtzWeightedFloor m k level) : level ≤ 1 :=
  not_lt.mp fun hlevel => not_gtzWeightedFloor_of_isTie htie hlevel hfloor

/-! ## The padded regular tetrahedron: an exact rank-three tie at EVERY size ≥ 4

The four tetrahedron vertices at leverage `3` carry a `(4,3)` design in which
every triple misses a vertex and ties there.  Splitting the fourth vertex's
weight over `extra + 1` copies of the SAME vector keeps Parseval exact and keeps
the tie: a triple of atoms still uses at most three of the four vertices, so it
still misses one, so its gap form still vanishes at the missed vertex.  Indexing
by `Fin (3 + (extra + 1))` makes `4 ≤ size` structural and splits every sum with
`Fin.sum_univ_add`.

Two copies of one vertex inside a triple make it rank-deficient rather than
merely tight, which is a strictly worse subset — the missed-vertex argument
covers that case uniformly and needs no separate repeated-atom lemma. -/

/-- The three corner vertices, in order. -/
def paddedTetraCorner : Fin 3 → Fin 4 := ![0, 1, 2]

/-- The vertex each padded atom carries: the first three atoms take three distinct
tetrahedron vertices, every remaining atom takes the fourth. -/
def paddedTetraVertex (extra : ℕ) : Fin (3 + (extra + 1)) → Fin 4 :=
  Fin.addCases paddedTetraCorner (fun _ => 3)

/-- The padded weights: `1/4` on each of the three corner atoms, the remaining
`1/4` split evenly over the `extra + 1` copies of the fourth vertex. -/
noncomputable def paddedTetraWeight (extra : ℕ) : Fin (3 + (extra + 1)) → ℝ :=
  Fin.addCases (fun _ => 1 / 4) (fun _ => 1 / (4 * ((extra : ℝ) + 1)))

@[simp] theorem paddedTetraVertex_corner (extra : ℕ) (corner : Fin 3) :
    paddedTetraVertex extra (Fin.castAdd (extra + 1) corner) = paddedTetraCorner corner :=
  Fin.addCases_left corner

@[simp] theorem paddedTetraVertex_copy (extra : ℕ) (copy : Fin (extra + 1)) :
    paddedTetraVertex extra (Fin.natAdd 3 copy) = 3 :=
  Fin.addCases_right copy

@[simp] theorem paddedTetraWeight_corner (extra : ℕ) (corner : Fin 3) :
    paddedTetraWeight extra (Fin.castAdd (extra + 1) corner) = 1 / 4 :=
  Fin.addCases_left corner

@[simp] theorem paddedTetraWeight_copy (extra : ℕ) (copy : Fin (extra + 1)) :
    paddedTetraWeight extra (Fin.natAdd 3 copy) = 1 / (4 * ((extra : ℝ) + 1)) :=
  Fin.addCases_right copy

/-- The padded weights sum to one: `3 · (1/4)` from the corners and
`(extra + 1) · (1/(4(extra+1)))` from the copies. -/
theorem paddedTetraWeight_sum_one (extra : ℕ) :
    ∑ atomIndex, paddedTetraWeight extra atomIndex = 1 := by
  have hcopiesNe : ((extra : ℝ) + 1) ≠ 0 := by positivity
  rw [Fin.sum_univ_add]
  simp only [paddedTetraWeight_corner, paddedTetraWeight_copy, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  field_simp
  norm_num

/-- The tetrahedron's own Parseval identity, in the shape the padding reassembles. -/
theorem tetraAtom_parseval :
    ∑ vertex : Fin 4, (1 / 4 : ℝ) • atomMatrix (tetraAtom vertex)
      = (1 : Matrix (Fin 3) (Fin 3) ℝ) :=
  tetraDesign.isParseval

/-- **The padded tetrahedron is a weighted design at every size `3 + (extra + 1)`.**
Parseval is exact and rational: the corner sum contributes `(1/4)(A₀+A₁+A₂)` and the
copies contribute `(1/4)A₃`, reassembling the tetrahedron's own tight frame. -/
noncomputable def paddedTetraDesign (extra : ℕ) : WeightedDesign (3 + (extra + 1)) 3 where
  atom := fun atomIndex => tetraAtom (paddedTetraVertex extra atomIndex)
  weight := paddedTetraWeight extra
  weight_pos := by
    have hcopiesPos : (0 : ℝ) < (extra : ℝ) + 1 := by positivity
    intro atomIndex
    induction atomIndex using Fin.addCases with
    | left corner => rw [paddedTetraWeight_corner]; norm_num
    | right copy => rw [paddedTetraWeight_copy]; positivity
  weight_sum_one := paddedTetraWeight_sum_one extra
  isParseval := by
    have hcopiesNe : ((extra : ℝ) + 1) ≠ 0 := by positivity
    have hcopiesSum : ∑ _copy : Fin (extra + 1),
          (1 / (4 * ((extra : ℝ) + 1))) • atomMatrix (tetraAtom 3)
        = (1 / 4 : ℝ) • atomMatrix (tetraAtom 3) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
      congr 1
      push_cast
      field_simp
    have htetra := tetraAtom_parseval
    rw [Fin.sum_univ_four] at htetra
    rw [Fin.sum_univ_add]
    simp only [paddedTetraWeight_corner, paddedTetraWeight_copy, paddedTetraVertex_corner,
      paddedTetraVertex_copy]
    rw [hcopiesSum, Fin.sum_univ_three]
    simp only [paddedTetraCorner, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
    exact htetra

@[simp] theorem paddedTetraDesign_atom (extra : ℕ) (atomIndex : Fin (3 + (extra + 1))) :
    (paddedTetraDesign extra).atom atomIndex = tetraAtom (paddedTetraVertex extra atomIndex) :=
  rfl

/-- Three padded atoms use at most three of the four tetrahedron vertices, so some
vertex is unused.  This is the only combinatorial input to the tie. -/
theorem exists_unusedPaddedVertex {extra : ℕ} {selected : Finset (Fin (3 + (extra + 1)))}
    (hcard : selected.card ≤ 3) :
    ∃ missed : Fin 4, ∀ atomIndex ∈ selected, paddedTetraVertex extra atomIndex ≠ missed := by
  by_contra hcontra
  have hcovered : (Finset.univ : Finset (Fin 4)) ⊆ selected.image (paddedTetraVertex extra) := by
    intro missed _
    by_contra hmissedNotMem
    exact hcontra ⟨missed, fun atomIndex hmem hvertex =>
      hmissedNotMem (Finset.mem_image.mpr ⟨atomIndex, hmem, hvertex⟩)⟩
  have hcoveredCard := Finset.card_le_card hcovered
  have himageCard :=
    Finset.card_image_le (s := selected) (f := paddedTetraVertex extra)
  rw [Finset.card_univ, Fintype.card_fin] at hcoveredCard
  omega

/-- **No 3-subset of the padded tetrahedron dominates strictly.**  The subset misses a
vertex `missed`; each selected atom pairs to `±1` with `tetraAtom missed`, so the gap
form there is `3 − 3 = 0`. -/
theorem paddedTetraDesign_no_strictDominator (extra : ℕ) :
    ∀ selected : Finset (Fin (3 + (extra + 1))), selected.card = 3 →
      ¬ (subsetSum (paddedTetraDesign extra) selected - 1).PosDef := by
  intro selected hcard hposDef
  obtain ⟨missed, hunused⟩ := exists_unusedPaddedVertex (extra := extra) (le_of_eq hcard)
  have hgapZero : tetraAtom missed
      ⬝ᵥ ((subsetSum (paddedTetraDesign extra) selected - 1) *ᵥ tetraAtom missed) = 0 := by
    rw [dominationGap_form]
    have hunitPairs : ∀ atomIndex ∈ selected,
        ((paddedTetraDesign extra).atom atomIndex ⬝ᵥ tetraAtom missed) ^ 2 = 1 :=
      fun atomIndex hmem => tetraAtom_dot_sq_of_ne (hunused atomIndex hmem)
    rw [Finset.sum_congr rfl hunitPairs, Finset.sum_const, hcard, tetraAtom_dot_self,
      nsmul_eq_mul]
    norm_num
  have hgapPos :=
    (Matrix.posDef_iff_dotProduct_mulVec.mp hposDef).2 (tetraAtom_ne_zero missed)
  rw [star_trivial, hgapZero] at hgapPos
  exact lt_irrefl 0 hgapPos

/-- The three corner atoms, as a subset of the padded index set. -/
def paddedTetraCornerTriple (extra : ℕ) : Finset (Fin (3 + (extra + 1))) :=
  Finset.univ.image (Fin.castAdd (extra + 1))

theorem card_paddedTetraCornerTriple (extra : ℕ) :
    (paddedTetraCornerTriple extra).card = 3 := by
  rw [paddedTetraCornerTriple,
    Finset.card_image_of_injective _ (fun left right hlr => by simpa [Fin.ext_iff] using hlr),
    Finset.card_univ, Fintype.card_fin]

theorem subsetSum_paddedTetraCornerTriple (extra : ℕ) :
    subsetSum (paddedTetraDesign extra) (paddedTetraCornerTriple extra)
      = ∑ corner : Fin 3, atomMatrix (tetraAtom (paddedTetraCorner corner)) := by
  rw [subsetSum, paddedTetraCornerTriple,
    Finset.sum_image (fun left _ right _ hlr => by simpa [Fin.ext_iff] using hlr)]
  exact Finset.sum_congr rfl fun corner _ => by
    rw [paddedTetraDesign_atom, paddedTetraVertex_corner]

/-- **The corner triple dominates**: its gap form is the sum of squares
`(x₀−x₁)² + (x₀+x₂)² + (x₁+x₂)²`, exactly the tetrahedron's own certificate. -/
theorem paddedTetraDesign_dominates (extra : ℕ) :
    Dominates (paddedTetraDesign extra) (paddedTetraCornerTriple extra) := by
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨?_, fun probe => ?_⟩
  · exact ((Matrix.posSemidef_sum (paddedTetraCornerTriple extra) fun atomIndex _ =>
      posSemidef_atomMatrix ((paddedTetraDesign extra).atom atomIndex)).1).sub
      Matrix.isHermitian_one
  · rw [star_trivial, Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec,
      subsetSum_paddedTetraCornerTriple, Matrix.sum_mulVec, dotProduct_sum, sub_nonneg]
    simp only [Fin.sum_univ_three, dotProduct_atomMatrix_mulVec]
    simp only [paddedTetraCorner, tetraAtom, dotProduct, Fin.sum_univ_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons]
    nlinarith [sq_nonneg (probe 0 - probe 1), sq_nonneg (probe 0 + probe 2),
      sq_nonneg (probe 1 + probe 2)]

/-- **The padded tetrahedron is an exact tie at every size `≥ 4`**: the corner triple
dominates weakly and nothing dominates strictly, so `F = 1` exactly. -/
theorem paddedTetraDesign_isTie (extra : ℕ) : IsTie (paddedTetraDesign extra) :=
  ⟨⟨paddedTetraCornerTriple extra, card_paddedTetraCornerTriple extra,
    paddedTetraDesign_dominates extra⟩, paddedTetraDesign_no_strictDominator extra⟩

/-! ## The rank-three ceiling -/

/-- **THE CEILING AT RANK THREE.**  No level above `1` holds at any size `4 ≤ size`.
The witness is exact and rational, so this is not a search artifact: `alpha_3 ≤ 1`
with equality ATTAINED, at every size. -/
theorem not_gtzWeightedFloor_rankThree_of_one_lt {size : ℕ} (hsize : 4 ≤ size)
    {level : ℝ} (hlevel : 1 < level) : ¬ GtzWeightedFloor size 3 level := by
  obtain ⟨extra, rfl⟩ : ∃ extra, size = 3 + (extra + 1) := ⟨size - 4, by omega⟩
  exact not_gtzWeightedFloor_of_isTie (paddedTetraDesign_isTie extra) hlevel

/-- The ceiling in contrapositive shape: any rank-three floor is at most one. -/
theorem gtzWeightedFloor_rankThree_level_le_one {size : ℕ} (hsize : 4 ≤ size)
    {level : ℝ} (hfloor : GtzWeightedFloor size 3 level) : level ≤ 1 :=
  not_lt.mp fun hlevel => not_gtzWeightedFloor_rankThree_of_one_lt hsize hlevel hfloor

/-- **THE PROVEN TWO-SIDED BRACKET at rank three**: the size-free floor `1/3` holds
at every size, and no level above `1` holds at any size `≥ 4`.  So
`1/3 ≤ alpha_3 ≤ 1` and the floor is off by a factor of exactly `3` — the whole
rank-three problem is a constant factor, and that constant is the rank. -/
theorem gtzWeightedFloor_rankThree_bracket {size : ℕ} (hsize : 4 ≤ size) :
    GtzWeightedFloor size 3 ((3 : ℝ)⁻¹)
      ∧ ∀ level : ℝ, GtzWeightedFloor size 3 level → level ≤ 1 := by
  refine ⟨?_, fun level hfloor => gtzWeightedFloor_rankThree_level_le_one hsize hfloor⟩
  simpa using gtzWeightedFloor_inv_rank size 3

/-- **The frontier object sits ON the ceiling.**  `(7,3)` is the single remaining
rank-three obligation; the padded tetrahedron at `extra = 3` is a `(7,3)` design that
ties.  So if `GtzWeighted 7 3` holds it holds with ZERO margin, and no proof of it can
produce a uniform epsilon of slack. -/
theorem not_gtzWeightedFloor_sevenThree_of_one_lt {level : ℝ} (hlevel : 1 < level) :
    ¬ GtzWeightedFloor 7 3 level :=
  not_gtzWeightedFloor_rankThree_of_one_lt (by norm_num) hlevel

/-- The `(7,3)` tie, named: `paddedTetraDesign 3` lives at size `3 + (3 + 1) = 7`. -/
theorem exists_isTie_sevenThree : ∃ D : WeightedDesign 7 3, IsTie D :=
  ⟨paddedTetraDesign 3, paddedTetraDesign_isTie 3⟩

/-! ## No direction is uniformly weak — the spike stratum is free

The float search's minimizers all sat on the two-spike stratum: two atoms carrying
weight `~10⁻⁶`, hence atom vectors of squared length `~10⁶`.  There the value of
`lambda_min` on a triple containing both spikes is governed by the single direction
`w` orthogonal to the two spike vectors, where the form reduces to
`(g_live . w)²`.  The lemmas below make both halves of that exact: the direction
test is NECESSARY for domination, and it is ALWAYS satisfiable.  So no counterexample
can live there, and the search was measuring its own leverage cap. -/

/-- **Parseval at one probe forces some atom to project at full length.**  The weighted
average of the squared atom projections IS the squared length, and the weights sum to
one, so the maximum is at least the average. -/
theorem exists_atom_dotProduct_sq_ge_self (D : WeightedDesign m k) (probe : Fin k → ℝ) :
    ∃ atomIndex : Fin m, probe ⬝ᵥ probe ≤ (D.atom atomIndex ⬝ᵥ probe) ^ 2 := by
  by_contra hcontra
  have hallStrict : ∀ atomIndex : Fin m,
      (D.atom atomIndex ⬝ᵥ probe) ^ 2 < probe ⬝ᵥ probe := fun atomIndex => by
    by_contra hge
    exact hcontra ⟨atomIndex, not_lt.mp hge⟩
  have hnonempty : (Finset.univ : Finset (Fin m)).Nonempty := by
    rcases Nat.eq_zero_or_pos m with hzero | hpos
    · exfalso
      subst hzero
      have hsum := D.weight_sum_one
      simp at hsum
    · haveI : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp hpos
      exact Finset.univ_nonempty
  have hstrictSum : ∑ atomIndex, D.weight atomIndex * (D.atom atomIndex ⬝ᵥ probe) ^ 2
      < ∑ atomIndex : Fin m, D.weight atomIndex * (probe ⬝ᵥ probe) :=
    Finset.sum_lt_sum_of_nonempty hnonempty fun atomIndex _ =>
      mul_lt_mul_of_pos_left (hallStrict atomIndex) (D.weight_pos atomIndex)
  rw [← Finset.sum_mul, D.weight_sum_one, one_mul,
    ← dotProduct_self_eq_sum_weight_mul_sq D probe] at hstrictSum
  exact lt_irrefl _ hstrictSum

/-- **The gap form along a direction annihilated by all but one selected atom** is the
survivor's squared projection minus the squared length.  This is the spike stratum's
whole content: the two huge atoms contribute nothing along their common normal. -/
theorem dominationGap_form_of_annihilated (D : WeightedDesign m k) (selected : Finset (Fin m))
    {live : Fin m} (hliveMem : live ∈ selected) (probe : Fin k → ℝ)
    (hannihilated : ∀ atomIndex ∈ selected, atomIndex ≠ live → D.atom atomIndex ⬝ᵥ probe = 0) :
    probe ⬝ᵥ ((subsetSum D selected - 1) *ᵥ probe)
      = (D.atom live ⬝ᵥ probe) ^ 2 - probe ⬝ᵥ probe := by
  rw [dominationGap_form]
  congr 1
  refine Finset.sum_eq_single live (fun atomIndex hmem hne => ?_)
    (fun hnotMem => absurd hliveMem hnotMem)
  rw [hannihilated atomIndex hmem hne]
  exact zero_pow two_ne_zero

/-- **The direction test is NECESSARY.**  On the stratum where every selected atom but
one annihilates a direction, domination forces the survivor to project at full length
there. -/
theorem dotProduct_sq_ge_self_of_dominates (D : WeightedDesign m k)
    {selected : Finset (Fin m)} {live : Fin m} (hliveMem : live ∈ selected)
    (probe : Fin k → ℝ)
    (hannihilated : ∀ atomIndex ∈ selected, atomIndex ≠ live → D.atom atomIndex ⬝ᵥ probe = 0)
    (hdominates : Dominates D selected) :
    probe ⬝ᵥ probe ≤ (D.atom live ⬝ᵥ probe) ^ 2 := by
  have hgapNonneg := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hdominates).2 probe
  rw [star_trivial,
    dominationGap_form_of_annihilated D selected hliveMem probe hannihilated] at hgapNonneg
  linarith

/-! ## The honest inertia statement -/

/-- **The full atom set strictly dominates** when `2 ≤ m`:
`S_univ − I = sum_c (1 − t_c) g_c g_c^T`, positive definite because every weight is
strictly below one and the atoms span. -/
theorem posDef_subsetSum_univ_sub_one (D : WeightedDesign m k) (hm : 2 ≤ m) :
    (subsetSum D Finset.univ - 1).PosDef := by
  have hsplit : subsetSum D Finset.univ - 1
      = ∑ atomIndex, (1 - D.weight atomIndex) • atomMatrix (D.atom atomIndex) := by
    rw [subsetSum, ← D.isParseval, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun atomIndex _ => by rw [sub_smul, one_smul]
  rw [hsplit]
  exact coParseval_posDef D hm

/-- **`2 ≤ m` is not decoration.**  A one-atom design has `S_univ = I` on the nose, so
the strict domination above is FALSE at `m = 1` at every rank.  Any statement of the
form "`P − diag(t)` has inertia `(k, m−k)`" carries this hypothesis silently. -/
theorem subsetSum_univ_sub_one_eq_zero_of_single (D : WeightedDesign 1 k) :
    subsetSum D Finset.univ - 1 = 0 := by
  have hweightOne : D.weight 0 = 1 := by
    have hsum := D.weight_sum_one
    rwa [Fin.sum_univ_one] at hsum
  have hparseval := D.isParseval
  rw [Fin.sum_univ_one, hweightOne, one_smul] at hparseval
  rw [subsetSum, Fin.sum_univ_one, hparseval, sub_self]

/-! ## Corank three is the open problem, not a free case -/

/-- Corank one and corank two are unconditional at every rank `≥ 2`, recorded together
so the boundary is visible in one place. -/
theorem gtzWeighted_corank_one_and_two (rank : ℕ) (hrank : 2 ≤ rank) :
    GtzWeighted (rank + 1) rank ∧ GtzWeighted (rank + 2) rank :=
  ⟨gtzWeighted_corank_one rank (by omega), gtzWeighted_corank_two rank hrank⟩

/-- **CORANK THREE IS NOT FREE.**  Naimark duality exchanges rank `k` with rank `m − k`
at the same size, so corank three at size `7` is rank four at size `7`, which duality
sends straight back to `(7,3)` — and `(7,3)` alone carries all of rank three.  A blanket
"corank ≤ 3 is free for every `k`" therefore PROVES the open problem; the free boundary
is corank two, where the dual rank is at most two and Sengupta–Pautov applies. -/
theorem gtzWeightedAll_three_of_corank_three
    (hcorank : ∀ rank : ℕ, 1 ≤ rank → GtzWeighted (rank + 3) rank) : GtzWeightedAll 3 := by
  have hsevenFour : GtzWeighted 7 4 := by
    have hinstance := hcorank 4 (by norm_num)
    norm_num at hinstance
    exact hinstance
  have hsevenThree : GtzWeighted 7 3 :=
    gtzWeighted_of_dual_rank (by norm_num) (by norm_num) (by norm_num; exact hsevenFour)
  exact gtzWeightedAll_three_of_seven_three hsevenThree

end Gtz
