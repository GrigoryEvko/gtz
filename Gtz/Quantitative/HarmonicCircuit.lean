/-
# The circuit layer: harmonic atoms, the domination cone, and vertex capture

Every statement here is at general `(size, rank)` unless its name says otherwise; the
`(6,3)` and rank-two statements are corollaries, never the content.

## The harmonic (traceless) atom part

`tracelessAtomMatrix k g = g gᵀ − (|g|²/k) I` is the traceless part of a Veronese
image, living in the shipped `Gtz.symmetricTracelessSubmodule` of
`Gtz/Quantitative/RankTwoRealnessCount.lean`.  Every weighted design satisfies
`∑_c t_c H_c = 0` (`sum_weight_smul_tracelessAtomMatrix_eq_zero`), because the
weighted leverages sum to the rank.  So the `H_c` are `size` points of a
`(k(k+1)/2 − 1)`-dimensional space carrying a distinguished POSITIVE relation — the
weights.  That is what makes them a circuit rather than a free family.

`sum_smul_tracelessAtomMatrix_eq_zero_iff` is the RELATION-SPACE SPLIT: a coefficient
vector annihilates the harmonic parts exactly when it becomes a stress after
subtracting the right multiple of the weights, the multiple being forced by its own
leverage pairing.  Together with `sum_weight_smul_atomMatrix_ne_zero` (the weights are
NOT a stress, since they reproduce the identity) this is "harmonic relations =
stresses ⊕ ℝ·t" in equation form, with no submodule algebra.

## The unique positive circuit on the stress-free stratum

Linear independence of the Veronese images IS stress-freeness, so on that stratum the
split collapses:
`sum_smul_tracelessAtomMatrix_eq_zero_iff_of_linearIndependent` says the harmonic
relation space is EXACTLY the line `ℝ·t`, and
`exists_pos_harmonicCircuit_of_linearIndependent` packages that as "there is a
strictly positive circuit, and every relation is a multiple of it".  When the Veronese
images additionally SPAN the symmetric forms — the Veronese-top situation of
`Gtz.span_atomMatrix_eq_symmetricSubmodule_of_linearIndependent` — the harmonic parts
span the traceless space
(`span_tracelessAtomMatrix_eq_symmetricTracelessSubmodule_of_span`), so they are a
spanning family with a one-dimensional, strictly positive relation space: a circuit in
the matroid sense, positively oriented.

`Gtz.SixThreeCrux.exists_pos_harmonicCircuit` and its two companions instantiate all
three at a `(6,3)` crux, consuming the shipped
`Gtz.SixThreeCrux.linearIndependent_veronese` and
`Gtz.SixThreeCrux.span_veronese_eq_symmetricSubmodule`.  A crux is therefore exactly a
positively-oriented spanning circuit of six harmonic points in the five-dimensional
traceless space, no `k`-subset of which dominates.

## The domination cone

`dominationCone D = { α : ∑_d α_d g_d g_dᵀ ⪰ 0 }` is a convex cone in `ℝ^size`.  Three
facts pin it: it contains the nonnegative orthant, it contains the weights (whose
image is the identity), and — `mem_dominationCone_neg_iff_stress` — its LINEALITY
SPACE IS EXACTLY THE STRESS SPACE.  So the stress-free stratum, where the walk of
`Gtz.exists_dominating_sixThree_of_stress` has nothing to consume, is precisely the
stratum on which this cone is pointed.

`salient_dominationCone_iff` says the same thing in Mathlib's own convex-cone
vocabulary: `ConvexCone.Salient` of this cone IS stress-freeness of the design, so the
campaign's stress-free stratum and the convex-geometric notion of a pointed cone are
literally the same predicate.

`exists_pos_smul_add_weight_mem_dominationCone` says the weights are an algebraic
interior point: every direction can be walked a positive distance from `t` without
leaving the cone.  The proof is an entrywise bound, no operator norm, so it needs no
spanning hypothesis — the weights are interior at EVERY weighted design.

## Vertex capture

`subsetSum_sub_one_eq_sum_vertexDirection_smul_atomMatrix` is the identity
`S_C − I = ∑_d ((1_C)_d − t_d) g_d g_dᵀ`, hence
`dominates_iff_vertexDirection_mem_dominationCone`: a subset dominates exactly when
the hypersimplex vertex direction `1_C − t` lies in the cone.  `GtzWeighted m k` is
therefore "at every design the domination cone captures a vertex direction of the
hypersimplex `Δ(m,k)` based at the weights".

The linear-algebraic content of that reading is nil and the docstrings say so; its
value is that the cone is WEIGHT-FREE (it depends only on the atoms) while the base
point `t` carries all the weight dependence, and that at a stress-free Veronese top
`t` is determined by the atoms.

## Rank two: the light cone, and the polygon template

At rank two the traceless symmetric matrices are two-dimensional and
`det` is minus the squared Euclidean length there, so `PSD` is a LIGHT CONE.
`det_tracelessAtomMatrix_rankTwo` computes the radius of a harmonic atom exactly:
`det H_g = −(ℓ_g/2)²`, i.e. `|h_g| = ℓ_g/2` — the double-angle fact whose vector form
is the shipped `Gtz.blochSquare_normSq`, and
`tracelessAtomMatrix_apply_diag_rankTwo` / `_offDiag_rankTwo` are the coordinate bridge
between the two forms.  `dominates_iff_harmonicRadius_rankTwo` then reads domination
as one sqrt-free light-cone inequality:

  `Dominates D C  ↔  0 ≤ (∑_{c∈C} ℓ_c)/2 − 1  ∧  0 ≤ ((∑_{c∈C} ℓ_c)/2 − 1)² + det(∑_{c∈C} H_c)`.

Writing `r_C` for the harmonic radius `√(−det ∑_{c∈C} H_c)` and using `|h_c| = ℓ_c/2`,
the two-element case is `|h_i| + |h_j| − |h_i + h_j| ≥ 1`: the classical planar
isoperimetric-polygon statement of rank-two GTZ, whose closed polygon is the circuit
`∑_c t_c H_c = 0`.  So the circuit layer reproduces the rank-two template exactly, and
that is the non-vacuity check for the whole harmonic reading.  Nothing here proves
rank-two GTZ — that is the shipped `Gtz.gtz_rank_two` — but it exhibits the polygon
the classical proof runs on inside the general-rank vocabulary.

## The metric capture criterion, and the measured verdict on it

`probeQuarticMoment D x = ∑_d ⟨g_d, x⟩⁴` is the UNWEIGHTED fourth moment in a probe
direction — a different object from the shipped `Gtz.shareWeightedFourthMoment`, which
is the probe-free Gram scalar `∑_{c,d} s_c s_d γ_cd⁴`.  Its uniform bound controls the
Euclidean inradius of the domination cone at `t`, and
`posSemidef_sum_smul_atomMatrix_of_probeQuarticBound` turns that into a sufficient
condition: splitting a direction as `scale·t + residual`, the moment is semidefinite
once `|residual|₂ √bound ≤ scale`.  `hasProbeQuarticBound_sum_sq_leverage` supplies
`∑_d ℓ_d²` as a free explicit bound.  These are theorems, at general `(size, rank)`,
and nothing rank-generic of this kind is shipped.

MEASURED SCOPE — read before building on this; it is a brick, not a route.  With the
SHARPEST bound `Q₄max = max_{|x|=1} ∑_d ⟨g_d,x⟩⁴` and the optimal `scale`, the
criterion is the angle test `sin ∠(1_C − t, t) ≤ 1/(√Q₄max · |t|)`, in scalars
`Q₄max · (|δ_C|² |t|² − ⟨δ_C,t⟩²) ≤ |δ_C|²`.  Exact evaluation gives:
  * `(4,3)` regular tetrahedron: `Q₄max = 28/3` (the Lagrange critical values on the
    sphere are exactly `{4, 8, 28/3}`), and the scalar criterion holds with slack
    EXACTLY 0 — the round cone touches the vertex direction, at the design where all
    four triples tie;
  * `(6,3)` icosahedron: `Q₄(x) − (54/5)|x|⁴` vanishes identically, so `Q₄max = 54/5`
    exactly, and the criterion FAILS.  The deficit is `8/15` in the SCALAR
    normalisation above and `32/15 = 54/5 − 26/3` in the `Q₄max` normalisation of the
    next bullet; quoting one against the other is the obvious way to misread it;
  * at uniform weights the criterion is `Q₄max ≤ m(km−2k+1)/(k(m−k))` — the right side
    is `26/3` at `(6,3)` — so for uniform projective 2-designs it holds iff
    `m ≤ (k+1)(3k−2)/(2k)` over ℝ and iff `m ≤ (2k²−1)/k` over ℂ.  At `k = 2` the real
    threshold is `3`, exactly the Veronese top; from `k = 3` on it falls strictly below
    it (`14/3 < 6`, `25/4 < 10`, `39/5 < 15`) and the shortfall widens.
The complex threshold EXCEEDS the real one at every rank, so the criterion is
field-anti-monotone: it proves more over ℂ, where GTZ is false, than over ℝ.  By
boundary condition B1 the metric leg therefore cannot be the mechanism.  Two further
measurements say the same thing from outside: the inradius `1/√Q₄max` is exactly
`1/‖A‖` for the linear map `A(α) = ∑_d α_d G_d` that carries this cone to the PSD cone
and `t` to the identity, so an aperture hypothesis constrains the coordinate system
rather than the design; and the Haar volume of `{V : W|_V ⪰ 0}` in the Grassmannian is
`0.198` at the complex counterexample with zero dominating triples against
`0.197`–`0.208` at the real ties with twelve or thirteen, so the SIZE of the capturing
set carries no information about capture.  Any capture lemma that closes anything must
read the DIRECTION `1_C − t`, not its length.

`tracelessAtomMatrix_mem_symmetricTracelessSubmodule` is a RESTATEMENT of the shipped
`Gtz.atomMatrix_sub_smul_one_mem_symmetricTracelessSubmodule` at the new name — it is
the API entry point for the definition and carries no new content.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Core.Sanity
import Gtz.LinAlg.ProjectionForm
import Gtz.LinAlg.TwoByTwo
import Gtz.Planar.BlochDictionary
import Gtz.Reduction.RealVolumeFloor
import Gtz.Quantitative.RankTwoRealnessCount
import Gtz.Quantitative.SixThreeStressExclusion
import Gtz.Quantitative.ComplexVeroneseDichotomy

namespace Gtz

open Matrix

variable {m k : ℕ}

/-! ## The harmonic atom part -/

/-- **The harmonic (traceless) part of an atom**, `H_g = g gᵀ − (|g|²/k) I`. -/
noncomputable def tracelessAtomMatrix (rank : ℕ) (atom : Fin rank → ℝ) :
    Matrix (Fin rank) (Fin rank) ℝ :=
  atomMatrix atom - (leverageOf atom / rank) • (1 : Matrix (Fin rank) (Fin rank) ℝ)

theorem tracelessAtomMatrix_transpose (rank : ℕ) (atom : Fin rank → ℝ) :
    (tracelessAtomMatrix rank atom)ᵀ = tracelessAtomMatrix rank atom := by
  rw [tracelessAtomMatrix, Matrix.transpose_sub, Matrix.transpose_smul,
    Matrix.transpose_one, atomMatrix, Matrix.transpose_vecMulVec]

/-- The harmonic part is traceless, which is its whole point. -/
theorem trace_tracelessAtomMatrix (rank : ℕ) (hrank : 1 ≤ rank) (atom : Fin rank → ℝ) :
    Matrix.trace (tracelessAtomMatrix rank atom) = 0 := by
  have hrankne : (rank : ℝ) ≠ 0 := by
    have hpos : 0 < rank := hrank
    positivity
  rw [tracelessAtomMatrix, Matrix.trace_sub, trace_atomMatrix, Matrix.trace_smul,
    Matrix.trace_one, Fintype.card_fin, smul_eq_mul, div_mul_cancel₀ _ hrankne, sub_self]

/-- The harmonic part lands in the traceless symmetric space of
`Gtz/Quantitative/RankTwoRealnessCount.lean`, which is where the circuit lives.  This
is a RESTATEMENT of the shipped
`Gtz.atomMatrix_sub_smul_one_mem_symmetricTracelessSubmodule` at the definition's own
name: no new content, only the API entry point. -/
theorem tracelessAtomMatrix_mem_symmetricTracelessSubmodule (rank : ℕ) (hrank : 1 ≤ rank)
    (atom : Fin rank → ℝ) :
    tracelessAtomMatrix rank atom ∈ symmetricTracelessSubmodule rank :=
  atomMatrix_sub_smul_one_mem_symmetricTracelessSubmodule rank hrank atom

/-- **The harmonic aggregate of a reweighting**: the harmonic parts differ from the
atoms by the leverage pairing times the identity. -/
theorem sum_smul_tracelessAtomMatrix (D : WeightedDesign m k) (coefficient : Fin m → ℝ) :
    ∑ c, coefficient c • tracelessAtomMatrix k (D.atom c)
      = (∑ c, coefficient c • atomMatrix (D.atom c))
        - ((∑ c, coefficient c * leverageOf (D.atom c)) / k)
          • (1 : Matrix (Fin k) (Fin k) ℝ) := by
  rw [Finset.sum_div, Finset.sum_smul, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [tracelessAtomMatrix, smul_sub, smul_smul, mul_div_assoc]

/-- **THE CIRCUIT.**  At every weighted design the weights annihilate the harmonic
parts: `∑_c t_c H_c = 0`.  This is the trace identity `∑_c t_c |g_c|² = k` read in
the traceless space, and it is the positive relation that makes the harmonic atoms a
circuit rather than a free family. -/
theorem sum_weight_smul_tracelessAtomMatrix_eq_zero (hk : 1 ≤ k) (D : WeightedDesign m k) :
    ∑ c, D.weight c • tracelessAtomMatrix k (D.atom c) = 0 := by
  have hrankne : (k : ℝ) ≠ 0 := by
    have hpos : 0 < k := hk
    positivity
  rw [sum_smul_tracelessAtomMatrix, D.isParseval, sum_weight_mul_leverage,
    div_self hrankne, one_smul, sub_self]

/-- A stress annihilates the harmonic parts too: its leverage pairing is the trace of
zero. -/
theorem sum_smul_tracelessAtomMatrix_eq_zero_of_stress (D : WeightedDesign m k)
    {stress : Fin m → ℝ} (hstress : ∑ c, stress c • atomMatrix (D.atom c) = 0) :
    ∑ c, stress c • tracelessAtomMatrix k (D.atom c) = 0 := by
  have hleverage : ∑ c, stress c * leverageOf (D.atom c) = 0 := by
    have htrace : Matrix.trace (∑ c, stress c • atomMatrix (D.atom c)) = 0 := by
      rw [hstress, Matrix.trace_zero]
    rw [Matrix.trace_sum] at htrace
    rw [← htrace]
    exact Finset.sum_congr rfl fun c _ => by
      rw [Matrix.trace_smul, trace_atomMatrix, smul_eq_mul]
  rw [sum_smul_tracelessAtomMatrix, hstress, hleverage, zero_div, zero_smul, sub_zero]

/-- **THE RELATION-SPACE SPLIT**, at general `(size, rank)`.  A coefficient vector
kills the harmonic parts exactly when subtracting its own leverage pairing worth of
weights turns it into a stress.  Read left to right it says harmonic relations are
stresses plus multiples of the weights; read right to left, with the stress zero, it
recovers `sum_weight_smul_tracelessAtomMatrix_eq_zero`. -/
theorem sum_smul_tracelessAtomMatrix_eq_zero_iff (D : WeightedDesign m k)
    (coefficient : Fin m → ℝ) :
    (∑ c, coefficient c • tracelessAtomMatrix k (D.atom c) = 0)
      ↔ (∑ c, (coefficient c
            - ((∑ d, coefficient d * leverageOf (D.atom d)) / k) * D.weight c)
          • atomMatrix (D.atom c) = 0) := by
  have hsplit :
      ∑ c, (coefficient c
            - ((∑ d, coefficient d * leverageOf (D.atom d)) / k) * D.weight c)
          • atomMatrix (D.atom c)
        = (∑ c, coefficient c • atomMatrix (D.atom c))
          - ((∑ d, coefficient d * leverageOf (D.atom d)) / k)
            • (1 : Matrix (Fin k) (Fin k) ℝ) := by
    rw [← D.isParseval, Finset.smul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun c _ => by rw [sub_smul, smul_smul]
  rw [hsplit, sum_smul_tracelessAtomMatrix]

/-- The weights are NOT a stress: their moment is the identity.  With the split
above, this is what makes the harmonic relation space one dimension bigger than the
stress space rather than equal to it. -/
theorem sum_weight_smul_atomMatrix_ne_zero (hk : 1 ≤ k) (D : WeightedDesign m k) :
    ∑ c, D.weight c • atomMatrix (D.atom c) ≠ 0 := by
  rw [D.isParseval]
  intro hzero
  have hentry : (1 : Matrix (Fin k) (Fin k) ℝ) ⟨0, hk⟩ ⟨0, hk⟩ = 0 := by rw [hzero]; rfl
  rw [Matrix.one_apply_eq] at hentry
  exact one_ne_zero hentry

/-! ## The unique positive circuit on the stress-free stratum -/

/-- **THE HARMONIC RELATION SPACE IS THE LINE `ℝ·t`** whenever the Veronese images are
independent — which is exactly stress-freeness.  General `(size, rank)`: the split
above turns a harmonic relation into a stress, independence kills it, and the residue
is the forced multiple of the weights. -/
theorem sum_smul_tracelessAtomMatrix_eq_zero_iff_of_linearIndependent
    (D : WeightedDesign m k) (hk : 1 ≤ k)
    (hindependent : LinearIndependent ℝ fun c : Fin m => atomMatrix (D.atom c))
    (coefficient : Fin m → ℝ) :
    (∑ c, coefficient c • tracelessAtomMatrix k (D.atom c) = 0)
      ↔ ∃ scale : ℝ, ∀ c, coefficient c = scale * D.weight c := by
  constructor
  · intro hzero
    rw [sum_smul_tracelessAtomMatrix_eq_zero_iff] at hzero
    refine ⟨(∑ d, coefficient d * leverageOf (D.atom d)) / k, fun c => ?_⟩
    have hvanishes := (Fintype.linearIndependent_iff.mp hindependent) _ hzero c
    linarith
  · rintro ⟨scale, hscale⟩
    have hrewrite : ∑ c, coefficient c • tracelessAtomMatrix k (D.atom c)
        = scale • ∑ c, D.weight c • tracelessAtomMatrix k (D.atom c) := by
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun c _ => by rw [hscale c, smul_smul]
    rw [hrewrite, sum_weight_smul_tracelessAtomMatrix_eq_zero hk, smul_zero]

/-- **THE POSITIVE CIRCUIT.**  On the stress-free stratum the harmonic atoms carry a
STRICTLY POSITIVE relation — the weights — and every relation among them is a multiple
of it.  This is the circuit of the harmonic reading, positively oriented, at general
`(size, rank)`. -/
theorem exists_pos_harmonicCircuit_of_linearIndependent (D : WeightedDesign m k) (hk : 1 ≤ k)
    (hindependent : LinearIndependent ℝ fun c : Fin m => atomMatrix (D.atom c)) :
    ∃ circuit : Fin m → ℝ, (∀ c, 0 < circuit c)
      ∧ (∑ c, circuit c • tracelessAtomMatrix k (D.atom c) = 0)
      ∧ ∀ other : Fin m → ℝ, (∑ c, other c • tracelessAtomMatrix k (D.atom c) = 0)
          → ∃ scale : ℝ, ∀ c, other c = scale * circuit c :=
  ⟨D.weight, D.weight_pos, sum_weight_smul_tracelessAtomMatrix_eq_zero hk D,
    fun other hother =>
      (sum_smul_tracelessAtomMatrix_eq_zero_iff_of_linearIndependent D hk hindependent
        other).mp hother⟩

/-- **THE HARMONIC ATOMS SPAN THE TRACELESS SPACE** whenever the Veronese images span
the symmetric forms.  Removing the trace is surjective onto the traceless part
because the harmonic combination of a representation of a TRACELESS matrix has
vanishing leverage pairing — the correction term dies on its own. -/
theorem span_tracelessAtomMatrix_eq_symmetricTracelessSubmodule_of_span
    (D : WeightedDesign m k) (hk : 1 ≤ k)
    (hspan : Submodule.span ℝ (Set.range fun c : Fin m => atomMatrix (D.atom c))
      = symmetricSubmodule k) :
    Submodule.span ℝ (Set.range fun c : Fin m => tracelessAtomMatrix k (D.atom c))
      = symmetricTracelessSubmodule k := by
  refine le_antisymm ?_ ?_
  · rw [Submodule.span_le]
    rintro _ ⟨c, rfl⟩
    exact tracelessAtomMatrix_mem_symmetricTracelessSubmodule k hk (D.atom c)
  · intro matrix hmatrix
    rw [mem_symmetricTracelessSubmodule_iff] at hmatrix
    obtain ⟨hsymmetric, htraceless⟩ := hmatrix
    have hmemSymmetric : matrix
        ∈ Submodule.span ℝ (Set.range fun c : Fin m => atomMatrix (D.atom c)) := by
      rw [hspan, mem_symmetricSubmodule_iff]
      exact hsymmetric
    rw [Submodule.mem_span_range_iff_exists_fun] at hmemSymmetric
    obtain ⟨coefficient, hcoefficient⟩ := hmemSymmetric
    have hleveragePairing : ∑ c, coefficient c * leverageOf (D.atom c) = 0 := by
      rw [← htraceless, ← hcoefficient, Matrix.trace_sum]
      exact Finset.sum_congr rfl fun c _ => by
        rw [Matrix.trace_smul, trace_atomMatrix, smul_eq_mul]
    rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨coefficient, ?_⟩
    rw [sum_smul_tracelessAtomMatrix, hcoefficient, hleveragePairing, zero_div, zero_smul,
      sub_zero]

/-- At a `(6,3)` crux the harmonic relation space is exactly the line spanned by the
weights: the instantiation of the general statement at the shipped
`Gtz.SixThreeCrux.linearIndependent_veronese`. -/
theorem SixThreeCrux.sum_smul_tracelessAtomMatrix_eq_zero_iff (crux : SixThreeCrux)
    (coefficient : Fin 6 → ℝ) :
    (∑ c, coefficient c • tracelessAtomMatrix 3 (crux.design.atom c) = 0)
      ↔ ∃ scale : ℝ, ∀ c, coefficient c = scale * crux.design.weight c :=
  sum_smul_tracelessAtomMatrix_eq_zero_iff_of_linearIndependent crux.design (by norm_num)
    crux.linearIndependent_veronese coefficient

/-- At a `(6,3)` crux the six harmonic parts SPAN the five-dimensional traceless space,
consuming the shipped `Gtz.SixThreeCrux.span_veronese_eq_symmetricSubmodule`. -/
theorem SixThreeCrux.span_tracelessAtomMatrix_eq_symmetricTracelessSubmodule
    (crux : SixThreeCrux) :
    Submodule.span ℝ (Set.range fun c : Fin 6 => tracelessAtomMatrix 3 (crux.design.atom c))
      = symmetricTracelessSubmodule 3 :=
  span_tracelessAtomMatrix_eq_symmetricTracelessSubmodule_of_span crux.design (by norm_num)
    crux.span_veronese_eq_symmetricSubmodule

/-- **A `(6,3)` CRUX IS A POSITIVELY ORIENTED SPANNING CIRCUIT.**  Its six harmonic
points span the five-dimensional traceless space, their relation space is a single
line, and that line is spanned by a STRICTLY POSITIVE vector — the weights.  What a
crux adds to that geometry is the failure itself, `Gtz.SixThreeCrux.hasNoDominatingTriple`. -/
theorem SixThreeCrux.exists_pos_harmonicCircuit (crux : SixThreeCrux) :
    ∃ circuit : Fin 6 → ℝ, (∀ c, 0 < circuit c)
      ∧ (∑ c, circuit c • tracelessAtomMatrix 3 (crux.design.atom c) = 0)
      ∧ ∀ other : Fin 6 → ℝ, (∑ c, other c • tracelessAtomMatrix 3 (crux.design.atom c) = 0)
          → ∃ scale : ℝ, ∀ c, other c = scale * circuit c :=
  exists_pos_harmonicCircuit_of_linearIndependent crux.design (by norm_num)
    crux.linearIndependent_veronese

/-! ## The hypersimplex vertex direction and the domination cone -/

/-- The direction from the weights to the hypersimplex vertex `1_C`. -/
def hypersimplexVertexDirection (D : WeightedDesign m k) (chosen : Finset (Fin m)) :
    Fin m → ℝ :=
  fun atomIndex => (if atomIndex ∈ chosen then (1 : ℝ) else 0) - D.weight atomIndex

/-- **THE CAPTURE IDENTITY**: `S_C − I = ∑_d ((1_C)_d − t_d) G_d`.  Trivial from
Parseval, and it is the whole content of the vertex-capture reading. -/
theorem subsetSum_sub_one_eq_sum_vertexDirection_smul_atomMatrix (D : WeightedDesign m k)
    (chosen : Finset (Fin m)) :
    subsetSum D chosen - 1
      = ∑ d, hypersimplexVertexDirection D chosen d • atomMatrix (D.atom d) := by
  have hindicator :
      ∑ d, (if d ∈ chosen then (1 : ℝ) else 0) • atomMatrix (D.atom d)
        = subsetSum D chosen := by
    have hpointwise : ∀ d : Fin m,
        (if d ∈ chosen then (1 : ℝ) else 0) • atomMatrix (D.atom d)
          = if d ∈ chosen then atomMatrix (D.atom d) else 0 := by
      intro d
      by_cases hmem : d ∈ chosen <;> simp [hmem]
    rw [Finset.sum_congr rfl fun d _ => hpointwise d, Finset.sum_ite_mem,
      Finset.univ_inter, subsetSum]
  rw [← hindicator, ← D.isParseval, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun d _ => by rw [hypersimplexVertexDirection, sub_smul]

/-- **THE DOMINATION CONE** `K = { α : ∑_d α_d g_d g_dᵀ ⪰ 0 }`.  Note it is
WEIGHT-FREE: it depends on the atoms alone, and all the weight dependence of the
capture reading sits in the base point. -/
def dominationCone (D : WeightedDesign m k) : ConvexCone ℝ (Fin m → ℝ) where
  carrier := {coefficient | (∑ d, coefficient d • atomMatrix (D.atom d)).PosSemidef}
  smul_mem' scale hscale coefficient hcoefficient := by
    have hrewrite : ∑ d, (scale • coefficient) d • atomMatrix (D.atom d)
        = scale • ∑ d, coefficient d • atomMatrix (D.atom d) := by
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun d _ => by rw [Pi.smul_apply, smul_smul, smul_eq_mul]
    show (∑ d, (scale • coefficient) d • atomMatrix (D.atom d)).PosSemidef
    rw [hrewrite]
    exact hcoefficient.smul hscale.le
  add_mem' {first} hfirst {second} hsecond := by
    have hrewrite : ∑ d, (first + second) d • atomMatrix (D.atom d)
        = (∑ d, first d • atomMatrix (D.atom d)) + ∑ d, second d • atomMatrix (D.atom d) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun d _ => by rw [Pi.add_apply, add_smul]
    show (∑ d, (first + second) d • atomMatrix (D.atom d)).PosSemidef
    rw [hrewrite]
    exact hfirst.add hsecond

theorem mem_dominationCone_iff (D : WeightedDesign m k) (coefficient : Fin m → ℝ) :
    coefficient ∈ dominationCone D
      ↔ (∑ d, coefficient d • atomMatrix (D.atom d)).PosSemidef :=
  Iff.rfl

/-- **DOMINATION IS VERTEX CAPTURE.** -/
theorem dominates_iff_vertexDirection_mem_dominationCone (D : WeightedDesign m k)
    (chosen : Finset (Fin m)) :
    Dominates D chosen ↔ hypersimplexVertexDirection D chosen ∈ dominationCone D := by
  rw [mem_dominationCone_iff, Dominates,
    subsetSum_sub_one_eq_sum_vertexDirection_smul_atomMatrix]

/-- `GtzWeighted m k` IS "the domination cone captures a hypersimplex vertex
direction, at every design". -/
theorem gtzWeighted_iff_forall_exists_vertexDirection_mem_dominationCone :
    GtzWeighted m k ↔ ∀ D : WeightedDesign m k, ∃ chosen : Finset (Fin m),
      chosen.card = k ∧ hypersimplexVertexDirection D chosen ∈ dominationCone D := by
  refine forall_congr' fun D => exists_congr fun chosen => and_congr_right fun _ => ?_
  exact dominates_iff_vertexDirection_mem_dominationCone D chosen

/-- The cone contains the nonnegative orthant: every atom is semidefinite. -/
theorem mem_dominationCone_of_nonneg (D : WeightedDesign m k) {coefficient : Fin m → ℝ}
    (hnonneg : ∀ d, 0 ≤ coefficient d) : coefficient ∈ dominationCone D := by
  rw [mem_dominationCone_iff]
  refine Finset.sum_induction _ Matrix.PosSemidef (fun _ _ => Matrix.PosSemidef.add)
    (Matrix.PosSemidef.zero) fun d _ => ?_
  exact (posSemidef_atomMatrix (D.atom d)).smul (hnonneg d)

/-- The weights lie in the cone, with the identity as image. -/
theorem weight_mem_dominationCone (D : WeightedDesign m k) : D.weight ∈ dominationCone D := by
  rw [mem_dominationCone_iff, D.isParseval]
  exact Matrix.PosSemidef.one

/-- **THE LINEALITY SPACE OF THE DOMINATION CONE IS THE STRESS SPACE.**  A direction
and its negative both lie in the cone exactly when the direction is a stress.  So the
cone is pointed precisely on the stress-free stratum — the stratum
`Gtz.exists_dominating_sixThree_of_stress` cannot reduce. -/
theorem mem_dominationCone_neg_iff_stress (D : WeightedDesign m k) (coefficient : Fin m → ℝ) :
    (coefficient ∈ dominationCone D ∧ (-coefficient) ∈ dominationCone D)
      ↔ ∑ d, coefficient d • atomMatrix (D.atom d) = 0 := by
  have hneg : ∑ d, (-coefficient) d • atomMatrix (D.atom d)
      = -∑ d, coefficient d • atomMatrix (D.atom d) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun d _ => by rw [Pi.neg_apply, neg_smul]
  rw [mem_dominationCone_iff, mem_dominationCone_iff, hneg]
  constructor
  · rintro ⟨hpos, hnegPos⟩
    refine Matrix.ext_of_mulVec_single fun basisIndex => ?_
    rw [Matrix.zero_mulVec]
    refine (Matrix.PosSemidef.dotProduct_mulVec_zero_iff hpos _).mp ?_
    have hupper := hnegPos.dotProduct_mulVec_nonneg (Pi.single basisIndex 1)
    rw [Matrix.neg_mulVec, dotProduct_neg] at hupper
    exact le_antisymm (by linarith [hupper])
      (hpos.dotProduct_mulVec_nonneg (Pi.single basisIndex 1))
  · intro hzero
    rw [hzero, neg_zero]
    exact ⟨Matrix.PosSemidef.zero, Matrix.PosSemidef.zero⟩

/-- The domination cone always contains the origin. -/
theorem pointed_dominationCone (D : WeightedDesign m k) : (dominationCone D).Pointed :=
  mem_dominationCone_of_nonneg D fun _ => le_refl 0

/-- **SALIENCE OF THE DOMINATION CONE IS STRESS-FREENESS**, in Mathlib's own
convex-cone vocabulary (`ConvexCone.Salient C : ∀ x ∈ C, x ≠ 0 → -x ∉ C`).  This is
`mem_dominationCone_neg_iff_stress` read as a property of the cone rather than of a
direction. -/
theorem salient_dominationCone_iff (D : WeightedDesign m k) :
    (dominationCone D).Salient
      ↔ ∀ stress : Fin m → ℝ, (∑ d, stress d • atomMatrix (D.atom d) = 0) → stress = 0 := by
  constructor
  · intro hsalient stress hstress
    by_contra hnonzero
    obtain ⟨hmem, hnegMem⟩ := (mem_dominationCone_neg_iff_stress D stress).mpr hstress
    exact hsalient stress hmem hnonzero hnegMem
  · intro hstressFree coefficient hmem hnonzero hnegMem
    exact hnonzero (hstressFree coefficient
      ((mem_dominationCone_neg_iff_stress D coefficient).mp ⟨hmem, hnegMem⟩))

/-- On the stress-free stratum the domination cone is SALIENT: linear independence of
the Veronese images is exactly the absence of a lineality direction. -/
theorem salient_dominationCone_of_linearIndependent (D : WeightedDesign m k)
    (hindependent : LinearIndependent ℝ fun c : Fin m => atomMatrix (D.atom c)) :
    (dominationCone D).Salient := by
  rw [salient_dominationCone_iff]
  intro stress hstress
  funext c
  exact (Fintype.linearIndependent_iff.mp hindependent) stress hstress c

/-- The domination cone of a `(6,3)` crux is salient. -/
theorem SixThreeCrux.salient_dominationCone (crux : SixThreeCrux) :
    (dominationCone crux.design).Salient :=
  salient_dominationCone_of_linearIndependent crux.design crux.linearIndependent_veronese

/-- **THE WEIGHTS ARE AN ALGEBRAIC INTERIOR POINT OF THE DOMINATION CONE.**  Every
direction can be walked a positive distance from `t` without leaving the cone,
because the weights' image is the identity.  The proof is an entrywise bound — no
operator norm, no spectral theorem, and NO spanning hypothesis — so it holds uniformly
at every weighted design. -/
theorem exists_pos_smul_add_weight_mem_dominationCone (D : WeightedDesign m k)
    (direction : Fin m → ℝ) :
    ∃ step : ℝ, 0 < step ∧ D.weight + step • direction ∈ dominationCone D := by
  classical
  set moment : Matrix (Fin k) (Fin k) ℝ := ∑ d, direction d • atomMatrix (D.atom d)
    with hmoment
  set entryBound : ℝ := ∑ rowIndex, ∑ colIndex, |moment rowIndex colIndex|
    with hentryBound
  have hentryBoundNonneg : 0 ≤ entryBound :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨(entryBound + 1)⁻¹, by positivity, ?_⟩
  have hsplit : ∑ d, (D.weight + (entryBound + 1)⁻¹ • direction) d • atomMatrix (D.atom d)
      = 1 + (entryBound + 1)⁻¹ • moment := by
    rw [hmoment, Finset.smul_sum, ← D.isParseval, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun d _ => by
      rw [Pi.add_apply, Pi.smul_apply, add_smul, smul_smul, smul_eq_mul]
  rw [mem_dominationCone_iff, hsplit]
  have hsymm : ((1 : Matrix (Fin k) (Fin k) ℝ) + (entryBound + 1)⁻¹ • moment).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial,
      Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_smul]
    congr 1
    congr 1
    rw [hmoment, Matrix.transpose_sum]
    exact Finset.sum_congr rfl fun d _ => by
      rw [Matrix.transpose_smul, atomMatrix, Matrix.transpose_vecMulVec]
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hsymm fun vector => ?_
  have hquadratic : star vector ⬝ᵥ ((1 : Matrix (Fin k) (Fin k) ℝ)
        + (entryBound + 1)⁻¹ • moment) *ᵥ vector
      = (∑ coord, vector coord ^ 2)
        + (entryBound + 1)⁻¹
          * ∑ rowIndex, ∑ colIndex, vector rowIndex * moment rowIndex colIndex
              * vector colIndex := by
    rw [Matrix.add_mulVec, dotProduct_add, Matrix.one_mulVec]
    congr 1
    · simp only [dotProduct, Pi.star_apply, star_trivial]
      exact Finset.sum_congr rfl fun coord _ => (pow_two _).symm
    · rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
      congr 1
      simp only [dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial, Finset.mul_sum]
      exact Finset.sum_congr rfl fun rowIndex _ =>
        Finset.sum_congr rfl fun colIndex _ => by ring
  rw [hquadratic]
  set squareSum : ℝ := ∑ coord, vector coord ^ 2 with hsquareSum
  have hsquareSumNonneg : 0 ≤ squareSum :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hcoordBound : ∀ rowIndex colIndex : Fin k,
      |vector rowIndex * moment rowIndex colIndex * vector colIndex|
        ≤ |moment rowIndex colIndex| * squareSum := by
    intro rowIndex colIndex
    have hrow : vector rowIndex ^ 2 ≤ squareSum :=
      Finset.single_le_sum (f := fun coord => vector coord ^ 2)
        (fun _ _ => sq_nonneg _) (Finset.mem_univ rowIndex)
    have hcol : vector colIndex ^ 2 ≤ squareSum :=
      Finset.single_le_sum (f := fun coord => vector coord ^ 2)
        (fun _ _ => sq_nonneg _) (Finset.mem_univ colIndex)
    have hproduct : |vector rowIndex| * |vector colIndex| ≤ squareSum := by
      nlinarith [abs_nonneg (vector rowIndex), abs_nonneg (vector colIndex),
        sq_abs (vector rowIndex), sq_abs (vector colIndex),
        sq_nonneg (|vector rowIndex| - |vector colIndex|)]
    calc |vector rowIndex * moment rowIndex colIndex * vector colIndex|
        = |moment rowIndex colIndex| * (|vector rowIndex| * |vector colIndex|) := by
          rw [abs_mul, abs_mul]; ring
      _ ≤ |moment rowIndex colIndex| * squareSum := by
          exact mul_le_mul_of_nonneg_left hproduct (abs_nonneg _)
  have hcross : |∑ rowIndex, ∑ colIndex,
        vector rowIndex * moment rowIndex colIndex * vector colIndex|
      ≤ entryBound * squareSum := by
    calc |∑ rowIndex, ∑ colIndex, vector rowIndex * moment rowIndex colIndex * vector colIndex|
        ≤ ∑ rowIndex, |∑ colIndex,
            vector rowIndex * moment rowIndex colIndex * vector colIndex| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ rowIndex, ∑ colIndex, |moment rowIndex colIndex| * squareSum := by
          refine Finset.sum_le_sum fun rowIndex _ => ?_
          exact (Finset.abs_sum_le_sum_abs _ _).trans
            (Finset.sum_le_sum fun colIndex _ => hcoordBound rowIndex colIndex)
      _ = entryBound * squareSum := by
          rw [hentryBound, Finset.sum_mul]
          exact Finset.sum_congr rfl fun _ _ => (Finset.sum_mul _ _ _).symm
  have hstepBound : (entryBound + 1)⁻¹ * (entryBound * squareSum) ≤ squareSum := by
    rw [inv_mul_le_iff₀ (by linarith)]
    nlinarith
  have hlower : -(entryBound * squareSum)
      ≤ ∑ rowIndex, ∑ colIndex, vector rowIndex * moment rowIndex colIndex * vector colIndex :=
    neg_le_of_abs_le hcross
  have hstepPos : (0 : ℝ) < (entryBound + 1)⁻¹ := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hlower hstepPos.le]

/-! ## The traceless reading of domination -/

/-- **DOMINATION IN HARMONIC COORDINATES.**  `S_C − I = ∑_{c ∈ C} H_c + (e₁(ℓ_C)/k − 1) I`,
so a subset dominates exactly when its harmonic sum clears the scalar
`1 − e₁(ℓ_C)/k` — the trace budget of the block against the rank.  All the
subset-dependence of the scalar leg is the one number `∑_{c ∈ C} ℓ_c`. -/
theorem subsetSum_sub_one_eq_sum_tracelessAtomMatrix_add_smul_one (D : WeightedDesign m k)
    (chosen : Finset (Fin m)) :
    subsetSum D chosen - 1
      = (∑ c ∈ chosen, tracelessAtomMatrix k (D.atom c))
        + (((∑ c ∈ chosen, leverageOf (D.atom c)) / k) - 1)
          • (1 : Matrix (Fin k) (Fin k) ℝ) := by
  have hharmonic : ∑ c ∈ chosen, tracelessAtomMatrix k (D.atom c)
      = subsetSum D chosen
        - ((∑ c ∈ chosen, leverageOf (D.atom c)) / k) • (1 : Matrix (Fin k) (Fin k) ℝ) := by
    rw [subsetSum, Finset.sum_div, Finset.sum_smul, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun c _ => rfl
  rw [hharmonic, sub_smul, one_smul]
  abel

/-! ## Rank two: the light cone and the polygon template -/

/-- The diagonal harmonic coordinate at rank two is half the shipped Bloch square. -/
theorem tracelessAtomMatrix_apply_diag_rankTwo (atom : Fin 2 → ℝ) :
    2 * tracelessAtomMatrix 2 atom 0 0 = blochSquare atom 0 := by
  simp only [tracelessAtomMatrix, blochSquare, atomMatrix, leverageOf, Matrix.sub_apply,
    Matrix.smul_apply, Matrix.vecMulVec_apply, Matrix.one_apply_eq, Fin.sum_univ_two,
    Matrix.cons_val_zero, smul_eq_mul]
  ring

/-- The off-diagonal harmonic coordinate at rank two is half the shipped Bloch square. -/
theorem tracelessAtomMatrix_apply_offDiag_rankTwo (atom : Fin 2 → ℝ) :
    2 * tracelessAtomMatrix 2 atom 0 1 = blochSquare atom 1 := by
  have hoff : (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = 0 :=
    Matrix.one_apply_ne (by decide)
  simp only [tracelessAtomMatrix, blochSquare, atomMatrix, Matrix.sub_apply,
    Matrix.smul_apply, Matrix.vecMulVec_apply, hoff, Matrix.cons_val_one,
    Matrix.cons_val_zero, smul_eq_mul]
  ring

/-- **THE DOUBLE-ANGLE RADIUS.**  At rank two the traceless symmetric matrices are two
dimensional and `−det` is the squared Euclidean length there, so a harmonic atom sits
on a circle whose radius is exactly HALF ITS LEVERAGE: `det H_g = −(ℓ_g/2)²`.  The
vector form of the same fact is the shipped `Gtz.blochSquare_normSq`; the two
coordinate systems are matched by `tracelessAtomMatrix_apply_diag_rankTwo` and
`tracelessAtomMatrix_apply_offDiag_rankTwo`. -/
theorem det_tracelessAtomMatrix_rankTwo (atom : Fin 2 → ℝ) :
    (tracelessAtomMatrix 2 atom).det = -(leverageOf atom / 2) ^ 2 := by
  have hdiag : (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = 1 := Matrix.one_apply_eq 0
  have hdiagOne : (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 1 = 1 := Matrix.one_apply_eq 1
  have hoffZeroOne : (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = 0 := Matrix.one_apply_ne (by decide)
  have hoffOneZero : (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = 0 := Matrix.one_apply_ne (by decide)
  simp only [Matrix.det_fin_two, tracelessAtomMatrix, atomMatrix, leverageOf,
    Matrix.sub_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, hdiag, hdiagOne,
    hoffZeroOne, hoffOneZero, Fin.sum_univ_two, smul_eq_mul]
  ring

/-- Adding a scalar to a TRACELESS `2 × 2` matrix adds its square to the determinant:
the light-cone identity `det(H + s I) = s² + det H`. -/
theorem det_add_smul_one_rankTwo {matrix : Matrix (Fin 2) (Fin 2) ℝ}
    (htrace : Matrix.trace matrix = 0) (scalar : ℝ) :
    (matrix + scalar • (1 : Matrix (Fin 2) (Fin 2) ℝ)).det = scalar ^ 2 + matrix.det := by
  have hdiagSum : matrix 0 0 + matrix 1 1 = 0 := by
    rw [Matrix.trace_fin_two] at htrace
    exact htrace
  have hdiag : (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = 1 := Matrix.one_apply_eq 0
  have hdiagOne : (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 1 = 1 := Matrix.one_apply_eq 1
  have hoffZeroOne : (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = 0 := Matrix.one_apply_ne (by decide)
  have hoffOneZero : (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = 0 := Matrix.one_apply_ne (by decide)
  simp only [Matrix.det_fin_two, Matrix.add_apply, Matrix.smul_apply, hdiag, hdiagOne,
    hoffZeroOne, hoffOneZero, smul_eq_mul, mul_one, mul_zero, add_zero]
  linear_combination scalar * hdiagSum

/-- **RANK-TWO DOMINATION IS A LIGHT-CONE INEQUALITY**, sqrt-free.  A subset dominates
exactly when its trace budget `(∑_{c∈C} ℓ_c)/2 − 1` is nonnegative and dominates the
harmonic radius of the block, `√(−det ∑_{c∈C} H_c)`.

With `det H_c = −(ℓ_c/2)²` (`det_tracelessAtomMatrix_rankTwo`), the two-element case
reads `|h_i| + |h_j| − |h_i + h_j| ≥ 1`: the classical isoperimetric-polygon form of
rank-two GTZ, whose closed polygon is the circuit `∑_c t_c H_c = 0`.  The general-rank
harmonic vocabulary therefore reproduces the rank-two template exactly.  This is a
DICTIONARY, not a proof of rank-two GTZ — that is the shipped `Gtz.gtz_rank_two`. -/
theorem dominates_iff_harmonicRadius_rankTwo (D : WeightedDesign m 2)
    (chosen : Finset (Fin m)) :
    Dominates D chosen
      ↔ (0 ≤ (∑ c ∈ chosen, leverageOf (D.atom c)) / 2 - 1
          ∧ 0 ≤ ((∑ c ∈ chosen, leverageOf (D.atom c)) / 2 - 1) ^ 2
              + (∑ c ∈ chosen, tracelessAtomMatrix 2 (D.atom c)).det) := by
  set harmonic : Matrix (Fin 2) (Fin 2) ℝ := ∑ c ∈ chosen, tracelessAtomMatrix 2 (D.atom c)
    with hharmonic
  set budget : ℝ := (∑ c ∈ chosen, leverageOf (D.atom c)) / 2 - 1 with hbudget
  have hgap : subsetSum D chosen - 1 = harmonic + budget • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    rw [hharmonic, hbudget]
    exact subsetSum_sub_one_eq_sum_tracelessAtomMatrix_add_smul_one D chosen
  have hsymmetric : harmonicᵀ = harmonic := by
    rw [hharmonic, Matrix.transpose_sum]
    exact Finset.sum_congr rfl fun c _ => tracelessAtomMatrix_transpose 2 (D.atom c)
  have htraceless : Matrix.trace harmonic = 0 := by
    rw [hharmonic, Matrix.trace_sum]
    refine Finset.sum_eq_zero fun c _ => ?_
    exact trace_tracelessAtomMatrix 2 (by norm_num) (D.atom c)
  have hdiagSum : harmonic 0 0 + harmonic 1 1 = 0 := by
    rw [Matrix.trace_fin_two] at htraceless
    exact htraceless
  have hsymEntry : harmonic 1 0 = harmonic 0 1 := by
    have hentry := congrFun (congrFun hsymmetric 0) 1
    rwa [Matrix.transpose_apply] at hentry
  have hgapSymmetric : (harmonic + budget • (1 : Matrix (Fin 2) (Fin 2) ℝ))ᵀ
      = harmonic + budget • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    rw [Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_one, hsymmetric]
  have hdiag : (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = 1 := Matrix.one_apply_eq 0
  have hdiagOne : (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 1 = 1 := Matrix.one_apply_eq 1
  have hoffZeroOne : (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = 0 := Matrix.one_apply_ne (by decide)
  have hoppositeDiag : harmonic 1 1 = -harmonic 0 0 := by linarith
  have hdetHarmonic : harmonic.det = -(harmonic 0 0 ^ 2) - harmonic 0 1 ^ 2 := by
    rw [Matrix.det_fin_two, hsymEntry, hoppositeDiag]
    ring
  rw [Dominates, hgap, posSemidef_two_iff hgapSymmetric]
  simp only [Matrix.add_apply, Matrix.smul_apply, hdiag, hdiagOne, hoffZeroOne, smul_eq_mul,
    mul_one, mul_zero, add_zero]
  rw [hdetHarmonic, hoppositeDiag]
  constructor
  · rintro ⟨hfirst, hsecond, hthird⟩
    exact ⟨by linarith, by nlinarith⟩
  · rintro ⟨hbudgetNonneg, hradius⟩
    have hsquare : harmonic 0 0 ^ 2 ≤ budget ^ 2 := by nlinarith [sq_nonneg (harmonic 0 1)]
    have habsolute : |harmonic 0 0| ≤ budget := by
      nlinarith [abs_nonneg (harmonic 0 0), sq_abs (harmonic 0 0)]
    have hlower := neg_abs_le (harmonic 0 0)
    have hupper := le_abs_self (harmonic 0 0)
    exact ⟨by linarith, by linarith, by nlinarith⟩

/-! ## The probe quartic moment and the metric capture criterion -/

/-- The **probe quartic moment** `Q₄(x) = ∑_d ⟨g_d, x⟩⁴`, the UNWEIGHTED fourth moment
of a design in a probe direction.  Distinct from the shipped
`Gtz.shareWeightedFourthMoment`, which is the share-weighted Gram scalar
`∑_{c,d} s_c s_d γ_cd⁴` and carries no probe. -/
noncomputable def probeQuarticMoment (D : WeightedDesign m k) (probe : Fin k → ℝ) : ℝ :=
  ∑ d, (D.atom d ⬝ᵥ probe) ^ 4

/-- `bound` dominates the probe quartic moment uniformly. -/
def HasProbeQuarticBound (D : WeightedDesign m k) (bound : ℝ) : Prop :=
  ∀ probe : Fin k → ℝ, probeQuarticMoment D probe ≤ bound * (∑ i, probe i ^ 2) ^ 2

/-- The sum of squared leverages is always a probe quartic bound: Cauchy–Schwarz on
each atom separately.  Free, explicit, and rank-generic — no optimisation. -/
theorem hasProbeQuarticBound_sum_sq_leverage (D : WeightedDesign m k) :
    HasProbeQuarticBound D (∑ d, leverageOf (D.atom d) ^ 2) := by
  intro probe
  rw [probeQuarticMoment, Finset.sum_mul]
  refine Finset.sum_le_sum fun d _ => ?_
  have hcs : (D.atom d ⬝ᵥ probe) ^ 2
      ≤ leverageOf (D.atom d) * ∑ i, probe i ^ 2 := by
    have hraw := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (D.atom d) probe
    simpa [leverageOf, dotProduct] using hraw
  have hnonneg : (0 : ℝ) ≤ ∑ i, probe i ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  calc (D.atom d ⬝ᵥ probe) ^ 4 = ((D.atom d ⬝ᵥ probe) ^ 2) ^ 2 := by ring
    _ ≤ (leverageOf (D.atom d) * ∑ i, probe i ^ 2) ^ 2 := by
        exact pow_le_pow_left₀ (sq_nonneg _) hcs 2
    _ = leverageOf (D.atom d) ^ 2 * (∑ i, probe i ^ 2) ^ 2 := by ring

/-- **THE METRIC CAPTURE LEMMA**, general `(size, rank)`.  Split a coefficient vector
as `scale · t + residual`.  Its moment is `scale · I + A(residual)`, and Cauchy–Schwarz
against the probe quartic bound controls the residual's quadratic form by
`|residual|₂ √bound` times the probe norm.  So once `|residual|₂ √bound ≤ scale`, the
moment is positive semidefinite.

Geometrically: `t` is an interior point of the domination cone whose Euclidean
inradius there is exactly `1/√Q₄max`, and this is the statement that the cone contains
the round cone that inradius generates.  The module header records exactly how far
that reaches, and why it cannot reach the cell. -/
theorem posSemidef_sum_smul_atomMatrix_of_probeQuarticBound (D : WeightedDesign m k)
    {bound scale : ℝ} (hboundNonneg : 0 ≤ bound) (hbound : HasProbeQuarticBound D bound)
    (residual : Fin m → ℝ)
    (hgap : Real.sqrt (∑ d, residual d ^ 2) * Real.sqrt bound ≤ scale) :
    (∑ d, (scale * D.weight d + residual d) • atomMatrix (D.atom d)).PosSemidef := by
  have hsplit : ∑ d, (scale * D.weight d + residual d) • atomMatrix (D.atom d)
      = scale • (1 : Matrix (Fin k) (Fin k) ℝ)
        + ∑ d, residual d • atomMatrix (D.atom d) := by
    rw [← D.isParseval, Finset.smul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun d _ => by rw [add_smul, smul_smul]
  rw [hsplit]
  have hsymm : (scale • (1 : Matrix (Fin k) (Fin k) ℝ)
      + ∑ d, residual d • atomMatrix (D.atom d)).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial,
      Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_one]
    congr 1
    rw [Matrix.transpose_sum]
    exact Finset.sum_congr rfl fun d _ => by
      rw [Matrix.transpose_smul, atomMatrix, Matrix.transpose_vecMulVec]
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hsymm fun probe => ?_
  have hquad : star probe ⬝ᵥ (scale • (1 : Matrix (Fin k) (Fin k) ℝ)
        + ∑ d, residual d • atomMatrix (D.atom d)) *ᵥ probe
      = scale * (∑ i, probe i ^ 2)
        + ∑ d, residual d * (D.atom d ⬝ᵥ probe) ^ 2 := by
    rw [Matrix.add_mulVec, dotProduct_add]
    congr 1
    · rw [Matrix.smul_mulVec, dotProduct_smul, Matrix.one_mulVec, smul_eq_mul]
      congr 1
      simp only [dotProduct, Pi.star_apply, star_trivial]
      exact Finset.sum_congr rfl fun i _ => (pow_two _).symm
    · rw [Matrix.sum_mulVec, dotProduct_sum]
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
      congr 1
      simp only [star_trivial]
      exact dotProduct_atomMatrix_mulVec (D.atom d) probe
  rw [hquad]
  set probeNormSq : ℝ := ∑ i, probe i ^ 2 with hprobeNormSq
  have hprobeNonneg : (0 : ℝ) ≤ probeNormSq :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  set residualNormSq : ℝ := ∑ d, residual d ^ 2 with hresidualNormSq
  have hresidualNonneg : (0 : ℝ) ≤ residualNormSq :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hcs : (∑ d, residual d * (D.atom d ⬝ᵥ probe) ^ 2) ^ 2
      ≤ residualNormSq * ∑ d, ((D.atom d ⬝ᵥ probe) ^ 2) ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ residual
      (fun d => (D.atom d ⬝ᵥ probe) ^ 2)
  have hquartic : ∑ d, ((D.atom d ⬝ᵥ probe) ^ 2) ^ 2 ≤ bound * probeNormSq ^ 2 := by
    have hraw := hbound probe
    rw [probeQuarticMoment] at hraw
    calc ∑ d, ((D.atom d ⬝ᵥ probe) ^ 2) ^ 2
        = ∑ d, (D.atom d ⬝ᵥ probe) ^ 4 := Finset.sum_congr rfl fun d _ => by ring
      _ ≤ bound * probeNormSq ^ 2 := hraw
  have hsqbound : (∑ d, residual d * (D.atom d ⬝ᵥ probe) ^ 2) ^ 2
      ≤ (residualNormSq * bound) * probeNormSq ^ 2 := by
    refine hcs.trans ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hquartic hresidualNonneg
  have hlower : -(Real.sqrt residualNormSq * Real.sqrt bound * probeNormSq)
      ≤ ∑ d, residual d * (D.atom d ⬝ᵥ probe) ^ 2 := by
    have habs : |∑ d, residual d * (D.atom d ⬝ᵥ probe) ^ 2|
        ≤ Real.sqrt residualNormSq * Real.sqrt bound * probeNormSq := by
      have hsqrt := Real.sqrt_le_sqrt hsqbound
      rw [Real.sqrt_sq_eq_abs] at hsqrt
      refine hsqrt.trans_eq ?_
      rw [Real.sqrt_mul (by positivity), Real.sqrt_mul hresidualNonneg,
        Real.sqrt_sq hprobeNonneg]
    exact neg_le_of_abs_le habs
  have hcoef : 0 ≤ scale - Real.sqrt residualNormSq * Real.sqrt bound := by linarith
  nlinarith [mul_nonneg hcoef hprobeNonneg]

/-- **VERTEX CAPTURE FROM THE PROBE QUARTIC BOUND.**  If the hypersimplex vertex
direction `1_C − t` decomposes as `scale · t + residual` with
`|residual|₂ √bound ≤ scale`, then `C` dominates.  The `scale` is free: the sharp
choice is `scale = ⟨δ_C, t⟩ / (|t|² − 1/bound)`, which turns the criterion into the
angle test `sin ∠(1_C − t, t) ≤ 1/(√bound · |t|)`. -/
theorem dominates_of_probeQuarticBound (D : WeightedDesign m k) (chosen : Finset (Fin m))
    {bound scale : ℝ} (hboundNonneg : 0 ≤ bound) (hbound : HasProbeQuarticBound D bound)
    (hgap : Real.sqrt (∑ d, (hypersimplexVertexDirection D chosen d
              - scale * D.weight d) ^ 2) * Real.sqrt bound ≤ scale) :
    Dominates D chosen := by
  have hkey := posSemidef_sum_smul_atomMatrix_of_probeQuarticBound D hboundNonneg hbound
    (fun d => hypersimplexVertexDirection D chosen d - scale * D.weight d) hgap
  have hsimp : ∑ d, (scale * D.weight d
        + (hypersimplexVertexDirection D chosen d - scale * D.weight d))
        • atomMatrix (D.atom d)
      = ∑ d, hypersimplexVertexDirection D chosen d • atomMatrix (D.atom d) :=
    Finset.sum_congr rfl fun d _ => by
      rw [show scale * D.weight d
            + (hypersimplexVertexDirection D chosen d - scale * D.weight d)
          = hypersimplexVertexDirection D chosen d from by ring]
  rw [hsimp] at hkey
  rw [Dominates, subsetSum_sub_one_eq_sum_vertexDirection_smul_atomMatrix]
  exact hkey

end Gtz
