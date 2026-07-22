# GTZ — Lean 4 formalization of the Goreinov–Tyrtyshnikov–Zamarashkin problem

**Conjecture (GTZ 1997).** Every real n×k matrix with orthonormal columns has a
k×k row submatrix with σ_min ≥ 1/√n. Known: k ≤ 2 proven (Sengupta–Pautov,
arXiv:2604.05944); false over ℂ (sharp constant α = 2 − 2/√3, SIC extremal).
First open case: weighted (6,3).

**This repository is the final proof artifact of the campaign** recorded in
`~/Downloads/gtz.md` (§§0–53): the eventual paper is the LaTeX rendition of
exactly the definitions, lemmas, and theorems in these modules, in the same
structure — the Lean development is the ground truth, the paper mirrors it.
(The C+OpenMP engine remains the discovery/refutation instrument; nothing enters
here before surviving its adversarial audits, and nothing is cited in the paper
that is not kernel-checked here.) Toolchain: Lean `v4.32.0` + Mathlib `v4.32.0`
(per-project; independent of the FX pin).

## Working form

Weighted design: g₁..g_m ∈ ℝᵏ, t_c > 0, Σt_c = 1, Σ t_c g_c g_cᵀ = I_k.
A k-subset C **dominates** iff Σ_{c∈C} g_c g_cᵀ ⪰ I_k. GTZ(k) for all n ⟺ every
weighted design has a dominating k-subset (`Gtz.GtzWeightedAll k`).

## The proven architecture being formalized (informal status: audited + verified)

1. **Canonical list** (Theorem L): via crystallization M(s) = s(s+1)/2 + 1 and
   weighted Naimark duality, GTZ(all k, all n) ⟺ the finite-per-rank list
   {weighted (m,s) : 2s ≤ m ≤ s(s+1)/2 + 1}. Closing (6,3) + (7,3) closes rank 3
   and co-rank ≤ 3 for every k.
2. **The certificate class** (rational Schur-pigeonhole): trace identity +
   excess-balance pigeonhole (branch a) and signature-(k−1,1) caps (branch b);
   regular at the zero-margin (k+1)-cycle; provably silent over ℂ.
3. **Lemma F_k** = Bhatia–Davis at mean zero: the corner covering at every rank,
   equality exactly at the 2ᵏ−1 fundamental-weight axes of A_k.
4. **Theorem B_k**: the exact (k+1)-cycle corner fiber closes at every rank.
5. Remaining open mathematics (not formalizable yet — still unproven): the
   Gate–Cap covering (GAP-S + GAP-T) and the corner tied tube at rank 3.

## Module map / status

| module | content | status |
|---|---|---|
| `Gtz/Basic.lean` | designs, domination, GtzWeighted/GtzOriginal, pivot | definitions |
| `Gtz/BhatiaDavis.lean` | Lemma F_k combinatorial core | **proved incl. tie classification** |
| `Gtz/Sanity.lean` | definition-pinning instances | **proved** (PSD atoms, monotonicity, (1,1) end-to-end) |
| `Gtz/SchurRankOne.lean` | rank-one Schur: N−ggᵀ ⪰ 0 ⟺ gᵀN⁻¹g ≤ 1 (N ≻ 0) | **proved** (polarization, no sqrt/no blocks) |
| `Gtz/TraceIdentity.lean` | trace identity, excess balance, rank-one Schur step, pigeonhole | **proved** (branch (a) complete, all (m,k)) |
| `Gtz/CapCriterion.lean` | signature-(k−1,1) rank-one completion | statement (sorry; see R-MECH-1) |
| `Gtz/Naimark.lean` | Theorem N, weighted duality | statement (sorry) |
| `Gtz/Crystallization.lean` | M(k) bounded support | statement (sorry) |
| `Gtz/CornerFiber.lean` | forced balance **proved** (audit F1); Theorem B_k | B_k assembly: sorry |
| `Gtz/Reductions.lean` | rank 1 **proved**; rank 2, canonical list, weighted→original | statements (sorry) |
| `Gtz/Audit.lean` | `#print axioms` for every proved theorem | FX discipline |

## Mechanization residuals (gaps surfaced BY the formalization; kept current)

* **R-MECH-1**: Mathlib v4.32 has no Cauchy eigenvalue interlacing. The cap
  criterion's "rank-one update keeps k−1 positive eigenvalues" needs either a
  hand-built interlacing lemma or a signature-free reformulation (candidate: the
  polarization pattern of `SchurRankOne` run on the negative eigenspace).
* **R-MECH-2**: Mathlib v4.32 has no PSD Schur-complement block criterion
  (`SchurComplement.lean` is determinant/inverse only). Worked around in
  `SchurRankOne.lean` by direct polarization; Theorem N's congruence chain will
  need the same treatment.
* Statement hygiene adopted while mechanizing: `pigeonhole` requires `1 ≤ k`
  (at k = 0 a one-atom design has weight 1 and the strict-weight argument
  degenerates) — the informal statements never said this.

## Rigor rules (FX standards)

- Nothing is called proven while it contains `sorry`; `Gtz/Audit.lean` prints the
  axiom set of every proved theorem on every build (expected: propext,
  Classical.choice, Quot.sound — nothing else, ever).
- Definitions stay minimal and Mathlib-anchored (`Matrix.PosSemidef`, no bespoke
  orders). Junk-value footguns are documented at the definition site and fenced
  by hypotheses at every use (`Matrix.inv` of a singular matrix is 0 — all
  `pivot` theorems carry `PosDef`).
- `Gtz/Sanity.lean` must stay sorry-free; if a refactor breaks it, the
  definitions drifted from the mathematics.
- Long game: a computable ℚ-certificate layer (`Decidable` checkers for the
  pigeonhole/cap certificates proven correct against the Prop layer) so that
  per-design closures are executable artifacts, not just proofs.

## Build

```
lake exe cache get   # once, downloads Mathlib oleans
lake build
```

## Next proof targets (in order)

1. `cap_criterion` (branch b) — resolve R-MECH-1 first (hand interlacing or the
   signature-free reformulation).
2. `corner_fiber_dominates` (Theorem B_k assembly: forced balance + pigeonhole +
   the exact spectrum of (k+1)I − h_dh_dᵀ; needs S_{Q₀} = (k+1)I from the corner
   Gram — a small quadratic-form lemma).
3. `crystallization` (Mathlib Carathéodory + drop monotonicity; the sharp bound
   needs dim Sym(k) = k(k+1)/2 — check Mathlib's `Matrix.IsSymm` submodule API).
4. `weighted_naimark_duality` (co-design completion; R-MECH-2 pattern again).
5. `gtz_rank_two` (de-spectralized Sengupta–Pautov — the largest single item).
