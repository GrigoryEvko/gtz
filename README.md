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
| `Gtz/CapCriterion.lean` | cap criterion, de-spectralized (signature witness pair) | **proved** (R-MECH-1 resolved by reformulation) |
| `Gtz/PsdKit.lean` | CS contraction flip, transpose transfers, invertible congruence, whitening | **proved** (squares only; no sqrt, no spectra) |
| `Gtz/Completion.lean` | orthonormal completion [A|B] | **proved** (stdOrthonormalBasis + fromCols flip) |
| `Gtz/Naimark.lean` | **Theorem N**, weighted duality | **proved** (four congruences; co-design completion) |
| `Gtz/Crystallization.lean` | M(k) = k(k+1)/2 + 1 bounded support (kernel walk) | **proved** (sharp constant; Sym2 count, no Carathéodory) |
| `Gtz/CornerFiber.lean` | simplex frame identity, forced balance, **Theorem B_k** | **proved** (all (m,k), 1 ≤ k; no spectral theory) |
| `Gtz/TwoByTwo.lean` | 2×2 PSD entry criterion (discriminant + SOS certificate); rank-one determinant lemma + **the one-surface identity** (wall tie ≡ z-mass tie) | **proved** |
| `Gtz/Deflation.lean` | k-general light-atom deflation (m+1,k) → (m,k) | **proved** |
| `Gtz/RankTwo.lean` | de-spectralized weighted Sengupta–Pautov Case B | **proved** (scalar sums and squares only) |
| `Gtz/PlanarPlatform.lean` | GAP-S platform: **Theorem R′** (E-restricted master identity, free shifted leverages), trace form, abstract **Corollary R″**, dust expansion (Prop-D.3 repair), pinch quadratic | **proved** (audited informally §68, then kernel-checked) |
| `Gtz/BlochDictionary.lean` | g-space dictionary: Bloch squares, the M-form identity, silence ⟹ pair entry ≥ 0, **Corollary R″ concrete and end-to-end** | **proved** |
| `Gtz/DustControl.lean` | **Proposition D complete**: mixed positivity, dust-pair floor, dust deficit ≥ −2δ₀δ₂ (tight), cross rebate ≥ 2κ₃δ₀; dust-only completions infeasible (moment squeeze) | **proved** (dust hypothesis unnecessary in D.3 — hygiene find) |
| `Gtz/Pushoff.lean` | **Zero-Atom Pushoff Theorem** — planar-norm kit (Cauchy–Schwarz, triangle from scratch), the pairing identity `Σ t_c d_c = 0`, Lipschitz defect, `t_e ≤ (\|ξ\|+½)·Σ t_c\|S_c−X_c\|` unconditionally, + the corner saturation witness (equality at ¼) | **proved** (dissolves GAP-T's δ_T = 0 case) |
| `Gtz/TightGraph.lean` | **max-degree theorem**: tightness is affine in the partner direction (polar chord), the chord's normal is nonzero when `ν\|ξ\| < ½`, a line meets the circle twice ⟹ ≤ 2 tight partners, **`K₁,₃` dead** | **proved** (pre-audit claim, mechanization surfaced its dust-exclusion dependency) |
| `Gtz/CertificateFrame.lean` | certificate-frame geometry: planar determinant kit, **the stress-leaf step** (two independent rays meet only at their vertex), the parabola pole characterization and its cloning consequence | **proved** (pre-audit claims) |
| `Gtz/LocalLaw.lean` | the **LP vertex bound** behind the first-order constant (weighted max, not average) and the **weight-split invariance** (structural root of σ-independence) | **proved** (pre-audit claims) |
| `Gtz/Interface.lean` | statement-(2) interface arithmetic: **the recorded pair is vacuous**, the ball's τ-ceiling, **the repaired pair is nonvacuous** (explicit witness), the formula rounds down, and the one-line nonvacuity test | **proved** |
| `Gtz/LawCounterexample.lean` | **kernel-checked refutation**: exact rational cap-10 design with `C_B(10)·σ* < B(σ*)` — the displayed local law `B_E(σ*) ≤ C_B(ℓ̄)σ*` is false for ℓ̄ ≥ 7 (`C_B` is the σ*→0 limit only) | **proved** (settles the build-vs-audit numerical dispute in the kernel) |
| `Gtz/Reductions.lean` | rank 1, **RANK 2**, bridge, **Theorem L**, rank-3→residuals, duality descent, square, rank bound, `GtzOriginal n 1/2` | **proved** (no sorries) |
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

## The formal frontier (everything else is kernel-checked)

RANK ≤ 2 IS FULLY CLOSED IN LEAN: `gtz_rank_two : GtzWeightedAll 2` (strong
induction on size; light-atom deflation + the de-spectralized Case-B pairing),
hence `gtz_original_rank_one/two : GtzOriginal n k` for k ∈ {1,2} and ALL n —
the Sengupta–Pautov theorem formalized, in its weighted generalization. The
assembly (Theorem L, rank-3 reduction, duality descent, square, rank bound)
is complete. The open obligations of GTZ-for-all-(n,k) are exactly:

1. `GtzWeighted 6 3` and `GtzWeighted 7 3` — the campaign's binding open
   mathematics (statement (1)/(2) residuals; math frontier LIVE — the audited
   GAP-S platform layer is kernel-checked in `PlanarPlatform.lean`; the open
   residue is the σ-free Łojasiewicz core + GAP-T + statement-(2) residuals).
2. The canonical window 2s ≤ m ≤ s(s+1)/2 + 1 for s ≥ 4 — open mathematics.
(The certificate infrastructure is complete: `cap_criterion` landed
de-spectralized — the signature-(k−1,1) hypothesis became a witness pair, a
negative direction plus PSD-ness on its N-orthogonal complement, resolving
R-MECH-1 by reformulation. THE REPOSITORY IS 100% SORRY-FREE: every formal
obligation of the campaign's proven ledger is kernel-checked.)

Theorem-N mechanization notes (landed): the informal W^{−1/2} matrix square
root is GONE — any whitening R with RᵀWR = I works (consumed from the
C*-factorization `CStarAlgebra.nonneg_iff_eq_star_mul_self`, the only
spectral-backed import); the two "spectra-sharing" steps of the informal proof
are replaced by the sqrt-free Cauchy–Schwarz flip (`PsdKit`): |Xᵀw|⁴ =
⟨w, X(Xᵀw)⟩² ≤ |w|²·|X(Xᵀw)|² ≤ |w|²·|Xᵀw|², squares only. `1 ≤ k` IS needed
here (k = 0 kills the co-design), unlike the bridge and crystallization.

Landed since: `original_of_weighted` (bridge, all n ≥ 1 — statement hygiene:
`1 ≤ k` and `k < n` both turned out unnecessary; the n = k square case rides
along free). `crystallization` at the SHARP M(k) = k(k+1)/2 + 1 — no
Carathéodory and no symmetric-matrix finrank needed: the moment map reads the
upper triangle (`Sym2.sortEquiv` + `Sym2.card` count k(k+1)/2), the kernel walk
does the support drop by hand, and domination pulls back because `subsetSum`
never reads weights; `1 ≤ k` again unnecessary.

Proof-technique note (B_k, landed): the informally-planned "exact spectrum of
(k+1)I − h_dh_dᵀ" was never needed — the pigeonhole consumes the forced balance
directly, and S = (k+1)I comes from Gram algebra alone (S² = (k+1)S, PSD
remainder of trace zero), keeping the whole file spectral-theory-free.
