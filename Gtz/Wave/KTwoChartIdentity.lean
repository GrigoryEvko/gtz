/-
# The chart identity of the two-zero stratum at `(5,3)`

The `(5,3)` two-zero stratum reduces to an eight-scalar chart.  Parseval
forces the two outside plane parts onto one line, the plane pair is the
explicit rotation chart, and the four avoiding refusals become four
polynomial slacks:

* `k2ChartCapD`, `k2ChartCapE` — the two excess caps of the silenced pair
  (the determinant laws of `Gtz.KTwoCrossPrice` in chart coordinates);
* `k2ChartRefusalY`, `k2ChartRefusalZ` — the two mixed refusals, linear in
  the plane angle variable `X`.

This module holds THE MASTER IDENTITY [derived and verified symbolically,
`scratchpad/corank1/f26sym/`]: with the negative-on-simplex multipliers
`te(te−1), (td−1), tz(tz−1), (td+te+tz)(td+te+tz−1)`, the four slacks
combine EXACTLY into

  `(excess residual)·QE + (G − 1)·Q1` ,

with `G = td·α² + te·β²` the outside `w`-mass, so `G − 1 = −t_x`.  At a tie
the four slacks are nonnegative, the excess residual vanishes, and the left
side is nonpositive.  The identity therefore makes BOTH quotients
nonnegative at every chart tie, with no case analysis: `t_x·Q1` EQUALS the
positive combination of the four slacks (`k2Chart_quotient_nonneg`), and the
mirror twin holds by the exact symmetry `S3 ↔ S4`, `X ↔ 1 − X`.  The
quotient conditions are the identity's real content: `Q1` carries no `ty`
and the mirror carries no `tz`, so the two mixed refusals are traded for two
variable-separated necessary conditions.  The whole chart kill is then ONE
named corner, `Gtz.K2ChartDoubleQuotientCorner`: the four slacks and the two
quotients together on the structured legal domain [MEASURED empty: the two
caps alone already fail there, 0 of 20881 corner samples].  The sign-case
consumers `caseA/caseB` stay as documentation of the identity's mechanism;
their cases are empty at ties.
-/
import Gtz.Wave.KTwoCrossPrice

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

/-! ## 1. The chart slacks -/

/-- The excess cap of the first outside atom, cleared: `te(1+ee)·(P·V − ed·D)`
in the reduced chart.  Nonnegative exactly at the refusal of `{y,z,d}`. -/
def k2ChartCapD (ed ee P td te ty tz X : ℝ) : ℝ :=
  -(P*X*ed^2*td^2*ty) + P*X*ed^2*td^2*tz - P*X*ed*ee*td*te*ty
    + P*X*ed*ee*td*te*tz - P*X*ed*td^2*ty + P*X*ed*td^2*tz - P*X*ed*td*te*ty
    + P*X*ed*td*te*tz - P*ed^2*td^2*tz - P*ed*ee*td*te*tz - P*X*ee*te*ty
    + P*X*ee*te*tz + P*ed^2*td^2 + P*ed*ee*td*te - P*ed*td^2*tz
    - P*ed*td*te*tz - P*ee*te*ty*tz - ed*ee*te*ty*tz - P*X*te*ty
    + P*X*te*tz + P*ed*td^2 + P*ed*td*te + P*ee*te*ty - P*te*ty*tz
    + ed*ee*te*ty + ed*ee*te*tz - ed*te*ty*tz + P*te*ty - ed*ee*te
    + ed*te*ty + ed*te*tz - ed*te

/-- The excess cap of the second outside atom, cleared by `te²(1+ee)`.
Nonnegative exactly at the refusal of `{y,z,e}`. -/
def k2ChartCapE (ed ee P td te ty tz X : ℝ) : ℝ :=
  -(P*X*ed*ee*td^2*te*ty) + P*X*ed*ee*td^2*te*tz - P*X*ee^2*td*te^2*ty
    + P*X*ee^2*td*te^2*tz - P*X*ee*td^2*te*ty + P*X*ee*td^2*te*tz
    - P*X*ee*td*te^2*ty + P*X*ee*td*te^2*tz - P*ed*ee*td^2*te*tz
    - P*ee^2*td*te^2*tz - P*X*ed*td^2*ty + P*X*ed*td^2*tz
    + P*ed*ee*td^2*te - P*ed*td^2*ty*tz + P*ee^2*td*te^2 - P*ee*td^2*te*tz
    - P*ee*td*te^2*tz - ee^2*te^2*ty*tz - P*X*td^2*ty + P*X*td^2*tz
    + P*ed*td^2*ty + P*ee*td^2*te + P*ee*td*te^2 - P*td^2*ty*tz
    + ee^2*te^2*ty + ee^2*te^2*tz - ee*te^2*ty*tz + P*td^2*ty - ee^2*te^2
    + ee*te^2*ty + ee*te^2*tz - ee*te^2

/-- The mixed-refusal slack that keeps the plane atom `y`, cleared:
`−ty·te²(1+ee)·det(S_{y,d,e} − 1)`.  Nonnegative exactly at the refusal.
The slack carries no `tz`. -/
def k2ChartRefusalY (ed ee P td te ty _tz X : ℝ) : ℝ :=
  P*X*ed^2*td^2*te + P*X*ed*ee*td^2*te + P*X*ed*ee*td*te^2
    + P*X*ee^2*td*te^2 - P*X*ed^2*td^2 - 2*P*X*ed*ee*td*te
    + 2*P*X*ed*td^2*te + P*X*ed*td*te^2 - P*X*ee^2*te^2 + P*X*ee*td^2*te
    + 2*P*X*ee*td*te^2 - P*ed^2*td^2*te + P*ed^2*td^2*ty - P*ed*ee*td^2*te
    - P*ed*ee*td*te^2 + 2*P*ed*ee*td*te*ty - P*ee^2*td*te^2 + P*ee^2*te^2*ty
    - P*X*ed*td^2 - 2*P*X*ed*td*te - 2*P*X*ee*td*te - P*X*ee*te^2
    + P*X*td^2*te + P*X*td*te^2 - 2*P*ed*td^2*te + P*ed*td^2*ty
    - P*ed*td*te^2 + 2*P*ed*td*te*ty - P*ee*td^2*te - 2*P*ee*td*te^2
    + 2*P*ee*td*te*ty + P*ee*te^2*ty - ed*ee*te^2*ty - ee^2*te^2*ty
    - 2*P*X*td*te - P*td^2*te - P*td*te^2 + 2*P*td*te*ty + ed*ee*te^2
    - ed*te^2*ty + ee^2*te^2 - 2*ee*te^2*ty + ed*te^2 + 2*ee*te^2
    - te^2*ty + te^2

/-- The mixed-refusal slack that keeps the plane atom `z`.  The slack
carries no `ty`. -/
def k2ChartRefusalZ (ed ee P td te _ty tz X : ℝ) : ℝ :=
  -(P*X*ed^2*td^2*te) - P*X*ed*ee*td^2*te - P*X*ed*ee*td*te^2
    - P*X*ee^2*td*te^2 + P*X*ed^2*td^2 + 2*P*X*ed*ee*td*te
    - 2*P*X*ed*td^2*te - P*X*ed*td*te^2 + P*X*ee^2*te^2 - P*X*ee*td^2*te
    - 2*P*X*ee*td*te^2 + P*ed^2*td^2*tz + 2*P*ed*ee*td*te*tz
    + P*ee^2*te^2*tz + P*X*ed*td^2 + 2*P*X*ed*td*te + 2*P*X*ee*td*te
    + P*X*ee*te^2 - P*X*td^2*te - P*X*td*te^2 - P*ed^2*td^2
    - 2*P*ed*ee*td*te + P*ed*td^2*tz + 2*P*ed*td*te*tz - P*ee^2*te^2
    + 2*P*ee*td*te*tz + P*ee*te^2*tz - ed*ee*te^2*tz - ee^2*te^2*tz
    + 2*P*X*td*te - P*ed*td^2 - 2*P*ed*td*te - 2*P*ee*td*te - P*ee*te^2
    + 2*P*td*te*tz + ed*ee*te^2 - ed*te^2*tz + ee^2*te^2 - 2*ee*te^2*tz
    - 2*P*td*te + ed*te^2 + 2*ee*te^2 - te^2*tz + te^2

/-- The quotient of the master identity against the outside `w`-mass gap.
Free of `ty`. -/
def k2ChartQuotient (ed ee P td te tz X : ℝ) : ℝ :=
  -(P*X*ed^2*td^2*te^2) - P*X*ed*ee*td^3*te - P*X*ed*ee*td*te^3
    - P*X*ee^2*td^2*te^2 + P*X*ed^2*td^2*te + P*X*ed*ee*td^2*te
    + P*X*ed*ee*td*te^2 - P*X*ed*td^3*te - 2*P*X*ed*td^2*te^2
    - 2*P*X*ed*td^2*te*tz - P*X*ed*td*te^3 + P*X*ee^2*td*te^2
    - P*X*ee*td^3*te - 2*P*X*ee*td^2*te^2 - P*X*ee*td*te^3
    - 2*P*X*ee*td*te^2*tz + P*ed^2*td^2*tz^2 + 2*P*ed*ee*td*te*tz^2
    + P*ee^2*te^2*tz^2 + 3*P*X*ed*td^2*te + 2*P*X*ed*td^2*tz
    + P*X*ed*td*te^2 + P*X*ee*td^2*te + 3*P*X*ee*td*te^2 + 2*P*X*ee*te^2*tz
    - P*X*td^3*te - 2*P*X*td^2*te^2 - 2*P*X*td^2*te*tz - P*X*td*te^3
    - 2*P*X*td*te^2*tz - P*ed^2*td^2*tz - 2*P*ed*ee*td*te*tz
    + 2*P*ed*td^2*te*tz + 2*P*ed*td^2*tz^2 + 2*P*ed*td*te*tz^2
    - P*ee^2*te^2*tz + 2*P*ee*td*te^2*tz + 2*P*ee*td*te*tz^2
    + 2*P*ee*te^2*tz^2 - ed*ee*te^3*tz - ed*ee*te^2*tz^2 - ee^2*td*te^2*tz
    - ee^2*te^2*tz^2 + 2*P*X*td^2*te + 2*P*X*td^2*tz + 2*P*X*td*te^2
    + 2*P*X*te^2*tz - 2*P*ed*td^2*te - 2*P*ed*td^2*tz - 2*P*ed*td*te*tz
    - 2*P*ee*td*te^2 - 2*P*ee*td*te*tz - 2*P*ee*te^2*tz + 2*P*td^2*te*tz
    + P*td^2*tz^2 + 2*P*td*te^2*tz + 2*P*td*te*tz^2 + P*te^2*tz^2
    + ed*ee*te^3 + 2*ed*ee*te^2*tz - ed*te^3*tz - ed*te^2*tz^2
    + ee^2*td*te^2 + 2*ee^2*te^2*tz - 2*ee*td*te^2*tz - ee*te^3*tz
    - 3*ee*te^2*tz^2 - 2*P*td^2*te - P*td^2*tz - 2*P*td*te^2 - 2*P*td*te*tz
    - P*te^2*tz - ed*ee*te^2 + ed*te^3 + 2*ed*te^2*tz - ee^2*te^2
    + 2*ee*td*te^2 + ee*te^3 + 4*ee*te^2*tz - td*te^2*tz - te^3*tz
    - 2*te^2*tz^2 - ed*te^2 - ee*te^2 + td*te^2 + te^3 + 2*te^2*tz

/-- The quotient of the master identity against the excess residual.
Free of `ty`. -/
def k2ChartExcessQuotient (ed ee P td te tz X : ℝ) : ℝ :=
  P*X*ed^2*td^2*te^2 + P*X*ed*ee*td^3*te + P*X*ed*ee*td*te^3
    + P*X*ee^2*td^2*te^2 - P*X*ed^2*td^2*te - P*X*ed*ee*td^2*te
    - P*X*ed*ee*td*te^2 + P*X*ed*td^2*te^2 + P*X*ed*td*te^3
    - P*X*ee^2*td*te^2 + P*X*ee*td^3*te + P*X*ee*td^2*te^2
    - P*ed^2*td^2*tz^2 - 2*P*ed*ee*td*te*tz^2 - P*ee^2*te^2*tz^2
    + P*X*ed*td^3 - P*X*ed*td^2*te - P*X*ed*td*te^2 - P*X*ee*td^2*te
    - P*X*ee*td*te^2 + P*X*ee*te^3 + P*ed^2*td^2*tz + 2*P*ed*ee*td*te*tz
    + P*ed*td^3*tz - P*ed*td^2*tz^2 - 2*P*ed*td*te*tz^2 + P*ee^2*te^2*tz
    - 2*P*ee*td*te*tz^2 + P*ee*te^3*tz - P*ee*te^2*tz^2 + ed*ee*te^3*tz
    + ed*ee*te^2*tz^2 + ee^2*td*te^2*tz + ee^2*te^2*tz^2 - P*X*ed*td^2
    - P*X*ee*te^2 + P*X*td^3 + P*X*te^3 - P*ed*td^3 + 2*P*ed*td*te*tz
    + 2*P*ee*td*te*tz - P*ee*te^3 + P*td^3*tz - 2*P*td*te*tz^2 + P*te^3*tz
    - ed*ee*te^3 - 2*ed*ee*te^2*tz + ed*te^3*tz + ed*te^2*tz^2
    - ee^2*td*te^2 - 2*ee^2*te^2*tz + ee*td*te^2*tz + 2*ee*te^2*tz^2
    - P*X*td^2 - P*X*te^2 + P*ed*td^2 + P*ee*te^2 - P*td^3 - P*td^2*tz
    + 2*P*td*te*tz - P*te^3 - P*te^2*tz + ed*ee*te^2 - ed*te^3
    - 2*ed*te^2*tz + ee^2*te^2 - ee*td*te^2 - 3*ee*te^2*tz + te^2*tz^2
    + P*td^2 + P*te^2 + ed*te^2 + ee*te^2 - te^2*tz

/-! ## 2. The master identity -/

/-- **THE MASTER IDENTITY OF THE `(5,3)` TWO-ZERO CHART.**  The four refusal
slacks, weighted by the four negative-on-simplex multipliers, collapse onto
the excess residual and the outside `w`-mass gap.  One `ring` step. -/
theorem k2Chart_master_identity (ed ee P td te ty tz X : ℝ) :
    te*(te-1) * k2ChartCapD ed ee P td te ty tz X
      + (td-1) * k2ChartCapE ed ee P td te ty tz X
      + tz*(tz-1) * k2ChartRefusalY ed ee P td te ty tz X
      + (td+te+tz)*(td+te+tz-1) * k2ChartRefusalZ ed ee P td te ty tz X
    = (td*ed + te*ee - ty - tz) * k2ChartExcessQuotient ed ee P td te tz X
      + (td*(1+ed) + te*(1+ee) - 1) * k2ChartQuotient ed ee P td te tz X := by
  unfold k2ChartCapD k2ChartCapE k2ChartRefusalY k2ChartRefusalZ
    k2ChartQuotient k2ChartExcessQuotient
  ring

/-! ## 3. The mirror symmetry -/

/-- The first cap is invariant under the plane swap. -/
theorem k2ChartCapD_swap (ed ee P td te ty tz X : ℝ) :
    k2ChartCapD ed ee P td te tz ty (1-X) = k2ChartCapD ed ee P td te ty tz X := by
  unfold k2ChartCapD; ring

/-- The second cap is invariant under the plane swap. -/
theorem k2ChartCapE_swap (ed ee P td te ty tz X : ℝ) :
    k2ChartCapE ed ee P td te tz ty (1-X) = k2ChartCapE ed ee P td te ty tz X := by
  unfold k2ChartCapE; ring

/-- The plane swap interchanges the two mixed-refusal slacks. -/
theorem k2ChartRefusalY_swap (ed ee P td te ty tz X : ℝ) :
    k2ChartRefusalY ed ee P td te tz ty (1-X)
      = k2ChartRefusalZ ed ee P td te ty tz X := by
  unfold k2ChartRefusalY k2ChartRefusalZ; ring

/-- The plane swap interchanges the two mixed-refusal slacks, other side. -/
theorem k2ChartRefusalZ_swap (ed ee P td te ty tz X : ℝ) :
    k2ChartRefusalZ ed ee P td te tz ty (1-X)
      = k2ChartRefusalY ed ee P td te ty tz X := by
  unfold k2ChartRefusalY k2ChartRefusalZ; ring

/-! ## 4. The two quotient-sign kills -/

/-- **A negative quotient forbids the chart tie.**  The four slack floors and
the excess identity force `(G−1)·Q1 ≥ 0` through the master identity, and a
negative quotient then pushes the outside `w`-mass to one or more — the
design loses its `x` weight. -/
theorem k2Chart_caseA_kill {ed ee P td te ty tz X : ℝ}
    (hty : 0 < ty) (htz : 0 < tz) (htd : 0 < td) (hte : 0 < te)
    (hsum : td + te + ty + tz < 1)
    (hE : td*ed + te*ee = ty + tz)
    (hS1 : 0 ≤ k2ChartCapD ed ee P td te ty tz X)
    (hS2 : 0 ≤ k2ChartCapE ed ee P td te ty tz X)
    (hS3 : 0 ≤ k2ChartRefusalY ed ee P td te ty tz X)
    (hS4 : 0 ≤ k2ChartRefusalZ ed ee P td te ty tz X)
    (hQ : k2ChartQuotient ed ee P td te tz X < 0) : False := by
  have hid := k2Chart_master_identity ed ee P td te ty tz X
  have hEzero : td*ed + te*ee - ty - tz = 0 := by linarith
  have hG : td*(1+ed) + te*(1+ee) - 1 < 0 := by nlinarith [hE, hsum]
  have h1 : te*(te-1) * k2ChartCapD ed ee P td te ty tz X ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by nlinarith) hS1
  have h2 : (td-1) * k2ChartCapE ed ee P td te ty tz X ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by nlinarith) hS2
  have h3 : tz*(tz-1) * k2ChartRefusalY ed ee P td te ty tz X ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by nlinarith) hS3
  have h4 : (td+te+tz)*(td+te+tz-1) * k2ChartRefusalZ ed ee P td te ty tz X ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)) hS4
  have hpos : 0 < (td*(1+ed) + te*(1+ee) - 1)
      * k2ChartQuotient ed ee P td te tz X := mul_pos_of_neg_of_neg hG hQ
  rw [hEzero, zero_mul, zero_add] at hid
  linarith [h1, h2, h3, h4, hpos, hid]

/-- **A negative mirror quotient forbids the chart tie.**  The plane swap
carries the four floors across, and the first kill fires at the swapped
chart point. -/
theorem k2Chart_caseB_kill {ed ee P td te ty tz X : ℝ}
    (hty : 0 < ty) (htz : 0 < tz) (htd : 0 < td) (hte : 0 < te)
    (hsum : td + te + ty + tz < 1)
    (hE : td*ed + te*ee = ty + tz)
    (hS1 : 0 ≤ k2ChartCapD ed ee P td te ty tz X)
    (hS2 : 0 ≤ k2ChartCapE ed ee P td te ty tz X)
    (hS3 : 0 ≤ k2ChartRefusalY ed ee P td te ty tz X)
    (hS4 : 0 ≤ k2ChartRefusalZ ed ee P td te ty tz X)
    (hQm : k2ChartQuotient ed ee P td te ty (1-X) < 0) : False := by
  refine k2Chart_caseA_kill htz hty htd hte (by linarith) (by linarith)
    (X := 1-X) ?_ ?_ ?_ ?_ hQm
  · rw [k2ChartCapD_swap]; exact hS1
  · rw [k2ChartCapE_swap]; exact hS2
  · rw [k2ChartRefusalY_swap]; exact hS4
  · rw [k2ChartRefusalZ_swap]; exact hS3

/-- **The quotient is nonnegative at every chart tie, free.**  The four
slack floors make the identity's left side nonpositive, the excess residual
vanishes, and the erased weight is positive.  No case analysis: the tie
PAYS `t_x·Q1` with the four slacks. -/
theorem k2Chart_quotient_nonneg {ed ee P td te ty tz X : ℝ}
    (hty : 0 < ty) (htz : 0 < tz) (htd : 0 < td) (hte : 0 < te)
    (hsum : td + te + ty + tz < 1)
    (hE : td*ed + te*ee = ty + tz)
    (hS1 : 0 ≤ k2ChartCapD ed ee P td te ty tz X)
    (hS2 : 0 ≤ k2ChartCapE ed ee P td te ty tz X)
    (hS3 : 0 ≤ k2ChartRefusalY ed ee P td te ty tz X)
    (hS4 : 0 ≤ k2ChartRefusalZ ed ee P td te ty tz X) :
    0 ≤ k2ChartQuotient ed ee P td te tz X := by
  by_contra hcon
  push Not at hcon
  exact k2Chart_caseA_kill hty htz htd hte hsum hE hS1 hS2 hS3 hS4 hcon

/-- The mirror quotient is nonnegative at every chart tie, free. -/
theorem k2Chart_quotient_mirror_nonneg {ed ee P td te ty tz X : ℝ}
    (hty : 0 < ty) (htz : 0 < tz) (htd : 0 < td) (hte : 0 < te)
    (hsum : td + te + ty + tz < 1)
    (hE : td*ed + te*ee = ty + tz)
    (hS1 : 0 ≤ k2ChartCapD ed ee P td te ty tz X)
    (hS2 : 0 ≤ k2ChartCapE ed ee P td te ty tz X)
    (hS3 : 0 ≤ k2ChartRefusalY ed ee P td te ty tz X)
    (hS4 : 0 ≤ k2ChartRefusalZ ed ee P td te ty tz X) :
    0 ≤ k2ChartQuotient ed ee P td te ty (1-X) := by
  by_contra hcon
  push Not at hcon
  exact k2Chart_caseB_kill hty htz htd hte hsum hE hS1 hS2 hS3 hS4 hcon

/-! ## 5. The residual corner -/

/-- **THE DOUBLE-QUOTIENT CORNER.**  The single unresolved case of the
`(5,3)` two-zero chart kill: both quotients nonnegative, the two excess caps
nonnegative, on the structured legal domain.  [MEASURED empty with the two
caps failing jointly: 0 of 20881 corner samples,
`scratchpad/corank1/f26sym/step21.py`.] -/
def K2ChartDoubleQuotientCorner : Prop :=
  ∀ ed ee P td te ty tz X : ℝ,
    0 < ty → 0 < tz → 0 < td → 0 < te → 0 < P →
    0 ≤ X → X ≤ 1 → (-1 : ℝ) < ed → (-1 : ℝ) < ee →
    td*ed + te*ee = ty + tz →
    td + te + ty + tz < 1 →
    0 < X*tz + (1-X)*ty - ty*tz →
    0 < (te*(1+ee) - P*td*(td*(1+ed) + te*(1+ee)))*((1-X)*tz + X*ty)
        - te*(1+ee)*ty*tz →
    0 < te*(1+ee)*((1-ty)*(1-tz))
        - P*td*(td*(1+ed) + te*(1+ee))*((1-X)*(1-tz) + X*(1-ty)) →
    0 < te*(1+ee) - P*td*(td*(1+ed) + te*(1+ee)) →
    0 ≤ k2ChartCapD ed ee P td te ty tz X →
    0 ≤ k2ChartCapE ed ee P td te ty tz X →
    0 ≤ k2ChartRefusalY ed ee P td te ty tz X →
    0 ≤ k2ChartRefusalZ ed ee P td te ty tz X →
    0 ≤ k2ChartQuotient ed ee P td te tz X →
    0 ≤ k2ChartQuotient ed ee P td te ty (1-X) →
    False

/-- **THE CHART KILL, conditional on the corner.**  The four refusal floors
of a `(5,3)` two-zero chart tie are impossible: the master identity supplies
the two quotient floors for free, and the corner eats the whole system. -/
theorem k2Chart_kill_of_doubleQuotientCorner
    (hcorner : K2ChartDoubleQuotientCorner)
    {ed ee P td te ty tz X : ℝ}
    (hty : 0 < ty) (htz : 0 < tz) (htd : 0 < td) (hte : 0 < te) (hP : 0 < P)
    (hX0 : 0 ≤ X) (hX1 : X ≤ 1) (hed : (-1 : ℝ) < ed) (hee : (-1 : ℝ) < ee)
    (hE : td*ed + te*ee = ty + tz)
    (hsum : td + te + ty + tz < 1)
    (hV : 0 < X*tz + (1-X)*ty - ty*tz)
    (hU : 0 < (te*(1+ee) - P*td*(td*(1+ed) + te*(1+ee)))*((1-X)*tz + X*ty)
        - te*(1+ee)*ty*tz)
    (hD : 0 < te*(1+ee)*((1-ty)*(1-tz))
        - P*td*(td*(1+ed) + te*(1+ee))*((1-X)*(1-tz) + X*(1-ty)))
    (hW : 0 < te*(1+ee) - P*td*(td*(1+ed) + te*(1+ee)))
    (hS1 : 0 ≤ k2ChartCapD ed ee P td te ty tz X)
    (hS2 : 0 ≤ k2ChartCapE ed ee P td te ty tz X)
    (hS3 : 0 ≤ k2ChartRefusalY ed ee P td te ty tz X)
    (hS4 : 0 ≤ k2ChartRefusalZ ed ee P td te ty tz X) : False :=
  hcorner ed ee P td te ty tz X hty htz htd hte hP hX0 hX1 hed hee
    hE hsum hV hU hD hW hS1 hS2 hS3 hS4
    (k2Chart_quotient_nonneg hty htz htd hte hsum hE hS1 hS2 hS3 hS4)
    (k2Chart_quotient_mirror_nonneg hty htz htd hte hsum hE hS1 hS2 hS3 hS4)

end Gtz
