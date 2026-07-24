/-
# Symmetry reduction: fundamental-domain certification transfers

The σ₉-continuum engines certify `M ≥ 0` on a FUNDAMENTAL DOMAIN of the
window under the system's symmetry group (four generators, verified
symbolically upstream: two atom swaps, the pair swap, `s ↦ 1−s`) and on a
finite cell cover of that domain. The two logical steps that turn the
machine's per-cell certificates into the window statement are generic and
pure, so they live here rather than in `Certs/`:

* **cover consumption**: nonnegativity on every cell of a cover gives
  nonnegativity on the union;
* **fundamental-domain transfer**: an invariant function certified on a
  set is certified at every point some invariant move sends into the set.

Both are stated for an arbitrary family of invariant self-maps — no group
structure is needed, only invariance and coverage.
-/
import Mathlib

namespace Gtz

variable {point : Type*} {cellIndex : Type*}

/-- **Cover consumption**: `margin ≥ 0` on every cell of a cover of the
window gives `margin ≥ 0` on the window. -/
theorem nonneg_of_cell_cover (margin : point → ℝ) (window : Set point)
    (cell : cellIndex → Set point)
    (hcover : window ⊆ ⋃ index, cell index)
    (hcellCert : ∀ index, ∀ sample ∈ cell index, 0 ≤ margin sample) :
    ∀ sample ∈ window, 0 ≤ margin sample := by
  intro sample hsample
  obtain ⟨index, hmember⟩ := Set.mem_iUnion.mp (hcover hsample)
  exact hcellCert index sample hmember

/-- **Symmetry transfer**: an invariant move sending the sample into the
certified set certifies the sample. -/
theorem nonneg_of_symmetry_transfer (margin : point → ℝ)
    (move : point → point)
    (hinvariant : ∀ sample, margin (move sample) = margin sample)
    (certified : Set point)
    (hcert : ∀ sample ∈ certified, 0 ≤ margin sample)
    (sample : point) (hmoved : move sample ∈ certified) :
    0 ≤ margin sample := by
  have hmovedValue := hcert (move sample) hmoved
  rwa [hinvariant sample] at hmovedValue

/-- **Fundamental-domain reduction**: a family of margin-invariant moves
whose orbit meets the fundamental domain at every point transfers a
domain certificate to the whole space. -/
theorem nonneg_of_fundamental_domain (margin : point → ℝ)
    {moveIndex : Type*} (move : moveIndex → point → point)
    (hinvariant : ∀ index sample, margin (move index sample) = margin sample)
    (fundamentalDomain : Set point)
    (hreaches : ∀ sample, ∃ index, move index sample ∈ fundamentalDomain)
    (hdomainCert : ∀ sample ∈ fundamentalDomain, 0 ≤ margin sample) :
    ∀ sample, 0 ≤ margin sample := by
  intro sample
  obtain ⟨index, hmember⟩ := hreaches sample
  exact nonneg_of_symmetry_transfer margin (move index) (hinvariant index)
    fundamentalDomain hdomainCert sample hmember

/-- **The engine's consumption statement**: window points reach the
fundamental domain by invariant moves; the domain is covered by cells;
every cell is certified — the window is certified. Exactly the shape the
σ₉ cell trees deliver. -/
theorem nonneg_on_window_of_symmetric_cells (margin : point → ℝ)
    (window : Set point)
    {moveIndex : Type*} (move : moveIndex → point → point)
    (hinvariant : ∀ index sample, margin (move index sample) = margin sample)
    (fundamentalDomain : Set point)
    (hreaches : ∀ sample ∈ window, ∃ index,
      move index sample ∈ fundamentalDomain)
    (cell : cellIndex → Set point)
    (hcover : fundamentalDomain ⊆ ⋃ index, cell index)
    (hcellCert : ∀ index, ∀ sample ∈ cell index, 0 ≤ margin sample) :
    ∀ sample ∈ window, 0 ≤ margin sample := by
  intro sample hsample
  obtain ⟨index, hmember⟩ := hreaches sample hsample
  exact nonneg_of_symmetry_transfer margin (move index) (hinvariant index)
    fundamentalDomain
    (nonneg_of_cell_cover margin fundamentalDomain cell hcover hcellCert)
    sample hmember

end Gtz
