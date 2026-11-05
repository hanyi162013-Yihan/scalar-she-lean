module

public import SHE.SmoothApproximation
public import Mathlib.Topology.MetricSpace.Holder

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.BoundedScalarData
open scoped NNReal

/-- Reuse the manuscript's scalar-data interface with the original
signed coefficient and its unchanged Hölder exponent. -/
def data {g : ℝ → ℝ} {C β : ℝ≥0} (hg : HolderWith C β g) (hβ : 0<β)
    (B : ℝ≥0) (hb : ∀ z, ‖g z‖≤B) (ell : ℝ) (hell : 0<ell)
    (hel : ∀ z, ell≤(g z)^2) : SHE.SmoothApproximation.ScalarData where
  coefficient := g
  lower := Real.sqrt ell
  upper := B
  holder := C
  exponent := β
  lower_pos := Real.sqrt_pos.mpr hell
  holder_nonneg := C.coe_nonneg
  exponent_pos := hβ
  bounds z := by
    constructor
    · have hs := Real.sq_sqrt hell.le
      have h0 := Real.sqrt_nonneg ell
      have hz := abs_nonneg (g z)
      have he := sq_abs (g z)
      nlinarith [hel z]
    · simpa only [Real.norm_eq_abs] using hb z
  holder_bound x y := by
    simpa only [Real.dist_eq] using hg.dist_le x y

end SHEStochastic.BoundedScalarData
