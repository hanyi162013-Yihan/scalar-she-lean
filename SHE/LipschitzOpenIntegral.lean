module

public import SHE.LipschitzIntegralIdentity

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SHE.LipschitzIntegralIdentity
open Set MeasureTheory
open scoped NNReal

/-- A derivative is needed only on the open integration interval.
Endpoint integrability is derived from the actual Lipschitz curve. -/
theorem integral_eq_sub_on_open {f g : ℝ → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    {a b : ℝ} (hab : a ≤ b) (hd : ∀ θ ∈ Ioo a b, HasDerivAt f (g θ) θ) :
    IntervalIntegrable g volume a b ∧ (∫ θ in a..b, g θ) = f b - f a := by
  have hac := hf.lipschitzOnWith.absolutelyContinuousOnInterval (a := a) (b := b)
  have he : deriv f =ᵐ[volume.restrict (Ioo a b)] g := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with θ hθ
    exact (hd θ hθ).deriv
  have he' : deriv f =ᵐ[volume.restrict (Ioc a b)] g := by
    rw [← Measure.restrict_congr_set (Ioo_ae_eq_Ioc : Ioo a b =ᵐ[volume] Ioc a b)]
    exact he
  have hu : deriv f =ᵐ[volume.restrict (uIoc a b)] g := by
    simpa only [uIoc_of_le hab] using he'
  refine ⟨hac.intervalIntegrable_deriv.congr_ae hu, ?_⟩
  rw [← hac.integral_deriv_eq_sub]
  exact intervalIntegral.integral_congr_ae_restrict hu.symm

end SHE.LipschitzIntegralIdentity
