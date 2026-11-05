module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SHE.LipschitzIntegralIdentity
open MeasureTheory
open scoped NNReal

/-- The actual a.e. derivative integrates to the endpoint difference of
a Lipschitz curve. The marked integrand is genuinely interval integrable. -/
theorem integral_eq_sub {f g : ℝ → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    (hd : ∀ᵐ θ ∂volume, HasDerivAt f (g θ) θ) (a b : ℝ) :
    IntervalIntegrable g volume a b ∧ (∫ θ in a..b, g θ) = f b - f a := by
  have hac := hf.lipschitzOnWith.absolutelyContinuousOnInterval (a := a) (b := b)
  have he : deriv f =ᵐ[volume] g := hd.mono (fun θ hθ => hθ.deriv)
  refine ⟨hac.intervalIntegrable_deriv.congr_ae (ae_restrict_of_ae he), ?_⟩
  rw [← hac.integral_deriv_eq_sub]
  exact intervalIntegral.integral_congr_ae (he.symm.mono (fun _ hx _ => hx))

end SHE.LipschitzIntegralIdentity
