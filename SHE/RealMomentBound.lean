module

public import SHE.FractionalMoment

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SHE.RealMomentBound
open Set MeasureTheory

/-- A finite stochastic moment bound supplies both the actual Bochner
integrability and the real integral bound used in Gaussian word Hölder. -/
theorem integral_bound {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (F : Ω → ℝ) (hF : AEStronglyMeasurable F μ) (hpos : ∀ ω, 0 ≤ F ω)
    {K : ℝ} (hK : 0 ≤ K)
    (hb : (∫⁻ ω,ENNReal.ofReal (F ω) ∂μ) ≤ ENNReal.ofReal K) :
    Integrable F μ ∧ (∫ ω,F ω ∂μ) ≤ K := by
  have hfi : HasFiniteIntegral F μ :=
    (hasFiniteIntegral_iff_ofReal (ae_of_all _ hpos)).mpr (hb.trans_lt ENNReal.ofReal_lt_top)
  have hi : Integrable F μ := ⟨hF,hfi⟩
  refine ⟨hi,?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ hpos)] at hb
  exact (ENNReal.ofReal_le_ofReal_iff hK).mp hb

end SHE.RealMomentBound
