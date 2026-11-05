module

public import SHE.ProcessEnergy

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SHE.LpEnergy
open MeasureTheory PredictableL2

variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {μ : Measure Ω}

theorem lintegral_energy (v : Lp E 2 μ) :
    ENNReal.ofReal (‖v‖^2)=∫⁻ ω,ENNReal.ofReal (‖v ω‖^2) ∂μ := by
  rw [realLp_norm_sq,ofReal_integral_eq_lintegral_ofReal (Lp.memLp v).norm.integrable_sq
    (Filter.Eventually.of_forall (fun _ => sq_nonneg _))]

theorem difference_energy (v w : Lp E 2 μ) :
    ENNReal.ofReal (‖v-w‖^2)=∫⁻ ω,ENNReal.ofReal (‖v ω-w ω‖^2) ∂μ := by
  rw [lintegral_energy]
  apply lintegral_congr_ae
  filter_upwards [Lp.coeFn_sub v w] with ω hω
  rw [hω]
  rfl

end SHE.LpEnergy
