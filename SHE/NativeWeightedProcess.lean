module
public import SHE.PredictableExponential
public import SHE.PastItoAlgebra
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace SHE.NativeWeightedProcess
open MeasureTheory PredictableL2
open scoped NNReal ENNReal
variable {Ω E : Type*} [MeasurableSpace Ω]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [SFinite μ] (H : ℝ≥0)

def energy (γ : ℝ) (d : Process (E:=E) 𝓕 μ H) : ℝ≥0∞ :=
  ∫⁻t, ∫⁻ω, ENNReal.ofReal (Real.exp (-2*γ*(t:ℝ))*‖d (t,ω)‖^2) ∂μ ∂timeMeasure H

theorem energy_eq (γ : ℝ) (d : Process (E:=E) 𝓕 μ H) :
    energy 𝓕 μ H γ d = ENNReal.ofReal (‖PredictableExponential.scale 𝓕 μ H (-γ) d‖^2) := by
  simpa only [energy, mul_neg, neg_mul] using (PredictableExponential.energy 𝓕 μ H (-γ) d).symm

theorem finite (γ : ℝ) (d : Process (E:=E) 𝓕 μ H) : energy 𝓕 μ H γ d < ∞ := by
  rw [energy_eq]
  exact ENNReal.ofReal_lt_top

theorem scale_zero (γ : ℝ) :
    PredictableExponential.scale 𝓕 μ H γ (0 : Process (E:=E) 𝓕 μ H) = 0 := by
  apply PastItoAlgebra.eq_of_ambient_ae
  filter_upwards [PredictableExponential.ae 𝓕 μ H γ (0 : Process (E:=E) 𝓕 μ H),
    ae_eq_of_ae_eq_trim (Lp.coeFn_zero (E:=E) (p:=2)
      ((energyMeasure μ H).trim (predictable_le_product 𝓕)))] with p hp hz
  rw [hp,hz]
  change PredictableExponential.weight H γ p • (0:E) = 0
  exact smul_zero _

/-- A genuine predictable L2 process with strictly contractive weighted
energy vanishes. Finiteness comes from the actual process, not a premise. -/
theorem eq_zero_of_contract (γ : ℝ) (d : Process (E:=E) 𝓕 μ H)
    {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1)
    (he : energy 𝓕 μ H γ d ≤ ENNReal.ofReal q * energy 𝓕 μ H γ d) : d = 0 := by
  rw [energy_eq, ← ENNReal.ofReal_mul hq] at he
  have hn : 0 ≤ ‖PredictableExponential.scale 𝓕 μ H (-γ) d‖^2 := sq_nonneg _
  have hb : ‖PredictableExponential.scale 𝓕 μ H (-γ) d‖^2 ≤
      q*‖PredictableExponential.scale 𝓕 μ H (-γ) d‖^2 :=
    (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hq hn)).mp he
  have hzsq : ‖PredictableExponential.scale 𝓕 μ H (-γ) d‖^2 = 0 := by
    by_contra hne
    have hp : 0 < ‖PredictableExponential.scale 𝓕 μ H (-γ) d‖^2 := lt_of_le_of_ne hn (Ne.symm hne)
    have hm := mul_pos (sub_pos.mpr hq1) hp
    nlinarith only [hb,hm]
  have hz : ‖PredictableExponential.scale 𝓕 μ H (-γ) d‖ = 0 := sq_eq_zero_iff.mp hzsq
  have hs : PredictableExponential.scale 𝓕 μ H (-γ) d = 0 := norm_eq_zero.mp hz
  rw [← PredictableExponential.cancel' 𝓕 μ H γ d, hs, scale_zero]
end SHE.NativeWeightedProcess
