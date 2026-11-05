module
public import SHE.BoundedRowStepFreezing
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
namespace SHE.BoundedRowStepInputs
open MeasureTheory Set PredictableL2 Filter
open scoped NNReal ENNReal Topology
variable {Ω E C : Type*} [MeasurableSpace Ω]
variable [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable [NormedAddCommGroup C] [InnerProductSpace ℝ C]
variable [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
variable (H q : ℝ≥0) (R : Iic q×E→C) (hR : Continuous R)
variable (U : ℝ≥0→Ω→E) (hUa : StronglyAdapted 𝓕 U)
variable (M : ℝ) (hb : ∀p,‖R p‖≤M)

/-- Genuine predictable input convergence follows from the actual raw
energy estimate, rather than being supplied as a stochastic premise. -/
theorem input_tendsto (hU : Measurable (Function.uncurry U))
    (hc : ∀ω,Continuous (fun s=>U s ω)) (hM : 0≤M)
    (f : Process (E:=C) 𝓕 μ H)
    (hf : f=ᵐ[energyMeasure μ H] BoundedContinuousRowFreezing.target q R U) :
    Tendsto (input 𝓕 μ H q R hR U hUa M hb) atTop (𝓝 f) := by
  have he (n : ℕ) : ‖input 𝓕 μ H q R hR U hUa M hb n-f‖^2=
      ∫p,‖BoundedContinuousRowFreezing.value q R U n p-
        BoundedContinuousRowFreezing.target q R U p‖^2 ∂energyMeasure μ H := by
    rw [subsigma_norm_sq]
    apply integral_congr_ae
    filter_upwards [ae_eq_of_ae_eq_trim (Lp.coeFn_sub (input 𝓕 μ H q R hR U hUa M hb n) f),
      input_frozen_ae 𝓕 μ H q R hR U hUa M hb n,hf] with p hs hi hf
    rw [hs]
    change ‖input 𝓕 μ H q R hR U hUa M hb n p-f p‖^2=_
    rw [hi,hf]
  have hsquare : Tendsto (fun n=>‖input 𝓕 μ H q R hR U hUa M hb n-f‖^2) atTop (𝓝 (0:ℝ)) := by
    simp_rw [he]
    exact BoundedContinuousRowFreezing.energy_tendsto q R U μ H hR hU hc M hM hb
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa only [Real.sqrt_sq (norm_nonneg _),Real.sqrt_zero] using hsquare.sqrt
end SHE.BoundedRowStepInputs
