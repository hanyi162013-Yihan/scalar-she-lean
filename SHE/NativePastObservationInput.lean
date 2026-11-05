module

public import SHE.NativePastBracket

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section

namespace SHE.NativePastObservationInput
open Set MeasureTheory PredictableL2 StoppedFourier FiniteHaar PastItoInputs
open scoped NNReal ENNReal
local instance nativePastObservationInput_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable {ell M : ℝ} (hell : 0<ell) (hM : 0≤M)
variable (f : ℝ≥0×Ω→EllipticField ell M) (hf : StronglyMeasurable[𝓕.predictable] f)

/-- A genuine post-v native observation input in the original full-H
predictable L2 space. The target T can lie below H, provided T>q. -/
def input (v q : ℝ≥0) {T : ℝ} (hT : (q:ℝ)<T) (x : HeatCircle) : Process (E := RealHaarInput) 𝓕 μ H :=
  post 𝓕 μ H v (NativeObservationProcess.process 𝓕 μ H hell hM f hf hT x)

theorem input_ae (v q : ℝ≥0) {T : ℝ} (hT : (q:ℝ)<T) (x : HeatCircle) :
    input 𝓕 μ H hell hM f hf v q hT x =ᵐ[energyMeasure μ H]
      (fun p => if v<p.1 then NativeObservationProcess.integrand hell f T (q:ℝ) x p else 0) := by
  filter_upwards [post_ae 𝓕 μ H v (NativeObservationProcess.process 𝓕 μ H hell hM f hf hT x),
    NativeObservationProcess.process_ae 𝓕 μ H hell hM f hf hT x] with p hp hr
  change post 𝓕 μ H v (NativeObservationProcess.process 𝓕 μ H hell hM f hf hT x) p=_
  rw [hp]
  by_cases h : v<p.1 <;> simp only [h,ite_true,ite_false,hr]

/-- Actual sharp local-window bracket, including arbitrary dependent
predictable coefficient fields and the original full-H noise. -/
theorem bracket_bound (v q : ℝ≥0) (hvq : v≤q) (hqH : q≤H)
    (hspan : (q:ℝ)-(v:ℝ)≤1) {T : ℝ} (hT : (q:ℝ)<T) (x : HeatCircle) :
    ∀ᵐ ω ∂μ,bracket (input 𝓕 μ H hell hM f hf v q hT x) ω≤
      ENNReal.ofReal (ProfileVariance.upperConstant*M*((q:ℝ)-(v:ℝ))^(1/2:ℝ)) :=
  NativePastBracket.bracket_bound_of_ae 𝓕 μ H v q hvq hqH hspan hell hM f hf hT x
    (input 𝓕 μ H hell hM f hf v q hT x) (input_ae 𝓕 μ H hell hM f hf v q hT x)

end SHE.NativePastObservationInput
