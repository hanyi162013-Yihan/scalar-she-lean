module

public import SHE.NativePastObservationInput
public import SHE.PastTwoChannelAlgebra
public import SHE.PredictableBracketAdd
public import SHE.NativeTwoChannelMoments
public import SHE.PredictableDamping

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section

namespace SHE.NativePastHybridInput
open Set MeasureTheory ProbabilityTheory Real PredictableL2 StoppedFourier FiniteHaar
  OrthogonalItoChannels PredictableItoRotation ProfileVariance
open scoped NNReal ENNReal
local instance nativePastHybridInputInstance1 : Fact (0 < 2 * π) := ⟨by positivity⟩
local instance nativePastHybridInputInstance2 : MeasurableSpace RealHaarInput := borel _
local instance nativePastHybridInputInstance3 : BorelSpace RealHaarInput := ⟨rfl⟩
local instance nativePastHybridInputInstance4 : MeasurableSpace (Both RealHaarInput) := borel _
local instance nativePastHybridInputInstance5 : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)

variable {ell₀ M₀ ell M : ℝ} (hell₀ : 0 < ell₀) (hM₀ : 0 ≤ M₀)
variable (f₀ : ℝ≥0 × Ω → EllipticField ell₀ M₀) (hf₀ : StronglyMeasurable[𝓕.predictable] f₀)
variable (hell : 0 < ell) (hM : 0 ≤ M)
variable (fU fV : ℝ≥0 × Ω → EllipticField ell M)
variable (hfU : StronglyMeasurable[𝓕.predictable] fU) (hfV : StronglyMeasurable[𝓕.predictable] fV)
variable (v q : ℝ≥0) {T : ℝ} (hT : (q : ℝ) < T) (x : HeatCircle)
variable {Λ θ : ℝ} (hΛ : 0 ≤ Λ) (hθ : |θ| ≤ 1)

open PastItoInputs NativeHybridInput

def input : Process (E := Both RealHaarInput) 𝓕 μ H :=
  post 𝓕 μ H v (NativeHybridInput.input 𝓕 μ H hell₀ hM₀ f₀ hf₀ hell hM fU fV hfU hfV q hT x hΛ hθ)

theorem bracket_bound (hvq : v≤q) (hqH : q≤H) (hspan : (q:ℝ)-(v:ℝ)≤1) :
    ∀ᵐ ω ∂μ,PredictableL2.bracket (input 𝓕 μ H hell₀ hM₀ f₀ hf₀ hell hM fU fV hfU hfV v q hT x hΛ hθ) ω≤
        ENNReal.ofReal (upperConstant*(2*M₀+10*M)*((q:ℝ)-(v:ℝ))^(1/2 : ℝ)) := by
  let K₀ := upperConstant*M₀*((q:ℝ)-(v:ℝ))^(1/2 : ℝ)
  let K := upperConstant*M*((q:ℝ)-(v:ℝ))^(1/2 : ℝ)
  have hK₀ : 0 ≤ K₀ := mul_nonneg (mul_nonneg upperConstant_pos.le hM₀) (rpow_nonneg (sub_nonneg.mpr (show (v:ℝ)≤(q:ℝ) by exact_mod_cast hvq)) _)
  have hK : 0 ≤ K := mul_nonneg (mul_nonneg upperConstant_pos.le hM) (rpow_nonneg (sub_nonneg.mpr (show (v:ℝ)≤(q:ℝ) by exact_mod_cast hvq)) _)
  let v₀ := PastItoInputs.post 𝓕 μ H v (NativeObservationProcess.process 𝓕 μ H hell₀ hM₀ f₀ hf₀ hT x)
  let vU := PastItoInputs.post 𝓕 μ H v (NativeObservationProcess.process 𝓕 μ H hell hM fU hfU hT x)
  let vV := PastItoInputs.post 𝓕 μ H v (NativeObservationProcess.process 𝓕 μ H hell hM fV hfV hT x)
  have h₀ := NativePastObservationInput.bracket_bound 𝓕 μ H hell₀ hM₀ f₀ hf₀ v q hvq hqH hspan hT x
  have hU := NativePastObservationInput.bracket_bound 𝓕 μ H hell hM fU hfU v q hvq hqH hspan hT x
  have hV := NativePastObservationInput.bracket_bound 𝓕 μ H hell hM fV hfV v q hvq hqH hspan hT x
  have hcur := TwoChannelMomentBracket.bracket_block_bound 𝓕 μ H v₀ vU hK₀ hK h₀ hU
  have hsub := PredictableBracketDifference.bracket_sub_bound 𝓕 μ H vV vU hK hV hU
  let dv := PredictableContraction.weighted 𝓕 μ H (PredictableDamping.weight Λ q)
    (PredictableDamping.weight_predictable 𝓕 Λ q) (PredictableDamping.weight_bound hΛ q) (vV-vU)
  have hdamp := PredictableContraction.bracket_le 𝓕 μ H (PredictableDamping.weight Λ q)
    (PredictableDamping.weight_predictable 𝓕 Λ q) (PredictableDamping.weight_bound hΛ q) (vV-vU)
  let tv := PredictableContraction.weighted 𝓕 μ H (fun _ => θ) stronglyMeasurable_const (fun _ => hθ) dv
  have hθb := PredictableContraction.bracket_le 𝓕 μ H (fun _ => θ) stronglyMeasurable_const (fun _ => hθ) dv
  have hright := PredictableItoRotation.bracket_ae 𝓕 μ H
    (fun _ => right (C := RealHaarInput)) (right_measurable 𝓕) tv
  have hrightBound : ∀ᵐ ω ∂μ, (∫⁻ s, ENNReal.ofReal
      (‖rightLift 𝓕 μ H tv (s,ω)‖^2) ∂timeMeasure H) ≤ ENNReal.ofReal (4*K) := by
    filter_upwards [hsub,hdamp,hθb,hright] with ω hs hd ht hr
    change (∫⁻ s, ENNReal.ofReal (‖rightLift 𝓕 μ H tv (s,ω)‖^2) ∂timeMeasure H) = _ at hr
    rw [hr]
    exact ht.trans (hd.trans hs)
  have hadd := PredictableBracketAdd.bracket_add_bound 𝓕 μ H
    (TwoChannelItoRows.block 𝓕 μ H v₀ vU) (rightLift 𝓕 μ H tv)
    (add_nonneg hK₀ hK) (mul_nonneg (by norm_num) hK) hcur hrightBound
  unfold input PredictableL2.bracket
  rw [PastTwoChannelAlgebra.post_hybrid_eq]
  filter_upwards [hadd] with ω hω
  exact hω.trans_eq (congrArg ENNReal.ofReal (by dsimp [K₀,K];ring))

end SHE.NativePastHybridInput
