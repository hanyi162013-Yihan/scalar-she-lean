module

public import SHE.NativeJointPhysicalGammaInput
public import SHE.L2ParameterAverage

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

namespace SHE.NativeJointGammaSquareKernel
open MeasureTheory Set FiniteHaar StoppedFourier NativeObservationCovariance OrthogonalItoChannels PredictableL2
open scoped NNReal ENNReal
local instance nativeJointPhysicalGammaInput_unit : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance nativeJointPhysicalGammaInput_period : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance nativeJointPhysicalGammaInput_circleSigma : MeasurableSpace CircleHeat.CircleL2:=borel _
local instance nativeJointPhysicalGammaInput_circleBorel : BorelSpace CircleHeat.CircleL2:=⟨rfl⟩
local instance nativeJointPhysicalGammaInput_rowSigma : MeasurableSpace RealHaarInput:=borel _
local instance nativeJointPhysicalGammaInput_rowBorel : BorelSpace RealHaarInput:=⟨rfl⟩
local instance nativeJointPhysicalGammaInput_bothSigma : MeasurableSpace (Both RealHaarInput):=borel _
local instance nativeJointPhysicalGammaInput_bothBorel : BorelSpace (Both RealHaarInput):=⟨rfl⟩
variable {Ω:Type*} [MeasurableSpace Ω]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›) (v b:ℝ≥0)
variable {κ m U:ℝ} (hκ:0<κ) (hm:0<m)
variable (μ:Measure Ω) [IsProbabilityMeasure μ] (H:ℝ≥0) (hbH:b≤H) (hb1:(b:ℝ)≤1)
variable (B:ℝ) (hB:0≤B) (g:Fin 6→(ℝ≥0×Ω)×HeatCircle→ℂ)
variable (hgm:∀i,@Measurable _ ℂ (𝓕.predictable.prod inferInstance) _ (g i))
variable (hg:∀i p x,‖g i (p,x)‖≤B)
variable (c0 c1 r0 r1:ℝ≥0×Ω→EllipticField m U)
variable (hc0:Measurable[𝓕.predictable] c0) (hc1:Measurable[𝓕.predictable] c1)
variable (hr0:Measurable[𝓕.predictable] r0) (hr1:Measurable[𝓕.predictable] r1)
variable (d:ℝ≥0×Ω→ℝ) (hd:Measurable[𝓕.predictable] d) (hdb:∀p,0≤d p ∧ d p≤1)

local notation "Raw"=>NativeJointPhysicalGammaInput.raw v b hκ hm g c0 c1 r0 r1 d
local notation "ν"=>((energyMeasure μ H).trim (predictable_le_product 𝓕))
local notation "Maj"=>NativePhysicalGammaInput.majorant v b (κ:=κ) (U:=U) B

theorem majorant_predictable:StronglyMeasurable[𝓕.predictable] Maj:=by
  have hs:=(((NativeGammaClock.age_measurable 𝓕 v b).pow_const (-(1/2:ℝ))).indicator
    (NativeGammaClock.window_measurable 𝓕 v b)).stronglyMeasurable
  exact stronglyMeasurable_const.add (hs.const_mul (16*B^2*(κ+U)*heatConstant))

include hgm hg hB hc0 hc1 hr0 hr1 hd hdb hbH hb1 in
/-- The actual full original row is jointly L2 for the spatial parameter
and the trimmed predictable energy measure. This is derived from its
native heat majorant, not assumed as a stochastic Fubini premise. -/
theorem input_memLp:
    (letI:MeasurableSpace (ℝ≥0×Ω):=𝓕.predictable
     MemLp (fun z:HeatCircle×(ℝ≥0×Ω)=>Raw (z.2,z.1)) 2
       (AddCircle.haarAddCircle.prod ν)):=by
  haveI:IsFiniteMeasure (energyMeasure μ H):=by dsimp only [energyMeasure];infer_instance
  letI:MeasurableSpace (ℝ≥0×Ω):=𝓕.predictable
  have hs:StronglyMeasurable (fun z:HeatCircle×(ℝ≥0×Ω)=>Raw (z.2,z.1)):=
    (NativeJointPhysicalGammaInput.raw_predictable 𝓕 v b hκ hm g hgm c0 c1 r0 r1
      hc0 hc1 hr0 hr1 d hd).comp_measurable measurable_swap
  have hi:Integrable Maj ν:=(NativePhysicalGammaInput.majorant_integrable 𝓕 v b μ H hbH hb1 B).trim
    (predictable_le_product 𝓕) (majorant_predictable 𝓕 v b B)
  apply (memLp_two_iff_integrable_sq_norm hs.aestronglyMeasurable).mpr
  apply (hi.comp_snd (AddCircle.haarAddCircle:Measure HeatCircle)).mono' (hs.norm.pow 2).aestronglyMeasurable
  filter_upwards with z
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  exact NativeJointPhysicalGammaInput.raw_majorized v b hκ hm B hB g hg c0 c1 r0 r1 d hdb z.2 z.1

/-- Finite genuine scalar output energy gives joint L2; this uses only
ordinary product integration and positivity. -/
theorem output_memLp (Y:HeatCircle×Ω→ℝ)(hY:Measurable Y)
    (hE:(∫⁻x,∫⁻ω,ENNReal.ofReal (|Y (x,ω)|^2) ∂μ ∂AddCircle.haarAddCircle)<∞):
    MemLp Y 2 (AddCircle.haarAddCircle.prod μ):=by
  apply (memLp_two_iff_integrable_sq_norm hY.stronglyMeasurable.aestronglyMeasurable).mpr
  refine ⟨(hY.stronglyMeasurable.norm.pow 2).aestronglyMeasurable,?_⟩
  apply (hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun z=>sq_nonneg ‖Y z‖))).mpr
  rw [lintegral_prod _ ((hY.norm.pow_const 2).ennreal_ofReal.aemeasurable)]
  simpa only [Real.norm_eq_abs] using hE
end SHE.NativeJointGammaSquareKernel
