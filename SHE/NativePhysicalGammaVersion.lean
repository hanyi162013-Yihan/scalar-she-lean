module

public import SHE.NativePhysicalGammaInput
public import SHE.NativeGammaClock
public import SHE.ScalarHeatGammaSlots
public import SHE.AdditiveHaarForcing
public import SHE.OrthogonalItoChannels
public import SHE.StandardItoParameterFubini

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
namespace SHE.NativePhysicalGammaVersion
open MeasureTheory Set FiniteHaar StoppedFourier NativeObservationCovariance OrthogonalItoChannels PredictableL2
open scoped NNReal ENNReal
local instance : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance : MeasurableSpace CircleHeat.CircleL2:=borel _
local instance : BorelSpace CircleHeat.CircleL2:=⟨rfl⟩
local instance : MeasurableSpace RealHaarInput:=borel _
local instance : BorelSpace RealHaarInput:=⟨rfl⟩
local instance : MeasurableSpace (Both RealHaarInput):=borel _
local instance : BorelSpace (Both RealHaarInput):=⟨rfl⟩
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
local notation "Raw"=>NativePhysicalGammaKernel.raw v b hκ hm g c0 c1 r0 r1
local notation "Hraw"=>NativePhysicalGammaKernel.raw_predictable 𝓕 v b hκ hm g hgm c0 c1 r0 r1 hc0 hc1 hr0 hr1

local notation "Maj"=>NativePhysicalGammaInput.majorant v b (κ:=κ) (U:=U) B
local notation "K"=>NativePhysicalGammaInput.process 𝓕 v b hκ hm μ H hbH hb1 B hB g hgm hg c0 c1 r0 r1 hc0 hc1 hr0 hr1

include 𝓕 hg hB hbH hb1 in
/-- Parameterized ordinary Ito construction has finite ORIGINAL
spatial/time/sample energy, derived from the native heat majorant. -/
theorem parameter_energy_finite :
    (∫⁻x:HeatCircle,∫⁻t,∫⁻ω,ENNReal.ofReal (‖Raw ((t,ω),x)‖^2) ∂μ ∂timeMeasure H ∂AddCircle.haarAddCircle)<∞:=by
  haveI:Nonempty Ω:=nonempty_of_isProbabilityMeasure μ
  have hU:0≤U:=elliptic_upper_nonneg (c0 (0,Classical.arbitrary Ω)).1 m U hm (c0 (0,Classical.arbitrary Ω)).2.2
  have hi:=NativePhysicalGammaInput.majorant_integrable 𝓕 v b μ H hbH hb1 (κ:=κ) (U:=U) B
  have htop: (∫⁻p,ENNReal.ofReal (Maj p) ∂energyMeasure μ H)<∞:=
    (hasFiniteIntegral_iff_ofReal (ae_of_all _ (NativePhysicalGammaInput.majorant_nonneg v b hκ B hU))).mp hi.hasFiniteIntegral
  apply lt_of_le_of_lt _ htop
  calc
    _≤∫⁻x:HeatCircle,∫⁻t,∫⁻ω,ENNReal.ofReal (Maj (t,ω)) ∂μ ∂timeMeasure H ∂AddCircle.haarAddCircle:=by
      apply lintegral_mono
      intro x
      apply lintegral_mono
      intro t
      apply lintegral_mono
      intro ω
      exact ENNReal.ofReal_le_ofReal (NativePhysicalGammaInput.raw_majorized v b hκ hm B hB g hg c0 c1 r0 r1 (t,ω) x)
    _=_:=by
      simp only [lintegral_const,measure_univ,mul_one,one_mul]
      exact (lintegral_prod _ hi.aestronglyMeasurable.aemeasurable.ennreal_ofReal).symm

include hgm hg hB hc0 hc1 hr0 hr1 hbH hb1 in
/-- Ordinary stochastic-Fubini package4 yields a jointly measurable
physical Gamma driven by the SAME original J. The integrated isometry
is proved from J and the actual kernel, with all applicability derived. -/
theorem exists_version (J:StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
    (hF:StandardItoParameterFubini J):
    ∃Y:HeatCircle×Ω→ℝ,Measurable Y ∧
      (∀ᵐx∂AddCircle.haarAddCircle,(fun ω=>Y (x,ω))=ᵐ[μ] J.integral (K x)) ∧
      (∫⁻x,∫⁻ω,ENNReal.ofReal (|Y (x,ω)|^2) ∂μ ∂AddCircle.haarAddCircle)=
        (∫⁻x:HeatCircle,∫⁻t,∫⁻ω,ENNReal.ofReal (‖Raw ((t,ω),x)‖^2) ∂μ ∂timeMeasure H ∂AddCircle.haarAddCircle) ∧
      (∫⁻x,∫⁻ω,ENNReal.ofReal (|Y (x,ω)|^2) ∂μ ∂AddCircle.haarAddCircle)<∞:=by
  have hs:StronglyMeasurable[(inferInstance:MeasurableSpace HeatCircle).prod 𝓕.predictable]
      (fun z:HeatCircle×(ℝ≥0×Ω)=>Raw (z.2,z.1)):=by
    letI:MeasurableSpace (ℝ≥0×Ω):=𝓕.predictable
    exact (Hraw).comp_measurable measurable_swap
  have hk(x:HeatCircle):K x=ᵐ[energyMeasure μ H] (fun p=>Raw (p,x)):=
    NativePhysicalGammaInput.process_ae 𝓕 v b hκ hm μ H hbH hb1 B hB g hgm hg c0 c1 r0 r1 hc0 hc1 hr0 hr1 x
  have ht:=parameter_energy_finite 𝓕 v b hκ hm μ H hbH hb1 B hB g hg c0 c1 r0 r1
  obtain ⟨Y,hY,hYa,hYe⟩:=StandardItoParameterFubini.energy J hF AddCircle.haarAddCircle K
    (fun z:HeatCircle×(ℝ≥0×Ω)=>Raw (z.2,z.1)) hs hk ht
  exact ⟨Y,hY,hYa,hYe,hYe.trans_lt ht⟩

end SHE.NativePhysicalGammaVersion
