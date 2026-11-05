module

public import SHE.NativeJointGammaSquareKernel
public import SHE.WeightedL2OperatorAverage

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

namespace SHE.NativeJointGammaSpatialIto
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
local notation "K"=>NativeJointPhysicalGammaInput.process 𝓕 v b hκ hm μ H hbH hb1 B hB g hgm hg
  c0 c1 r0 r1 hc0 hc1 hr0 hr1 d hd hdb

include hgm hg hB hc0 hc1 hr0 hr1 hd hdb hbH hb1 in
/-- Spatial averaging of the literal original Gamma row commutes with
its SAME original scalar Ito map. All joint L2 applicability follows
from the actual heat majorant and the supplied genuine output version. -/
theorem integral_eq_average (J:StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
    (Y:HeatCircle×Ω→ℝ)(hY:Measurable Y)
    (hRep:∀ᵐx∂AddCircle.haarAddCircle,(fun ω=>Y (x,ω))=ᵐ[μ] J.integral (K x))
    (hE:(∫⁻x,∫⁻ω,ENNReal.ofReal (|Y (x,ω)|^2) ∂μ ∂AddCircle.haarAddCircle)<∞)
    (φ:HeatCircle→ℝ)(hφ:Measurable φ)(M:ℝ)(hφM:∀x,‖φ x‖≤M)
    (P:Process (E:=Both RealHaarInput) 𝓕 μ H)
    (hP:P=ᵐ[energyMeasure μ H] fun p=>∫x:HeatCircle,φ x • Raw (p,x) ∂AddCircle.haarAddCircle):
    J.integral P=ᵐ[μ] fun ω=>∫x:HeatCircle,φ x*Y (x,ω) ∂AddCircle.haarAddCircle:=by
  haveI:IsFiniteMeasure (energyMeasure μ H):=by dsimp only [energyMeasure];infer_instance
  letI:MeasurableSpace (ℝ≥0×Ω):=𝓕.predictable
  have hrs:StronglyMeasurable (fun z:HeatCircle×(ℝ≥0×Ω)=>Raw (z.2,z.1)):=
    (NativeJointPhysicalGammaInput.raw_predictable 𝓕 v b hκ hm g hgm c0 c1 r0 r1
      hc0 hc1 hr0 hr1 d hd).comp_measurable measurable_swap
  have hAvg:StronglyMeasurable (fun p:ℝ≥0×Ω=>∫x:HeatCircle,φ x • Raw (p,x) ∂AddCircle.haarAddCircle):=
    ((hφ.comp measurable_fst).stronglyMeasurable.smul hrs).integral_prod_left'
  have hPa:P=ᵐ[ν] fun p=>∫x:HeatCircle,φ x • Raw (p,x) ∂AddCircle.haarAddCircle:=
    ae_eq_trim_of_measurable (predictable_le_product 𝓕) (Lp.stronglyMeasurable P).measurable hAvg.measurable hP
  have hK:∀x:HeatCircle,K x=ᵐ[ν] fun p=>Raw (p,x):=by
    intro x
    exact (NativeJointPhysicalGammaInput.section_memLp 𝓕 v b hκ hm μ H hbH hb1 B hB g hgm hg
      c0 c1 r0 r1 hc0 hc1 hr0 hr1 d hd hdb x).coeFn_toLp
  exact WeightedL2OperatorAverage.commutes AddCircle.haarAddCircle ν μ J.integral.toContinuousLinearMap
    K (fun z=>Raw (z.2,z.1))
    (NativeJointGammaSquareKernel.input_memLp 𝓕 v b hκ hm μ H hbH hb1 B hB g hgm hg
      c0 c1 r0 r1 hc0 hc1 hr0 hr1 d hd hdb) hK Y hY.stronglyMeasurable
    (NativeJointGammaSquareKernel.output_memLp μ Y hY hE)
    (hRep.mono (fun x hx=>hx.symm)) φ hφ M hφM P hPa
end SHE.NativeJointGammaSpatialIto
