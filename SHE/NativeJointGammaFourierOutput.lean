module

public import SHE.NativePairedGammaEnergy
public import SHE.NativeConvexGammaProcess
public import SHE.ScalarHeatSixFields
public import SHE.NativeJointGammaFourierAverage
public import SHE.NativeJointGammaFourierInput
public import SHE.NativeJointGammaSpatialIto
public import SHE.NativeScalarFourierWeight
public import SHE.NativeFourierSections

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
namespace SHE.NativeJointGammaFourierOutput
open Set MeasureTheory PredictableL2 StoppedFourier FiniteHaar NativeMultiplierHilbertColumns
open OrthogonalItoChannels NativeFourierIto NativeFourierNoiseRows
open scoped NNReal ENNReal
local instance nativePairedGammaEnergy_period : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance nativePairedGammaEnergy_unit : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance nativePairedGammaEnergy_sigma : MeasurableSpace CircleL2:=borel _
local instance nativePairedGammaEnergy_borel : BorelSpace CircleL2:=⟨rfl⟩
local instance nativePairedGammaEnergy_unitSigma : MeasurableSpace CircleHeat.CircleL2:=borel _
local instance nativePairedGammaEnergy_unitBorel : BorelSpace CircleHeat.CircleL2:=⟨rfl⟩
local instance nativePairedGammaEnergy_second : SecondCountableTopology CircleL2:=
  (_root_.fourierBasis (T:=2*Real.pi)).repr.toHomeomorph.secondCountableTopology
local instance nativePairedGammaEnergy_spaceSigma : MeasurableSpace Space:=borel _
local instance nativePairedGammaEnergy_spaceBorel : BorelSpace Space:=⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
variable (H v b : ℝ≥0) (hbH : b≤H) (hb1 : (b:ℝ)≤1)
variable {Λ ρ m U : ℝ} (hΛ : 1≤Λ) (hρ : 0<ρ) (hρhalf : ρ<1/2) (hm : 0<m)
variable (B : ℝ) (hB:0≤B) (g : Fin 6→(ℝ≥0×Ω)×HeatCircle→ℂ)
variable (hgm : ∀ i,@Measurable _ _ (𝓕.predictable.prod inferInstance) _ (g i))
variable (hg : ∀ i p x,‖g i (p,x)‖≤B)
variable (hr:∀i p x,(g i (p,x)).im=0)
variable (d:ℝ≥0×Ω→ℝ) (hd:Measurable[𝓕.predictable] d) (hd0:∀p,0≤d p) (hd1:∀p,d p≤1)
variable (κ : ℝ) (hκ : 0<κ)
variable (c0 c1 r0 r1 : ℝ≥0×Ω→EllipticField m U)
variable (hc0 : Measurable[𝓕.predictable] c0) (hc1 : Measurable[𝓕.predictable] c1)
variable (hr0 : Measurable[𝓕.predictable] r0) (hr1 : Measurable[𝓕.predictable] r1)

local notation "K0"=>NativePairedGammaProcess.field 𝓕 v b hb1 hΛ hρ.le hρhalf hκ B g hgm hg
  (fun _=>AdditiveHaarForcing.constantField κ hκ) (fun _=>AdditiveHaarForcing.constantField κ hκ)
  (fun _=>AdditiveHaarForcing.constantField κ hκ) (fun _=>AdditiveHaarForcing.constantField κ hκ)
local notation "K1"=>NativeConvexGammaProcess.field 𝓕 v b hb1 hΛ hρ.le hρhalf hm B g hgm hg d c0 c1 r0 r1
local notation "hK0"=>NativePairedGammaProcess.field_predictable 𝓕 v b hb1 hΛ hρ.le hρhalf hκ B g hgm hg
  _ _ _ _ measurable_const measurable_const measurable_const measurable_const
local notation "hK1"=>NativeConvexGammaProcess.field_predictable 𝓕 v b hb1 hΛ hρ.le hρhalf hm B g hgm hg d hd
  c0 c1 r0 r1 hc0 hc1 hr0 hr1
local notation "hE0"=>NativePairedGammaProcess.field_energy 𝓕 μ H v b hbH hb1 hΛ hρ.le hρhalf hκ B g hgm hg
  _ _ _ _ measurable_const measurable_const measurable_const measurable_const
local notation "hE1"=>NativeConvexGammaProcess.field_energy 𝓕 μ H v b hbH hb1 hΛ hρ.le hρhalf hm B g hgm hg d hd hd0 hd1
  c0 c1 r0 r1 hc0 hc1 hr0 hr1


local notation "A0"=>NativePairedGammaEnergy.additive 𝓕 μ H v b hbH hb1 hΛ hρ hρhalf B g hgm hg κ hκ
local notation "A1"=>NativeConvexGammaEnergy.residual 𝓕 μ H v b hbH hb1 hΛ hρ hρhalf hm B g hgm hg d hd hd0 hd1 c0 c1 r0 r1 hc0 hc1 hr0 hr1

local notation "Raw"=>NativeJointPhysicalGammaInput.raw v b hκ hm g c0 c1 r0 r1 d

local notation "S"=>NativeJointPhysicalGammaInput.process 𝓕 v b hκ hm μ H hbH hb1 B hB g hgm hg
  c0 c1 r0 r1 hc0 hc1 hr0 hr1 d hd (fun p=>⟨hd0 p,hd1 p⟩)

include hB hr in
/-- ONE genuine spatial scalar Gamma version has the exact Fourier
outputs of the native additive/convex Hilbert columns on the SAME J.
Both coordinates and ALL modes hold on one original sample event. -/
theorem exists_output (J:StandardTerminalIto (C:=Both Row) (E:=ℝ) 𝓕 μ H)
    (hF:StandardItoParameterFubini J):
    ∃Y:HeatCircle×Ω→ℝ,Measurable Y ∧
      (∀ᵐx∂AddCircle.haarAddCircle,(fun ω=>Y (x,ω))=ᵐ[μ] J.integral (S x)) ∧
      (∫⁻x,∫⁻ω,ENNReal.ofReal (|Y (x,ω)|^2) ∂μ ∂AddCircle.haarAddCircle)<∞ ∧
      ∀ᵐω∂μ,∀l:ℤ,
        J.integral (realInput 𝓕 μ H l A0 A1) ω=
          (Λ+(l:ℝ)^2)^(-ρ/2)*(fourierCoeff (fun x:HeatCircle=>(Y (x,ω):ℂ)) l).re ∧
        J.integral (imagInput 𝓕 μ H l A0 A1) ω=
          (Λ+(l:ℝ)^2)^(-ρ/2)*(fourierCoeff (fun x:HeatCircle=>(Y (x,ω):ℂ)) l).im:=by
  obtain ⟨Y,hY,hRep,_,hE⟩:=NativeJointPhysicalGammaInput.exists_version 𝓕 v b hκ hm μ H hbH hb1 B hB g hgm hg
    c0 c1 r0 r1 hc0 hc1 hr0 hr1 d hd (fun p=>⟨hd0 p,hd1 p⟩) J hF
  refine ⟨Y,hY,hRep,hE,?_⟩
  have hInput:=NativeJointGammaFourierInput.input_ae 𝓕 μ H v b hbH hb1 hΛ hρ hρhalf hm B hB g hgm hg hr
    d hd hd0 hd1 κ hκ c0 c1 r0 r1 hc0 hc1 hr0 hr1
  have hR(l:ℤ):J.integral (realInput 𝓕 μ H l A0 A1)=ᵐ[μ]
      fun ω=>∫x:HeatCircle,NativeScalarFourierWeight.value ((Λ+(l:ℝ)^2)^(-ρ/2)) Complex.reCLM l x*Y (x,ω) ∂AddCircle.haarAddCircle:=by
    exact NativeJointGammaSpatialIto.integral_eq_average 𝓕 v b hκ hm μ H hbH hb1 B hB g hgm hg
      c0 c1 r0 r1 hc0 hc1 hr0 hr1 d hd (fun p=>⟨hd0 p,hd1 p⟩) J Y hY hRep hE
      (NativeScalarFourierWeight.value ((Λ+(l:ℝ)^2)^(-ρ/2)) Complex.reCLM l)
      (NativeScalarFourierWeight.measurable _ _ _) (‖(Λ+(l:ℝ)^2)^(-ρ/2)‖*‖Complex.reCLM‖)
      (NativeScalarFourierWeight.bound _ _ _) (realInput 𝓕 μ H l A0 A1)
      (hInput.mono (fun p hp=>(hp l).1))
  have hI(l:ℤ):J.integral (imagInput 𝓕 μ H l A0 A1)=ᵐ[μ]
      fun ω=>∫x:HeatCircle,NativeScalarFourierWeight.value ((Λ+(l:ℝ)^2)^(-ρ/2)) Complex.imCLM l x*Y (x,ω) ∂AddCircle.haarAddCircle:=by
    exact NativeJointGammaSpatialIto.integral_eq_average 𝓕 v b hκ hm μ H hbH hb1 B hB g hgm hg
      c0 c1 r0 r1 hc0 hc1 hr0 hr1 d hd (fun p=>⟨hd0 p,hd1 p⟩) J Y hY hRep hE
      (NativeScalarFourierWeight.value ((Λ+(l:ℝ)^2)^(-ρ/2)) Complex.imCLM l)
      (NativeScalarFourierWeight.measurable _ _ _) (‖(Λ+(l:ℝ)^2)^(-ρ/2)‖*‖Complex.imCLM‖)
      (NativeScalarFourierWeight.bound _ _ _) (imagInput 𝓕 μ H l A0 A1)
      (hInput.mono (fun p hp=>(hp l).2))
  have hSections:=((NativeJointGammaSquareKernel.output_memLp μ Y hY hE).integrable
    (by norm_num : (1:ℝ≥0∞)≤2)).prod_left_ae
  filter_upwards [ae_all_iff.mpr hR,ae_all_iff.mpr hI,hSections] with ω hr hi hs l
  constructor
  · exact (hr l).trans (NativeScalarFourierWeight.integral (fun x=>Y (x,ω)) hs _ Complex.reCLM l)
  · exact (hi l).trans (NativeScalarFourierWeight.integral (fun x=>Y (x,ω)) hs _ Complex.imCLM l)
end SHE.NativeJointGammaFourierOutput
