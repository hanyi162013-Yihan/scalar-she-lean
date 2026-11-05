module

public import SHE.NativePairedGammaEnergy
public import SHE.NativeConvexGammaProcess
public import SHE.ScalarHeatSixFields
public import SHE.NativeJointGammaFourierAverage

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
namespace SHE.NativeJointGammaFourierInput
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

include hB hr in
/-- Every actual predictable Fourier input is the spatial average of
the literal original scalar joint-Gamma row, on one event for ALL modes. -/
theorem input_ae:
    ∀ᵐp∂energyMeasure μ H,∀l:ℤ,
      realInput 𝓕 μ H l A0 A1 p=
        (∫x:HeatCircle,((Λ+(l:ℝ)^2)^(-ρ/2)*(fourier (-l) x).re) • Raw (p,x) ∂AddCircle.haarAddCircle) ∧
      imagInput 𝓕 μ H l A0 A1 p=
        (∫x:HeatCircle,((Λ+(l:ℝ)^2)^(-ρ/2)*(fourier (-l) x).im) • Raw (p,x) ∂AddCircle.haarAddCircle):=by
  have h0:=NativeColumnProcesses.process_ae 𝓕 μ H K0 hK0 hE0
  have h1:=NativeColumnProcesses.process_ae 𝓕 μ H K1 hK1 hE1
  change A0=ᵐ[energyMeasure μ H] K0 at h0
  change A1=ᵐ[energyMeasure μ H] K1 at h1
  filter_upwards [ae_all_iff.mpr (fun l=>realInput_ae 𝓕 μ H l A0 A1),
    ae_all_iff.mpr (fun l=>imagInput_ae 𝓕 μ H l A0 A1),h0,h1] with p hp hq h0 h1 l
  constructor
  · rw [hp l,h0,h1]
    exact NativeJointGammaFourierAverage.real 𝓕 v b hΛ hρ hρhalf hb1 hκ hm B hB g hgm hg hr
      c0 c1 r0 r1 hc0 hc1 hr0 hr1 d hd (fun p=>⟨hd0 p,hd1 p⟩) p l
  · rw [hq l,h0,h1]
    exact NativeJointGammaFourierAverage.imag 𝓕 v b hΛ hρ hρhalf hb1 hκ hm B hB g hgm hg hr
      c0 c1 r0 r1 hc0 hc1 hr0 hr1 d hd (fun p=>⟨hd0 p,hd1 p⟩) p l
end SHE.NativeJointGammaFourierInput
