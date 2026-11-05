module

public import SHE.NativePairedGammaEnergy
public import SHE.NativeConvexGammaProcess
public import SHE.ScalarHeatSixFields
public import SHE.NativeJointGammaFourierAverage
public import SHE.NativeJointGammaFourierInput
public import SHE.NativeJointGammaFourierOutput
public import SHE.NativeConvexGammaReal
public import SHE.NativeJointGammaSpatialIto
public import SHE.NativeScalarFourierWeight
public import SHE.NativeFourierSections

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
namespace SHE.NativeJointGammaHilbertIdentity
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
local instance : MeasurableSpace DyadicApproximation.RealL2:=borel _
local instance : BorelSpace DyadicApproximation.RealL2:=⟨rfl⟩
local instance : MeasurableSpace RealHaarInput:=borel _
local instance : BorelSpace RealHaarInput:=⟨rfl⟩
local instance : MeasurableSpace (Both RealHaarInput):=borel _
local instance : BorelSpace (Both RealHaarInput):=⟨rfl⟩
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

variable (I0 I1:StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=DyadicApproximation.RealL2) 𝓕 μ H)
variable (J:StandardTerminalIto (C:=Both Row) (E:=ℝ) 𝓕 μ H)
variable (hIJ0:NativeObservationNaturality.StandardScalarNaturality I0 (leftIntegral 𝓕 μ H J))
variable (hIJ1:NativeObservationNaturality.StandardScalarNaturality I1 (rightIntegral 𝓕 μ H J))
local notation "Z"=>fun ω=>NativeHeatObservation.embed
  (I0.integral (NativeRealFourierProcess.realProcess 𝓕 μ H A0) ω+
   I1.integral (NativeRealFourierProcess.realProcess 𝓕 μ H A1) ω)

include hB hr hIJ0 hIJ1 in
/-- The ORIGINAL scalar spatial Gamma and ORIGINAL physical Hilbert
output are the SAME stochastic object after the native Bessel weight.
This is an output identity, not merely an equality of expected energies. -/
theorem exists_identified_output (hF:StandardItoParameterFubini J):
    ∃Y:HeatCircle×Ω→ℝ,Measurable Y ∧
      (∀ᵐx∂AddCircle.haarAddCircle,(fun ω=>Y (x,ω))=ᵐ[μ] J.integral (S x)) ∧
      (∫⁻x,∫⁻ω,ENNReal.ofReal (|Y (x,ω)|^2) ∂μ ∂AddCircle.haarAddCircle)<∞ ∧
      ∀ᵐω∂μ,
        (∀l:ℤ,fourierCoeff (Z ω) l=
          (((Λ+(l:ℝ)^2)^(-ρ/2):ℝ):ℂ)*fourierCoeff (fun x:HeatCircle=>(Y (x,ω):ℂ)) l) ∧
        Summable (fun l:ℤ=>(Λ+(l:ℝ)^2)^(-ρ)*‖fourierCoeff (fun x:HeatCircle=>(Y (x,ω):ℂ)) l‖^2) ∧
        (∑'l:ℤ,(Λ+(l:ℝ)^2)^(-ρ)*‖fourierCoeff (fun x:HeatCircle=>(Y (x,ω):ℂ)) l‖^2)=‖Z ω‖^2:=by
  obtain ⟨Y,hY,hRep,hE,hFourier⟩:=NativeJointGammaFourierOutput.exists_output 𝓕 μ H v b hbH hb1
    hΛ hρ hρhalf hm B hB g hgm hg hr d hd hd0 hd1 κ hκ c0 c1 r0 r1 hc0 hc1 hr0 hr1 J hF
  refine ⟨Y,hY,hRep,hE,?_⟩
  have hReal0:=NativeConvexGammaReal.additive_real 𝓕 μ H v b hbH hb1 hΛ hρ hρhalf B g hgm hr hg κ hκ
  have hReal1:=NativeConvexGammaReal.residual_real 𝓕 μ H v b hbH hb1 hΛ hρ hρhalf hm B g hgm hr hg
    d hd hd0 hd1 c0 c1 r0 r1 hc0 hc1 hr0 hr1
  have hCoeff:=NativeHilbertFourierIto.coefficients 𝓕 μ H I0 I1 J hIJ0 hIJ1
    (NativeRealFourierProcess.realProcess 𝓕 μ H A0) (NativeRealFourierProcess.realProcess 𝓕 μ H A1)
  rw [NativeRealFourierProcess.native_real_eq 𝓕 μ H A0 hReal0,
    NativeRealFourierProcess.native_real_eq 𝓕 μ H A1 hReal1] at hCoeff
  filter_upwards [hFourier,hCoeff] with ω hf hc
  have he:∀l:ℤ,fourierCoeff (Z ω) l=
      (((Λ+(l:ℝ)^2)^(-ρ/2):ℝ):ℂ)*fourierCoeff (fun x:HeatCircle=>(Y (x,ω):ℂ)) l:=by
    intro l
    rw [←NativeMultiplierFourierIntegral.coefficient_apply]
    apply Complex.ext
    · simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
      exact (hc l).1.trans (hf l).1
    · simp only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero]
      exact (hc l).2.trans (hf l).2
  exact ⟨he,NativeFourierAverage.energy_of_identified Λ ρ hΛ (Z ω) (fun x:HeatCircle=>(Y (x,ω):ℂ)) he⟩
end SHE.NativeJointGammaHilbertIdentity
