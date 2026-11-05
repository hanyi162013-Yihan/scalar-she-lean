module

public import SHE.NativePairedGammaReal
public import SHE.NativeConvexGammaEnergy
public import SHE.NativePairedColumnsReal
public import SHE.NativeRealFourierProcess
public import SHE.ScalarHeatSixFields

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
namespace SHE.NativeConvexGammaReal
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
local instance : MeasurableSpace RealHaarInput:=borel _
local instance : BorelSpace RealHaarInput:=⟨rfl⟩
local instance : MeasurableSpace (Both RealHaarInput):=borel _
local instance : BorelSpace (Both RealHaarInput):=⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
variable (H v b : ℝ≥0) (hbH : b≤H) (hb1 : (b:ℝ)≤1)
variable {Λ ρ m U : ℝ} (hΛ : 1≤Λ) (hρ : 0<ρ) (hρhalf : ρ<1/2) (hm : 0<m)
variable (B : ℝ) (g : Fin 6→(ℝ≥0×Ω)×HeatCircle→ℂ)
variable (hgm : ∀ i,@Measurable _ _ (𝓕.predictable.prod inferInstance) _ (g i))
variable (hr:∀i p x,(g i (p,x)).im=0)
variable (hg : ∀ i p x,‖g i (p,x)‖≤B)
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

def additive : Process (E:=Columns) 𝓕 μ H:=NativeColumnProcesses.process 𝓕 μ H K0 hK0 hE0
def residual : Process (E:=Columns) 𝓕 μ H:=NativeColumnProcesses.process 𝓕 μ H K1 hK1 hE1

local notation "A0"=>NativePairedGammaEnergy.additive 𝓕 μ H v b hbH hb1 hΛ hρ hρhalf B g hgm hg κ hκ
local notation "A1"=>NativeConvexGammaEnergy.residual 𝓕 μ H v b hbH hb1 hΛ hρ hρhalf hm B g hgm hg d hd hd0 hd1 c0 c1 r0 r1 hc0 hc1 hr0 hr1

theorem real_smul (e:ℝ) (f:CircleL2) (hf:∀ᵐx∂AddCircle.haarAddCircle,(f x).im=0):
    ∀ᵐx∂AddCircle.haarAddCircle,((e • f) x).im=0:=by
  filter_upwards [hf,Lp.coeFn_smul e f] with x hf hx
  rw [hx]
  change (e • f x).im=0
  simpa only [Complex.smul_im,hf,smul_zero]

include hr in
theorem field_real (f0 f1 s0 s1:ℝ≥0×Ω→EllipticField m U) (p:ℝ≥0×Ω) (q:HaarNode):
    ∀ᵐx∂AddCircle.haarAddCircle,
      (NativeConvexGammaProcess.field 𝓕 v b hb1 hΛ hρ.le hρhalf hm B g hgm hg d f0 f1 s0 s1 p q x).im=0:=by
  have h0:=NativePairedGammaReal.field_real 𝓕 v b hb1 hΛ hρ hρhalf hm B g hgm hr hg f0 f1 s0 s1 p q
  have h1:=NativePairedGammaReal.field_real 𝓕 v b hb1 hΛ hρ hρhalf hm B g hgm hr hg f0 f0 s0 s1 p q
  simp only [NativeConvexGammaProcess.field,lp.coeFn_add,lp.coeFn_smul,Pi.add_apply,Pi.smul_apply]
  exact NativePairedColumnsReal.real_add _ _ (real_smul (d p) _ h0) (real_smul (1-d p) _ h1)

include hr in
theorem additive_real :∀ᵐp∂energyMeasure μ H,∀q:HaarNode,∀ᵐx∂AddCircle.haarAddCircle,(A0 p q x).im=0:=by
  filter_upwards [NativeColumnProcesses.process_ae 𝓕 μ H K0 hK0 hE0] with p hp q
  change A0 p=K0 p at hp
  rw [hp]
  exact NativePairedGammaReal.field_real (m:=κ) (U:=κ) 𝓕 v b hb1 hΛ hρ hρhalf hκ B g hgm hr hg _ _ _ _ p q

include hr in
theorem residual_real :∀ᵐp∂energyMeasure μ H,∀q:HaarNode,∀ᵐx∂AddCircle.haarAddCircle,(A1 p q x).im=0:=by
  filter_upwards [NativeColumnProcesses.process_ae 𝓕 μ H K1 hK1 hE1] with p hp q
  change A1 p=K1 p at hp
  rw [hp]
  exact field_real 𝓕 v b hb1 hΛ hρ hρhalf hm B g hgm hr hg d c0 c1 r0 r1 p q

include hr in
/-- The checked complete paired Fourier Gamma is exactly the native
physical Hilbert stochastic output of the ORIGINAL two Ito channels.
All real-subspace and native column applicability is derived above. -/
theorem physical_energy_eq
    (I0 I1:StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=DyadicApproximation.RealL2) 𝓕 μ H)
    (J:StandardTerminalIto (C:=Both Row) (E:=ℝ) 𝓕 μ H)
    (hIJ0:NativeObservationNaturality.StandardScalarNaturality I0 (leftIntegral 𝓕 μ H J))
    (hIJ1:NativeObservationNaturality.StandardScalarNaturality I1 (rightIntegral 𝓕 μ H J)):
    (∫⁻ω,ENNReal.ofReal (‖NativeHeatObservation.embed
      (I0.integral (NativeRealFourierProcess.realProcess 𝓕 μ H A0) ω+
       I1.integral (NativeRealFourierProcess.realProcess 𝓕 μ H A1) ω)‖^2) ∂μ)=
      (∫⁻ω,(∑'l:ℤ,ENNReal.ofReal (‖J.integral (realInput 𝓕 μ H l A0 A1) ω‖^2))+
        (∑'l:ℤ,ENNReal.ofReal (‖J.integral (imagInput 𝓕 μ H l A0 A1) ω‖^2)) ∂μ):=by
  exact NativeRealFourierProcess.physical_energy 𝓕 μ H I0 I1 J hIJ0 hIJ1 A0 A1
    (additive_real 𝓕 μ H v b hbH hb1 hΛ hρ hρhalf B g hgm hr hg κ hκ)
    (residual_real 𝓕 μ H v b hbH hb1 hΛ hρ hρhalf hm B g hgm hr hg d hd hd0 hd1 c0 c1 r0 r1 hc0 hc1 hr0 hr1)

end SHE.NativeConvexGammaReal
