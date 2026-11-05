module

public import SHE.NativeConvexGammaEnergy
public import SHE.NativeConvexGammaProcess
public import SHE.ScalarHeatSixFields

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
namespace SHE.NativeConvexGammaUniform
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
variable (B : ℝ) (g : Fin 6→(ℝ≥0×Ω)×HeatCircle→ℂ)
variable (hgm : ∀ i,@Measurable _ _ (𝓕.predictable.prod inferInstance) _ (g i))
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

/-- Chosen before every past/current clock, field, damping and band. -/
def constant (m U:ℝ) (hm:0<m) {ρ:ℝ} (hρ:0<ρ) (hρhalf:ρ<1/2):ℝ:=
  Classical.choose (NativeConvexGammaTrace.exists_convex_trace m U hm hρ hρhalf)
theorem constant_pos (m U:ℝ) (hm:0<m) {ρ:ℝ} (hρ:0<ρ) (hρhalf:ρ<1/2):
    0<constant m U hm hρ hρhalf:=
  (Classical.choose_spec (NativeConvexGammaTrace.exists_convex_trace m U hm hρ hρhalf)).1
local notation "A0"=>NativePairedGammaEnergy.additive 𝓕 μ H v b hbH hb1 hΛ hρ hρhalf B g hgm hg κ hκ
local notation "A1"=>NativeConvexGammaEnergy.residual 𝓕 μ H v b hbH hb1 hΛ hρ hρhalf hm B g hgm hg d hd hd0 hd1 c0 c1 r0 r1 hc0 hc1 hr0 hr1

theorem complete_energy :
    ∀ (J : StandardTerminalIto (C:=Both Row) (E:=ℝ) 𝓕 μ H)
      (sharp : ℝ≥0×Ω→ℝ) (hsharp0 : ∀ p∈NativeGammaClock.window v b,0≤sharp p)
      (hsharp : ∀ p∈NativeGammaClock.window v b,∀ i,∀ᵐ x∂AddCircle.haarAddCircle,
        ‖NativeRandomRows.nativeRow (g i) p x‖≤sharp p),
    (∫⁻ ω,(∑' l : ℤ,ENNReal.ofReal (‖J.integral (realInput 𝓕 μ H l A0 A1) ω‖^2))+
      (∑' l : ℤ,ENNReal.ofReal (‖J.integral (imagInput 𝓕 μ H l A0 A1) ω‖^2)) ∂μ)≤
      ∫⁻ p,ENNReal.ofReal ((NativeGammaClock.window v b).indicator (fun p=>6*(
        (constant m U hm hρ hρhalf)*(sharp p)^2*(NativeHeatSpan.clock (NativeGammaClock.age v b p))^(-(1/2:ℝ))*
          NativeSignedHaarProcess.inputEnergy hΛ hρ.le (c1 p) (c0 p)+
        HaarWeightedHeat.higherConstant m U hm 0 ρ*(sharp p)^2*
          (NativeHeatSpan.clock (NativeGammaClock.age v b p))^(ρ-1/2)*‖(r0 p).1-(r1 p).1‖^2+
        (κ+U)*((1+2*HeatTrace.fractionalGaussianIntegral ρ)*(NativeGammaClock.age v b p)^(ρ-1/2))*
          (‖NativeRandomRows.nativeRow (g 0) p-NativeRandomRows.nativeRow (g 1) p‖^2+
           ‖NativeRandomRows.nativeRow (g 1) p-NativeRandomRows.nativeRow (g 2) p‖^2+
           ‖NativeRandomRows.nativeRow (g 3) p-NativeRandomRows.nativeRow (g 4) p‖^2+
           ‖NativeRandomRows.nativeRow (g 4) p-NativeRandomRows.nativeRow (g 5) p‖^2))) p) ∂energyMeasure μ H := by
  let C:=constant m U hm hρ hρhalf
  have ht:=(Classical.choose_spec (NativeConvexGammaTrace.exists_convex_trace m U hm hρ hρhalf)).2
  intro J sharp hsharp0 hsharp
  rw [NativeFourierIto.scalar_energy 𝓕 μ H J A0 A1]
  apply lintegral_mono_ae
  filter_upwards [NativeColumnProcesses.process_ae 𝓕 μ H K0 hK0 hE0,
    NativeColumnProcesses.process_ae 𝓕 μ H K1 hK1 hE1] with p ha0 ha1
  change A0 p=K0 p at ha0
  change A1 p=K1 p at ha1
  rw [ha0,ha1]
  apply ENNReal.ofReal_le_ofReal
  by_cases hp : p∈NativeGammaClock.window v b
  · simp only [NativeConvexGammaProcess.field,NativePairedGammaProcess.field,indicator_of_mem hp]
    letI : MeasurableSpace (ℝ≥0×Ω):=𝓕.predictable
    have hs:=ht Λ (NativeGammaClock.age v b p) hΛ (NativeGammaClock.age_pos v b p)
      (NativeGammaClock.age_le_one v b hb1 p) κ hκ
      (fun i=>NativeRandomRows.nativeRow (g i) p) (sharp p) (hsharp0 p hp) (hsharp p hp)
      (c0 p) (c1 p) (r0 p) (r1 p) (d p) (hd0 p) (hd1 p)
    have he:=fun (i:Fin 6) (f:ℝ≥0×Ω→EllipticField m U) (n:HaarNode)=>
      NativePairedGammaEnergy.single_apply 𝓕 v b hb1 hΛ hρ hρhalf hm B g hgm hg i p f (sharp p) (hsharp p hp i) n
    have he0:=fun (i:Fin 6) (n:HaarNode)=>
      NativePairedGammaEnergy.single_apply (m:=κ) (U:=κ) 𝓕 v b hb1 hΛ hρ hρhalf hκ B g hgm hg i p
        (fun _=>AdditiveHaarForcing.constantField κ hκ) (sharp p) (hsharp p hp i) n
    rw [HilbertColumns.norm_sq,HilbertColumns.norm_sq,←(HilbertColumns.summable_sq _).tsum_add (HilbertColumns.summable_sq _)]
    convert hs.2 using 1
    · apply tsum_congr
      intro n
      simp only [NativePairedColumnFields.paired,lp.coeFn_add,lp.coeFn_sub,lp.coeFn_smul,Pi.add_apply,Pi.sub_apply,Pi.smul_apply,he,he0]
    · rfl
  · simp only [NativeConvexGammaProcess.field,NativePairedGammaProcess.field,indicator_of_notMem hp,smul_zero,zero_add,norm_zero,
      zero_pow (by norm_num : (2:ℕ)≠0),zero_add,le_refl]

end SHE.NativeConvexGammaUniform
