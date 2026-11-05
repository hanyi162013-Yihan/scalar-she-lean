module

public import SHE.NativePairedColumnFields
public import SHE.NativeGammaClock

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
namespace SHE.NativePairedGammaProcess
open Set MeasureTheory PredictableL2 StoppedFourier FiniteHaar NativeMultiplierHilbertColumns
open scoped ENNReal NNReal
local instance nativePairedGammaProcess_period : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance nativePairedGammaProcess_unit : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance nativePairedGammaProcess_sigma : MeasurableSpace CircleL2:=borel _
local instance nativePairedGammaProcess_borel : BorelSpace CircleL2:=⟨rfl⟩
local instance nativePairedGammaProcess_unitSigma : MeasurableSpace CircleHeat.CircleL2:=borel _
local instance nativePairedGammaProcess_unitBorel : BorelSpace CircleHeat.CircleL2:=⟨rfl⟩
local instance nativePairedGammaProcess_second : SecondCountableTopology CircleL2:=
  (_root_.fourierBasis (T:=2*Real.pi)).repr.toHomeomorph.secondCountableTopology
local instance nativePairedGammaProcess_spaceSigma : MeasurableSpace Space:=borel _
local instance nativePairedGammaProcess_spaceBorel : BorelSpace Space:=⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
variable (H v b : ℝ≥0) (hbH : b≤H) (hb1 : (b:ℝ)≤1)
variable {Λ ρ m U : ℝ} (hΛ : 1≤Λ) (hρ : 0≤ρ) (hρhalf : ρ<1/2) (hm : 0<m)
variable (B : ℝ) (g : Fin 6→(ℝ≥0×Ω)×HeatCircle→ℂ)
variable (hgm : ∀ i,@Measurable _ _ (𝓕.predictable.prod inferInstance) _ (g i))
variable (hg : ∀ i p x,‖g i (p,x)‖≤B)

def field (c0 c1 r0 r1 : ℝ≥0×Ω→EllipticField m U) : ℝ≥0×Ω→Space:=by
  letI : MeasurableSpace (ℝ≥0×Ω):=𝓕.predictable
  exact (NativeGammaClock.window v b).indicator
    (NativePairedColumnFields.paired hΛ hρ hρhalf hm B g hgm hg
      (NativeGammaClock.age v b) (NativeGammaClock.age_measurable 𝓕 v b)
      (NativeGammaClock.age_pos v b) (NativeGammaClock.age_le_one v b hb1) c0 c1 r0 r1)

theorem field_predictable (c0 c1 r0 r1 : ℝ≥0×Ω→EllipticField m U)
    (hc0 : Measurable[𝓕.predictable] c0) (hc1 : Measurable[𝓕.predictable] c1)
    (hr0 : Measurable[𝓕.predictable] r0) (hr1 : Measurable[𝓕.predictable] r1) :
    StronglyMeasurable[𝓕.predictable] (field 𝓕 v b hb1 hΛ hρ hρhalf hm B g hgm hg c0 c1 r0 r1) := by
  letI : MeasurableSpace (ℝ≥0×Ω):=𝓕.predictable
  exact (NativePairedColumnFields.paired_measurable hΛ hρ hρhalf hm B g hgm hg
    (NativeGammaClock.age v b) (NativeGammaClock.age_measurable 𝓕 v b)
    (NativeGammaClock.age_pos v b) (NativeGammaClock.age_le_one v b hb1)
    c0 c1 r0 r1 hc0 hc1 hr0 hr1).stronglyMeasurable.indicator (NativeGammaClock.window_measurable 𝓕 v b)

include hbH in
/-- The literal whole paired column field has finite stochastic energy
on the SAME full-H predictable space. This is derived from ellipticity
and the integrable native heat singularity, rather than supplied as a
Gamma applicability premise. -/
theorem field_energy (c0 c1 r0 r1 : ℝ≥0×Ω→EllipticField m U)
    (hc0 : Measurable[𝓕.predictable] c0) (hc1 : Measurable[𝓕.predictable] c1)
    (hr0 : Measurable[𝓕.predictable] r0) (hr1 : Measurable[𝓕.predictable] r1) :
    Integrable (fun p=>‖field 𝓕 v b hb1 hΛ hρ hρhalf hm B g hgm hg c0 c1 r0 r1 p‖^2)
      (energyMeasure μ H) := by
  letI : Nonempty Ω:=nonempty_of_isProbabilityMeasure μ
  let C:=16*U*(1+2*HeatTrace.fractionalGaussianIntegral ρ)*B^2
  have hC : 0≤C:=mul_nonneg (mul_nonneg (mul_nonneg (by norm_num)
    (elliptic_upper_nonneg (c0 (0,Classical.arbitrary Ω)).1 m U hm (c0 (0,Classical.arbitrary Ω)).2.2))
    (by linarith [HeatTrace.fractionalGaussianIntegral_pos hρhalf])) (sq_nonneg _)
  have hi:=(NativeGammaClock.power_integrable 𝓕 v b μ H hbH hb1 hρ).const_mul C
  have hs:=(field_predictable 𝓕 v b hb1 hΛ hρ hρhalf hm B g hgm hg c0 c1 r0 r1 hc0 hc1 hr0 hr1).mono
    (predictable_le_product 𝓕)
  apply hi.mono' (hs.norm.pow 2).aestronglyMeasurable
  filter_upwards with p
  simp only [Pi.pow_apply]
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  by_cases hp : p∈NativeGammaClock.window v b
  · simp only [field,indicator_of_mem hp]
    letI : MeasurableSpace (ℝ≥0×Ω):=𝓕.predictable
    have he:=NativePairedColumnFields.paired_energy hΛ hρ hρhalf hm B g hgm hg
      (NativeGammaClock.age v b) (NativeGammaClock.age_measurable 𝓕 v b)
      (NativeGammaClock.age_pos v b) (NativeGammaClock.age_le_one v b hb1) c0 c1 r0 r1 p
    exact he.trans_eq (show 16*U*((1+2*HeatTrace.fractionalGaussianIntegral ρ)*(NativeGammaClock.age v b p)^(ρ-1/2))*B^2=C*(NativeGammaClock.age v b p)^(ρ-1/2) from by dsimp only [C];ring)
  · simp only [field,indicator_of_notMem hp,norm_zero,zero_pow (by norm_num : (2:ℕ)≠0),mul_zero,le_refl]

end SHE.NativePairedGammaProcess
