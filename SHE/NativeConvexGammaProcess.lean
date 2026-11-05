module

public import SHE.NativePairedGammaProcess
public import SHE.NativeConvexGammaTrace
public import SHE.NativeGammaClock

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
namespace SHE.NativeConvexGammaProcess
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

variable (d:ℝ≥0×Ω→ℝ) (hd:Measurable[𝓕.predictable] d) (hd0:∀p,0≤d p) (hd1:∀p,d p≤1)

def field (c0 c1 r0 r1:ℝ≥0×Ω→EllipticField m U) (p:ℝ≥0×Ω):Space:=
  d p • NativePairedGammaProcess.field 𝓕 v b hb1 hΛ hρ hρhalf hm B g hgm hg c0 c1 r0 r1 p+
    (1-d p) • NativePairedGammaProcess.field 𝓕 v b hb1 hΛ hρ hρhalf hm B g hgm hg c0 c0 r0 r1 p

include hd in
theorem field_predictable (c0 c1 r0 r1:ℝ≥0×Ω→EllipticField m U)
    (hc0:Measurable[𝓕.predictable] c0) (hc1:Measurable[𝓕.predictable] c1)
    (hr0:Measurable[𝓕.predictable] r0) (hr1:Measurable[𝓕.predictable] r1):
    StronglyMeasurable[𝓕.predictable] (field 𝓕 v b hb1 hΛ hρ hρhalf hm B g hgm hg d c0 c1 r0 r1):=by
  have h0:=NativePairedGammaProcess.field_predictable 𝓕 v b hb1 hΛ hρ hρhalf hm B g hgm hg c0 c1 r0 r1 hc0 hc1 hr0 hr1
  have h1:=NativePairedGammaProcess.field_predictable 𝓕 v b hb1 hΛ hρ hρhalf hm B g hgm hg c0 c0 r0 r1 hc0 hc0 hr0 hr1
  exact (hd.stronglyMeasurable.smul h0).add ((measurable_const.sub hd).stronglyMeasurable.smul h1)

include hd hd0 hd1 hbH in
/-- The literal convex-right native columns have finite ORIGINAL
stochastic energy, derived from the two actual endpoint column fields. -/
theorem field_energy (c0 c1 r0 r1:ℝ≥0×Ω→EllipticField m U)
    (hc0:Measurable[𝓕.predictable] c0) (hc1:Measurable[𝓕.predictable] c1)
    (hr0:Measurable[𝓕.predictable] r0) (hr1:Measurable[𝓕.predictable] r1):
    Integrable (fun p=>‖field 𝓕 v b hb1 hΛ hρ hρhalf hm B g hgm hg d c0 c1 r0 r1 p‖^2) (energyMeasure μ H):=by
  have h0:=NativePairedGammaProcess.field_energy 𝓕 μ H v b hbH hb1 hΛ hρ hρhalf hm B g hgm hg c0 c1 r0 r1 hc0 hc1 hr0 hr1
  have h1:=NativePairedGammaProcess.field_energy 𝓕 μ H v b hbH hb1 hΛ hρ hρhalf hm B g hgm hg c0 c0 r0 r1 hc0 hc0 hr0 hr1
  have hs:=(field_predictable 𝓕 v b hb1 hΛ hρ hρhalf hm B g hgm hg d hd c0 c1 r0 r1 hc0 hc1 hr0 hr1).mono (predictable_le_product 𝓕)
  apply (h0.add h1).mono' (hs.norm.pow 2).aestronglyMeasurable
  filter_upwards with p
  rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  have hn:=NativeConvexGammaTrace.norm_convex_sq (hd0 p) (hd1 p)
    (NativePairedGammaProcess.field 𝓕 v b hb1 hΛ hρ hρhalf hm B g hgm hg c0 c1 r0 r1 p)
    (NativePairedGammaProcess.field 𝓕 v b hb1 hΛ hρ hρhalf hm B g hgm hg c0 c0 r0 r1 p)
  exact hn.trans (add_le_add (mul_le_of_le_one_left (sq_nonneg _) (hd1 p))
    (mul_le_of_le_one_left (sq_nonneg _) (by linarith [hd0 p])))

/-- Exact four-term physical columns: ONLY the second current right
factor is the convex Haar interpolation; reference factors are literal. -/
theorem field_on_window (c0 c1 r0 r1:ℝ≥0×Ω→EllipticField m U) (p:ℝ≥0×Ω) (hp:p∈NativeGammaClock.window v b):
    field 𝓕 v b hb1 hΛ hρ hρhalf hm B g hgm hg d c0 c1 r0 r1 p=
      (letI:MeasurableSpace (ℝ≥0×Ω):=𝓕.predictable
       let single:=NativePairedColumnFields.single hΛ hρ hρhalf hm B g hgm hg
         (NativeGammaClock.age v b) (NativeGammaClock.age_measurable 𝓕 v b)
         (NativeGammaClock.age_pos v b) (NativeGammaClock.age_le_one v b hb1)
       single 0 c0 p-single 3 r0 p-((1-d p) • single 2 c0 p+d p • single 2 c1 p)+single 5 r1 p):=by
  letI:MeasurableSpace (ℝ≥0×Ω):=𝓕.predictable
  simp only [field,NativePairedGammaProcess.field,Set.indicator_of_mem hp,NativePairedColumnFields.paired]
  module

end SHE.NativeConvexGammaProcess
