module
public import SHE.ControlledOrdinaryNoise

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
namespace SHE.ControlledOrdinaryAverage
open Set MeasureTheory StoppedFourier WordRecursion ControlledProfile ControlledReferenceLevel
  CutoffWordLevel CutoffWordHistories SmoothCylinders UniformSmooth Filter Topology
open scoped NNReal
local instance controlledOrdinaryAverage_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance controlledOrdinaryAverage_sigma : MeasurableSpace CircleL2 := borel _
local instance controlledOrdinaryAverage_borel : BorelSpace CircleL2 := ⟨rfl⟩
variable (P : CanonicalCovariance.ProfileParameters) (A : ℝ→ℝ) (hA : BoundedSmooth A)
variable (Λ θ : ℝ) (v b : ℝ≥0) (hvb : v≤b)
variable {Y : Type} [MeasurableSpace Y] {n : ℕ} (Z : VariableObservations.Family Y n)
variable (htarget : ∀ y i,(b:ℝ)≤(Z.observations y i).target)
variable (hstop : ∀ y i,(b:ℝ)≤(Z.observations y i).stop)
variable (F : Y→WordRecursion.State n→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun q : Y×WordRecursion.State n => F q.1 q.2))
local notation "Base" => ControlledReferenceFamilyLevel.level P A hA Λ θ v b hvb Z htarget hstop F hF hFm
local notation "R₀" => ControlledReferenceLevel.referenceData P A hA Λ θ v b hvb (0,0)
variable {Ω : Type} [MeasurableSpace Ω]
variable {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {H : ℝ≥0} {κ : ℝ} {a : ℝ→ℝ} {ell M : ℝ}
variable (m : TwoChannelCutoffModel.Model 𝓕 μ H κ a ell M)

/-- The original history measure is independent of the past-state
reference input; no random measure substitution is being made. -/
theorem measure_eq (ν : Measure Y) (p p' : Inputs) (k : ℕ) :
    historyMeasure (referenceData P A hA Λ θ v b hvb p) ν k=
      historyMeasure (referenceData P A hA Λ θ v b hvb p') ν k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change (historyMeasure _ ν k).prod (nodeMeasure _)=(historyMeasure _ ν k).prod (nodeMeasure _)
    rw [ih]
    rfl

def average (ν : Measure Y) (p : Inputs) (k : ℕ) (ω : Ω) : ℝ :=
  ∫h,ControlledOrdinaryNoise.value P A hA Λ θ v b hvb Z htarget hstop F hF hFm m p k h ω
    ∂historyMeasure R₀ ν k

theorem average_measurable (ν : Measure Y) [IsFiniteMeasure ν] (p : Inputs) (k : ℕ) :
    Measurable (average P A hA Λ θ v b hvb Z htarget hstop F hF hFm m ν p k) :=
  (OrdinaryUncutNoise.value_measurable m (Base p) k).stronglyMeasurable.integral_prod_left'.measurable

/-- A single deterministic bound works for every reference past input,
after averaging the integrable original heat-history weight. -/
theorem average_bound (ν : Measure Y) [IsFiniteMeasure ν] (k : ℕ) :
    ∃B:ℝ,0≤B∧∀p ω,‖average P A hA Λ θ v b hvb Z htarget hstop F hF hFm m ν p k ω‖≤B := by
  obtain ⟨C,hC,hCb⟩:=ControlledOrdinaryNoise.value_bound P A hA Λ θ v b hvb Z htarget hstop F hF hFm m k
  let W:=UncutSmoothWords.weight (Base (0,0)) k
  have hW:Integrable W (historyMeasure R₀ ν k):=UncutHistoryMass.weight_integrable (Base (0,0)) ν k
  refine ⟨C*(∫h,W h ∂historyMeasure R₀ ν k),mul_nonneg hC (integral_nonneg (UncutSmoothWords.weight_nonneg (Base (0,0)) k)),fun p ω=>?_⟩
  have hb:=norm_integral_le_of_norm_le (hW.const_mul C) (Filter.Eventually.of_forall (fun h=>hCb p h ω))
  simpa only [average,integral_const_mul] using hb

variable (hsmall : ProfileStability.memoryConstant P.lower P.holder P.exponent*
  ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
include hsmall in
theorem average_continuous (hΛ : 0≤Λ) (ν : Measure Y) [IsFiniteMeasure ν] (k : ℕ) (ω : Ω) :
    Continuous (fun p:Inputs=>average P A hA Λ θ v b hvb Z htarget hstop F hF hFm m ν p k ω) := by
  obtain ⟨C,hC,hCb⟩:=ControlledOrdinaryNoise.value_bound P A hA Λ θ v b hvb Z htarget hstop F hF hFm m k
  let W:=UncutSmoothWords.weight (Base (0,0)) k
  have hW:Integrable W (historyMeasure R₀ ν k):=UncutHistoryMass.weight_integrable (Base (0,0)) ν k
  apply continuous_of_dominated (bound:=fun h=>C*W h)
  · intro p
    have hm:=OrdinaryUncutNoise.value_measurable m (Base p) k
    have hmap:Measurable (fun h:History Y k=>(h,ω)):=measurable_id.prodMk measurable_const
    exact (hm.comp hmap).aestronglyMeasurable
  · exact fun p=>Filter.Eventually.of_forall (fun h=>hCb p h ω)
  · exact hW.const_mul C
  · exact Filter.Eventually.of_forall (fun h=>ControlledOrdinaryNoise.value_continuous P A hA Λ θ v b hvb
      Z htarget hstop F hF hFm m hsmall hΛ k h ω)

end SHE.ControlledOrdinaryAverage
