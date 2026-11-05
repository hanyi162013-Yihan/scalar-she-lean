module

public import SHE.ControlledFamilyMarkedAverages
public import SHE.ControlledFamilyFrontFields
public import SHE.CarrierStopBounds
public import SHE.ControlledJointMarkedWord
public import SHE.ControlledJointMeanIdentity
public import SHE.NativeHeatSpan

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section

namespace SHE.ControlledFamilyExpectedTransfer
open Set MeasureTheory ProbabilityTheory AddCircle StoppedFourier WordRecursion ControlledProfile ControlledReferenceLevel
  CutoffWordLevel CutoffWordHistories SmoothCylinders UniformSmooth CutoffCarriers PhysicalChainArrays
  PhysicalScoreChain ControlledOldIntervals ControlledReferenceWindows ControlledFamilyProfileForest
  ProjectedUncutWord CoveredControlledLaw CoveredHistoryGeometry GaussianConvolution FiniteCenteredProduct
open scoped NNReal BigOperators
local instance controlledFamilyExpectedTransfer_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance controlledFamilyExpectedTransfer_circleSigma : MeasurableSpace CircleL2 := borel _
local instance controlledFamilyExpectedTransfer_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable (P : CanonicalCovariance.ProfileParameters) (A : ℝ→ℝ) (hA : BoundedSmooth A)
variable (Λ : ℝ) (v b : ℝ≥0) (hvb : v≤b)
variable {X : Type} [MeasurableSpace X] {n : ℕ} (Z : VariableObservations.Family X n)
variable (htarget : ∀ x i,(b:ℝ)≤(Z.observations x i).target)
variable (hstop : ∀ x i,(b:ℝ)≤(Z.observations x i).stop)
variable (F : X→WordRecursion.State n→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun q : X×WordRecursion.State n=>F q.1 q.2))
local notation "Base" => ControlledReferenceThetaGeometry.level P A hA Λ v b hvb Z htarget hstop F hF hFm

local notation "Sig" => ControlledFamilyThreeLeg.sigma P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "Tar" => ControlledFamilyThreeLeg.target P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "Cen" => ControlledFamilyThreeLeg.center P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "Value" => ControlledFamilyThreeLeg.value P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "Mark" => ControlledFamilyThreeLeg.mark P A hA Λ v b hvb Z htarget hstop F hF hFm

local notation "Active" => ControlledFamilyFrontFields.activeValue P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "Physical" => ControlledFamilyPhysicalTransfer.physicalMark P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "R₀" => referenceData P A hA Λ 0 v b hvb (0,0)

local notation "ActiveMark" => ControlledFamilyHistoryTransfer.activeMark P A hA Λ v b hvb Z htarget hstop F hF hFm

/-- Genuine product integrability of actual recursively generated
endpoints for arbitrary dependent random original-past/current inputs.
No moment bound on those inputs is needed for a bounded smooth root. -/
theorem endpoint_product_integrable {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (ρ : Measure X) [IsFiniteMeasure ρ] (k : ℕ)
    (p : Ω→Inputs) (hp : Measurable p) (q : Ω→ℝ) (hq : Measurable q)
    (U D : Ω→CircleL2) (hU : Measurable U) (hD : Measurable D) (θ : ℝ) :
    Integrable (fun z : Ω×History X k=>Active (p z.1) k z.2 (q z.1) (U z.1) (D z.1) θ)
      (μ.prod (historyMeasure R₀ ρ k)) := by
  obtain ⟨K,hKn,hK⟩:=ControlledFamilyFrontFields.actual_value_bound P A hA Λ v b hvb
    Z htarget hstop F hF hFm k
  have hm:=ControlledFamilyFrontFields.active_value_measurable P A hA Λ v b hvb
    Z htarget hstop F hF hFm k
    (fun z : Ω×History X k=>p z.1) (hp.comp measurable_fst) Prod.snd measurable_snd
    (fun z=>q z.1) (hq.comp measurable_fst) (fun z=>U z.1) (fun z=>D z.1)
    (hU.comp measurable_fst) (hD.comp measurable_fst) (fun _=>θ) measurable_const
  have hi:=(integrable_const K : Integrable (fun _ : Ω=>K) μ).mul_prod
    (UncutHistoryMass.weight_integrable (Base (0,(0,0))) ρ k)
  apply hi.mono' hm.aestronglyMeasurable
  apply ae_of_all
  intro z
  simp only [Real.norm_eq_abs]
  unfold ControlledFamilyFrontFields.activeValue
  split_ifs with ha
  · exact hK (p z.1) θ z.2 (q z.1) (U z.1) (D z.1)
  · exact abs_zero.le.trans (mul_nonneg hKn (UncutSmoothWords.weight_nonneg _ _ _))

/-- Expected original-history FTC for arbitrary measurable random-past
and actual current inputs, including event-restricted or finite weighted
outer laws. The interpolation integral remains inside its actual
history section; no unjustified theta/history exchange is used. -/
theorem expected_history_transfer (hΛ : 0≤Λ)
    (hsmall : ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hroot : ∀ x i,(Z.observations x i).stop=(b:ℝ))
    (hspan : (b:ℝ)-(v:ℝ)≤P.horizon)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (ρ : Measure X) [IsFiniteMeasure ρ] (k : ℕ)
    (p : Ω→Inputs) (hp : Measurable p) (q : Ω→ℝ) (hq : Measurable q)
    (U D : Ω→CircleL2) (hU : Measurable U) (hD : Measurable D) (r t : ℝ) :
    Integrable (fun ω=>∫ h,(∫ θ in r..t,ActiveMark (p ω) k h (q ω) (U ω) (D ω) θ)
      ∂historyMeasure R₀ ρ k) μ ∧
    (∫ ω,(∫ h,(∫ θ in r..t,ActiveMark (p ω) k h (q ω) (U ω) (D ω) θ)
      ∂historyMeasure R₀ ρ k) ∂μ)=
      (∫ ω,(∫ h,Active (p ω) k h (q ω) (U ω) (D ω) t ∂historyMeasure R₀ ρ k) ∂μ)-
        (∫ ω,(∫ h,Active (p ω) k h (q ω) (U ω) (D ω) r ∂historyMeasure R₀ ρ k) ∂μ) := by
  have ht:=(endpoint_product_integrable P A hA Λ v b hvb Z htarget hstop F hF hFm
    μ ρ k p hp q hq U D hU hD t).integral_prod_left
  have hr:=(endpoint_product_integrable P A hA Λ v b hvb Z htarget hstop F hF hFm
    μ ρ k p hp q hq U D hU hD r).integral_prod_left
  have he : (fun ω=>∫ h,(∫ θ in r..t,ActiveMark (p ω) k h (q ω) (U ω) (D ω) θ)
      ∂historyMeasure R₀ ρ k)=
      fun ω=>(∫ h,Active (p ω) k h (q ω) (U ω) (D ω) t ∂historyMeasure R₀ ρ k)-
        (∫ h,Active (p ω) k h (q ω) (U ω) (D ω) r ∂historyMeasure R₀ ρ k) := by
    funext ω
    exact (ControlledFamilyHistoryTransfer.history_integrated_transfer
      P A hA Λ v b hvb Z htarget hstop F hF hFm hΛ hsmall hroot hspan ρ k
      (fun _=>p ω) measurable_const (fun _=>q ω) measurable_const
      (fun _=>U ω) (fun _=>D ω) measurable_const measurable_const r t).2
  rw [he]
  exact ⟨ht.sub hr,integral_sub ht hr⟩

end SHE.ControlledFamilyExpectedTransfer
