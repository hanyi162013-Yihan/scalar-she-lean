module

public import SHE.ControlledFamilyExpectedTransfer
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

namespace SHE.ControlledFamilyThetaFubini
open Set MeasureTheory ProbabilityTheory AddCircle StoppedFourier WordRecursion ControlledProfile ControlledReferenceLevel
  CutoffWordLevel CutoffWordHistories SmoothCylinders UniformSmooth CutoffCarriers PhysicalChainArrays
  PhysicalScoreChain ControlledOldIntervals ControlledReferenceWindows ControlledFamilyProfileForest
  ProjectedUncutWord CoveredControlledLaw CoveredHistoryGeometry GaussianConvolution FiniteCenteredProduct
open scoped NNReal BigOperators
local instance controlledFamilyThetaFubini_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance controlledFamilyThetaFubini_circleSigma : MeasurableSpace CircleL2 := borel _
local instance controlledFamilyThetaFubini_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
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

/-- The exact remaining deterministic applicability condition for
exchanging theta, original history and expectation is finite absolute
product mass of the LITERAL marked field. Joint Borel has already been
proved; no fixed-reference or a.e.-parameter substitution is used. -/
theorem expected_theta_transfer (hΛ : 0≤Λ)
    (hsmall : ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hroot : ∀ x i,(Z.observations x i).stop=(b:ℝ))
    (hspan : (b:ℝ)-(v:ℝ)≤P.horizon)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (ρ : Measure X) [IsFiniteMeasure ρ] (k : ℕ)
    (p : Ω→Inputs) (hp : Measurable p) (q : Ω→ℝ) (hq : Measurable q)
    (U D : Ω→CircleL2) (hU : Measurable U) (hD : Measurable D)
    (hfinite : HasFiniteIntegral (fun z : ℝ×(Ω×History X k)=>
      ActiveMark (p z.2.1) k z.2.2 (q z.2.1) (U z.2.1) (D z.2.1) z.1)
      ((volume.restrict (Ioc (0:ℝ) 1)).prod (μ.prod (historyMeasure R₀ ρ k)))) :
    IntervalIntegrable (fun θ=>∫ ω,(∫ h,ActiveMark (p ω) k h (q ω) (U ω) (D ω) θ
      ∂historyMeasure R₀ ρ k) ∂μ) volume 0 1 ∧
    (∫ θ in (0:ℝ)..1,∫ ω,(∫ h,ActiveMark (p ω) k h (q ω) (U ω) (D ω) θ
      ∂historyMeasure R₀ ρ k) ∂μ)=
      (∫ ω,(∫ h,Active (p ω) k h (q ω) (U ω) (D ω) 1 ∂historyMeasure R₀ ρ k) ∂μ)-
        (∫ ω,(∫ h,Active (p ω) k h (q ω) (U ω) (D ω) 0 ∂historyMeasure R₀ ρ k) ∂μ) := by
  let G : ℝ×(Ω×History X k)→ℝ :=fun z=>ActiveMark (p z.2.1) k z.2.2 (q z.2.1) (U z.2.1) (D z.2.1) z.1
  have hGm : Measurable G:=ControlledFamilyMarkedFields.active_mark_variable_measurable
    P A hA Λ v b hvb Z htarget hstop F hF hFm hΛ hsmall k
    (fun z : ℝ×(Ω×History X k)=>p z.2.1) (hp.comp measurable_snd.fst) (fun z=>z.2.2) measurable_snd.snd
    (fun z=>q z.2.1) (hq.comp measurable_snd.fst) (fun z=>U z.2.1) (fun z=>D z.2.1)
    (hU.comp measurable_snd.fst) (hD.comp measurable_snd.fst) Prod.fst measurable_fst
  have hGi : Integrable G ((volume.restrict (Ioc (0:ℝ) 1)).prod (μ.prod (historyMeasure R₀ ρ k))):=
    ⟨hGm.aestronglyMeasurable,hfinite⟩
  have hinner : (fun θ=>∫ ω,(∫ h,ActiveMark (p ω) k h (q ω) (U ω) (D ω) θ
      ∂historyMeasure R₀ ρ k) ∂μ)=ᵐ[volume.restrict (Ioc (0:ℝ) 1)]
      fun θ=>∫ z : Ω×History X k,G (θ,z) ∂μ.prod (historyMeasure R₀ ρ k) := by
    filter_upwards [hGi.prod_right_ae] with θ hθ
    exact (integral_prod _ hθ).symm
  have haverage:=hGi.integral_prod_left.congr hinner.symm
  have hinterval : IntervalIntegrable (fun θ=>∫ ω,(∫ h,ActiveMark (p ω) k h (q ω) (U ω) (D ω) θ
      ∂historyMeasure R₀ ρ k) ∂μ) volume 0 1 := by
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ)≤1)).mpr haverage
  refine ⟨hinterval,?_⟩
  calc
    _=(∫ θ in (0:ℝ)..1,∫ z : Ω×History X k,G (θ,z) ∂μ.prod (historyMeasure R₀ ρ k)) := by
      simp only [intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1)]
      exact integral_congr_ae hinner
    _=∫ z : Ω×History X k,(∫ θ in (0:ℝ)..1,G (θ,z)) ∂μ.prod (historyMeasure R₀ ρ k) := by
      apply intervalIntegral_integral_swap
      have he : Function.uncurry (fun x y=>G (x,y))=G := by
        funext z
        cases z
        rfl
      rw [he,Set.uIoc_of_le (by norm_num : (0:ℝ)≤1)]
      exact hGi
    _=(∫ ω,(∫ h,(∫ θ in (0:ℝ)..1,ActiveMark (p ω) k h (q ω) (U ω) (D ω) θ)
        ∂historyMeasure R₀ ρ k) ∂μ) := by
      apply integral_prod
      simpa only [intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1)] using hGi.integral_prod_right
    _=_:=(ControlledFamilyExpectedTransfer.expected_history_transfer
      P A hA Λ v b hvb Z htarget hstop F hF hFm hΛ hsmall hroot hspan μ ρ k p hp q hq U D hU hD 0 1).2

end SHE.ControlledFamilyThetaFubini
