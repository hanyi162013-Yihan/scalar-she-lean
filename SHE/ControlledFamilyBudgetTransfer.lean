module

public import SHE.ControlledFamilyLegFubini
public import SHE.ThreePieceProductIntegral
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

namespace SHE.ControlledFamilyBudgetTransfer
open Set MeasureTheory ProbabilityTheory AddCircle StoppedFourier WordRecursion ControlledProfile ControlledReferenceLevel
  CutoffWordLevel CutoffWordHistories SmoothCylinders UniformSmooth CutoffCarriers PhysicalChainArrays
  PhysicalScoreChain ControlledOldIntervals ControlledReferenceWindows ControlledFamilyProfileForest
  ProjectedUncutWord CoveredControlledLaw CoveredHistoryGeometry GaussianConvolution FiniteCenteredProduct
open scoped NNReal BigOperators
local instance controlledFamilyBudgetTransfer_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance controlledFamilyBudgetTransfer_circleSigma : MeasurableSpace CircleL2 := borel _
local instance controlledFamilyBudgetTransfer_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
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

local notation "Mean"=>ControlledFamilyActualTransfer.mean P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "LP"=>ControlledFamilyThreeLeg.leafPoint P A hA Λ v b hvb Z htarget hstop F hF hFm

local notation "Cov"=>ControlledFamilyLegFubini.covariance P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "MeanLeg"=>ControlledFamilyLegFubini.mean P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "BaseLeg"=>ControlledFamilyLegFubini.baseline P A hA Λ v b hvb Z htarget hstop F hF hFm

/-- The actual three-leg section estimates discharge the absolute
product-mass condition of the canonical finite-history FTC. The result
exchanges theta, expectation and original history with every literal
mark and its original sign/normalization retained. -/
theorem expected_transfer_of_leg_budgets (hΛ : 0≤Λ)
    (hsmall : ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hroot : ∀ x i,(Z.observations x i).stop=(b:ℝ))
    (hspan : (b:ℝ)-(v:ℝ)≤P.horizon)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (ρ : Measure X) [IsFiniteMeasure ρ] (k : ℕ)
    (p : Ω→Inputs) (hp : Measurable p) (q : Ω→ℝ) (hq : Measurable q)
    (U D : Ω→CircleL2) (hU : Measurable U) (hD : Measurable D)
    (Ec Em Eb : ℝ→ℝ)
    (hEc : IntervalIntegrable Ec volume 0 1) (hEm : IntervalIntegrable Em volume 0 1)
    (hEb : IntervalIntegrable Eb volume 0 1)
    (hC : ∀ᵐ θ ∂volume.restrict (Ioc (0:ℝ) 1),
      Integrable (fun z : Ω×History X k=>Cov (p z.1) k z.2 (q z.1) (U z.1) (D z.1) θ)
        (μ.prod (historyMeasure R₀ ρ k)) ∧
      (∫ z : Ω×History X k,|Cov (p z.1) k z.2 (q z.1) (U z.1) (D z.1) θ|
        ∂μ.prod (historyMeasure R₀ ρ k))≤Ec θ)
    (hM : ∀ᵐ θ ∂volume.restrict (Ioc (0:ℝ) 1),
      Integrable (fun z : Ω×History X k=>MeanLeg (p z.1) k z.2 (q z.1) (U z.1) (D z.1) θ)
        (μ.prod (historyMeasure R₀ ρ k)) ∧
      (∫ z : Ω×History X k,|MeanLeg (p z.1) k z.2 (q z.1) (U z.1) (D z.1) θ|
        ∂μ.prod (historyMeasure R₀ ρ k))≤Em θ)
    (hB : ∀ᵐ θ ∂volume.restrict (Ioc (0:ℝ) 1),
      Integrable (fun z : Ω×History X k=>BaseLeg (p z.1) k z.2 (q z.1) (U z.1) (D z.1) θ)
        (μ.prod (historyMeasure R₀ ρ k)) ∧
      (∫ z : Ω×History X k,|BaseLeg (p z.1) k z.2 (q z.1) (U z.1) (D z.1) θ|
        ∂μ.prod (historyMeasure R₀ ρ k))≤Eb θ) :
    IntervalIntegrable (fun θ=>∫ ω,(∫ h,ActiveMark (p ω) k h (q ω) (U ω) (D ω) θ
      ∂historyMeasure R₀ ρ k) ∂μ) volume 0 1 ∧
    (∫ θ in (0:ℝ)..1,∫ ω,(∫ h,ActiveMark (p ω) k h (q ω) (U ω) (D ω) θ
      ∂historyMeasure R₀ ρ k) ∂μ)=
      (∫ ω,(∫ h,Active (p ω) k h (q ω) (U ω) (D ω) 1 ∂historyMeasure R₀ ρ k) ∂μ)-
        (∫ ω,(∫ h,Active (p ω) k h (q ω) (U ω) (D ω) 0 ∂historyMeasure R₀ ρ k) ∂μ) := by
  have hi:=(ControlledFamilyLegFubini.product_integrable_of_leg_budgets
    P A hA Λ v b hvb Z htarget hstop F hF hFm hΛ hsmall μ ρ k p hp q hq U D hU hD
    Ec Em Eb hEc hEm hEb hC hM hB).1
  exact ControlledFamilyThetaFubini.expected_theta_transfer
    P A hA Λ v b hvb Z htarget hstop F hF hFm hΛ hsmall hroot hspan μ ρ k p hp q hq U D hU hD
    hi.hasFiniteIntegral

end SHE.ControlledFamilyBudgetTransfer
