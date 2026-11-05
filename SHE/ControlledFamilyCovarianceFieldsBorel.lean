module

public import SHE.ControlledFamilyLegFubini
public import SHE.ControlledFamilyProfileMarkFields
public import SHE.ControlledFamilyHistoryTransfer
public import SHE.ControlledFamilyCovarianceLeg
public import SHE.ControlledFamilyBaselineLeg
public import SHE.ControlledFamilyActualTransfer
public import SHE.ChainAssignedRepresentation
public import SHE.CarrierStopBounds
public import SHE.ControlledJointMarkedWord
public import SHE.ControlledJointMeanIdentity
public import SHE.NativeHeatSpan

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section

namespace SHE.ControlledFamilyCovarianceFieldsBorel
open Set MeasureTheory ProbabilityTheory AddCircle StoppedFourier WordRecursion ControlledProfile ControlledReferenceLevel
  CutoffWordLevel CutoffWordHistories SmoothCylinders UniformSmooth CutoffCarriers PhysicalChainArrays
  PhysicalScoreChain ControlledOldIntervals ControlledReferenceWindows ControlledFamilyProfileForest
  ProjectedUncutWord CoveredControlledLaw CoveredHistoryGeometry GaussianConvolution FiniteCenteredProduct
open scoped NNReal BigOperators
local instance controlledFamilyCovarianceFieldsBorel_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance controlledFamilyCovarianceFieldsBorel_circleSigma : MeasurableSpace CircleL2 := borel _
local instance controlledFamilyCovarianceFieldsBorel_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
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

local notation "Lo" => ControlledFamilyThreeLeg.lo P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "Hi" => ControlledFamilyThreeLeg.hi P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "Law" => ControlledFamilyThreeLeg.oldLaw P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "Wgt" => ControlledFamilyThreeLeg.oldWeight P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "Root" => ControlledFamilyThreeLeg.scaledRoot P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "Leaf" => ControlledFamilyThreeLeg.coefficientLeaf A (n:=n)
local notation "LP" => ControlledFamilyThreeLeg.leafPoint P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "Mean" => ControlledFamilyActualTransfer.mean P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "TME" => ControlledReferenceThetaGeometry.carrier_terminal_eq P A hA Λ v b hvb Z htarget hstop F hF hFm

/-- The literal continuum covariance leg is jointly Borel with all
reference inputs, theta, original history and current states/time. -/
theorem covariance_variable_measurable (hΛ : 0≤Λ)
    (hsmall : ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    {W : Type} [MeasurableSpace W] (k : ℕ)
    (p : W→Inputs) (hp : Measurable p) (h : W→History X k) (hh : Measurable h)
    (q : W→ℝ) (hq : Measurable q) (U D : W→CircleL2) (hU : Measurable U) (hD : Measurable D)
    (θ : W→ℝ) (hθ : Measurable θ) :
    Measurable (fun w=>ControlledFamilyLegFubini.covariance P A hA Λ v b hvb Z htarget hstop F hF hFm
      (p w) k (h w) (q w) (U w) (D w) (θ w)) := by
  classical
  let a : W→ℝ×Inputs :=fun w=>(θ w,p w)
  have ha : Measurable a:=hθ.prodMk hp
  let m : W→WordRecursion.State (n+k) :=fun w=>Mean (p w) k (h w) (q w) (U w) (D w) (θ w)
  have hm : Measurable m:=ControlledFamilyFrontFields.mean_measurable
    P A hA Λ v b hvb Z htarget hstop F hF hFm k p hp h hh q hq U D hU hD θ hθ
  have hc:=ControlledFamilyProfileMarkFields.old_profile_variable_measurable P Λ v p hp
  have he:=ControlledFamilyProfileMarkFields.profile_direction_variable_measurable
    P Λ v hΛ hsmall p hp θ hθ
  have hb:=ControlledThetaPhysicalMarkFields.covariance_point_variable_measurable
    P A hA Λ v b hvb Z htarget hstop F hF hFm k a ha h hh q hq
    (fun z=>oldProfile P Λ v (p z.1) z.2)
    (fun z=>ObservationTimeShift.profile (v:ℝ)
      (fun r=>ControlledProfile.derivative P Λ (p z.1).1 (p z.1).2 (r,θ z.1)) z.2) hc he m hm
  let g : W→ℝ:=fun w=>ActualCovarianceMarkFields.point (Base (a w)) (oldProfile P Λ v (p w))
    (ObservationTimeShift.profile (v:ℝ)
      (fun r=>ControlledProfile.derivative P Λ (p w).1 (p w).2 (r,θ w))) k (q w) (m w) (h w)
  have hgm : Measurable g:=hb
  have hT:=ControlledThetaWordFields.terminal_joint_measurable P A hA Λ v b hvb Z htarget hstop F hF hFm k
  have hmap0 : Measurable (fun w=>(((0:ℝ),p w),h w)) := (measurable_const.prodMk hp).prodMk hh
  have ht0:=hT.comp hmap0
  have hs : MeasurableSet {w : W | (v:ℝ)≤q w ∧ q w<(carrier (Base (0,p w)) k).terminal (h w)} :=
    (measurableSet_le measurable_const hq).inter (measurableSet_lt hq ht0)
  have hhg : Measurable (fun w=>if (v:ℝ)≤q w ∧ q w<(carrier (Base (0,p w)) k).terminal (h w) then g w else 0) :=
    hgm.ite hs measurable_const
  exact hhg

end SHE.ControlledFamilyCovarianceFieldsBorel
