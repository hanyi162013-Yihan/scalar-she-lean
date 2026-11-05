module

public import SHE.ControlledFamilyMeanLeg
public import SHE.ControlledThetaPhysicalMarkFields
public import SHE.ControlledFamilyFrontFields
public import SHE.ControlledProfileFamilies
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

namespace SHE.ControlledFamilyProfileMarkFields
open Set MeasureTheory ProbabilityTheory AddCircle StoppedFourier WordRecursion ControlledProfile ControlledReferenceLevel
  CutoffWordLevel CutoffWordHistories SmoothCylinders UniformSmooth CutoffCarriers PhysicalChainArrays
  PhysicalScoreChain ControlledOldIntervals ControlledReferenceWindows ControlledFamilyProfileForest
  ProjectedUncutWord CoveredControlledLaw CoveredHistoryGeometry GaussianConvolution FiniteCenteredProduct
open scoped NNReal BigOperators
local instance controlledFamilyProfileMarkFields_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance controlledFamilyProfileMarkFields_circleSigma : MeasurableSpace CircleL2 := borel _
local instance controlledFamilyProfileMarkFields_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
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

/-- The actual fixed old reference profile is jointly Borel in arbitrary
original-past inputs and the absolute physical space-time point. -/
theorem old_profile_variable_measurable {W : Type} [MeasurableSpace W]
    (p : W→Inputs) (hp : Measurable p) :
    Measurable (fun z : W×StoppedGaussianFeatures.Domain=>oldProfile P Λ v (p z.1) z.2) := by
  have hm:=ControlledThetaWordFields.coefficient_joint_measurable P Λ v
  have hmap : Measurable (fun z : W×StoppedGaussianFeatures.Domain=>(((0:ℝ),p z.1),z.2)) :=
    (measurable_const.prodMk (hp.comp measurable_fst)).prodMk measurable_snd
  have hh:=(hm.comp hmap).const_mul (fraction P)
  exact hh

/-- The actual signed profile direction at original past v, jointly in
theta, original inputs, current parameters and physical space-time. -/
theorem profile_direction_variable_measurable (hΛ : 0≤Λ)
    (hsmall : ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    {W : Type} [MeasurableSpace W] (p : W→Inputs) (hp : Measurable p)
    (θ : W→ℝ) (hθ : Measurable θ) :
    Measurable (fun z : W×StoppedGaussianFeatures.Domain=>
      ObservationTimeShift.profile (v:ℝ) (fun r=>ControlledProfile.derivative P Λ (p z.1).1 (p z.1).2 (r,θ z.1)) z.2) := by
  have hm:=ControlledProfile.derivative_joint_measurable P hΛ hsmall
  have hmap : Measurable (fun z : W×StoppedGaussianFeatures.Domain=>
      ((p z.1,(z.2.1-(v:ℝ),z.2.2)),θ z.1)) :=
    ((hp.comp measurable_fst).prodMk ((measurable_snd.fst.sub_const (v:ℝ)).prodMk measurable_snd.snd)).prodMk
      (hθ.comp measurable_fst)
  have hh:=hm.comp hmap
  exact hh

/-- All original full-profile baseline derivatives form a joint Borel
vector for the ACTUAL recursively generated carrier family. -/
theorem baseline_direction_variable_measurable (hΛ : 0≤Λ)
    (hsmall : ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    {W : Type} [MeasurableSpace W] (k : ℕ)
    (p : W→Inputs) (hp : Measurable p) (h : W→History X k) (hh : Measurable h)
    (θ : W→ℝ) (hθ : Measurable θ) :
    Measurable (fun w=>fun j=>ControlledFiniteWord.baselineDerivatives P Λ (p w).1 (p w).2
      (LP (p w) k (h w)) j (θ w)) := by
  apply Measurable.of_eval
  intro j
  have hlo:=(lower_measurable (Base (0,(0,0))) k j).comp hh
  have hsp:=(space_measurable k j).comp hh
  have hm:=ControlledProfile.derivative_joint_measurable P hΛ hsmall
  have hmap : Measurable (fun w=>((p w,(lower (Base (0,(0,0))) k (h w) j-(v:ℝ),space k (h w) j)),θ w)) :=
    (hp.prodMk ((hlo.sub_const (v:ℝ)).prodMk hsp)).prodMk hθ
  have hg:=hm.comp hmap
  convert hg using 1
  funext w
  unfold ControlledFiniteWord.baselineDerivatives ControlledFamilyThreeLeg.leafPoint ControlledFamilyThreeLeg.lo
  rw [ControlledThetaPhysicalGeometry.lower_eq P A hA Λ v b hvb Z htarget hstop F hF hFm
    (0,p w) (0,(0,0)) k (h w)]
  rfl

end SHE.ControlledFamilyProfileMarkFields
