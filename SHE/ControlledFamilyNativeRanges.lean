module
public import SHE.ControlledFamilyNativeLegs
public import SHE.PhysicalMeanEnergy
public import SHE.RelativeHistoryGeometry
public import SHE.ControlledFamilyThreeLeg
public import SHE.NativeDirectionKernelFTC

public import SHE.ControlledThetaStoppedCovariance
public import SHE.CarrierStopBounds
public import SHE.ControlledJointMarkedWord
public import SHE.ControlledJointMeanIdentity
public import SHE.NativeHeatSpan

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section

namespace SHE.ControlledFamilyNativeRanges
open Set MeasureTheory ProbabilityTheory AddCircle StoppedFourier WordRecursion ControlledProfile ControlledReferenceLevel
  CutoffWordLevel CutoffWordHistories SmoothCylinders UniformSmooth CutoffCarriers PhysicalChainArrays
  PhysicalScoreChain ControlledOldIntervals ControlledReferenceWindows ControlledFamilyProfileForest
  ProjectedUncutWord CoveredControlledLaw CoveredHistoryGeometry GaussianConvolution FiniteCenteredProduct
open scoped NNReal BigOperators
local instance controlledFamilyThreeLeg_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance controlledFamilyThreeLeg_circleSigma : MeasurableSpace CircleL2 := borel _
local instance controlledFamilyThreeLeg_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
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
local notation "Lo" => ControlledFamilyThreeLeg.lo P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "Hi" => ControlledFamilyThreeLeg.hi P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "LP" => ControlledFamilyThreeLeg.leafPoint P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "Law" => ControlledFamilyThreeLeg.oldLaw P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "Wgt" => ControlledFamilyThreeLeg.oldWeight P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "Root" => ControlledFamilyThreeLeg.scaledRoot P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "Leaf" => ControlledFamilyThreeLeg.coefficientLeaf A (n:=n)
open ControlledFamilyThreeLeg

/-- The actual original-stop damped current direction lies in the
three-eighths remaining covariance at EVERY theta. -/
theorem damped_direction_mem_range (hΛ:0≤Λ)
    (hroot:∀x i,(Z.observations x i).stop=(b:ℝ))
    (p:Inputs)(k:ℕ)(h:History X k)(q:ℝ)(hvq:(v:ℝ)≤q)
    (hqt:q<(carrier (Base (0,p)) k).terminal h)(D:CircleL2)(θ:ℝ):
    PhysicalMeanRange.dampedDirection (Sig p k h) (Tar p k h) (Cen p k h) (q-(v:ℝ)) Λ D∈
      (Matrix.toEuclideanCLM (𝕜:=ℝ) (ControlledFamilyNativeLegs.remaining
        P A hA Λ v b hvb Z htarget hstop F hF hFm p k h q θ)).range:=by
  let old:=fixedProfile P Λ p.1 p.2 (Lo p k h) (Hi p k h)
  have hdisjoint:∀j l:Fin k,j≠l→Hi p k h j≤Lo p k h l ∨ Hi p k h l≤Lo p k h j:=
    RelativeHistoryGeometry.relative_disjoint (Base (0,p)) k h
  have hold:Measurable old:=fixedProfile_measurable P Λ _ _ _ _
  have holdb:∀z,0≤old z∧old z≤P.lower/2:=fixedProfile_bounds P Λ _ _ _ _ hdisjoint
  have hages:∀x i,(Z.observations x i).stop≤(Z.observations x i).target:=by
    intro x i
    rw [hroot x i]
    exact htarget x i
  have hgeom:∀i,Sig p k h i≤Tar p k h i:=fun i=>sub_le_sub_right
    (RecursiveScoreSupport.carrier_ages (Base (0,p)) hages k h i) _
  have hgap:∀i,q-(v:ℝ)<Sig p k h i:=fun i=>sub_lt_sub_right
    (hqt.trans_le ((carrier (Base (0,p)) k).stops_after h i)) _
  obtain ⟨δ,hδ,hδi⟩:=PhysicalMeanRange.exists_positive_gap (fun i=>Sig p k h i-(q-(v:ℝ)))
    (fun i=>sub_pos.mpr (hgap i))
  have hmin:∀i,q-(v:ℝ)+δ≤Sig p k h i:=fun i=>by linarith [hδi i]
  let c:=ControlledFixedReserve.coefficient P Λ p.1 p.2 (NativeFirstScoreReserve.oldProfile P old) θ
  have hc:Measurable c:=((ControlledProfile.profile_measurable P Λ p.1 p.2).comp
    (measurable_const.prodMk measurable_id)).sub (NativeFirstScoreReserve.oldProfile_measurable P hold)
  have hfloor:0<3*P.lower/8:=by have:=P.lower_pos;positivity
  have hb(z):3*P.lower/8≤c z∧c z≤P.upper:=NativeFirstScoreReserve.residual_bounds P Λ p.1 p.2 holdb θ z
  exact PhysicalMeanRange.dampedDirection_mem_range (Sig p k h) (Tar p k h) (Cen p k h)
    (q-(v:ℝ)) Λ hΛ hgeom δ hδ hmin c hc P.upper (3*P.lower/8)
    (fun z=>⟨hfloor.le.trans (hb z).1,(hb z).2⟩) hfloor (fun z=>(hb z).1) D

end SHE.ControlledFamilyNativeRanges
