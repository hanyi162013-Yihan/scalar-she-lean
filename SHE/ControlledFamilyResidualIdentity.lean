module

public import SHE.ControlledFamilyValueIdentity
public import SHE.ControlledJointDirectionRange
public import SHE.CarrierStopBounds
public import SHE.ControlledJointMarkedWord
public import SHE.ControlledJointMeanIdentity
public import SHE.NativeHeatSpan

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section

namespace SHE.ControlledFamilyResidualIdentity
open Set MeasureTheory ProbabilityTheory AddCircle StoppedFourier WordRecursion ControlledProfile ControlledReferenceLevel
  CutoffWordLevel CutoffWordHistories SmoothCylinders UniformSmooth CutoffCarriers PhysicalChainArrays
  PhysicalScoreChain ControlledOldIntervals ControlledReferenceWindows ControlledFamilyProfileForest
  ProjectedUncutWord CoveredControlledLaw CoveredHistoryGeometry GaussianConvolution FiniteCenteredProduct
open scoped NNReal BigOperators
local instance controlledFamilyResidualIdentity_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance controlledFamilyResidualIdentity_circleSigma : MeasurableSpace CircleL2 := borel _
local instance controlledFamilyResidualIdentity_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
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
local notation "Value" => ControlledFamilyThreeLeg.value P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "TME" => ControlledReferenceThetaGeometry.carrier_terminal_eq P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "OME" => ControlledReferenceThetaGeometry.carrier_observations_eq P A hA Λ v b hvb Z htarget hstop F hF hFm

/-- Pointwise covariance identification on the same all-parameter history
event. The original separate stops are covered exactly, never replaced
by the common minimum target. -/
theorem residual_eq_all_parameters_ae
    (hroot : ∀ x i,(Z.observations x i).stop=(b:ℝ))
    (ρ : Measure X) [IsFiniteMeasure ρ] (k : ℕ) :
    ∀ᵐ h ∂historyMeasure (referenceData P A hA Λ 0 v b hvb (0,0)) ρ k,
      ∀ p : Inputs,∀ θ q : ℝ,(v:ℝ)≤q → q≤(carrier (Base (0,p)) k).terminal h →
      fullResidualCovariance (Base (θ,p)) (oldProfile P Λ v p) k h q=
        ControlledFixedReserve.covariance P Λ p.1 p.2 (fixedProfile P Λ p.1 p.2 (Lo p k h) (Hi p k h))
          (Sig p k h) (Tar p k h) (StoppedGaussianScore.nativeCenter (Cen p k h)) (q-(v:ℝ)) θ := by
  have hages : ∀ x i,(Z.observations x i).stop≤(Z.observations x i).target := by
    intro x i
    rw [hroot x i]
    exact htarget x i
  filter_upwards [ControlledThetaStoppedCovariance.relative_all_parameters_ae
    P A hA Λ v b hvb Z htarget hstop F hF hFm hages ρ k] with h hh
  intro p θ q hvq hqt
  have hqt' : q≤(carrier (Base (θ,p)) k).terminal h := by
    rw [TME (θ,p) (0,p) k]
    exact hqt
  have he:=hh (θ,p) q (v.2.trans hvq) hqt'
  rw [ControlledFamilyValueIdentity.relative_stops_eq P A hA Λ v b hvb Z htarget hstop F hF hFm hroot,
    ControlledFamilyValueIdentity.relative_targets_eq P A hA Λ v b hvb Z htarget hstop F hF hFm,
    ControlledFamilyValueIdentity.centers_eq P A hA Λ v b hvb Z htarget hstop F hF hFm,
    ControlledFamilyValueIdentity.relative_lower_eq P A hA Λ v b hvb Z htarget hstop F hF hFm,
    ControlledFamilyValueIdentity.relative_upper_eq P A hA Λ v b hvb Z htarget hstop F hF hFm] at he
  exact he

/-- Literal original-stop mean directions are in the actual remaining
covariance range for every interpolation and every current difference,
on one common original history event. -/
theorem damped_range_all_parameters_ae (hΛ : 0≤Λ)
    (hroot : ∀ x i,(Z.observations x i).stop=(b:ℝ))
    (ρ : Measure X) [IsFiniteMeasure ρ] (k : ℕ) :
    ∀ᵐ h ∂historyMeasure (referenceData P A hA Λ 0 v b hvb (0,0)) ρ k,
      ∀ p : Inputs,∀ θ q : ℝ,(v:ℝ)≤q → q<(carrier (Base (0,p)) k).terminal h →
      ∀ D : CircleL2,PhysicalMeanRange.dampedDirection (Sig p k h) (Tar p k h) (Cen p k h) (q-(v:ℝ)) Λ D∈
        (Matrix.toEuclideanCLM (𝕜:=ℝ) (fullResidualCovariance (Base (θ,p)) (oldProfile P Λ v p) k h q)).range := by
  have hages : ∀ x i,(Z.observations x i).stop≤(Z.observations x i).target := by
    intro x i
    rw [hroot x i]
    exact htarget x i
  filter_upwards [residual_eq_all_parameters_ae P A hA Λ v b hvb Z htarget hstop F hF hFm hroot ρ k]
    with h hh
  intro p θ q hvq hqt D
  rw [hh p θ q hvq hqt.le]
  have hgeom:=RecursiveScoreSupport.carrier_ages (Base (0,p)) hages k h
  have hs : ∀ i,Sig p k h i≤Tar p k h i:=fun i=>sub_le_sub_right (hgeom i) _
  have hgap : ∀ i,q-(v:ℝ)<Sig p k h i := by
    intro i
    exact sub_lt_sub_right (hqt.trans_le ((carrier (Base (0,p)) k).stops_after h i)) _
  have hd : ∀ j l : Fin k,j≠l → Hi p k h j≤Lo p k h l ∨ Hi p k h l≤Lo p k h j := by
    intro j l hjl
    rcases disjoint (Base (0,p)) k h j l hjl with hj|hl
    · exact Or.inl (sub_le_sub_right hj _)
    · exact Or.inr (sub_le_sub_right hl _)
  exact ControlledJointWeightedWord.jointDirection_mem_range_at P hΛ p.1 p.2 D
    (fixedProfile P Λ p.1 p.2 (Lo p k h) (Hi p k h))
    (fixedProfile_measurable P Λ p.1 p.2 (Lo p k h) (Hi p k h))
    (half_lt_self P.lower_pos) (fixedProfile_bounds P Λ p.1 p.2 (Lo p k h) (Hi p k h) hd)
    (Sig p k h) (Tar p k h) (Cen p k h) (q-(v:ℝ)) hgap hs θ

end SHE.ControlledFamilyResidualIdentity
