module

public import SHE.ControlledThetaRelativeSecondScore
public import SHE.ControlledThetaRelativeArrays
public import SHE.FullResidualFrameRange
public import SHE.RelativeHistoryGeometry
public import SHE.PointwiseCompleteCovarianceInput
public import SHE.ControlledThetaRelativeDerivative
public import SHE.ControlledThetaStoppedCovariance
public import SHE.ControlledThetaAssigned
public import SHE.VaryingFullResidualMoments
public import SHE.ControlledThetaSupported
public import SHE.FullResidualStoppedCovariance
public import SHE.ControlledProfileTimeShift

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section

namespace SHE.ControlledThetaRelativeCovarianceMark
open Set MeasureTheory ProbabilityTheory StoppedFourier WordRecursion ControlledProfile ControlledReferenceLevel
  CutoffWordLevel CutoffWordHistories SmoothCylinders UniformSmooth CutoffCarriers PhysicalChainArrays
  PhysicalScoreChain ControlledOldIntervals ControlledReferenceWindows ControlledFamilyProfileForest
  ProjectedUncutWord CoveredControlledLaw CoveredHistoryGeometry
open scoped NNReal
local instance controlledThetaRelativeCovarianceMark_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance controlledThetaRelativeCovarianceMark_circleSigma : MeasurableSpace CircleL2 := borel _
local instance controlledThetaRelativeCovarianceMark_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable (P : CanonicalCovariance.ProfileParameters) (hA : BoundedSmooth P.coefficient)
variable (Λ : ℝ) (v b : ℝ≥0) (hvb : v≤b)
variable {X : Type} [MeasurableSpace X] {n : ℕ} (Z : VariableObservations.Family X n)
variable (htarget : ∀ x i,(b:ℝ)≤(Z.observations x i).target)
variable (hstop : ∀ x i,(b:ℝ)≤(Z.observations x i).stop)
variable (F : X→WordRecursion.State n→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun q : X×WordRecursion.State n=>F q.1 q.2))
local notation "Base" => ControlledReferenceThetaGeometry.level P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm



local notation "Zero" => Base (0,(0,0))

/-- Exact actual covariance mark as a relative-time complete Gaussian
assignment integral. The stopped-row range is PROVED on one common
physical input event for every theta/past input, using a fixed positive
floor before introducing the parameter. Thus this identity may be used
at genuinely random observed-past data. -/
theorem mark_all_parameters_ae
    (hages : ∀ x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (ρ : Measure X) [IsFiniteMeasure ρ] (k : ℕ) :
    ∀ᵐ h ∂historyMeasure (referenceData P P.coefficient hA Λ 0 v b hvb (0,0)) ρ k,
      ∀ p : ℝ×Inputs,∀ q : ℝ,(v:ℝ)≤q→q<(carrier Zero k).terminal h→
      ∀ e : StoppedGaussianFeatures.Domain→ℝ,∀ mean : WordRecursion.State (n+k),
      FiniteWordScores.covarianceMark (StoppedGaussianFeatures.historyMeasure q)
        (fullResidualCovariance (Base p) (oldProfile P Λ v p.2) k h q)
        (ObservationTimeShift.profile (v:ℝ) e)
        (StoppedGaussianFeatures.stoppedRow (stops (Base p) k h) (targets (Base p) k h) (centers (Base p) k h))
        (oldAverage (Base p) (oldProfile P Λ v p.2) k h) mean=
      (1/2:ℝ)*∫ x,e x*PointwiseCompleteGaussianWord.value P Λ p.2.1 p.2.2 p.1 (q-(v:ℝ))
        (fun i=>stops Zero k h i-(v:ℝ)) (fun i=>targets Zero k h i-(v:ℝ)) (centers Zero k h)
        (fun j=>lower Zero k h j-(v:ℝ)) (fun j=>upper Zero k h j-(v:ℝ)) mean true
        (directions Zero ((carrier Zero k).observations.observations h) k h)
        (StoppedGaussianFeatures.stoppedRow (fun i=>stops Zero k h i-(v:ℝ))
          (fun i=>targets Zero k h i-(v:ℝ)) (centers Zero k h) x)
        (rootSelector k (fun i=>i)) (leafIndex k (fun i=>i)) (F (rootParameter k h))
          ∂StoppedGaussianFeatures.historyMeasure (q-(v:ℝ)) := by
  filter_upwards [ControlledThetaRelativeSecondScore.score_all_parameters_ae
      P hA Λ v b hvb Z htarget hstop F hF hFm hages ρ k,
    ControlledThetaRelativeArrays.full_covariance_relative_fixed_ae
      P hA Λ v b hvb Z htarget hstop F hF hFm hages ρ k] with h hrep hres
  intro p q hvq hqt e mean
  let σ:=fun i=>stops Zero k h i-(v:ℝ)
  let target:=fun i=>targets Zero k h i-(v:ℝ)
  let center:=centers Zero k h
  let lo:=fun j=>lower Zero k h j-(v:ℝ)
  let hi:=fun j=>upper Zero k h j-(v:ℝ)
  let row:=StoppedGaussianFeatures.stoppedRow σ target center
  let c:=fun a : ℝ×Inputs=>ControlledFixedReserve.coefficient P Λ a.2.1 a.2.2
    (fixedProfile P Λ a.2.1 a.2.2 lo hi) a.1
  have hgeom (i) : σ i≤target i:=sub_le_sub_right
    ((min_le_left _ _).trans (RecursiveScoreSupport.carrier_ages Zero hages k h i)) _
  have hdisjoint (j l) (hne:j≠l) : hi j≤lo l ∨ hi l≤lo j:=
    RelativeHistoryGeometry.relative_disjoint Zero k h j l hne
  have hc (a : ℝ×Inputs) : Measurable (c a):=
    ((ControlledProfile.profile_measurable P Λ a.2.1 a.2.2).comp
      (measurable_const.prodMk measurable_id)).sub (fixedProfile_measurable P Λ a.2.1 a.2.2 lo hi)
  have hcb (a : ℝ×Inputs) (z) : P.lower/2≤c a z ∧ c a z≤P.upper := by
    have hh:=ControlledFixedReserve.coefficient_bounds P Λ a.2.1 a.2.2
      (fixedProfile P Λ a.2.1 a.2.2 lo hi)
      (fixedProfile_bounds P Λ a.2.1 a.2.2 lo hi hdisjoint) a.1 z
    constructor <;> linarith
  have hrange:=FullResidualFrameRange.row_mem_all_ranges_ae σ target center hgeom (q-(v:ℝ)) c hc
    (half_pos P.lower_pos) hcb
  have htme:=ControlledReferenceThetaGeometry.carrier_terminal_eq
    P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm p (0,(0,0)) k h
  have hqp : q<(carrier (Base p) k).terminal h:=by simpa only [htme] using hqt
  have hcov:=hres p q (v.2.trans hvq) hqt.le
  have hrow (x) : StoppedGaussianFeatures.stoppedRow
      (stops (Base p) k h) (targets (Base p) k h) (centers (Base p) k h)
      (ObservationTimeShift.translation (v:ℝ) x)=row x := by
    rw [ControlledThetaRelativeDerivative.stops_eq P hA Λ v b hvb Z htarget hstop F hF hFm p (0,(0,0)) k h,
      ControlledThetaRelativeDerivative.targets_eq P hA Λ v b hvb Z htarget hstop F hF hFm p (0,(0,0)) k h,
      ControlledThetaRelativeDerivative.centers_eq P hA Λ v b hvb Z htarget hstop F hF hFm p (0,(0,0)) k h]
    have hh:=ObservationTimeShift.stoppedRow_translation (v:ℝ) σ target center x
    simpa only [σ,target,sub_add_cancel] using hh
  unfold FiniteWordScores.covarianceMark
  rw [←show (q-(v:ℝ))+(v:ℝ)=q by ring,
    ←ObservationTimeShift.integral_history_translation (v:ℝ) (q-(v:ℝ))]
  simp only [sub_add_cancel]
  congr 1
  apply integral_congr_ae
  filter_upwards [hrange] with x hx
  rw [ObservationTimeShift.profile_translation,hrow]
  have hd : row x∈(Matrix.toEuclideanCLM (𝕜:=ℝ)
      (fullResidualCovariance (Base p) (oldProfile P Λ v p.2) k h q)).range := by
    rw [hcov]
    exact hx p
  have hh:=hrep p q hvq hqp (row x) mean hd
  change e x*(∫ y,oldAverage (Base p) (oldProfile P Λ v p.2) k h (mean+y)*
    MeasurableGaussianScores.secondScore (fullResidualCovariance (Base p) (oldProfile P Λ v p.2) k h q)
      (row x) y ∂multivariateGaussian 0 (fullResidualCovariance (Base p) (oldProfile P Λ v p.2) k h q))=_
  rw [hh]
  rfl

end SHE.ControlledThetaRelativeCovarianceMark

