module

public import SHE.BoundedThetaRelativeSecondScore
public import SHE.ControlledResidualGaussianSegment
public import SHE.ObservationMarkTimeShift
public import SHE.BoundedOldAverage
public import SHE.ControlledThetaRelativeArrays

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.ControlledThetaGaussianDifference
open Set MeasureTheory ProbabilityTheory StoppedFourier WordRecursion ControlledProfile ControlledReferenceLevel
  CutoffWordLevel CutoffWordHistories SmoothCylinders UniformSmooth CutoffCarriers PhysicalChainArrays
  PhysicalScoreChain ControlledOldIntervals ControlledReferenceWindows ControlledFamilyProfileForest
  ProjectedUncutWord CoveredControlledLaw CoveredHistoryGeometry
open scoped NNReal
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
local instance : MeasurableSpace CircleL2 := borel _
local instance : BorelSpace CircleL2 := ⟨rfl⟩
variable (P : CanonicalCovariance.ProfileParameters) (hA : BoundedSmooth P.coefficient)
variable (Λ : ℝ) (v b : ℝ≥0) (hvb : v ≤ b)
variable {X : Type} [MeasurableSpace X] (Z : VariableObservations.Family X 1)
variable (htarget : ∀ x i, (b : ℝ) ≤ (Z.observations x i).target)
variable (hstop : ∀ x i, (b : ℝ) ≤ (Z.observations x i).stop)
variable (F : X → WordRecursion.State 1 → ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun q : X × WordRecursion.State 1 => F q.1 q.2))
local notation "Base" => ControlledReferenceThetaGeometry.level P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm
local notation "Zero" => Base (0, (0, 0))
local notation "Cov" => BoundedThetaRelativeSecondScore.covariance P hA Λ v b hvb Z htarget hstop F hF hFm

/-- Finite comparison of the ACTUAL future Gaussian laws of the whole
recursive word, with its own fixed endpoint baseline and mean. All
measurability/boundedness of the old word, covariance segment, clock
translation and endpoint applicability are derived on ONE original event
before choosing any random past input or interpolation parameter. -/
theorem covariance_ftc_all_parameters_ae
    (hages : ∀ x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (ρ : Measure X) [IsFiniteMeasure ρ] (k : ℕ) :
    ∀ᵐ h ∂historyMeasure (referenceData P P.coefficient hA Λ 0 v b hvb (0,0)) ρ k,
      ∀ p : ℝ×Inputs,∀ q : ℝ,(v:ℝ)≤q→q≤(carrier Zero k).terminal h→
      ∀ θ₀ θ₁ : ℝ,∀ mean : WordRecursion.State (1+k),
      let W:=oldAverage (Base p) (oldProfile P Λ v p.2) k h
      let B₀:=fullResidualCovariance (Base (θ₀,p.2)) (oldProfile P Λ v p.2) k h q
      let B₁:=fullResidualCovariance (Base (θ₁,p.2)) (oldProfile P Λ v p.2) k h q
      let mark:=fun ζ=>FiniteWordScores.covarianceMark (StoppedGaussianFeatures.historyMeasure q)
        ((1-ζ) • B₀+ζ • B₁)
        (ObservationTimeShift.profile (v:ℝ) (fun z=>ControlledProfile.profile P Λ p.2.1 p.2.2 (θ₁,z)-
          ControlledProfile.profile P Λ p.2.1 p.2.2 (θ₀,z)))
        (StoppedGaussianFeatures.stoppedRow (stops (Base p) k h) (targets (Base p) k h) (centers (Base p) k h))
        W mean
      IntervalIntegrable mark volume 0 1 ∧ (∫ ζ in (0:ℝ)..1,mark ζ)=
        GaussianConvolution.gaussianAverage B₁ W mean-GaussianConvolution.gaussianAverage B₀ W mean := by
  filter_upwards [ControlledThetaRelativeArrays.full_covariance_relative_fixed_ae
    P hA Λ v b hvb Z htarget hstop F hF hFm hages ρ k] with h hres
  intro p q hvq hqt θ₀ θ₁ mean W B₀ B₁ mark
  let σ:=fun i=>stops Zero k h i-(v:ℝ)
  let target:=fun i=>targets Zero k h i-(v:ℝ)
  let center:=centers Zero k h
  let lo:=fun j=>lower Zero k h j-(v:ℝ)
  let hi:=fun j=>upper Zero k h j-(v:ℝ)
  let e:=fun z=>ControlledProfile.profile P Λ p.2.1 p.2.2 (θ₁,z)-
    ControlledProfile.profile P Λ p.2.1 p.2.2 (θ₀,z)
  have hgeom (i) : σ i≤target i:=sub_le_sub_right
    ((min_le_left _ _).trans (RecursiveScoreSupport.carrier_ages Zero hages k h i)) _
  have hdisjoint (j l) (hne:j≠l) : hi j≤lo l ∨ hi l≤lo j :=
    RelativeHistoryGeometry.relative_disjoint Zero k h j l hne
  have hW : Measurable W := by
    convert! (oldAverage_measurable (Base p) (oldProfile P Λ v p.2)
      ((ControlledReferenceWindows.coefficient_section_measurable P Λ 0 v p.2).const_mul (fraction P)) k).comp
      (measurable_const.prodMk measurable_id) using 1
  obtain ⟨BW,_,hBW⟩:=oldAverage_bounded (Base p) (oldProfile P Λ v p.2) k h
  have hftc:=ControlledResidualGaussianSegment.covariance_ftc P Λ p.2.1 p.2.2 lo hi hdisjoint
    σ target center hgeom (q-(v:ℝ)) θ₀ θ₁ W hW BW hBW mean
  have hcov₀:=hres (θ₀,p.2) q (v.2.trans hvq) hqt
  have hcov₁:=hres (θ₁,p.2) q (v.2.trans hvq) hqt
  let M:=fun ζ=>StoppedGaussianFeatures.stoppedCovariance σ target center
    (BoundedWindowDecomposition.residual P Λ p.2.1 p.2.2 lo hi
      (BoundedWindowDecomposition.convexProfile P Λ p.2.1 p.2.2 θ₀ θ₁ ζ)) (q-(v:ℝ))
  have hm (ζ) : mark ζ=FiniteWordScores.covarianceMark
      (StoppedGaussianFeatures.historyMeasure (q-(v:ℝ))) (M ζ) e
        (StoppedGaussianFeatures.stoppedRow σ target center) W mean := by
    dsimp only [mark,B₀,B₁]
    rw [hcov₀,hcov₁,←ConvexResidualCovariance.covariance P Λ p.2.1 p.2.2 lo hi hdisjoint
      σ target center hgeom (q-(v:ℝ)) θ₀ θ₁ ζ]
    rw [ControlledThetaRelativeDerivative.stops_eq P hA Λ v b hvb Z htarget hstop F hF hFm p (0,(0,0)) k h,
      ControlledThetaRelativeDerivative.targets_eq P hA Λ v b hvb Z htarget hstop F hF hFm p (0,(0,0)) k h,
      ControlledThetaRelativeDerivative.centers_eq P hA Λ v b hvb Z htarget hstop F hF hFm p (0,(0,0)) k h]
    have hh:=ObservationTimeShift.covarianceMark_translation (v:ℝ) (q-(v:ℝ)) σ target center (M ζ) e W mean
    simpa only [σ,target,sub_add_cancel] using hh
  have hmfun:=funext hm
  rw [hmfun]
  have he₀ : B₀=ControlledFixedReserve.covariance P Λ p.2.1 p.2.2
      (fixedProfile P Λ p.2.1 p.2.2 lo hi) σ target center (q-(v:ℝ)) θ₀ := hcov₀
  have he₁ : B₁=ControlledFixedReserve.covariance P Λ p.2.1 p.2.2
      (fixedProfile P Λ p.2.1 p.2.2 lo hi) σ target center (q-(v:ℝ)) θ₁ := hcov₁
  rw [he₀,he₁]
  simpa only [M,e] using hftc

end SHE.ControlledThetaGaussianDifference
