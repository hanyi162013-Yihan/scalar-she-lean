module

public import SHE.ControlledThetaNativeGradient
public import SHE.ControlledThetaCompleteNativeWord
public import SHE.FullResidualFrameRange
public import SHE.ControlledThetaTwoFreshArrays
public import SHE.ControlledThetaNativeAssignments
public import SHE.TwoFreshCompleteWord
public import SHE.ControlledThetaConsistentNative
public import SHE.NativeFirstWholeComplete
public import SHE.NativeFirstOmittedPointwise
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

namespace SHE.ControlledThetaNativeCovariance
open Set MeasureTheory ProbabilityTheory StoppedFourier WordRecursion ControlledProfile ControlledReferenceLevel
  CutoffWordLevel CutoffWordHistories SmoothCylinders UniformSmooth CutoffCarriers PhysicalChainArrays
  PhysicalScoreChain ControlledOldIntervals ControlledReferenceWindows ControlledFamilyProfileForest
  ProjectedUncutWord CoveredControlledLaw CoveredHistoryGeometry
open scoped NNReal BigOperators
local instance controlledThetaNativeMean_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance controlledThetaNativeMean_circleSigma : MeasurableSpace CircleL2 := borel _
local instance controlledThetaNativeMean_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable (P : CanonicalCovariance.ProfileParameters) (hA : BoundedSmooth P.coefficient)
variable (Λ : ℝ) (v b : ℝ≥0) (hvb : v≤b)
variable {X : Type} [MeasurableSpace X] {n : ℕ} (Z : VariableObservations.Family X n)
variable (htarget : ∀ x i,(b:ℝ)≤(Z.observations x i).target)
variable (hstop : ∀ x i,(b:ℝ)≤(Z.observations x i).stop)
variable (F : X→WordRecursion.State n→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun q : X×WordRecursion.State n=>F q.1 q.2))
local notation "Base" => ControlledReferenceThetaGeometry.level P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm

local notation "Zero"=>Base (0,(0,0))

/-- The actual covariance leg of the original native-first kernel is
its complete true-score packet against the literal signed continuum
input. The physical row range is derived simultaneously for every
interpolation parameter and past input before either is selected. -/
theorem mark_all_parameters_ae
    (hages:∀x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (ρ:Measure X) [IsFiniteMeasure ρ] (k:ℕ):
    ∀ᵐh∂historyMeasure (referenceData P P.coefficient hA Λ 0 v b hvb (0,0)) ρ k,
      ∀p:ℝ×Inputs,∀q:ℝ,(v:ℝ)≤q → q<(carrier Zero k).terminal h →
      ∀(mean E:WordRecursion.State (n+k)),
      let Rnative:=NativeFirstScoreReserve.covariance P (stops (Base p) k h) (targets (Base p) k h)
        (centers (Base p) k h) q
      let C:=fullResidualCovariance (Base p) (oldProfile P Λ v p.2) k h q-Rnative
      E∈(Matrix.toEuclideanCLM (𝕜:=ℝ) Rnative).range →
      let A:=covariances (Base p) ((carrier (Base p) k).observations.observations h) (oldProfile P Λ v p.2) k h
      let D:=directions (Base p) ((carrier (Base p) k).observations.observations h) k h
      ∀e:StoppedGaussianFeatures.Domain→ℝ,
      FiniteWordScores.covarianceMark (StoppedGaussianFeatures.historyMeasure q) C
        (ObservationTimeShift.profile (v:ℝ) e)
        (StoppedGaussianFeatures.stoppedRow (stops (Base p) k h) (targets (Base p) k h) (centers (Base p) k h))
        (WeightedBorelAverage.average
          ((Measure.pi (fun j=>multivariateGaussian (0:WordRecursion.State (n+k)) (A j))).prod
            (multivariateGaussian (0:WordRecursion.State (n+k)) Rnative))
          (GaussianFixedFirstAverage.weight Rnative E (fun old=>∏j,MeasurableGaussianScores.secondScore (A j) (D j) (old j)))
          (GaussianFixedFirstAverage.shift (fun old=>∑j,old j)) (word (Base p) k h (fun i=>i))) mean=
      (1/2:ℝ)*∫x,e x*TwoFreshCompleteWord.value P Λ p.2.1 p.2.2 p.1 (q-(v:ℝ))
        (fun i=>stops Zero k h i-(v:ℝ)) (fun i=>targets Zero k h i-(v:ℝ)) (centers Zero k h)
        (fun j=>lower Zero k h j-(v:ℝ)) (fun j=>upper Zero k h j-(v:ℝ)) mean true
        (directions Zero ((carrier Zero k).observations.observations h) k h) E
        (StoppedGaussianFeatures.stoppedRow (fun i=>stops Zero k h i-(v:ℝ))
          (fun i=>targets Zero k h i-(v:ℝ)) (centers Zero k h) x)
        (rootSelector k (fun i=>i)) (leafIndex k (fun i=>i)) (F (rootParameter k h))
          ∂StoppedGaussianFeatures.historyMeasure (q-(v:ℝ)) := by
  filter_upwards [ControlledThetaNativeAssignments.score_all_parameters_ae
      P hA Λ v b hvb Z htarget hstop F hF hFm hages ρ k,
    ControlledThetaCompleteNativeWord.integral_all_parameters_ae
      P hA Λ v b hvb Z htarget hstop F hF hFm hages ρ k,
    ControlledThetaTwoFreshArrays.residual_all_parameters_ae
      P hA Λ v b hvb Z htarget hstop F hF hFm hages ρ k] with h hscore hcomplete hres
  intro p q hvq hqt mean E Rnative C hE A D e
  let σ:=fun i=>stops Zero k h i-(v:ℝ)
  let target:=fun i=>targets Zero k h i-(v:ℝ)
  let center:=centers Zero k h
  let lo:=fun j=>lower Zero k h j-(v:ℝ)
  let hi:=fun j=>upper Zero k h j-(v:ℝ)
  let row:=StoppedGaussianFeatures.stoppedRow σ target center
  let c:=fun a:ℝ×Inputs=>ControlledFixedReserve.coefficient P Λ a.2.1 a.2.2
    (NativeFirstScoreReserve.oldProfile P (fixedProfile P Λ a.2.1 a.2.2 lo hi)) a.1
  have hgeom(i):σ i≤target i:=sub_le_sub_right
    ((min_le_left _ _).trans (RecursiveScoreSupport.carrier_ages Zero hages k h i)) _
  have hdisjoint(j l)(hne:j≠l):hi j≤lo l ∨ hi l≤lo j:=
    RelativeHistoryGeometry.relative_disjoint Zero k h j l hne
  have hc(a:ℝ×Inputs):Measurable (c a):=
    ((ControlledProfile.profile_measurable P Λ a.2.1 a.2.2).comp
      (measurable_const.prodMk measurable_id)).sub
      (NativeFirstScoreReserve.oldProfile_measurable P (fixedProfile_measurable P Λ _ _ _ _))
  have hcb(a:ℝ×Inputs)(z):3*P.lower/8≤c a z ∧ c a z≤P.upper:=
    NativeFirstScoreReserve.residual_bounds P Λ a.2.1 a.2.2
      (fixedProfile_bounds P Λ _ _ _ _ hdisjoint) a.1 z
  have hrange:=FullResidualFrameRange.row_mem_all_ranges_ae σ target center hgeom (q-(v:ℝ)) c hc
    (by have := P.lower_pos; positivity : 0<3*P.lower/8) hcb
  have hcov:=hres p q hvq hqt.le
  have hage(i:Fin (n+k)):stops (Base p) k h i≤targets (Base p) k h i:=
    (min_le_left _ _).trans (RecursiveScoreSupport.carrier_ages (Base p) hages k h i)
  have hR:Rnative.PosSemidef:=NativeFirstScoreReserve.covariance_posSemidef P _ _ _ hage q
  have hC:C.PosSemidef:=by
    rw [show C=fullResidualCovariance (Base p) (oldProfile P Λ v p.2) k h q-
      NativeFirstScoreReserve.covariance P (stops (Base p) k h) (targets (Base p) k h)
        (centers (Base p) k h) q from rfl,hcov]
    exact NativeFirstScoreRepresentation.residual_posSemidef P Λ p.2.1 p.2.2
      (fixedProfile P Λ p.2.1 p.2.2 lo hi) (fixedProfile_measurable P Λ _ _ _ _)
      (fixedProfile_bounds P Λ _ _ _ _ hdisjoint) σ target center hgeom (q-(v:ℝ)) p.1
  have hrow(x):StoppedGaussianFeatures.stoppedRow
      (stops (Base p) k h) (targets (Base p) k h) (centers (Base p) k h)
      (ObservationTimeShift.translation (v:ℝ) x)=row x:=by
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
  have hxC:row x∈(Matrix.toEuclideanCLM (𝕜:=ℝ) C).range:=by
    rw [show C=fullResidualCovariance (Base p) (oldProfile P Λ v p.2) k h q-Rnative from rfl,hcov]
    exact hx p
  have hs:=hscore p true Rnative C hR hC E (row x) mean hE hxC
  have heq: (∫y,WeightedBorelAverage.average
      ((Measure.pi (fun j=>multivariateGaussian (0:WordRecursion.State (n+k)) (A j))).prod
        (multivariateGaussian (0:WordRecursion.State (n+k)) Rnative))
      (GaussianFixedFirstAverage.weight Rnative E (fun old=>∏j,MeasurableGaussianScores.secondScore (A j) (D j) (old j)))
      (GaussianFixedFirstAverage.shift (fun old=>∑j,old j)) (word (Base p) k h (fun i=>i)) (mean+y)*
      MeasurableGaussianScores.secondScore C (row x) y ∂multivariateGaussian 0 C)=
      WeightedBorelAverage.average (multivariateGaussian (0:WordRecursion.State (n+k)) C)
        (GaussianDependentScores.factor true C (row x)) id
        (WeightedBorelAverage.average
          ((Measure.pi (fun j=>multivariateGaussian (0:WordRecursion.State (n+k)) (A j))).prod
            (multivariateGaussian (0:WordRecursion.State (n+k)) Rnative))
          (GaussianFixedFirstAverage.weight Rnative E (fun old=>∏j,MeasurableGaussianScores.secondScore (A j) (D j) (old j)))
          (GaussianFixedFirstAverage.shift (fun old=>∑j,old j)) (word (Base p) k h (fun i=>i))) mean:=by
    apply integral_congr_ae
    exact ae_of_all _ (fun y=>mul_comm _ _)
  rw [heq,hs,hcomplete p q hvq hqt.le mean true E (row x)]

end SHE.ControlledThetaNativeCovariance
