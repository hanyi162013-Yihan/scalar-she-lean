module

public import SHE.NativeFirstMeanHessian
public import SHE.ControlledThetaNativeMean
public import SHE.ControlledThetaCompleteNativeWord
public import SHE.ControlledThetaNativeGradient
public import SHE.ProfileReserveTotalMark
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

namespace SHE.ControlledThetaNativeMeanHessian
open Set MeasureTheory ProbabilityTheory StoppedFourier WordRecursion ControlledProfile ControlledReferenceLevel
  CutoffWordLevel CutoffWordHistories SmoothCylinders UniformSmooth CutoffCarriers PhysicalChainArrays
  PhysicalScoreChain ControlledOldIntervals ControlledReferenceWindows ControlledFamilyProfileForest
  ProjectedUncutWord CoveredControlledLaw CoveredHistoryGeometry
open scoped NNReal BigOperators
local instance controlledThetaNativeMeanHessian_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance controlledThetaNativeMeanHessian_circleSigma : MeasurableSpace CircleL2 := borel _
local instance controlledThetaNativeMeanHessian_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable (P : CanonicalCovariance.ProfileParameters) (hA : BoundedSmooth P.coefficient)
variable (Λ : ℝ) (v b : ℝ≥0) (hvb : v≤b)
variable {X : Type} [MeasurableSpace X] {n : ℕ} (Z : VariableObservations.Family X n)
variable (htarget : ∀ x i,(b:ℝ)≤(Z.observations x i).target)
variable (hstop : ∀ x i,(b:ℝ)≤(Z.observations x i).stop)
variable (F : X→WordRecursion.State n→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun q : X×WordRecursion.State n=>F q.1 q.2))
local notation "Base" => ControlledReferenceThetaGeometry.level P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm

local notation "Zero"=>Base (0,(0,0))

/-- The actual original backward Hessian is the native-R-first,
C-first complete mean packet, on one event before all random past and
current substitutions. This supplies its literal joint Borel version. -/
theorem hessian_all_parameters_ae
    (hages:∀x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (ρ:Measure X) [IsFiniteMeasure ρ] (k:ℕ):
    ∀ᵐh∂historyMeasure (referenceData P P.coefficient hA Λ 0 v b hvb (0,0)) ρ k,
      ∀p:ℝ×Inputs,∀q:ℝ,(v:ℝ)≤q→q<(carrier Zero k).terminal h→
      ∀(mean E V:WordRecursion.State (n+k)),
      let Rnative:=NativeFirstScoreReserve.covariance P (stops (Base p) k h) (targets (Base p) k h)
        (centers (Base p) k h) q
      let C:=fullResidualCovariance (Base p) (oldProfile P Λ v p.2) k h q-Rnative
      E∈(Matrix.toEuclideanCLM (𝕜:=ℝ) Rnative).range→
      V∈(Matrix.toEuclideanCLM (𝕜:=ℝ) C).range→
      GaussianTaylor.hessian (GaussianConvolution.gaussianAverage (WordRecursion.covariance
        (referenceData P P.coefficient hA Λ p.1 v b hvb p.2).reference
        ((carrier (Base p) k).observations.observations h) q ((carrier (Base p) k).terminal h))
        (UncutSmoothWords.test (Base p) k h)) mean V E=
      TwoFreshCompleteWord.value P Λ p.2.1 p.2.2 p.1 (q-(v:ℝ))
        (fun i=>stops Zero k h i-(v:ℝ)) (fun i=>targets Zero k h i-(v:ℝ)) (centers Zero k h)
        (fun j=>lower Zero k h j-(v:ℝ)) (fun j=>upper Zero k h j-(v:ℝ)) mean false
        (directions Zero ((carrier Zero k).observations.observations h) k h) E V
        (rootSelector k (fun i=>i)) (leafIndex k (fun i=>i)) (F (rootParameter k h)):=by
  filter_upwards [ControlledThetaNativeGradient.gradient_all_parameters_ae
      P hA Λ v b hvb Z htarget hstop F hF hFm hages ρ k,
    ControlledThetaConsistentKernel.kernel_all_parameters_ae
      P hA Λ v b hvb Z htarget hstop F hF hFm hages ρ k,
    ControlledThetaNativeMean.affine_mean_all_parameters_ae
      P hA Λ v b hvb Z htarget hstop F hF hFm hages ρ k,
    ControlledThetaTwoFreshArrays.residual_all_parameters_ae
      P hA Λ v b hvb Z htarget hstop F hF hFm hages ρ k,
    ControlledThetaSupported.physical_chain_all_parameters_ae
      P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm hages ρ k] with h hgrad hpacket hmean hres hchain
  intro p q hvq hqt mean E V Rnative C hE hV
  obtain ⟨chain,_,_,hphysical⟩:=hchain p
  let A:=covariances (Base p) ((carrier (Base p) k).observations.observations h) (oldProfile P Λ v p.2) k h
  let D:=directions (Base p) ((carrier (Base p) k).observations.observations h) k h
  let μold:=Measure.pi (fun j=>multivariateGaussian (0:WordRecursion.State (n+k)) (A j))
  let w:=fun old:Fin k→WordRecursion.State (n+k)=>∏j,MeasurableGaussianScores.secondScore (A j) (D j) (old j)
  let shift:=fun old:Fin k→WordRecursion.State (n+k)=>∑j,old j
  let G:=word (Base p) k h (fun i=>i)
  let inner:=WeightedBorelAverage.average (μold.prod (multivariateGaussian (0:WordRecursion.State (n+k)) Rnative))
    (GaussianFixedFirstAverage.weight Rnative E w) (GaussianFixedFirstAverage.shift shift) G
  let Original:=GaussianConvolution.gaussianAverage (WordRecursion.covariance
    (referenceData P P.coefficient hA Λ p.1 v b hvb p.2).reference
    ((carrier (Base p) k).observations.observations h) q ((carrier (Base p) k).terminal h))
    (UncutSmoothWords.test (Base p) k h)
  have hw:Integrable w μold:=Integrable.fintype_prod (fun j=>
    GaussianVectorFractions.gaussian_secondScore_integrable (A j) (D j))
  have hwm:Measurable w:=Finset.measurable_prod Finset.univ (fun j _=>
    (GaussianDependentScores.factor_measurable true (A j) (D j)).comp (measurable_pi_apply j))
  have hs:Measurable shift:=by fun_prop
  have hG:Measurable G:=(word_measurable (Base p) k (fun i=>i)).comp
    (measurable_const.prodMk measurable_id)
  obtain ⟨M,hMb⟩:=chain.fullTest_boundedSmooth.norm_bound
  have hM:0≤M:=(norm_nonneg _).trans (hMb 0)
  have hGb(z:WordRecursion.State (n+k)):|G z|≤M:=by
    rw [show G=TriangularScoreWords.fullTest chain.word chain.initial from (fullTest_eq_word (Base p) chain).symm]
    simpa only [Real.norm_eq_abs] using hMb z
  have hinner:Measurable inner:=WeightedBorelAverage.measurable _ _
    (GaussianFixedFirstAverage.weight_measurable Rnative E hwm) _
    (GaussianFixedFirstAverage.shift_measurable hs) G hG
  have hbound:=WeightedBorelAverage.bound _ _ (GaussianFixedFirstAverage.weight_integrable μold Rnative E hw) _
    (GaussianFixedFirstAverage.shift_measurable hs) G hG M hM hGb
  have hage0(i:Fin (n+k)):stops Zero k h i-(v:ℝ)≤targets Zero k h i-(v:ℝ):=
    sub_le_sub_right ((min_le_left _ _).trans (RecursiveScoreSupport.carrier_ages Zero hages k h i)) _
  have hC:C.PosSemidef:=by
    rw [show C=fullResidualCovariance (Base p) (oldProfile P Λ v p.2) k h q-
      NativeFirstScoreReserve.covariance P (stops (Base p) k h) (targets (Base p) k h)
        (centers (Base p) k h) q from rfl,hres p q hvq hqt.le]
    exact NativeFirstScoreRepresentation.residual_posSemidef P Λ p.2.1 p.2.2
      (fixedProfile P Λ p.2.1 p.2.2 (fun j=>lower Zero k h j-(v:ℝ)) (fun j=>upper Zero k h j-(v:ℝ)))
      (fixedProfile_measurable P Λ _ _ _ _)
      (fixedProfile_bounds P Λ _ _ _ _ (RelativeHistoryGeometry.relative_disjoint Zero k h))
      _ _ _ hage0 (q-(v:ℝ)) p.1
  have hrep(z:WordRecursion.State (n+k)):fderiv ℝ Original z E=GaussianConvolution.gaussianAverage C inner z:=
    (hgrad p q hvq hqt z E hE).trans (hpacket p q hvq hqt.le z E).symm
  have hh:=NativeFirstMeanHessian.hessian_eq_meanScore hC hV Original inner
    ((ActualMeanKernel.test_boundedSmooth (Base p) k h).average (multivariateGaussian (0:WordRecursion.State (n+k)) _))
    hinner _ hbound hrep mean
  have hm:=hmean p q hvq hqt.le (mean-p.1•V) E V hE hV
  have hz:mean-p.1•V+p.1•V=mean:=by abel
  rw [hz] at hm
  rw [←hm]
  change GaussianTaylor.hessian Original mean V E=
    ∫y,inner (mean-p.1•V+p.1•V+y)*MeasurableGaussianScores.firstScore C V y
      ∂multivariateGaussian (0:WordRecursion.State (n+k)) C
  rw [hz]
  exact hh

end SHE.ControlledThetaNativeMeanHessian

