module

public import SHE.ControlledThetaOldAverageFields
public import SHE.ActualBaselineMarkFields
public import SHE.GaussianProductAverageFields
public import SHE.ActualCovarianceMarkFields
public import SHE.WeightedMeanKernel

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
noncomputable section

namespace SHE.ControlledThetaPhysicalMarkFields
open Set MeasureTheory ProbabilityTheory StoppedFourier WordRecursion ControlledProfile
  CutoffWordLevel CutoffWordHistories CutoffCarriers CutoffInsertionCore GaussianConvolution
  SmoothCylinders UniformSmooth GaussianContinuity PhysicalChainArrays ControlledReferenceLevel FiniteCenteredProduct
open scoped NNReal
local instance controlledThetaPhysicalMarkFields_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance controlledThetaPhysicalMarkFields_circleSigma : MeasurableSpace CircleL2 := borel _
local instance controlledThetaPhysicalMarkFields_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable (P : CanonicalCovariance.ProfileParameters) (A : ℝ→ℝ) (hA : BoundedSmooth A)
variable (Λ : ℝ) (v b : ℝ≥0) (hvb : v≤b)
variable {X : Type} [MeasurableSpace X] {n : ℕ} (Z : VariableObservations.Family X n)
variable (htarget : ∀ x i,(b:ℝ)≤(Z.observations x i).target)
variable (hstop : ∀ x i,(b:ℝ)≤(Z.observations x i).stop)
variable (F : X→WordRecursion.State n→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun q : X×WordRecursion.State n=>F q.1 q.2))
local notation "Base" => ControlledReferenceThetaGeometry.level P A hA Λ v b hvb Z htarget hstop F hF hFm

/-- Joint Borel complete covariance mark for a genuinely moving
canonical reference family, arbitrary dependent old/signed profiles,
current means, law times and original histories. -/
theorem covariance_point_variable_measurable {W : Type} [MeasurableSpace W] (k : ℕ)
    (p : W→ℝ×Inputs) (hp : Measurable p) (h : W→History X k) (hh : Measurable h)
    (q : W→ℝ) (hq : Measurable q)
    (c e : W×StoppedGaussianFeatures.Domain→ℝ) (hc : Measurable c) (he : Measurable e)
    (m : W→WordRecursion.State (n+k)) (hm : Measurable m) :
    Measurable (fun w=>ActualCovarianceMarkFields.point (Base (p w)) (fun r=>c (w,r))
      (fun r=>e (w,r)) k (q w) (m w) (h w)) := by
  classical
  let S:=CutoffWordLevel.reindexFamily
    (ControlledThetaWordFields.carrierFamily P A hA Λ v b hvb Z htarget hstop F hF hFm k)
    (fun w=>(p w,h w)) (hp.prodMk hh)
  let B : VariableObservations.Family W (n+k) :=
    { observations := fun w i=>⟨min (S.observations w i).stop (b:ℝ),
        (S.observations w i).target,(S.observations w i).center⟩
      stop_measurable := fun i=>(S.stop_measurable i).min measurable_const
      target_measurable := S.target_measurable
      center_measurable := S.center_measurable }
  have hAr:=ControlledThetaCovarianceFields.capped_residual_variable_measurable
    P A hA Λ v b hvb Z htarget hstop F hF hFm k p hp h hh q hq c hc
  have hc' : Measurable (fun z : (W×WordRecursion.State (n+k))×StoppedGaussianFeatures.Domain=>c (z.1.1,z.2)) :=
    hc.comp (measurable_fst.fst.prodMk measurable_snd)
  have hG:=ControlledThetaOldAverageFields.old_average_variable_measurable
    P A hA Λ v b hvb Z htarget hstop F hF hFm k
    (fun z : W×WordRecursion.State (n+k)=>p z.1) (hp.comp measurable_fst)
    (fun z=>h z.1) (hh.comp measurable_fst) (fun z=>c (z.1.1,z.2)) hc' Prod.snd measurable_snd
  have hrow : Measurable (fun z : W×StoppedGaussianFeatures.Domain=>StoppedGaussianFeatures.stoppedRow
      (CoveredControlledLaw.stops (Base (p z.1)) k (h z.1))
      (CoveredControlledLaw.targets (Base (p z.1)) k (h z.1))
      (CoveredControlledLaw.centers (Base (p z.1)) k (h z.1)) z.2) := by
    convert StoppedGaussianFields.row_measurable B using 1
    rfl
  have hpoint:=VariableFiniteMarkFields.history_covariance_mark_measurable
    (fun w=>ActualCovarianceMarkFields.cappedResidual (Base (p w)) (fun r=>c (w,r)) k (h w) (q w)) hAr
    (fun z=>oldAverage (Base (p z.1)) (fun r=>c (z.1,r)) k (h z.1) z.2) hG m hm _ hrow e he q hq
  have ht:=ControlledThetaWordFields.terminal_joint_measurable P A hA Λ v b hvb Z htarget hstop F hF hFm k
  have hmap : Measurable (fun w=>(p w,h w)):=hp.prodMk hh
  have ht':=ht.comp hmap
  have hs : MeasurableSet {w : W | q w<(carrier (Base (p w)) k).terminal (h w)} := measurableSet_lt hq ht'
  have hg : Measurable (fun w=>if q w<(carrier (Base (p w)) k).terminal (h w) then
      FiniteWordScores.covarianceMark (StoppedGaussianFeatures.historyMeasure (q w))
        (ActualCovarianceMarkFields.cappedResidual (Base (p w)) (fun r=>c (w,r)) k (h w) (q w))
        (fun r=>e (w,r)) (StoppedGaussianFeatures.stoppedRow
          (CoveredControlledLaw.stops (Base (p w)) k (h w))
          (CoveredControlledLaw.targets (Base (p w)) k (h w))
          (CoveredControlledLaw.centers (Base (p w)) k (h w)))
        (oldAverage (Base (p w)) (fun r=>c (w,r)) k (h w)) (m w) else 0) := hpoint.ite hs measurable_const
  convert hg using 1
  funext w
  simp only [ActualCovarianceMarkFields.point]
  split_ifs with ha
  · simp only [ActualCovarianceMarkFields.cappedResidual,min_eq_left ha.le]
  · rfl

/-- Joint Borel whole erased-leaf baseline mark for the moving family,
including all original full-profile baseline derivatives. -/
theorem baseline_point_variable_measurable {W : Type} [MeasurableSpace W] (k : ℕ)
    (p : W→ℝ×Inputs) (hp : Measurable p) (h : W→History X k) (hh : Measurable h)
    (q : W→ℝ) (hq : Measurable q)
    (c : W×StoppedGaussianFeatures.Domain→ℝ) (hc : Measurable c)
    (db : W→Fin k→ℝ) (hdb : Measurable db)
    (m : W→WordRecursion.State (n+k)) (hm : Measurable m) :
    Measurable (fun w=>ActualBaselineMarkFields.point (Base (p w)) (fun r=>c (w,r))
      k (q w) (db w) (m w) (h w)) := by
  classical
  have hAr:=ControlledThetaCovarianceFields.capped_residual_variable_measurable
    P A hA Λ v b hvb Z htarget hstop F hF hFm k p hp h hh q hq c hc
  have hc' : Measurable (fun z : (W×WordRecursion.State (n+k))×StoppedGaussianFeatures.Domain=>c (z.1.1,z.2)) :=
    hc.comp (measurable_fst.fst.prodMk measurable_snd)
  have hterm (j0 : Fin k) : Measurable (fun w=>db w j0*(1/2:ℝ)^k*
      gaussianAverage (ActualCovarianceMarkFields.cappedResidual (Base (p w)) (fun r=>c (w,r)) k (h w) (q w))
        (WeightedBorelAverage.average
          (Measure.pi (fun j=>multivariateGaussian (0:WordRecursion.State (n+k))
            (covariances (Base (p w)) ((carrier (Base (p w)) k).observations.observations (h w))
              (fun r=>c (w,r)) k (h w) j)))
          (fun x=>∏ j,MeasurableGaussianScores.secondScore
            (covariances (Base (p w)) ((carrier (Base (p w)) k).observations.observations (h w))
              (fun r=>c (w,r)) k (h w) j)
            (directions (Base (p w)) ((carrier (Base (p w)) k).observations.observations (h w)) k (h w) j) (x j))
          (fun x=>∑ j,x j)
          (test (Finset.univ.erase j0) (initial (Base (p w)) k (h w) (fun i=>i))
            (fun j z=>A (z (leafIndex k (fun i=>i) j))) (baseline (Base (p w)) k (h w)))) (m w)) := by
    have htest:=ControlledThetaOldAverageFields.centered_test_variable_measurable
      P A hA Λ v b hvb Z htarget hstop F hF hFm k (Finset.univ.erase j0)
      (fun z : (W×WordRecursion.State (n+k))×WordRecursion.State (n+k)=>p z.1.1)
      (hp.comp measurable_fst.fst) (fun z=>h z.1.1) (hh.comp measurable_fst.fst) Prod.snd measurable_snd
    have hmean : Measurable (fun z : W×WordRecursion.State (n+k)=>m z.1+z.2):=
      (hm.comp measurable_fst).add measurable_snd
    have hav:=ControlledThetaOldAverageFields.weighted_average_variable_measurable
      P A hA Λ v b hvb Z htarget hstop F hF hFm k
      (fun z : W×WordRecursion.State (n+k)=>p z.1) (hp.comp measurable_fst)
      (fun z=>h z.1) (hh.comp measurable_fst) (fun z=>c (z.1.1,z.2)) hc'
      (fun z=>test (Finset.univ.erase j0) (initial (Base (p z.1.1)) k (h z.1.1) (fun i=>i))
        (fun j w=>A (w (leafIndex k (fun i=>i) j))) (baseline (Base (p z.1.1)) k (h z.1.1)) z.2)
      htest (fun z=>m z.1+z.2) hmean
    have hgauss:=(hav.stronglyMeasurable.integral_kernel_prod_right'
      (κ:=GaussianScoreKernel.gaussianKernel _ hAr)).measurable
    exact ((((measurable_pi_apply j0).comp hdb).mul_const ((1/2:ℝ)^k)).mul hgauss)
  have hsum:=(Finset.measurable_sum Finset.univ (fun j _=>hterm j)).neg
  have ht:=ControlledThetaWordFields.terminal_joint_measurable P A hA Λ v b hvb Z htarget hstop F hF hFm k
  have hmap : Measurable (fun w=>(p w,h w)):=hp.prodMk hh
  have ht':=ht.comp hmap
  have hs : MeasurableSet {w : W | q w<(carrier (Base (p w)) k).terminal (h w)} := measurableSet_lt hq ht'
  let g : W→ℝ := fun w=>baselineMark (Base (p w)) (fun r=>c (w,r)) k (h w)
    (min (q w) ((carrier (Base (p w)) k).terminal (h w))) (db w) (m w)
  have hgm : Measurable g := by
    convert hsum using 1
    funext w
    simp only [g,baselineMark,omittedAverage,ActualCovarianceMarkFields.cappedResidual,Pi.neg_apply,mul_assoc]
    rfl
  have hg : Measurable (fun w=>if q w<(carrier (Base (p w)) k).terminal (h w) then g w else 0) :=
    hgm.ite hs measurable_const
  convert hg using 1
  funext w
  simp only [ActualBaselineMarkFields.point]
  split_ifs with ha
  · simp only [g,min_eq_left ha.le]
  · rfl

end SHE.ControlledThetaPhysicalMarkFields
