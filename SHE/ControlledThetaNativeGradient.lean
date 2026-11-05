module

public import SHE.ControlledThetaConsistentKernel
public import SHE.NativeFirstScoreRepresentation
public import SHE.SeparatedMeanKernel
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

namespace SHE.ControlledThetaNativeGradient
open Set MeasureTheory ProbabilityTheory StoppedFourier WordRecursion ControlledProfile ControlledReferenceLevel
  CutoffWordLevel CutoffWordHistories SmoothCylinders UniformSmooth CutoffCarriers PhysicalChainArrays
  PhysicalScoreChain ControlledOldIntervals ControlledReferenceWindows ControlledFamilyProfileForest
  ProjectedUncutWord CoveredControlledLaw CoveredHistoryGeometry
open scoped NNReal BigOperators
local instance controlledThetaConsistentKernel_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance controlledThetaConsistentKernel_circleSigma : MeasurableSpace CircleL2 := borel _
local instance controlledThetaConsistentKernel_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable (P : CanonicalCovariance.ProfileParameters) (hA : BoundedSmooth P.coefficient)
variable (Λ : ℝ) (v b : ℝ≥0) (hvb : v≤b)
variable {X : Type} [MeasurableSpace X] {n : ℕ} (Z : VariableObservations.Family X n)
variable (htarget : ∀ x i,(b:ℝ)≤(Z.observations x i).target)
variable (hstop : ∀ x i,(b:ℝ)≤(Z.observations x i).stop)
variable (F : X→WordRecursion.State n→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun q : X×WordRecursion.State n=>F q.1 q.2))
local notation "Base" => ControlledReferenceThetaGeometry.level P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm

local notation "Zero"=>Base (0,(0,0))

/-- The ORIGINAL backward recursive gradient equals the complete
consistent native packet, on one event before every random past/current
substitution. Its input remains in its own fixed native reserve. -/
theorem gradient_all_parameters_ae
    (hages:∀x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (ρ:Measure X)[IsFiniteMeasure ρ](k:ℕ):
    ∀ᵐh∂historyMeasure (referenceData P P.coefficient hA Λ 0 v b hvb (0,0)) ρ k,
      ∀p:ℝ×Inputs,∀q:ℝ,(v:ℝ)≤q→q<(carrier Zero k).terminal h→
      ∀(mean E:WordRecursion.State (n+k)),
      E∈(Matrix.toEuclideanCLM (𝕜:=ℝ) (NativeFirstScoreReserve.covariance P
        (stops (Base p) k h) (targets (Base p) k h) (centers (Base p) k h) q)).range→
      fderiv ℝ (GaussianConvolution.gaussianAverage (WordRecursion.covariance
        (referenceData P P.coefficient hA Λ p.1 v b hvb p.2).reference
        ((carrier (Base p) k).observations.observations h) q ((carrier (Base p) k).terminal h))
        (UncutSmoothWords.test (Base p) k h)) mean E=
      NativeFirstWholeComplete.value P Λ p.2.1 p.2.2 p.1 (q-(v:ℝ))
        (fun i=>stops Zero k h i-(v:ℝ)) (fun i=>targets Zero k h i-(v:ℝ)) (centers Zero k h)
        (fun j=>lower Zero k h j-(v:ℝ)) (fun j=>upper Zero k h j-(v:ℝ)) mean
        (directions Zero ((carrier Zero k).observations.observations h) k h) E
        (rootSelector k (fun i=>i)) (leafIndex k (fun i=>i)) (F (rootParameter k h)):=by
  filter_upwards [ControlledThetaSupported.physical_chain_all_parameters_ae
      P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm hages ρ k,
    ControlledThetaSupported.full_residual_average_all_parameters_ae
      P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm hages ρ k,
    ControlledThetaTwoFreshArrays.residual_all_parameters_ae
      P hA Λ v b hvb Z htarget hstop F hF hFm hages ρ k,
    ControlledThetaConsistentKernel.kernel_all_parameters_ae
      P hA Λ v b hvb Z htarget hstop F hF hFm hages ρ k] with h hchain havg hres hpacket
  intro p q hvq hqt mean E hE
  obtain ⟨chain,_,_,hphysical⟩:=hchain p
  let Rnative:=NativeFirstScoreReserve.covariance P (stops (Base p) k h)
    (targets (Base p) k h) (centers (Base p) k h) q
  let C:=fullResidualCovariance (Base p) (oldProfile P Λ v p.2) k h q-Rnative
  let A:=covariances (Base p) ((carrier (Base p) k).observations.observations h) (oldProfile P Λ v p.2) k h
  let D:=directions (Base p) ((carrier (Base p) k).observations.observations h) k h
  let μold:=Measure.pi (fun j=>multivariateGaussian (0:WordRecursion.State (n+k)) (A j))
  let w:=fun old:Fin k→WordRecursion.State (n+k)=>∏j,MeasurableGaussianScores.secondScore (A j) (D j) (old j)
  let shift:=fun old:Fin k→WordRecursion.State (n+k)=>∑j,old j
  let G:=word (Base p) k h (fun i=>i)
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
  have hage(i:Fin (n+k)):stops (Base p) k h i≤targets (Base p) k h i:=
    (min_le_left _ _).trans (RecursiveScoreSupport.carrier_ages (Base p) hages k h i)
  have hR:Rnative.PosSemidef:=NativeFirstScoreReserve.covariance_posSemidef P _ _ _ hage q
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
  have hh:=GaussianFixedFirstAverage.hasDerivAt μold hR hC hE w hw hwm shift hs G hG M hM hGb mean 0
  have hsum:Rnative+C=fullResidualCovariance (Base p) (oldProfile P Λ v p.2) k h q:=by
    dsimp only [C];abel
  rw [hsum] at hh
  have haverage:WeightedBorelAverage.average μold w shift G=oldAverage (Base p) (oldProfile P Λ v p.2) k h:=rfl
  rw [haverage] at hh
  let Original:=GaussianConvolution.gaussianAverage (WordRecursion.covariance
    (referenceData P P.coefficient hA Λ p.1 v b hvb p.2).reference
    ((carrier (Base p) k).observations.observations h) q ((carrier (Base p) k).terminal h))
    (UncutSmoothWords.test (Base p) k h)
  have hqt':q≤(carrier (Base p) k).terminal h:=by
    rw [ControlledReferenceThetaGeometry.carrier_terminal_eq P P.coefficient hA Λ v b hvb
      Z htarget hstop F hF hFm p (0,(0,0)) k h]
    exact hqt.le
  have heq:Original=GaussianConvolution.gaussianAverage
      (fullResidualCovariance (Base p) (oldProfile P Λ v p.2) k h q)
      (oldAverage (Base p) (oldProfile P Λ v p.2) k h):=
    funext (havg p q (v.2.trans hvq) hqt')
  rw [←heq] at hh
  have hline:HasDerivAt (fun t:ℝ=>mean+t•E) E 0:=by
    convert! ((hasDerivAt_id (0:ℝ)).smul_const E).const_add mean using 1 <;>
      simp only [id_eq,one_smul]
  have hSmooth:BoundedSmooth Original:=(ActualMeanKernel.test_boundedSmooth (Base p) k h).average _
  have hd:=(hSmooth.smooth.differentiable (by simp) (mean+(0:ℝ)•E)).hasFDerivAt.comp_hasDerivAt 0 hline
  have hderiv:=hd.unique hh
  simp only [zero_smul,add_zero,Function.comp_def] at hderiv
  exact hderiv.trans (hpacket p q hvq hqt.le mean E)
/-- The literal two-clock physical row kernel uses its ORIGINAL q-law
and current mean, with only its native input row evaluated at r. -/
theorem rowPoint_all_parameters_ae
    (hages:∀x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (ρ:Measure X)[IsFiniteMeasure ρ](k:ℕ):
    ∀ᵐh∂historyMeasure (referenceData P P.coefficient hA Λ 0 v b hvb (0,0)) ρ k,
      ∀ p : ℝ×Inputs, ∀ q r : ℝ, (v:ℝ) ≤ q →
      q < (carrier Zero k).terminal h → r < (carrier Zero k).terminal h →
      ∀m:History X k→WordRecursion.State (n+k),∀y:HeatCircle,
      heatRow ((carrier (Base p) k).observations.observations h) r y∈
        (Matrix.toEuclideanCLM (𝕜:=ℝ) (NativeFirstScoreReserve.covariance P
          (stops (Base p) k h) (targets (Base p) k h) (centers (Base p) k h) q)).range→
      ActualMeanKernel.rowPoint (Base p) k q r m h y=
      NativeFirstWholeComplete.value P Λ p.2.1 p.2.2 p.1 (q-(v:ℝ))
        (fun i=>stops Zero k h i-(v:ℝ)) (fun i=>targets Zero k h i-(v:ℝ)) (centers Zero k h)
        (fun j=>lower Zero k h j-(v:ℝ)) (fun j=>upper Zero k h j-(v:ℝ)) (m h)
        (directions Zero ((carrier Zero k).observations.observations h) k h)
        (heatRow ((carrier (Base p) k).observations.observations h) r y)
        (rootSelector k (fun i=>i)) (leafIndex k (fun i=>i)) (F (rootParameter k h)):=by
  filter_upwards [gradient_all_parameters_ae P hA Λ v b hvb Z htarget hstop F hF hFm hages ρ k]
    with h hh
  intro p q r hvq hq hr m y hy
  have htime: (carrier (Base p) k).terminal h=(carrier Zero k).terminal h:=
    ControlledReferenceThetaGeometry.carrier_terminal_eq P P.coefficient hA Λ v b hvb
      Z htarget hstop F hF hFm p (0,(0,0)) k h
  rw [ActualMeanKernel.rowPoint_of_active (Base p) k q r m h y
    (by rwa [htime]) (by rwa [htime])]
  exact hh p q hvq hq (m h) _ hy

end SHE.ControlledThetaNativeGradient
