module

public import SHE.ControlledThetaNativeMeanHessian
public import SHE.TwoFreshBoundedHaarContraction

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3600000

namespace SHE.ControlledThetaBoundedHaarHessian
open Set MeasureTheory ProbabilityTheory StoppedFourier WordRecursion ControlledProfile ControlledReferenceLevel
  CutoffWordLevel CutoffWordHistories SmoothCylinders UniformSmooth CutoffCarriers PhysicalChainArrays
  PhysicalScoreChain ControlledOldIntervals ControlledReferenceWindows ControlledFamilyProfileForest
  ProjectedUncutWord CoveredControlledLaw CoveredHistoryGeometry MeasurableGaussianScores FiniteHaar
  PhysicalParentGeometry
open scoped NNReal BigOperators
local instance controlledThetaBoundedHaarHessian_period:Fact (0<2*Real.pi):=⟨by positivity⟩
local instance controlledThetaBoundedHaarHessian_sigma:MeasurableSpace CircleL2:=borel _
local instance controlledThetaBoundedHaarHessian_borel:BorelSpace CircleL2:=⟨rfl⟩
variable (P:CanonicalCovariance.ProfileParameters)(hA:BoundedSmooth P.coefficient)
variable (Λ:ℝ)(v b:ℝ≥0)(hvb:v≤b)
variable {X:Type}[MeasurableSpace X]{n:ℕ}(Z:VariableObservations.Family X n)
variable (htarget:∀x i,(b:ℝ)≤(Z.observations x i).target)
variable (hstop:∀x i,(b:ℝ)≤(Z.observations x i).stop)
variable (F:X→WordRecursion.State n→ℝ)(hF:UniformBoundedSmooth F)
variable (hFm:Measurable (fun q:X×WordRecursion.State n=>F q.1 q.2))
local notation "Base"=>ControlledReferenceThetaGeometry.level P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm
local notation "Zero"=>Base (0,(0,0))
local notation "OME"=>ControlledReferenceThetaGeometry.carrier_observations_eq P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm
local notation "COVE"=>ControlledThetaPhysicalGeometry.covariances_eq P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm
local notation "DE"=>ControlledThetaPhysicalGeometry.directions_eq P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm
local notation "SE"=>ControlledThetaRelativeDerivative.stops_eq P hA Λ v b hvb Z htarget hstop F hF hFm
local notation "TE"=>ControlledThetaRelativeDerivative.targets_eq P hA Λ v b hvb Z htarget hstop F hF hFm
local notation "CE"=>ControlledThetaRelativeDerivative.centers_eq P hA Λ v b hvb Z htarget hstop F hF hFm

/-- The actual recursive Gaussian-front Hessian, contracted along the
original matched Haar coordinates, has a complete bounded-empty packet
bound. One history event precedes ALL past inputs, interpolation values,
current means and directions. All old range and relative-age hypotheses
are discharged from the actual physical chain. -/
theorem hessian_trace_all_parameters_ae
    (hages:∀x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (ρ:Measure X)[IsFiniteMeasure ρ](k:ℕ):
    ∀ᵐh∂historyMeasure (referenceData P P.coefficient hA Λ 0 v b hvb (0,0)) ρ k,
      ∀p:ℝ×Inputs,∀q:ℝ,(v:ℝ)≤q→q<(carrier Zero k).terminal h→StrictHistory Zero k h→
      (b:ℝ)-(v:ℝ)≤P.horizon→
      ∀(mean:WordRecursion.State (n+k))(E V:HaarNode→WordRecursion.State (n+k)),
      let σ:=fun i=>stops Zero k h i-(v:ℝ)
      let target:=fun i=>targets Zero k h i-(v:ℝ)
      let center:=centers Zero k h
      let lo:=fun j=>lower Zero k h j-(v:ℝ)
      let hi:=fun j=>upper Zero k h j-(v:ℝ)
      let R:=NativeFirstScoreReserve.covariance P σ target center (q-(v:ℝ))
      let C:=ControlledFixedReserve.covariance P Λ p.2.1 p.2.2
        (NativeFirstScoreReserve.oldProfile P (fixedProfile P Λ p.2.1 p.2.2 lo hi))
        σ target center (q-(v:ℝ)) p.1
      (∀j,E j∈(Matrix.toEuclideanCLM (𝕜:=ℝ) R).range)→
      (∀j,V j∈(Matrix.toEuclideanCLM (𝕜:=ℝ) C).range)→
      Summable (fun j=>scoreVariance R (E j))→Summable (fun j=>scoreVariance C (V j))→
      ∀A0 ν:ℝ,0≤A0→0≤ν→
      (∀j,j≤k→∀z,‖iteratedFDeriv ℝ j (F (rootParameter k h)) z‖≤A0*ν^j)→
      let A:=OldIntervalCovariance.familyCovariance σ target center
        (referenceProfile P Λ p.2.1 p.2.2) lo hi
      let D:=directions Zero ((carrier Zero k).observations.observations h) k h
      let B:=GaussianTaylor.hessian (GaussianConvolution.gaussianAverage (WordRecursion.covariance
        (referenceData P P.coefficient hA Λ p.1 v b hvb p.2).reference
        ((carrier (Base p) k).observations.observations h) q ((carrier (Base p) k).terminal h))
        (UncutSmoothWords.test (Base p) k h)) mean
      Summable (fun j=>B (V j) (E j)) ∧
      |∑'j,B (V j) (E j)|≤Real.sqrt (TwoFreshBoundedEmptyWord.momentConstant P k k 1)*
        ((∏j,scoreVariance (A j) (D j))*TwoFreshBoundedEmptyWord.total (d:=n)
          P lo hi (fun j=>target (leafIndex k (fun i=>i) j)) A0 ν)*
        (Real.sqrt (∑'j,scoreVariance R (E j))*Real.sqrt (∑'j,scoreVariance C (V j))):=by
  filter_upwards [ControlledThetaNativeMeanHessian.hessian_all_parameters_ae
      P hA Λ v b hvb Z htarget hstop F hF hFm hages ρ k,
    ControlledThetaTwoFreshArrays.residual_all_parameters_ae
      P hA Λ v b hvb Z htarget hstop F hF hFm hages ρ k,
    ControlledThetaSupported.physical_chain_all_parameters_ae
      P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm hages ρ k] with h hessian hres hchain
  intro p q hvq hqt hstrict hspan mean E V σ target center lo hi R C hE hV hsE hsV A0 ν hA0 hν hjet A D B
  obtain ⟨chain,_,_,hphysical⟩:=hchain p
  have hdir:directions (Base p) ((carrier (Base p) k).observations.observations h) k h=D:=by
    rw [OME p (0,(0,0)) k h]
    exact DE p (0,(0,0)) _ k h
  have hcov:covariances (Base p) ((carrier (Base p) k).observations.observations h)
      (oldProfile P Λ v p.2) k h=A:=by
    rw [OME p (0,(0,0)) k h,COVE p (0,(0,0))]
    exact ControlledThetaRelativeArrays.old_covariance_relative_fixed
      P hA Λ v b hvb Z htarget hstop F hF hFm p k h hvq hqt.le
  have hD(j:Fin k):D j∈(Matrix.toEuclideanCLM (𝕜:=ℝ) (A j)).range:=by
    rw [←hdir,←hcov,←Physical.direction_eq (Base p) _ _ chain hphysical,
      ←Physical.old_eq (Base p) _ _ chain hphysical]
    exact chain.assigned_direction_mem_range j
  have hR:NativeFirstScoreReserve.covariance P (stops (Base p) k h) (targets (Base p) k h)
      (centers (Base p) k h) q=R:=by
    rw [SE p (0,(0,0)) k h,TE p (0,(0,0)) k h,CE p (0,(0,0)) k h,
      ControlledThetaTwoFreshArrays.native_relative P (v:ℝ) q]
  have hC:fullResidualCovariance (Base p) (oldProfile P Λ v p.2) k h q-
      NativeFirstScoreReserve.covariance P (stops (Base p) k h) (targets (Base p) k h)
        (centers (Base p) k h) q=C:=hres p q hvq hqt.le
  have he(j:HaarNode):B (V j) (E j)=TwoFreshBoundedEmptyWord.value P Λ p.2.1 p.2.2 p.1
      (q-(v:ℝ)) σ target center lo hi mean false D (E j) (V j)
      (rootSelector k (fun i=>i)) (leafIndex k (fun i=>i)) (F (rootParameter k h)):=by
    exact hessian p q hvq hqt mean (E j) (V j) (by simpa only [hR] using hE j)
      (by simpa only [hC] using hV j)
  have hσ(i:Fin (n+k)):0<σ i:=RelativeHistoryGeometry.relative_stop_pos Zero k h hvq hqt i
  have hσ1(i:Fin (n+k)):σ i≤1:=
    (RelativeHistoryGeometry.relative_stop_le_span Zero b (fun _=>le_rfl) k h i).trans
      (hspan.trans P.horizon_le_one)
  have hage(i:Fin (n+k)):σ i≤target i:=sub_le_sub_right
    ((min_le_left _ _).trans (RecursiveScoreSupport.carrier_ages Zero hages k h i)) _
  have hlo(j:Fin k):q-(v:ℝ)≤lo j:=sub_le_sub_right (hqt.le.trans (terminal_le_lower Zero k h j)) _
  have hlh(j:Fin k):lo j<hi j:=sub_lt_sub_right (lower_lt_upper Zero k h hstrict j) _
  have hnative(j:Fin k):σ (leafIndex k (fun i=>i) j)=target (leafIndex k (fun i=>i) j):=
    congrArg (fun z:ℝ=>z-(v:ℝ)) (RelativeHistoryGeometry.native_leaf Zero k h hstrict j)
  have ht(j:Fin k):target (leafIndex k (fun i=>i) j)∈Ioc 0 P.horizon:=
    RelativeHistoryGeometry.native_leaf_relative_age Zero b P.horizon (fun _=>le_rfl) hspan
      k h hstrict hvq hqt j
  have hh:=TwoFreshBoundedHaarContraction.complete_word P Λ p.2.1 p.2.2 p.1
    (q-(v:ℝ)) (sub_nonneg.mpr hvq) σ target center hσ hσ1 hage lo hi hlo hlh
    (RelativeHistoryGeometry.relative_stop_dichotomy Zero k h)
    (RelativeHistoryGeometry.relative_disjoint Zero k h) mean D hD E V hE hV
    (rootSelector k (fun i=>i)) (leafIndex k (fun i=>i)) hnative ht
    (F (rootParameter k h)) (hF.smooth _).continuous.measurable hA0 hν
    ((hF.smooth _).of_le (by simp)) hjet hsE hsV
  simpa only [he] using hh

end SHE.ControlledThetaBoundedHaarHessian
