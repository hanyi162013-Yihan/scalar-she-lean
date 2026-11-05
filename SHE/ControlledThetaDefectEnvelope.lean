module

public import SHE.ControlledThetaBoundedHaarHessian
public import SHE.ControlledFamilyProfileForest

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000

namespace SHE.ControlledThetaDefectEnvelope
open Set MeasureTheory ProbabilityTheory StoppedFourier WordRecursion ControlledProfile ControlledReferenceLevel
  CutoffWordLevel CutoffWordHistories SmoothCylinders UniformSmooth CutoffCarriers PhysicalChainArrays
  PhysicalScoreChain ControlledOldIntervals ControlledReferenceWindows ControlledFamilyProfileForest
  ProjectedUncutWord CoveredControlledLaw CoveredHistoryGeometry MeasurableGaussianScores FiniteHaar
  PhysicalParentGeometry
open scoped NNReal BigOperators
local instance controlledThetaDefectEnvelope_period:Fact (0<2*Real.pi):=⟨by positivity⟩
local instance controlledThetaDefectEnvelope_sigma:MeasurableSpace CircleL2:=borel _
local instance controlledThetaDefectEnvelope_borel:BorelSpace CircleL2:=⟨rfl⟩
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

/-- Complete literal Hessian packets use the actual earlier-parent
forest, uniformly before ALL theta, original past data and current
means. The positive density depends only on original physical geometry;
the reference profile stays inside the genuine old Gaussian laws. -/
theorem hessian_envelope_all_parameters_ae
    (hages:∀x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (ρ:Measure X)[IsFiniteMeasure ρ](k:ℕ):
    ∀ᵐh∂historyMeasure (referenceData P P.coefficient hA Λ 0 v b hvb (0,0)) ρ k,
      ∀p:ℝ×Inputs,∀q:ℝ,(v:ℝ)≤q→q<(carrier Zero k).terminal h→
      ∀(hp:StrictHistory Zero k h),SmallHistory Zero (uniformHorizon n) k h→
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
      let Hgeo:=timeWeight Zero (fraction P*P.lower) (uniformConstant n) k h*
        OrderedHeatForests.parentDensity 2 (by norm_num) k
          (fun i=>((carrier Zero k).observations.observations h i).target)
          (carrier_orderedTimes Zero hages k h hp)
          (fun i=>((carrier Zero k).observations.observations h i).center)
      let B:=GaussianTaylor.hessian (GaussianConvolution.gaussianAverage (WordRecursion.covariance
        (referenceData P P.coefficient hA Λ p.1 v b hvb p.2).reference
        ((carrier (Base p) k).observations.observations h) q ((carrier (Base p) k).terminal h))
        (UncutSmoothWords.test (Base p) k h)) mean
      Summable (fun j=>B (V j) (E j)) ∧
      |∑'j,B (V j) (E j)|≤Real.sqrt (TwoFreshBoundedEmptyWord.momentConstant P k k 1)*
        (Hgeo*TwoFreshBoundedEmptyWord.total (d:=n)
          P lo hi (fun j=>target (leafIndex k (fun i=>i) j)) A0 ν)*
        (Real.sqrt (∑'j,scoreVariance R (E j))*Real.sqrt (∑'j,scoreVariance C (V j))):=by
  filter_upwards [ControlledThetaBoundedHaarHessian.hessian_trace_all_parameters_ae
      P hA Λ v b hvb Z htarget hstop F hF hFm hages ρ k,
    all_inputs_forest_ae P P.coefficient hA Λ 0 v b hvb Z htarget hstop F hF hFm hages ρ k]
    with h hh hf
  intro p q hvq hqt hp hsmall hspan mean E V σ target center lo hi R C hE hV hsE hsV A0 ν hA0 hν hjet Hgeo B
  have hh':=hh p q hvq hqt hp hspan mean E V hE hV hsE hsV A0 ν hA0 hν hjet
  let A:=OldIntervalCovariance.familyCovariance σ target center (referenceProfile P Λ p.2.1 p.2.2) lo hi
  let D:=directions Zero ((carrier Zero k).observations.observations h) k h
  have hold:(∏j,scoreVariance (A j) (D j))≤Hgeo:=by
    have hs:=(hf p.2).2 hp hsmall
    change scoreProduct (Base (0,p.2)) ((carrier (Base (0,p.2)) k).observations.observations h)
      (oldProfile P Λ v p.2) k h≤Hgeo at hs
    rw [OME (0,p.2) (0,(0,0)) k h,
      ControlledThetaPhysicalGeometry.scoreProduct_eq P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm
        (0,p.2) (0,(0,0))] at hs
    unfold scoreProduct at hs
    rw [ControlledThetaRelativeArrays.old_covariance_relative_fixed
      P hA Λ v b hvb Z htarget hstop F hF hFm p k h hvq hqt.le] at hs
    exact hs
  refine ⟨hh'.1,hh'.2.trans ?_⟩
  have hT:=TwoFreshBoundedEmptyWord.total_nonneg (d:=n) P lo hi
    (fun j=>target (leafIndex k (fun i=>i) j)) A0 ν
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hold hT) (Real.sqrt_nonneg _))
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

end SHE.ControlledThetaDefectEnvelope
