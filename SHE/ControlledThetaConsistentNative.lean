module

public import SHE.NativeFirstWholeAssignment
public import SHE.ControlledThetaRelativeNativeWord
public import SHE.NativeFirstWholeComplete
public import SHE.ChainAssignedRepresentation

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000
noncomputable section
namespace SHE.PhysicalChainArrays
open Set Filter MeasureTheory ProbabilityTheory AddCircle StoppedFourier WordRecursion
  CutoffWordLevel CutoffWordHistories CutoffCarriers GaussianCoordinates ProjectedUncutWord
  PhysicalScoreChain OldIntervalCovariance StoppedGaussianFeatures GaussianConvolution GaussianAssignmentBlocks
  GaussianDependentScores MeasurableGaussianScores
open scoped BigOperators
local instance controlledThetaConsistentNative_period : Fact (0<2*Real.pi):=⟨by positivity⟩
variable {X:Type} [MeasurableSpace X] {R:ReferenceData} {n:ℕ}
variable (L:Level R X n)

def nativeWholeAssignedWord (c:Domain→ℝ) (k:ℕ) (p:History X k)
    (Rnative C:MeasurableGeneralizedInverse.Mat (n+k)) (E mean:WordRecursion.State (n+k))
    (choices:List (Fin k×Fin (k+1)))
    (z:(Fin k→WordRecursion.State (n+k))×(WordRecursion.State (n+k)×WordRecursion.State (n+k))):ℝ:=
  NativeFirstWholeMoments.word
    (covariances L ((carrier L k).observations.observations p) c k p)
    (directions L ((carrier L k).observations.observations p) k p) Rnative E choices
    R.totalVariance (L.test (rootParameter k p)) (fun _:Unit=>mean)
    (rootSelector k (fun i=>i)) (leafIndex k (fun i=>i)) (baseline L k p) ((),z)

/-- Supplied-chain physical attachment of the untouched TWO fresh score
carriers to the literal complete recursive word. The old intervals and
the original normalization are identified internally. -/
theorem native_whole_average_of_chain (c:Domain→ℝ) {k:ℕ} {p:History X k}
    (chain:Chain L k p (fun i=>i))
    (hphysical:Physical L ((carrier L k).observations.observations p) c chain)
    (Rnative C:MeasurableGeneralizedInverse.Mat (n+k)) (E mean:WordRecursion.State (n+k)):
    let A:=covariances L ((carrier L k).observations.observations p) c k p
    let D:=directions L ((carrier L k).observations.observations p) k p
    gaussianAverage C
      (WeightedBorelAverage.average
        ((Measure.pi (fun j=>multivariateGaussian (0:WordRecursion.State (n+k)) (A j))).prod
          (multivariateGaussian (0:WordRecursion.State (n+k)) Rnative))
        (GaussianFixedFirstAverage.weight Rnative E (fun old=>∏j,secondScore (A j) (D j) (old j)))
        (GaussianFixedFirstAverage.shift (fun old=>∑j,old j)) (word L k p (fun i=>i))) mean=
      (1/2:ℝ)^k*((assignments (m:=k+1) (List.finRange k)).map (fun choices=>
        ∫z,nativeWholeAssignedWord L c k p Rnative C E mean choices z
          ∂twoFreshMeasure L c k p Rnative C)).sum:=by
  intro A D
  have hA(j:Fin k):(A j).PosSemidef:=by
    rw [show A=chain.old from (Physical.old_eq L _ c chain hphysical).symm]
    exact chain.old_posSemidef j
  have hD(j:Fin k):D j∈(Matrix.toEuclideanCLM (𝕜:=ℝ) (A j)).range:=by
    rw [show A=chain.old from (Physical.old_eq L _ c chain hphysical).symm,
      show D=chain.direction from (Physical.direction_eq L _ c chain hphysical).symm]
    exact chain.assigned_direction_mem_range j
  obtain ⟨K,hK,hKF⟩:=L.test_uniform.norm_bound
  obtain ⟨M,hMa⟩:=R.totalVariance_smooth.norm_bound
  have hF:Measurable (L.test (rootParameter k p)):=(L.test_uniform.smooth _).continuous.measurable
  have hFb(z:WordRecursion.State n):|L.test (rootParameter k p) z|≤K:=by
    simpa only [Real.norm_eq_abs] using hKF (rootParameter k p) z
  have hab(z:ℝ):|R.totalVariance z|≤M:=by simpa only [Real.norm_eq_abs] using hMa z
  let μoldR:=(Measure.pi (fun j=>multivariateGaussian (0:WordRecursion.State (n+k)) (A j))).prod
    (multivariateGaussian (0:WordRecursion.State (n+k)) Rnative)
  let w:=GaussianFixedFirstAverage.weight Rnative E
    (fun old:Fin k→WordRecursion.State (n+k)=>∏j,secondScore (A j) (D j) (old j))
  let sh:=GaussianFixedFirstAverage.shift (fun old:Fin k→WordRecursion.State (n+k)=>∑j,old j)
  let raw:=VectorAssignmentIdentity.raw R.totalVariance (L.test (rootParameter k p))
    (rootSelector k (fun i=>i)) (leafIndex k (fun i=>i)) (baseline L k p)
  have hinner:WeightedBorelAverage.average μoldR w sh (fun z=>(1/2:ℝ)^k*raw z)=
      (fun z=>(1/2:ℝ)^k*WeightedBorelAverage.average μoldR w sh raw z):=by
    funext z
    exact WeightedBorelAverage.const_mul μoldR w sh raw ((1/2:ℝ)^k) z
  rw [word_eq_raw]
  change gaussianAverage C
    (WeightedBorelAverage.average μoldR w sh (fun z=>(1/2:ℝ)^k*raw z)) mean=_
  rw [hinner]
  simp_rw [gaussianAverage]
  rw [integral_const_mul]
  congr 1
  exact NativeFirstWholeAssignment.average A hA D hD Rnative C E
    (List.finRange k) (List.nodup_finRange k) R.totalVariance
    R.totalVariance_smooth.smooth.continuous.measurable (L.test (rootParameter k p)) hF mean
    (rootSelector k (fun i=>i)) (leafIndex k (fun i=>i)) (baseline L k p) hK hFb hab


end SHE.PhysicalChainArrays

namespace SHE.ControlledThetaConsistentNative
open Set MeasureTheory ProbabilityTheory StoppedFourier WordRecursion ControlledProfile ControlledReferenceLevel
  CutoffWordLevel CutoffWordHistories SmoothCylinders UniformSmooth CutoffCarriers PhysicalChainArrays
  PhysicalScoreChain ControlledOldIntervals ControlledReferenceWindows ControlledFamilyProfileForest
  ProjectedUncutWord CoveredControlledLaw CoveredHistoryGeometry
open scoped NNReal
local instance controlledThetaConsistentNative_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance controlledThetaConsistentNative_circleSigma : MeasurableSpace CircleL2 := borel _
local instance controlledThetaConsistentNative_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable (P : CanonicalCovariance.ProfileParameters) (hA : BoundedSmooth P.coefficient)
variable (Λ : ℝ) (v b : ℝ≥0) (hvb : v≤b)
variable {X : Type} [MeasurableSpace X] {n : ℕ} (Z : VariableObservations.Family X n)
variable (htarget : ∀ x i,(b:ℝ)≤(Z.observations x i).target)
variable (hstop : ∀ x i,(b:ℝ)≤(Z.observations x i).stop)
variable (F : X→WordRecursion.State n→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun q : X×WordRecursion.State n=>F q.1 q.2))
local notation "Base" => ControlledReferenceThetaGeometry.level P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm

local notation "Zero"=>Base (0,(0,0))

/-- The literal physical consistent native-FIRST assigned integral is the exact
relative-age fibre used by the genuine random-past conditional moments.
The event is selected once, before theta, past inputs or current mean. -/
theorem assigned_integral_all_parameters_ae
    (hages:∀x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (ρ:Measure X) [IsFiniteMeasure ρ] (k:ℕ):
    ∀ᵐh∂historyMeasure (referenceData P P.coefficient hA Λ 0 v b hvb (0,0)) ρ k,
      ∀p:ℝ×Inputs,∀q:ℝ,(v:ℝ)≤q→q≤(carrier Zero k).terminal h→
      ∀(mean:WordRecursion.State (n+k)) (E:WordRecursion.State (n+k)) choices,
      let Rnative:=NativeFirstScoreReserve.covariance P (stops (Base p) k h) (targets (Base p) k h)
        (centers (Base p) k h) q
      let C:=fullResidualCovariance (Base p) (oldProfile P Λ v p.2) k h q-Rnative
      (∫x,nativeWholeAssignedWord (Base p) (oldProfile P Λ v p.2) k h Rnative C E mean choices x
        ∂twoFreshMeasure (Base p) (oldProfile P Λ v p.2) k h Rnative C)=
      NativeFirstWholeMoments.fibreAverage P Λ p.2.1 p.2.2 p.1 (q-(v:ℝ))
        (fun i=>stops Zero k h i-(v:ℝ)) (fun i=>targets Zero k h i-(v:ℝ)) (centers Zero k h)
        (fun j=>lower Zero k h j-(v:ℝ)) (fun j=>upper Zero k h j-(v:ℝ)) mean
        (directions Zero ((carrier Zero k).observations.observations h) k h) E
        (rootSelector k (fun i=>i)) (leafIndex k (fun i=>i)) choices (F (rootParameter k h)):=by
  filter_upwards [ControlledThetaTwoFreshArrays.residual_all_parameters_ae
    P hA Λ v b hvb Z htarget hstop F hF hFm hages ρ k] with h hh
  intro p q hvq hqt mean E choices Rnative C
  have hcov:covariances (Base p) ((carrier (Base p) k).observations.observations h)
      (oldProfile P Λ v p.2) k h=
      OldIntervalCovariance.familyCovariance
        (fun i=>stops Zero k h i-(v:ℝ)) (fun i=>targets Zero k h i-(v:ℝ)) (centers Zero k h)
        (referenceProfile P Λ p.2.1 p.2.2) (fun j=>lower Zero k h j-(v:ℝ))
        (fun j=>upper Zero k h j-(v:ℝ)):=by
    rw [ControlledReferenceThetaGeometry.carrier_observations_eq
      P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm p (0,(0,0)) k h,
      ControlledThetaPhysicalGeometry.covariances_eq P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm p (0,(0,0))]
    exact ControlledThetaRelativeArrays.old_covariance_relative_fixed
      P hA Λ v b hvb Z htarget hstop F hF hFm p k h hvq hqt
  have hres:=hh p q hvq hqt
  change C=_ at hres
  have hnative:Rnative=NativeFirstScoreReserve.covariance P
      (fun i=>stops Zero k h i-(v:ℝ)) (fun i=>targets Zero k h i-(v:ℝ))
      (centers Zero k h) (q-(v:ℝ)):=by
    dsimp only [Rnative]
    rw [ControlledThetaRelativeDerivative.stops_eq P hA Λ v b hvb Z htarget hstop F hF hFm p (0,(0,0)) k h,
      ControlledThetaRelativeDerivative.targets_eq P hA Λ v b hvb Z htarget hstop F hF hFm p (0,(0,0)) k h,
      ControlledThetaRelativeDerivative.centers_eq P hA Λ v b hvb Z htarget hstop F hF hFm p (0,(0,0)) k h]
    exact ControlledThetaTwoFreshArrays.native_relative P (v:ℝ) q _ _ _
  have hbase:baseline (Base p) k h=(fun j=>ControlledProfile.profile P Λ p.2.1 p.2.2
      (p.1,(targets Zero k h (leafIndex k (fun i=>i) j)-(v:ℝ),
        centers Zero k h (leafIndex k (fun i=>i) j)))):=by
    funext j
    rw [ControlledThetaRelativeWord.baseline_relative P hA Λ v b hvb Z htarget hstop F hF hFm p k h j,
      ControlledThetaRelativeDerivative.targets_eq P hA Λ v b hvb Z htarget hstop F hF hFm p (0,(0,0)) k h,
      ControlledThetaRelativeDerivative.centers_eq P hA Λ v b hvb Z htarget hstop F hF hFm p (0,(0,0)) k h]
  have hdir:directions (Base p) ((carrier (Base p) k).observations.observations h) k h=
      directions Zero ((carrier Zero k).observations.observations h) k h:=by
    rw [ControlledReferenceThetaGeometry.carrier_observations_eq
      P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm p (0,(0,0)) k h]
    exact ControlledThetaPhysicalGeometry.directions_eq
      P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm p (0,(0,0)) _ k h
  unfold nativeWholeAssignedWord twoFreshMeasure NativeFirstWholeMoments.fibreAverage
  change (∫x,NativeFirstWholeMoments.word _ _ Rnative E choices _ _ _ _ _ _ ((),x) ∂_)=_
  rw [hcov,hres,hnative,hbase,hdir]
  rfl

end SHE.ControlledThetaConsistentNative


