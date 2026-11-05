module

public import SHE.PhysicalTwoFreshAssignments
public import SHE.NativeFirstOmittedWholeAverage

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2300000
noncomputable section
namespace SHE.PhysicalChainArrays
open Set Filter MeasureTheory ProbabilityTheory AddCircle StoppedFourier WordRecursion
  CutoffWordLevel CutoffWordHistories CutoffCarriers GaussianCoordinates ProjectedUncutWord
  PhysicalScoreChain OldIntervalCovariance StoppedGaussianFeatures GaussianConvolution GaussianAssignmentBlocks
  GaussianDependentScores MeasurableGaussianScores
open scoped BigOperators
local instance physicalNativeOmittedAssignments_period : Fact (0<2*Real.pi):=⟨by positivity⟩
variable {X:Type} [MeasurableSpace X] {R:ReferenceData} {n:ℕ}
variable (L:Level R X n)

def nativeOmittedAverage (c:Domain→ℝ) (k:ℕ) (p:History X k)
    (Rnative C:MeasurableGeneralizedInverse.Mat (n+k)) (E mean:WordRecursion.State (n+k)) (j0:Fin k):ℝ:=
  (1/2:ℝ)^k*gaussianAverage C
    (WeightedBorelAverage.average
      ((Measure.pi (fun j=>multivariateGaussian (0:WordRecursion.State (n+k))
        (covariances L ((carrier L k).observations.observations p) c k p j))).prod
          (multivariateGaussian (0:WordRecursion.State (n+k)) Rnative))
      (GaussianFixedFirstAverage.weight Rnative E (fun old=>∏j,secondScore
        (covariances L ((carrier L k).observations.observations p) c k p j)
        (directions L ((carrier L k).observations.observations p) k p j) (old j)))
      (GaussianFixedFirstAverage.shift (fun old=>∑j,old j))
      (FiniteCenteredProduct.test (Finset.univ.erase j0) (initial L k p (fun i=>i))
        (fun j z=>R.totalVariance (z (leafIndex k (fun i=>i) j))) (baseline L k p))) mean

def nativeOmittedAssignedWord (c:Domain→ℝ) (k:ℕ) (p:History X k)
    (Rnative:MeasurableGeneralizedInverse.Mat (n+k)) (E mean:WordRecursion.State (n+k))
    (choices:List (Fin k×Fin (k+1))) (j0:Fin k):
    ((Fin k→WordRecursion.State (n+k))×(WordRecursion.State (n+k)×WordRecursion.State (n+k)))→ℝ:=
  NativeFirstOmittedAssignment.value
    (covariances L ((carrier L k).observations.observations p) c k p)
    (directions L ((carrier L k).observations.observations p) k p) Rnative E choices j0
    R.totalVariance (L.test (rootParameter k p)) mean (rootSelector k (fun i=>i))
    (leafIndex k (fun i=>i)) (baseline L k p)

/-- The actual omitted baseline in the physical native-first kernel
has its original normalization once and its exact two-fresh assignment
law. C remains unscored, including singular and zero residual laws. -/
theorem native_omitted_average_of_chain (c:Domain→ℝ) {k:ℕ} {p:History X k}
    (chain:Chain L k p (fun i=>i))
    (hphysical:Physical L ((carrier L k).observations.observations p) c chain)
    (Rnative C:MeasurableGeneralizedInverse.Mat (n+k)) (E mean:WordRecursion.State (n+k)) (j0:Fin k):
    nativeOmittedAverage L c k p Rnative C E mean j0=
      (1/2:ℝ)^k*((assignments (m:=k+1) (List.finRange k)).map (fun choices=>
        ∫z,nativeOmittedAssignedWord L c k p Rnative E mean choices j0 z
          ∂twoFreshMeasure L c k p Rnative C)).sum:=by
  let A:=covariances L ((carrier L k).observations.observations p) c k p
  let D:=directions L ((carrier L k).observations.observations p) k p
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
  exact congrArg (fun x:ℝ=>(1/2:ℝ)^k*x)
    (NativeFirstOmittedWholeAverage.average A hA D hD Rnative C E
      (List.finRange k) (List.nodup_finRange k) j0 R.totalVariance
      R.totalVariance_smooth.smooth.continuous.measurable (L.test (rootParameter k p)) hF mean
      (rootSelector k (fun i=>i)) (leafIndex k (fun i=>i)) (baseline L k p) hK hFb hab)

end SHE.PhysicalChainArrays
