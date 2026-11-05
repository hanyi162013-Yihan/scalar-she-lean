module

public import SHE.OmittedFullAverage
public import SHE.OmittedPhysicalMoments
public import SHE.WeightedCenteredExpansion

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section

namespace SHE.PhysicalChainArrays
open Set Filter MeasureTheory ProbabilityTheory AddCircle StoppedFourier WordRecursion
  CutoffWordLevel CutoffWordHistories CutoffCarriers GaussianCoordinates ProjectedUncutWord PhysicalScoreChain
  OldIntervalCovariance StoppedGaussianFeatures GaussianConvolution GaussianAssignmentBlocks
open scoped BigOperators
local instance omittedPhysicalIdentity_periodPos : Fact (0<2*Real.pi) := ⟨by positivity⟩
variable {X : Type} [MeasurableSpace X] {R : ReferenceData} {n : ℕ}
variable (L : CutoffWordLevel.Level R X n)

/-- The literal omitted full centered product under the same old score
average and full remaining Gaussian as the original recursive word. -/
def omittedAverage (c : Domain→ℝ) (k : ℕ) (p : History X k) (q : ℝ) (j0 : Fin k)
    (mean : WordRecursion.State (n+k)) : ℝ :=
  (1/2:ℝ)^k*gaussianAverage (fullResidualCovariance L c k p q)
    (WeightedBorelAverage.average
      (Measure.pi (fun j=>multivariateGaussian (0 : WordRecursion.State (n+k))
        (covariances L ((carrier L k).observations.observations p) c k p j)))
      (fun x=>∏ j,MeasurableGaussianScores.secondScore
        (covariances L ((carrier L k).observations.observations p) c k p j)
        (directions L ((carrier L k).observations.observations p) k p j) (x j)) (fun x=>∑ j,x j)
      (FiniteCenteredProduct.test (Finset.univ.erase j0) (initial L k p (fun i=>i))
        (fun j z=>R.totalVariance (z (leafIndex k (fun i=>i) j))) (baseline L k p))) mean

def omittedAssignedWord (c : Domain→ℝ) (k : ℕ) (p : History X k)
    (mean : WordRecursion.State (n+k)) (choices : List (Fin k×Fin (k+1))) (j0 : Fin k) :
    ((Fin k→WordRecursion.State (n+k))×WordRecursion.State (n+k))→ℝ :=
  OmittedAssignmentIdentity.value
    (covariances L ((carrier L k).observations.observations p) c k p)
    (directions L ((carrier L k).observations.observations p) k p) choices j0 R.totalVariance
    (L.test (rootParameter k p)) (rootSelector k (fun i=>i)) (leafIndex k (fun i=>i)) (baseline L k p) mean

/-- Actual all-order baseline omissions have the original old-fraction
assignment law. A deleted leaf is a constant before centering, so its
nonempty assignments vanish; no reference baseline is replaced. -/
theorem omitted_average_assignment_ae (c : Domain→ℝ) (hc : Measurable c)
    {ell : ℝ} (hell : 0<ell) (hb : ∀ z,ell≤c z ∧ c z≤R.reference z)
    (hages : ∀ p i,(L.observations.observations p i).stop≤(L.observations.observations p i).target)
    (μ : Measure X) [IsFiniteMeasure μ] (k : ℕ) :
    ∀ᵐ p ∂CutoffWordHistories.historyMeasure R μ k,
      ∀ q : ℝ,∀ mean : WordRecursion.State (n+k),∀ j0 : Fin k,
      (∀ choices,Integrable (omittedAssignedWord L c k p mean choices j0) (fullAssignedMeasure L c k p q)) ∧
      omittedAverage L c k p q j0 mean=(1/2:ℝ)^k*
        ((assignments (m:=k+1) (List.finRange k)).map (fun choices=>∫ x,
          omittedAssignedWord L c k p mean choices j0 x ∂fullAssignedMeasure L c k p q)).sum := by
  filter_upwards [exists_chain_ae L c hc hell hb hages μ k] with p hp
  obtain ⟨chain,_,_,hphysical⟩ := hp
  let Z := (carrier L k).observations.observations p
  let A := covariances L Z c k p
  let D := directions L Z k p
  have hA (j : Fin k) : (A j).PosSemidef := by
    rw [show A=chain.old from (Physical.old_eq L Z c chain hphysical).symm]
    exact chain.old_posSemidef j
  have hD (j : Fin k) : D j∈(Matrix.toEuclideanCLM (𝕜:=ℝ) (A j)).range := by
    rw [show A=chain.old from (Physical.old_eq L Z c chain hphysical).symm,
      show D=chain.direction from (Physical.direction_eq L Z c chain hphysical).symm]
    exact chain.assigned_direction_mem_range j
  obtain ⟨K,hK,hKF⟩ := L.test_uniform.norm_bound
  obtain ⟨M,hMa⟩ := R.totalVariance_smooth.norm_bound
  have hF : Measurable (L.test (rootParameter k p)) := (L.test_uniform.smooth _).continuous.measurable
  have hFb (w : WordRecursion.State n) : |L.test (rootParameter k p) w|≤K := by
    simpa only [Real.norm_eq_abs] using hKF (rootParameter k p) w
  have hab (w : ℝ) : |R.totalVariance w|≤M := by simpa only [Real.norm_eq_abs] using hMa w
  intro q mean j0
  constructor
  · intro choices
    exact OmittedAssignmentIdentity.value_integrable A D (fullResidualCovariance L c k p q) choices j0
      R.totalVariance R.totalVariance_smooth.smooth.continuous.measurable (L.test (rootParameter k p)) hF
      (rootSelector k (fun i=>i)) (leafIndex k (fun i=>i)) (baseline L k p) mean hK hFb hab
  · have he := OmittedAssignmentIdentity.full_average_eq A hA D hD (fullResidualCovariance L c k p q)
      (List.finRange k) (List.nodup_finRange k) R.totalVariance R.totalVariance_smooth.smooth.continuous.measurable
      (L.test (rootParameter k p)) hF (rootSelector k (fun i=>i)) (leafIndex k (fun i=>i)) (baseline L k p) j0
      hK hFb hab mean
    exact congrArg (fun z : ℝ=>(1/2:ℝ)^k*z) he

end SHE.PhysicalChainArrays

namespace SHE.OmittedPhysicalMoments
open Set MeasureTheory ProbabilityTheory Real AddCircle StoppedFourier WordRecursion CutoffWordLevel
  CutoffWordHistories CutoffCarriers GaussianCoordinates PhysicalChainArrays ControlledOldIntervals
  GaussianAssignmentBlocks
open scoped BigOperators
variable {X : Type} [MeasurableSpace X] {n : ℕ}

theorem actual_assignedWord_eq (P : CanonicalCovariance.ProfileParameters)
    (ha : SmoothCylinders.BoundedSmooth P.coefficient) (Λ : ℝ) (u dir : CircleL2) (θ : ℝ)
    (L : CutoffWordLevel.Level (ControlledWordLevel.referenceData P ha Λ u dir θ) X n)
    (k : ℕ) (p : History X k) (mean : WordRecursion.State (n+k))
    (choices : List (Fin k×Fin (k+1))) (j0 : Fin k)
    (x : (Fin k→WordRecursion.State (n+k))×WordRecursion.State (n+k)) :
    omittedAssignedWord L (referenceProfile P Λ u dir) k p mean choices j0 x=
      if block choices j0.succ=[] then value P ha Λ u dir θ L k p mean choices j0 x else 0 := by
  by_cases hb : block choices j0.succ=[]
  · simp only [omittedAssignedWord,OmittedAssignmentIdentity.value,OmittedAssignmentIdentity.testValue,
      ite_eq_left hb,value,ControlledWordLevel.referenceData]
    ring
  · simp only [omittedAssignedWord,OmittedAssignmentIdentity.value,OmittedAssignmentIdentity.testValue,
      ite_eq_right hb,mul_zero]

end SHE.OmittedPhysicalMoments
