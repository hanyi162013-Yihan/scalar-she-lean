module

public import SHE.OmittedPhysicalIdentity
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
local instance chainOmittedAssignments_periodPos : Fact (0<2*Real.pi) := ⟨by positivity⟩
variable {X : Type} [MeasurableSpace X] {R : ReferenceData} {n : ℕ}
variable (L : CutoffWordLevel.Level R X n)

/-- The literal erased-leaf old Gaussian assignment identity on a
supplied physical chain. It can therefore be used on a common event
for every interpolation/reference input, rather than a fixed-L event. -/
theorem omitted_average_assignment_of_chain (c : Domain→ℝ) {k : ℕ} {p : History X k}
    (chain : Chain L k p (fun i=>i))
    (hphysical : Physical L ((carrier L k).observations.observations p) c chain) :
    ∀ q : ℝ,∀ mean : WordRecursion.State (n+k),∀ j0 : Fin k,
      (∀ choices,Integrable (omittedAssignedWord L c k p mean choices j0) (fullAssignedMeasure L c k p q)) ∧
      omittedAverage L c k p q j0 mean=(1/2:ℝ)^k*
        ((assignments (m:=k+1) (List.finRange k)).map (fun choices=>∫ x,
          omittedAssignedWord L c k p mean choices j0 x ∂fullAssignedMeasure L c k p q)).sum := by
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
