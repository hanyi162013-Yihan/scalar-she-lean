module

public import SHE.ChainAssignedRepresentation
public import SHE.PhysicalFullResidualCovariance
public import SHE.PhysicalFullResidualAssignments
public import SHE.GaussianFullResidualMarks

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000
noncomputable section

namespace SHE.PhysicalChainArrays
open Set Filter MeasureTheory ProbabilityTheory AddCircle StoppedFourier WordRecursion
  CutoffWordLevel CutoffWordHistories CutoffCarriers GaussianCoordinates ProjectedUncutWord PhysicalScoreChain
  OldIntervalCovariance StoppedGaussianFeatures GaussianConvolution GaussianAssignmentBlocks
open scoped BigOperators
local instance chainCovarianceAssignments_periodPos : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
variable {X : Type} [MeasurableSpace X] {R : ReferenceData} {n : ℕ}
variable (L : CutoffWordLevel.Level R X n)

/-- Exact full-second-score assignment identity on an actual supplied
physical chain; it selects no parameter-dependent history event. -/
theorem full_residual_covariance_integral_of_chain (c : Domain→ℝ) {k : ℕ} {p : History X k}
    (chain : Chain L k p (fun i=>i)) (hs : chain.CoordinateSupport)
    (hphysical : Physical L ((carrier L k).observations.observations p) c chain)
    (hages : ∀ x i,(L.observations.observations x i).stop≤(L.observations.observations x i).target) :
      ∀ q : ℝ,0 ≤ q → q < (carrier L k).terminal p →
      ∀ d z : WordRecursion.State (n+k),
        d ∈ (Matrix.toEuclideanCLM (𝕜:=ℝ) (fullResidualCovariance L c k p q)).range →
        (∀ choices,MemLp (fullCovarianceAssignedWord L c k p q d z choices) 2 (fullAssignedMeasure L c k p q)) ∧
        (∫ y,oldAverage L c k p (z+y)*MeasurableGaussianScores.secondScore
          (fullResidualCovariance L c k p q) d y
          ∂multivariateGaussian 0 (fullResidualCovariance L c k p q))=
          (1/2:ℝ)^k*((assignments (m:=k+1) (List.finRange k)).map (fun choices =>
            ∫ x,fullCovarianceAssignedWord L c k p q d z choices x ∂fullAssignedMeasure L c k p q)).sum := by
  have hscore:=full_residual_first_score_of_chain L c chain hs hphysical hages
  have hassignment:=oldAverage_assignment_of_chain L c chain hphysical
  let Z := (carrier L k).observations.observations p
  let A := covariances L Z c k p
  let D := directions L Z k p
  have hA (j : Fin k) : (A j).PosSemidef := by
    rw [show A=chain.old from (Physical.old_eq L Z c chain hphysical).symm]
    exact chain.old_posSemidef j
  have hD (j : Fin k) : D j ∈ (Matrix.toEuclideanCLM (𝕜:=ℝ) (A j)).range := by
    rw [show A=chain.old from (Physical.old_eq L Z c chain hphysical).symm,
      show D=chain.direction from (Physical.direction_eq L Z c chain hphysical).symm]
    exact chain.assigned_direction_mem_range j
  obtain ⟨K,hK,hKF⟩ := L.test_uniform.norm_bound
  obtain ⟨M,hMa⟩ := R.totalVariance_smooth.norm_bound
  have hF : Measurable (L.test (rootParameter k p)) :=
    (L.test_uniform.smooth _).continuous.measurable
  have hFb (w : WordRecursion.State n) : |L.test (rootParameter k p) w| ≤ K := by
    simpa only [Real.norm_eq_abs] using hKF (rootParameter k p) w
  have hab (w : ℝ) : |R.totalVariance w| ≤ M := by simpa only [Real.norm_eq_abs] using hMa w
  intro q hq hqt d z hd
  obtain ⟨hT,_⟩ := hscore q hq hqt
  let T := fullResidualCovariance L c k p q
  letI : IsProbabilityMeasure (fullAssignedMeasure L c k p q) := by
    unfold fullAssignedMeasure
    infer_instance
  have hm (choices : List (Fin k × Fin (k+1))) :
      MemLp (fullCovarianceAssignedWord L c k p q d z choices) 2 (fullAssignedMeasure L c k p q) :=
    GaussianFullResidualWord.value_memLp true A hA D hD T hT d hd choices
      R.totalVariance R.totalVariance_smooth.smooth.continuous.measurable
      (L.test (rootParameter k p)) hF z (rootSelector k (fun i => i))
      (leafIndex k (fun i => i)) (baseline L k p) hK hFb hab
  refine ⟨hm,?_⟩
  have he := GaussianFullResidualWord.nested_sum_mark_eq true A D T d
    (assignments (m:=k+1) (List.finRange k)) R.totalVariance (L.test (rootParameter k p)) z
    (rootSelector k (fun i => i)) (leafIndex k (fun i => i)) (baseline L k p)
    (fun choices _ => (hm choices).integrable (by norm_num))
  change _=(1/2:ℝ)^k*((assignments (m:=k+1) (List.finRange k)).map (fun choices =>
    ∫ x,GaussianFullResidualWord.value true A D T d choices R.totalVariance
      (L.test (rootParameter k p)) z (rootSelector k (fun i => i))
      (leafIndex k (fun i => i)) (baseline L k p) x
      ∂(Measure.pi (fun j => multivariateGaussian (0 : WordRecursion.State (n+k)) (A j))).prod
        (multivariateGaussian 0 T))).sum
  rw [←he,←integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ (fun fresh => by
    dsimp only
    rw [hassignment z fresh]
    change ((1/2:ℝ)^k*∫ old,(∏ j,MeasurableGaussianScores.secondScore (A j) (D j) (old j))*
      assignedSum L k p z fresh old ∂Measure.pi (fun j => multivariateGaussian (0 : WordRecursion.State (n+k)) (A j)))*
      MeasurableGaussianScores.secondScore T d fresh=_
    dsimp only [assignedSum,assignedProduct]
    simp only [GaussianDependentScores.factor,ite_true]
    ring)


end SHE.PhysicalChainArrays
