module

public import SHE.PhysicalFullResidualScore
public import SHE.GaussianFullResidualWord

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
local instance physicalFullResidualAssignments_periodPos : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
variable {X : Type} [MeasurableSpace X] {R : ReferenceData} {n : ℕ}
variable (L : CutoffWordLevel.Level R X n)

def fullAssignedMeasure (c : Domain → ℝ) (k : ℕ) (p : History X k) (q : ℝ) :
    Measure ((Fin k → WordRecursion.State (n+k)) × WordRecursion.State (n+k)) :=
  (Measure.pi (fun j => multivariateGaussian (0 : WordRecursion.State (n+k))
    (covariances L ((carrier L k).observations.observations p) c k p j))).prod
      (multivariateGaussian 0 (fullResidualCovariance L c k p q))

def fullAssignedWord (c : Domain → ℝ) (k : ℕ) (p : History X k) (q : ℝ)
    (direction mean : WordRecursion.State (n+k)) (choices : List (Fin k × Fin (k+1))) :
    ((Fin k → WordRecursion.State (n+k)) × WordRecursion.State (n+k)) → ℝ :=
  GaussianFullResidualWord.value false
    (covariances L ((carrier L k).observations.observations p) c k p)
    (directions L ((carrier L k).observations.observations p) k p)
    (fullResidualCovariance L c k p q) direction choices R.totalVariance
    (L.test (rootParameter k p)) mean (rootSelector k (fun i => i))
    (leafIndex k (fun i => i)) (baseline L k p)

/-- Exact actual all-order finite assignment representation with its
fresh first score in the entire remaining Gaussian covariance. Every
old score, root, rough leaf and full-profile baseline is preserved. -/
theorem full_residual_integral_ae (c : Domain → ℝ) (hc : Measurable c)
    {ell : ℝ} (hell : 0 < ell) (hb : ∀ z,ell ≤ c z ∧ c z ≤ R.reference z)
    (hages : ∀ p i,(L.observations.observations p i).stop ≤ (L.observations.observations p i).target)
    (μ : Measure X) [IsFiniteMeasure μ] (k : ℕ) :
    ∀ᵐ p ∂CutoffWordHistories.historyMeasure R μ k,
      ∀ q : ℝ,0 ≤ q → q < (carrier L k).terminal p →
      ∀ d z : WordRecursion.State (n+k),
        d ∈ (Matrix.toEuclideanCLM (𝕜:=ℝ) (fullResidualCovariance L c k p q)).range →
        (∀ choices,MemLp (fullAssignedWord L c k p q d z choices) 2 (fullAssignedMeasure L c k p q)) ∧
        fderiv ℝ (gaussianAverage (WordRecursion.covariance R.reference
          ((carrier L k).observations.observations p) q ((carrier L k).terminal p))
          (UncutSmoothWords.test L k p)) z d=
          (1/2:ℝ)^k*((assignments (m:=k+1) (List.finRange k)).map (fun choices =>
            ∫ x,fullAssignedWord L c k p q d z choices x ∂fullAssignedMeasure L c k p q)).sum := by
  filter_upwards [exists_chain_ae L c hc hell hb hages μ k,
    full_residual_first_score_ae L c hc hell hb hages μ k,
    oldAverage_assignment_ae L c hc hell hb hages μ k] with p hp hscore hassignment
  obtain ⟨chain,_,_,hphysical⟩ := hp
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
  obtain ⟨hT,hformula⟩ := hscore q hq hqt
  let T := fullResidualCovariance L c k p q
  letI : IsProbabilityMeasure (fullAssignedMeasure L c k p q) := by
    unfold fullAssignedMeasure
    infer_instance
  have hm (choices : List (Fin k × Fin (k+1))) :
      MemLp (fullAssignedWord L c k p q d z choices) 2 (fullAssignedMeasure L c k p q) :=
    GaussianFullResidualWord.value_memLp false A hA D hD T hT d hd choices
      R.totalVariance R.totalVariance_smooth.smooth.continuous.measurable
      (L.test (rootParameter k p)) hF z (rootSelector k (fun i => i))
      (leafIndex k (fun i => i)) (baseline L k p) hK hFb hab
  refine ⟨hm,?_⟩
  have he := GaussianFullResidualWord.nested_sum_first_eq A D T d
    (assignments (m:=k+1) (List.finRange k)) R.totalVariance (L.test (rootParameter k p)) z
    (rootSelector k (fun i => i)) (leafIndex k (fun i => i)) (baseline L k p)
    (fun choices _ => (hm choices).integrable (by norm_num))
  rw [hformula d z hd]
  change _=(1/2:ℝ)^k*((assignments (m:=k+1) (List.finRange k)).map (fun choices =>
    ∫ x,GaussianFullResidualWord.value false A D T d choices R.totalVariance
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
      MeasurableGaussianScores.firstScore T d fresh=_
    dsimp only [assignedSum,assignedProduct]
    ring)

end SHE.PhysicalChainArrays
