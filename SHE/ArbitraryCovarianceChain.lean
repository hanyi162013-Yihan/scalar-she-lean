module

public import SHE.ArbitraryResidualCovariance
public import SHE.ChainAssignedRepresentation

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000
noncomputable section
namespace SHE.ArbitraryResidualCovariance
open Set Filter MeasureTheory ProbabilityTheory AddCircle StoppedFourier WordRecursion
  CutoffWordLevel CutoffWordHistories CutoffCarriers GaussianCoordinates ProjectedUncutWord PhysicalScoreChain
  OldIntervalCovariance StoppedGaussianFeatures GaussianConvolution GaussianAssignmentBlocks PhysicalChainArrays
open scoped BigOperators
local instance : Fact (0<2*Real.pi):=⟨by positivity⟩
variable {X : Type} [MeasurableSpace X] {R : ReferenceData} {n : ℕ}
variable (L : CutoffWordLevel.Level R X n)

/-- The arbitrary-residual second-score assignment is pointwise on a
supplied original physical chain. It can be used on a common history
event for every past profile, avoiding parameter-dependent null sets. -/
theorem integral_of_chain (c : Domain→ℝ) {k : ℕ} {p : History X k}
    (chain : Chain L k p (fun i=>i))
    (hphysical : Physical L ((carrier L k).observations.observations p) c chain) :
      ∀ (B : Matrix (Fin (n+k)) (Fin (n+k)) ℝ),B.PosSemidef →
      ∀ d z : WordRecursion.State (n+k),
        d ∈ (Matrix.toEuclideanCLM (𝕜:=ℝ) B).range →
        (∀ choices,MemLp (assignedWord L c k p B d z choices) 2
          ((Measure.pi (fun j=>multivariateGaussian (0:WordRecursion.State (n+k))
            (covariances L ((carrier L k).observations.observations p) c k p j))).prod
              (multivariateGaussian 0 B))) ∧
        (∫ y,oldAverage L c k p (z+y)*MeasurableGaussianScores.secondScore B d y
          ∂multivariateGaussian 0 B)=
          (1/2:ℝ)^k*((assignments (m:=k+1) (List.finRange k)).map (fun choices=>
            ∫ x,assignedWord L c k p B d z choices x
              ∂(Measure.pi (fun j=>multivariateGaussian (0:WordRecursion.State (n+k))
                (covariances L ((carrier L k).observations.observations p) c k p j))).prod
                  (multivariateGaussian 0 B))).sum := by
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
  intro T hT d z hd
  let νG : Measure ((Fin k→WordRecursion.State (n+k))×WordRecursion.State (n+k)):=
    (Measure.pi (fun j=>multivariateGaussian 0 (A j))).prod (multivariateGaussian 0 T)
  have hm (choices : List (Fin k × Fin (k+1))) :
      MemLp (assignedWord L c k p T d z choices) 2 νG :=
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

end SHE.ArbitraryResidualCovariance
