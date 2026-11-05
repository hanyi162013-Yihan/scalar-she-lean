module

public import SHE.PhysicalFullResidualAssignments
public import SHE.FullResidualChainAverage

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000
noncomputable section

namespace SHE.PhysicalChainArrays
open Set Filter MeasureTheory ProbabilityTheory AddCircle StoppedFourier WordRecursion
  CutoffWordLevel CutoffWordHistories CutoffCarriers GaussianCoordinates ProjectedUncutWord PhysicalScoreChain
  OldIntervalCovariance StoppedGaussianFeatures GaussianConvolution GaussianAssignmentBlocks
  MeasurableGaussianScores SmoothCylinders
open scoped BigOperators
local instance chainAssignedRepresentation_period : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
variable {X : Type} [MeasurableSpace X] {R : ReferenceData} {n : ℕ}
variable (L : CutoffWordLevel.Level R X n)
/-- Exact full-residual first score on a supplied physical chain.
This pointwise theorem can be evaluated on a common all-parameter event. -/
theorem full_residual_first_score_of_chain (c : Domain→ℝ) {k : ℕ} {p : History X k}
    (chain : Chain L k p (fun i=>i)) (hs : chain.CoordinateSupport)
    (hphysical : Physical L ((carrier L k).observations.observations p) c chain)
    (hages : ∀ x i,(L.observations.observations x i).stop≤(L.observations.observations x i).target) :
      ∀ q : ℝ,0 ≤ q → q < (carrier L k).terminal p →
      (fullResidualCovariance L c k p q).PosSemidef ∧
      ∀ d z : WordRecursion.State (n+k),
        d ∈ (Matrix.toEuclideanCLM (𝕜:=ℝ) (fullResidualCovariance L c k p q)).range →
        fderiv ℝ (gaussianAverage (WordRecursion.covariance R.reference
          ((carrier L k).observations.observations p) q ((carrier L k).terminal p))
          (UncutSmoothWords.test L k p)) z d=
          ∫ y,oldAverage L c k p (z+y)*firstScore (fullResidualCovariance L c k p q) d y
            ∂multivariateGaussian 0 (fullResidualCovariance L c k p q) := by
  let Z := (carrier L k).observations.observations p
  have hZ : ∀ i,(Z i).stop ≤ (Z i).target := RecursiveScoreSupport.carrier_ages L hages k p
  have havg : chain.oldAverage=oldAverage L c k p := by
    unfold Chain.oldAverage oldAverage
    rw [Physical.old_eq L Z c chain hphysical,Physical.direction_eq L Z c chain hphysical,
      fullTest_eq_word L chain]
  let νG : Measure (Fin k → WordRecursion.State (n+k)) :=
    Measure.pi (fun j => multivariateGaussian 0 (chain.old j))
  let S : (Fin k → WordRecursion.State (n+k)) → ℝ :=
    fun x => ∏ j,secondScore (chain.old j) (chain.direction j) (x j)
  let shift : (Fin k → WordRecursion.State (n+k)) → WordRecursion.State (n+k) := fun x => ∑ j,x j
  have hS : Integrable S νG := Integrable.fintype_prod
    (fun j => GaussianVectorFractions.gaussian_secondScore_integrable (chain.old j) (chain.direction j))
  have hSm : Measurable S := by
    apply Finset.measurable_prod Finset.univ
    intro j _
    have hm : Measurable (fun x : Fin k → WordRecursion.State (n+k) =>
        inner ℝ (coefficient (chain.old j) (chain.direction j)) (x j)) :=
      (innerSL ℝ (coefficient (chain.old j) (chain.direction j))).measurable.comp (measurable_pi_apply j)
    exact (hm.pow_const 2).sub measurable_const
  have hshift : Measurable shift := Finset.measurable_sum Finset.univ (fun j _ => measurable_pi_apply j)
  have hF := chain.fullTest_boundedSmooth.smooth.continuous.measurable
  obtain ⟨M,hM⟩ := chain.fullTest_boundedSmooth.norm_bound
  have hMn : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hbound : ∀ w,|TriangularScoreWords.fullTest chain.word chain.initial w| ≤ M :=
    fun w => by simpa only [Real.norm_eq_abs] using hM w
  have hG : Measurable chain.oldAverage := WeightedBorelAverage.measurable νG S hSm shift hshift _ hF
  have hGb : ∀ w,|chain.oldAverage w| ≤ M*∫ x,|S x| ∂νG :=
    WeightedBorelAverage.bound νG S hS shift hshift _ hF M hMn hbound
  rw [havg] at hG hGb
  intro q hq hqt
  let C := WordRecursion.covariance R.reference Z q ((carrier L k).terminal p)
  have hC : C.PosSemidef := by
    change (WordRecursion.covariance R.reference Z q ((carrier L k).terminal p)).PosSemidef
    have he := PhysicalIntervalCovariance.interval_eq_covariance Z R.reference R.reference_measurable
      R.reference_bound hZ ((carrier L k).stops_after p) hq hqt.le
    rw [←he]
    exact PhysicalFirstScore.interval_posSemidef Z hZ R.reference R.reference_measurable
      (fun r => ⟨R.reference_nonneg r,(le_abs_self _).trans (R.reference_bound r)⟩)
      q ((carrier L k).terminal p)
  have hres : C+∑ j,chain.residual j=fullResidualCovariance L c k p q := by
    rw [Physical.residual_eq L Z c chain hphysical]
    rfl
  have hT : (fullResidualCovariance L c k p q).PosSemidef := by
    rw [←hres]
    exact hC.add (Matrix.posSemidef_sum _ (fun j _ => chain.residual_posSemidef j))
  refine ⟨hT,?_⟩
  have hrep : gaussianAverage C (UncutSmoothWords.test L k p)=
      gaussianAverage (fullResidualCovariance L c k p q) (oldAverage L c k p) := by
    funext z
    have hh := chain.predictable_eq_reserved_average hs hC z
    have hid : (fun w => UncutSmoothWords.test L k p (projection (fun i => i) w))=
        UncutSmoothWords.test L k p := rfl
    rw [hid,hres,havg] at hh
    exact hh
  intro d z hd
  exact GaussianFullResidualScore.fderiv_eq_firstScore hT hd
    (RecursiveGaussianScores.test_boundedSmooth L k p) hG _ hGb hrep z

/-- The complete canonical assignment identity on an explicitly
constructed physical chain, at every base mean and residual. -/
theorem oldAverage_assignment_of_chain (c : Domain→ℝ) {k : ℕ} {p : History X k}
    (chain : Chain L k p (fun i=>i))
    (hphysical : Physical L ((carrier L k).observations.observations p) c chain) :
    ∀ mean residual : WordRecursion.State (n+k),
      oldAverage L c k p (mean+residual)=(1/2:ℝ)^k*
        ∫ x,(∏ j,MeasurableGaussianScores.secondScore
          (covariances L ((carrier L k).observations.observations p) c k p j)
          (directions L ((carrier L k).observations.observations p) k p j) (x j))*
          assignedSum L k p mean residual x
          ∂Measure.pi (fun j => multivariateGaussian (0:WordRecursion.State (n+k))
            (covariances L ((carrier L k).observations.observations p) c k p j)) := by
  let Z := (carrier L k).observations.observations p
  have hA (j : Fin k) : (covariances L Z c k p j).PosSemidef := by
    rw [←Physical.old_eq L Z c chain hphysical]
    exact chain.old_posSemidef j
  have hD (j : Fin k) : directions L Z k p j∈
      (Matrix.toEuclideanCLM (𝕜:=ℝ) (covariances L Z c k p j)).range := by
    rw [←Physical.old_eq L Z c chain hphysical,←Physical.direction_eq L Z c chain hphysical]
    exact chain.assigned_direction_mem_range j
  obtain ⟨K,hK,hKF⟩ := L.test_uniform.norm_bound
  obtain ⟨M,hMa⟩ := R.totalVariance_smooth.norm_bound
  have hF : Measurable (L.test (rootParameter k p)) :=
    (L.test_uniform.smooth _).continuous.measurable
  have hFb (z : WordRecursion.State n) : |L.test (rootParameter k p) z|≤K := by
    simpa only [Real.norm_eq_abs] using hKF (rootParameter k p) z
  have hab (z : ℝ) : |R.totalVariance z|≤M := by simpa only [Real.norm_eq_abs] using hMa z
  intro mean residual
  have hh := VectorAssignmentIdentity.old_average_eq (covariances L Z c k p) hA
    (directions L Z k p) hD (List.finRange k) (List.nodup_finRange k)
    R.totalVariance R.totalVariance_smooth.smooth.continuous.measurable
    (L.test (rootParameter k p)) hF (rootSelector k (fun i => i))
    (leafIndex k (fun i => i)) (baseline L k p) hK hFb hab mean residual
  change WeightedBorelAverage.average _ _ _ (word L k p (fun i => i)) (mean+residual)=_
  rw [word_eq_raw,WeightedBorelAverage.const_mul]
  apply congrArg (fun z : ℝ => (1/2:ℝ)^k*z)
  convert! hh using 1

/-- Genuine full assigned-product integral representation with its
actual physical chain supplied explicitly. In particular no parameter-
dependent exceptional set is selected by this theorem. -/
theorem full_residual_integral_of_chain (c : Domain→ℝ) {k : ℕ} {p : History X k}
    (chain : Chain L k p (fun i=>i)) (hs : chain.CoordinateSupport)
    (hphysical : Physical L ((carrier L k).observations.observations p) c chain)
    (hages : ∀ x i,(L.observations.observations x i).stop≤(L.observations.observations x i).target) :
      ∀ q : ℝ,0 ≤ q → q < (carrier L k).terminal p →
      ∀ d z : WordRecursion.State (n+k),
        d ∈ (Matrix.toEuclideanCLM (𝕜:=ℝ) (fullResidualCovariance L c k p q)).range →
        (∀ choices,MemLp (fullAssignedWord L c k p q d z choices) 2 (fullAssignedMeasure L c k p q)) ∧
        fderiv ℝ (gaussianAverage (WordRecursion.covariance R.reference
          ((carrier L k).observations.observations p) q ((carrier L k).terminal p))
          (UncutSmoothWords.test L k p)) z d=
          (1/2:ℝ)^k*((assignments (m:=k+1) (List.finRange k)).map (fun choices =>
            ∫ x,fullAssignedWord L c k p q d z choices x ∂fullAssignedMeasure L c k p q)).sum := by
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
