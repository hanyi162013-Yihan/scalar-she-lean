module

public import SHE.GaussianFullResidualScore
public import SHE.RangeTerminalRepresentation

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2700000
noncomputable section

namespace SHE.PhysicalChainArrays
open Set Filter MeasureTheory ProbabilityTheory AddCircle StoppedFourier WordRecursion
  CutoffWordLevel CutoffWordHistories CutoffCarriers GaussianCoordinates ProjectedUncutWord PhysicalScoreChain
  OldIntervalCovariance StoppedGaussianFeatures GaussianConvolution GaussianAssignmentBlocks
  MeasurableGaussianScores SmoothCylinders
open scoped BigOperators
local instance physicalFullResidualScore_periodPos : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
variable {X : Type} [MeasurableSpace X] {R : ReferenceData} {n : ℕ}
variable (L : CutoffWordLevel.Level R X n)

/-- The full remaining covariance after removing just the fixed old
fractions. The complete current window is left in the fresh Gaussian. -/
def fullResidualCovariance (c : Domain → ℝ) (k : ℕ) (p : History X k) (q : ℝ) :
    Matrix (Fin (n+k)) (Fin (n+k)) ℝ :=
  WordRecursion.covariance R.reference ((carrier L k).observations.observations p)
    q ((carrier L k).terminal p)+
      ∑ j,covariances L ((carrier L k).observations.observations p)
        (fun r => R.reference r-c r) k p j

/-- Exact first-score representation in the whole remaining future
covariance. It retains every original old score and requires only the
true full-residual range, rather than the smaller common front range. -/
theorem full_residual_first_score_ae (c : Domain → ℝ) (hc : Measurable c)
    {ell : ℝ} (hell : 0 < ell) (hb : ∀ z,ell ≤ c z ∧ c z ≤ R.reference z)
    (hages : ∀ p i,(L.observations.observations p i).stop ≤ (L.observations.observations p i).target)
    (μ : Measure X) [IsFiniteMeasure μ] (k : ℕ) :
    ∀ᵐ p ∂CutoffWordHistories.historyMeasure R μ k,
      ∀ q : ℝ,0 ≤ q → q < (carrier L k).terminal p →
      (fullResidualCovariance L c k p q).PosSemidef ∧
      ∀ d z : WordRecursion.State (n+k),
        d ∈ (Matrix.toEuclideanCLM (𝕜:=ℝ) (fullResidualCovariance L c k p q)).range →
        fderiv ℝ (gaussianAverage (WordRecursion.covariance R.reference
          ((carrier L k).observations.observations p) q ((carrier L k).terminal p))
          (UncutSmoothWords.test L k p)) z d=
          ∫ y,oldAverage L c k p (z+y)*firstScore (fullResidualCovariance L c k p q) d y
            ∂multivariateGaussian 0 (fullResidualCovariance L c k p q) := by
  filter_upwards [exists_chain_ae L c hc hell hb hages μ k] with p hp
  obtain ⟨chain,hs,_,hphysical⟩ := hp
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

end SHE.PhysicalChainArrays
