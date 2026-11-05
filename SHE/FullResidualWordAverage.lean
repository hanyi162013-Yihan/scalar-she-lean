module

public import SHE.PhysicalFullResidualScore

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.PhysicalChainArrays
open Set Filter MeasureTheory ProbabilityTheory AddCircle StoppedFourier WordRecursion
  CutoffWordLevel CutoffWordHistories CutoffCarriers GaussianCoordinates ProjectedUncutWord PhysicalScoreChain
  OldIntervalCovariance StoppedGaussianFeatures GaussianConvolution GaussianAssignmentBlocks
open scoped BigOperators
local instance fullResidualWordAverage_periodPositive : Fact (0<2*Real.pi) := ⟨by positivity⟩
variable {X : Type} [MeasurableSpace X] {R : ReferenceData} {n : ℕ}
variable (L : Level R X n)

/-- The actual recursively inserted test, smoothed over its whole
current window, equals its fixed-old score average under the entire
remaining future covariance. This value identity retains the original
root and every centered leaf, and has no score/range applicability
premise. It applies at EVERY mean on one genuine history event. -/
theorem full_residual_average_ae (c : Domain→ℝ) (hc : Measurable c)
    {ell : ℝ} (hell : 0<ell) (hb : ∀ z,ell≤c z ∧ c z≤R.reference z)
    (hages : ∀ p i,(L.observations.observations p i).stop≤(L.observations.observations p i).target)
    (μ : Measure X) [IsFiniteMeasure μ] (k : ℕ) :
    ∀ᵐ p ∂CutoffWordHistories.historyMeasure R μ k,
      ∀ q : ℝ,0≤q → q≤(carrier L k).terminal p → ∀ z : WordRecursion.State (n+k),
      gaussianAverage (WordRecursion.covariance R.reference
        ((carrier L k).observations.observations p) q ((carrier L k).terminal p))
        (UncutSmoothWords.test L k p) z=
      gaussianAverage (fullResidualCovariance L c k p q) (oldAverage L c k p) z := by
  filter_upwards [exists_chain_ae L c hc hell hb hages μ k] with p hp
  obtain ⟨chain,hs,_,hphysical⟩:=hp
  let Z:=(carrier L k).observations.observations p
  have hZ : ∀ i,(Z i).stop≤(Z i).target:=RecursiveScoreSupport.carrier_ages L hages k p
  have havg : chain.oldAverage=oldAverage L c k p := by
    unfold Chain.oldAverage oldAverage
    rw [Physical.old_eq L Z c chain hphysical,Physical.direction_eq L Z c chain hphysical,
      fullTest_eq_word L chain]
  intro q hq hqt z
  let C:=WordRecursion.covariance R.reference Z q ((carrier L k).terminal p)
  have hC : C.PosSemidef := by
    have he:=PhysicalIntervalCovariance.interval_eq_covariance Z R.reference R.reference_measurable
      R.reference_bound hZ ((carrier L k).stops_after p) hq hqt
    change (WordRecursion.covariance R.reference Z q ((carrier L k).terminal p)).PosSemidef
    rw [←he]
    exact PhysicalFirstScore.interval_posSemidef Z hZ R.reference R.reference_measurable
      (fun r=>⟨R.reference_nonneg r,(le_abs_self _).trans (R.reference_bound r)⟩)
      q ((carrier L k).terminal p)
  have hres : C+∑ j,chain.residual j=fullResidualCovariance L c k p q := by
    rw [Physical.residual_eq L Z c chain hphysical]
    rfl
  have hh:=chain.predictable_eq_reserved_average hs hC z
  change gaussianAverage C (fun w=>UncutSmoothWords.test L k p (projection (fun i=>i) w)) z=_ at hh
  have hid : (fun w=>UncutSmoothWords.test L k p (projection (fun i=>i) w))=UncutSmoothWords.test L k p := rfl
  rw [hid,hres,havg] at hh
  exact hh

end SHE.PhysicalChainArrays
