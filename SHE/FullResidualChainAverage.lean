module

public import SHE.FullResidualWordAverage

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
local instance fullResidualChainAverage_periodPositive : Fact (0<2*Real.pi) := ⟨by positivity⟩
variable {X : Type} [MeasurableSpace X] {R : ReferenceData} {n : ℕ}
variable (L : Level R X n)

/-- Exact current-window smoothing identity for a genuinely constructed
physical chain. The canonical family theorem discharges the chain on
one common event for every interpolation and past-input parameter. -/
theorem full_residual_average_of_chain (c : Domain→ℝ) {k : ℕ} {p : History X k}
    (chain : Chain L k p (fun i=>i)) (hs : chain.CoordinateSupport)
    (hp : Physical L ((carrier L k).observations.observations p) c chain)
    (hZ : ∀ i,((carrier L k).observations.observations p i).stop≤
      ((carrier L k).observations.observations p i).target) :
    ∀ q : ℝ,0≤q → q≤(carrier L k).terminal p → ∀ z : WordRecursion.State (n+k),
      gaussianAverage (WordRecursion.covariance R.reference
        ((carrier L k).observations.observations p) q ((carrier L k).terminal p))
        (UncutSmoothWords.test L k p) z=
      gaussianAverage (fullResidualCovariance L c k p q) (oldAverage L c k p) z := by
  let Z:=(carrier L k).observations.observations p
  have havg : chain.oldAverage=oldAverage L c k p := by
    unfold Chain.oldAverage oldAverage
    rw [Physical.old_eq L Z c chain hp,Physical.direction_eq L Z c chain hp,
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
    rw [Physical.residual_eq L Z c chain hp]
    rfl
  have hh:=chain.predictable_eq_reserved_average hs hC z
  change gaussianAverage C (fun w=>UncutSmoothWords.test L k p (projection (fun i=>i) w)) z=_ at hh
  have hid : (fun w=>UncutSmoothWords.test L k p (projection (fun i=>i) w))=UncutSmoothWords.test L k p := rfl
  rw [hid,hres,havg] at hh
  exact hh

end SHE.PhysicalChainArrays
