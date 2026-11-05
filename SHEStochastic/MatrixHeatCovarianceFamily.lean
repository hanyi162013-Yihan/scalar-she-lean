module

public import SHEStochastic.MatrixProfileFixedPoint
public import SHE.ParametricProfile

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section

namespace SHEStochastic.MatrixHeatCovarianceFamily
open MeasureTheory MatrixHeatCovariance
open scoped NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
variable {d Z : Type*} [Fintype d] [DecidableEq d] [MeasurableSpace Z]

def covariance (κ : Z × Domain → Matrix d d ℝ)
    (p : Z × (HeatCovarianceMeasure.Window × SpatialCircle)) : Matrix d d ℝ :=
  MatrixHeatCovariance.covariance (fun q => κ (p.1,q)) p.2

/-- Joint Borel dependence of the actual full matrix covariance on an
arbitrary measurable parameter, time, and spatial center. -/
theorem measurable (κ : Z × Domain → Matrix d d ℝ) (hκ : Measurable κ)
    (M : ℝ) (hM : ∀ p, ‖κ p‖ ≤ M) : Measurable (covariance κ) := by
  apply Measurable.of_eval_matrix
  intro i j
  have hscalar := (entry i j).continuous.measurable.comp hκ
  have hp : Measurable (fun p : Z × (HeatCovarianceMeasure.Window × SpatialCircle) =>
      (p.1,(p.2.1.val,p.2.2))) :=
    measurable_fst.prodMk ((measurable_subtype_coe.comp measurable_snd.fst).prodMk measurable_snd.snd)
  have hm := (SHE.ParametricProfile.positiveVarianceFamily_measurable hscalar).comp hp
  have he : (fun p : Z × (HeatCovarianceMeasure.Window × SpatialCircle) => covariance κ p i j) =
      (fun p => SHE.ParametricProfile.positiveVarianceFamily (fun z => κ z i j)
        (p.1,(p.2.1.val,p.2.2))) := by
    funext p
    exact MatrixHeatCovariance.entry_formula (fun q => κ (p.1,q))
      (hκ.comp (measurable_const.prodMk measurable_id)) M (fun q => hM (p.1,q)) p.2 i j
  rw [he]
  exact hm

end SHEStochastic.MatrixHeatCovarianceFamily
