module

public import SHEStochastic.MatrixHeatCovariance
public import SHE.ProfileL2

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section

namespace SHEStochastic.MatrixHeatCovarianceL2
open MeasureTheory Set MatrixHeatCovariance SHE.ProfileL2 SHE.ProfileVariance SHE.StoppedFourier
open scoped NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
variable {d : Type*} [Fintype d] [DecidableEq d]

/-- The Bochner covariance is dominated by the scalar positive heat
map of the matrix norm. This avoids entrywise dimension losses. -/
theorem pointwise (κ η : Domain → Matrix d d ℝ) (hκ : Measurable κ) (hη : Measurable η)
    (M : ℝ) (hκM : ∀ p, ‖κ p‖ ≤ M) (hηM : ∀ p, ‖η p‖ ≤ M)
    (p : HeatCovarianceMeasure.Window × SpatialCircle) :
    ‖covariance κ p-covariance η p‖ ≤
      varianceMap (fun z => ‖κ z-η z‖) p.1.val p.2 := by
  unfold covariance
  rw [← integral_sub (integrable κ hκ M hκM p) (integrable η hη M hηM p)]
  apply (norm_integral_le_integral_norm _).trans_eq
  apply HeatCovarianceMeasure.scalar_integral p.1 p.2 _ (hκ.sub hη).norm (2*M)
  intro z
  rw [abs_of_nonneg (norm_nonneg _)]
  exact (norm_sub_le _ _).trans (by linarith [hκM z,hηM z])

theorem measurable (κ : Domain → Matrix d d ℝ) (hκ : Measurable κ) (M : ℝ)
    (hκM : ∀ p, ‖κ p‖ ≤ M) (r : HeatCovarianceMeasure.Window) :
    Measurable (fun x => covariance κ (r,x)) :=
  (MatrixHeatCovariance.measurable κ hκ M hκM).comp (measurable_const.prodMk measurable_id)

/-- The matrix heat covariance obeys exactly the scalar singular L2
memory bound, by domination through the positive heat-square kernel. -/
theorem bound (κ η : Domain → Matrix d d ℝ) (hκ : Measurable κ) (hη : Measurable η)
    (M : ℝ) (hM : 0 ≤ M) (hκM : ∀ p, ‖κ p‖ ≤ M) (hηM : ∀ p, ‖η p‖ ≤ M)
    (r : HeatCovarianceMeasure.Window) :
    normTwo AddCircle.haarAddCircle (fun x => ‖covariance κ (r,x)-covariance η (r,x)‖) ≤
      (1+heatConstant)*(∫ s in (0 : ℝ)..r.val, (r.val-s)^(-(1/2 : ℝ))*
        normTwo AddCircle.haarAddCircle (fun y => ‖κ (s,y)-η (s,y)‖)) := by
  have hdiff : ∀ z, ‖κ z-η z‖ ≤ 2*M := fun z => (norm_sub_le _ _).trans
    (by linarith [hκM z,hηM z])
  have hscalar := (hκ.sub hη).norm
  have hv := varianceMap_memLp hscalar r.property.1 r.property.2 (by positivity : 0 ≤ 2*M)
    (fun s hs y => by rw [abs_of_nonneg (norm_nonneg _)]; exact hdiff (s,y))
  have hm := (measurable κ hκ M hκM r).sub (measurable η hη M hηM r)
  have ht : MemLp (fun x => ‖covariance κ (r,x)-covariance η (r,x)‖) 2 AddCircle.haarAddCircle := by
    apply bounded_memLp (C := upperConstant*(2*M)*r.val^(1/2 : ℝ)) hm.norm
    intro x
    rw [abs_of_nonneg (norm_nonneg _)]
    change ‖covariance κ (r,x)-covariance η (r,x)‖ ≤ _
    exact MatrixHeatCovariance.difference κ η hκ hη M (2*M) (by positivity) hκM hηM hdiff (r,x)
  apply (normTwo_mono ht hv (Filter.Eventually.of_forall fun x => ?_)).trans
    (varianceMap_normTwo_bound hscalar r.property.1 r.property.2 (by positivity : 0 ≤ 2*M)
      (fun s hs y => by rw [abs_of_nonneg (norm_nonneg _)]; exact hdiff (s,y)))
  rw [abs_of_nonneg (norm_nonneg _)]
  exact (pointwise κ η hκ hη M hκM hηM (r,x)).trans (le_abs_self _)

end SHEStochastic.MatrixHeatCovarianceL2
