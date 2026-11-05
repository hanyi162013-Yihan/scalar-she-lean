module

public import SHE.LocalizedItoTest

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1300000
noncomputable section

namespace SHE.LocalizedPathStability
open Set Filter LocalizedItoTest
open scoped Topology
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Expanding state cutoffs eventually preserve every value, gradient,
Hessian and time derivative along an entire continuous path segment.
The cutoff threshold may depend on the path. -/
theorem eventually_jets_on_path (a b : ℝ) (G dG : ℝ→E→ℝ)
    (Y : ℝ→E) (hY : ContinuousOn Y (Icc a b)) :
    ∀ᶠ n in atTop,∀ t∈Icc a b,
      localized n G t (Y t)=G t (Y t) ∧
      fderiv ℝ (localized n G t) (Y t)=fderiv ℝ (G t) (Y t) ∧
      GaussianTaylor.hessian (localized n G t) (Y t)=GaussianTaylor.hessian (G t) (Y t) ∧
      localized n dG t (Y t)=dG t (Y t) := by
  obtain ⟨B,hB⟩ := (isCompact_Icc : IsCompact (Icc a b)).exists_bound_of_continuousOn hY
  have he := (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop).eventually
    (eventually_gt_atTop B)
  filter_upwards [he] with n hn t ht
  have hz : ‖Y t‖<(n:ℝ)+1 := (hB t ht).trans_lt (by linarith)
  have hj := localized_jets_eq n G t hz
  refine ⟨hj.1,hj.2.1,hj.2.2,?_⟩
  rw [localized,StateCutoff.eq_one (by positivity : 0<(n:ℝ)+1) hz.le,one_mul]

end SHE.LocalizedPathStability
