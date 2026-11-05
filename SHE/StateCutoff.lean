module

public import SHE.SmoothCylinders
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section

namespace SHE.StateCutoff
open Set Filter MeasureTheory
open scoped Topology ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def unit : ContDiffBump (0:E) where
  rIn := 1
  rOut := 2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

def cutoff (R : ℝ) (z : E) : ℝ := (unit (E := E)) (R⁻¹ • z)

theorem nonneg (R : ℝ) (z : E) : 0≤cutoff R z := (unit (E := E)).nonneg
theorem le_one (R : ℝ) (z : E) : cutoff R z≤1 := (unit (E := E)).le_one
theorem abs_le_one (R : ℝ) (z : E) : |cutoff R z|≤1 := by
  rw [abs_of_nonneg (nonneg R z)]
  exact le_one R z

theorem smooth (R : ℝ) : ContDiff ℝ ∞ (cutoff (E := E) R) :=
  (unit (E := E)).contDiff.comp (contDiff_const.smul contDiff_id)

theorem eq_one {R : ℝ} (hR : 0<R) {z : E} (hz : ‖z‖≤R) : cutoff R z=1 := by
  apply (unit (E := E)).one_of_mem_closedBall
  change dist (R⁻¹ • z) (0:E)≤1
  rw [dist_zero_right,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hR,← div_eq_inv_mul]
  exact (div_le_one hR).mpr hz

theorem eventuallyEq_one {R : ℝ} (hR : 0<R) {z : E} (hz : ‖z‖<R) :
    cutoff (E := E) R=ᶠ[𝓝 z] (fun _ => (1:ℝ)) := by
  have he : ∀ᶠ w in 𝓝 z,‖w‖<R := continuous_norm.continuousAt.eventually (gt_mem_nhds hz)
  filter_upwards [he] with w hw
  exact eq_one hR hw.le

theorem zero_of_norm_large {R : ℝ} (hR : 0<R) {z : E} (hz : 2*R≤‖z‖) : cutoff R z=0 := by
  apply (unit (E := E)).zero_of_le_dist
  change 2≤dist (R⁻¹ • z) (0:E)
  rw [dist_zero_right,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hR,← div_eq_inv_mul]
  exact (le_div_iff₀ hR).mpr hz

theorem norm_lt_of_ne_zero {R : ℝ} (hR : 0<R) {z : E} (hz : cutoff R z≠0) : ‖z‖<2*R := by
  by_contra hn
  exact hz (zero_of_norm_large hR (le_of_not_gt hn))

/-- All genuine Fréchet derivatives of the expanding cutoffs admit
bounds independent of their radius R≥1. -/
theorem uniform_derivative_bound (k : ℕ) : ∃ B : ℝ,0≤B ∧
    ∀ R : ℝ,1≤R → ∀ z : E,‖iteratedFDeriv ℝ k (cutoff R) z‖≤B := by
  obtain ⟨B,hB,hbound⟩ := (unit (E := E)).hasCompactSupport.exists_bound_iteratedFDeriv
    (unit (E := E)).contDiff k
  refine ⟨B,hB,fun R hR z => ?_⟩
  have hR0 : 0<R := lt_of_lt_of_le zero_lt_one hR
  have hi : 0≤R⁻¹ := inv_nonneg.mpr hR0.le
  have hi1 : R⁻¹≤1 := inv_le_one_of_one_le₀ hR
  have he := congrFun (iteratedFDeriv_comp_const_smul R⁻¹
    ((unit (E := E)).contDiff : ContDiff ℝ k (unit (E := E)))) z
  change ‖iteratedFDeriv ℝ k (fun x : E => (unit (E := E)) (R⁻¹ • x)) z‖≤B
  rw [he,norm_smul,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg hi k)]
  calc
    _≤1*‖iteratedFDeriv ℝ k (unit (E := E)) (R⁻¹ • z)‖ :=
      mul_le_mul_of_nonneg_right (pow_le_one₀ hi hi1) (norm_nonneg _)
    _≤B := by simpa only [one_mul] using hbound k le_rfl (R⁻¹ • z)

end SHE.StateCutoff
