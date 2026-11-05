module

public import SHE.GaussianPeriodizedLocal
public import SHE.NativeHeatSpan

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.GaussianWeightKernel
open Set Filter MeasureTheory ProbabilityTheory AddCircle HeatLine HeatPeriodization FourierHeatLine LineGaussianLocal
open scoped BigOperators
local instance gaussianWeightKernel_periodPositive : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

/-- The Gaussian distance envelope is dominated by the actual normalized
positive heat kernel at twice the age. This preserves its spatial parent
and gives a genuine mass-one heat-tree edge. -/
theorem weight_le_kernel {t : ℝ} (ht : 0 < t) (a x : UnitAddCircle) :
    GlobalTorusHeatSpan.weight t a x ≤
      Real.sqrt (8*Real.pi) * ‖HeatMarkov.kernel (2*t) (by positivity) (x-a)‖ := by
  let r : ℝ := AddCircle.equivIco 1 (-(1/2:ℝ)) (x-a)
  have hr : (r : UnitAddCircle) = x-a := AddCircle.coe_equivIco
  have hrb : |r| ≤ 1/2 := by
    have hh := (AddCircle.equivIco 1 (-(1/2:ℝ)) (x-a)).property
    exact abs_le.mpr ⟨hh.1, by linarith [hh.2]⟩
  have hdist : dist x a = |r| := by
    rw [dist_eq_norm, ← hr]
    exact (AddCircle.norm_coe_eq_abs_iff 1 one_ne_zero).mpr (by simpa only [abs_one] using hrb)
  have hs := (GaussianPeriodizedLocal.gaussian_summable (by positivity : 0 < 2*t) r).sum_le_tsum
    ({0} : Finset ℤ) (fun _ _ => (Real.exp_pos _).le)
  simp only [Finset.sum_singleton, Int.cast_zero, add_zero] at hs
  have hmass : heatMass (2*t) = Real.sqrt (8*Real.pi) * Real.sqrt t := by
    unfold heatMass
    rw [← Real.sqrt_mul (by positivity : 0 ≤ 8*Real.pi)]
    congr 1
    ring
  rw [← hr, GaussianPeriodizedLocal.kernel_coe_norm (by positivity : 0 < 2*t) r, hmass]
  have hnorm : Real.sqrt (8*Real.pi) * (Real.sqrt (8*Real.pi) * Real.sqrt t)⁻¹ = (Real.sqrt t)⁻¹ := by
    rw [mul_inv_rev]
    field_simp
  rw [← mul_assoc, hnorm]
  unfold GlobalTorusHeatSpan.weight
  rw [hdist, sq_abs]
  convert mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr (Real.sqrt_nonneg t)) using 1 <;>
    simp only [gaussian, show 4*(2*t)=8*t by ring]

end SHE.GaussianWeightKernel
