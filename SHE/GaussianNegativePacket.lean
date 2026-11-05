module

public import SHE.HaarFinePacket

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.GaussianNegativePacket
open Finset Set MeasureTheory AddCircle CircleHeat FiniteHaar HeatMarkov NegativeNash HaarWeightedHeat
open scoped ENNReal
local instance gaussianNegativePacket_periodPos : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩

def traceConstant : ℝ := 1+2*HeatTrace.fractionalGaussianIntegral 0

theorem traceConstant_pos : 0 < traceConstant := by
  unfold traceConstant
  linarith [(HeatTrace.fractionalGaussianIntegral_pos (by norm_num : (0:ℝ)<1/2)).le]

theorem kernel_norm_sq {s : ℝ} (hs : 0 < s) (a : AddCircle (1:ℝ)) :
    ‖HeatTorusKernel.unitHeatKernel s a‖^2 = ∑' n : ℤ, ‖heatWeight s n‖^2 := by
  rw [norm_sq_fourier]
  apply tsum_congr
  intro n
  rw [HeatTorusKernel.fourierCoeff_unitHeatKernel hs,norm_mul,
    (show ‖fourier (-n) a‖ = 1 from Circle.norm_coe _),one_mul]
  congr 1
  rw [heatWeight,max_eq_left hs.le]
  congr 2
  ring

theorem kernel_eight_norm_sq {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (a : AddCircle (1:ℝ)) :
    ‖HeatTorusKernel.unitHeatKernel (8*t) a‖^2 ≤ traceConstant*t^(-(1/2:ℝ)) := by
  rw [kernel_norm_sq (by positivity)]
  have hh := heatWeight_trace_bound (by positivity : 0 < 8*t)
  have hpow : (8*t)^(-(1/2:ℝ)) ≤ t^(-(1/2:ℝ)) :=
    Real.rpow_le_rpow_of_nonpos ht (by linarith) (by norm_num)
  have hone : 1 ≤ t^(-(1/2:ℝ)) := by
    simpa using Real.rpow_le_rpow_of_nonpos ht ht1 (by norm_num : -(1/2:ℝ) ≤ 0)
  have hG := (HeatTrace.fractionalGaussianIntegral_pos (by norm_num : (0:ℝ)<1/2)).le
  exact hh.trans (by unfold traceConstant; nlinarith)

theorem dominated_norms {t R : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (hR : 0 ≤ R)
    (a : AddCircle (1:ℝ)) (v : CircleL2)
    (hv : ∀ᵐ y ∂haarAddCircle, ‖v y‖ ≤ R*‖kernel (8*t) (by positivity) (y-a)‖) :
    ‖v‖^2 ≤ traceConstant*t^(-(1/2:ℝ))*R^2 ∧ normOne v^2 ≤ R^2 := by
  let k := HeatTorusKernel.unitHeatKernel (8*t) a
  have hk : k =ᵐ[haarAddCircle] (fun y => kernel (8*t) (by positivity) (y-a)) := unitHeatKernel_ae (by positivity) a
  have hvi : Integrable (fun y => ‖v y‖^2) haarAddCircle :=
    (memLp_two_iff_integrable_sq_norm (Lp.memLp v).aestronglyMeasurable).mp (Lp.memLp v)
  have hki : Integrable (fun y => ‖k y‖^2) haarAddCircle :=
    (memLp_two_iff_integrable_sq_norm (Lp.memLp k).aestronglyMeasurable).mp (Lp.memLp k)
  have h2 : ‖v‖^2 ≤ R^2*‖k‖^2 := by
    rw [StoppedFourier.L2_norm_sq_eq_integral,StoppedFourier.L2_norm_sq_eq_integral,← integral_const_mul]
    apply integral_mono_ae hvi (hki.const_mul _)
    filter_upwards [hv,hk] with y hy hky
    rw [hky]
    simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) hy 2
  have h1 : normOne v ≤ R := by
    unfold normOne
    have hi := ((Lp.memLp v).integrable (by norm_num : (1:ℝ≥0∞) ≤ 2)).norm
    have hki' := ((Lp.memLp k).integrable (by norm_num : (1:ℝ≥0∞) ≤ 2)).norm
    calc
      _ ≤ ∫ y, R*‖k y‖ ∂haarAddCircle := integral_mono_ae hi (hki'.const_mul _) (by
        filter_upwards [hv,hk] with y hy hky
        simpa only [hky] using hy)
      _ = R := by
        rw [integral_const_mul]
        have he : (∫ y, ‖k y‖ ∂haarAddCircle) = 1 := by
          calc
            _ = ∫ y, ‖kernel (8*t) (by positivity) (y-a)‖ ∂haarAddCircle := integral_congr_ae (by
              filter_upwards [hk] with y hy
              rw [hy])
            _ = 1 := (integral_sub_right_eq_self (μ := haarAddCircle) _ a).trans (kernel_norm_mass (by positivity))
        rw [he,mul_one]
  exact ⟨(h2.trans (mul_le_mul_of_nonneg_left (kernel_eight_norm_sq ht ht1 a) (sq_nonneg R))).trans_eq (by ring),
    pow_le_pow_left₀ (normOne_nonneg _) h1 2⟩

def constant (ρ : ℝ) : ℝ := 1+2*HeatTrace.fractionalGaussianIntegral ρ+traceConstant

theorem dominated_negative {Λ ρ t R : ℝ} (hΛ : 1 ≤ Λ) (hρ : 0 < ρ) (hρhalf : ρ < 1/2)
    (ht : 0 < t) (ht1 : t ≤ 1) (hR : 0 ≤ R) (a : AddCircle (1:ℝ)) (v : CircleL2)
    (hv : ∀ᵐ y ∂haarAddCircle, ‖v y‖ ≤ R*‖kernel (8*t) (by positivity) (y-a)‖) :
    energy Λ ρ v ≤ constant ρ*t^(ρ-1/2)*R^2 ∧
      energy Λ ρ v ≤ traceConstant*Λ^(-ρ)*t^(-(1/2:ℝ))*R^2 := by
  have hn := dominated_norms ht ht1 hR a v hv
  have hh := energy_cutoff hΛ hρ hρhalf ht ht1 v
  have hG := (HeatTrace.fractionalGaussianIntegral_pos hρhalf).le
  have hb := add_le_add
    (mul_le_mul_of_nonneg_left hn.2 (by positivity : 0 ≤ (1+2*HeatTrace.fractionalGaussianIntegral ρ)*t^(ρ-1/2)))
    (mul_le_mul_of_nonneg_left hn.1 (Real.rpow_nonneg ht.le ρ))
  have hE := CellNegative.energy_mass_le (zero_lt_one.trans_le hΛ) hρ.le v
  have hm : energy Λ ρ v ≤ Λ^(-ρ)*‖v‖^2 := by
    rw [Real.rpow_neg (zero_lt_one.trans_le hΛ).le]
    rw [mul_comm,← div_eq_mul_inv]
    exact (le_div_iff₀ (Real.rpow_pos_of_pos (zero_lt_one.trans_le hΛ) _)).mpr (by simpa only [mul_comm] using! hE)
  constructor
  · apply (hh.trans hb).trans_eq
    rw [show t^ρ*(traceConstant*t^(-(1/2:ℝ))*R^2) = traceConstant*(t^ρ*t^(-(1/2:ℝ)))*R^2 by ring,
      ← Real.rpow_add ht]
    unfold constant
    congr 1 <;> ring
  · exact (hm.trans (mul_le_mul_of_nonneg_left hn.1 (by positivity))).trans_eq (by ring)

end SHE.GaussianNegativePacket
