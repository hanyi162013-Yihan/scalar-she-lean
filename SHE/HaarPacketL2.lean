module

public import SHE.HaarGeometry
public import SHE.HaarCancellation
public import SHE.HaarSingleHeat

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHE.FiniteHaar
open Finset Set MeasureTheory AddCircle CircleHeat
local instance haarPacketL2_periodPos : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

def nodeIndicator (p : List Bool) : CircleL2 := nodeRestriction p circleOne

theorem nodeIndicator_ae (p : List Bool) :
    nodeIndicator p =ᵐ[haarAddCircle] (nodeCell p).indicator (fun _ => (1 : ℂ)) := by
  filter_upwards [nodeRestriction_ae p circleOne, circleOne_ae] with y hr ho
  change nodeIndicator p y = _ at hr
  rw [hr]
  by_cases hy : y ∈ nodeCell p
  · simp only [Set.indicator_of_mem hy, ho]
  · simp only [Set.indicator_of_notMem hy]

theorem nodeRestriction_inner (p : List Bool) (u v : CircleL2) :
    inner ℂ u (nodeRestriction p v) = inner ℂ (nodeRestriction p u) v := by
  simp only [nodeRestriction, add_apply, inner_add_left, inner_add_right,
    cellRestriction_inner]

theorem nodeRestriction_eq_of_supported (p : List Bool) (v : CircleL2)
    (hv : ∀ᵐ y ∂haarAddCircle, y ∉ nodeCell p → v y = 0) : nodeRestriction p v = v := by
  apply Lp.ext
  filter_upwards [nodeRestriction_ae p v, hv] with y hr hv
  rw [hr]
  by_cases hy : y ∈ nodeCell p
  · rw [Set.indicator_of_mem hy]
  · rw [Set.indicator_of_notMem hy, hv hy]

theorem nodeRestriction_idempotent (p : List Bool) (v : CircleL2) :
    nodeRestriction p (nodeRestriction p v) = nodeRestriction p v := by
  apply nodeRestriction_eq_of_supported
  filter_upwards [nodeRestriction_ae p v] with y hr
  intro hy
  rw [hr, Set.indicator_of_notMem hy]

theorem nodeIndicator_norm_sq (p : List Bool) : ‖nodeIndicator p‖ ^ 2 = nodeLength p := by
  have he : inner ℂ circleOne (nodeIndicator p) = inner ℂ (nodeIndicator p) (nodeIndicator p) := by
    change inner ℂ circleOne (nodeRestriction p circleOne) =
      inner ℂ (nodeRestriction p circleOne) (nodeRestriction p circleOne)
    rw [← nodeRestriction_inner, nodeRestriction_idempotent]
  rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ), ← he]
  change (inner ℂ circleOne (nodeIndicator p)).re = _
  unfold nodeIndicator nodeRestriction
  rw [add_apply, inner_add_right, Complex.add_re]
  have hc (b : Bool) :
      (inner ℂ circleOne (cellRestriction (p.length+1) (bottomLeaf p b) circleOne)).re =
        (((2 ^ (p.length+1) : ℕ) : ℝ))⁻¹ := by
    have he : inner ℂ circleOne (cellRestriction (p.length+1) (bottomLeaf p b) circleOne) =
      inner ℂ (cellRestriction (p.length+1) (bottomLeaf p b) circleOne)
        (cellRestriction (p.length+1) (bottomLeaf p b) circleOne) := by
      rw [← cellRestriction_inner, cellRestriction_idempotent]
    rw [he]
    rw [cellRestriction_one]
    change RCLike.re (inner ℂ (cellIndicator (p.length+1) (bottomLeaf p b))
      (cellIndicator (p.length+1) (bottomLeaf p b))) = _
    rw [← InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ), cellIndicator_norm_sq]
  rw [hc false, hc true]
  unfold nodeLength
  ring

theorem nodeRestriction_bounded_norm (p : List Bool) (v : CircleL2) (M : ℝ)
    (hv : ∀ᵐ y ∂haarAddCircle, y ∈ nodeCell p → ‖v y‖ ≤ M) :
    ‖nodeRestriction p v‖ ≤ M * ‖nodeIndicator p‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [nodeRestriction_ae p v, nodeIndicator_ae p, hv] with y hr hi hv
  rw [hr, hi]
  by_cases hy : y ∈ nodeCell p
  · simpa only [Set.indicator_of_mem hy, norm_one, mul_one] using hv hy
  · simp only [Set.indicator_of_notMem hy, norm_zero, mul_zero, le_refl]

def nodeFourierDifference (p : List Bool) (n : ℤ) : CircleL2 :=
  fourierBasis n - (fourier n (nodeCenter p) : ℂ) • circleOne

theorem nodeFourierDifference_ae (p : List Bool) (n : ℤ) :
    nodeFourierDifference p n =ᵐ[haarAddCircle]
      (fun y => (fourier n y : ℂ) - fourier n (nodeCenter p)) := by
  filter_upwards [Lp.coeFn_sub (fourierBasis n) ((fourier n (nodeCenter p) : ℂ) • circleOne),
    Lp.coeFn_smul (fourier n (nodeCenter p) : ℂ) circleOne,
    coeFn_fourierLp 2 n, circleOne_ae] with y hs hm hf ho
  change nodeFourierDifference p n y = _ at hs
  rw [hs]
  simp only [Pi.sub_apply]
  rw [hm]
  simp only [Pi.smul_apply, smul_eq_mul, ho, mul_one]
  rw [coe_fourierBasis]
  exact congrArg (fun z : ℂ => z - fourier n (nodeCenter p)) hf

theorem nodeFourierDifference_restricted_norm (p : List Bool) (n : ℤ) :
    ‖nodeRestriction p (nodeFourierDifference p n)‖ ≤
      (2 * Real.pi * |(n : ℝ)| * nodeLength p) * ‖nodeIndicator p‖ := by
  apply nodeRestriction_bounded_norm
  filter_upwards [nodeFourierDifference_ae p n] with y hy
  intro hm
  rw [hy]
  exact (fourier_lipschitz_bound n y (nodeCenter p)).trans
    (mul_le_mul_of_nonneg_left (nodeCell_distance p y hm) (by positivity))

/-- Literal interval support and zero mean imply a quantitative Fourier
cancellation estimate, for arbitrary circle `L²` functions. -/
theorem supported_mean_zero_fourier (p : List Bool) (v : CircleL2)
    (hv : ∀ᵐ y ∂haarAddCircle, y ∉ nodeCell p → v y = 0)
    (hz : inner ℂ circleOne v = 0) (n : ℤ) :
    ‖fourierCoeff v n‖ ^ 2 ≤
      (2 * Real.pi * (n : ℝ)) ^ 2 * (nodeLength p) ^ 3 * ‖v‖ ^ 2 := by
  have he : inner ℂ (nodeFourierDifference p n) v = fourierCoeff v n := by
    simp only [nodeFourierDifference, inner_sub_left, inner_smul_left, hz, mul_zero, sub_zero]
    rw [← fourierBasis_repr, HilbertBasis.repr_apply_apply]
  have hr : inner ℂ (nodeRestriction p (nodeFourierDifference p n)) v = fourierCoeff v n := by
    rw [← nodeRestriction_inner, nodeRestriction_eq_of_supported p v hv, he]
  have hb := (norm_inner_le_norm (𝕜 := ℂ) (nodeRestriction p (nodeFourierDifference p n)) v).trans
    (mul_le_mul_of_nonneg_right (nodeFourierDifference_restricted_norm p n) (norm_nonneg v))
  rw [hr] at hb
  have hs := pow_le_pow_left₀ (norm_nonneg (fourierCoeff v n)) hb 2
  calc
    _ ≤ ((2 * Real.pi * |(n : ℝ)| * nodeLength p) * ‖nodeIndicator p‖ * ‖v‖) ^ 2 := hs
    _ = _ := by
      rw [mul_pow, mul_pow, nodeIndicator_norm_sq, mul_pow, mul_pow, sq_abs]
      ring

def heatGradientTrace (t : ℝ) : ℝ :=
  ∑' n : ℤ, (2 * Real.pi * (n : ℝ)) ^ 2 * ‖heatWeight t n‖ ^ 2

theorem heatGradientWeight_bound {t : ℝ} (ht : 0 < t) (n : ℤ) :
    (2 * Real.pi * (n : ℝ)) ^ 2 * ‖heatWeight t n‖ ^ 2 ≤
      t⁻¹ * ‖heatWeight (t/2) n‖ ^ 2 := by
  rw [heatWeight_norm_sq ht.le, heatWeight_norm_sq (by positivity : 0 ≤ t/2)]
  let a : ℝ := (2 * Real.pi * (n : ℝ)) ^ 2
  have hh : (t*a) * Real.exp (-(t*a)) ≤ 1 :=
    (Real.mul_exp_neg_le_exp_neg_one (t*a)).trans (Real.exp_le_one_iff.mpr (by norm_num))
  have he := mul_le_mul_of_nonneg_right hh (Real.exp_pos (-(t*a))).le
  rw [mul_assoc, ← Real.exp_add] at he
  rw [show -(t*a) + -(t*a) = -(2*t)*a by ring, one_mul] at he
  have he' : t * (a * Real.exp (-(2*t)*a)) ≤ Real.exp (-t*a) := by
    simpa only [mul_assoc, neg_mul] using he
  change a * Real.exp (-(2*t)*a) ≤ t⁻¹ * Real.exp (-(2*(t/2))*a)
  rw [show 2*(t/2) = t by ring]
  rw [← div_eq_inv_mul]
  apply (le_div_iff₀ ht).mpr
  simpa only [mul_comm] using he'

theorem heatGradientWeight_summable {t : ℝ} (ht : 0 < t) :
    Summable (fun n : ℤ => (2 * Real.pi * (n : ℝ)) ^ 2 * ‖heatWeight t n‖ ^ 2) :=
  Summable.of_nonneg_of_le (fun _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
    (heatGradientWeight_bound ht) ((heatWeight_square_summable (by positivity : 0 < t/2)).mul_left _)

def packetHeatConstant : ℝ :=
  1 + 2 * HeatTrace.fractionalGaussianIntegral 0 * (1/2 : ℝ) ^ (-(1/2 : ℝ))

theorem packetHeatConstant_one_le : 1 ≤ packetHeatConstant := by
  have hh := (HeatTrace.fractionalGaussianIntegral_pos (by norm_num : (0:ℝ)<1/2)).le
  unfold packetHeatConstant
  have hh' : 0 ≤ 2 * HeatTrace.fractionalGaussianIntegral 0 * (1/2 : ℝ) ^ (-(1/2 : ℝ)) := by positivity
  linarith

theorem heatGradientTrace_bound {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    heatGradientTrace t ≤ packetHeatConstant * t ^ (-(3/2 : ℝ)) := by
  have hG := (HeatTrace.fractionalGaussianIntegral_pos (by norm_num : (0:ℝ)<1/2)).le
  have htp : 1 ≤ t ^ (-(1/2 : ℝ)) := by
    simpa using Real.rpow_le_rpow_of_nonpos ht ht1 (by norm_num : -(1/2:ℝ) ≤ 0)
  calc
    _ ≤ ∑' n : ℤ, t⁻¹ * ‖heatWeight (t/2) n‖ ^ 2 :=
      (heatGradientWeight_summable ht).tsum_le_tsum (heatGradientWeight_bound ht)
        ((heatWeight_square_summable (by positivity : 0 < t/2)).mul_left _)
    _ = t⁻¹ * (∑' n : ℤ, ‖heatWeight (t/2) n‖ ^ 2) := tsum_mul_left
    _ ≤ t⁻¹ * (1 + 2 * HeatTrace.fractionalGaussianIntegral 0 * (t/2) ^ (-(1/2 : ℝ))) :=
      mul_le_mul_of_nonneg_left (heatWeight_trace_bound (by positivity : 0 < t/2)) (by positivity)
    _ ≤ t⁻¹ * (t ^ (-(1/2 : ℝ)) +
        2 * HeatTrace.fractionalGaussianIntegral 0 * (t/2) ^ (-(1/2 : ℝ))) := by gcongr
    _ = _ := by
      rw [show t/2 = t*(1/2:ℝ) by ring, Real.mul_rpow ht.le (by norm_num)]
      rw [show t⁻¹ = t ^ (-1:ℝ) by rw [Real.rpow_neg_one]]
      rw [show (-(3/2:ℝ)) = -1 + -(1/2:ℝ) by ring, Real.rpow_add ht]
      unfold packetHeatConstant
      ring

/-- A genuine periodic `L²` packet cancellation estimate, derived from
Fourier Lipschitz continuity, its literal support, and Parseval. -/
theorem supported_mean_zero_heat_trace {t : ℝ} (ht : 0 < t)
    (p : List Bool) (v : CircleL2)
    (hv : ∀ᵐ y ∂haarAddCircle, y ∉ nodeCell p → v y = 0)
    (hz : inner ℂ circleOne v = 0) :
    ‖heat t v‖ ^ 2 ≤ (nodeLength p) ^ 3 * heatGradientTrace t * ‖v‖ ^ 2 := by
  rw [norm_sq_fourier]
  have hm (n : ℤ) : ‖fourierCoeff (heat t v) n‖ ^ 2 ≤
      ((nodeLength p) ^ 3 * ‖v‖ ^ 2) *
        ((2 * Real.pi * (n : ℝ)) ^ 2 * ‖heatWeight t n‖ ^ 2) := by
    rw [heat_fourierCoeff, norm_mul, mul_pow]
    exact (mul_le_mul_of_nonneg_left (supported_mean_zero_fourier p v hv hz n) (sq_nonneg _)).trans_eq (by ring)
  calc
    _ ≤ ∑' n : ℤ, ((nodeLength p) ^ 3 * ‖v‖ ^ 2) *
        ((2 * Real.pi * (n : ℝ)) ^ 2 * ‖heatWeight t n‖ ^ 2) :=
      (summable_fourier_sq (heat t v)).tsum_le_tsum hm ((heatGradientWeight_summable ht).mul_left _)
    _ = _ := by rw [tsum_mul_left]; unfold heatGradientTrace; ring

/-- Heat cancellation for every mean-zero packet on a literal periodic
dyadic node; neither a step-function assumption nor a smoothing estimate
is a premise. The constant is independent of the node and its depth. -/
theorem supported_mean_zero_heat {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (p : List Bool) (v : CircleL2)
    (hv : ∀ᵐ y ∂haarAddCircle, y ∉ nodeCell p → v y = 0)
    (hz : inner ℂ circleOne v = 0) :
    ‖heat t v‖ ^ 2 ≤ packetHeatConstant *
      min 1 ((nodeLength p) ^ 2 / t) * ‖v‖ ^ 2 := by
  have hl : 0 < nodeLength p := nodeLength_pos p
  have hC : 0 ≤ packetHeatConstant := zero_le_one.trans packetHeatConstant_one_le
  by_cases hr : (nodeLength p) ^ 2 / t ≤ 1
  · rw [min_eq_right hr]
    have hs : nodeLength p ≤ Real.sqrt t := by
      have hh := (div_le_iff₀ ht).mp hr
      nlinarith [Real.sq_sqrt ht.le, Real.sqrt_nonneg t]
    have he : Real.sqrt t * t ^ (-(1/2 : ℝ)) = 1 := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add ht]
      norm_num
    have hm : nodeLength p * t ^ (-(1/2 : ℝ)) ≤ 1 := by
      exact (mul_le_mul_of_nonneg_right hs (Real.rpow_nonneg ht.le _)).trans_eq he
    calc
      _ ≤ (nodeLength p) ^ 3 * (packetHeatConstant * t ^ (-(3/2 : ℝ))) * ‖v‖ ^ 2 :=
        (supported_mean_zero_heat_trace ht p v hv hz).trans
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (heatGradientTrace_bound ht ht1)
            (by positivity)) (sq_nonneg _))
      _ = (packetHeatConstant * ((nodeLength p) ^ 2 / t) * ‖v‖ ^ 2) *
          (nodeLength p * t ^ (-(1/2 : ℝ))) := by
        rw [show (-(3/2:ℝ)) = -1 + -(1/2:ℝ) by ring, Real.rpow_add ht, Real.rpow_neg_one]
        ring
      _ ≤ _ := (mul_le_mul_of_nonneg_left hm (by positivity)).trans_eq (mul_one _)
  · rw [min_eq_left (le_of_not_ge hr), mul_one]
    exact (pow_le_pow_left₀ (norm_nonneg _) (heat_contraction t v) 2).trans
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_right packetHeatConstant_one_le (sq_nonneg ‖v‖))

end SHE.FiniteHaar
