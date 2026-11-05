module

public import SHE.PolynomialGaussianTime
public import SHE.ScalarHeatBandEnvelope
public import SHE.GaussianProfile

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
namespace SHE.PolynomialGaussianDecay
open Set MeasureTheory ProbabilityTheory Real ScalarHeatBandEnvelope ScalarGaussianSemigroup SmoothCylinders
open scoped NNReal ENNReal

theorem min_sq {u : ℝ} (hu : 0≤u) : (min 1 u)^2=min 1 (u^2):=by
  by_cases h : u≤1
  · rw [min_eq_right h,min_eq_right (by nlinarith : u^2≤1)]
  · rw [min_eq_left (le_of_not_ge h),min_eq_left (by nlinarith [le_of_not_ge h] : 1≤u^2)]
    norm_num

/-- The square of the actual polynomial variance envelope is dominated
by one scale-invariant physical-time kernel whenever elliptic variance
is at least c sqrt(t). -/
theorem decay_sq_bound {r c t σ s : ℝ} (hr : 0<r) (hc : 0<c) (ht : 0<t)
    (hs : 0≤s) (hσ : c*sqrt t≤σ) :
    decay r σ s^2≤min 1 (((c^2/r^4)*t)^(-s)) := by
  have hsqrt : 0<sqrt t:=sqrt_pos.2 ht
  have hσpos : 0<σ:=(mul_pos hc hsqrt).trans_le hσ
  have hbase : 0<σ/r^2:=div_pos hσpos (sq_pos_of_pos hr)
  have hlow : 0<(c^2/r^4)*t:=mul_pos (div_pos (sq_pos_of_pos hc) (pow_pos hr 4)) ht
  have hcomp : (c^2/r^4)*t≤(σ/r^2)^2:=by
    have he : (c*sqrt t/r^2)^2=(c^2/r^4)*t:=by
      rw [div_pow,mul_pow,sq_sqrt ht.le]
      ring
    rw [←he]
    exact pow_le_pow_left₀ (div_nonneg (mul_nonneg hc.le hsqrt.le) (sq_nonneg r))
      (div_le_div_of_nonneg_right hσ (sq_nonneg r)) 2
  have he : ((σ/r^2)^(-s))^2=((σ/r^2)^2)^(-s):=by
    rw [Real.rpow_pow_comm hbase.le]
  rw [decay,min_sq (rpow_nonneg hbase.le _),he]
  exact min_le_min_left 1 (rpow_le_rpow_of_nonpos hlow hcomp (neg_nonpos.mpr hs))

/-- The finite derivative used in the martingale is genuinely jointly
Borel in its future variance and current physical mean. -/
theorem derivative_measurable {a : ℝ→ℝ} (ha : BoundedSmooth a) (j : ℕ)
    {X : Type*} [MeasurableSpace X] (σ m : X→ℝ) (hσ : Measurable σ) (hm : Measurable m) :
    Measurable (fun x=>deriv (heat (σ x).toNNReal (ScalarHeatBands.band a j)) (m x)) := by
  have hb:=ScalarHeatBands.band_boundedSmooth ha j
  have hg:=GaussianProfile.gaussianAverage_joint_measurable (deriv_boundedSmooth hb).smooth.continuous.measurable
  have he (x : X) : deriv (heat (σ x).toNNReal (ScalarHeatBands.band a j)) (m x)=
      GaussianProfile.gaussianAverage (deriv (ScalarHeatBands.band a j)) (m x) (σ x):=by
    rw [deriv_heat _ hb]
    rfl
  simp_rw [he]
  exact hg.comp (hm.prodMk hσ)

end SHE.PolynomialGaussianDecay
