module

public import SHE.ScalarGaussianSemigroup
public import SHE.ScalarDyadicBands

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
namespace SHE.ScalarHeatBands
open Set MeasureTheory ProbabilityTheory Filter Topology Real GaussianAudit SmoothCylinders ScalarGaussianSemigroup
open scoped NNReal ENNReal

def variance (j : ℕ) : ℝ≥0:=⟨CompactMollifier.radius j^2,sq_nonneg _⟩
def smooth (a : ℝ→ℝ) (j : ℕ) : ℝ→ℝ:=heat (variance j) a
def band (a : ℝ→ℝ) : ℕ→ℝ→ℝ
  | 0=>smooth a 0
  | j+1=>fun x=>smooth a (j+1) x-smooth a j x

theorem variance_pos (j : ℕ) : 0<variance j:=by
  change 0<CompactMollifier.radius j^2
  exact sq_pos_of_pos (CompactMollifier.radius_pos j)

theorem variance_power (j : ℕ) (p : ℝ) :
    (variance j:ℝ)^(p/2)=CompactMollifier.radius j^p := by
  change (CompactMollifier.radius j^2)^(p/2)=_
  rw [←Real.rpow_natCast_mul (CompactMollifier.radius_pos j).le]
  congr 1
  ring

theorem smooth_boundedSmooth {a : ℝ→ℝ} (ha : BoundedSmooth a) (j : ℕ) : BoundedSmooth (smooth a j):=
  heat_boundedSmooth (variance j) ha

theorem band_boundedSmooth {a : ℝ→ℝ} (ha : BoundedSmooth a) (j : ℕ) : BoundedSmooth (band a j):=by
  cases j with
  | zero => exact smooth_boundedSmooth ha 0
  | succ j => exact (smooth_boundedSmooth ha (j+1)).sub (smooth_boundedSmooth ha j)

/-- The genuine Gaussian-heat bands telescope exactly at every finite
cutoff; no assumed Littlewood-Paley decomposition occurs here. -/
theorem sum_band (a : ℝ→ℝ) (J : ℕ) (x : ℝ) :
    (∑ j∈Finset.range (J+1),band a j x)=smooth a J x:=by
  induction J with
  | zero => simp [band]
  | succ J ih => rw [Finset.sum_range_succ,ih]; simp only [band]; ring

theorem smooth_error {a : ℝ→ℝ} (ha : Measurable a) {B H β : ℝ}
    (hB : ∀ x,|a x|≤B) (hβ : 0≤β)
    (hh : ∀ x y,|a x-a y|≤H*|x-y|^β) (j : ℕ) (x : ℝ) :
    |smooth a j x-a x|≤H*gaussianAbsMoment β*CompactMollifier.radius j^β:=by
  simpa only [smooth,variance_power] using heat_error (variance j) ha hB hβ hh x

theorem smooth_tendstoUniformly {a : ℝ→ℝ} (ha : Measurable a) {B H β : ℝ}
    (hB : ∀ x,|a x|≤B) (hβ : 0<β)
    (hh : ∀ x y,|a x-a y|≤H*|x-y|^β) : TendstoUniformly (smooth a) a atTop:=by
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  have ht : Tendsto (fun j=>H*gaussianAbsMoment β*CompactMollifier.radius j^β) atTop (𝓝 (0:ℝ)):=by
    simpa only [zero_rpow hβ.ne',mul_zero] using
      (CompactMollifier.radius_tendsto.rpow_const (Or.inr hβ.le)).const_mul (H*gaussianAbsMoment β)
  filter_upwards [ht.eventually (gt_mem_nhds hε)] with j hj x
  exact (show dist (a x) (smooth a j x)≤H*gaussianAbsMoment β*CompactMollifier.radius j^β by
    simpa only [Real.dist_eq,abs_sub_comm] using smooth_error ha hB hβ.le hh j x).trans_lt hj

/-- Every positive band retains the original Holder amplitude at the
same physical dyadic scale. The constant is a true Gaussian moment. -/
theorem band_succ_bound {a : ℝ→ℝ} (ha : Measurable a) {B H β : ℝ}
    (hB : ∀ x,|a x|≤B) (hH : 0≤H) (hβ : 0≤β) (hβ1 : β≤1)
    (hh : ∀ x y,|a x-a y|≤H*|x-y|^β) (j : ℕ) (x : ℝ) :
    |band a (j+1) x|≤3*(H*gaussianAbsMoment β)*CompactMollifier.radius (j+1)^β:=by
  have hp : (2:ℝ)^β≤2:=by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2) hβ1
  have hr : CompactMollifier.radius j^β≤2*CompactMollifier.radius (j+1)^β:=by
    rw [ScalarDyadicBands.radius_succ j,Real.mul_rpow (by norm_num) (CompactMollifier.radius_pos (j+1)).le]
    exact mul_le_mul_of_nonneg_right hp (rpow_nonneg (CompactMollifier.radius_pos (j+1)).le _)
  change |smooth a (j+1) x-smooth a j x|≤_
  calc
    _≤|smooth a (j+1) x-a x|+|smooth a j x-a x|:=by
      simpa only [abs_sub_comm] using abs_sub_le (smooth a (j+1) x) (a x) (smooth a j x)
    _≤H*gaussianAbsMoment β*CompactMollifier.radius (j+1)^β+
        H*gaussianAbsMoment β*CompactMollifier.radius j^β:=
      add_le_add (smooth_error ha hB hβ hh (j+1) x) (smooth_error ha hB hβ hh j x)
    _≤_:=by nlinarith [mul_le_mul_of_nonneg_left hr (mul_nonneg hH (gaussianAbsMoment_nonneg β))]

end SHE.ScalarHeatBands
