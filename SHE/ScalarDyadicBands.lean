module

public import SHE.ScaledMollifierEstimates
public import SHE.SmoothCylinderAlgebra

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SHE.ScalarDyadicBands
open Set Filter Real MeasureTheory
open scoped ContDiff Topology

def smooth (a : ℝ→ℝ) (j : ℕ) : ℝ→ℝ :=
  ScaledMollifierEstimates.mollify (CompactMollifier.radius j) a

def band (a : ℝ→ℝ) : ℕ→ℝ→ℝ
  | 0 => smooth a 0
  | j+1 => fun x=>smooth a (j+1) x-smooth a j x

theorem smooth_boundedSmooth {a : ℝ→ℝ} (ha : Continuous a) {B : ℝ}
    (hB : ∀ x,|a x|≤B) (j : ℕ) : SmoothCylinders.BoundedSmooth (smooth a j) :=
  ScaledMollifierEstimates.mollify_boundedSmooth ha hB (CompactMollifier.radius_pos j)

theorem band_boundedSmooth {a : ℝ→ℝ} (ha : Continuous a) {B : ℝ}
    (hB : ∀ x,|a x|≤B) (j : ℕ) : SmoothCylinders.BoundedSmooth (band a j) := by
  cases j with
  | zero => exact smooth_boundedSmooth ha hB 0
  | succ j => exact (smooth_boundedSmooth ha hB (j+1)).sub (smooth_boundedSmooth ha hB j)

/-- Every finite root cutoff is the literal smoothing, without an
assumed frequency decomposition. -/
theorem sum_band (a : ℝ→ℝ) (J : ℕ) (x : ℝ) :
    (∑ j∈Finset.range (J+1),band a j x)=smooth a J x := by
  induction J with
  | zero => simp [band]
  | succ J h => rw [Finset.sum_range_succ,h]; simp only [band]; ring

theorem smooth_error {a : ℝ→ℝ} (ha : Continuous a) {B H β : ℝ}
    (hB : ∀ x,|a x|≤B) (hH : 0≤H) (hβ : 0≤β)
    (hh : ∀ x y,|a x-a y|≤H*|x-y|^β) (j : ℕ) (x : ℝ) :
    |smooth a j x-a x|≤H*CompactMollifier.radius j^β :=
  ScaledMollifierEstimates.mollify_error ha hB hH hβ (CompactMollifier.radius_pos j) hh x

theorem smooth_tendstoUniformly {a : ℝ→ℝ} (ha : Continuous a) {B H β : ℝ}
    (hB : ∀ x,|a x|≤B) (hH : 0≤H) (hβ : 0<β)
    (hh : ∀ x y,|a x-a y|≤H*|x-y|^β) :
    TendstoUniformly (smooth a) a atTop := by
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  have ht : Tendsto (fun j=>H*CompactMollifier.radius j^β) atTop (𝓝 (0:ℝ)) := by
    simpa only [Real.zero_rpow hβ.ne',mul_zero] using
      (CompactMollifier.radius_tendsto.rpow_const (Or.inr hβ.le)).const_mul H
  filter_upwards [ht.eventually (gt_mem_nhds hε)] with j hj x
  have hb : dist (a x) (smooth a j x)≤H*CompactMollifier.radius j^β := by
    simpa only [Real.dist_eq,abs_sub_comm] using smooth_error ha hB hH hβ.le hh j x
  exact hb.trans_lt hj

theorem radius_succ (j : ℕ) :
    CompactMollifier.radius j=2*CompactMollifier.radius (j+1) := by
  simp only [CompactMollifier.radius,pow_succ]
  ring

theorem radius_antitone (j : ℕ) :
    CompactMollifier.radius (j+1)≤CompactMollifier.radius j := by
  rw [radius_succ j]
  nlinarith [CompactMollifier.radius_pos (j+1)]

theorem radius_frequency (j : ℕ) (β : ℝ) (n : ℕ) :
    CompactMollifier.radius j^(β-(n:ℝ))=
      ((2:ℝ)^j)^(-β)*((2:ℝ)^j)^n := by
  have hp : 0<(2:ℝ)^j:=by positivity
  rw [CompactMollifier.radius,inv_pow,Real.inv_rpow (by positivity),←Real.rpow_neg hp.le,
    ←Real.rpow_natCast ((2:ℝ)^j) n,←Real.rpow_add hp]
  congr 1
  ring

/-- Zeroth-order bands retain the Holder scale; no derivative of the
rough coefficient is required. -/
theorem band_succ_bound {a : ℝ→ℝ} (ha : Continuous a) {B H β : ℝ}
    (hB : ∀ x,|a x|≤B) (hH : 0≤H) (hβ : 0≤β) (hβ1 : β≤1)
    (hh : ∀ x y,|a x-a y|≤H*|x-y|^β) (j : ℕ) (x : ℝ) :
    |band a (j+1) x|≤3*H*CompactMollifier.radius (j+1)^β := by
  have hp : (2:ℝ)^β≤2 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2) hβ1
  have hr : CompactMollifier.radius j^β≤2*CompactMollifier.radius (j+1)^β := by
    rw [radius_succ j,Real.mul_rpow (by norm_num) (CompactMollifier.radius_pos (j+1)).le]
    exact mul_le_mul_of_nonneg_right hp (rpow_nonneg (CompactMollifier.radius_pos (j+1)).le _)
  change |smooth a (j+1) x-smooth a j x|≤_
  calc
    _≤|smooth a (j+1) x-a x|+|smooth a j x-a x| := by
      simpa only [abs_sub_comm] using abs_sub_le (smooth a (j+1) x) (a x) (smooth a j x)
    _≤H*CompactMollifier.radius (j+1)^β+H*CompactMollifier.radius j^β :=
      add_le_add (smooth_error ha hB hH hβ hh (j+1) x) (smooth_error ha hB hH hβ hh j x)
    _≤3*H*CompactMollifier.radius (j+1)^β := by
      nlinarith [mul_le_mul_of_nonneg_left hr hH]

end SHE.ScalarDyadicBands
