module

public import SHE.GaussianPeriodizedLocal
public import SHE.NodeKernelLocal

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.HeatKernelAgeComparison
open Set MeasureTheory AddCircle HeatMarkov GaussianPeriodizedLocal FourierHeatLine LineGaussianLocal
local instance heatKernelAgeComparison_periodPos : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩

theorem mass_scale {C t : ℝ} (hC : 0 ≤ C) (ht : 0 < t) :
    heatMass (C*t) = Real.sqrt C*heatMass t := by
  unfold heatMass
  rw [show 4*Real.pi*(C*t)=C*(4*Real.pi*t) by ring,Real.sqrt_mul hC]

theorem mass_mono {s t : ℝ} (hst : s ≤ t) : heatMass s ≤ heatMass t := by
  unfold heatMass
  exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hst (by positivity : 0 ≤ 4*Real.pi))

/-- Pointwise comparison of the literal positive periodic kernels at
two ages, obtained termwise from their normalized Gaussian series. -/
theorem age_le {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (hst : s ≤ t) (x : AddCircle (1:ℝ)) :
    ‖kernel s hs x‖ ≤ (heatMass t/heatMass s)*‖kernel t ht x‖ := by
  induction x using Quotient.inductionOn with
  | _ r =>
    have hterm (n : ℤ) : gaussian s (r+(n:ℝ)) ≤ gaussian t (r+(n:ℝ)) := by
      unfold gaussian
      apply Real.exp_le_exp.mpr
      have hh := div_le_div_of_nonneg_left (sq_nonneg (r+(n:ℝ))) (by positivity : 0 < 4*s)
        (mul_le_mul_of_nonneg_left hst (by norm_num : (0:ℝ) ≤ 4))
      simpa only [neg_div] using neg_le_neg hh
    have hh := (gaussian_summable hs r).tsum_le_tsum hterm (gaussian_summable ht r)
    rw [kernel_coe_norm hs r,kernel_coe_norm ht r]
    apply (mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr (heatMass_pos hs).le)).trans_eq
    field_simp [(heatMass_pos hs).ne',(heatMass_pos ht).ne']

theorem scale_le {C R t : ℝ} (hC : 0 < C) (hR : 0 < R) (ht : 0 < t) (hCR : C ≤ R)
    (x : AddCircle (1:ℝ)) :
    ‖kernel (C*t) (by positivity) x‖ ≤ (Real.sqrt R/Real.sqrt C)*‖kernel (R*t) (by positivity) x‖ := by
  have hh := age_le (by positivity : 0 < C*t) (by positivity : 0 < R*t)
    (mul_le_mul_of_nonneg_right hCR ht.le) x
  rw [mass_scale hR.le ht,mass_scale hC.le ht] at hh
  have he : Real.sqrt R*heatMass t/(Real.sqrt C*heatMass t) = Real.sqrt R/Real.sqrt C := by
    field_simp [(heatMass_pos ht).ne',(Real.sqrt_pos.mpr hC).ne']
  rwa [he] at hh

theorem exists_fixed_ratio {R : ℝ} (hR : 0 < R) :
    ∃ L : ℝ,0 < L ∧ ∀ x : AddCircle (1:ℝ),‖kernel R hR x‖ ≤ L*‖kernel 1 zero_lt_one x‖ := by
  let u : C(AddCircle (1:ℝ),ℝ) := ⟨fun x => ‖kernel R hR x‖/‖kernel 1 zero_lt_one x‖,
    (kernel R hR).continuous.norm.div (kernel 1 zero_lt_one).continuous.norm
      (fun x => (NodeKernelLocal.kernel_norm_pos zero_lt_one x).ne')⟩
  refine ⟨1+‖u‖,by positivity,?_⟩
  intro x
  have hh := u.norm_coe_le_norm x
  change ‖‖kernel R hR x‖/‖kernel 1 zero_lt_one x‖‖ ≤ ‖u‖ at hh
  rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)] at hh
  have hh' : ‖kernel R hR x‖/‖kernel 1 zero_lt_one x‖ ≤ 1+‖u‖ := by linarith
  exact (div_le_iff₀ (NodeKernelLocal.kernel_norm_pos zero_lt_one x)).mp hh'

def envelopeScale (C : ℝ) : ℝ := max 1 C
def clippedAge (C w : ℝ) : ℝ := min (envelopeScale C*w) 1

theorem envelopeScale_pos (C : ℝ) : 0 < envelopeScale C := zero_lt_one.trans_le (le_max_left _ _)
theorem clippedAge_pos {C w : ℝ} (hw : 0 < w) : 0 < clippedAge C w := by
  unfold clippedAge
  exact lt_min (mul_pos (envelopeScale_pos C) hw) zero_lt_one

theorem clippedAge_bounds {C w : ℝ} (hw : 0 < w) (hw1 : w ≤ 1) :
    w ≤ clippedAge C w ∧ clippedAge C w ≤ 1 ∧ clippedAge C w ≤ envelopeScale C*w := by
  refine ⟨le_min ?_ hw1,min_le_right _ _,min_le_left _ _⟩
  have hh := mul_le_mul_of_nonneg_right (le_max_left 1 C) hw.le
  simpa only [one_mul,envelopeScale] using! hh

/-- Every fixed positive Gaussian age multiplier reduces, uniformly in
the outer scale, to a genuine heat kernel whose age lies between w and
one. This includes the positive-age tail Cw≥1 and C<1. -/
theorem exists_clipped_envelope {C : ℝ} (hC : 0 < C) :
    ∃ L : ℝ,0 < L ∧ ∀ (w : ℝ) (hw : 0 < w),w ≤ 1 → ∀ x : AddCircle (1:ℝ),
      ‖kernel (C*w) (by positivity) x‖ ≤ L*‖kernel (clippedAge C w) (clippedAge_pos hw) x‖ := by
  let R := envelopeScale C
  have hR : 0 < R := envelopeScale_pos C
  have hR1 : 1 ≤ R := le_max_left _ _
  obtain ⟨J,hJ,hfixed⟩ := exists_fixed_ratio hR
  let M := heatMass R/heatMass 1*J
  have hM : 0 < M := by dsimp [M]; positivity [heatMass_pos hR,heatMass_pos zero_lt_one]
  let L := (Real.sqrt R/Real.sqrt C)*(1+M)
  refine ⟨L,by dsimp [L]; positivity,?_⟩
  intro w hw hw1 x
  have hh := scale_le hC hR hw (le_max_right _ _) x
  have hS : 0 ≤ Real.sqrt R/Real.sqrt C := by positivity
  by_cases hc : R*w ≤ 1
  · have he : clippedAge C w = R*w := min_eq_left hc
    simp only [he]
    have hm := mul_le_mul_of_nonneg_left (by linarith : (1:ℝ) ≤ 1+M)
      (mul_nonneg hS (norm_nonneg (kernel (R*w) (by positivity) x)))
    exact hh.trans (by dsimp only [L]; nlinarith only [hm])
  · have hc' : 1 ≤ R*w := le_of_not_ge hc
    have he : clippedAge C w = 1 := min_eq_right hc'
    simp only [he]
    have hage := age_le (by positivity : 0 < R*w) hR (by nlinarith) x
    have hmass : heatMass 1 ≤ heatMass (R*w) := mass_mono hc'
    have hratio : heatMass R/heatMass (R*w) ≤ heatMass R/heatMass 1 :=
      div_le_div_of_nonneg_left (heatMass_pos hR).le (heatMass_pos zero_lt_one) hmass
    have hkernel : ‖kernel (R*w) (by positivity) x‖ ≤ M*‖kernel 1 zero_lt_one x‖ := by
      have hm := mul_le_mul hratio (hfixed x) (norm_nonneg _)
        (div_nonneg (heatMass_pos hR).le (heatMass_pos zero_lt_one).le)
      exact hage.trans (hm.trans_eq (by dsimp only [M]; ring))
    have hm := mul_le_mul_of_nonneg_left hkernel hS
    have hm' := mul_le_mul_of_nonneg_left (by linarith : M ≤ 1+M)
      (mul_nonneg hS (norm_nonneg (kernel 1 zero_lt_one x)))
    exact hh.trans (hm.trans (by dsimp only [L]; nlinarith only [hm']))

end SHE.HeatKernelAgeComparison
