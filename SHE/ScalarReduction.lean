module

public import SHE.CompanionPicard
public import Mathlib.Topology.MetricSpace.Holder

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

namespace SHE.ScalarReduction
open MeasureTheory
open scoped ENNReal NNReal

def workingExponent (β : ℝ) : ℝ := min β (1/8)
def additiveAmplitude (c : ℝ) : ℝ := c/2
def residual (g : ℝ → ℝ) (c : ℝ) (x : ℝ) : ℝ := (g x)^2-(additiveAmplitude c)^2

theorem workingExponent_admissible {β : ℝ} (hβ : 0 < β) :
    0 < workingExponent β ∧ workingExponent β ≤ β ∧ workingExponent β ≤ 4/25 := by
  unfold workingExponent
  exact ⟨lt_min hβ (by norm_num),min_le_left _ _,(min_le_right _ _).trans (by norm_num)⟩

theorem holder_exponent_reduction {g : ℝ → ℝ} {β₀ β L C : ℝ} (hβ : 0 < β)
    (hββ : β ≤ β₀) (hL : 0 ≤ L) (hC : 0 ≤ C) (hbound : ∀ x,|g x| ≤ C)
    (hholder : ∀ x y,|g x-g y| ≤ L*|x-y|^β₀) :
    ∀ x y,|g x-g y| ≤ (L+2*C)*|x-y|^β := by
  intro x y
  by_cases hsmall : |x-y| ≤ 1
  · have hp : |x-y|^β₀ ≤ |x-y|^β := by
      by_cases he : x=y
      · subst y
        simp only [sub_self,abs_zero,Real.zero_rpow (ne_of_gt hβ),
          Real.zero_rpow (ne_of_gt (hβ.trans_le hββ))]
        exact le_rfl
      · exact Real.rpow_le_rpow_of_exponent_ge (abs_pos.mpr (sub_ne_zero.mpr he)) hsmall hββ
    exact (hholder x y).trans ((mul_le_mul_of_nonneg_left hp hL).trans
      (mul_le_mul_of_nonneg_right (by linarith : L ≤ L+2*C) (Real.rpow_nonneg (abs_nonneg _) _)))
  · have hd : 1 ≤ |x-y|^β := Real.one_le_rpow (le_of_not_ge hsmall) hβ.le
    have hb : |g x-g y| ≤ 2*C := (abs_sub (g x) (g y)).trans (by linarith [hbound x,hbound y])
    have hm := mul_le_mul_of_nonneg_left hd (show 0 ≤ L+2*C by positivity)
    nlinarith

theorem holder_continuous {g : ℝ → ℝ} {β H : ℝ} (hβ : 0 < β) (hH : 0 ≤ H)
    (hholder : ∀ x y,|g x-g y| ≤ H*|x-y|^β) : Continuous g := by
  let C : ℝ≥0 := ⟨H,hH⟩
  let r : ℝ≥0 := ⟨β,hβ.le⟩
  have hh : HolderWith C r g := by
    intro x y
    rw [edist_dist,edist_dist,← ENNReal.ofReal_coe_nnreal]
    change ENNReal.ofReal (dist (g x) (g y)) ≤ ENNReal.ofReal H*(ENNReal.ofReal (dist x y))^β
    rw [ENNReal.ofReal_rpow_of_nonneg (dist_nonneg : 0 ≤ dist x y) hβ.le,
      ← ENNReal.ofReal_mul hH]
    apply ENNReal.ofReal_le_ofReal
    simpa only [Real.dist_eq] using hholder x y
  exact hh.continuous hβ

theorem residual_elliptic {g : ℝ → ℝ} {c C : ℝ} (hc : 0 < c)
    (hbound : ∀ x,c ≤ |g x| ∧ |g x| ≤ C) :
    ∀ x,c^2/2 ≤ residual g c x ∧ residual g c x ≤ C^2 := by
  intro x
  have hlow := pow_le_pow_left₀ hc.le (hbound x).1 2
  have hhigh := pow_le_pow_left₀ (abs_nonneg (g x)) (hbound x).2 2
  simp only [sq_abs] at hlow hhigh
  unfold residual additiveAmplitude
  constructor <;> nlinarith [sq_nonneg c]

theorem residual_identity (g : ℝ → ℝ) (c x : ℝ) :
    (additiveAmplitude c)^2+residual g c x=(g x)^2 := by unfold residual; ring

theorem residual_holder {g : ℝ → ℝ} {c C H β : ℝ} (_hC : 0 ≤ C) (hH : 0 ≤ H)
    (hbound : ∀ x,|g x| ≤ C) (hholder : ∀ x y,|g x-g y| ≤ H*|x-y|^β) :
    ∀ x y,|residual g c x-residual g c y| ≤ (2*C*H)*|x-y|^β := by
  intro x y
  have he : residual g c x-residual g c y=(g x-g y)*(g x+g y) := by unfold residual; ring
  have hs : |g x+g y| ≤ 2*C := (abs_add_le _ _).trans (by linarith [hbound x,hbound y])
  rw [he,abs_mul]
  calc
    _ ≤ (H*|x-y|^β)*(2*C) := mul_le_mul (hholder x y) hs (abs_nonneg _) (by positivity)
    _ = _ := by ring

end SHE.ScalarReduction
