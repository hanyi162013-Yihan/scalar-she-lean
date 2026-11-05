module

public import SHE.HeatMarkov
public import Mathlib.Analysis.Calculus.MeanValue

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.LineGaussianLocal
open Set

def gaussian (t x : ℝ) : ℝ := Real.exp (-(x^2)/(4*t))

theorem score_bound (z : ℝ) : |z| * Real.exp (-(z^2)/8) ≤ 2 := by
  have hq : |z| ≤ 2+z^2/8 := by nlinarith [sq_nonneg (|z|-4),sq_abs z]
  have he : 2+z^2/8 ≤ 2*Real.exp (z^2/8) := by
    nlinarith [Real.add_one_le_exp (z^2/8),sq_nonneg z]
  have hm := mul_le_mul_of_nonneg_right (hq.trans he) (Real.exp_pos (-(z^2)/8)).le
  calc
    _ ≤ (2*Real.exp (z^2/8))*Real.exp (-(z^2)/8) := hm
    _ = 2 := by rw [mul_assoc,← Real.exp_add]; norm_num <;> ring

theorem hasDerivAt_gaussian {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasDerivAt (gaussian t) ((-x/(2*t))*gaussian t x) x := by
  have hp := (((hasDerivAt_id x).pow 2).neg.div_const (4*t))
  simp only [Pi.pow_apply,Pi.neg_apply,id_eq,pow_one,mul_one,Nat.cast_ofNat,Nat.reduceSub] at hp
  change HasDerivAt (fun y : ℝ => -(y^2)/(4*t)) (-(2*x)/(4*t)) x at hp
  convert hp.exp using 1
  · rfl
  · dsimp only [gaussian]
    field_simp
    ring

/-- The Gaussian derivative is bounded by a wider Gaussian with the
correct inverse square-root time factor. -/
theorem derivative_bound {t : ℝ} (ht : 0 < t) (x : ℝ) :
    ‖deriv (gaussian t) x‖ ≤ (1/Real.sqrt t)*Real.exp (-(x^2)/(8*t)) := by
  have hspos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hsq := Real.sq_sqrt ht.le
  have hz : (x/Real.sqrt t)^2=x^2/t := by rw [div_pow,hsq]
  have hs := score_bound (x/Real.sqrt t)
  rw [abs_div,abs_of_pos hspos,hz] at hs
  have hexp : Real.exp (-(x^2)/(4*t))=
      Real.exp (-(x^2)/(8*t))*Real.exp (-(x^2)/(8*t)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hc : |x|/(2*t)=(1/(2*Real.sqrt t))*(|x|/Real.sqrt t) := by
    conv_lhs => rw [← hsq]
    field_simp <;> ring
  have hi : ‖deriv (gaussian t) x‖=
      (1/(2*Real.sqrt t))*(|x|/Real.sqrt t*Real.exp (-(x^2)/(8*t)))*
        Real.exp (-(x^2)/(8*t)) := by
    rw [(hasDerivAt_gaussian ht x).deriv,Real.norm_eq_abs,abs_mul,abs_div,abs_neg,
      abs_of_pos (by positivity : 0 < 2*t),gaussian,abs_of_pos (Real.exp_pos _),hexp,hc]
    ring
  rw [hi]
  have hs' : |x|/Real.sqrt t*Real.exp (-(x^2)/(8*t)) ≤ 2 := by
    convert hs using 1 <;> congr 2 <;> ring
  calc
    _ ≤ (1/(2*Real.sqrt t))*2*Real.exp (-(x^2)/(8*t)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs' (by positivity)) (Real.exp_pos _).le
    _ = _ := by ring

/-- The derivative envelope remains localized at a fixed nearby center. -/
theorem local_derivative_bound {t a x : ℝ} (ht : 0 < t)
    (hnear : |x-a| ≤ Real.sqrt t) :
    ‖deriv (gaussian t) x‖ ≤
      (Real.exp (1/4:ℝ)/Real.sqrt t)*Real.exp (-(a^2)/(32*t)) := by
  have hs : (x-a)^2 ≤ t := by
    have h := (sq_le_sq₀ (abs_nonneg (x-a)) (Real.sqrt_nonneg t)).mpr hnear
    simpa only [sq_abs,Real.sq_sqrt ht.le] using h
  have ha : a^2 ≤ 2*x^2+2*t := by nlinarith [sq_nonneg (2*x-a)]
  have he : -(x^2)/(8*t) ≤ (1/4:ℝ)-a^2/(32*t) := by
    apply (mul_le_mul_iff_right₀ (show 0 < 32*t by positivity)).mp
    have hl : (-(x^2)/(8*t))*(32*t)= -4*x^2 := by field_simp; ring
    have hr : ((1/4:ℝ)-a^2/(32*t))*(32*t)=8*t-a^2 := by field_simp; ring
    nlinarith [sq_nonneg x]
  have h := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (show 0 ≤ 1/Real.sqrt t by positivity)
  calc
    _ ≤ (1/Real.sqrt t)*Real.exp ((1/4:ℝ)-a^2/(32*t)) := (derivative_bound ht x).trans h
    _ = _ := by simp only [sub_eq_add_neg,Real.exp_add,neg_div]; ring

/-- A local Lipschitz estimate with an enlarged Gaussian spatial
envelope, rather than a spatially constant derivative bound. -/
theorem difference_bound {t a x y : ℝ} (ht : 0 < t)
    (hx : |x-a| ≤ Real.sqrt t) (hy : |y-a| ≤ Real.sqrt t) :
    |gaussian t x-gaussian t y| ≤
      ((Real.exp (1/4:ℝ)/Real.sqrt t)*Real.exp (-(a^2)/(32*t)))*|x-y| := by
  have hmem {z : ℝ} (hz : |z-a| ≤ Real.sqrt t) : z ∈ Icc (a-Real.sqrt t) (a+Real.sqrt t) := by
    have hh := abs_le.mp hz
    constructor <;> linarith
  have hnear {z : ℝ} (hz : z ∈ Icc (a-Real.sqrt t) (a+Real.sqrt t)) : |z-a| ≤ Real.sqrt t := by
    apply abs_le.mpr
    constructor <;> linarith [hz.1,hz.2]
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    (f := gaussian t) (s := Icc (a-Real.sqrt t) (a+Real.sqrt t))
    (fun z _ => (hasDerivAt_gaussian ht z).differentiableAt)
    (fun z hz => local_derivative_bound ht (hnear hz)) (convex_Icc _ _)
    (hmem hy) (hmem hx)
  simpa only [Real.norm_eq_abs] using h

end SHE.LineGaussianLocal
