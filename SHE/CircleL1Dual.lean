module

public import SHE.CoarseCellSobolev

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section

namespace SHE.CircleL1Dual
open Finset Set MeasureTheory AddCircle CircleHeat HeatMarkov FiniteHaar ArcFourier FractionalHardy
open scoped ENNReal InnerProductSpace
local instance circleL1Dual_periodPos : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩

def signValue (z : ℂ) : ℂ := ((‖z‖ : ℂ)⁻¹) • z

theorem signValue_norm_le (z : ℂ) : ‖signValue z‖ ≤ 1 := by
  unfold signValue
  by_cases hz : z = 0
  · simp only [hz,norm_zero,Complex.ofReal_zero,inv_zero,zero_smul,norm_zero,zero_le_one]
  · rw [norm_smul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)]
    rw [inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz)]

theorem signValue_pair (z : ℂ) : inner ℂ (signValue z) z = (‖z‖ : ℂ) := by
  unfold signValue
  rw [inner_smul_left,inner_self_eq_norm_sq_to_K,← Complex.ofReal_inv,Complex.conj_ofReal]
  by_cases hz : z = 0
  · simp [hz]
  · have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr hn]
    rfl

theorem sign_memLp (f : CircleL2) : MemLp (fun x => signValue (f x)) 2 haarAddCircle := by
  apply MemLp.of_bound _ 1 (ae_of_all _ (fun x => signValue_norm_le (f x)))
  unfold signValue
  exact ((Complex.continuous_ofReal.comp_aestronglyMeasurable (Lp.aestronglyMeasurable f).norm).inv₀).smul (Lp.aestronglyMeasurable f)

def sign (f : CircleL2) : CircleL2 := (sign_memLp f).toLp _

theorem sign_ae (f : CircleL2) : sign f =ᵐ[haarAddCircle] fun x => signValue (f x) := (sign_memLp f).coeFn_toLp

theorem sign_bound (f : CircleL2) : ∀ᵐ x ∂haarAddCircle, ‖sign f x‖ ≤ 1 := by
  filter_upwards [sign_ae f] with x hx
  rw [hx]
  exact signValue_norm_le _

theorem sign_pair (f : CircleL2) : inner ℂ (sign f) f = (normOne f : ℂ) := by
  rw [L2.inner_def]
  unfold normOne
  calc
    _ = ∫ x, (‖f x‖ : ℂ) ∂haarAddCircle := by
      apply integral_congr_ae
      filter_upwards [sign_ae f] with x hx
      rw [hx,signValue_pair]
    _ = _ := integral_ofReal

theorem heat_inner (t : ℝ) (f g : CircleL2) : inner ℂ (heat t f) g = inner ℂ f (heat t g) := by
  rw [← fourierBasis.repr.inner_map_map,← fourierBasis.repr.inner_map_map (x := f),lp.inner_eq_tsum,lp.inner_eq_tsum]
  apply tsum_congr
  intro n
  simp only [fourierBasis_repr,heat_fourierCoeff,RCLike.inner_apply',map_mul,heatWeight,Complex.conj_ofReal]
  ring

theorem massive_add_bound {Λ ρ : ℝ} (hΛ : 0 ≤ Λ) (f g : CircleL2)
    (hf : Summable (fun k : ℤ => weight Λ ρ k*‖fourierCoeff f k‖^2))
    (hg : Summable (fun k : ℤ => weight Λ ρ k*‖fourierCoeff g k‖^2)) :
    Summable (fun k : ℤ => weight Λ ρ k*‖fourierCoeff (f+g) k‖^2) ∧
      positiveSq Λ ρ ((f+g : CircleL2)) ≤ 2*(positiveSq Λ ρ f+positiveSq Λ ρ g) := by
  have hcoef (n : ℤ) : fourierCoeff (f+g) n = fourierCoeff f n+fourierCoeff g n := by
    simp only [← fourierBasis_repr,map_add,lp.coeFn_add,Pi.add_apply]
  have hpoint (n : ℤ) : weight Λ ρ n*‖fourierCoeff (f+g) n‖^2 ≤
      2*(weight Λ ρ n*‖fourierCoeff f n‖^2+weight Λ ρ n*‖fourierCoeff g n‖^2) := by
    rw [hcoef]
    have hh := norm_square_young 1 zero_lt_one (fourierCoeff f n+fourierCoeff g n) (fourierCoeff f n)
    norm_num only [inv_one,one_add_one_eq_two,add_sub_cancel_left] at hh
    exact (mul_le_mul_of_nonneg_left hh (by unfold weight; positivity)).trans_eq (by ring)
  have hs := (hf.add hg).mul_left 2
  have ho := Summable.of_nonneg_of_le (fun n => by unfold weight; positivity) hpoint hs
  refine ⟨ho,?_⟩
  have hh := ho.tsum_le_tsum hpoint hs
  simpa only [tsum_mul_left,Summable.tsum_add hf hg,positiveSq] using hh

end SHE.CircleL1Dual
