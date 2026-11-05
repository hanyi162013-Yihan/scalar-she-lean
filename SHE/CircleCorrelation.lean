module

public import SHE.GlobalTorusHeatSpan

/-! Actual Haar translation correlation and its complete Fourier Parseval
identity for arbitrary signed complex L² inputs. -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SHE.CircleCorrelation
open MeasureTheory AddCircle SHE.HeatTorus SHE.HeatTorusKernel
open scoped InnerProductSpace ENNReal

def coefficient (e d : CircleL2) (n : ℤ) : ℂ := star (fourierCoeff e n) * fourierCoeff d n

theorem coefficient_norm_summable (e d : CircleL2) : Summable (fun n => ‖coefficient e d n‖) := by
  have h := lp.summable_mul (p := 2) (q := 2) (by rw [Real.holderConjugate_iff]; norm_num)
    ((fourierBasis (T := 1)).repr e) ((fourierBasis (T := 1)).repr d)
  simpa only [coefficient, norm_mul, norm_star, fourierBasis_repr] using h

theorem fourierCoeff_norm_le (e : CircleL2) (n : ℤ) : ‖fourierCoeff e n‖ ≤ ‖e‖ := by
  have h := lp.norm_apply_le_norm (show (2 : ℝ≥0∞) ≠ 0 by norm_num)
    ((fourierBasis (T := 1)).repr e) n
  simpa only [fourierBasis_repr, LinearIsometryEquiv.norm_map] using h

theorem coefficient_memℓp (e d : CircleL2) : Memℓp (coefficient e d) 2 := by
  have hm : Memℓp (fun n : ℤ => ‖e‖ * ‖fourierCoeff d n‖) 2 := by
    simpa only [fourierBasis_repr] using
      ((lp.memℓp ((fourierBasis (T := 1)).repr d)).norm.const_mul ‖e‖)
  apply hm.mono
  intro n
  rw [coefficient, norm_mul, norm_star]
  exact mul_le_mul_of_nonneg_right (fourierCoeff_norm_le e n) (norm_nonneg _)

def correlation (e d : CircleL2) : CircleL2 :=
  (fourierBasis (T := 1)).repr.symm ⟨coefficient e d, coefficient_memℓp e d⟩

theorem correlation_fourierCoeff (e d : CircleL2) (n : ℤ) :
    fourierCoeff (correlation e d) n = coefficient e d n := by
  rw [← fourierBasis_repr, correlation, LinearIsometryEquiv.apply_symm_apply]

theorem translated_inner_hasSum (e d : CircleL2) (x : UnitAddCircle) :
    HasSum (fun n : ℤ => coefficient e d n * fourier n x) (inner ℂ (translate x e) d) := by
  have hs := (fourierBasis (T := 1)).hasSum_inner_mul_inner (translate x e) d
  convert! hs using 1
  funext n
  rw [← inner_conj_symm (translate x e) (fourierBasis n),
    ← HilbertBasis.repr_apply_apply, ← HilbertBasis.repr_apply_apply,
    fourierBasis_repr, fourierBasis_repr, fourierCoeff_translate]
  simp only [coefficient, map_mul, fourier_neg, starRingEnd_self_apply]
  change star (fourierCoeff e n) * fourierCoeff d n * fourier n x =
    fourier n x * star (fourierCoeff e n) * fourierCoeff d n
  ring

/-- The actual translated pairing is the L² function with the product
Fourier coefficients; the equality is proved by two genuine summable series. -/
theorem translated_inner_ae (e d : CircleL2) :
    (fun x : UnitAddCircle => inner ℂ (translate x e) d) =ᵐ[haarAddCircle] correlation e d := by
  let b := fourierBasis (T := 1)
  let f : ℤ → CircleL2 := fun n => fourierCoeff (correlation e d) n • b n
  have hsum : HasSum f (correlation e d) := by
    simpa only [f, b, fourierBasis_repr] using b.hasSum_repr (correlation e d)
  have hn : Summable (fun n => ‖f n‖) := by
    simpa only [f, norm_smul, b.orthonormal.norm_eq_one, mul_one,
      correlation_fourierCoeff] using coefficient_norm_summable e d
  have hae := Lp.hasSum_coeFn_tsum (tsum_enorm_ne_top_iff_summable_norm.mpr hn)
  have hterms : ∀ᵐ x : UnitAddCircle ∂haarAddCircle, ∀ n : ℤ,
      f n x = coefficient e d n * fourier n x := by
    apply ae_all_iff.mpr
    intro n
    have hsmul := Lp.coeFn_smul (fourierCoeff (correlation e d) n) (b n)
    have hb : (b n : UnitAddCircle → ℂ) =ᵐ[haarAddCircle] fourier n := by
      simpa only [b, coe_fourierBasis] using coeFn_fourierLp 2 n
    filter_upwards [hsmul, hb] with x hx hbx
    change (fourierCoeff (correlation e d) n • b n : CircleL2) x = _
    rw [hx, Pi.smul_apply, smul_eq_mul, hbx, correlation_fourierCoeff]
  rw [hsum.tsum_eq] at hae
  filter_upwards [hae, hterms] with x hx htx
  have hp := translated_inner_hasSum e d x
  have hx' := hx.congr_fun (fun n => (htx n).symm)
  exact hp.unique hx'

theorem translated_inner_sq_integrable (e d : CircleL2) :
    Integrable (fun x : UnitAddCircle => ‖inner ℂ (translate x e) d‖ ^ 2) haarAddCircle := by
  have hi := (memLp_two_iff_integrable_sq_norm (Lp.memLp (correlation e d)).aestronglyMeasurable).mp
    (Lp.memLp (correlation e d))
  exact hi.congr ((translated_inner_ae e d).symm.mono (fun _ h => congrArg (fun z : ℂ => ‖z‖ ^ 2) h))

/-- Complete Parseval for the actual translated one-input pairing. -/
theorem translated_inner_energy (e d : CircleL2) :
    (∫ x : UnitAddCircle, ‖inner ℂ (translate x e) d‖ ^ 2 ∂haarAddCircle) =
      ∑' n : ℤ, ‖fourierCoeff e n‖ ^ 2 * ‖fourierCoeff d n‖ ^ 2 := by
  calc
    _ = ∫ x : UnitAddCircle, ‖correlation e d x‖ ^ 2 ∂haarAddCircle := by
      apply integral_congr_ae
      exact (translated_inner_ae e d).mono (fun _ h => congrArg (fun z : ℂ => ‖z‖ ^ 2) h)
    _ = ∑' n : ℤ, ‖fourierCoeff (correlation e d) n‖ ^ 2 :=
      (hasSum_sq_fourierCoeff (correlation e d)).tsum_eq.symm
    _ = _ := by
      apply tsum_congr
      intro n
      rw [correlation_fourierCoeff, coefficient, norm_mul, norm_star, mul_pow]

end SHE.CircleCorrelation
