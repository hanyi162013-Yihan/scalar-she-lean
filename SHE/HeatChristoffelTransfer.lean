module

public import SHE.HeatChristoffel
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving

/-! Positive row and column transfer from the literal finite heat-span
Christoffel density, acting on one signed physical L² input. -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace SHE.HeatChristoffelTransfer
open MeasureTheory Set Real AddCircle SHE.HeatTorus SHE.HeatTorusKernel
  SHE.HeatProjection SHE.HeatChristoffel
open scoped InnerProductSpace

variable {q r : ℕ} (t : Fin q → ℝ) (a : Fin q → UnitAddCircle)
  (ht : ∀ i, 0 < t i)

theorem evaluation_energy (f : heatSpan t a) :
    (∫ x : UnitAddCircle, ‖evaluation t a ht x f‖ ^ 2 ∂haarAddCircle) = ‖f‖ ^ 2 := by
  change (∫ x : UnitAddCircle, ‖evaluation t a ht x f‖ ^ 2 ∂haarAddCircle) = ‖(f : CircleL2)‖ ^ 2
  rw [SHE.StoppedFourier.L2_norm_sq_eq_integral (f : CircleL2)]
  apply integral_congr_ae
  have h := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) haarAddCircle (continuousLift t a ht f)
  rw [toLp_continuousLift] at h
  filter_upwards [h] with x hx
  rw [hx]
  rfl

def frameDensity (e : Fin r → heatSpan t a) (x : UnitAddCircle) : ℝ :=
  ∑ j, ‖evaluation t a ht x (e j)‖ ^ 2

theorem frameDensity_nonneg (e : Fin r → heatSpan t a) (x : UnitAddCircle) :
    0 ≤ frameDensity t a ht e x := Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem continuous_frameDensity (e : Fin r → heatSpan t a) :
    Continuous (frameDensity t a ht e) := by
  apply continuous_finsetSum
  intro j _
  exact (continuousLift t a ht (e j)).continuous.norm.pow 2

theorem frameDensity_integrable (e : Fin r → heatSpan t a) :
    Integrable (frameDensity t a ht e) haarAddCircle :=
  (continuous_frameDensity t a ht e).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem integral_frameDensity (e : Fin r → heatSpan t a) :
    (∫ x : UnitAddCircle, frameDensity t a ht e x ∂haarAddCircle) = ∑ j, ‖e j‖ ^ 2 := by
  change (∫ x : UnitAddCircle, ∑ j, ‖evaluation t a ht x (e j)‖ ^ 2 ∂haarAddCircle) = _
  rw [integral_finsetSum Finset.univ]
  · simp_rw [evaluation_energy]
  · intro j _
    exact ((continuousLift t a ht (e j)).continuous.norm.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

theorem integral_orthonormal_frameDensity (e : Fin r → heatSpan t a) (he : Orthonormal ℂ e) :
    (∫ x : UnitAddCircle, frameDensity t a ht e x ∂haarAddCircle) = r := by
  rw [integral_frameDensity]
  simp only [he.norm_eq_one, one_pow, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one]

/-- Both marginal masses are exact. The kernel is a genuine translated
positive continuous physical density, rather than an asserted transfer map. -/
theorem frameDensity_row_column_mass (e : Fin r → heatSpan t a) (he : Orthonormal ℂ e)
    (x y : UnitAddCircle) :
    (∫ z : UnitAddCircle, frameDensity t a ht e (z - x) ∂haarAddCircle) = r ∧
    (∫ z : UnitAddCircle, frameDensity t a ht e (y - z) ∂haarAddCircle) = r := by
  constructor
  · rw [integral_sub_right_eq_self]
    exact integral_orthonormal_frameDensity t a ht e he
  · rw [integral_sub_left_eq_self]
    exact integral_orthonormal_frameDensity t a ht e he

theorem continuous_translate_action :
    Continuous (fun p : UnitAddCircle × CircleL2 => translate p.1 p.2) := by
  let g : C(UnitAddCircle × CircleL2, C(UnitAddCircle, UnitAddCircle)) :=
    (ContinuousMap.mk (fun p : UnitAddCircle × UnitAddCircle => p.2 - p.1)
      (by fun_prop)).curry.comp ContinuousMap.fst
  exact continuous_snd.compMeasurePreservingLp g.continuous
    (fun p => measurePreserving_sub_right haarAddCircle p.1) (by norm_num)

/-- Positive Haar averaging acts on the actual signed L² input by true
translations. Its bound is exactly the positive spatial marginal mass. -/
theorem positive_circle_average_bound (k : UnitAddCircle → ℝ)
    (hk : Integrable k haarAddCircle) (hk0 : ∀ x, 0 ≤ k x) (d : CircleL2) :
    Integrable (fun y : UnitAddCircle => k y • translate y d) haarAddCircle ∧
    ‖∫ y : UnitAddCircle, k y • translate y d ∂haarAddCircle‖ ≤
      (∫ y : UnitAddCircle, k y ∂haarAddCircle) * ‖d‖ := by
  have htrans : AEStronglyMeasurable (fun y : UnitAddCircle => translate y d) haarAddCircle :=
    (continuous_translate_action.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
  have hnorm (y : UnitAddCircle) : ‖k y • translate y d‖ = k y * ‖d‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hk0 y), translate_norm]
  have hi : Integrable (fun y : UnitAddCircle => k y • translate y d) haarAddCircle := by
    apply (hk.mul_const ‖d‖).mono' (hk.aestronglyMeasurable.smul htrans)
    exact ae_of_all _ (fun y => (hnorm y).le)
  refine ⟨hi, (norm_integral_le_integral_norm _).trans_eq ?_⟩
  simp_rw [hnorm]
  exact integral_mul_const _ _

/-- The actual finite-span Christoffel kernel transfers one signed input
with an exact rank bound, while retaining its already-proved positive
Gaussian localization pointwise. -/
theorem christoffel_average_bound (e : Fin r → heatSpan t a) (he : Orthonormal ℂ e)
    (d : CircleL2) :
    Integrable (fun y : UnitAddCircle => frameDensity t a ht e y • translate y d) haarAddCircle ∧
    ‖∫ y : UnitAddCircle, frameDensity t a ht e y • translate y d ∂haarAddCircle‖ ≤
      (r : ℝ) * ‖d‖ := by
  have h := positive_circle_average_bound (frameDensity t a ht e)
    (frameDensity_integrable t a ht e) (frameDensity_nonneg t a ht e) d
  rwa [integral_orthonormal_frameDensity t a ht e he] at h

end SHE.HeatChristoffelTransfer
