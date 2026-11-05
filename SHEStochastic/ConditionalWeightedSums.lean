module

public import SHEStochastic.ConditionalOrthogonalSums
public import MathFin.Foundations.ItoIntegralL2

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
noncomputable section

namespace SHEStochastic.ConditionalWeightedSums
open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {Ω κ T : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [Fintype κ] [LinearOrder κ] [Preorder T]

theorem memLp_mul_bounded (X w : Ω → ℝ) (hX : MemLp X 2 μ)
    (hw : AEStronglyMeasurable w μ) (C : ℝ) (hC : 0 ≤ C) (hwb : ∀ ω, |w ω| ≤ C) :
    MemLp (fun ω ↦ w ω * X ω) 2 μ := by
  apply MemLp.mono (hX.const_mul C) (hw.mul hX.aestronglyMeasurable)
  apply Filter.Eventually.of_forall
  intro ω
  change ‖w ω * X ω‖ ≤ ‖C * X ω‖
  rw [norm_mul, norm_mul, Real.norm_eq_abs (w ω), Real.norm_of_nonneg hC]
  exact mul_le_mul_of_nonneg_right (hwb ω) (norm_nonneg _)

theorem memLp_sum (X w : κ → Ω → ℝ) (hX : ∀ k, MemLp (X k) 2 μ)
    (hw : ∀ k, AEStronglyMeasurable (w k) μ)
    (C : ℝ) (hC : 0 ≤ C) (hwb : ∀ k ω, |w k ω| ≤ C) :
    MemLp (fun ω ↦ ∑ k, w k ω * X k ω) 2 μ :=
  memLp_finsetSum _ (fun k _ ↦ memLp_mul_bounded _ _ (hX k) (hw k) C hC (hwb k))

/-- Bounded past weights preserve orthogonality of centered future errors.
The resulting bound needs no independence between the time cells. -/
theorem integral_sq_le (F : Filtration T mΩ) (a b : κ → T)
    (hab : ∀ k, a k ≤ b k) (hsep : ∀ k l, k < l → b k ≤ a l)
    (X w : κ → Ω → ℝ) (hX : ∀ k, MemLp (X k) 2 μ)
    (hXa : ∀ k, AEStronglyMeasurable[F (b k)] (X k) μ)
    (hzero : ∀ k, μ[X k | F (a k)] =ᵐ[μ] (fun _ ↦ 0))
    (hw : ∀ k, StronglyMeasurable[F (a k)] (w k))
    (C : ℝ) (hC : 0 ≤ C) (hwb : ∀ k ω, |w k ω| ≤ C) :
    (∫ ω, (∑ k, w k ω * X k ω) ^ 2 ∂μ) ≤ C ^ 2 * ∑ k, ∫ ω, X k ω ^ 2 ∂μ := by
  classical
  let Z (k : κ) (ω : Ω) := w k ω * X k ω
  have hZ (k : κ) : MemLp (Z k) 2 μ :=
    memLp_mul_bounded _ _ (hX k) ((hw k).mono (F.le (a k))).aestronglyMeasurable C hC (hwb k)
  let A (k : κ) : Lp ℝ 2 μ := (hZ k).toLp (Z k)
  have hrep (k : κ) : A k =ᵐ[μ] Z k := (hZ k).coeFn_toLp
  have hAa (k : κ) : AEStronglyMeasurable[F (b k)] (A k) μ :=
    (((hw k).mono (F.mono (hab k))).aestronglyMeasurable.mul (hXa k)).congr (hrep k).symm
  have hAz (k : κ) : μ[(A k : Ω → ℝ) | F (a k)] =ᵐ[μ] (fun _ ↦ 0) := by
    refine (condExp_congr_ae (hrep k)).trans ?_
    refine (condExp_mul_of_aestronglyMeasurable_left (hw k).aestronglyMeasurable
      ((hZ k).integrable (by norm_num)) ((hX k).integrable (by norm_num))).trans ?_
    filter_upwards [hzero k] with ω hω
    change w k ω * (μ[X k | F (a k)]) ω = 0
    rw [hω, mul_zero]
  have hsum : (∑ k, A k : Lp ℝ 2 μ) =ᵐ[μ] (fun ω ↦ ∑ k, Z k ω) := by
    filter_upwards [Lp.coeFn_finsetSum Finset.univ A, ae_all_iff.mpr hrep] with ω hs hr
    rw [hs]
    simp only [Finset.sum_apply]
    exact Finset.sum_congr rfl (fun k _ ↦ hr k)
  have hpy := ConditionalOrthogonalSums.norm_sum_sq_intervals F a b A Finset.univ
    (fun k _ l _ hkl ↦ hsep k l hkl) (fun k _ ↦ hAa k) (fun k _ ↦ hAz k)
  have hdiag (k : κ) : ‖A k‖ ^ 2 ≤ C ^ 2 * ∫ ω, X k ω ^ 2 ∂μ := by
    calc
      _ = ∫ ω, Z k ω ^ 2 ∂μ :=
        (MathFin.ItoIntegralL2.lp_two_norm_sq _).trans (integral_congr_ae ((hrep k).pow_const 2))
      _ ≤ ∫ ω, C ^ 2 * X k ω ^ 2 ∂μ := by
        apply integral_mono (hZ k).integrable_sq ((hX k).integrable_sq.const_mul _)
        intro ω
        have hw2 : (w k ω) ^ 2 ≤ C ^ 2 := by
          simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hC).mpr (hwb k ω)
        exact (mul_pow (w k ω) (X k ω) 2).le.trans
          (mul_le_mul_of_nonneg_right hw2 (sq_nonneg _))
      _ = _ := integral_const_mul _ _
  calc
    _ = ‖∑ k, A k‖ ^ 2 := (integral_congr_ae (hsum.pow_const 2).symm).trans
      (MathFin.ItoIntegralL2.lp_two_norm_sq _).symm
    _ = ∑ k, ‖A k‖ ^ 2 := hpy
    _ ≤ ∑ k, C ^ 2 * ∫ ω, X k ω ^ 2 ∂μ := Finset.sum_le_sum (fun k _ ↦ hdiag k)
    _ = _ := (Finset.mul_sum _ _ _).symm

end SHEStochastic.ConditionalWeightedSums
