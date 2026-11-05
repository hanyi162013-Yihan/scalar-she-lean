module

public import SHEStochastic.NativeQuadraticBandBounds
public import SHEStochastic.ConditionalWeightedSums
public import MathFin.Foundations.ItoIntegralBrownian
public import MathFin.Foundations.ItoFormulaAdapted

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
noncomputable section

namespace SHEStochastic.NativeQuadraticFluctuation
open MeasureTheory ProbabilityTheory SHE SHE.PredictableL2 SHE.StoppedItoInputs
open scoped NNReal ENNReal Topology

variable {Ω C ι : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {H : ℝ≥0}
local notation "νin" => FiniteScalarIto.inputMeasure F μ H
local notation "D" => (96 * Real.exp (1 / 2 : ℝ) + 2)

/-- A deterministic partition has weighted quadratic-error variance at
most a fixed constant times the sum of squared cell-energy caps. -/
theorem finite_bound (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    (u : Process (E := C) F μ H) (M : ℝ≥0) (hu : ∀ᵐ p ∂νin, ‖u p‖ ≤ M)
    (n : ℕ) (τ : ℕ → ℝ≥0) (hτ : Monotone τ) (hH : τ n ≤ H)
    (w : Fin n → Ω → ℝ) (hw : ∀ i : Fin n, StronglyMeasurable[F (τ i)] (w i))
    (B : ℝ) (hB : 0 ≤ B) (hwb : ∀ i ω, |w i ω| ≤ B) :
    (∫ ω, (∑ i : Fin n, w i ω * QuadraticBandError.error
      (FiniteCylindricalIto.terminalIto P.toCoordinates e) u (τ i) (τ (i + 1)) ω) ^ 2 ∂μ) ≤
        B ^ 2 * D * ∑ i : Fin n, ((((τ (i + 1) - τ i) * M ^ 2 : ℝ≥0) : ℝ) ^ 2) := by
  let J := FiniteCylindricalIto.terminalIto P.toCoordinates e
  let X (i : Fin n) := QuadraticBandError.error J u (τ i) (τ (i + 1))
  have hi (i : Fin n) : MemLp (X i) 2 μ :=
    (NativeQuadraticBandBounds.error_bound P e u M hu (hτ (Nat.le_succ _))
      ((hτ (Nat.succ_le_of_lt i.isLt)).trans hH)).1
  have hb (i : Fin n) : (∫ ω, X i ω ^ 2 ∂μ) ≤
      D * ((((τ (i + 1) - τ i) * M ^ 2 : ℝ≥0) : ℝ) ^ 2) :=
    (NativeQuadraticBandBounds.error_bound P e u M hu (hτ (Nat.le_succ _))
      ((hτ (Nat.succ_le_of_lt i.isLt)).trans hH)).2
  have hh := ConditionalWeightedSums.integral_sq_le F (fun i : Fin n ↦ τ i) (fun i ↦ τ (i + 1))
    (fun i ↦ hτ (Nat.le_succ _))
    (fun i j hij ↦ hτ (Nat.succ_le_of_lt (show (i : ℕ) < j from hij))) X w hi
    (fun i ↦ QuadraticBandError.adapted J u (hτ (Nat.le_succ _)))
    (fun i ↦ QuadraticBandError.centered J (FiniteCylindricalIto.pastLocality P e) u (hτ (Nat.le_succ _)))
    hw B hB hwb
  calc
    _ ≤ B ^ 2 * ∑ i : Fin n, ∫ ω, X i ω ^ 2 ∂μ := hh
    _ ≤ B ^ 2 * ∑ i : Fin n, D * ((((τ (i + 1) - τ i) * M ^ 2 : ℝ≥0) : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ ↦ hb i)) (sq_nonneg _)
    _ = _ := by rw [← Finset.mul_sum]; ring

open MathFin.QuadraticVariationL2

def fluctuation (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    (u : Process (E := C) F μ H) (w : ℝ≥0 → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ i : Fin n, w (unifPart H n i) ω * QuadraticBandError.error
    (FiniteCylindricalIto.terminalIto P.toCoordinates e) u
      (unifPart H n i) (unifPart H n (i + 1)) ω

theorem memLp_fluctuation (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    (u : Process (E := C) F μ H) (M : ℝ≥0) (hu : ∀ᵐ p ∂νin, ‖u p‖ ≤ M)
    (w : ℝ≥0 → Ω → ℝ) (hw : StronglyAdapted F w)
    (B : ℝ) (hB : 0 ≤ B) (hwb : ∀ t ω, |w t ω| ≤ B) (n : ℕ) :
    MemLp (fluctuation P e u w n) 2 μ := by
  have hτ := MathFin.ItoIntegralBrownian.unifPart_mono H n
  apply ConditionalWeightedSums.memLp_sum
    (fun i : Fin n ↦ QuadraticBandError.error (FiniteCylindricalIto.terminalIto P.toCoordinates e) u
      (unifPart H n i) (unifPart H n (i + 1))) (fun i ↦ w (unifPart H n i))
  · intro i
    exact (NativeQuadraticBandBounds.error_bound P e u M hu (hτ (Nat.le_succ _))
      (MathFin.ItoIntegralBrownian.unifPart_le_T (Nat.succ_le_of_lt i.isLt))).1
  · intro i
    exact ((hw _).mono (F.le _)).aestronglyMeasurable
  · exact hB
  · exact fun i ↦ hwb _

/-- Along uniform partitions the bounded-row fluctuation has mean-square
error at most a constant divided by the number of cells. -/
theorem uniform_bound (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    (u : Process (E := C) F μ H) (M : ℝ≥0) (hu : ∀ᵐ p ∂νin, ‖u p‖ ≤ M)
    (w : ℝ≥0 → Ω → ℝ) (hw : StronglyAdapted F w)
    (B : ℝ) (hB : 0 ≤ B) (hwb : ∀ t ω, |w t ω| ≤ B) (n : ℕ) (hn : 0 < n) :
    (∫ ω, fluctuation P e u w n ω ^ 2 ∂μ) ≤
      (B ^ 2 * D * (H : ℝ) ^ 2 * (M : ℝ) ^ 4) / n := by
  have hτ := MathFin.ItoIntegralBrownian.unifPart_mono H n
  have hb := finite_bound P e u M hu n (unifPart H n) hτ
    (MathFin.ItoIntegralBrownian.unifPart_le_T (le_refl n))
    (fun i ↦ w (unifPart H n i)) (fun i ↦ hw _) B hB (fun i ↦ hwb _)
  have hlen (i : Fin n) : (((unifPart H n (i + 1) - unifPart H n i) * M ^ 2 : ℝ≥0) : ℝ) =
      ((H : ℝ) / n) * (M : ℝ) ^ 2 := by
    rw [NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_sub (hτ (Nat.le_succ _))]
    push_cast [unifPart]
    ring
  simp only [hlen, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hb
  change (∫ ω, fluctuation P e u w n ω ^ 2 ∂μ) ≤ _ at hb
  convert hb using 1
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  field_simp

theorem tendsto_mean_square (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    (u : Process (E := C) F μ H) (M : ℝ≥0) (hu : ∀ᵐ p ∂νin, ‖u p‖ ≤ M)
    (w : ℝ≥0 → Ω → ℝ) (hw : StronglyAdapted F w)
    (B : ℝ) (hB : 0 ≤ B) (hwb : ∀ t ω, |w t ω| ≤ B) :
    Filter.Tendsto (fun n ↦ ∫ ω, fluctuation P e u w n ω ^ 2 ∂μ) Filter.atTop (𝓝 0) := by
  apply squeeze_zero' (Filter.Eventually.of_forall fun n ↦ integral_nonneg fun _ ↦ sq_nonneg _)
  · filter_upwards [Filter.eventually_gt_atTop 0] with n hn
    exact uniform_bound P e u M hu w hw B hB hwb n hn
  · exact tendsto_const_div_atTop_nhds_zero_nat _

/-- Mean-square control also gives the L¹ fluctuation limit. -/
theorem tendsto_integral_abs (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    (u : Process (E := C) F μ H) (M : ℝ≥0) (hu : ∀ᵐ p ∂νin, ‖u p‖ ≤ M)
    (w : ℝ≥0 → Ω → ℝ) (hw : StronglyAdapted F w)
    (B : ℝ) (hB : 0 ≤ B) (hwb : ∀ t ω, |w t ω| ≤ B) :
    Filter.Tendsto (fun n ↦ ∫ ω, |fluctuation P e u w n ω| ∂μ) Filter.atTop (𝓝 0) := by
  apply squeeze_zero (fun n ↦ integral_nonneg fun _ ↦ abs_nonneg _)
    (fun n ↦ MathFin.integral_abs_le_sqrt_integral_sq (memLp_fluctuation P e u M hu w hw B hB hwb n))
  simpa only [Real.sqrt_zero, Function.comp_def] using (Real.continuous_sqrt.tendsto 0).comp
    (tendsto_mean_square P e u M hu w hw B hB hwb)

/-- The weighted quadratic errors vanish in measure, without assuming
continuity of the weights or any Itô formula. -/
theorem tendstoInMeasure (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    (u : Process (E := C) F μ H) (M : ℝ≥0) (hu : ∀ᵐ p ∂νin, ‖u p‖ ≤ M)
    (w : ℝ≥0 → Ω → ℝ) (hw : StronglyAdapted F w)
    (B : ℝ) (hB : 0 ≤ B) (hwb : ∀ t ω, |w t ω| ≤ B) :
    TendstoInMeasure μ (fluctuation P e u w) Filter.atTop (fun _ ↦ 0) := by
  have hLp (n : ℕ) := memLp_fluctuation P e u M hu w hw B hB hwb n
  have ht := tendsto_integral_abs P e u M hu w hw B hB hwb
  apply MathFin.ItoFormulaAdapted.tendstoInMeasure_of_tendsto_integral_abs
  · intro n
    simpa only [sub_zero] using (hLp n).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  · exact aestronglyMeasurable_const
  · simpa only [sub_zero] using ht

end SHEStochastic.NativeQuadraticFluctuation
