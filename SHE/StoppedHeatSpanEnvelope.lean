module

public import SHE.NativeHeatSpan
public import SHE.IntervalHistoryEnergy

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.StoppedHeatSpanEnvelope
open Set Filter MeasureTheory ProbabilityTheory AddCircle GaussianIncrement StoppedGaussianFeatures StoppedFourier
open scoped BigOperators
local instance stoppedHeatSpanEnvelope_nativePositive : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
variable {n : ℕ}

def weight (σ target : Fin n → ℝ) (center : Fin n → HeatCircle) (lo hi : ℝ) (x : HeatCircle) : ℝ :=
  ∑ i ∈ IntervalHistoryEnergy.active σ hi, NativeHeatSpan.weight (target i - lo) (center i) x

theorem weight_nonneg (σ target : Fin n → ℝ) (center : Fin n → HeatCircle) (lo hi : ℝ) (x : HeatCircle) :
    0 ≤ weight σ target center lo hi x :=
  Finset.sum_nonneg (fun _ _ => NativeHeatSpan.weight_nonneg _ _ _)

/-- The collision-uniform spatial envelope for the literal stopped
endpoint heat span. The positive envelope contains only original active
observations; no new center or artificial path is introduced by padding. -/
theorem stopped_heat_span_envelope (n : ℕ) :
    ∃ H C : ℝ, 0 < H ∧ 0 < C ∧
      ∀ (σ target : Fin n → ℝ) (center : Fin n → HeatCircle),
      (∀ i, σ i ≤ target i) → ∀ {lo hi : ℝ}, lo < hi →
      (∀ i, σ i ≤ lo ∨ hi ≤ σ i) → (∀ i, hi ≤ σ i → target i - lo ≤ H) →
      ∀ z : Fin n → ℂ, ∀ᵐ x : HeatCircle ∂haarAddCircle,
        ‖historyF Finset.univ z σ target center lo x‖ ^ 2 ≤
          C * ‖historyF Finset.univ z σ target center lo‖ ^ 2 * weight σ target center lo hi x := by
  classical
  obtain ⟨H, C, hH, hC, henv⟩ := NativeHeatSpan.native_heat_sum_envelope n
  refine ⟨H, ((n:ℝ)+1)*C, hH, by positivity, ?_⟩
  intro σ target center hages lo hi hgap hstop hsmall z
  by_cases hactive : ∃ i, hi ≤ σ i
  · obtain ⟨i₀, hi₀⟩ := hactive
    let t : Fin n → ℝ := fun i => if hi ≤ σ i then target i - lo else target i₀ - lo
    let a : Fin n → HeatCircle := fun i => if hi ≤ σ i then center i else center i₀
    let v : Fin n → ℂ := fun i => if hi ≤ σ i then z i else 0
    have ht (i : Fin n) : 0 < t i := by
      dsimp only [t]
      split_ifs with h
      · linarith [hages i]
      · linarith [hages i₀]
    have htH (i : Fin n) : t i ≤ H := by
      dsimp only [t]
      split_ifs with h
      · exact hsmall i h
      · exact hsmall i₀ hi₀
    have hsum : historyF Finset.univ z σ target center lo = ∑ i, v i • circleHeat (t i) (a i) := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases h : hi ≤ σ i
      · have hs : lo < σ i := hgap.trans_le h
        simp only [v, t, a, h, hs, ite_true]
      · have hs : ¬ lo < σ i := not_lt.mpr ((hstop i).resolve_right h)
        simp only [v, t, a, h, hs, ite_false, zero_smul]
    have hw (i : Fin n) (x : HeatCircle) : NativeHeatSpan.weight (t i) (a i) x ≤ weight σ target center lo hi x := by
      change NativeHeatSpan.weight (t i) (a i) x ≤
        ∑ j ∈ IntervalHistoryEnergy.active σ hi, NativeHeatSpan.weight (target j - lo) (center j) x
      dsimp only [t, a]
      split_ifs with h
      · exact Finset.single_le_sum (fun j _ => NativeHeatSpan.weight_nonneg (target j - lo) (center j) x)
          (show i ∈ IntervalHistoryEnergy.active σ hi from Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
      · exact Finset.single_le_sum (fun j _ => NativeHeatSpan.weight_nonneg (target j - lo) (center j) x)
          (show i₀ ∈ IntervalHistoryEnergy.active σ hi from Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi₀⟩)
    have htot (x : HeatCircle) : (∑ i, NativeHeatSpan.weight (t i) (a i) x) ≤ (n:ℝ) * weight σ target center lo hi x := by
      simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using
        Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hw i x)
    have hh := henv t a v ht htH
    rw [← hsum] at hh
    filter_upwards [hh] with x hx
    calc
      _ ≤ C * ‖historyF Finset.univ z σ target center lo‖ ^ 2 *
          ((n:ℝ) * weight σ target center lo hi x) :=
        hx.trans (mul_le_mul_of_nonneg_left (htot x) (mul_nonneg hC.le (sq_nonneg _)))
      _ ≤ _ := by
        have hw0 := weight_nonneg σ target center lo hi x
        nlinarith [mul_nonneg (mul_nonneg hC.le (sq_nonneg ‖historyF Finset.univ z σ target center lo‖)) hw0]
  · have hs (i : Fin n) : ¬ lo < σ i := not_lt.mpr ((hstop i).resolve_right (fun h => hactive ⟨i,h⟩))
    have hz : historyF Finset.univ z σ target center lo = 0 := by simp only [historyF, hs, ite_false, Finset.sum_const_zero]
    rw [hz]
    filter_upwards [Lp.coeFn_zero (E := ℂ) (p := 2) (μ := haarAddCircle (T := 2*Real.pi))] with x hx
    simp only [hx, Pi.zero_apply, norm_zero, zero_pow (by norm_num : 2 ≠ 0), mul_zero, zero_mul, le_refl]

end SHE.StoppedHeatSpanEnvelope
