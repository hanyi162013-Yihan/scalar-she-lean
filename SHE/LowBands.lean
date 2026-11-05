module

public import SHE.SignedPrefix

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace SHE.LowBands
open MeasureTheory AddCircle CircleHeat Finset
open scoped NNReal ENNReal
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

abbrev StateL2 := Lp ℝ 2 (haarAddCircle (T := (1:ℝ)))

theorem centered_lipschitz {a : ℝ → ℂ} {L : ℝ≥0} (ha : LipschitzWith L a) :
    LipschitzWith L (fun z => a z-a 0) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [dist_eq_norm, sub_sub_sub_cancel_right] using ha.dist_le_mul x y

/-- Centering a state band defines its actual L² composition even when
the original band does not vanish at state zero. Centering cancels in
the two-endpoint difference. -/
def composeBand (a : ℝ → ℂ) {L : ℝ≥0} (ha : LipschitzWith L a) (U : StateL2) : CircleL2 :=
  (centered_lipschitz ha).compLp (by simp) U

theorem composeBand_ae (a : ℝ → ℂ) {L : ℝ≥0} (ha : LipschitzWith L a) (U : StateL2) :
    composeBand a ha U =ᵐ[haarAddCircle] (fun x => a (U x)-a 0) :=
  (centered_lipschitz ha).coeFn_compLp (by simp) U

theorem composeBand_difference_ae (a : ℝ → ℂ) {L : ℝ≥0} (ha : LipschitzWith L a)
    (U V : StateL2) :
    (composeBand a ha U-composeBand a ha V : CircleL2) =ᵐ[haarAddCircle]
      (fun x => a (U x)-a (V x)) := by
  filter_upwards [composeBand_ae a ha U, composeBand_ae a ha V,
    Lp.coeFn_sub (composeBand a ha U) (composeBand a ha V)] with x hU hV hsub
  rw [hsub, Pi.sub_apply, hU, hV]
  abel

theorem composeBand_difference_norm (a : ℝ → ℂ) {L : ℝ≥0} (ha : LipschitzWith L a)
    (U V : StateL2) :
    ‖composeBand a ha U-composeBand a ha V‖ ≤ (L:ℝ) * ‖U-V‖ :=
  (centered_lipschitz ha).norm_compLp_sub_le (by simp) U V

/-- A bounded band keeps its endpoint cap after taking the actual L² norm.
This cap and the Lipschitz input bound can therefore be used together. -/
theorem composeBand_difference_cap (a : ℝ → ℂ) {L : ℝ≥0} (ha : LipschitzWith L a)
    {M : ℝ} (hM : 0 ≤ M) (haM : ∀ z, ‖a z‖ ≤ M) (U V : StateL2) :
    ‖composeBand a ha U-composeBand a ha V‖ ≤ min (2*M) ((L:ℝ) * ‖U-V‖) := by
  apply le_min _ (composeBand_difference_norm a ha U V)
  have hb : ∀ᵐ x ∂haarAddCircle,
      ‖(composeBand a ha U-composeBand a ha V : CircleL2) x‖ ≤ 2*M := by
    filter_upwards [composeBand_difference_ae a ha U V] with x hx
    rw [hx]
    exact (norm_sub_le _ _).trans (by linarith [haM (U x), haM (V x)])
  have hh := Lp.norm_le_of_ae_bound (by positivity : 0 ≤ 2*M) hb
  simpa [measureUnivNNReal] using hh

/-- The clipped state-band minimum uses the true physical endpoint
difference, with no Gaussianity or independence hypothesis. -/
theorem composeBand_clipped {ν β C : ℝ} (hν : 0 < ν) (hC : 0 ≤ C)
    (a : ℝ → ℂ) {L : ℝ≥0} (ha : LipschitzWith L a)
    (haB : ∀ z, ‖a z‖ ≤ C * ν ^ (-β)) (hL : (L:ℝ) ≤ C * ν ^ (1-β)) (U V : StateL2) :
    ‖composeBand a ha U-composeBand a ha V‖ ≤
      (2*C*ν ^ (-β)) * min 1 (ν * ‖U-V‖) := by
  have hA : 0 ≤ C * ν ^ (-β) := mul_nonneg hC (Real.rpow_nonneg hν.le _)
  have hh := composeBand_difference_cap a ha hA haB U V
  by_cases hc : ν * ‖U-V‖ ≤ 1
  · rw [min_eq_right hc]
    apply (hh.trans (min_le_right _ _)).trans
    have he : ν ^ (1-β) = ν * ν ^ (-β) := by
      rw [show 1-β = 1+(-β) by ring, Real.rpow_add hν, Real.rpow_one]
    have hl := mul_le_mul_of_nonneg_right hL (norm_nonneg (U-V))
    rw [he] at hl
    nlinarith [mul_nonneg hA (mul_nonneg hν.le (norm_nonneg (U-V)))]
  · rw [min_eq_left (le_of_lt (lt_of_not_ge hc)), mul_one]
    have hh' := hh.trans (min_le_left _ _)
    nlinarith only [hh']

/-- The actual finite low-state comparison field. The inhomogeneous band
may be included as one member of the finite set. -/
def comparison (a : ℕ → ℝ → ℂ) (L : ℕ → ℝ≥0)
    (ha : ∀ j, LipschitzWith (L j) (a j)) (s : Finset ℕ) (U V : StateL2) : CircleL2 :=
  ∑ j ∈ s, (composeBand (a j) (ha j) U-composeBand (a j) (ha j) V)

theorem comparison_norm (a : ℕ → ℝ → ℂ) (L : ℕ → ℝ≥0)
    (ha : ∀ j, LipschitzWith (L j) (a j)) (s : Finset ℕ) (U V : StateL2) :
    ‖comparison a L ha s U V‖ ≤ (∑ j ∈ s, (L j:ℝ)) * ‖U-V‖ := by
  unfold comparison
  calc
    _ ≤ ∑ j ∈ s, ‖composeBand (a j) (ha j) U-composeBand (a j) (ha j) V‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ s, (L j:ℝ) * ‖U-V‖ :=
      sum_le_sum (fun j _ => composeBand_difference_norm (a j) (ha j) U V)
    _ = _ := (sum_mul _ _ _).symm

/-- Direct low-state comparison in the actual massive negative Fourier
norm, valid for arbitrary physical L² states, including time zero. -/
theorem comparison_negative_energy {κ Λ ρ : ℝ} (hΛ : 0 < Λ) (hρ : 0 ≤ ρ)
    (a : ℕ → ℝ → ℂ) (L : ℕ → ℝ≥0) (ha : ∀ j, LipschitzWith (L j) (a j))
    (s : Finset ℕ) (U V : StateL2) :
    StepInput.negativeEnergy κ Λ ρ (comparison a L ha s U V) ≤
      Λ ^ (-ρ) * (∑ j ∈ s, (L j:ℝ)) ^ 2 * ‖U-V‖ ^ 2 := by
  apply (FiniteHaar.negativeEnergy_le_L2 hΛ hρ _).trans
  have hh := pow_le_pow_left₀ (norm_nonneg _) (comparison_norm a L ha s U V) 2
  have hm := mul_le_mul_of_nonneg_left hh (Real.rpow_nonneg hΛ.le (-ρ))
  simpa only [mul_pow, mul_assoc] using hm

theorem negative_norm_le_L2 {κ Λ ρ : ℝ} (hΛ : 0 < Λ) (hρ : 0 ≤ ρ) (f : CircleL2) :
    Real.sqrt (StepInput.negativeEnergy κ Λ ρ f) ≤ Λ ^ (-ρ/2) * ‖f‖ := by
  apply (Real.sqrt_le_sqrt (FiniteHaar.negativeEnergy_le_L2 hΛ hρ f)).trans_eq
  rw [Real.sqrt_mul (Real.rpow_nonneg hΛ.le _), Real.sqrt_sq (norm_nonneg _),
    Real.sqrt_eq_rpow, ← Real.rpow_mul hΛ.le]
  congr 2
  ring

theorem geometric_partial_bound {q : ℝ} (hq : 1 < q) (N : ℕ) :
    (∑ j ∈ range (N+1), q ^ j) ≤ (q/(q-1)) * q ^ N := by
  rw [geom_sum_eq hq.ne' (N+1), div_mul_eq_mul_div]
  apply div_le_div_of_nonneg_right _ (by linarith : 0 ≤ q-1)
  rw [pow_succ]
  nlinarith

def lowBandConstant (β : ℝ) : ℝ := (2:ℝ) ^ (1-β) / ((2:ℝ) ^ (1-β)-1)

/-- The finite original low-state block obeys its genuine geometric
Bernstein bound, including the first band. No spatial regularity of
either state and no freezing or Gaussian comparison is used. -/
theorem dyadic_comparison_norm {β C : ℝ} (hβ : β < 1) (hC : 0 ≤ C)
    (a : ℕ → ℝ → ℂ) (L : ℕ → ℝ≥0) (ha : ∀ j, LipschitzWith (L j) (a j))
    (hL : ∀ j, (L j:ℝ) ≤ C * (((2:ℝ) ^ j) ^ (1-β))) (N : ℕ) (U V : StateL2) :
    ‖comparison a L ha (range (N+1)) U V‖ ≤
      (C * lowBandConstant β) * (((2:ℝ) ^ N) ^ (1-β)) * ‖U-V‖ := by
  have hq : 1 < (2:ℝ) ^ (1-β) := by
    simpa only [Real.rpow_zero] using Real.rpow_lt_rpow_of_exponent_lt
      (by norm_num : (1:ℝ) < 2) (by linarith : (0:ℝ) < 1-β)
  have hsum : (∑ j ∈ range (N+1), (L j:ℝ)) ≤
      C * (lowBandConstant β * (((2:ℝ) ^ N) ^ (1-β))) := by
    calc
      _ ≤ ∑ j ∈ range (N+1), C * (((2:ℝ) ^ (1-β)) ^ j) := by
        apply sum_le_sum
        intro j hj
        simpa only [Real.rpow_pow_comm (by norm_num : (0:ℝ) ≤ 2)] using hL j
      _ = C * ∑ j ∈ range (N+1), ((2:ℝ) ^ (1-β)) ^ j := (mul_sum _ _ _).symm
      _ ≤ C * (lowBandConstant β * (((2:ℝ) ^ N) ^ (1-β))) := by
        have hh := mul_le_mul_of_nonneg_left (geometric_partial_bound hq N) hC
        simpa only [lowBandConstant, Real.rpow_pow_comm (by norm_num : (0:ℝ) ≤ 2)] using hh
  apply (comparison_norm a L ha (range (N+1)) U V).trans
  have hh := mul_le_mul_of_nonneg_right hsum (norm_nonneg (U-V))
  simpa only [mul_assoc] using hh

/-- The manuscript's direct original-low-band comparison with its exact
mass factor. It holds for arbitrary L² endpoint states. The bandwise
Bernstein Lipschitz bounds remain explicit hypotheses on the bands. -/
theorem dyadic_comparison_negative_norm {κ Λ ρ β C : ℝ}
    (hΛ : 0 < Λ) (hρ : 0 ≤ ρ) (hβ : β < 1) (hC : 0 ≤ C)
    (a : ℕ → ℝ → ℂ) (L : ℕ → ℝ≥0) (ha : ∀ j, LipschitzWith (L j) (a j))
    (hL : ∀ j, (L j:ℝ) ≤ C * (((2:ℝ) ^ j) ^ (1-β))) (N : ℕ) (U V : StateL2) :
    Real.sqrt (StepInput.negativeEnergy κ Λ ρ (comparison a L ha (range (N+1)) U V)) ≤
      ((C * lowBandConstant β) * Λ ^ (-ρ/2)) * (((2:ℝ) ^ N) ^ (1-β)) * ‖U-V‖ := by
  apply (negative_norm_le_L2 hΛ hρ _).trans
  have hh := mul_le_mul_of_nonneg_left (dyadic_comparison_norm hβ hC a L ha hL N U V)
    (Real.rpow_nonneg hΛ.le (-ρ/2))
  convert hh using 1; ring

end SHE.LowBands
