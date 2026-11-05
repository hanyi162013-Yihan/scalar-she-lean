module

public import SHEStochastic.MatrixUnboundedExitTail

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section

namespace SHEStochastic.MatrixExitPolynomialTail
open MeasureTheory ProbabilityTheory SHEStochastic.HeatParameterCover
open scoped NNReal ENNReal Matrix.Norms.L2Operator
variable {n : ℕ} (G : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ)
    {C β : ℝ≥0} (H : ℝ≥0)

def constant (k : ℕ) (α : ℝ≥0) : ℝ≥0∞ :=
  MatrixUnboundedPointMaximum.momentConstant G (C := C) (β := β) H 0 k*
    constL 64 2 (2*2^k : ℕ) (UnboundedHeatIncrementCaps.exponent β*(2^k : ℕ)) α*
      (HeatFieldThreshold.denominator n α : ℝ≥0∞)^(2*2^k)*(2 : ℝ≥0∞)^(2^k)

theorem constant_finite (k : ℕ) (hq : 2<UnboundedHeatIncrementCaps.exponent β*(2^k : ℕ))
    (α : ℝ≥0) (hα : (α : ℝ)<(UnboundedHeatIncrementCaps.exponent β*(2^k : ℕ)-2)/(2*2^k : ℕ)) :
    constant G (C := C) (β := β) H k α≠⊤ := by
  have hM := MatrixUnboundedPointMaximum.moment_finite G (C := C) (β := β) H 0 k
  have hL := constL_lt_top (by norm_num : (64 : ℝ≥0∞)≠⊤) (by norm_num : (0 : ℝ)<2)
    (by positivity : (0 : ℝ)<(2*2^k : ℕ)) hq hα
  unfold constant
  finiteness

/-- The existing cutoff-independent stochastic error has an explicit
polynomial majorant at every moment order. For beta<1 the exponent is
negative, and the order may be chosen to make the tail integrable. -/
theorem bound (hβ : 0<β) (k : ℕ) (hq : 2<UnboundedHeatIncrementCaps.exponent β*(2^k : ℕ))
    (α : ℝ≥0) (hα : (α : ℝ)<(UnboundedHeatIncrementCaps.exponent β*(2^k : ℕ)-2)/(2*2^k : ℕ))
    (N : ℕ) (hN : 1≤N) :
    MatrixUnboundedExitTail.error G (C := C) (β := β) H k α N≤
      constant G (C := C) (β := β) H k α*(N : ℝ≥0∞)^((2*(β : ℝ)-2)*(2^k : ℕ)) := by
  let L : ℝ≥0∞ := constL 64 2 (2*2^k : ℕ) (UnboundedHeatIncrementCaps.exponent β*(2^k : ℕ)) α
  have hL : L≠⊤ := (constL_lt_top (by norm_num : (64 : ℝ≥0∞)≠⊤) (by norm_num : (0 : ℝ)<2)
    (by positivity : (0 : ℝ)<(2*2^k : ℕ)) hq hα).ne
  have hM := MatrixUnboundedPointMaximum.moment_finite G (C := C) (β := β) H (N : ℝ) k
  have hd : (SublinearHeatIntegratedEnergy.stateFactor (N : ℝ) β/(N : ℝ≥0∞)^2)^(2^k)=
      SublinearHeatIntegratedEnergy.stateFactor (N : ℝ) β^(2^k)/(N : ℝ≥0∞)^(2*2^k) := by
    simpa only [ENNReal.rpow_natCast,pow_mul] using
      ENNReal.div_rpow_of_nonneg (SublinearHeatIntegratedEnergy.stateFactor (N : ℝ) β)
        ((N : ℝ≥0∞)^2) (z := (2^k : ℕ)) (Nat.cast_nonneg _)
  have he : MatrixUnboundedExitTail.error G (C := C) (β := β) H k α N=
      (MatrixUnboundedPointMaximum.momentConstant G (C := C) (β := β) H 0 k*L*
        (HeatFieldThreshold.denominator n α : ℝ≥0∞)^(2*2^k))*
          (SublinearHeatIntegratedEnergy.stateFactor (N : ℝ) β/(N : ℝ≥0∞)^2)^(2^k) := by
    unfold MatrixUnboundedExitTail.error
    rw [HeatFieldThreshold.scaled_eq n α (2*2^k) _ (by finiteness) N (by omega),
      MatrixUnboundedPointMaximum.moment_factor G hβ H (N : ℝ) k,hd]
    change ((MatrixUnboundedPointMaximum.momentConstant G H 0 k*
      SublinearHeatIntegratedEnergy.stateFactor (N : ℝ) β^(2^k)*L)/(N : ℝ≥0∞)^(2*2^k))*_=_
    simp only [div_eq_mul_inv]
    ring
  rw [he]
  apply (mul_le_mul_right (SublinearHeatMomentScale.normalized_bound β N hN (2^k)) _).trans_eq
  unfold constant
  dsimp only [L]
  ring

end SHEStochastic.MatrixExitPolynomialTail
