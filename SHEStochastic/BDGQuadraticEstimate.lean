module

public import SHEStochastic.BDGRealMoments
public import SHEStochastic.BDGMomentAlgebra

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
noncomputable section

namespace SHEStochastic.BDGQuadraticEstimate
open MeasureTheory SHE SHE.PredictableL2 Filter
open scoped NNReal ENNReal

def nextConstant (p : ℕ) (B : ℝ≥0) : ℝ≥0 :=
  2 * (2 * ((2 : ℝ≥0) ^ (2 * p)) ^ 2 * B) ^ 2 + 2 * (2 : ℝ≥0) ^ (2 * p)

variable {Ω C : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {H : ℝ≥0}

/-- The reusable analytic part of BDG moment doubling. The quadratic
identity and its bracket comparison are the only stochastic data; the
same estimate applies to scalar integrals and Hilbert norm squares. -/
theorem estimate (p : ℕ) (B : ℝ≥0)
    (J : StandardTerminalIto (C := C) (E := ℝ) F μ H)
    (hBDG : StandardTerminalBDGPower p J B)
    (X A D : Ω → ℝ) (V : Process (E := C) F μ H)
    (hD0 : ∀ ω, 0 ≤ D ω) (hA0 : ∀ ω, 0 ≤ A ω)
    (hX4p : Integrable (fun ω ↦ ‖X ω‖ ^ (4 * p)) μ)
    (hAp : MemLp (fun ω ↦ A ω ^ p) 2 μ)
    (hDp : MemLp (fun ω ↦ D ω ^ (2 * p)) 2 μ)
    (hDpBound : (∫ ω, D ω ^ (4 * p) ∂μ) ≤ 4 * ∫ ω, ‖X ω‖ ^ (4 * p) ∂μ)
    (hVB : ∀ᵐ ω ∂μ, StochasticExponential.bracket F μ H V ω ≤ D ω ^ 2 * A ω)
    (hSquare : ∀ᵐ ω ∂μ, X ω ^ 2 = 2 * J.integral V ω + A ω) :
    (∫ ω, ‖X ω‖ ^ (4 * p) ∂μ) ≤ (nextConstant p B : ℝ) * ∫ ω, A ω ^ (2 * p) ∂μ := by
  have hAI : Integrable (fun ω ↦ A ω ^ (2 * p)) μ := by
    have hh := hAp.integrable_sq
    simpa only [← pow_mul, Nat.mul_comm p 2] using hh
  have hProd : Integrable (fun ω ↦ D ω ^ (2 * p) * A ω ^ p) μ :=
    (MemLp.mul (hf := hAp) (hφ := hDp)).integrable le_rfl
  have hVP : ∀ᵐ ω ∂μ, StochasticExponential.bracket F μ H V ω ^ p ≤ D ω ^ (2 * p) * A ω ^ p := by
    filter_upwards [hVB] with ω hω
    have hh := pow_le_pow_left₀ (WeightedBracketBound.bracket_nonneg V ω) hω p
    simpa only [mul_pow, ← pow_mul, Nat.mul_comm 2 p] using hh
  have hVI : Integrable (fun ω ↦ StochasticExponential.bracket F μ H V ω ^ p) μ := by
    apply hProd.mono' ((StochasticExponential.bracket_measurable F μ H V).pow_const p).stronglyMeasurable.aestronglyMeasurable
    filter_upwards [hVP] with ω hω
    rwa [Real.norm_of_nonneg (pow_nonneg (WeightedBracketBound.bracket_nonneg V ω) p)]
  obtain ⟨hNI, hNB⟩ := BDGRealMoments.bound p J B hBDG V hVI
  have hN : (∫ ω, ‖J.integral V ω‖ ^ (2 * p) ∂μ) ≤
      (B : ℝ) * ∫ ω, D ω ^ (2 * p) * A ω ^ p ∂μ :=
    hNB.trans (mul_le_mul_of_nonneg_left (integral_mono_ae hVI hProd hVP) B.property)
  have hCS := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (Eventually.of_forall fun ω ↦ pow_nonneg (hD0 ω) (2 * p))
    (Eventually.of_forall fun ω ↦ pow_nonneg (hA0 ω) p)
    (by simpa only [ENNReal.ofReal_ofNat] using hDp)
    (by simpa only [ENNReal.ofReal_ofNat] using hAp)
  simp only [Real.rpow_two, ← Real.sqrt_eq_rpow, ← pow_mul,
    show (2 * p) * 2 = 4 * p by omega, Nat.mul_comm p 2] at hCS
  have hDstep : Real.sqrt (∫ ω, D ω ^ (4 * p) ∂μ) ≤
      2 * Real.sqrt (∫ ω, ‖X ω‖ ^ (4 * p) ∂μ) := by
    have hh := Real.sqrt_le_sqrt hDpBound
    have h4 : Real.sqrt (4 : ℝ) = 2 := by norm_num
    simpa only [show 2 * (2 * p) = 4 * p by omega,
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), h4] using hh
  have hCS' : (∫ ω, D ω ^ (2 * p) * A ω ^ p ∂μ) ≤
      2 * Real.sqrt (∫ ω, ‖X ω‖ ^ (4 * p) ∂μ) * Real.sqrt (∫ ω, A ω ^ (2 * p) ∂μ) :=
    hCS.trans (mul_le_mul_of_nonneg_right hDstep (Real.sqrt_nonneg _))
  have hAest := BDGMomentAlgebra.integral_square_power_le p X (J.integral V) A hA0 hSquare hX4p hNI hAI
  let c : ℝ := (2 : ℝ) ^ (2 * p)
  have hc : 0 ≤ c := by positivity
  have hEst : (∫ ω, ‖X ω‖ ^ (4 * p) ∂μ) ≤
      (2 * c ^ 2 * B) * Real.sqrt (∫ ω, ‖X ω‖ ^ (4 * p) ∂μ) *
        Real.sqrt (∫ ω, A ω ^ (2 * p) ∂μ) + c * ∫ ω, A ω ^ (2 * p) ∂μ := by
    have hh := hN.trans (mul_le_mul_of_nonneg_left hCS' B.property)
    have hg := mul_le_mul_of_nonneg_left hh (sq_nonneg c)
    dsimp only [c] at hg ⊢
    nlinarith
  have hFinal := BDGMomentAlgebra.absorb
    (integral_nonneg fun _ ↦ pow_nonneg (norm_nonneg _) _) (integral_nonneg fun ω ↦ pow_nonneg (hA0 ω) _)
    (by positivity : 0 ≤ 2 * c ^ 2 * (B : ℝ)) hc hEst
  simpa only [nextConstant, NNReal.coe_add, NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_ofNat, c] using hFinal

end SHEStochastic.BDGQuadraticEstimate
