module

public import SHEStochastic.NativeScalarBDGStep
public import SHEStochastic.BDGBoundedReduction
public import SHEStochastic.BDGSecondMoment

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.NativeScalarBDG
open MeasureTheory ProbabilityTheory SHE SHE.PredictableL2 Filter
open scoped NNReal ENNReal

variable {Ω C ι : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {H : ℝ≥0}

/-- Truncation extends the proved bounded-row doubling estimate to
every original predictable L² input, preserving the universal constant. -/
theorem doubling (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    (p : ℕ) (hp : 0 < p) (B : ℝ≥0)
    (hBDG : StandardTerminalBDGPower p (FiniteCylindricalIto.terminalIto P.toCoordinates e) B) :
    StandardTerminalBDGPower (2 * p) (FiniteCylindricalIto.terminalIto P.toCoordinates e)
      (NativeScalarBDGStep.nextConstant p B) := by
  let J := FiniteCylindricalIto.terminalIto P.toCoordinates e
  apply BDGBoundedReduction.of_bounded
  intro u n hu
  let M : ℝ≥0 := n
  have huM : ∀ᵐ x ∂(energyMeasure μ H).trim (predictable_le_product F), ‖u x‖ ≤ M := hu
  have hLp := NativeBoundedMoments.memLp_stopped P e u M huM H ((4 * p : ℕ) : ℝ≥0)
  rw [FiniteItoStoppedVersions.stop_horizon] at hLp
  have hOut : Integrable (fun ω ↦ ‖J.integral u ω‖ ^ (2 * (2 * p))) μ := by
    simpa only [show 2 * (2 * p) = 4 * p by omega] using
      hLp.integrable_norm_pow (by omega : 4 * p ≠ 0)
  let A := StochasticExponential.bracket F μ H u
  let K : ℝ := (timeMeasure H).real Set.univ * (M : ℝ) ^ 2
  have hAb : ∀ᵐ ω ∂μ, A ω ≤ K := WeightedBracketBound.bounded u M M.property huM
  have hA : Integrable (fun ω ↦ A ω ^ (2 * p)) μ := by
    apply Integrable.of_bound ((StochasticExponential.bracket_measurable F μ H u).pow_const
      (2 * p)).stronglyMeasurable.aestronglyMeasurable (K ^ (2 * p))
    filter_upwards [hAb] with ω hω
    rw [Real.norm_of_nonneg (pow_nonneg (WeightedBracketBound.bracket_nonneg u ω) _)]
    exact pow_le_pow_left₀ (WeightedBracketBound.bracket_nonneg u ω) hω _
  apply BDGRealMoments.of_real_bound (2 * p) J (NativeScalarBDGStep.nextConstant p B) u hOut hA
  simpa only [show 2 * (2 * p) = 4 * p by omega] using
    NativeScalarBDGStep.bounded_moment P e p hp B hBDG u M huM

def constant : ℕ → ℝ≥0
  | 0 => 1
  | k + 1 => NativeScalarBDGStep.nextConstant (2 ^ k) (constant k)

theorem power_two (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    (k : ℕ) :
    StandardTerminalBDGPower (2 ^ k) (FiniteCylindricalIto.terminalIto P.toCoordinates e) (constant k) := by
  induction k with
  | zero =>
      simpa only [pow_zero, constant] using
        (BDGSecondMoment.power_one (FiniteCylindricalIto.terminalIto P.toCoordinates e))
  | succ k ih =>
      simpa only [constant, pow_succ, Nat.mul_comm (2 ^ k) 2] using
        doubling P e (2 ^ k) (by positivity) (constant k) ih

/-- Scalar BDG16 for the actual native integral, with arbitrary L²
Hilbert-noise rows. No null-completeness hypothesis or additional stochastic input is used. -/
theorem scalarBDG16 (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    :
    StandardTerminalBDG16 (FiniteCylindricalIto.terminalIto P.toCoordinates e) (constant 3) := by
  change StandardTerminalBDGPower 8 _ _
  simpa only [show (2 : ℕ) ^ 3 = 8 by decide] using power_two P e 3

omit [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C] in
/-- A countable noise basis supplies the descriptive-space instances.
Any deterministic extended bracket cap therefore gives every dyadic
moment, without requiring callers to repeat measurability setup. -/
theorem moment_of_bracket_bound (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    (k : ℕ) (u : Process (E := C) F μ H) {L : ℝ≥0∞}
    (hbr : ∀ᵐ ω ∂μ, (∫⁻ s, ENNReal.ofReal (‖u (s, ω)‖ ^ 2) ∂timeMeasure H) ≤ L) :
    (∫⁻ ω, ENNReal.ofReal
      (‖(FiniteCylindricalIto.terminalIto P.toCoordinates e).integral u ω‖ ^ (2 * 2 ^ k)) ∂μ) ≤
      (constant k : ℝ≥0∞) * L ^ (2 ^ k) := by
  letI : MeasurableSpace C := borel _
  letI : BorelSpace C := ⟨rfl⟩
  letI : SecondCountableTopology C := e.repr.toHomeomorph.secondCountableTopology
  apply (power_two P e k u).trans
  apply mul_le_mul_right
  have hh := lintegral_mono_ae (hbr.mono fun _ hω ↦ pow_le_pow_left₀ (by simp) hω (2 ^ k))
  simpa only [lintegral_const, measure_univ, mul_one] using hh

omit [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C] in
theorem difference_moment_of_bracket_bound (P : FiniteScalarIto.Family F μ H ι)
    (e : HilbertBasis ι ℝ C) (k : ℕ) (u v : Process (E := C) F μ H) {L : ℝ≥0∞}
    (hbr : ∀ᵐ ω ∂μ, (∫⁻ s, ENNReal.ofReal (‖(u - v) (s, ω)‖ ^ 2) ∂timeMeasure H) ≤ L) :
    (∫⁻ ω, ENNReal.ofReal
      (‖(FiniteCylindricalIto.terminalIto P.toCoordinates e).integral u ω -
        (FiniteCylindricalIto.terminalIto P.toCoordinates e).integral v ω‖ ^ (2 * 2 ^ k)) ∂μ) ≤
      (constant k : ℝ≥0∞) * L ^ (2 ^ k) := by
  let J := FiniteCylindricalIto.terminalIto P.toCoordinates e
  have he : J.integral (u - v) =ᵐ[μ] fun ω ↦ J.integral u ω - J.integral v ω := by
    rw [map_sub]
    exact Lp.coeFn_sub _ _
  exact (lintegral_congr_ae (he.mono fun _ hx ↦
    congrArg (fun z ↦ ENNReal.ofReal (‖z‖ ^ (2 * 2 ^ k))) hx)).symm.trans_le
      (moment_of_bracket_bound P e k (u - v) hbr)

end SHEStochastic.NativeScalarBDG
