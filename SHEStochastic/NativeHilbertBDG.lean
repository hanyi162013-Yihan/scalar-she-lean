module

public import SHEStochastic.NativeFiniteHilbertBDG
public import SHEStochastic.HilbertCoefficientBounds
public import SHEStochastic.NoiseRestrictionBounds

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
noncomputable section

namespace SHEStochastic.NativeHilbertBDG
open MeasureTheory ProbabilityTheory SHE SHE.PredictableL2 SHE.HilbertColumns Filter
open scoped NNReal ENNReal Topology

variable {Ω ι κ β C E : Type*} [MeasurableSpace Ω] [Countable ι] [Countable κ]
  [Countable β] [DecidableEq β]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [SecondCountableTopology E]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {H : ℝ≥0}

local instance : MeasurableSpace (Space ι ℝ) := borel _
local instance : BorelSpace (Space ι ℝ) := ⟨rfl⟩
local instance : MeasurableSpace (Space ι E) := borel _
local instance : BorelSpace (Space ι E) := ⟨rfl⟩

/-- Finite output projections have a uniform bound in terms of the
original, full Hilbert-input bracket. The constant does not depend on
the projection or the bound on the input. -/
theorem partial_power_bound (P : FiniteScalarIto.Family F μ H β)
    (e : HilbertBasis β ℝ C) (r : Space ι ℝ →ₗᵢ[ℝ] C) (b : HilbertBasis κ ℝ E)
    (p : ℕ) (hp : 0 < p) (B : ℝ≥0)
    (hBDG : StandardTerminalBDGPower p (FiniteCylindricalIto.terminalIto P.toCoordinates e) B)
    (u : Process (E := Space ι E) F μ H) (M : ℝ≥0)
    (hu : ∀ᵐ x ∂(energyMeasure μ H).trim (predictable_le_product F), ‖u x‖ ≤ M)
    (s : Finset κ) :
    (∫⁻ ω, ENNReal.ofReal (‖∑ j ∈ s,
      (restrictNoise (FiniteCylindricalIto.terminalIto P.toCoordinates e) r).integral
        (HilbertTerminalIto.coefficient F μ H b u j) ω • b j‖ ^ (4 * p)) ∂μ) ≤
      (BDGQuadraticEstimate.nextConstant p B : ℝ≥0∞) *
        ∫⁻ ω, (∫⁻ r, ENNReal.ofReal (‖u (r, ω)‖ ^ 2) ∂timeMeasure H) ^ (2 * p) ∂μ := by
  classical
  let K0 := FiniteCylindricalIto.terminalIto P.toCoordinates e
  let J := restrictNoise K0 r
  let R (j : s) := NoiseRestrictionBounds.input r (HilbertTerminalIto.coefficient F μ H b u j)
  let v (j : s) := b j
  let Z (ω : Ω) := FiniteOrthonormalSums.value v (fun j ↦ K0.integral (R j) ω)
  let A (ω : Ω) := ∑ j : s, StochasticExponential.bracket F μ H (R j) ω
  have hR (j : s) : ∀ᵐ x ∂(energyMeasure μ H).trim (predictable_le_product F), ‖R j x‖ ≤ M :=
    NoiseRestrictionBounds.bounded r _ M (HilbertCoefficientBounds.bounded b u M hu j)
  have hZ : Integrable (fun ω ↦ ‖Z ω‖ ^ (4 * p)) μ := by
    have hLp (j : s) := NativeBoundedMoments.memLp_stopped P e (R j) M (hR j) H ((4 * p : ℕ) : ℝ≥0)
    simp only [FiniteItoStoppedVersions.stop_horizon] at hLp
    exact (FiniteOrthonormalSums.memLp v _ ((4 * p : ℕ) : ℝ≥0) hLp).integrable_norm_pow
      (by omega : 4 * p ≠ 0)
  have hA0 (ω : Ω) : 0 ≤ A ω :=
    Finset.sum_nonneg fun j _ ↦ WeightedBracketBound.bracket_nonneg (R j) ω
  have hAm : Measurable A := Finset.measurable_sum _
    (fun j _ ↦ StochasticExponential.bracket_measurable F μ H (R j))
  have hAU : ∀ᵐ ω ∂μ, A ω ≤ StochasticExponential.bracket F μ H u ω := by
    have he (ω : Ω) := Finset.sum_coe_sort s
      (fun j ↦ StochasticExponential.bracket F μ H (HilbertTerminalIto.coefficient F μ H b u j) ω)
    filter_upwards [HilbertCoefficientBounds.partial_bracket_le b u s,
      ae_all_iff.mpr (fun j : s ↦ NoiseRestrictionBounds.bracket_eq r
        (HilbertTerminalIto.coefficient F μ H b u j))] with ω hω hr
    change (∑ j : s, StochasticExponential.bracket F μ H (R j) ω) ≤ _
    calc
      _ = ∑ j : s, StochasticExponential.bracket F μ H
          (HilbertTerminalIto.coefficient F μ H b u j) ω :=
        Finset.sum_congr rfl (fun j _ ↦ hr j)
      _ = ∑ j ∈ s, StochasticExponential.bracket F μ H
          (HilbertTerminalIto.coefficient F μ H b u j) ω := he ω
      _ ≤ _ := hω
  let K : ℝ := (timeMeasure H).real Set.univ * (M : ℝ) ^ 2
  have hUb := WeightedBracketBound.bounded u M M.property hu
  have hAI : Integrable (fun ω ↦ A ω ^ (2 * p)) μ := by
    apply Integrable.of_bound (hAm.pow_const (2 * p)).stronglyMeasurable.aestronglyMeasurable (K ^ (2 * p))
    filter_upwards [hAU, hUb] with ω hω hU
    rw [Real.norm_of_nonneg (pow_nonneg (hA0 ω) (2 * p))]
    exact pow_le_pow_left₀ (hA0 ω) (hω.trans hU) (2 * p)
  have hb := NativeFiniteHilbertBDG.bounded_moment P e p hp B hBDG
    R M hR v (b.orthonormal.comp Subtype.val Subtype.val_injective)
  have hZe : (fun ω ↦ ∑ j ∈ s, J.integral (HilbertTerminalIto.coefficient F μ H b u j) ω • b j) = Z := by
    funext ω
    exact (Finset.sum_coe_sort s
      (fun j ↦ J.integral (HilbertTerminalIto.coefficient F μ H b u j) ω • b j)).symm
  change (∫ ω, ‖Z ω‖ ^ (4 * p) ∂μ) ≤
    (BDGQuadraticEstimate.nextConstant p B : ℝ) * ∫ ω, A ω ^ (2 * p) ∂μ at hb
  change (∫⁻ ω, ENNReal.ofReal (‖∑ j ∈ s,
    J.integral (HilbertTerminalIto.coefficient F μ H b u j) ω • b j‖ ^ (4 * p)) ∂μ) ≤ _
  rw [show (fun ω ↦ ENNReal.ofReal (‖∑ j ∈ s,
    J.integral (HilbertTerminalIto.coefficient F μ H b u j) ω • b j‖ ^ (4 * p))) =
      (fun ω ↦ ENNReal.ofReal (‖Z ω‖ ^ (4 * p))) by
        funext ω
        rw [congrFun hZe ω]]
  calc
    _ = ENNReal.ofReal (∫ ω, ‖Z ω‖ ^ (4 * p) ∂μ) :=
      (ofReal_integral_eq_lintegral_ofReal hZ (Eventually.of_forall fun _ ↦ by positivity)).symm
    _ ≤ ENNReal.ofReal ((BDGQuadraticEstimate.nextConstant p B : ℝ) * ∫ ω, A ω ^ (2 * p) ∂μ) :=
      ENNReal.ofReal_le_ofReal hb
    _ = (BDGQuadraticEstimate.nextConstant p B : ℝ≥0∞) * ∫⁻ ω, ENNReal.ofReal (A ω ^ (2 * p)) ∂μ := by
      rw [← ofReal_integral_eq_lintegral_ofReal hAI
        (Eventually.of_forall fun ω ↦ pow_nonneg (hA0 ω) (2 * p))]
      exact (ENNReal.ofReal_mul (BDGQuadraticEstimate.nextConstant p B).property).trans (by simp)
    _ ≤ _ := by
      apply mul_le_mul_right _ (BDGQuadraticEstimate.nextConstant p B : ℝ≥0∞)
      apply lintegral_mono_ae
      filter_upwards [hAU, WeightedBracketBound.lintegral_eq u] with ω hω he
      rw [he, ← ENNReal.ofReal_pow (WeightedBracketBound.bracket_nonneg u ω)]
      exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (hA0 ω) hω (2 * p))

/-- Countably many orthogonal Hilbert-output directions are recovered
by Fatou from the dimension-independent finite-dimensional estimate.
Predictable-row truncation then gives every original L² input. -/
theorem hilbertPower (P : FiniteScalarIto.Family F μ H β)
    (e : HilbertBasis β ℝ C) (r : Space ι ℝ →ₗᵢ[ℝ] C) (b : HilbertBasis κ ℝ E)
    (p : ℕ) (hp : 0 < p) (B : ℝ≥0)
    (hBDG : StandardTerminalBDGPower p (FiniteCylindricalIto.terminalIto P.toCoordinates e) B)
    :
    StandardTerminalBDGPower (2 * p) (HilbertTerminalIto.terminalIto F μ H b
      (restrictNoise (FiniteCylindricalIto.terminalIto P.toCoordinates e) r)) (BDGQuadraticEstimate.nextConstant p B) := by
  classical
  let J := restrictNoise (FiniteCylindricalIto.terminalIto P.toCoordinates e) r
  let I := HilbertTerminalIto.terminalIto F μ H b J
  change StandardTerminalBDGPower (2 * p) I (BDGQuadraticEstimate.nextConstant p B)
  apply BDGBoundedReduction.of_bounded
  intro u n hu
  simp only [show 2 * (2 * p) = 4 * p by omega]
  change (∫⁻ ω, ENNReal.ofReal (‖I.integral u ω‖ ^ (4 * p)) ∂μ) ≤ _
  let Z (s : Finset κ) (ω : Ω) := ∑ j ∈ s,
    J.integral (HilbertTerminalIto.coefficient F μ H b u j) ω • b j
  have hcoord := ae_all_iff.mpr (HilbertCoefficientBounds.integral_coordinate_ae b J u)
  have hlim : ∀ᵐ ω ∂μ, Tendsto (fun s ↦ Z s ω) atTop (𝓝 (I.integral u ω)) := by
    filter_upwards [hcoord] with ω hω
    have hh := b.hasSum_repr (I.integral u ω)
    change Tendsto (fun s : Finset κ ↦ ∑ j ∈ s, b.repr (I.integral u ω) j • b j)
      atTop (𝓝 (I.integral u ω)) at hh
    have hc (j : κ) : innerSL ℝ (b j) (I.integral u ω) =
        J.integral (HilbertTerminalIto.coefficient F μ H b u j) ω := hω j
    simpa only [HilbertBasis.repr_apply_apply, ← innerSL_apply_apply, hc, Z] using hh
  have hm (s : Finset κ) : Measurable (fun ω ↦ ENNReal.ofReal (‖Z s ω‖ ^ (4 * p))) := by
    have hZ : StronglyMeasurable (Z s) := by
      convert Finset.stronglyMeasurable_sum s
        (fun j _ ↦ (Lp.stronglyMeasurable
          (J.integral (HilbertTerminalIto.coefficient F μ H b u j))).smul_const (b j)) using 1
      ext ω
      simp only [Z, Finset.sum_apply]
    exact (hZ.norm.pow (4 * p)).measurable.ennreal_ofReal
  calc
    _ = ∫⁻ ω, liminf (fun s ↦ ENNReal.ofReal (‖Z s ω‖ ^ (4 * p))) atTop ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [hlim] with ω hω
      exact (ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hω.norm.pow (4 * p))).liminf_eq.symm
    _ ≤ liminf (fun s ↦ ∫⁻ ω, ENNReal.ofReal (‖Z s ω‖ ^ (4 * p)) ∂μ) atTop :=
      lintegral_liminf_le hm
    _ ≤ _ := liminf_le_of_frequently_le' (Eventually.of_forall
      (fun s ↦ partial_power_bound P e r b p hp B hBDG u n hu s)).frequently

/-- All dyadic even moments are available for localization and stochastic
factorization. The scalar induction is reused; no second Hilbert induction
or extra moment assumption is needed. -/
theorem power_two (P : FiniteScalarIto.Family F μ H β)
    (e : HilbertBasis β ℝ C) (r : Space ι ℝ →ₗᵢ[ℝ] C) (b : HilbertBasis κ ℝ E)
    (k : ℕ) :
    StandardTerminalBDGPower (2 ^ k) (HilbertTerminalIto.terminalIto F μ H b
      (restrictNoise (FiniteCylindricalIto.terminalIto P.toCoordinates e) r)) (NativeScalarBDG.constant k) := by
  cases k with
  | zero => simpa only [pow_zero, NativeScalarBDG.constant] using BDGSecondMoment.power_one _
  | succ k =>
      simpa only [pow_succ, Nat.mul_comm (2 ^ k) 2, NativeScalarBDG.constant] using
        hilbertPower P e r b (2 ^ k) (by positivity) (NativeScalarBDG.constant k)
          (NativeScalarBDG.power_two P e k)

/-- The exact original sixteenth-moment interface is the third dyadic case. -/
theorem hilbertBDG16 (P : FiniteScalarIto.Family F μ H β)
    (e : HilbertBasis β ℝ C) (r : Space ι ℝ →ₗᵢ[ℝ] C) (b : HilbertBasis κ ℝ E) :
    StandardTerminalBDG16 (HilbertTerminalIto.terminalIto F μ H b
      (restrictNoise (FiniteCylindricalIto.terminalIto P.toCoordinates e) r)) (NativeScalarBDG.constant 3) := by
  change StandardTerminalBDGPower 8 _ _
  simpa only [show (2 : ℕ) ^ 3 = 8 by decide] using power_two P e r b 3

end SHEStochastic.NativeHilbertBDG
