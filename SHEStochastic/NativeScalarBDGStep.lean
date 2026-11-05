module

public import SHEStochastic.NativeBoundedAEVersion
public import SHEStochastic.NativeSquareFormula
public import SHEStochastic.DoobAEEnvelope
public import SHEStochastic.BDGRealMoments
public import SHEStochastic.BDGMomentAlgebra
public import SHEStochastic.BDGQuadraticEstimate

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
noncomputable section

namespace SHEStochastic.NativeScalarBDGStep
open MeasureTheory ProbabilityTheory SHE SHE.PredictableL2 SHE.StoppedItoInputs Filter
open scoped NNReal ENNReal

abbrev nextConstant := BDGQuadraticEstimate.nextConstant

variable {Ω C ι : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {H : ℝ≥0}

/-- One scalar BDG moment-doubling step, proved from the actual square
formula and Doob's inequality. Predictable almost surely continuous versions keep the original
filtration, without imposing null completeness. -/
theorem bounded_moment (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    (p : ℕ) (hp : 0 < p) (B : ℝ≥0)
    (hBDG : StandardTerminalBDGPower p (FiniteCylindricalIto.terminalIto P.toCoordinates e) B)
    (u : Process (E := C) F μ H) (M : ℝ≥0)
    (hu : ∀ᵐ x ∂(energyMeasure μ H).trim (predictable_le_product F), ‖u x‖ ≤ M) :
    (∫ ω, ‖(FiniteCylindricalIto.terminalIto P.toCoordinates e).integral u ω‖ ^ (4 * p) ∂μ) ≤
      (nextConstant p B : ℝ) * ∫ ω, StochasticExponential.bracket F μ H u ω ^ (2 * p) ∂μ := by
  let J := FiniteCylindricalIto.terminalIto P.toCoordinates e
  obtain ⟨Y, hYc, hYa, hYp, hYm, hYr, hMem, hCap⟩ :=
    NativeBoundedAEVersion.exists_version P e u M hu
  have hYI (t : ℝ≥0) (k : ℕ) (hk : 0 < k) : Integrable (fun ω ↦ ‖Y t ω‖ ^ k) μ :=
    (hMem t k).integrable_norm_pow hk.ne'
  have hY4p := hYI H (4 * p) (by omega)
  have hT : MemLp (fun ω ↦ ‖Y H ω‖ ^ (2 * p)) 2 μ := by
    apply (memLp_two_iff_integrable_sq (((hYa H).mono (F.le H)).norm.aestronglyMeasurable.pow (2 * p))).mpr
    change Integrable (fun ω ↦ (‖Y H ω‖ ^ (2 * p)) ^ 2) μ
    simpa only [← pow_mul, show (2 * p) * 2 = 4 * p by omega] using hY4p
  obtain ⟨D, hD, hD0, hDb, hDmax⟩ := DoobAEEnvelope.exists_envelope hYm hYc H (hMem H 2)
  have hDY : ∀ᵐ ω ∂μ, ∀ t, |Y t ω| ≤ D ω := by
    filter_upwards [hDb, hCap] with ω hbω hcω
    intro t
    rw [hcω t]
    exact hbω (min t H) (min_le_right t H)
  obtain ⟨hDp, hDpBound⟩ := DoobAEEnvelope.bound hYm hYc H D hD hD0 hDb hDmax (2 * p)
    (fun t ↦ hYI t (2 * p) (by omega)) hT
  let A := StochasticExponential.bracket F μ H u
  have hA0 (ω : Ω) : 0 ≤ A ω := WeightedBracketBound.bracket_nonneg u ω
  let K : ℝ := (timeMeasure H).real Set.univ * (M : ℝ) ^ 2
  have hK : 0 ≤ K := mul_nonneg measureReal_nonneg (sq_nonneg _)
  have hAb : ∀ᵐ ω ∂μ, A ω ≤ K := WeightedBracketBound.bounded u M M.property hu
  have hAp (k : ℕ) : MemLp (fun ω ↦ A ω ^ k) 2 μ := by
    apply MemLp.of_bound ((StochasticExponential.bracket_measurable F μ H u).pow_const k).stronglyMeasurable.aestronglyMeasurable (K ^ k)
    filter_upwards [hAb] with ω hω
    rw [Real.norm_of_nonneg (pow_nonneg (hA0 ω) k)]
    exact pow_le_pow_left₀ (hA0 ω) hω k
  have hAI : Integrable (fun ω ↦ A ω ^ (2 * p)) μ := (hAp (2 * p)).integrable one_le_two
  let V := PredictableEnvelopeMultiplier.process u M M.property hu (Function.uncurry Y) hYp D hD
    (PredictableEnvelopeMultiplier.path_bound Y D hDY)
  have hVrep : V =ᵐ[energyMeasure μ H] (fun x ↦ Y x.1 x.2 • u x) :=
    PredictableEnvelopeMultiplier.process_ae u M M.property hu _ hYp D hD (PredictableEnvelopeMultiplier.path_bound Y D hDY)
  have hVB := WeightedBracketBound.weighted u V (Function.uncurry Y) hVrep D hD0
    (PredictableEnvelopeMultiplier.path_bound Y D hDY)
  have hSquare := NativeSquareFormula.formula P e u M M.property hu Y hYa hYp
    (hYc.mono fun _ hω ↦ hω.continuousOn) hYr D hD hD0 hDY
  have hY0 : Y 0 =ᵐ[μ] (fun _ ↦ (0 : ℝ)) := by
    have hh := hYr 0
    rw [NNReal.coe_zero, stop_zero, map_zero] at hh
    exact hh.trans (Lp.coeFn_zero _ _ _)
  have hSquare' : ∀ᵐ ω ∂μ, Y H ω ^ 2 = 2 * J.integral V ω + A ω := by
    filter_upwards [hSquare, hY0] with ω hs hz
    change Y H ω ^ 2 - Y 0 ω ^ 2 = 2 * J.integral V ω + A ω at hs
    simpa only [hz, zero_pow (by decide : 2 ≠ 0), sub_zero] using hs
  have hFinal := BDGQuadraticEstimate.estimate p B J hBDG (Y H) A D V hD0 hA0 hY4p (hAp p) hDp
    (by simpa only [show 2 * (2 * p) = 4 * p by omega] using hDpBound) hVB hSquare'
  have hEnd : Y H =ᵐ[μ] J.integral u := by
    have hh := hYr H
    rwa [FiniteItoStoppedVersions.stop_horizon] at hh
  have hEI : (∫ ω, ‖Y H ω‖ ^ (4 * p) ∂μ) = ∫ ω, ‖J.integral u ω‖ ^ (4 * p) ∂μ :=
    integral_congr_ae (hEnd.mono fun ω hω ↦ by
      change ‖Y H ω‖ ^ (4 * p) = ‖J.integral u ω‖ ^ (4 * p)
      rw [hω])
  rw [hEI] at hFinal
  exact hFinal

end SHEStochastic.NativeScalarBDGStep
