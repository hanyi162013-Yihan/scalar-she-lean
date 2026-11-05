module

public import SHEStochastic.NativeFiniteItoHorizon
public import SHEStochastic.FiniteItoIntervalTime

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
noncomputable section

namespace SHEStochastic.NativeFiniteItoInterval
open MeasureTheory ProbabilityTheory Set SHE SHE.PredictableL2 SHE.GaussianItoTest SHE.StoppedItoInputs
open scoped NNReal ENNReal Topology

variable {Ω C ι : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {H : ℝ≥0} {n : ℕ}

/-- Finite-dimensional native Itô formula on any deterministic interval,
with EXACT original gradient-row noise and original covariance density. -/
theorem formula_random (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    (R : Fin n → Process (E := C) F μ H) (z : Ω → State n)
    (Y : ℝ≥0 × Ω → State n) (hY : StronglyMeasurable[F.predictable] Y)
    (hc : ∀ ω, Continuous (fun t ↦ Y (t, ω)))
    (hRep : ∀ t : ℝ≥0, t ≤ H → (fun ω ↦ Y (t, ω)) =ᵐ[μ]
      (fun ω ↦ StandardFiniteIto.vectorIntegral F μ H (FiniteCylindricalIto.terminalIto P.toCoordinates e) (z ω) R t ω))
    (a b : ℝ≥0) (hab : a ≤ b) (hbH : b ≤ H)
    (G dG : ℝ → State n → ℝ) (hG : RegularTest (a : ℝ) (b : ℝ) G dG) :
    ∀ᵐ ω ∂μ, G b (Y (b, ω)) = G a (Y (a, ω)) +
      FiniteItoNoise.noise F μ H Y hY R (FiniteCylindricalIto.terminalIto P.toCoordinates e) a b G ω +
      ∫ r in (a : ℝ)..(b : ℝ), dG r (Y (r.toNNReal, ω)) + (1 / 2 : ℝ) *
        GaussianTaylorAverage.covarianceAction (StandardFiniteIto.rowCovariance F μ H R ω r)
          (GaussianTaylor.hessian (G r) (Y (r.toNNReal, ω))) := by
  let J := FiniteCylindricalIto.terminalIto P.toCoordinates e
  let YB := FiniteItoStoppedVersions.stopped Y b
  let YA := FiniteItoStoppedVersions.stopped Y a
  let hYB := FiniteItoStoppedVersions.predictable Y hY hc b
  let hYA := FiniteItoStoppedVersions.predictable Y hY hc a
  let GB := FiniteItoTestExtension.value a b G
  let GA := FiniteItoTestExtension.constant G a
  let dGB := FiniteItoTestExtension.derivative a b dG
  have hgb := FiniteItoTestExtension.regular (by exact_mod_cast hab) hG H
  have hga := FiniteItoTestExtension.constant_regular hG a H
  let UB := FiniteItoIntervalAlgebra.stoppedGradient b R Y hY hc GB (FiniteItoNoise.regular_admissible hgb)
  let UA := FiniteItoIntervalAlgebra.stoppedGradient a R Y hY hc GA (FiniteItoNoise.regular_admissible hga)
  have hB := NativeFiniteItoHorizon.formula_random P e (fun i ↦ stop F μ H b (R i)) z YB hYB
    (FiniteItoStoppedVersions.continuous Y hc b)
    (fun r hr ↦ FiniteItoStoppedVersions.represents_random J R z Y hRep b r hr) GB dGB hgb
  have hA := NativeFiniteItoHorizon.formula_random P e (fun i ↦ stop F μ H a (R i)) z YA hYA
    (FiniteItoStoppedVersions.continuous Y hc a)
    (fun r hr ↦ FiniteItoStoppedVersions.represents_random J R z Y hRep a r hr) GA (fun _ _ ↦ 0) hga
  have hNoise : J.integral UB - J.integral UA = FiniteItoNoise.noise F μ H Y hY R J a b G := by
    rw [← map_sub, FiniteItoIntervalAlgebra.gradient_difference a b hab R Y hY hc G dG hG]
    exact (FiniteItoNoise.noise_eq F μ H Y hY R J a b G (FiniteItoNoise.regular_admissible hG)).symm
  have hN := Lp.coeFn_sub (J.integral UB) (J.integral UA)
  rw [hNoise] at hN
  have hE := FiniteItoIntervalEnergy.energy_difference a b hab R Y hY hc G dG hG
  have hD := (FiniteItoIntervalEnergy.density_integrable R Y hY hG).prod_left_ae
  filter_upwards [hB, hA, hN, hE, hD] with ω hBω hAω hNω hEω hDω
  have hBend : GB H = G b := congrArg G (ClampedAbsoluteContinuity.of_right_le
    (show (a : ℝ) ≤ b by exact_mod_cast hab) (show (b : ℝ) ≤ H by exact_mod_cast hbH))
  have hBzero : GB 0 = G a := congrArg G (ClampedAbsoluteContinuity.of_le_left
    (show (a : ℝ) ≤ b by exact_mod_cast hab) a.coe_nonneg)
  change GB H (YB (H, ω)) = GB 0 (YB (0, ω)) + J.integral UB ω +
    (∫ r, dGB r (YB (r, ω)) ∂timeMeasure H) + (1 / 2 : ℝ) *
      FiniteItoQuadraticTerms.energy (fun i ↦ stop F μ H b (R i)) YB GB ω at hBω
  rw [hBend, hBzero] at hBω
  have hYBend : YB (H, ω) = Y (b, ω) := by
    simp only [YB, FiniteItoStoppedVersions.stopped, min_eq_right hbH]
  have hYBzero : YB (0, ω) = Y (0, ω) := by
    simp only [YB, FiniteItoStoppedVersions.stopped, min_eq_left (show (0 : ℝ≥0) ≤ b from zero_le)]
  rw [hYBend, hYBzero] at hBω
  have hYAend : YA (H, ω) = Y (a, ω) := by
    simp only [YA, FiniteItoStoppedVersions.stopped, min_eq_right (hab.trans hbH)]
  have hYAzero : YA (0, ω) = Y (0, ω) := by
    simp only [YA, FiniteItoStoppedVersions.stopped, min_eq_left (show (0 : ℝ≥0) ≤ a from zero_le)]
  change G a (YA (H, ω)) = G a (YA (0, ω)) + J.integral UA ω + (∫ _r, (0 : ℝ) ∂timeMeasure H) +
    (1 / 2 : ℝ) * FiniteItoQuadraticTerms.energy (fun i ↦ stop F μ H a (R i)) YA GA ω at hAω
  rw [hYAend, hYAzero] at hAω
  change G a (Y (a, ω)) = G a (Y (0, ω)) + J.integral UA ω + (∫ _r, (0 : ℝ) ∂timeMeasure H) +
    (1 / 2 : ℝ) * FiniteItoQuadraticTerms.energy (fun i ↦ stop F μ H a (R i)) YA GA ω at hAω
  simp only [integral_zero, add_zero] at hAω
  rw [FiniteItoIntervalTime.integral_eq H a b dG Y ω] at hBω
  have hDr := FiniteItoIntervalTime.integrable_derivative H a b G dG hG (fun r ↦ Y (r, ω)) (hc ω)
  have hclock := FiniteItoTimeCalculus.clock_cell H a b hab hbH
    (fun r : ℝ ↦ dG r (Y (r.toNNReal, ω)) + (1 / 2 : ℝ) *
      GaussianTaylorAverage.covarianceAction (StandardFiniteIto.rowCovariance F μ H R ω r)
        (GaussianTaylor.hessian (G r) (Y (r.toNNReal, ω))))
  have hcomb : (∫ r in (a : ℝ)..(b : ℝ), dG r (Y (r.toNNReal, ω)) + (1 / 2 : ℝ) *
      GaussianTaylorAverage.covarianceAction (StandardFiniteIto.rowCovariance F μ H R ω r)
        (GaussianTaylor.hessian (G r) (Y (r.toNNReal, ω)))) =
      (∫ r, (Ioc a b).indicator (fun r ↦ dG r (Y (r, ω))) r ∂timeMeasure H) +
        (1 / 2 : ℝ) * ∫ r, (Ioc a b).indicator
          (fun r ↦ FiniteItoIntervalEnergy.density R Y G (r, ω)) r ∂timeMeasure H := by
    rw [← hclock, ← timeMeasure_eq]
    have he : (fun r : ℝ≥0 ↦ (Ioc a b).indicator (fun r : ℝ≥0 ↦
        dG r (Y ((r : ℝ).toNNReal, ω)) + (1 / 2 : ℝ) *
          GaussianTaylorAverage.covarianceAction (StandardFiniteIto.rowCovariance F μ H R ω r)
            (GaussianTaylor.hessian (G r) (Y ((r : ℝ).toNNReal, ω)))) r) =
        (fun r ↦ (Ioc a b).indicator (fun r ↦ dG r (Y (r, ω))) r +
          (1 / 2 : ℝ) * (Ioc a b).indicator
            (fun r ↦ FiniteItoIntervalEnergy.density R Y G (r, ω)) r) := by
      funext r
      by_cases hr : r ∈ Ioc a b
      · simp only [Set.indicator_of_mem hr, Real.toNNReal_coe]
        have hcov : SHE.StandardFiniteIto.rowCovariance F μ H R ω (r : ℝ) =
            (fun i j ↦ inner ℝ (R i (r, ω)) (R j (r, ω)) : Matrix (Fin n) (Fin n) ℝ) := by
          funext i j
          change inner ℝ (R i ((r : ℝ).toNNReal, ω)) (R j ((r : ℝ).toNNReal, ω)) = _
          rw [Real.toNNReal_coe]
        rw [hcov]
        rfl
      · simp only [Set.indicator_of_notMem hr, mul_zero, add_zero]
    rw [he, integral_add hDr ((hDω.indicator measurableSet_Ioc).const_mul (1 / 2 : ℝ)), integral_const_mul]
  change FiniteItoNoise.noise F μ H Y hY R J a b G ω = J.integral UB ω - J.integral UA ω at hNω
  rw [hcomb]
  linarith

/-- The deterministic-initial interface is retained as a specialization. -/
theorem formula (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    (R : Fin n → Process (E := C) F μ H) (z : State n)
    (Y : ℝ≥0 × Ω → State n) (hY : StronglyMeasurable[F.predictable] Y)
    (hc : ∀ ω, Continuous (fun t ↦ Y (t, ω)))
    (hRep : ∀ t : ℝ≥0, t ≤ H → (fun ω ↦ Y (t, ω)) =ᵐ[μ]
      StandardFiniteIto.vectorIntegral F μ H (FiniteCylindricalIto.terminalIto P.toCoordinates e) z R t)
    (a b : ℝ≥0) (hab : a ≤ b) (hbH : b ≤ H)
    (G dG : ℝ → State n → ℝ) (hG : RegularTest (a : ℝ) (b : ℝ) G dG) :
    ∀ᵐ ω ∂μ, G b (Y (b, ω)) = G a (Y (a, ω)) +
      FiniteItoNoise.noise F μ H Y hY R (FiniteCylindricalIto.terminalIto P.toCoordinates e) a b G ω +
      ∫ r in (a : ℝ)..(b : ℝ), dG r (Y (r.toNNReal, ω)) + (1 / 2 : ℝ) *
        GaussianTaylorAverage.covarianceAction (StandardFiniteIto.rowCovariance F μ H R ω r)
          (GaussianTaylor.hessian (G r) (Y (r.toNNReal, ω))) := by
  exact formula_random P e R (fun _ ↦ z) Y hY hc hRep a b hab hbH G dG hG

end SHEStochastic.NativeFiniteItoInterval
