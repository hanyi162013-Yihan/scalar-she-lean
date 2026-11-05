module

public import SHEStochastic.FiniteItoQuadraticTerms
public import SHEStochastic.FiniteItoPathFormula
public import SHEStochastic.FiniteItoTimeCalculus

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
noncomputable section

namespace SHEStochastic.NativeFiniteItoHorizon
open MeasureTheory ProbabilityTheory SHE SHE.PredictableL2 SHE.StoppedItoInputs SHE.GaussianItoTest
open MathFin.QuadraticVariationL2
open scoped NNReal ENNReal Topology

variable {Ω C ι : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {H : ℝ≥0} {n : ℕ}

/-- Native finite-dimensional Itô formula over the full horizon. All
predictable rows may be random and unbounded in L². The gradient term
is the existing scalar integral and the covariance is the original row
Gram. Arbitrary subinterval assembly is a subsequent step. -/
theorem formula_random (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    (R : Fin n → Process (E := C) F μ H) (z : Ω → State n)
    (Y : ℝ≥0 × Ω → State n) (hY : StronglyMeasurable[F.predictable] Y)
    (hc : ∀ ω, Continuous (fun t ↦ Y (t, ω)))
    (hRep : ∀ t : ℝ≥0, t ≤ H → (fun ω ↦ Y (t, ω)) =ᵐ[μ]
      (fun ω ↦ StandardFiniteIto.vectorIntegral F μ H (FiniteCylindricalIto.terminalIto P.toCoordinates e) (z ω) R t ω))
    (G dG : ℝ → State n → ℝ) (hG : RegularTest 0 (H : ℝ) G dG) :
    ∀ᵐ ω ∂μ, G H (Y (H, ω)) = G 0 (Y (0, ω)) +
      (FiniteCylindricalIto.terminalIto P.toCoordinates e).integral
        (FiniteItoNoise.gradientProcess F μ H Y hY R G (FiniteItoNoise.regular_admissible hG)) ω +
      (∫ r, dG r (Y (r, ω)) ∂timeMeasure H) + (1 / 2 : ℝ) * FiniteItoQuadraticTerms.energy R Y G ω := by
  let J := FiniteCylindricalIto.terminalIto P.toCoordinates e
  have hL := FiniteItoStochasticTerms.linearSum_tendstoInMeasure J
    (FiniteCylindricalIto.pastLocality P e) R z Y hY hc hRep hG
  have hQ := FiniteItoQuadraticTerms.tendstoInMeasure P e R z Y hY hc hRep hG
  have hN := FiniteItoQuadraticTerms.normSum_tendstoInMeasure P e R z Y hRep
  obtain ⟨ns, hns, hLa, hQa⟩ := MathFin.exists_subseq_tendsto_ae₂ hL hQ id Filter.tendsto_id
  obtain ⟨ms, hms, hNa⟩ := (hN.comp hns.tendsto_atTop).exists_seq_tendsto_ae
  have hH : Continuous (fun p : ℝ≥0 × State n ↦ GaussianTaylor.hessian (G p.1) p.2) :=
    hG.hessian_continuous.comp ((NNReal.continuous_coe.comp continuous_fst).prodMk continuous_snd)
  filter_upwards [hLa, hQa, hNa] with ω hLω hQω hNω
  let x : ℝ≥0 → State n := fun r ↦ Y (r, ω)
  let ν : ℕ → ℕ := ns ∘ ms
  have hν : Filter.Tendsto ν Filter.atTop Filter.atTop := hns.tendsto_atTop.comp hms.tendsto_atTop
  have htime : Filter.Tendsto (fun k ↦ FiniteItoPathFormula.timeSum H (fun r z ↦ G r z) x (ν k))
      Filter.atTop (𝓝 (∫ r, dG r (Y (r, ω)) ∂timeMeasure H)) := by
    have ht := FiniteItoTimeCalculus.regular_time_sums H G dG hG x (hc ω).continuousOn
    have he (m : ℕ) : FiniteItoPathFormula.timeSum H (fun r z ↦ G r z) x m =
        ∑ k ∈ Finset.range m, (G (unifPart H m (k + 1)) (x (unifPart H m (k + 1))) -
          G (unifPart H m k) (x (unifPart H m (k + 1)))) :=
      Fin.sum_univ_eq_sum_range (fun k : ℕ ↦ G (unifPart H m (k + 1)) (x (unifPart H m (k + 1))) -
        G (unifPart H m k) (x (unifPart H m (k + 1)))) m
    simp_rw [he, timeMeasure_eq]
    exact ht.comp hν
  have hlinear : Filter.Tendsto (fun k ↦ FiniteItoPathFormula.linearSum H (fun r z ↦ G r z) x (ν k))
      Filter.atTop (𝓝 (J.integral (FiniteItoNoise.gradientProcess F μ H Y hY R G
        (FiniteItoNoise.regular_admissible hG)) ω)) := by
    exact hLω.comp hms.tendsto_atTop
  have hquadratic : Filter.Tendsto (fun k ↦ FiniteItoPathFormula.quadraticSum H (fun r z ↦ G r z) x (ν k))
      Filter.atTop (𝓝 (FiniteItoQuadraticTerms.energy R Y G ω)) := by
    exact hQω.comp hms.tendsto_atTop
  have hbound : ∀ᶠ k in Filter.atTop, ∑ j : Fin (ν k),
      ‖x (unifPart H (ν k) (j + 1)) - x (unifPart H (ν k) j)‖ ^ 2 ≤
        (∑ i : Fin n, NativeWeightedEnergy.integral (R i) (fun _ _ ↦ 1) ω) + 1 := by
    filter_upwards [hNω.eventually_lt_const (lt_add_one _)] with k hk
    exact hk.le
  have hh := FiniteItoPathFormula.of_tendsto H (fun r z ↦ G r z) (fun r ↦ hG.state_smooth r) hH
    x (hc ω).continuousOn ν hν htime hlinear hquadratic hbound
  change G H (Y (H, ω)) - G 0 (Y (0, ω)) = _ at hh
  linarith

/-- The deterministic-initial interface is retained as a specialization. -/
theorem formula (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    (R : Fin n → Process (E := C) F μ H) (z : State n)
    (Y : ℝ≥0 × Ω → State n) (hY : StronglyMeasurable[F.predictable] Y)
    (hc : ∀ ω, Continuous (fun t ↦ Y (t, ω)))
    (hRep : ∀ t : ℝ≥0, t ≤ H → (fun ω ↦ Y (t, ω)) =ᵐ[μ]
      StandardFiniteIto.vectorIntegral F μ H (FiniteCylindricalIto.terminalIto P.toCoordinates e) z R t)
    (G dG : ℝ → State n → ℝ) (hG : RegularTest 0 (H : ℝ) G dG) :
    ∀ᵐ ω ∂μ, G H (Y (H, ω)) = G 0 (Y (0, ω)) +
      (FiniteCylindricalIto.terminalIto P.toCoordinates e).integral
        (FiniteItoNoise.gradientProcess F μ H Y hY R G (FiniteItoNoise.regular_admissible hG)) ω +
      (∫ r, dG r (Y (r, ω)) ∂timeMeasure H) + (1 / 2 : ℝ) * FiniteItoQuadraticTerms.energy R Y G ω := by
  exact formula_random P e R (fun _ ↦ z) Y hY hc hRep G dG hG

end SHEStochastic.NativeFiniteItoHorizon
