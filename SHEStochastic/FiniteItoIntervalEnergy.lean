module

public import SHEStochastic.FiniteItoIntervalAlgebra
public import SHEStochastic.FiniteItoQuadraticTerms
public import SHEStochastic.FiniteItoTimeCalculus

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
noncomputable section

namespace SHEStochastic.FiniteItoIntervalEnergy
open MeasureTheory ProbabilityTheory Set SHE SHE.PredictableL2 SHE.GaussianItoTest SHE.StoppedItoInputs
open scoped NNReal ENNReal Topology

variable {Ω C : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {H : ℝ≥0} {n : ℕ}

def density (R : Fin n → Process (E := C) F μ H) (Y : ℝ≥0 × Ω → State n)
    (G : ℝ → State n → ℝ) (p : ℝ≥0 × Ω) : ℝ :=
  GaussianTaylorAverage.covarianceAction (fun i j ↦ inner ℝ (R i p) (R j p))
    (GaussianTaylor.hessian (G p.1) (Y p))

theorem density_integrable (R : Fin n → Process (E := C) F μ H)
    (Y : ℝ≥0 × Ω → State n) (hY : StronglyMeasurable[F.predictable] Y)
    {a b : ℝ} {G dG : ℝ → State n → ℝ} (hG : RegularTest a b G dG) :
    Integrable (density R Y G) (energyMeasure μ H) := by
  obtain ⟨B, hB, hb⟩ := FiniteItoWeights.hessian_bound Y hG
  have hs : Integrable (fun p : ℝ≥0 × Ω ↦ ∑ i : Fin n, ∑ j : Fin n,
      FiniteItoWeights.hessian Y G i j p.1 p.2 * inner ℝ (R i p) (R j p)) (energyMeasure μ H) :=
    integrable_finsetSum _ (fun i hi ↦ integrable_finsetSum _ (fun j hj ↦
      FiniteItoQuadraticTerms.product_integrable (R i) (R j) (FiniteItoWeights.hessian Y G i j)
        (FiniteItoWeights.hessian_predictable Y hY hG i j) B (hb i j)))
  refine hs.congr (Filter.Eventually.of_forall fun p ↦ ?_)
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  exact mul_comm _ _

/-- The covariance density of a stopped row is its literal strict-time
indicator times the original Gram density at the stopped state. -/
theorem stopped_density_ae (t : ℝ≥0) (R : Fin n → Process (E := C) F μ H)
    (Y : ℝ≥0 × Ω → State n) (G : ℝ → State n → ℝ) :
    density (fun i ↦ stop F μ H t (R i)) (FiniteItoStoppedVersions.stopped Y t) G =ᵐ[energyMeasure μ H]
      (fun p ↦ if p.1 < t then GaussianTaylorAverage.covarianceAction
        (fun i j ↦ inner ℝ (R i p) (R j p))
        (GaussianTaylor.hessian (G p.1) (Y (min p.1 t, p.2))) else 0) := by
  filter_upwards [ae_all_iff.mpr (fun i : Fin n ↦ stop_ae F μ H t (R i))] with p hp
  by_cases ht : p.1 < t
  · have hr (i : Fin n) : stop F μ H t (R i) p = R i p := by
      rw [hp i, Set.indicator_of_mem (show p ∈ before (Ω := Ω) t from by exact_mod_cast ht)]
    simp only [density, GaussianTaylorAverage.covarianceAction, FiniteItoStoppedVersions.stopped,
      hr, ht, ite_true]
  · have hr (i : Fin n) : stop F μ H t (R i) p = 0 := by
      rw [hp i, Set.indicator_of_notMem (show p ∉ before (Ω := Ω) t from by exact_mod_cast ht)]
    simp only [density, GaussianTaylorAverage.covarianceAction, hr, ht, ite_false,
      inner_zero_left, zero_mul, Finset.sum_const_zero]

theorem density_difference (a b : ℝ≥0) (hab : a ≤ b)
    (R : Fin n → Process (E := C) F μ H) (Y : ℝ≥0 × Ω → State n)
    (G : ℝ → State n → ℝ) :
    (fun p ↦ density (fun i ↦ stop F μ H b (R i)) (FiniteItoStoppedVersions.stopped Y b)
        (FiniteItoTestExtension.value a b G) p -
      density (fun i ↦ stop F μ H a (R i)) (FiniteItoStoppedVersions.stopped Y a)
        (FiniteItoTestExtension.constant G a) p) =ᵐ[energyMeasure μ H]
      (fun p ↦ (if p.1 < b then density R Y G p else 0) -
        (if p.1 < a then density R Y G p else 0)) := by
  filter_upwards [stopped_density_ae b R Y (FiniteItoTestExtension.value a b G),
    stopped_density_ae a R Y (FiniteItoTestExtension.constant G a)] with p hB hA
  rw [hB, hA]
  have hj := FiniteItoIntervalAlgebra.jet_difference a b hab
    (fun r z ↦ GaussianTaylorAverage.covarianceAction (fun i j ↦ inner ℝ (R i p) (R j p))
      (GaussianTaylor.hessian (G r) z)) Y p
  simpa only [FiniteItoTestExtension.value, FiniteItoTestExtension.constant, density] using hj

/-- Covariance energies subtract to the ordinary original row energy
on the requested interval. All densities are proved integrable first. -/
theorem energy_difference (a b : ℝ≥0) (hab : a ≤ b)
    (R : Fin n → Process (E := C) F μ H) (Y : ℝ≥0 × Ω → State n)
    (hY : StronglyMeasurable[F.predictable] Y) (hc : ∀ ω, Continuous (fun r ↦ Y (r, ω)))
    (G dG : ℝ → State n → ℝ) (hG : RegularTest (a : ℝ) (b : ℝ) G dG) :
    (fun ω ↦ FiniteItoQuadraticTerms.energy (fun i ↦ stop F μ H b (R i))
        (FiniteItoStoppedVersions.stopped Y b) (FiniteItoTestExtension.value a b G) ω -
      FiniteItoQuadraticTerms.energy (fun i ↦ stop F μ H a (R i))
        (FiniteItoStoppedVersions.stopped Y a) (FiniteItoTestExtension.constant G a) ω) =ᵐ[μ]
      (fun ω ↦ ∫ r, (Set.Ioc a b).indicator (fun r ↦ density R Y G (r, ω)) r ∂timeMeasure H) := by
  let DB := density (fun i ↦ stop F μ H b (R i)) (FiniteItoStoppedVersions.stopped Y b)
    (FiniteItoTestExtension.value a b G)
  let DA := density (fun i ↦ stop F μ H a (R i)) (FiniteItoStoppedVersions.stopped Y a)
    (FiniteItoTestExtension.constant G a)
  have hDB := density_integrable (fun i ↦ stop F μ H b (R i)) (FiniteItoStoppedVersions.stopped Y b)
    (FiniteItoStoppedVersions.predictable Y hY hc b)
    (FiniteItoTestExtension.regular (by exact_mod_cast hab) hG H)
  have hDA := density_integrable (fun i ↦ stop F μ H a (R i)) (FiniteItoStoppedVersions.stopped Y a)
    (FiniteItoStoppedVersions.predictable Y hY hc a) (FiniteItoTestExtension.constant_regular hG a H)
  have hp := (Measure.measurePreserving_swap (μ := μ) (ν := timeMeasure H)).quasiMeasurePreserving.ae
    (density_difference a b hab R Y G)
  filter_upwards [hDB.prod_left_ae, hDA.prod_left_ae, (density_integrable R Y hY hG).prod_left_ae,
    Measure.ae_ae_of_ae_prod hp] with ω hBω hAω h0ω hω
  change (∫ r, DB (r, ω) ∂timeMeasure H) - (∫ r, DA (r, ω) ∂timeMeasure H) = _
  rw [← integral_sub hBω hAω]
  have he : (fun r ↦ DB (r, ω) - DA (r, ω)) =ᵐ[timeMeasure H]
      (fun r ↦ (Iio b).indicator (fun r ↦ density R Y G (r, ω)) r -
        (Iio a).indicator (fun r ↦ density R Y G (r, ω)) r) := by
    filter_upwards [hω] with r hr
    simpa only [Prod.swap, Set.indicator_apply, Set.mem_Iio] using hr
  rw [integral_congr_ae he,
    integral_sub (h0ω.indicator measurableSet_Iio) (h0ω.indicator measurableSet_Iio)]
  exact SimplePrimitivePairing.primitive_sub (timeMeasure H) (fun r ↦ density R Y G (r, ω)) h0ω a b hab

end SHEStochastic.FiniteItoIntervalEnergy
