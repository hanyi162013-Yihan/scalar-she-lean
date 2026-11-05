module

public import SHE.FiniteItoNoise
public import SHEStochastic.StochasticRiemannSums
public import SHEStochastic.NativeWeightedCovariation

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
noncomputable section

namespace SHEStochastic.FiniteItoWeights
open MeasureTheory ProbabilityTheory SHE SHE.GaussianItoTest
open scoped NNReal ENNReal Topology

variable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {a b : ℝ}
  {G dG : ℝ → State n → ℝ}

def gradient (Y : ℝ≥0 × Ω → State n) (G : ℝ → State n → ℝ) (i : Fin n)
    (t : ℝ≥0) (ω : Ω) : ℝ := FiniteItoNoise.gradientCoefficient Y G i (t, ω)

def hessian (Y : ℝ≥0 × Ω → State n) (G : ℝ → State n → ℝ) (i j : Fin n)
    (t : ℝ≥0) (ω : Ω) : ℝ := GaussianTaylor.hessian (G t) (Y (t, ω))
      (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j)

variable (Y : ℝ≥0 × Ω → State n) (hY : StronglyMeasurable[F.predictable] Y)
  (hG : RegularTest a b G dG)
include hY hG

theorem gradient_predictable (i : Fin n) :
    IsStronglyPredictable F (gradient Y G i) :=
  FiniteItoNoise.gradientCoefficient_predictable F Y hY (FiniteItoNoise.regular_admissible hG) i

theorem gradient_adapted (i : Fin n) : StronglyAdapted F (gradient Y G i) :=
  (gradient_predictable Y hY hG i).stronglyAdapted

omit hY in
theorem gradient_continuous (hc : ∀ ω, Continuous (fun t ↦ Y (t, ω))) (i : Fin n) (ω : Ω) :
    Continuous (fun t ↦ gradient Y G i t ω) :=
  (hG.gradient_continuous.clm_apply continuous_const).comp (NNReal.continuous_coe.prodMk (hc ω))

omit hY in
theorem gradient_bound : ∃ L : ℝ, 0 ≤ L ∧ ∀ i t ω, |gradient Y G i t ω| ≤ L := by
  obtain ⟨M, L, B, hb⟩ := hG.bounds
  refine ⟨L, (norm_nonneg _).trans (hb 0 0).2.1, ?_⟩
  intro i t ω
  simpa only [Real.norm_eq_abs, gradient] using FiniteItoNoise.gradientCoefficient_bound Y
    (fun t z ↦ (hb t z).2.1) i (t, ω)

theorem hessian_predictable (i j : Fin n) : IsStronglyPredictable F (hessian Y G i j) := by
  have hc := (hG.hessian_continuous.clm_apply
    (continuous_const (y := EuclideanSpace.basisFun (Fin n) ℝ i))).clm_apply
      (continuous_const (y := EuclideanSpace.basisFun (Fin n) ℝ j))
  exact (hc.measurable.comp ((PredictableClock.real_time_measurable F).prodMk hY.measurable)).stronglyMeasurable

theorem hessian_adapted (i j : Fin n) : StronglyAdapted F (hessian Y G i j) :=
  (hessian_predictable Y hY hG i j).stronglyAdapted

omit hY in
theorem hessian_continuous (hc : ∀ ω, Continuous (fun t ↦ Y (t, ω))) (i j : Fin n) (ω : Ω) :
    Continuous (fun t ↦ hessian Y G i j t ω) :=
  ((hG.hessian_continuous.clm_apply continuous_const).clm_apply continuous_const).comp
    (NNReal.continuous_coe.prodMk (hc ω))

omit hY in
theorem hessian_bound : ∃ B : ℝ, 0 ≤ B ∧ ∀ i j t ω, |hessian Y G i j t ω| ≤ B := by
  obtain ⟨M, L, B, hb⟩ := hG.bounds
  refine ⟨B, (norm_nonneg (GaussianTaylor.hessian (G 0) 0)).trans (hb 0 0).2.2, ?_⟩
  intro i j t ω
  have hh : |hessian Y G i j t ω| ≤ ‖GaussianTaylor.hessian (G t) (Y (t, ω))‖ := by
    simpa only [Real.norm_eq_abs, hessian] using
      PositiveMatrixBounds.bilinear_basis_bound (GaussianTaylor.hessian (G t) (Y (t, ω))) i j
  exact hh.trans (hb t (Y (t, ω))).2.2

end SHEStochastic.FiniteItoWeights
