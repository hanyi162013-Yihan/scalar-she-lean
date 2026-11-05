module

public import SHE.HeatFieldWeightedLimit

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section

namespace SHE.HeatFieldMovingWeight
open Set MeasureTheory AddCircle StoppedFourier NativeHeatObservation Filter Topology
open DyadicApproximation HeatFieldApproximation HeatFieldWeightedLimit
local instance heatFieldMovingWeight_periodPositive : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local instance heatFieldMovingWeight_realSigma : MeasurableSpace RealL2 := borel _
local instance heatFieldMovingWeight_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance heatFieldMovingWeight_nativeSigma : MeasurableSpace CircleL2 := borel _
local instance heatFieldMovingWeight_nativeBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable {P : Type*} [MeasurableSpace P]

/-- A moving bounded Borel weight need not converge at all. A uniform
bound suffices to remove the coefficient heat regularization in full L¹. -/
theorem integrated_mass_tendsto_zero (U : P → RealL2) (hU : Measurable U)
    (A : ℝ → ℝ) (hA : Measurable A) (D : ℝ → P × HeatCircle → ℝ)
    (hD : ∀ ε,Measurable (D ε)) (ν : Measure P) [IsFiniteMeasure ν]
    {M C L : ℝ} (hM : ∀ z,|A z| ≤ M) (hC : 0 ≤ C)
    (hDb : ∀ ε p,|D ε p| ≤ C) (hL : 0 ≤ L) (hLip : ∀ z w,|A z-A w| ≤ L*|z-w|) :
    Tendsto (fun ε => ∫ p,HeatFieldWeightedLimit.mass U A (D ε) ε p ∂ν)
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
  have ht (p : P) : Tendsto (fun ε => HeatFieldWeightedLimit.mass U A (D ε) ε p)
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have he := (tendsto_const_nhds (x := C)).mul (error_tendsto_zero U p hM hL hLip)
    simp only [mul_zero] at he
    exact squeeze_zero' (Filter.Eventually.of_forall (fun ε => mass_nonneg U A (D ε) ε p))
      (Filter.Eventually.of_forall (fun ε => mass_le_error U hU A hA (D ε) hM hC (hDb ε) ε p)) he
  have hi := tendsto_integral_filter_of_dominated_convergence (μ := ν) (fun _ : P => 2*M*C)
    (Filter.Eventually.of_forall (fun ε => (mass_measurable U hU A hA (D ε) (hD ε) ε).aestronglyMeasurable))
    (Filter.Eventually.of_forall (fun ε => Filter.Eventually.of_forall (fun p => by
      rw [Real.norm_eq_abs,abs_of_nonneg (mass_nonneg U A (D ε) ε p)]
      exact mass_bound U A (D ε) hM hC (hDb ε) ε p))) (integrable_const _)
    (Filter.Eventually.of_forall ht)
  simpa only [integral_zero] using hi

end SHE.HeatFieldMovingWeight
