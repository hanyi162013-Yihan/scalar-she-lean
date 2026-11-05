module

public import SHEStochastic.NativeWeightedQuadraticVariation
public import SHEStochastic.L2ProductLimit
public import SHEStochastic.FiniteItoStoppedVersions

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
noncomputable section

namespace SHEStochastic.NativeUnweightedQuadraticVariation
open MeasureTheory ProbabilityTheory SHE SHE.PredictableL2 Filter
open MathFin.QuadraticVariationL2
open scoped NNReal ENNReal Topology

variable {Ω C ι : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {H : ℝ≥0}

/-- For constant weights the energy sum telescopes exactly. -/
theorem energy_sum (u : Process (E := C) F μ H) (n : ℕ) (hn : 0 < n) :
    NativeWeightedEnergy.sum u (fun _ _ ↦ 1) n =ᵐ[μ]
      StochasticExponential.bracket F μ H u := by
  have hE := PredictableBracket.stopped_eq u H
  rw [FiniteItoStoppedVersions.stop_horizon] at hE
  filter_upwards [hE] with ω he
  dsimp only [NativeWeightedEnergy.sum]
  simp only [one_mul]
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ ↦ PredictableBracket.energy u (unifPart H n (i+1)) ω-
    PredictableBracket.energy u (unifPart H n i) ω),
    Finset.sum_range_sub (fun i ↦ PredictableBracket.energy u (unifPart H n i) ω)]
  have hn0 : (n : ℝ≥0) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  simpa [unifPart, hn0, PredictableBracket.energy] using he.symm

/-- Every fixed L² pairing of the quadratic fluctuation tends to zero. -/
theorem pairing_limit (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    (u : Process (E := C) F μ H) (M : ℝ≥0)
    (hu : ∀ᵐ x ∂FiniteScalarIto.inputMeasure F μ H, ‖u x‖ ≤ M)
    (f : Ω → ℝ) (hf : MemLp f 2 μ) :
    Tendsto (fun n ↦ ∫ ω, f ω*NativeQuadraticFluctuation.fluctuation P e u (fun _ _ ↦ 1) n ω ∂μ)
      atTop (𝓝 0) := by
  exact L2ProductLimit.integral_mul hf _
    (NativeQuadraticFluctuation.memLp_fluctuation P e u M hu (fun _ _ ↦ 1)
      (fun _ ↦ stronglyMeasurable_const) 1 (by norm_num) (fun _ _ ↦ by norm_num))
    (NativeQuadraticFluctuation.tendsto_mean_square P e u M hu (fun _ _ ↦ 1)
      (fun _ ↦ stronglyMeasurable_const) 1 (by norm_num) (fun _ _ ↦ by norm_num))

end SHEStochastic.NativeUnweightedQuadraticVariation
