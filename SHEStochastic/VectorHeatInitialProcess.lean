module

public import SHEStochastic.MatrixConstructedPicard

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.VectorHeatInitialProcess
open MeasureTheory SHE SHE.PredictableL2 SHE.FiniteHaar MatrixInfiniteHaar
open scoped NNReal ENNReal Matrix.Norms.L2Operator
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
variable {d Ω : Type*} [Fintype d] [DecidableEq d] [MeasurableSpace Ω]
local instance : SecondCountableTopology (Physical (d := d)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (Physical (d := d)) := borel _
local instance : BorelSpace (Physical (d := d)) := ⟨rfl⟩
variable (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (H : ℝ≥0)

def function (u : Physical (d := d)) (p : ℝ≥0 × Ω) : Physical (d := d) :=
  VectorAnalyticHeat.heat p.1 u

theorem predictable (u : Physical (d := d)) : StronglyMeasurable[F.predictable] (function u (Ω := Ω)) :=
  ((VectorHeat.continuous_action (d := d)).measurable.comp
    (((PredictableClock.real_time_measurable F).div_const NativeHeatObservation.timeScale).prodMk
      measurable_const)).stronglyMeasurable

theorem memLp (u : Physical (d := d)) :
    @MemLp _ _ F.predictable _ _ (function u (Ω := Ω)) 2
      ((energyMeasure μ H).trim (predictable_le_product F)) := by
  have : IsFiniteMeasure (energyMeasure μ H) := by dsimp only [energyMeasure]; infer_instance
  exact MemLp.of_bound (predictable F u).aestronglyMeasurable ‖u‖
    (Filter.Eventually.of_forall (fun p => VectorAnalyticHeat.contraction p.1 u))

def process (u : Physical (d := d)) : Process (E := Physical (d := d)) F μ H :=
  (memLp F μ H u).toLp (function u (Ω := Ω))

theorem process_ae (u : Physical (d := d)) :
    process F μ H u =ᵐ[energyMeasure μ H] function u :=
  ae_eq_of_ae_eq_trim (memLp F μ H u).coeFn_toLp

/-- Arbitrary deterministic vector L2 initial data yield an actual
short-time native predictable mild fixed point for every bounded
globally Lipschitz elliptic matrix coefficient. -/
theorem exists_unique_heat_mild (hH : (H : ℝ) ≤ 1)
    (N : FiniteScalarIto.Family F μ H (d × HaarNode))
    (G : MatrixNonlinearCoefficient.Coefficient d) {L : ℝ} (hL : 0 ≤ L)
    (hLip : ∀ z w, ‖G.value z-G.value w‖ ≤ L*‖z-w‖)
    (hsmall : 2*MatrixNonlinearHeatBounds.constant G L*(H : ℝ)^(1/2 : ℝ) ≤ 1/4)
    (u : Physical (d := d)) :
    ∃! v : Process (E := Physical (d := d)) F μ H,
      v=process F μ H u+MatrixPredictableConvolution.map hH N G v :=
  MatrixConstructedPicard.exists_unique_forced hH N G hL hLip hsmall (process F μ H u)

end SHEStochastic.VectorHeatInitialProcess
