module

public import SHEStochastic.VectorHeatInitialProcess
public import SHE.ContinuousPredictable
public import Mathlib.MeasureTheory.Function.LpSeminorm.Prod

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section

namespace SHEStochastic.RandomVectorHeatInitialProcess
open MeasureTheory SHE SHE.PredictableL2 MatrixInfiniteHaar
open scoped NNReal ENNReal
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
variable {d Ω : Type*} [Fintype d] [DecidableEq d] [MeasurableSpace Ω]
local instance : SecondCountableTopology (Physical (d := d)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (Physical (d := d)) := borel _
local instance : BorelSpace (Physical (d := d)) := ⟨rfl⟩
variable (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (H : ℝ≥0) (Z : Ω → Physical (d := d))
    (hZ₀ : StronglyMeasurable[F 0] Z) (hZ : MemLp Z 2 μ)

/-- The vector heat semigroup applied to the original random L2 state. -/
def function (p : ℝ≥0 × Ω) : Physical (d := d) := VectorAnalyticHeat.heat p.1 (Z p.2)

include hZ₀ in
theorem predictable : StronglyMeasurable[F.predictable] (function Z) := by
  have ha : StronglyAdapted F (fun _ : ℝ≥0 => Z) := fun t =>
    hZ₀.mono (F.mono (show (0 : ℝ≥0) ≤ t from zero_le))
  have hs : StronglyMeasurable[F.predictable] (fun p : ℝ≥0 × Ω => Z p.2) :=
    ContinuousPredictable.stronglyMeasurable F (fun _ ω => Z ω) ha (fun _ => continuous_const)
  have ht : StronglyMeasurable[F.predictable]
      (fun p : ℝ≥0 × Ω => ((p.1 : ℝ)/NativeHeatObservation.timeScale, Z p.2)) :=
    (((PredictableClock.real_time_measurable F).div_const NativeHeatObservation.timeScale).stronglyMeasurable.prodMk hs)
  exact Continuous.comp_stronglyMeasurable
    (g := fun p : ℝ × Physical (d := d) => VectorHeat.heat p.1 p.2)
    (f := fun p : ℝ≥0 × Ω => ((p.1 : ℝ)/NativeHeatObservation.timeScale, Z p.2))
    VectorHeat.continuous_action ht

theorem continuous_paths (ω : Ω) : Continuous (fun t : ℝ≥0 => function Z (t,ω)) := by
  have hi : Continuous (fun t : ℝ≥0 => ((t : ℝ)/NativeHeatObservation.timeScale,Z ω)) :=
    (NNReal.continuous_coe.div_const _).prodMk continuous_const
  exact Continuous.comp (f := fun t : ℝ≥0 => ((t : ℝ)/NativeHeatObservation.timeScale,Z ω))
    (g := fun p : ℝ × Physical (d := d) => VectorHeat.heat p.1 p.2) VectorHeat.continuous_action hi

include hZ₀ hZ in
theorem memLp : @MemLp _ _ F.predictable _ _ (function Z) 2
    ((energyMeasure μ H).trim (predictable_le_product F)) := by
  have hp := predictable F Z hZ₀
  have hd : MemLp (fun p : ℝ≥0 × Ω => Z p.2) 2 (energyMeasure μ H) := hZ.comp_snd (timeMeasure H)
  have hm : MemLp (function Z) 2 (energyMeasure μ H) :=
    hd.mono (hp.mono (predictable_le_product F)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => VectorAnalyticHeat.contraction p.1 (Z p.2))
  exact (le_of_eq (eLpNorm_trim (predictable_le_product F) hp)).trans_lt hm

/-- No boundedness or higher initial moment is imposed. -/
def process : Process (E := Physical (d := d)) F μ H :=
  (memLp F μ H Z hZ₀ hZ).toLp (function Z)

theorem process_ae : process F μ H Z hZ₀ hZ =ᵐ[energyMeasure μ H] function Z :=
  ae_eq_of_ae_eq_trim (memLp F μ H Z hZ₀ hZ).coeFn_toLp

end SHEStochastic.RandomVectorHeatInitialProcess
