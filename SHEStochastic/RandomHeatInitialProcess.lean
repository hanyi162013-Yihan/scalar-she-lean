module

public import SHE.HeatInitialProcess
public import SHE.ContinuousPredictable
public import Mathlib.MeasureTheory.Function.LpSeminorm.Prod
public import Mathlib.MeasureTheory.Measure.SeparableMeasure

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 700000
noncomputable section

namespace SHEStochastic.RandomHeatInitialProcess
open MeasureTheory SHE SHE.PredictableL2 SHE.DyadicApproximation AddCircle
open scoped NNReal ENNReal

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩
local instance : SecondCountableTopology RealL2 := inferInstanceAs
  (SecondCountableTopology (Lp ℝ 2 (haarAddCircle (T := (1 : ℝ)))))
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩

variable {Ω : Type*} [MeasurableSpace Ω]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (speed : ℝ) (Z : Ω → RealL2) (hZ₀ : StronglyMeasurable[F 0] Z) (hZ : MemLp Z 2 μ)

def function (p : ℝ≥0 × Ω) : RealL2 := RealHeat.realHeat (speed * p.1) (Z p.2)

include hZ₀ in
theorem predictable : StronglyMeasurable[F.predictable] (function speed Z) := by
  have ha : StronglyAdapted F (fun _ : ℝ≥0 ↦ Z) := by
    intro t
    exact hZ₀.mono (F.mono (show (0 : ℝ≥0) ≤ t from zero_le))
  have hs : StronglyMeasurable[F.predictable] (fun p : ℝ≥0 × Ω ↦ Z p.2) :=
    ContinuousPredictable.stronglyMeasurable F (fun _ sample ↦ Z sample)
      ha (fun _ ↦ continuous_const)
  have ht : StronglyMeasurable[F.predictable] (fun p : ℝ≥0 × Ω ↦ speed * (p.1 : ℝ)) :=
    ((PredictableClock.real_time_measurable F).const_mul speed).stronglyMeasurable
  have hh := RealHeat.continuous_realHeat_action.comp_stronglyMeasurable (ht.prodMk hs)
  convert hh using 1 <;> rfl

theorem continuous_paths (sample : Ω) : Continuous (fun t : ℝ≥0 ↦ function speed Z (t, sample)) := by
  have ht : Continuous (fun t : ℝ≥0 ↦ (speed * (t : ℝ), Z sample)) :=
    (continuous_const.mul continuous_subtype_val).prodMk continuous_const
  convert RealHeat.continuous_realHeat_action.comp ht using 1 <;> rfl

include hZ₀ hZ in
theorem memLp : @MemLp _ _ F.predictable _ _ (function speed Z) 2
    ((energyMeasure μ H).trim (predictable_le_product F)) := by
  have hp := predictable F speed Z hZ₀
  haveI : IsFiniteMeasure (timeMeasure H) := inferInstance
  have hd : MemLp (fun p : ℝ≥0 × Ω ↦ Z p.2) 2 (energyMeasure μ H) := hZ.comp_snd (timeMeasure H)
  have hm : MemLp (function speed Z) 2 (energyMeasure μ H) :=
    hd.mono (hp.mono (predictable_le_product F)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun p ↦ RealHeat.realHeat_contraction _ _)
  exact (le_of_eq (eLpNorm_trim (predictable_le_product F) hp)).trans_lt hm

/-- Square-integrable random initial data measurable at time zero give
the genuine predictable L2 heat forcing used by the existing Picard
construction. This retains arbitrary L2 initial data, with no L∞ premise. -/
def process : Process (E := RealL2) F μ H :=
  (memLp F μ H speed Z hZ₀ hZ).toLp (function speed Z)

theorem process_ae : process F μ H speed Z hZ₀ hZ =ᵐ[energyMeasure μ H] function speed Z :=
  ae_eq_of_ae_eq_trim (memLp F μ H speed Z hZ₀ hZ).coeFn_toLp

end SHEStochastic.RandomHeatInitialProcess
