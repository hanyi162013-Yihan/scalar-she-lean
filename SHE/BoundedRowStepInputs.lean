module
public import SHE.BoundedContinuousRowFreezing
public import SHE.ApproximationCells
public import SHE.PredictableItoCells
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
namespace SHE.BoundedRowStepInputs
open MeasureTheory Set PredictableL2 ApproximationCells
open scoped NNReal ENNReal
variable {Ω E C : Type*} [MeasurableSpace Ω]
variable [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable [NormedAddCommGroup C] [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
variable (H q : ℝ≥0) (R : Iic q×E→C) (hR : Continuous R)
variable (U : ℝ≥0→Ω→E) (hUa : StronglyAdapted 𝓕 U)
variable (M : ℝ) (hb : ∀p,‖R p‖≤M)

def time (n k : ℕ) : ℝ≥0 := min (point n k) q

def coefficient (n k : ℕ) (ω : Ω) : C :=
  R (⟨time q n (k-1),min_le_right _ _⟩,U (time q n (k-1)) ω)

include hR hUa in
theorem coefficient_measurable (n k : ℕ) :
    StronglyMeasurable[𝓕 (time q n (k-1))] (coefficient q R U n k) := by
  have hm : Measurable (fun u:E=>R (⟨time q n (k-1),min_le_right _ _⟩,u)) :=
    hR.measurable.comp (measurable_const.prodMk measurable_id)
  exact (hm.comp (hUa _).measurable).stronglyMeasurable

include hb in
theorem coefficient_bound (n k : ℕ) (ω : Ω) : ‖coefficient q R U n k ω‖≤M := hb _

include hR hUa hb in
theorem coefficient_memLp (n k : ℕ) : MemLp (coefficient q R U n k) 2 μ :=
  MemLp.of_bound ((coefficient_measurable 𝓕 q R hR U hUa n k).mono (𝓕.le _)).aestronglyMeasurable M
    (Filter.Eventually.of_forall (coefficient_bound q R U M hb n k))

def cell (n k : ℕ) : Process (E:=C) 𝓕 μ H :=
  PredictableSteps.process 𝓕 μ H (time q n (k-1)) (time q n k) (coefficient q R U n k)
    (coefficient_measurable 𝓕 q R hR U hUa n k) (coefficient_memLp 𝓕 μ q R hR U hUa M hb n k)

def input (n : ℕ) : Process (E:=C) 𝓕 μ H :=
  ∑k∈Finset.Icc 1 (index n q),cell 𝓕 μ H q R hR U hUa M hb n k

theorem input_ae (n : ℕ) : input 𝓕 μ H q R hR U hUa M hb n=ᵐ[energyMeasure μ H]
    (fun p=>∑k∈Finset.Icc 1 (index n q),PredictableSteps.step (time q n (k-1)) (time q n k)
      (coefficient q R U n k) p) := by
  have hs := ae_eq_of_ae_eq_trim (Lp.coeFn_fun_finsetSum (Finset.Icc 1 (index n q))
    (fun k=>cell 𝓕 μ H q R hR U hUa M hb n k))
  have hc : ∀ᵐp∂energyMeasure μ H,∀k:ℕ,
      cell 𝓕 μ H q R hR U hUa M hb n k p=
        PredictableSteps.step (time q n (k-1)) (time q n k) (coefficient q R U n k) p :=
    ae_all_iff.mpr (fun k=>PredictableSteps.process_ae 𝓕 μ H _ _ _ _ _)
  filter_upwards [hs,hc] with p hs hc
  change (∑k∈Finset.Icc 1 (index n q),cell 𝓕 μ H q R hR U hUa M hb n k) p=_
  rw [hs]
  exact Finset.sum_congr rfl (fun k _=>hc k)
end SHE.BoundedRowStepInputs
