module

public import SHEStochastic.MatrixHeatedFactor
public import SHEStochastic.MatrixHaarParameterAction
public import SHE.PredictableClock

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section

namespace SHEStochastic.MatrixHaarKernel
open MeasureTheory SHE SHE.FiniteHaar MatrixInfiniteHaar
open scoped NNReal ENNReal Topology
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
variable {d Z : Type*} [Fintype d] [DecidableEq d] [MeasurableSpace Z]
local notation "μ" => AddCircle.haarAddCircle (T := (1 : ℝ))
abbrev Columns := HilbertColumns.Space (d × HaarNode) (Physical (d := d))
local instance : SecondCountableTopology (Physical (d := d)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (Physical (d := d)) := borel _
local instance : BorelSpace (Physical (d := d)) := ⟨rfl⟩
local instance : MeasurableSpace (Input (d := d)) := borel _
local instance : BorelSpace (Input (d := d)) := ⟨rfl⟩
local instance : MeasurableSpace (Columns (d := d)) := borel _
local instance : BorelSpace (Columns (d := d)) := ⟨rfl⟩

def kernel (t : ℝ) (P : Profile d) : Columns (d := d) :=
  if ht : 0 < t then MatrixHeatedFactor.columns ht P else 0

theorem column (t : ℝ) (P : Profile d) (k : d × HaarNode) :
    kernel t P k = if 0 < t then VectorHeat.heat t (factor P (lp.single 2 k 1)) else 0 := by
  unfold kernel
  split_ifs <;> rfl

theorem norm_sq {t : ℝ} (ht : 0 < t) (P : Profile d) :
    ‖kernel t P‖ ^ 2 ≤ (Fintype.card d : ℝ) * P.upper *
      (1 + 2 * HeatTrace.fractionalGaussianIntegral 0 * t ^ (-(1/2 : ℝ))) := by
  rw [kernel, dif_pos ht]
  exact MatrixHeatedFactor.columns_bound ht P

theorem factor_measurable (Q : Z → Profile d)
    (hQ : Measurable (fun z : Z × AddCircle (1 : ℝ) => (Q z.1).value z.2))
    (u : Z → Input (d := d)) (hu : Measurable u) :
    Measurable (fun z => factor (Q z) (u z)) := by
  exact MatrixFieldParameterAction.action (fun z x => (Q z).value x) hQ
    (fun z => (Q z).measurable) (fun z => (Q z).bound) (fun z => (Q z).norm_bound)
    (fun z => MatrixInfiniteHaar.synthesis (Q z) (u z)) (MatrixHaarParameterAction.synthesis Q hQ u hu)

/-- Jointly measurable covariance profiles give actual measurable
Hilbert--Schmidt heat kernels. No measurable-factor hypothesis remains. -/
theorem measurable (τ : Z → ℝ) (hτ : Measurable τ) (Q : Z → Profile d)
    (hQ : Measurable (fun z : Z × AddCircle (1 : ℝ) => (Q z.1).value z.2)) :
    Measurable (fun z => kernel (τ z) (Q z)) := by
  apply HilbertColumns.measurable_of_columns
  intro k
  have hf := factor_measurable Q hQ (fun _ => lp.single 2 k 1) measurable_const
  have hh := VectorHeat.continuous_action.measurable.comp (hτ.prodMk hf)
  have hi : Measurable (fun z : Z => if 0 < τ z then
      VectorHeat.heat (τ z) (factor (Q z) (lp.single 2 k 1)) else (0 : Physical (d := d))) :=
    hh.ite (measurableSet_lt measurable_const hτ) measurable_const
  simpa only [column] using hi

/-- The same concrete kernel is predictable in time/probability as
soon as the covariance field is jointly predictable with space. -/
theorem predictable {Ω : Type*} [MeasurableSpace Ω] (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (Q : ℝ≥0 × Ω → Profile d)
    (hQ : @Measurable ((ℝ≥0 × Ω) × AddCircle (1 : ℝ)) (Matrix d d ℝ)
      (F.predictable.prod inferInstance) inferInstance (fun z => (Q z.1).value z.2)) (t : ℝ) :
    StronglyMeasurable[F.predictable] (fun p : ℝ≥0 × Ω => kernel (t - (p.1 : ℝ)) (Q p)) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  have ht : Measurable (fun p : ℝ≥0 × Ω => t - (p.1 : ℝ)) :=
    measurable_const.sub (PredictableClock.real_time_measurable F)
  exact (measurable _ ht Q hQ).stronglyMeasurable

end SHEStochastic.MatrixHaarKernel
