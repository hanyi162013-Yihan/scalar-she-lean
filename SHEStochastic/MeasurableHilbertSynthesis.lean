module

public import SHEStochastic.WeightedRieszSynthesis
public import SHE.HilbertColumns

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHEStochastic.MeasurableHilbertSynthesis
open MeasureTheory
open scoped ENNReal

variable {P ι κ E : Type*} [MeasurableSpace P] [Countable ι] [DecidableEq ι] [Countable κ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

local instance : MeasurableSpace (lp (fun _ : ι => ℝ) 2) := borel _
local instance : BorelSpace (lp (fun _ : ι => ℝ) 2) := ⟨rfl⟩
local instance : MeasurableSpace (lp (fun _ : κ => ℝ) 2) := borel _
local instance : BorelSpace (lp (fun _ : κ => ℝ) 2) := ⟨rfl⟩

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
theorem adjoint_coordinate (S : lp (fun _ : ι => ℝ) 2 →L[ℝ] E) (u : E) (i : ι) :
    S.adjoint u i=inner ℝ (S (lp.single 2 i 1)) u := by
  have hh := ContinuousLinearMap.adjoint_inner_right S (lp.single 2 i 1) u
  simpa only [lp.inner_single_left, RCLike.inner_apply, conj_trivial, one_mul, mul_one] using hh

/-- Strong-operator measurability of the analysis is obtained from
the actual measurable columns, rather than operator-norm separability. -/
theorem adjoint_action (S : P → lp (fun _ : ι => ℝ) 2 →L[ℝ] E)
    (hS : ∀ i, Measurable (fun p => S p (lp.single 2 i 1)))
    (u : P → E) (hu : Measurable u) : Measurable (fun p => (S p).adjoint (u p)) := by
  apply SHE.HilbertColumns.measurable_of_columns
  intro i
  have hh : Measurable (fun p => inner ℝ (S p (lp.single 2 i 1)) (u p)) :=
    continuous_inner.measurable.comp ((hS i).prodMk hu)
  simpa only [adjoint_coordinate] using hh

/-- A countable fixed output basis turns column measurability into
joint measurability of the actual infinite synthesis action. -/
theorem action (e : HilbertBasis κ ℝ E) (S : P → lp (fun _ : ι => ℝ) 2 →L[ℝ] E)
    (hS : ∀ i, Measurable (fun p => S p (lp.single 2 i 1)))
    (z : P → lp (fun _ : ι => ℝ) 2) (hz : Measurable z) : Measurable (fun p => S p (z p)) := by
  have hc : Measurable (fun p => e.repr (S p (z p))) := by
    apply SHE.HilbertColumns.measurable_of_columns
    intro k
    have hh : Measurable (fun p => inner ℝ ((S p).adjoint (e k)) (z p)) :=
      continuous_inner.measurable.comp
        ((adjoint_action S hS (fun _ => e k) measurable_const).prodMk hz)
    have he (p : P) : inner ℝ ((S p).adjoint (e k)) (z p)=e.repr (S p (z p)) k := by
      rw [ContinuousLinearMap.adjoint_inner_left, HilbertBasis.repr_apply_apply]
    simpa only [he] using hh
  have hh := e.repr.symm.continuous.measurable.comp hc
  change Measurable (fun p => e.repr.symm (e.repr (S p (z p)))) at hh
  have he : (fun p => e.repr.symm (e.repr (S p (z p))))=(fun p => S p (z p)) :=
    funext (fun p => e.repr.symm_apply_apply (S p (z p)))
  rwa [he] at hh

end SHEStochastic.MeasurableHilbertSynthesis
