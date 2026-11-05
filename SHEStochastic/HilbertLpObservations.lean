module

public import SHEStochastic.HilbertIsometryLift

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.HilbertLpObservations
open MeasureTheory
open scoped ENNReal
variable {Ω E I : Type*} [MeasurableSpace Ω] [Countable I]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (μ : Measure Ω) (b : HilbertBasis I ℝ E)

theorem coordinate (v : Lp E 2 μ) (i : I) :
    HilbertIsometryLift.targetEquiv μ b v i = (innerSL ℝ (b i)).compLpL 2 μ v := by
  change (L2HilbertSum.total μ (ColumnsHilbertSum.unit b)
    (ColumnsHilbertSum.unit_total b)).linearIsometryEquiv v i = _
  rw [L2HilbertSum.coordinate, L2HilbertSum.lift_adjoint μ (ColumnsHilbertSum.unit b) i,
    ColumnsHilbertSum.unit_adjoint]

/-- A complete countable spatial Hilbert basis separates actual random
variables in `L²`, so scalar native transport determines the vector integral. -/
theorem ext (v w : Lp E 2 μ)
    (h : ∀ i, (innerSL ℝ (b i)).compLpL 2 μ v = (innerSL ℝ (b i)).compLpL 2 μ w) : v = w := by
  apply (HilbertIsometryLift.targetEquiv μ b).injective
  apply lp.ext
  funext i
  rw [coordinate, coordinate, h i]

/-- Countably many tested almost-everywhere identities determine an
arbitrary Hilbert-valued random variable, before L2 integrability is known. -/
theorem ae_eq (v w : Ω → E)
    (h : ∀ i, (fun ω => inner ℝ (b i) (v ω)) =ᵐ[μ] fun ω => inner ℝ (b i) (w ω)) :
    v =ᵐ[μ] w := by
  filter_upwards [ae_all_iff.mpr h] with ω hω
  apply b.repr.injective
  apply lp.ext
  funext i
  simpa only [HilbertBasis.repr_apply_apply] using hω i

end SHEStochastic.HilbertLpObservations
