module

public import SHEStochastic.HilbertTerminalIto

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
noncomputable section

namespace SHEStochastic.HilbertIntegralUniqueness
open MeasureTheory SHE SHE.PredictableL2 SHE.HilbertColumns
open scoped NNReal ENNReal

/-- Compatible scalar observations determine the entire Hilbert-valued
terminal integral. This transfers estimates to every compatible integral,
not only the representative used to construct the Hilbert lift. -/
theorem integral_eq {Ω κ E : Type*} [MeasurableSpace Ω] [Countable κ]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {μ : Measure Ω} (b : HilbertBasis κ ℝ E) (f g : Lp E 2 μ)
    (hcoord : ∀ j : κ, ((innerSL ℝ (b j)).compLpL 2 μ) f =
      ((innerSL ℝ (b j)).compLpL 2 μ) g) : f = g := by
  have he (j : κ) : (fun ω ↦ innerSL ℝ (b j) (f ω)) =ᵐ[μ]
      (fun ω ↦ innerSL ℝ (b j) (g ω)) := by
    have hi := (innerSL ℝ (b j)).coeFn_compLpL f
    have hk := (innerSL ℝ (b j)).coeFn_compLpL g
    rw [hcoord j] at hi
    exact hi.symm.trans hk
  apply Lp.ext
  filter_upwards [ae_all_iff.mpr he] with ω hω
  apply b.repr.injective
  apply lp.ext
  funext j
  simpa only [HilbertBasis.repr_apply_apply, innerSL_apply_apply] using hω j

end SHEStochastic.HilbertIntegralUniqueness
