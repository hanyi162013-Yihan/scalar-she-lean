module

public import SHE.HilbertBandTails

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace SHE.HilbertBandTails
open Set Filter MeasureTheory Real PredictableL2
open scoped ENNReal
variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- The actual finite-frequency truncations converge in the global
L2 space, with the same geometric cutoff error as the true series tail. -/
theorem cutoff_error (μ : Measure X) (F : ℕ→X→E) (hF : ∀ j,Measurable (F j))
    (hi : ∀ j,Integrable (fun x=>‖F j x‖^2) μ) {γ A : ℝ} (hγ : 0<γ) (hA : 0≤A)
    (hb : ∀ j,(∫ x,‖F j x‖^2 ∂μ)≤A^2*((2:ℝ)^j)^(-2*γ)) :
    Tendsto (fun J=>∑ j∈Finset.range J,vector μ F hF hi j) atTop (nhds (∑' j,vector μ F hF hi j)) ∧
      ∀ J : ℕ,‖(∑' j,vector μ F hF hi j)-(∑ j∈Finset.range J,vector μ F hF hi j)‖≤
        A*StateBands.geometricConstant γ*((2:ℝ)^J)^(-γ) := by
  have hs:=dyadic μ F hF hi hγ hA hb
  refine ⟨hs.1.hasSum.tendsto_sum_nat,fun J=>?_⟩
  have he :=hs.1.sum_add_tsum_nat_add J
  have ht : (∑' j,vector μ F hF hi j)-(∑ j∈Finset.range J,vector μ F hF hi j)=
      ∑' n,vector μ F hF hi (n+J):=by rw [←he,add_sub_cancel_left]
  rw [ht]
  exact hs.2 J
end SHE.HilbertBandTails
