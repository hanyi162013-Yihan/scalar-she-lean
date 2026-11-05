module

public import SHE.HilbertBandApproximation

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace SHE.HilbertBandTails
open Set Filter MeasureTheory Real PredictableL2
open scoped ENNReal BigOperators
variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable (μ : Measure X) (F : ℕ→X→E) (hF : ∀ j,Measurable (F j))
variable (hi : ∀ j,Integrable (fun x=>‖F j x‖^2) μ)
variable (C : ℕ→X→E) (he : ∀ J,C J=ᵐ[μ](fun x=>∑ j∈Finset.range J,F j x))
include hF hi he

theorem cutoff_memLp (J : ℕ) : MemLp (C J) 2 μ :=
  (memLp_finsetSum (Finset.range J) (fun j _=>
    (memLp_two_iff_integrable_sq_norm (hF j).aestronglyMeasurable).mpr (hi j))).ae_eq (he J).symm

def cutoffVector (J : ℕ) : Lp E 2 μ := (cutoff_memLp μ F hF hi C he J).toLp (C J)

theorem cutoffVector_eq (J : ℕ) : cutoffVector μ F hF hi C he J=
    ∑ j∈Finset.range J,vector μ F hF hi j := by
  apply Lp.ext
  have hv (j : ℕ) : vector μ F hF hi j=ᵐ[μ]F j:=
    ((memLp_two_iff_integrable_sq_norm (hF j).aestronglyMeasurable).mpr (hi j)).coeFn_toLp
  filter_upwards [(cutoff_memLp μ F hF hi C he J).coeFn_toLp,he J,
    Lp.coeFn_finsetSum (Finset.range J) (vector μ F hF hi),ae_all_iff.2 hv] with x hc hx hs hvec
  change cutoffVector μ F hF hi C he J x=C J x at hc
  rw [hc,hx,hs,Finset.sum_apply]
  exact Finset.sum_congr rfl (fun j _=>(hvec j).symm)

/-- Once the literal finite cutoff identity is proved, its true L²
realizations converge to the band series with the quantitative tail. -/
theorem literal_cutoff_error {γ A : ℝ} (hγ : 0<γ) (hA : 0≤A)
    (hb : ∀ j,(∫ x,‖F j x‖^2 ∂μ)≤A^2*((2:ℝ)^j)^(-2*γ)) :
    Tendsto (cutoffVector μ F hF hi C he) atTop (nhds (∑' j,vector μ F hF hi j)) ∧
      ∀ J : ℕ,‖(∑' j,vector μ F hF hi j)-cutoffVector μ F hF hi C he J‖≤
        A*StateBands.geometricConstant γ*((2:ℝ)^J)^(-γ) := by
  have hf : cutoffVector μ F hF hi C he=(fun J=>∑ j∈Finset.range J,vector μ F hF hi j):=
    funext (cutoffVector_eq μ F hF hi C he)
  rw [hf]
  exact cutoff_error μ F hF hi hγ hA hb

theorem literal_cutoff_of_tail (hs : Summable (vector μ F hF hi))
    (A : ℕ→ℝ) (htail : ∀ J,‖∑' n,vector μ F hF hi (n+J)‖≤A J) :
    Tendsto (cutoffVector μ F hF hi C he) atTop (nhds (∑' j,vector μ F hF hi j)) ∧
      ∀ J,‖(∑' j,vector μ F hF hi j)-cutoffVector μ F hF hi C he J‖≤A J := by
  refine ⟨?_,fun J=>?_⟩
  · have hf : cutoffVector μ F hF hi C he=(fun J=>∑ j∈Finset.range J,vector μ F hF hi j):=
      funext (cutoffVector_eq μ F hF hi C he)
    rw [hf]
    exact hs.hasSum.tendsto_sum_nat
  · rw [cutoffVector_eq μ F hF hi C he,←hs.sum_add_tsum_nat_add J,add_sub_cancel_left]
    exact htail J
end SHE.HilbertBandTails
