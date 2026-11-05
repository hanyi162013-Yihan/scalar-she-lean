module

public import SHE.StateBands
public import SHE.HilbertParameterAverage

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1100000
noncomputable section
namespace SHE.HilbertBandTails
open Set Filter MeasureTheory Real PredictableL2
open scoped ENNReal
variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable (μ : Measure X) (F : ℕ→X→E) (hF : ∀ j,Measurable (F j))
variable (hi : ∀ j,Integrable (fun x=>‖F j x‖^2) μ)

def vector (j : ℕ) : Lp E 2 μ:=
  ((memLp_two_iff_integrable_sq_norm (hF j).aestronglyMeasurable).mpr (hi j)).toLp (F j)

theorem vector_norm_sq (j : ℕ) : ‖vector μ F hF hi j‖^2=∫ x,‖F j x‖^2 ∂μ := by
  rw [realLp_norm_sq]
  apply integral_congr_ae
  exact (((memLp_two_iff_integrable_sq_norm (hF j).aestronglyMeasurable).mpr (hi j)).coeFn_toLp).mono
    (fun _ hx=>congrArg (fun z : E=>‖z‖^2) hx)

/-- Genuine L2-valued root-band summation and geometric cutoff tails.
The same statement holds on a current-time × probability measure,
without separability of the global probability L2 space. -/
theorem dyadic {γ A : ℝ} (hγ : 0<γ) (hA : 0≤A)
    (hb : ∀ j,(∫ x,‖F j x‖^2 ∂μ)≤A^2*((2:ℝ)^j)^(-2*γ)) :
    Summable (vector μ F hF hi) ∧
      ∀ J : ℕ,‖∑' n,vector μ F hF hi (n+J)‖≤
        A*StateBands.geometricConstant γ*((2:ℝ)^J)^(-γ) := by
  have hv (j : ℕ) : ‖vector μ F hF hi j‖≤A*((2:ℝ)^j)^(-γ):=by
    have hh:=hb j
    rw [←vector_norm_sq μ F hF hi j] at hh
    have hp : ((2:ℝ)^j)^(-2*γ)=(((2:ℝ)^j)^(-γ))^2:=by
      rw [←rpow_mul_natCast (show 0≤(2:ℝ)^j by positivity)]
      congr 1
      ring
    rw [hp,←mul_pow] at hh
    have hn : 0≤A*((2:ℝ)^j)^(-γ):=mul_nonneg hA (rpow_nonneg (by positivity) _)
    nlinarith [norm_nonneg (vector μ F hF hi j)]
  have hs:=StateBands.vector_geometric_bands hγ (show 0<(1:ℝ) by norm_num) hA
    (vector μ F hF hi) (fun j=>by simpa only [one_mul] using hv j)
  refine ⟨hs.1,fun J=>?_⟩
  have ht:=StateBands.vector_geometric_bands hγ (show 0<(2:ℝ)^J by positivity) hA
    (fun n=>vector μ F hF hi (n+J)) (fun n=>by simpa only [pow_add,mul_comm ((2:ℝ)^n)] using hv (n+J))
  exact ht.2
end SHE.HilbertBandTails
