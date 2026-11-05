module

public import SHE.VolterraPredictable

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

namespace SHE.IntegralEnergy
open MeasureTheory
open scoped ENNReal

/-- The finite-measure Hilbert integral energy bound, with its actual
measure mass. This is ordinary deterministic Cauchy--Schwarz. -/
theorem norm_integral_sq {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    [NormedSpace ℝ E] (μ : Measure X) [IsFiniteMeasure μ] (v : X → E) (hv : MemLp v 2 μ) :
    ‖∫ x,v x ∂μ‖^2 ≤ μ.real Set.univ*(∫ x,‖v x‖^2 ∂μ) := by
  have hf : MemLp (fun x => ‖v x‖) (ENNReal.ofReal (2:ℝ)) μ := by simpa using hv.norm
  have hg : MemLp (fun _ : X => (1:ℝ)) (ENNReal.ofReal (2:ℝ)) μ := by
    simpa using (memLp_const (1:ℝ) : MemLp (fun _ : X => (1:ℝ)) 2 μ)
  have hp : (2:ℝ).HolderConjugate 2 := by rw [Real.holderConjugate_iff]; norm_num
  have hs := integral_mul_norm_le_Lp_mul_Lq hp hf hg
  simp only [norm_norm,norm_one,mul_one,Real.rpow_two,one_pow,integral_const,
    smul_eq_mul] at hs
  rw [← Real.sqrt_eq_rpow,← Real.sqrt_eq_rpow] at hs
  have hE : 0 ≤ ∫ x,‖v x‖^2 ∂μ := integral_nonneg (fun _ => sq_nonneg _)
  have hm : 0 ≤ μ.real Set.univ := measureReal_nonneg
  have hb := pow_le_pow_left₀ (norm_nonneg (∫ x,v x ∂μ))
    ((norm_integral_le_integral_norm v).trans hs) 2
  rw [mul_pow,Real.sq_sqrt hE,Real.sq_sqrt hm] at hb
  simpa only [mul_comm] using hb

end SHE.IntegralEnergy
