module

public import SHE.ScaledLpPull

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section

namespace SHE.ScaledLpPull
open MeasureTheory Filter
open scoped ENNReal
variable {A B E : Type*} [MeasurableSpace A] [MeasurableSpace B]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable (μ : Measure A) (ν : Measure B) (c : ℝ) (hc : 0<c)
variable (e : A≃ᵐB) (he : MeasurePreserving e (ENNReal.ofReal c • μ) ν)

include hc he in
theorem inverse_preserving : MeasurePreserving e.symm (ENNReal.ofReal c⁻¹ • ν) μ := by
  have hh := (MeasurePreserving.symm e he).smul_measure (ENNReal.ofReal c⁻¹)
  have heq : ENNReal.ofReal c⁻¹*ENNReal.ofReal c=1 := by
    rw [← ENNReal.ofReal_mul (inv_pos.mpr hc).le,inv_mul_cancel₀ hc.ne',ENNReal.ofReal_one]
  simpa only [smul_smul,heq,one_smul] using hh

include hc in
theorem sqrt_mul_sqrt_inv : Real.sqrt c*Real.sqrt c⁻¹=1 := by
  rw [← Real.sqrt_mul hc.le, mul_inv_cancel₀ hc.ne',Real.sqrt_one]

theorem pull_inverse (v : Lp E 2 μ) :
    pull μ ν c hc e he
      (pull ν μ c⁻¹ (inv_pos.mpr hc) e.symm (inverse_preserving μ ν c hc e he) v)=v := by
  apply Lp.ext
  have hs := ae_comp μ ν c hc e he
    (pull_ae ν μ c⁻¹ (inv_pos.mpr hc) e.symm (inverse_preserving μ ν c hc e he) v)
  filter_upwards [pull_ae μ ν c hc e he
    (pull ν μ c⁻¹ (inv_pos.mpr hc) e.symm (inverse_preserving μ ν c hc e he) v),hs] with x hx hi
  rw [hx]
  simp only [raw] at hi ⊢
  rw [hi,MeasurableEquiv.symm_apply_apply,smul_smul,sqrt_mul_sqrt_inv c hc,one_smul]

/-- Exact complete-space clock equivalence, with an explicit inverse
square-root Jacobian. No surjectivity of stochastic integration is used. -/
def equivalence : Lp E 2 ν≃ₗᵢ[ℝ]Lp E 2 μ :=
  LinearIsometryEquiv.ofSurjective (isometry μ ν c hc e he e.measurableEmbedding)
    (fun v => ⟨pull ν μ c⁻¹ (inv_pos.mpr hc) e.symm (inverse_preserving μ ν c hc e he) v,
      pull_inverse μ ν c hc e he v⟩)

theorem equivalence_ae (v : Lp E 2 ν) : equivalence μ ν c hc e he v=ᵐ[μ]
    (fun x => Real.sqrt c • v (e x)) := pull_ae μ ν c hc e he v

theorem equivalence_symm_ae (v : Lp E 2 μ) : (equivalence μ ν c hc e he).symm v=ᵐ[ν]
    (fun y => Real.sqrt c⁻¹ • v (e.symm y)) := by
  have hh : (equivalence μ ν c hc e he).symm v=
      pull ν μ c⁻¹ (inv_pos.mpr hc) e.symm (inverse_preserving μ ν c hc e he) v := by
    apply (equivalence μ ν c hc e he).injective
    rw [LinearIsometryEquiv.apply_symm_apply]
    exact (pull_inverse μ ν c hc e he v).symm
  rw [hh]
  exact pull_ae ν μ c⁻¹ (inv_pos.mpr hc) e.symm (inverse_preserving μ ν c hc e he) v

end SHE.ScaledLpPull
