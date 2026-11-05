module

public import SHE.ProfileL2
public import SHE.ProcessEnergy
public import Mathlib.MeasureTheory.Function.AEEqOfIntegral
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section

namespace SHE.LpIntegralFubini
open MeasureTheory Set Filter
open scoped ENNReal
variable {Ω P E : Type*} [MeasurableSpace Ω] [MeasurableSpace P]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable (μ : Measure Ω) [IsFiniteMeasure μ]

theorem integral_norm_le_norm (v : Lp E 2 μ) :
    (∫ ω,‖v ω‖ ∂μ)≤Real.sqrt (μ.real univ)*‖v‖ := by
  have hn : ProfileL2.normTwo μ (fun ω => ‖v ω‖)=‖v‖ := by
    rw [ProfileL2.normTwo,← PredictableL2.realLp_norm_sq,Real.sqrt_sq (norm_nonneg _)]
  have h1 : ProfileL2.normTwo μ (fun _ : Ω => (1:ℝ))=Real.sqrt (μ.real univ) := by simp [ProfileL2.normTwo]
  have hh := ProfileL2.integral_mul_normTwo_bound (Lp.memLp v).norm
    (memLp_const (1:ℝ) : MemLp (fun _ : Ω => (1:ℝ)) 2 μ)
  simp only [mul_one,hn,h1] at hh
  exact ((le_abs_self _).trans hh).trans_eq (mul_comm _ _)

/-- Integration over a measurable event is an actual bounded linear
functional on finite-measure L² for Hilbert-valued random variables. -/
def setIntegralCLM (s : Set Ω) : Lp E 2 μ→L[ℝ]E :=
  LinearMap.mkContinuous
    { toFun := fun v => ∫ ω in s,v ω ∂μ
      map_add' := fun v w => by
        rw [integral_congr_ae (ae_restrict_of_ae (Lp.coeFn_add v w))]
        exact integral_add ((Lp.memLp v).integrable (by norm_num : (1:ENNReal)≤2)).integrableOn
          ((Lp.memLp w).integrable (by norm_num : (1:ENNReal)≤2)).integrableOn
      map_smul' := fun r v => by
        rw [integral_congr_ae (ae_restrict_of_ae (Lp.coeFn_smul r v))]
        exact integral_smul r _ }
    (Real.sqrt (μ.real univ)) (fun v => by
      exact (norm_integral_le_integral_norm _).trans
        ((integral_mono_measure Measure.restrict_le_self (Eventually.of_forall (fun _ => norm_nonneg _))
          ((Lp.memLp v).integrable (by norm_num : (1:ENNReal)≤2)).norm).trans (integral_norm_le_norm μ v)))

theorem setIntegralCLM_apply (s : Set Ω) (v : Lp E 2 μ) :
    setIntegralCLM (E := E) μ s v=∫ ω in s,v ω ∂μ := rfl

/-- Evaluation of the actual L² Bochner integral is the pointwise
integral of any jointly integrable representative. It is proved by
bounded event integrals and ordinary Bochner Fubini, without a point
evaluation functional on L². -/
theorem integral_ae (ν : Measure P) [SFinite ν]
    (F : P→Lp E 2 μ) (hF : Integrable F ν) (H : P×Ω→E)
    (hH : Integrable H (ν.prod μ)) (hRep : ∀ᵐ p ∂ν,F p=ᵐ[μ] fun ω => H (p,ω)) :
    (∫ p,F p ∂ν)=ᵐ[μ] fun ω => ∫ p,H (p,ω) ∂ν := by
  apply Integrable.ae_eq_of_forall_setIntegral_eq
    (f := (∫ p,F p ∂ν : Lp E 2 μ)) (g := fun ω => ∫ p,H (p,ω) ∂ν)
    ((Lp.memLp _).integrable (by norm_num : (1:ENNReal)≤2)) hH.integral_prod_right
  intro s hs _
  have hHs : Integrable H (ν.prod (μ.restrict s)) :=
    hH.mono_measure (Measure.prod_mono le_rfl Measure.restrict_le_self)
  calc
    _=∫ p,setIntegralCLM (E := E) μ s (F p) ∂ν :=
      ((setIntegralCLM (E := E) μ s).integral_comp_comm hF).symm
    _=∫ p,∫ ω in s,H (p,ω) ∂μ ∂ν := by
      apply integral_congr_ae
      filter_upwards [hRep] with p hp
      exact integral_congr_ae (ae_restrict_of_ae hp)
    _=_ := integral_integral_swap hHs

end SHE.LpIntegralFubini
