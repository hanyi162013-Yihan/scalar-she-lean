module

public import SHEStochastic.PastedLinearHeatFunctional
public import SHEStochastic.AdaptedCanonicalPathTests
public import SHEStochastic.DoobL2Envelope

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section

namespace SHEStochastic.LinearHeatMaximum
open MeasureTheory ProbabilityTheory StoppedPathPasting AdaptedCanonicalPathTests
open PastedLinearHeatFunctional
open scoped NNReal ENNReal

variable {E : Type*} [AddCommGroup E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [T2Space E] [Module ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  (H : ℝ≥0) (ell : E →L[ℝ] ℝ) (lam : ℝ)
  {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (X : Ω → Path H E)

/-- The fixed continuous path envelope obeys Doob's fourth moment
bound. It can therefore be used uniformly over continuation kernels. -/
theorem fourth_bound
    (hM : Martingale (fun q x ↦ value H ell lam (X x) (clock H q)) F ν)
    (hMom : ∀ q, MemLp (fun x ↦ value H ell lam (X x) (clock H q)) 4 ν) :
    (∫⁻ x, ENNReal.ofReal ((envelope H ell lam (X x))^4) ∂ν) ≤
      4 * ∫⁻ x, ENNReal.ofReal ((value H ell lam (X x) (clock H H))^4) ∂ν := by
  let M := fun q x ↦ value H ell lam (X x) (clock H q)
  have hc (x : Ω) : Continuous (fun q ↦ M q x) :=
    (continuous_value H ell lam).comp (continuous_const.prodMk (continuous_clock H))
  have hb (q : ℝ≥0) (_ : q ≤ H) (x : Ω) : ‖M q x‖ ≤ envelope H ell lam (X x) :=
    value_bound H ell lam (X x) _
  have hmax (x : Ω) : ∃ q : ℝ≥0, q ≤ H ∧ envelope H ell lam (X x) = ‖M q x‖ := by
    obtain ⟨t, ht⟩ := envelope_attained H ell lam (X x)
    refine ⟨toNN H t, t.property.2, ?_⟩
    simpa only [M, clock_toNN] using ht
  have hsq (q : ℝ≥0) : Integrable (fun x ↦ ‖M q x‖^2) ν :=
    ((hMom q).mono_exponent (by norm_num : (2 : ℝ≥0∞) ≤ 4)).integrable_norm_pow (by norm_num)
  have hT : MemLp (fun x ↦ ‖M H x‖^2) 2 ν := by
    apply (memLp_two_iff_integrable_sq ((hMom H).aestronglyMeasurable.norm.pow 2)).mpr
    convert (hMom H).integrable_norm_pow (by norm_num : (4 : ℕ) ≠ 0) using 1
    funext x
    simp only [Pi.pow_apply]
    ring
  have hh := DoobL2Envelope.power_bound hM hc H (fun x ↦ envelope H ell lam (X x)) hb hmax 2 hsq hT
  have he (x : Ω) : ‖M H x‖^4 = (M H x)^4 := by
    rw [Real.norm_eq_abs, ← abs_pow, abs_of_nonneg (by positivity)]
  change (∫⁻ x, ENNReal.ofReal ((envelope H ell lam (X x))^4) ∂ν) ≤
    4 * ∫⁻ x, ENNReal.ofReal (‖M H x‖^4) ∂ν at hh
  simpa only [he] using hh

end SHEStochastic.LinearHeatMaximum
