module

public import SHE.RealMomentBound

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHE.NormalizedScalarMoment
open Set MeasureTheory Real

def value (f source : ℝ) : ℝ := if source=0 then 0 else f/source

theorem measurable {Ω : Type*} [MeasurableSpace Ω] (f source : Ω→ℝ)
    (hf : Measurable f) (hs : Measurable source) :
    Measurable (fun ω=>value (f ω) (source ω)) := by
  unfold value
  exact Measurable.ite (measurableSet_eq_fun hs measurable_const) measurable_const (hf.div hs)

theorem factorization (f source : ℝ) (hzero : source=0→f=0) : source*value f source=f := by
  unfold value
  split_ifs with hs
  · simp [hs,hzero hs]
  · exact mul_div_cancel₀ _ hs

/-- Remove a deterministic current source BEFORE the conditional
Gaussian moment. The resulting moment is uniform in that source; the
source can later be an actual correlated current displacement. -/
theorem even_moment {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω→ℝ) (p : ℕ) (hp : 0<p) {source C S : ℝ}
    (hs : 0≤source) (hC : 0≤C) (hS : 0≤S)
    (hi : Integrable (fun ω=>|f ω|^(2*p)) μ)
    (hb : (∫ ω,|f ω|^(2*p) ∂μ)≤C*(source*S)^(2*p)) :
    Integrable (fun ω=>|value (f ω) source|^(2*p)) μ ∧
      (∫ ω,|value (f ω) source|^(2*p) ∂μ)≤C*S^(2*p) := by
  by_cases hs0 : source=0
  · have hk : 2*p≠0:=Nat.mul_ne_zero (by decide) hp.ne'
    simp only [value,hs0,ite_true,abs_zero,zero_pow hk]
    exact ⟨integrable_const (0:ℝ),by
      simpa only [integral_zero] using mul_nonneg hC (pow_nonneg hS (2*p))⟩
  · have hspos : 0<source:=lt_of_le_of_ne hs (Ne.symm hs0)
    have he (ω : Ω) : |value (f ω) source|^(2*p)=|f ω|^(2*p)/source^(2*p) := by
      simp only [value,hs0,ite_false,abs_div,abs_of_pos hspos,div_pow]
    have hiN : Integrable (fun ω=>|value (f ω) source|^(2*p)) μ := by
      simpa only [he] using hi.div_const (source^(2*p))
    refine ⟨hiN,?_⟩
    simp_rw [he]
    rw [integral_div]
    apply (div_le_iff₀ (pow_pos hspos (2*p))).mpr
    exact hb.trans_eq (by rw [mul_pow];ring)

end SHE.NormalizedScalarMoment
