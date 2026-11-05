module

public import SHE.NormalizedProductTelescope

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1700000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SHE.NormalizedProductTelescope
open MeasureTheory Set Real
open scoped BigOperators
open Classical
variable {Ω:Type*} [MeasurableSpace Ω] {m:ℕ}

/-- All normalized product slots are genuinely integrable against an
integrable old-score product. Only ordinary bounded factor hypotheses
are used; a nonzero source may be arbitrarily small. -/
theorem integrable_slots (μ:Measure Ω) (new old:Ω→Fin m→ℝ)
    (hn:∀j,Measurable (fun x=>new x j)) (ho:∀j,Measurable (fun x=>old x j))
    (C:Fin m→ℝ) (hC:∀j,0≤C j)
    (hnb:∀x j,|new x j|≤C j) (hob:∀x j,|old x j|≤C j)
    (S:Ω→ℝ) (hS:Integrable S μ) (source:Fin m→ℝ) :
    (∀i,Integrable (fun x=>S x*term (new x) (old x) source i) μ) ∧
      Integrable (fun x=>S x*∏j,new x j) μ ∧
      Integrable (fun x=>S x*∏j,old x j) μ := by
  have hprod(f:Ω→Fin m→ℝ) (hf:∀j,Measurable (fun x=>f x j))
      (hb:∀x j,|f x j|≤C j):Integrable (fun x=>S x*∏j,f x j) μ := by
    apply hS.mul_bdd (Finset.measurable_prod Finset.univ (fun j _=>hf j)).aestronglyMeasurable
    apply ae_of_all
    intro x
    rw [Real.norm_eq_abs,Finset.abs_prod]
    exact Finset.prod_le_prod₀ (fun j _=>abs_nonneg _) (fun j _=>hb x j)
  refine ⟨?_,hprod new hn hnb,hprod old ho hob⟩
  intro i
  have hv:∀x,|NormalizedScalarMoment.value (new x i-old x i) (source i)|≤(2*C i)/|source i| := by
    intro x
    by_cases hs:source i=0
    · simp only [NormalizedScalarMoment.value,hs,ite_true,abs_zero,div_zero]
      exact le_rfl
    · simp only [NormalizedScalarMoment.value,hs,ite_false,abs_div]
      apply div_le_div_of_nonneg_right _ (abs_nonneg _)
      exact (abs_sub _ _).trans (by linarith [hnb x i,hob x i])
  have htm:Measurable (fun x=>term (new x) (old x) source i):=
    ((NormalizedScalarMoment.measurable _ _ ((hn i).sub (ho i)) measurable_const).mul
      (Finset.measurable_prod _ (fun j _=>ho j))).mul
      (Finset.measurable_prod _ (fun j _=>hn j))
  apply hS.mul_bdd htm.aestronglyMeasurable
  apply ae_of_all
  intro x
  rw [Real.norm_eq_abs]
  unfold term
  simp only [abs_mul,Finset.abs_prod]
  exact mul_le_mul
    (mul_le_mul (hv x) (Finset.prod_le_prod₀ (fun j _=>abs_nonneg _) (fun j _=>hob x j))
      (Finset.prod_nonneg (fun j _=>abs_nonneg _))
      (div_nonneg (mul_nonneg (by norm_num) (hC i)) (abs_nonneg _)))
    (Finset.prod_le_prod₀ (fun j _=>abs_nonneg _) (fun j _=>hnb x j))
    (Finset.prod_nonneg (fun j _=>abs_nonneg _))
    (mul_nonneg (div_nonneg (mul_nonneg (by norm_num) (hC i)) (abs_nonneg _))
      (Finset.prod_nonneg (fun j _=>hC j)))

end SHE.NormalizedProductTelescope
