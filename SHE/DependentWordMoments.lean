module

public import SHE.DependentWordAssembly

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section

namespace SHE.DependentWordMoments
open Set MeasureTheory Real DependentProducts DependentProductBounds DependentWordAssembly
open scoped BigOperators
variable {Ω : Type*} [MeasurableSpace Ω]

/-- Actual all-fixed-even moments of a dependent finite product. All
physical scales multiply; no factor independence is assumed. -/
theorem product_even_moment (μ : Measure Ω) {n : ℕ} (hn : 0<n)
    (f : Fin n→Ω→ℝ) (hf : ∀ i,Measurable (f i)) (r : Fin n→ℝ) (hr : ∀ i,0≤r i)
    (p : ℕ) (hi : ∀ i,Integrable (fun ω => |f i ω|^(2*p*n)) μ)
    {C : ℝ} (hC : 0≤C) (hb : ∀ i,(∫ ω,|f i ω|^(2*p*n) ∂μ)≤C*r i^(2*p*n)) :
    Integrable (fun ω => |∏ i,f i ω|^(2*p)) μ ∧
      (∫ ω,|∏ i,f i ω|^(2*p) ∂μ)≤C*(∏ i,r i)^(2*p) := by
  let g := fun i ω => |f i ω|^(2*p)
  have hg : ∀ i,Measurable (g i) := fun i => ((continuous_abs.measurable.comp (hf i)).pow_const _)
  have hi' : ∀ i,Integrable (fun ω => |g i ω|^n) μ := by
    intro i
    simpa only [g,abs_pow,abs_abs,←pow_mul] using hi i
  have hb' : ∀ i,(∫ ω,|g i ω|^n ∂μ)≤C*(r i^(2*p))^n := by
    intro i
    simpa only [g,abs_pow,abs_abs,←pow_mul] using hb i
  have he (ω : Ω) : (∏ i,g i ω)=|∏ i,f i ω|^(2*p) := by
    dsimp [g]
    rw [Finset.abs_prod,Finset.prod_pow]
  have hin := integrable_abs_product μ hn g hg hi'
  have hiProd : Integrable (fun ω => |∏ i,f i ω|^(2*p)) μ := by
    simp_rw [he] at hin
    exact hin.congr (ae_of_all _ (fun ω => abs_of_nonneg (pow_nonneg (abs_nonneg _) _)))
  have hh := nonnegative_scaled_product_bound μ hn g hg (fun i => r i^(2*p))
    (fun i => pow_nonneg (hr i) _) hi' hC hb'
  simp_rw [he] at hh
  rw [abs_of_nonneg (integral_nonneg (fun _ => pow_nonneg (abs_nonneg _) _)),Finset.prod_pow] at hh
  exact ⟨hiProd,hh⟩

theorem word_even_moment (μ : Measure Ω) {m : ℕ}
    (S R : Ω→ℝ) (L : Fin m→Ω→ℝ)
    (hS : Measurable S) (hR : Measurable R) (hL : ∀ j,Measurable (L j))
    (s r : ℝ) (l : Fin m→ℝ) (hs : 0≤s) (hr : 0≤r) (hl : ∀ j,0≤l j)
    (CS CR : ℝ) (CL : Fin m→ℝ) (hCS : 0≤CS) (hCR : 0≤CR) (hCL : ∀ j,0≤CL j)
    (p : ℕ)
    (hiS : Integrable (fun x => |S x|^(2*p*(m+2))) μ)
    (hiR : Integrable (fun x => |R x|^(2*p*(m+2))) μ)
    (hiL : ∀ j,Integrable (fun x => |L j x|^(2*p*(m+2))) μ)
    (hbS : (∫ x,|S x|^(2*p*(m+2)) ∂μ)≤CS*s^(2*p*(m+2)))
    (hbR : (∫ x,|R x|^(2*p*(m+2)) ∂μ)≤CR*r^(2*p*(m+2)))
    (hbL : ∀ j,(∫ x,|L j x|^(2*p*(m+2)) ∂μ)≤CL j*l j^(2*p*(m+2))) :
    Integrable (fun x => |S x*R x*(∏ j,L j x)|^(2*p)) μ ∧
      (∫ x,|S x*R x*(∏ j,L j x)|^(2*p) ∂μ)≤
        (CS+CR+∑ j,CL j)*(s*r*(∏ j,l j))^(2*p) := by
  let f := factors S R L
  let a : Fin (m+2)→ℝ := Fin.cases s (Fin.cases r l)
  let C := CS+CR+∑ j,CL j
  have hsum : 0≤∑ j,CL j := Finset.sum_nonneg (fun j _ => hCL j)
  have hC : 0≤C := by dsimp [C];positivity
  have hf : ∀ i,Measurable (f i) := Fin.cases hS (Fin.cases hR hL)
  have ha : ∀ i,0≤a i := Fin.cases hs (Fin.cases hr hl)
  have hi : ∀ i,Integrable (fun x => |f i x|^(2*p*(m+2))) μ :=
    Fin.cases hiS (Fin.cases hiR hiL)
  have hb : ∀ i,(∫ x,|f i x|^(2*p*(m+2)) ∂μ)≤C*a i^(2*p*(m+2)) := by
    refine Fin.cases ?_ (Fin.cases ?_ ?_)
    · exact hbS.trans (mul_le_mul_of_nonneg_right (by dsimp [C];linarith) (pow_nonneg hs _))
    · exact hbR.trans (mul_le_mul_of_nonneg_right (by dsimp [C];linarith) (pow_nonneg hr _))
    · intro j
      have hj : CL j≤∑ i,CL i := Finset.single_le_sum (fun i _ => hCL i) (Finset.mem_univ j)
      exact (hbL j).trans (mul_le_mul_of_nonneg_right (by dsimp [C];linarith) (pow_nonneg (hl j) _))
  have hh := product_even_moment μ (by omega : 0<m+2) f hf a ha p hi hC hb
  have he (x : Ω) : (∏ i,f i x)=S x*R x*(∏ j,L j x) := factors_product S R L x
  simp_rw [he] at hh
  have hprod : (∏ i,a i)=s*r*(∏ j,l j) := by
    simp only [a,Fin.prod_univ_succ,Fin.cases_zero,Fin.cases_succ]
    ring
  rw [hprod] at hh
  exact hh

end SHE.DependentWordMoments
