module

public import SHE.DependentProductBounds

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1900000
noncomputable section

namespace SHE.DependentWordAssembly
open Set MeasureTheory Real ProfileL2 DependentProducts DependentProductBounds
open scoped BigOperators
variable {Ω : Type*} [MeasurableSpace Ω] {m : ℕ}

def factors (S R : Ω → ℝ) (L : Fin m → Ω → ℝ) : Fin (m+2) → Ω → ℝ :=
  Fin.cases S (Fin.cases R L)

omit [MeasurableSpace Ω] in
theorem factors_product (S R : Ω → ℝ) (L : Fin m → Ω → ℝ) (x : Ω) :
    (∏ i, factors S R L i x) = S x*R x*(∏ j,L j x) := by
  simp only [factors, Fin.prod_univ_succ, Fin.cases_zero, Fin.cases_succ]
  ring

/-- A whole word may contain arbitrarily dependent old scores, root
blocks, rough leaves and marked factors. Only the proved individual
moments are combined; physical scales remain a product. -/
theorem word_normTwo (μ : Measure Ω) [IsProbabilityMeasure μ]
    (S R : Ω → ℝ) (L : Fin m → Ω → ℝ)
    (hS : Measurable S) (hR : Measurable R) (hL : ∀ j, Measurable (L j))
    (s r : ℝ) (l : Fin m → ℝ) (hs : 0 ≤ s) (hr : 0 ≤ r) (hl : ∀ j, 0 ≤ l j)
    (CS CR : ℝ) (CL : Fin m → ℝ) (hCS : 0 ≤ CS) (hCR : 0 ≤ CR) (hCL : ∀ j, 0 ≤ CL j)
    (hiS : Integrable (fun x => |S x|^(2*(m+2))) μ)
    (hiR : Integrable (fun x => |R x|^(2*(m+2))) μ)
    (hiL : ∀ j, Integrable (fun x => |L j x|^(2*(m+2))) μ)
    (hbS : (∫ x, |S x|^(2*(m+2)) ∂μ) ≤ CS*s^(2*(m+2)))
    (hbR : (∫ x, |R x|^(2*(m+2)) ∂μ) ≤ CR*r^(2*(m+2)))
    (hbL : ∀ j, (∫ x, |L j x|^(2*(m+2)) ∂μ) ≤ CL j*l j^(2*(m+2))) :
    MemLp (fun x => S x*R x*(∏ j,L j x)) 2 μ ∧
      normTwo μ (fun x => S x*R x*(∏ j,L j x)) ≤
        sqrt (CS+CR+∑ j,CL j)*s*r*(∏ j,l j) := by
  let f := factors S R L
  let a : Fin (m+2) → ℝ := Fin.cases s (Fin.cases r l)
  let C := CS+CR+∑ j,CL j
  have hsum : 0 ≤ ∑ j,CL j := Finset.sum_nonneg (fun j _ => hCL j)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hf : ∀ i, Measurable (f i) := Fin.cases hS (Fin.cases hR hL)
  have ha : ∀ i, 0 ≤ a i := Fin.cases hs (Fin.cases hr hl)
  have hi : ∀ i, Integrable (fun x => |f i x|^(2*(m+2))) μ :=
    Fin.cases hiS (Fin.cases hiR hiL)
  have hb : ∀ i, (∫ x, |f i x|^(2*(m+2)) ∂μ) ≤ C*a i^(2*(m+2)) := by
    refine Fin.cases ?_ (Fin.cases ?_ ?_)
    · exact hbS.trans (mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) (pow_nonneg hs _))
    · exact hbR.trans (mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) (pow_nonneg hr _))
    · intro j
      have hj : CL j ≤ ∑ i,CL i := Finset.single_le_sum (fun i _ => hCL i) (Finset.mem_univ j)
      exact (hbL j).trans (mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) (pow_nonneg (hl j) _))
  have hp := product_memLp μ (by omega : 0 < m+2) f hf hi
  have hh := product_normTwo_bound μ (by omega : 0 < m+2) f hf a ha hi hC hb
  have he : (fun x => ∏ i,f i x) = fun x => S x*R x*(∏ j,L j x) := by
    funext x
    exact factors_product S R L x
  rw [he] at hp hh
  refine ⟨hp, ?_⟩
  convert! hh using 1
  simp only [a, Fin.prod_univ_succ, Fin.cases_zero, Fin.cases_succ]
  ring

theorem abs_integral_le_normTwo (μ : Measure Ω) [IsProbabilityMeasure μ]
    {f : Ω → ℝ} (hf : MemLp f 2 μ) : |∫ x,f x ∂μ| ≤ normTwo μ f := by
  have hh := integral_mul_normTwo_bound hf (memLp_const (1 : ℝ))
  simpa [normTwo] using hh

end SHE.DependentWordAssembly
