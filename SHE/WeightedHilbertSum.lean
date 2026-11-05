module

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Tactic

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace SHE.WeightedHilbertSum
open scoped ENNReal

variable {I A : Type*}

theorem weighted_norm_sq {w : ℝ} (hw : 0 ≤ w) (z : ℂ) :
    ‖(Real.sqrt w:ℂ)*z‖^2=w*‖z‖^2 := by
  rw [norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _),Real.sq_sqrt hw]

def vector (w : I → ℝ) (hw : ∀ i, 0 ≤ w i) (f : I → ℂ)
    (hf : Summable (fun i => w i*‖f i‖^2)) : lp (fun _ : I => ℂ) 2 :=
  ⟨fun i => (Real.sqrt (w i):ℂ)*f i,memℓp_gen (by
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two,weighted_norm_sq (hw _)] using hf)⟩

theorem vector_norm_sq (w : I → ℝ) (hw : ∀ i, 0 ≤ w i) (f : I → ℂ)
    (hf : Summable (fun i => w i*‖f i‖^2)) :
    ‖vector w hw f hf‖^2 = ∑' i, w i*‖f i‖^2 := by
  have hh := lp.norm_rpow_eq_tsum (by norm_num : 0<(2:ENNReal).toReal) (vector w hw f hf)
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two,vector,weighted_norm_sq (hw _)] using hh

theorem vector_norm (w : I → ℝ) (hw : ∀ i, 0 ≤ w i) (f : I → ℂ)
    (hf : Summable (fun i => w i*‖f i‖^2)) :
    ‖vector w hw f hf‖ = Real.sqrt (∑' i, w i*‖f i‖^2) := by
  rw [← vector_norm_sq w hw f hf,Real.sqrt_sq (norm_nonneg _)]

/-- Minkowski on the actual full weighted column/frequency space.
The finite sum is square-summable as a conclusion. No generation
orthogonality or exchange of a norm with a scalar series is assumed. -/
theorem finite_minkowski (w : I → ℝ) (hw : ∀ i, 0 ≤ w i)
    (f : A → I → ℂ) (hf : ∀ a, Summable (fun i => w i*‖f a i‖^2)) (s : Finset A) :
    Summable (fun i => w i*‖∑ a ∈ s, f a i‖^2) ∧
      Real.sqrt (∑' i, w i*‖∑ a ∈ s, f a i‖^2) ≤
        ∑ a ∈ s, Real.sqrt (∑' i, w i*‖f a i‖^2) := by
  let V : lp (fun _ : I => ℂ) 2 := ∑ a ∈ s, vector w hw (f a) (hf a)
  have hcoeff (i : I) : V i = (Real.sqrt (w i):ℂ)*(∑ a ∈ s, f a i) := by
    simp only [V,lp.coeFn_sum,Finset.sum_apply,vector,Finset.mul_sum]
  have henergy (i : I) : ‖V i‖^2=w i*‖∑ a ∈ s, f a i‖^2 := by
    rw [hcoeff,weighted_norm_sq (hw i)]
  have hs : Summable (fun i => w i*‖∑ a ∈ s, f a i‖^2) := by
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two,henergy] using
      (lp.memℓp V).summable (by norm_num)
  have hnormsq : ‖V‖^2=∑' i, w i*‖∑ a ∈ s, f a i‖^2 := by
    have hh := lp.norm_rpow_eq_tsum (by norm_num : 0<(2:ENNReal).toReal) V
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two,henergy] using hh
  refine ⟨hs, ?_⟩
  rw [← hnormsq,Real.sqrt_sq (norm_nonneg _)]
  calc
    _ ≤ ∑ a ∈ s, ‖vector w hw (f a) (hf a)‖ := norm_sum_le s _
    _ = _ := by simp only [vector_norm]

end SHE.WeightedHilbertSum
