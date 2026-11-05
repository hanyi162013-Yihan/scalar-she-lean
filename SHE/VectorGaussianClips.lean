module

public import SHE.VectorClipCoordinates
public import SHE.FiniteMomentSum

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.VectorGaussianClips
open Set MeasureTheory ProbabilityTheory Real GaussianIncrement GaussianClipMoments GaussianClipProducts
open scoped BigOperators NNReal

/-- Joint vector clips retain each original Gaussian increment's scale.
Only one-dimensional marginal Gaussian laws are used; scores, other old
increments and the residual may remain arbitrarily dependent. -/
theorem dominated_even_moment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n r : ℕ} (hr : 0 < r)
    (X : Fin r → Ω → State n) (hXm : ∀ j, Measurable (X j))
    (v : Fin r → Fin n → ℝ≥0) (V : Fin r → ℝ≥0)
    (hX : ∀ j i, HasLaw (fun x => X j x i) (gaussianReal 0 (v j i)) μ)
    (hv : ∀ j i, v j i ≤ V j) {ν B : ℝ} (hν : 0 ≤ ν) (hB : 0 ≤ B)
    (R : Ω → ℝ) (hR : Measurable R)
    (hdom : ∀ x, |R x| ≤ B*∏ j,min 1 (ν*‖X j x‖))
    (p : ℕ) (hp : 0 < p) :
    Integrable (fun x => |R x|^(2*p)) μ ∧
      (∫ x,|R x|^(2*p) ∂μ) ≤ clipMomentConstant (p*r)*
        (B*(n : ℝ)^r*(∏ j,min 1 (ν*sqrt (V j : ℝ))))^(2*p) := by
  let f := fun (choice : Fin r → Fin n) (x : Ω) => ∏ j,clip ν (X j x (choice j))
  let S := ∏ j,min 1 (ν*sqrt (V j : ℝ))
  have hfn (choice : Fin r → Fin n) (x : Ω) : 0 ≤ f choice x :=
    Finset.prod_nonneg (fun j _ => clip_nonneg hν _)
  have hfm (choice : Fin r → Fin n) : Measurable (f choice) := by
    apply Finset.measurable_prod
    intro j _
    exact measurable_const.min (measurable_const.mul
      (continuous_abs.measurable.comp ((EuclideanSpace.proj (𝕜 := ℝ) (choice j)).continuous.measurable.comp (hXm j))))
  have hmoment (choice : Fin r → Fin n) :=
    GaussianClipProducts.product_even_moment μ hr (fun j x => X j x (choice j))
      (fun j => (EuclideanSpace.proj (𝕜 := ℝ) (choice j)).continuous.measurable.comp (hXm j))
      (fun j => v j (choice j)) (fun j => hX j (choice j)) hν p
  have hi (choice : Fin r → Fin n) : Integrable (fun x => f choice x^(2*p)) μ := by
    simpa only [f,abs_of_nonneg (hfn choice _)] using (hmoment choice).1
  have hscale (choice : Fin r → Fin n) :
      (∏ j,min 1 (ν*sqrt (v j (choice j) : ℝ))) ≤ S := by
    apply Finset.prod_le_prod₀ (fun j _ => le_min (by norm_num) (mul_nonneg hν (sqrt_nonneg _)))
    intro j _
    apply min_le_min_left
    exact mul_le_mul_of_nonneg_left (sqrt_le_sqrt (by exact_mod_cast hv j (choice j))) hν
  have hb (choice : Fin r → Fin n) :
      (∫ x,f choice x^(2*p) ∂μ) ≤ clipMomentConstant (p*r)*S^(2*p) := by
    have hh := (hmoment choice).2
    simp only [f,abs_of_nonneg (hfn choice _)] at hh ⊢
    exact hh.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (Finset.prod_nonneg (fun j _ =>
        le_min (by norm_num) (mul_nonneg hν (sqrt_nonneg _)))) (hscale choice) _)
      (clipMomentConstant_nonneg _))
  have hd (x : Ω) : |R x| ≤ B*∑ choice : Fin r → Fin n,f choice x :=
    (hdom x).trans (mul_le_mul_of_nonneg_left
      (VectorClipCoordinates.vector_clips_le_coordinate_assignments hν (fun j => X j x)) hB)
  have hh := FiniteMomentSum.dominated_power_moment μ (2*p) (by omega) f hfm hfn hi
    hB (clipMomentConstant_nonneg (p*r))
    (show 0 ≤ S from Finset.prod_nonneg (fun j _ =>
      le_min (by norm_num) (mul_nonneg hν (sqrt_nonneg _)))) hb R hR hd
  simpa only [Fintype.card_fun,Fintype.card_fin,Nat.cast_pow,S] using hh

end SHE.VectorGaussianClips
