module

public import SHEStochastic.MatrixHaarFunctions
public import Mathlib.Analysis.Normed.Module.FiniteDimension

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
noncomputable section

namespace SHEStochastic.MatrixHaarPairings
open MeasureTheory Matrix Set MatrixHaarFunctions
open scoped MatrixOrder Matrix.Norms.L2Operator

variable {X n : Type*} [MeasurableSpace X] [Fintype n] [DecidableEq n]
  (μ : Measure X) (κ : X → Matrix n n ℝ)

def entry (i j : n) : Matrix n n ℝ →L[ℝ] ℝ :=
  (((LinearMap.proj j) : (n → ℝ) →ₗ[ℝ] ℝ).comp
    ((LinearMap.proj i) : Matrix n n ℝ →ₗ[ℝ] (n → ℝ))).toContinuousLinearMap

theorem gram_integrable (hκ : Integrable κ μ) (s t : Set X)
    (hs : MeasurableSet s) (ht : MeasurableSet t) (hd : Disjoint s t) :
    Integrable (fun x ↦ (column μ κ s t x)ᴴ*κ x*column μ κ s t x) μ := by
  simp_rw [gram_value μ κ s t hd]
  exact (((hκ.const_mul _).mul_const _).indicator hs).add
    (((hκ.const_mul _).mul_const _).indicator ht)

/-- In particular, the d actual component columns have Kronecker
weighted pairings; no scalarization discards off-diagonal terms. -/
theorem components (hκ : Integrable κ μ) (s t : Set X)
    (hs : MeasurableSet s) (ht : MeasurableSet t) (hd : Disjoint s t)
    (hA : (mass μ κ s).PosDef) (hB : (mass μ κ t).PosDef) (i j : n) :
    (∫ x, ∑ p : n, ∑ q : n,
      column μ κ s t x p i * κ x p q * column μ κ s t x q j ∂μ) = if i=j then 1 else 0 := by
  have hh := (entry i j).integral_comp_comm (gram_integrable μ κ hκ s t hs ht hd)
  rw [weighted_gram μ κ hκ s t hs ht hd hA hB] at hh
  change (∫ x, ((column μ κ s t x)ᴴ*κ x*column μ κ s t x) i j ∂μ) = (1 : Matrix n n ℝ) i j at hh
  rw [Matrix.one_apply] at hh
  rw [← hh]
  apply integral_congr_ae
  filter_upwards with x
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, star_trivial]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]

/-- A function constant on the support of a finer column is orthogonal
to it. This includes the root column and every coarser dyadic ancestor. -/
theorem nested (hκ : Integrable κ μ) (s t : Set X)
    (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hA : (mass μ κ s).PosDef) (hB : (mass μ κ t).PosDef)
    (P : X → Matrix n n ℝ) (C : Matrix n n ℝ)
    (hP : ∀ x ∈ s ∪ t, P x=C) :
    (∫ x, (P x)ᴴ*κ x*column μ κ s t x ∂μ) = 0 := by
  have he : (fun x ↦ (P x)ᴴ*κ x*column μ κ s t x) =
      (fun x ↦ Cᴴ*(κ x*column μ κ s t x)) := by
    funext x
    by_cases hx : x∈s∪t
    · rw [hP x hx, mul_assoc]
    · simp only [support μ κ s t x hx, mul_zero]
  rw [he]
  exact MatrixHaarFunctions.constant_orthogonal μ κ hκ s t hs ht hA hB C

/-- Separate dyadic supports give zero pairing pointwise, so no
additional integrability assumption on a cross term is necessary. -/
theorem disjoint (s t u v : Set X) (hd : Disjoint (s∪t) (u∪v)) :
    (∫ x, (column μ κ s t x)ᴴ*κ x*column μ κ u v x ∂μ) = 0 := by
  have he (x : X) : (column μ κ s t x)ᴴ*κ x*column μ κ u v x = 0 := by
    by_cases hx : x∈s∪t
    · have hy : x∉u∪v := fun hy ↦ Set.disjoint_left.mp hd hx hy
      rw [support μ κ u v x hy, mul_zero]
    · rw [support μ κ s t x hx, conjTranspose_zero, zero_mul, zero_mul]
  simp_rw [he]
  simp only [integral_zero]

end SHEStochastic.MatrixHaarPairings
