module

public import SHEStochastic.MatrixHaarMeasurability
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section

namespace SHEStochastic.MatrixHaarFunctions
open MeasureTheory MatrixHaarAlgebra Matrix Set
open scoped MatrixOrder Matrix.Norms.L2Operator

variable {X n : Type*} [MeasurableSpace X] [Fintype n] [DecidableEq n]
  (μ : Measure X) (κ : X → Matrix n n ℝ)

def mass (s : Set X) : Matrix n n ℝ := ∫ x in s, κ x ∂μ

/-- The literal matrix Haar function on two disjoint children. In the
application these children are the left and right halves of a dyadic interval. -/
def column (s t : Set X) (x : X) : Matrix n n ℝ :=
  s.indicator (fun _ ↦ left (mass μ κ s) (mass μ κ t)) x +
    t.indicator (fun _ ↦ right (mass μ κ s) (mass μ κ t)) x

theorem measurable_column (s t : Set X) (hs : MeasurableSet s) (ht : MeasurableSet t) :
    Measurable (column μ κ s t) :=
  (measurable_const.indicator hs).add (measurable_const.indicator ht)

theorem support (s t : Set X) (x : X) (hx : x ∉ s ∪ t) : column μ κ s t x = 0 := by
  have hs : x∉s := fun hs ↦ hx (Or.inl hs)
  have ht : x∉t := fun ht ↦ hx (Or.inr ht)
  simp [column, hs, ht]

theorem weighted_value (s t : Set X) (x : X) :
    κ x*column μ κ s t x =
      s.indicator (fun x ↦ κ x*left (mass μ κ s) (mass μ κ t)) x +
      t.indicator (fun x ↦ κ x*right (mass μ κ s) (mass μ κ t)) x := by
  by_cases hs : x∈s <;> by_cases ht : x∈t <;> simp [column, hs, ht, mul_add]

theorem integrable_weighted (hκ : Integrable κ μ) (s t : Set X)
    (hs : MeasurableSet s) (ht : MeasurableSet t) :
    Integrable (fun x ↦ κ x*column μ κ s t x) μ := by
  simp_rw [weighted_value]
  exact ((hκ.mul_const _).indicator hs).add ((hκ.mul_const _).indicator ht)

/-- The matrix cancellation formula holds as an actual spatial integral. -/
theorem weighted_mean (hκ : Integrable κ μ) (s t : Set X)
    (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hA : (mass μ κ s).PosDef) (hB : (mass μ κ t).PosDef) :
    (∫ x, κ x*column μ κ s t x ∂μ) = 0 := by
  simp_rw [weighted_value]
  rw [integral_add ((hκ.mul_const _).indicator hs) ((hκ.mul_const _).indicator ht),
    integral_indicator hs, integral_indicator ht,
    integral_mul_const_of_integrable hκ.integrableOn,
    integral_mul_const_of_integrable hκ.integrableOn]
  exact MatrixHaarAlgebra.weighted_mean _ _ hA hB

theorem gram_value (s t : Set X) (hd : Disjoint s t) (x : X) :
    (column μ κ s t x)ᴴ*κ x*column μ κ s t x =
      s.indicator (fun x ↦ (left (mass μ κ s) (mass μ κ t))ᴴ*κ x*left (mass μ κ s) (mass μ κ t)) x +
      t.indicator (fun x ↦ (right (mass μ κ s) (mass μ κ t))ᴴ*κ x*right (mass μ κ s) (mass μ κ t)) x := by
  by_cases hs : x∈s
  · have ht : x∉t := fun ht ↦ Set.disjoint_left.mp hd hs ht
    simp [column, hs, ht]
  · by_cases ht : x∈t <;> simp [column, hs, ht]

theorem integral_sandwich (hκ : Integrable κ μ) (s : Set X) (L R : Matrix n n ℝ) :
    (∫ x in s, Lᴴ*κ x*R ∂μ) = Lᴴ*mass μ κ s*R := by
  rw [integral_mul_const_of_integrable (hκ.integrableOn.const_mul Lᴴ),
    integral_const_mul_of_integrable hκ.integrableOn]
  rfl

/-- All component pairings are normalized simultaneously. No
commutation of the two child covariance masses is assumed. -/
theorem weighted_gram (hκ : Integrable κ μ) (s t : Set X)
    (hs : MeasurableSet s) (ht : MeasurableSet t) (hd : Disjoint s t)
    (hA : (mass μ κ s).PosDef) (hB : (mass μ κ t).PosDef) :
    (∫ x, (column μ κ s t x)ᴴ*κ x*column μ κ s t x ∂μ) = 1 := by
  simp_rw [gram_value μ κ s t hd]
  rw [integral_add (((hκ.const_mul _).mul_const _).indicator hs)
      (((hκ.const_mul _).mul_const _).indicator ht),
    integral_indicator hs, integral_indicator ht,
    integral_sandwich μ κ hκ, integral_sandwich μ κ hκ]
  exact MatrixHaarAlgebra.weighted_gram _ _ hA hB

/-- The pairing with any constant block vanishes, which is the local
orthogonality identity for nested dyadic intervals. -/
theorem constant_orthogonal (hκ : Integrable κ μ) (s t : Set X)
    (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hA : (mass μ κ s).PosDef) (hB : (mass μ κ t).PosDef) (C : Matrix n n ℝ) :
    (∫ x, Cᴴ*(κ x*column μ κ s t x) ∂μ) = 0 := by
  rw [integral_const_mul_of_integrable (integrable_weighted μ κ hκ s t hs ht),
    weighted_mean μ κ hκ s t hs ht hA hB, mul_zero]

end SHEStochastic.MatrixHaarFunctions
