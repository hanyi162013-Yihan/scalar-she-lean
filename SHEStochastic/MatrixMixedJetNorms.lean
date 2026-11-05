module

public import SHEStochastic.MatrixFrobeniusNorm
public import SHEStochastic.MatrixSqrtMixedDerivatives
public import SHEStochastic.MatrixInverseMixedDerivatives

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section

namespace SHEStochastic.MatrixMixedJetNorms
open Matrix DirectionalJets MatrixFrobeniusNorm
open scoped MatrixOrder Matrix.Norms.L2Operator ContDiff

variable {d E : Type*} [Fintype d] [DecidableEq d]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Full mixed product estimate for actual matrix derivatives. -/
theorem product (s : Set E) (hs : IsOpen s) (x : E) (hx : x∈s)
    (w : List E) (A B : E → Matrix d d ℝ)
    (hA : ∀ y∈s, ContDiffAt ℝ ∞ A y) (hB : ∀ y∈s, ContDiffAt ℝ ∞ B y) :
    size (jet w (fun y ↦ A y*B y) x) ≤
      ((pairs w).map (fun p ↦ size (jet p.1 A x)*size (jet p.2 B x))).sum := by
  rw [DirectionalJets.mul s hs x hx w A B hA hB]
  exact list_products (pairs w) _ _

/-- Quantitative mixed square-root recurrence. All terms on the right
involving the square root have strictly lower derivative order. -/
theorem sqrt (A : E → Matrix d d ℝ) (s : Set E) (hs : IsOpen s)
    (hA : ∀ y∈s, ContDiffAt ℝ ∞ A y) (hp : ∀ y∈s, (A y).PosDef)
    (x : E) (hx : x∈s) (w : List E) (hw : w≠[]) (r : ℝ) (hr : 0≤r)
    (hLo : r^2 • (1 : Matrix d d ℝ) ≤ A x) :
    2*r*size (jet w (fun y ↦ CFC.sqrt (A y)) x) ≤ size (jet w A x)+
      ((properPairs w).map (fun p ↦ size (jet p.1 (fun y ↦ CFC.sqrt (A y)) x)*
        size (jet p.2 (fun y ↦ CFC.sqrt (A y)) x))).sum := by
  have hb := MatrixSqrtMixedDerivatives.bound A s hs hA hp x hx w hw r hr hLo
  let D := jet w (fun y ↦ CFC.sqrt (A y)) x
  let R := MatrixSqrtMixedDerivatives.remainder A w x
  have hsq : (2*r*size D)^2 ≤ size (jet w A x-R)^2 := by
    rw [mul_pow, square, square]
    exact hb
  have hn : 2*r*size D ≤ size (jet w A x-R) :=
    (sq_le_sq₀ (mul_nonneg (by positivity) (nonneg D)) (nonneg _)).mp hsq
  apply hn.trans
  apply (sub (jet w A x) R).trans
  exact add_le_add le_rfl (list_products (properPairs w) _ _)

/-- Quantitative actual inverse recurrence, with all proper inverse
jets of smaller order, suitable for the inverse-square-root Haar masses. -/
theorem inverse (A : E → Matrix d d ℝ) (s : Set E) (hs : IsOpen s)
    (hA : ∀ y∈s, ContDiffAt ℝ ∞ A y) (hu : ∀ y∈s, IsUnit (A y))
    (x : E) (hx : x∈s) (w : List E) (hw : w≠[]) :
    size (jet w (fun y ↦ (A y)⁻¹) x) ≤ size ((A x)⁻¹)*
      (size (jet w A x)*size ((A x)⁻¹)+
        ((properPairs w).map (fun p ↦ size (jet p.1 A x)*size (jet p.2 (fun y ↦ (A y)⁻¹) x))).sum) := by
  rw [MatrixInverseMixedDerivatives.formula A s hs hA hu x hx w hw, MatrixFrobeniusNorm.neg]
  apply (MatrixFrobeniusNorm.mul _ _).trans
  apply mul_le_mul_of_nonneg_left _ (nonneg _)
  exact (MatrixFrobeniusNorm.add _ _).trans (add_le_add (MatrixFrobeniusNorm.mul _ _) (list_products (properPairs w) _ _))

end SHEStochastic.MatrixMixedJetNorms
