module

public import SHE.GaussianMatrixGramCurve
public import Mathlib.Analysis.InnerProductSpace.GramMatrix

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SHE.GaussianRowGramCurve
open Set MeasureTheory GaussianCovariancePath GaussianMatrixGramCurve
open scoped InnerProductSpace Matrix.Norms.Elementwise

variable {C : Type*} [NormedAddCommGroup C] [InnerProductSpace ℝ C]
variable [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
variable {n : ℕ} (r : Fin n → ℝ → C) (hr : ∀ i, Measurable (r i))
variable (a b : ℝ) (hab : a ≤ b)
variable (hri : ∀ i, IntervalIntegrable (fun t => ‖r i t‖^2) volume a b)

def gram (t : ℝ) : Mat n := fun i j => inner ℝ (r i t) (r j t)

include hr in
theorem gram_measurable : Measurable (gram r) := by
  apply measurable_pi_iff.mpr
  intro i
  apply measurable_pi_iff.mpr
  intro j
  exact continuous_inner.measurable.comp ((hr i).prodMk (hr j))

theorem gram_positive (t : ℝ) : (gram r t).PosSemidef :=
  Matrix.posSemidef_gram ℝ (fun i => r i t)

include hr hri in
theorem gram_integrable (i j : Fin n) :
    IntervalIntegrable (fun t => gram r t i j) volume a b := by
  apply (((hri i).add (hri j)).const_mul (1/2:ℝ)).mono_fun'
  · exact (continuous_inner.measurable.comp ((hr i).prodMk (hr j))).aestronglyMeasurable
  · filter_upwards with t
    have h := norm_inner_le_norm (𝕜:=ℝ) (r i t) (r j t)
    have hs := sq_nonneg (‖r i t‖ - ‖r j t‖)
    change ‖inner ℝ (r i t) (r j t)‖ ≤ (1/2:ℝ)*(‖r i t‖^2+‖r j t‖^2)
    nlinarith

def density : Density n where
  left := a
  right := b
  ordered := hab
  value := gram r
  measurable := gram_measurable r hr
  positive := gram_positive r
  integrable := gram_integrable r hr a b hri

end SHE.GaussianRowGramCurve
