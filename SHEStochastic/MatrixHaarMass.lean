module

public import SHEStochastic.MatrixHaarPairings
import all Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
noncomputable section

namespace SHEStochastic.MatrixHaarMass
open MeasureTheory Matrix MatrixHaarFunctions Filter
open scoped MatrixOrder Matrix.Norms.L2Operator

variable {X n : Type*} [MeasurableSpace X] [Fintype n] [DecidableEq n]
  (μ : Measure X) [IsFiniteMeasure μ] (κ : X → Matrix n n ℝ)

/-- Integrating a uniformly elliptic profile gives precisely the
interval-mass ellipticity bound, with its actual spatial measure. -/
theorem lower (hκ : Integrable κ μ) (c : ℝ)
    (hLower : ∀ᵐ x ∂μ, c • (1 : Matrix n n ℝ) ≤ κ x) (s : Set X) :
    (μ.real s*c) • (1 : Matrix n n ℝ) ≤ mass μ κ s := by
  have hh := integral_mono_ae
    (integrable_const (c • (1 : Matrix n n ℝ)) : Integrable (fun _ : X ↦ c • (1 : Matrix n n ℝ)) (μ.restrict s))
    hκ.integrableOn (ae_restrict_of_ae hLower)
  rw [Matrix.le_iff] at hh
  change (mass μ κ s-(μ.real s*c) • (1 : Matrix n n ℝ)).PosSemidef
  simp only [integral_const, Measure.real, Measure.restrict_apply MeasurableSet.univ,
    Set.univ_inter, smul_smul] at hh
  convert! hh using 1

/-- Every positive-measure interval has a positive definite covariance
mass. The inverse-square-root coefficients therefore require no
separate matrix invertibility hypothesis. -/
theorem posDef (hκ : Integrable κ μ) (c : ℝ) (hc : 0<c)
    (hLower : ∀ᵐ x ∂μ, c • (1 : Matrix n n ℝ) ≤ κ x)
    (s : Set X) (hs : 0<μ s) : (mass μ κ s).PosDef := by
  have hsR : 0<μ.real s := ENNReal.toReal_pos (ne_of_gt hs) (measure_ne_top μ s)
  have hp : ((μ.real s*c) • (1 : Matrix n n ℝ)).PosDef :=
    Matrix.PosDef.one.smul (mul_pos hsR hc)
  have hDiff : (mass μ κ s-(μ.real s*c) • (1 : Matrix n n ℝ)).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr (lower μ κ hκ c hLower s))
  convert hp.add_posSemidef hDiff using 1
  abel

/-- The matching upper bound is inherited by the same matrix mass. -/
theorem upper (hκ : Integrable κ μ) (C : ℝ)
    (hUpper : ∀ᵐ x ∂μ, κ x ≤ C • (1 : Matrix n n ℝ)) (s : Set X) :
    mass μ κ s ≤ (μ.real s*C) • (1 : Matrix n n ℝ) := by
  have hh := integral_mono_ae hκ.integrableOn
    (integrable_const (C • (1 : Matrix n n ℝ)) : Integrable (fun _ : X ↦ C • (1 : Matrix n n ℝ)) (μ.restrict s))
    (ae_restrict_of_ae hUpper)
  rw [Matrix.le_iff] at hh
  change ((μ.real s*C) • (1 : Matrix n n ℝ)-mass μ κ s).PosSemidef
  simp only [integral_const, Measure.real, Measure.restrict_apply MeasurableSet.univ,
    Set.univ_inter, smul_smul] at hh
  convert! hh using 1

end SHEStochastic.MatrixHaarMass
