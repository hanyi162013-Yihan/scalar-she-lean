module

public import SHEStochastic.CanonicalNativeBrownian
public import SHEStochastic.BrownianCoordinates
public import Mathlib.Probability.Moments.SubGaussian

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section

namespace SHEStochastic.CanonicalBrownianSubGaussian
open MeasureTheory ProbabilityTheory SHE
open scoped NNReal

theorem of_law {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {X : Ω → ℝ} (c : ℝ≥0) (hX : HasLaw X (gaussianReal 0 c) μ) :
    HasSubgaussianMGF X c μ := by
  apply (HasSubgaussianMGF.id_map_iff hX.aemeasurable).mp
  rw [hX.map_eq]
  refine ⟨fun a ↦ integrable_exp_mul_gaussianReal a, fun a ↦ ?_⟩
  rw [mgf_id_gaussianReal]
  simp

theorem coordinate {Ω E ι : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
    (P : FiniteScalarIto.Family F μ H ι) (U : ℝ≥0 → Ω → E)
    (hc : ∀ sample, Continuous (fun t ↦ U t sample)) (hU : ∀ t, Measurable[F t] (U t))
    (i : ι) (t : ℝ≥0) :
    HasSubgaussianMGF (CanonicalStateDriverFiltration.coordinate (E := E) H i t) (min t H)
      (μ.map (CanonicalNativeBrownian.bundle F μ H P U hc)) := by
  have hB := CanonicalNativeBrownian.law F μ H P U hc hU
  have hl := BrownianCoordinates.eval_law (CanonicalStateDriverFiltration.filtration H)
    (μ.map (CanonicalNativeBrownian.bundle F μ H P U hc)) H (CanonicalStateDriverFiltration.coordinate H)
    hB i (min t H) (min_le_right _ _)
  have he : CanonicalStateDriverFiltration.coordinate (E := E) H i (min t H) =
      CanonicalStateDriverFiltration.coordinate H i t := by
    funext x
    simp only [CanonicalStateDriverFiltration.coordinate, CanonicalStateDriverFiltration.clock,
      NNReal.coe_min, min_assoc, min_self]
  rw [he] at hl
  exact of_law _ (min t H) hl

end SHEStochastic.CanonicalBrownianSubGaussian
