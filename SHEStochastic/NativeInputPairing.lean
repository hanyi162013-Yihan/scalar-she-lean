module

public import SHEStochastic.NativeRowRepresentatives
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.NativeInputPairing
open MeasureTheory SHE SHE.PredictableL2
open scoped NNReal ENNReal
variable {Ω C : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {H : ℝ≥0}

theorem process_ext (v w : Process (E := C) F μ H)
    (h : v =ᵐ[energyMeasure μ H] w) : v = w := by
  apply (processEmbedding F μ H).injective
  apply Lp.ext
  exact (ambient_ae (energyMeasure μ H) (predictable_le_product F) v).trans
    (h.trans (ambient_ae (energyMeasure μ H) (predictable_le_product F) w).symm)

theorem integrable (v w : Process (E := C) F μ H) :
    Integrable (fun p : ℝ≥0 × Ω => inner ℝ (v p) (w p)) (energyMeasure μ H) := by
  apply (L2.integrable_inner (𝕜 := ℝ) (processEmbedding F μ H v) (processEmbedding F μ H w)).congr
  filter_upwards [ambient_ae (energyMeasure μ H) (predictable_le_product F) v,
    ambient_ae (energyMeasure μ H) (predictable_le_product F) w] with p hv hw
  change inner ℝ (ambient (energyMeasure μ H) (predictable_le_product F) v p)
    (ambient (energyMeasure μ H) (predictable_le_product F) w p) = _
  rw [hv, hw]

/-- Native cylindrical input transport preserves the literal space-time
pairing, without a deterministic covariance hypothesis. -/
theorem pairing (v w : Process (E := C) F μ H) :
    inner ℝ (FiniteCylindricalIto.processTransport v) (FiniteCylindricalIto.processTransport w) =
      ∫ r, ∫ ω, inner ℝ (v (r,ω)) (w (r,ω)) ∂μ ∂timeMeasure H := by
  rw [(FiniteCylindricalIto.processTransport (F := F) (μ := μ) (H := H) (C := C)).inner_map_map]
  have he : inner ℝ v w = inner ℝ (processEmbedding F μ H v) (processEmbedding F μ H w) :=
    ((processEmbedding F μ H).inner_map_map v w).symm
  rw [he, L2.inner_def]
  calc
    _ = ∫ p, inner ℝ (v p) (w p) ∂energyMeasure μ H := by
      apply integral_congr_ae
      filter_upwards [ambient_ae (energyMeasure μ H) (predictable_le_product F) v,
        ambient_ae (energyMeasure μ H) (predictable_le_product F) w] with p hv hw
      change inner ℝ (ambient (energyMeasure μ H) (predictable_le_product F) v p)
        (ambient (energyMeasure μ H) (predictable_le_product F) w p) = _
      rw [hv, hw]
    _ = _ := integral_prod _ (integrable v w)

end SHEStochastic.NativeInputPairing
