module

public import SHE.StandardFiniteIto
public import SHE.HaarKernelL2Approximation

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section

namespace SHEStochastic.WholeFieldRowCovariance
open MeasureTheory Set SHE SHE.PredictableL2
open scoped NNReal ENNReal
variable {Ω C X : Type*} [MeasurableSpace Ω] [NormedAddCommGroup C] [InnerProductSpace ℝ C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [SFinite μ] {H : ℝ≥0}

/-- Convert one whole-field energy identity to the covariance density
needed by finite-dimensional Itô. Random parameters stay inside the
same exceptional event before Fubini is applied. -/
theorem bracket {k : ℕ} (v b : ℝ≥0) (hbH : b ≤ H)
    (R : Fin k → Process (E := C) F μ H) (data : Ω → X) (r : X → Fin k → ℝ → C)
    (h : ∀ᵐ p ∂energyMeasure μ H, ∀ i, v < p.1 ∧ p.1 < b → R i p=r (data p.2) i (p.1 : ℝ)) :
    ∀ᵐ ω ∂μ, ∀ᵐ t : ℝ, t ∈ Ioo (v : ℝ) (b : ℝ) →
      StandardFiniteIto.rowCovariance F μ H R ω t =
        Matrix.gram ℝ (fun i => r (data ω) i t) := by
  have hs := (Measure.measurePreserving_swap (μ := μ) (ν := timeMeasure H)).quasiMeasurePreserving.ae h
  filter_upwards [Measure.ae_ae_of_ae_prod hs] with ω hω
  have hre : ∀ᵐ t : ℝ ∂volume.restrict (Ioc (0 : ℝ) (H : ℝ)), t ∈ Ioo (v : ℝ) (b : ℝ) →
      StandardFiniteIto.rowCovariance F μ H R ω t=Matrix.gram ℝ (fun i => r (data ω) i t) := by
    rw [← timeMeasure_map H]
    apply nonnegative_coe_measurableEmbedding.ae_map_iff.mpr
    filter_upwards [hω] with t ht htin
    simp only [Prod.swap] at ht
    have hti : v < t ∧ t < b := by exact_mod_cast htin
    ext i j
    change inner ℝ (R i ((t : ℝ).toNNReal,ω)) (R j ((t : ℝ).toNNReal,ω)) =
      inner ℝ (r (data ω) i (t : ℝ)) (r (data ω) j (t : ℝ))
    simp only [Real.toNNReal_coe]
    rw [ht i hti,ht j hti]
  rw [ae_restrict_iff' measurableSet_Ioc] at hre
  filter_upwards [hre] with t ht htin
  exact ht ⟨v.2.trans_lt htin.1,htin.2.le.trans (by exact_mod_cast hbH)⟩ htin

end SHEStochastic.WholeFieldRowCovariance
