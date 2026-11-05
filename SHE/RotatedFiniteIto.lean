module

public import SHE.RotatedItoAlgebra

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.RotatedFiniteIto
open MeasureTheory Set PredictableL2 PredictableItoRotation StoppedItoInputs FiniteItoNoise RotatedItoAlgebra
open scoped NNReal ENNReal

variable {Ω A C : Type*} [MeasurableSpace Ω]
variable [NormedAddCommGroup A] [InnerProductSpace ℝ A] [MeasurableSpace A] [BorelSpace A]
variable [NormedAddCommGroup C] [InnerProductSpace ℝ C] [MeasurableSpace C] [BorelSpace C]
variable [SecondCountableTopology C]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [SFinite μ] (h : ℝ≥0)
variable (Φ : (ℝ≥0 × Ω) → A →ₗᵢ[ℝ] C)
variable (hΦ : @Measurable ((ℝ≥0 × Ω) × A) C
  (𝓕.predictable.prod ‹MeasurableSpace A›) ‹MeasurableSpace C› (fun p => Φ p.1 p.2))

theorem rowCovariance_ae_real {n : ℕ} (R : Fin n → Process (E := A) 𝓕 μ h) :
    ∀ᵐ ω ∂μ,∀ᵐ t : ℝ ∂volume.restrict (Ioc (0:ℝ) (h:ℝ)),
      StandardFiniteIto.rowCovariance 𝓕 μ h (fun i => processIsometry 𝓕 μ h Φ hΦ (R i)) ω t=
        StandardFiniteIto.rowCovariance 𝓕 μ h R ω t := by
  have hp : ∀ᵐ p ∂energyMeasure μ h,
      StandardFiniteIto.rowCovariance 𝓕 μ h (fun i => processIsometry 𝓕 μ h Φ hΦ (R i)) p.2 (p.1:ℝ)=
        StandardFiniteIto.rowCovariance 𝓕 μ h R p.2 (p.1:ℝ) := by
    filter_upwards [row_gram_ae 𝓕 μ h Φ hΦ R] with p hp
    ext i j
    simpa only [StandardFiniteIto.rowCovariance,Real.toNNReal_coe] using hp i j
  have hs := (Measure.measurePreserving_swap (μ := μ) (ν := timeMeasure h)).quasiMeasurePreserving.ae hp
  filter_upwards [Measure.ae_ae_of_ae_prod hs] with ω hω
  rw [← timeMeasure_map h]
  apply nonnegative_coe_measurableEmbedding.ae_map_iff.mpr
  simpa only [Real.toNNReal_coe,Prod.swap] using hω

/-- The ordinary universal finite-dimensional Ito formula is preserved
by every actual predictable isometric noise rotation. Brackets, stopped
integrals and the actual gradient-noise integral are all identified in
the proof; applicability is not a further standard-input hypothesis. -/
theorem universal (J : StandardTerminalIto (C := C) (E := ℝ) 𝓕 μ h)
    (hJ : StandardFiniteIto.Universal 𝓕 μ h J) :
    StandardFiniteIto.Universal 𝓕 μ h (PredictableItoRotation.integral 𝓕 μ h Φ hΦ J) := by
  constructor
  intro n R z Y hY hc hRep a b ha hab hb G dG hG
  let R' := fun i => processIsometry 𝓕 μ h Φ hΦ (R i)
  have hRep' : ∀ (t : ℝ≥0),t ≤ h → (fun ω => Y (t,ω)) =ᵐ[μ]
      StandardFiniteIto.vectorIntegral 𝓕 μ h J z R' t := by
    intro t ht
    rw [← vectorIntegral_rotation 𝓕 μ h Φ hΦ R J z t]
    exact hRep t ht
  filter_upwards [hJ.formula R' z Y hY hc hRep' ha hab hb G dG hG,
    rowCovariance_ae_real 𝓕 μ h Φ hΦ R] with ω hformula hcov
  have hi : (∫ t in a..b,dG t (Y (t.toNNReal,ω))+(1/2:ℝ)*
      GaussianTaylorAverage.covarianceAction (StandardFiniteIto.rowCovariance 𝓕 μ h R' ω t)
        (GaussianTaylor.hessian (G t) (Y (t.toNNReal,ω))))=
      ∫ t in a..b,dG t (Y (t.toNNReal,ω))+(1/2:ℝ)*
        GaussianTaylorAverage.covarianceAction (StandardFiniteIto.rowCovariance 𝓕 μ h R ω t)
          (GaussianTaylor.hessian (G t) (Y (t.toNNReal,ω))) := by
    apply intervalIntegral.integral_congr_ae_restrict
    rw [uIoc_of_le hab]
    have hsub : Ioc a b ⊆ Ioc (0:ℝ) (h:ℝ) := fun t ht => ⟨ha.trans_lt ht.1,ht.2.trans hb⟩
    have hc' := hcov.filter_mono (ae_mono (Measure.restrict_mono_set volume hsub))
    filter_upwards [hc'] with t ht
    rw [ht]
  rw [hi] at hformula
  simpa only [noise_rotation 𝓕 μ h Φ hΦ Y hY R J a b G] using hformula

end SHE.RotatedFiniteIto
