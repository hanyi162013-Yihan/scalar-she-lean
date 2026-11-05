module

public import SHE.StandardFiniteIto
public import SHE.SmoothWords
public import SHE.FiniteItoPastNoise

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.FrozenReferenceIto
open Set MeasureTheory PredictableL2 GaussianItoTest CovarianceEndpoint
open SmoothCylinders GaussianTaylorAverage
open scoped NNReal ENNReal

variable {Ω C : Type*} [MeasurableSpace Ω]
variable [NormedAddCommGroup C] [InnerProductSpace ℝ C]
variable [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω)
variable [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (J : StandardTerminalIto (C := C) (E := ℝ) 𝓕 μ H)
variable {n : ℕ} (R : Fin n → Process (E := C) 𝓕 μ H) (z : WordRecursion.State n)
variable (Y : ℝ≥0 × Ω → WordRecursion.State n)
variable (hY : StronglyMeasurable[𝓕.predictable] Y)

/-- The deterministic reference backward test cancels the ACTUAL row
bracket. Gaussian transition identities are consequently derived from
the accepted ordinary finite-dimensional Ito formula; no additional
Gaussian-law assumption on the integral is used. -/
theorem terminal_identity (hJ : StandardFiniteIto.Universal 𝓕 μ H J)
    (hc : ∀ ω, Continuous (fun t => Y (t,ω)))
    (hrep : ∀ t : ℝ≥0, t≤H → (fun ω => Y (t,ω)) =ᵐ[μ]
      StandardFiniteIto.vectorIntegral 𝓕 μ H J z R t)
    (W : EndpointWindow n) (ha : 0≤W.left) (hb : W.right≤(H:ℝ))
    (hcov : ∀ᵐ ω ∂μ, ∀ᵐ t : ℝ, t∈Ioo W.left W.right →
      StandardFiniteIto.rowCovariance 𝓕 μ H R ω t =
        CovarianceMatrix.densityMatrix W.coefficient W.observations t)
    {F : WordRecursion.State n → ℝ} (hF : BoundedSmooth F) :
    ∀ᵐ ω ∂μ, F (Y (W.right.toNNReal,ω)) =
      backward W F W.left (Y (W.left.toNNReal,ω)) +
        FiniteItoNoise.noise 𝓕 μ H Y hY R J W.left W.right (backward W F) ω := by
  have hf := hJ.formula R z Y hY hc hrep ha W.ordered hb
    (backward W F) (backwardDerivative W F)
    (SmoothWords.boundedSmooth_backward_regular W hF)
  filter_upwards [hf,hcov] with ω hf hcov
  rw [PhysicalIto.backward_terminal W F] at hf
  have hz : (∫ t in W.left..W.right,
      backwardDerivative W F t (Y (t.toNNReal,ω)) + (1/2:ℝ) *
        covarianceAction (StandardFiniteIto.rowCovariance 𝓕 μ H R ω t)
          (GaussianTaylor.hessian (backward W F t) (Y (t.toNNReal,ω)))) = 0 := by
    apply intervalIntegral.integral_zero_ae
    filter_upwards [hcov,volume.ae_ne W.right] with t ht htr htin
    rw [uIoc_of_le W.ordered] at htin
    have hto : t∈Ioo W.left W.right := ⟨htin.1,lt_of_le_of_ne htin.2 htr⟩
    rw [ht hto]
    unfold backwardDerivative
    ring
  simpa only [hz,add_zero] using hf

include hY in
/-- Conditional Gaussian-semigroup transition on EVERY actual past
event. The centering is proved for the original full-horizon gradient
integral by ordinary past locality; there is no restarted noise input. -/
theorem transition_on_past_event (hJ : StandardFiniteIto.Universal 𝓕 μ H J)
    (hlocal : StandardTerminalPastLocality J)
    (hc : ∀ ω, Continuous (fun t => Y (t,ω)))
    (hrep : ∀ t : ℝ≥0, t≤H → (fun ω => Y (t,ω)) =ᵐ[μ]
      StandardFiniteIto.vectorIntegral 𝓕 μ H J z R t)
    (W : EndpointWindow n) (v b : ℝ≥0)
    (hv : W.left=(v:ℝ)) (hb : W.right=(b:ℝ)) (hbH : b≤H)
    (hcov : ∀ᵐ ω ∂μ, ∀ᵐ t : ℝ, t∈Ioo W.left W.right →
      StandardFiniteIto.rowCovariance 𝓕 μ H R ω t =
        CovarianceMatrix.densityMatrix W.coefficient W.observations t)
    {F : WordRecursion.State n → ℝ} (hF : BoundedSmooth F)
    (A : Set Ω) (hA : MeasurableSet[𝓕 v] A) :
    (∫ ω in A, F (Y (b,ω)) ∂μ) =
      ∫ ω in A, backward W F W.left (Y (v,ω)) ∂μ := by
  have hvb : v≤b := by exact_mod_cast (show (v:ℝ)≤(b:ℝ) by simpa only [hv,hb] using W.ordered)
  have hform := terminal_identity 𝓕 μ H J R z Y hY hJ hc hrep W
    (by rw [hv]; exact v.2) (by rw [hb]; exact_mod_cast hbH) hcov hF
  have hform' : (fun ω => F (Y (b,ω))) =ᵐ[μ] fun ω =>
      backward W F W.left (Y (v,ω)) +
        FiniteItoNoise.noise 𝓕 μ H Y hY R J v b (backward W F) ω := by
    filter_upwards [hform] with ω hω
    simpa only [hv,hb,Real.toNNReal_coe] using hω
  have hslice (t : ℝ≥0) : Measurable (fun ω => Y (t,ω)) :=
    ((hY.mono (predictable_le_product 𝓕)).measurable).comp
      (measurable_const.prodMk measurable_id)
  obtain ⟨M,hM⟩ := hF.norm_bound
  have hqi : Integrable (fun ω => backward W F W.left (Y (v,ω))) μ := by
    apply (integrable_const M).mono'
      (((SmoothWords.backward_boundedSmooth W hF W.left).smooth.continuous.measurable).comp
        (hslice v)).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun ω => GaussianSmooth.average_norm_bound _ hM _)
  have hni := FiniteItoNoise.noise_integrable 𝓕 μ H Y hY R J v b (backward W F)
  rw [integral_congr_ae (ae_restrict_of_ae hform'),
    integral_add hqi.integrableOn hni.integrableOn,
    FiniteItoPastNoise.noise_centered_on_past_event 𝓕 μ H Y hY R J hlocal v b hvb
      (backward W F) A hA,add_zero]

end SHE.FrozenReferenceIto
