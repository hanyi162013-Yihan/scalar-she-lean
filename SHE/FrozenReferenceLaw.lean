module

public import SHE.FrozenReferenceIto
public import SHE.SmoothTestLaw

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.FrozenReferenceIto
open Set MeasureTheory ProbabilityTheory PredictableL2 GaussianItoTest CovarianceEndpoint
open SmoothCylinders
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

include hY in
/-- The ACTUAL original-noise reference integral has the Gaussian
distribution dictated by its deterministic physical row covariance.
This law is proved from finite Ito, ordinary past locality and smooth
test separation. It remains valid for singular observation covariance. -/
theorem gaussian_law (hJ : StandardFiniteIto.Universal 𝓕 μ H J)
    (hlocal : StandardTerminalPastLocality J)
    (hc : ∀ ω, Continuous (fun t => Y (t,ω)))
    (hrep : ∀ t : ℝ≥0, t≤H → (fun ω => Y (t,ω)) =ᵐ[μ]
      StandardFiniteIto.vectorIntegral 𝓕 μ H J z R t)
    (W : EndpointWindow n) (v b : ℝ≥0)
    (hv : W.left=(v:ℝ)) (hb : W.right=(b:ℝ)) (hbH : b≤H)
    (hcov : ∀ᵐ ω ∂μ, ∀ᵐ t : ℝ, t∈Ioo W.left W.right →
      StandardFiniteIto.rowCovariance 𝓕 μ H R ω t =
        CovarianceMatrix.densityMatrix W.coefficient W.observations t)
    (m : WordRecursion.State n) (hstart : (fun ω => Y (v,ω))=ᵐ[μ] fun _ => m) :
    HasLaw (fun ω => Y (b,ω))
      ((multivariateGaussian 0 (W.path W.left).val).map (fun y => m+y)) μ := by
  have hslice (t : ℝ≥0) : Measurable (fun ω => Y (t,ω)) :=
    ((hY.mono (predictable_le_product 𝓕)).measurable).comp
      (measurable_const.prodMk measurable_id)
  apply SmoothTestLaw.hasLaw μ _ (hslice b)
  intro F hF
  have htrans := transition_on_past_event 𝓕 μ H J R z Y hY hJ hlocal hc hrep
    W v b hv hb hbH hcov hF univ MeasurableSet.univ
  simp only [Measure.restrict_univ] at htrans
  have he : (∫ ω,backward W F W.left (Y (v,ω)) ∂μ)=backward W F W.left m := by
    calc
      _ = ∫ _ω : Ω,backward W F W.left m ∂μ := by
        apply integral_congr_ae
        filter_upwards [hstart] with ω hω
        rw [hω]
      _ = _ := by simp
  rw [htrans,he,integral_map (by fun_prop) hF.smooth.continuous.measurable.aestronglyMeasurable]
  rfl

end SHE.FrozenReferenceIto
