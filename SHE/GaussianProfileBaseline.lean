module

public import SHE.ControlledProfile
public import SHE.NativeFirstWordRepresentation
public import SHE.StoppedGaussianMarginals

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section

namespace SHE.GaussianProfileBaseline
open Set MeasureTheory ProbabilityTheory StoppedFourier GaussianIncrement StoppedGaussianFeatures
open GaussianConvolution
variable [MeasurableSpace CircleL2] [BorelSpace CircleL2] {n : ℕ}

/-- The actual self-consistent controlled baseline is the expectation of
the original total coefficient under the full observation Gaussian law
at its own prescribed controlled mean. It is not recomputed after old
increments are suppressed. -/
theorem controlled_native_baseline (P : CanonicalCovariance.ProfileParameters)
    (Λ : ℝ) (u d : CircleL2) (θ : ℝ) (target : Fin n → ℝ) (center : Fin n → HeatCircle)
    (ht : ∀ i, target i ∈ Ioc 0 P.horizon) (m : State n)
    (hm : ∀ i, m i = ControlledProfile.mean Λ u d (θ,(target i,center i))) (i : Fin n) :
    gaussianAverage
      (stoppedCovariance target target center (fun p => ControlledProfile.profile P Λ u d (θ,p)) 0)
      (fun z => P.coefficient (z i)) m =
      ControlledProfile.profile P Λ u d (θ,(target i,center i)) := by
  let c : StoppedGaussianFeatures.Domain → ℝ := fun p => ControlledProfile.profile P Λ u d (θ,p)
  have hc : Measurable c := (ControlledProfile.profile_measurable P Λ u d).comp
    (measurable_const.prodMk measurable_id)
  have hb : ∀ p, 0 ≤ c p ∧ c p ≤ P.upper := fun p =>
    ⟨P.lower_pos.le.trans (ControlledProfile.profile_bounds P Λ u d (θ,p)).1,
      (ControlledProfile.profile_bounds P Λ u d (θ,p)).2⟩
  have hA : (stoppedCovariance target target center c 0).PosSemidef := by
    rw [← weightedFeature_gram target target center c hc P.upper hb (fun _ => le_rfl) 0]
    exact Matrix.posSemidef_gram ℝ _
  change (∫ y : State n, P.coefficient ((m+y) i)
    ∂multivariateGaussian 0 (stoppedCovariance target target center c 0)) = _
  simp only [PiLp.add_apply]
  rw [NativeFirstWordRepresentation.coordinate_average hA i P.coefficient P.measurable (m i)]
  rw [StoppedGaussianMarginals.native_covariance_diagonal target center
    (fun j => (ht j).1) (fun j => (ht j).2.trans P.horizon_le_one) c hc P.upper hb i, hm i]
  exact (ControlledProfile.profile_fixed P Λ u d θ (ht i) (center i)).symm

end SHE.GaussianProfileBaseline
