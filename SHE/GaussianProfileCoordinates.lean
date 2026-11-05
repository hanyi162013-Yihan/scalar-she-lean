module

public import SHE.GaussianProfileBaseline

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section

namespace SHE.GaussianProfileBaseline
open Set MeasureTheory ProbabilityTheory StoppedFourier GaussianIncrement StoppedGaussianFeatures
open GaussianConvolution
variable {n : ℕ}

/-- A native leaf retains its own scalar profile variance even when the
other coordinates have different targets, stops or collision patterns. -/
theorem coordinate_covariance_eq_native (σ target : Fin n → ℝ) (center : Fin n → HeatCircle)
    (c : Domain → ℝ) (hc : Measurable c) (M : ℝ) (hb : ∀ p, 0 ≤ c p ∧ c p ≤ M)
    (i : Fin n) (hnative : σ i = target i) (ht : 0 < target i) (ht1 : target i ≤ 1) :
    stoppedCovariance σ target center c 0 i i = ProfileVariance.varianceMap c (target i) (center i) := by
  have h := StoppedGaussianMarginals.native_covariance_diagonal
    (fun _ : Fin 1 => target i) (fun _ : Fin 1 => center i)
    (fun _ => ht) (fun _ => ht1) c hc M hb 0
  calc
    _ = stoppedCovariance (fun _ : Fin 1 => target i) (fun _ => target i)
        (fun _ => center i) c 0 0 0 := by
      unfold StoppedGaussianFeatures.stoppedCovariance
      apply integral_congr_ae
      apply ae_of_all
      intro r
      simp only [stoppedRow,hnative]
    _ = _ := h

/-- Full-profile baseline compatibility for one actual native leaf.
Other observations may have older heat targets or earlier stops. Only
this leaf's own mean is required to match the controlled profile. -/
theorem controlled_coordinate_baseline (P : CanonicalCovariance.ProfileParameters)
    (Λ : ℝ) (u d : CircleL2) (θ : ℝ) (σ target : Fin n → ℝ) (center : Fin n → HeatCircle)
    (hages : ∀ j, σ j ≤ target j) (i : Fin n) (hnative : σ i = target i)
    (ht : target i ∈ Ioc 0 P.horizon) (m : State n)
    (hm : m i = ControlledProfile.mean Λ u d (θ,(target i,center i))) :
    gaussianAverage
      (stoppedCovariance σ target center (fun p => ControlledProfile.profile P Λ u d (θ,p)) 0)
      (fun z => P.coefficient (z i)) m =
      ControlledProfile.profile P Λ u d (θ,(target i,center i)) := by
  let c : Domain → ℝ := fun p => ControlledProfile.profile P Λ u d (θ,p)
  have hc : Measurable c := (ControlledProfile.profile_measurable P Λ u d).comp
    (measurable_const.prodMk measurable_id)
  have hb : ∀ p, 0 ≤ c p ∧ c p ≤ P.upper := fun p =>
    ⟨P.lower_pos.le.trans (ControlledProfile.profile_bounds P Λ u d (θ,p)).1,
      (ControlledProfile.profile_bounds P Λ u d (θ,p)).2⟩
  have hA : (stoppedCovariance σ target center c 0).PosSemidef := by
    rw [← weightedFeature_gram σ target center c hc P.upper hb hages 0]
    exact Matrix.posSemidef_gram ℝ _
  change (∫ y : State n, P.coefficient ((m+y) i)
    ∂multivariateGaussian 0 (stoppedCovariance σ target center c 0)) = _
  simp only [PiLp.add_apply]
  rw [NativeFirstWordRepresentation.coordinate_average hA i P.coefficient P.measurable (m i)]
  rw [coordinate_covariance_eq_native σ target center c hc P.upper hb i hnative ht.1
    (ht.2.trans P.horizon_le_one),hm]
  exact (ControlledProfile.profile_fixed P Λ u d θ ht (center i)).symm

end SHE.GaussianProfileBaseline
