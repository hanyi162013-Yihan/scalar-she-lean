module

public import SHE.CovarianceTargetContinuity

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.CovarianceCoefficientContinuity
open Set Filter MeasureTheory StoppedFourier WordRecursion CovarianceMatrix CovarianceEndpoint
open scoped Topology Matrix.Norms.Elementwise
local instance covarianceCoefficientContinuity_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
variable {X : Type*} [TopologicalSpace X] [FirstCountableTopology X] {n : ℕ}

theorem continuous_density (c : X→ℝ×HeatCircle→ℝ) (hc : ∀ p,Measurable (c p))
    (hcont : ∀ z,Continuous (fun p => c p z)) (Z : Fin n→Observation)
    {M s t : ℝ} (hM : 0≤M) (ht : t<s) (hgap : ∀ i,s≤(Z i).target)
    (hb : ∀ p x,|c p (t,x)|≤M) (i j : Fin n) :
    Continuous (fun p => covarianceDensity (c p) Z t i j) := by
  apply continuous_of_dominated (bound := fun _ : HeatCircle => M*(heatRowBound (s-t))^2)
  · intro p
    exact (covariance_spatial_integrable (c p) (hc p) Z (sub_pos.mpr ht) hM
      (fun i => by linarith [hgap i]) (le_rfl : t≤t) (hb p) i j).aestronglyMeasurable
  · intro p
    exact ae_of_all _ (fun x => by
      rw [Real.norm_eq_abs]
      exact density_integrand_bound (c p) Z (sub_pos.mpr ht) hM
        (fun i => by linarith [hgap i]) (le_rfl : t≤t) (hb p) i j x)
  · exact integrable_const _
  · exact ae_of_all _ (fun x => ((hcont (t,x)).mul continuous_const).mul continuous_const)

/-- Genuine continuity of the full physical covariance in a bounded
pointwise-continuous coefficient family. The terminal heat singularity
is controlled by the actual integrable inverse-square-root majorant. -/
theorem continuous_covariance (c : X→ℝ×HeatCircle→ℝ) (hc : ∀ p,Measurable (c p))
    (hcont : ∀ z,Continuous (fun p => c p z)) (Z : Fin n→Observation)
    {M q s : ℝ} (hM : 0≤M) (hqs : q≤s) (hgap : ∀ i,s≤(Z i).target)
    (hb : ∀ p,∀ t∈Icc q s,∀ x,|c p (t,x)|≤M) :
    Continuous (fun p => covariance (c p) Z q s) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  have he : (fun p => covariance (c p) Z q s i j)=
      fun p => ∫ t,covarianceDensity (c p) Z t i j ∂volume.restrict (Ioc q s) := by
    funext p
    exact intervalIntegral.integral_of_le hqs
  rw [he]
  apply continuous_of_dominated (bound := fun t : ℝ => M*(1+heatConstant*(s-t)^(-(1/2:ℝ))))
  · intro p
    exact (covarianceDensity_measurable (c p) (hc p) Z i j).aestronglyMeasurable
  · intro p
    filter_upwards [ae_restrict_mem measurableSet_Ioc,ae_restrict_of_ae (volume.ae_ne s)] with t ht hne
    rw [Real.norm_eq_abs]
    exact covarianceDensity_endpoint_bound (c p) (hc p) Z hM (lt_of_le_of_ne ht.2 hne) hgap
      (hb p t ⟨ht.1.le,ht.2⟩) i j
  · exact (endpoint_majorant_integrable (q := q) (s := s) M).1
  · filter_upwards [ae_restrict_mem measurableSet_Ioc,ae_restrict_of_ae (volume.ae_ne s)] with t ht hne
    exact continuous_density c hc hcont Z hM (lt_of_le_of_ne ht.2 hne) hgap
      (fun p => hb p t ⟨ht.1.le,ht.2⟩) i j

end SHE.CovarianceCoefficientContinuity
