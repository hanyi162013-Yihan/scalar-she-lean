module

public import SHE.HeatAgeContinuity
public import SHE.CovarianceEndpointPath

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section

namespace SHE.CovarianceTargetContinuity
open Set Filter MeasureTheory StoppedFourier WordRecursion CovarianceMatrix CovarianceEndpoint
open scoped Topology Matrix.Norms.Elementwise
local instance covarianceTargetContinuity_periodPositive : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
variable {X : Type*} [TopologicalSpace X] [FirstCountableTopology X] {n : ℕ}

theorem continuous_heatRow (Z : X → Fin n → Observation) (centers : Fin n → HeatCircle)
    (hT : ∀ i,Continuous (fun p => (Z p i).target)) (hx : ∀ p i,(Z p i).center=centers i)
    {s t : ℝ} (ht : t < s) (hgap : ∀ p i,s ≤ (Z p i).target) (x : HeatCircle) (i : Fin n) :
    Continuous (fun p => heatRow (Z p) t x i) := by
  have he : (fun p => heatRow (Z p) t x i)=
      fun p => (ProfileVariance.heatPhysical ((Z p i).target-t) (centers i) x).re := by
    funext p
    change (ProfileVariance.heatPhysical ((Z p i).target-t) (Z p i).center x).re=_
    rw [hx]
  rw [he]
  apply continuous_iff_continuousAt.mpr
  intro p
  have ha : 0 < (Z p i).target-t := by linarith [hgap p i]
  exact Complex.continuous_re.continuousAt.comp
    ((HeatAgeContinuity.continuousAt_heatPhysical_age ha _ _).comp
      (f := fun p => (Z p i).target-t) ((hT i).sub continuous_const).continuousAt)

theorem continuous_covarianceDensity (c : ℝ × HeatCircle → ℝ) (hc : Measurable c)
    (Z : X → Fin n → Observation) (centers : Fin n → HeatCircle)
    (hT : ∀ i,Continuous (fun p => (Z p i).target)) (hx : ∀ p i,(Z p i).center=centers i)
    {M s t : ℝ} (hM : 0 ≤ M) (ht : t < s) (hgap : ∀ p i,s ≤ (Z p i).target)
    (hb : ∀ x,|c (t,x)| ≤ M) (i j : Fin n) :
    Continuous (fun p => covarianceDensity c (Z p) t i j) := by
  apply continuous_of_dominated (bound := fun _ : HeatCircle => M*(heatRowBound (s-t))^2)
  · intro p
    exact (covariance_spatial_integrable c hc (Z p) (sub_pos.mpr ht) hM
      (fun i => by linarith [hgap p i]) (le_rfl : t ≤ t) hb i j).aestronglyMeasurable
  · intro p
    exact ae_of_all _ (fun x => by
      rw [Real.norm_eq_abs]
      exact density_integrand_bound c (Z p) (sub_pos.mpr ht) hM
        (fun i => by linarith [hgap p i]) (le_rfl : t ≤ t) hb i j x)
  · exact integrable_const _
  · exact ae_of_all _ (fun x =>
      (continuous_const.mul (continuous_heatRow Z centers hT hx ht hgap x i)).mul
        (continuous_heatRow Z centers hT hx ht hgap x j))

/-- Actual covariance entries are continuous as the original targets
move, even when their limiting target equals the terminal time. The
integrable inverse-square-root endpoint majorant is proved, not assumed. -/
theorem continuous_covariance (c : ℝ × HeatCircle → ℝ) (hc : Measurable c)
    (Z : X → Fin n → Observation) (centers : Fin n → HeatCircle)
    (hT : ∀ i,Continuous (fun p => (Z p i).target)) (hx : ∀ p i,(Z p i).center=centers i)
    {M q s : ℝ} (hM : 0 ≤ M) (hqs : q ≤ s) (hgap : ∀ p i,s ≤ (Z p i).target)
    (hb : ∀ t ∈ Icc q s,∀ x,|c (t,x)| ≤ M) :
    Continuous (fun p => covariance c (Z p) q s) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  have he : (fun p => covariance c (Z p) q s i j)=
      fun p => ∫ t,covarianceDensity c (Z p) t i j ∂volume.restrict (Ioc q s) := by
    funext p
    exact intervalIntegral.integral_of_le hqs
  rw [he]
  apply continuous_of_dominated (bound := fun t : ℝ => M*(1+heatConstant*(s-t)^(-(1/2:ℝ))))
  · intro p
    exact (covarianceDensity_measurable c hc (Z p) i j).aestronglyMeasurable
  · intro p
    filter_upwards [ae_restrict_mem measurableSet_Ioc,ae_restrict_of_ae (volume.ae_ne s)] with t ht hts
    rw [Real.norm_eq_abs]
    exact covarianceDensity_endpoint_bound c hc (Z p) hM (lt_of_le_of_ne ht.2 hts) (hgap p)
      (hb t ⟨ht.1.le,ht.2⟩) i j
  · have hi := (endpoint_majorant_integrable (q := q) (s := s) M).1
    exact hi
  · filter_upwards [ae_restrict_mem measurableSet_Ioc,ae_restrict_of_ae (volume.ae_ne s)] with t ht hts
    exact continuous_covarianceDensity c hc Z centers hT hx hM (lt_of_le_of_ne ht.2 hts) hgap
      (hb t ⟨ht.1.le,ht.2⟩) i j

end SHE.CovarianceTargetContinuity
