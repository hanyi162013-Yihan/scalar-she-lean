module

public import SHE.ControlledReferenceInsertionContinuity

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option quotPrecheck false
noncomputable section

namespace SHE.ControlledReferenceRemainderContinuity
open Set MeasureTheory StoppedFourier WordRecursion ControlledProfile ControlledReferenceLevel
open ControlledReferenceWindows GaussianItoTest GaussianTaylor JointWordAnalytic
open Filter Topology
open scoped NNReal
local instance controlledReferenceRemainderContinuity_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance controlledReferenceRemainderContinuity_circleSigma : MeasurableSpace CircleL2 := borel _
local instance controlledReferenceRemainderContinuity_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]
variable (P : CanonicalCovariance.ProfileParameters) (A : ℝ→ℝ) (hAs : SmoothCylinders.BoundedSmooth A)
variable {Λ : ℝ} (hΛ : 0≤Λ) (θ : ℝ) (v b : ℝ≥0) (hvb : v≤b)
variable {n : ℕ} (Z : Fin n→Observation)
variable (htarget : ∀ i,(b:ℝ)≤(Z i).target) (hstop : ∀ i,(b:ℝ)≤(Z i).stop)
variable (F : WordRecursion.State n→ℝ) (hF : SmoothCylinders.BoundedSmooth F)
variable (hsmall : ProfileStability.memoryConstant P.lower P.holder P.exponent*
  ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
variable (U V : Ω×ℝ→CircleL2) (XU XV : Ω×(ℝ×HeatCircle)→ℝ)
local notation "L" p => ControlledReferenceLevel.level P A hAs Λ θ v b hvb Z htarget hstop F hF p
local notation "W" p => ControlledReferenceWindows.window P Λ θ v Z b (by exact_mod_cast hvb) htarget p

include hΛ hsmall in
/-- The genuine complete local insertion integral is continuous in
both initial reference states. Its endpoint singularity is integrated,
so no unjustified uniform pointwise bound is used at t=b. -/
theorem continuous_remainder (hU : Measurable U) (hV : Measurable V) (hXU : Measurable XU) (hXV : Measurable XV)
    (ω : Ω) : Continuous (fun p : Inputs => JointWordAnalytic.remainder (L p) Λ U V XU XV () ω) := by
  obtain ⟨a,ha⟩ := hAs.norm_bound
  have han : 0≤a := (norm_nonneg _).trans (ha 0)
  obtain ⟨C,hC⟩ := hF.norm_bound
  obtain ⟨D,hD⟩ := hF.fderiv.norm_bound
  obtain ⟨B,hB⟩ := hF.fderiv.fderiv.norm_bound
  have hBn : 0≤B := (norm_nonneg _).trans (hB 0)
  let K := ((1/2:ℝ)*(a+P.upper)*B*n)
  have hvb' : (v:ℝ)≤(b:ℝ) := by exact_mod_cast hvb
  have he : (fun p : Inputs => JointWordAnalytic.remainder (L p) Λ U V XU XV () ω)=
      fun p => ∫ t,ControlledReferenceInsertionContinuity.spatial (Λ := Λ)
        P A hAs θ v b hvb Z htarget hstop F hF U V XU XV p ω t ∂volume.restrict (Ioc (v:ℝ) (b:ℝ)) := by
    funext p
    exact intervalIntegral.integral_of_le hvb'
  rw [he]
  apply continuous_of_dominated (bound := fun t : ℝ => K*(1+heatConstant*((b:ℝ)-t)^(-(1/2:ℝ))))
  · intro p
    have hs := (JointWordAnalytic.insertion_measurable (L p) Λ hU hV hXU hXV).stronglyMeasurable.integral_prod_right' (ν := AddCircle.haarAddCircle (T := 2*Real.pi))
    exact (hs.measurable.comp ((measurable_const (a := ((),ω))).prodMk measurable_id)).aestronglyMeasurable
  · intro p
    filter_upwards [ae_restrict_mem measurableSet_Ioc,ae_restrict_of_ae (volume.ae_ne (b:ℝ))] with t ht hne
    have ht' : t∈Ioo (v:ℝ) (b:ℝ) := ⟨ht.1,lt_of_le_of_ne ht.2 hne⟩
    have hH : ‖GaussianTaylor.hessian (backward (W p) F t) (JointWordAnalytic.state (L p) Λ U V XU XV () ω t)‖≤B :=
      BackwardRegularity.gaussian_state_hessian_bound _ (hF.smooth.of_le (by simp)) hC hD hB _
    exact JointInsertionBounds.spatial_bound (W p) han (fun z => by change |A z|≤a; simpa only [Real.norm_eq_abs] using ha z)
      hBn (fun z => XV (ω,z)) ht' (backward (W p) F t) (JointWordAnalytic.state (L p) Λ U V XU XV () ω t) hH
  · exact (CovarianceEndpoint.endpoint_majorant_integrable (q := (v:ℝ)) (s := (b:ℝ)) K).1
  · filter_upwards [ae_restrict_mem measurableSet_Ioc,ae_restrict_of_ae (volume.ae_ne (b:ℝ))] with t ht hne
    exact ControlledReferenceInsertionContinuity.continuous_spatial P A hAs hΛ θ v b hvb Z htarget hstop F hF hsmall
      U V XU XV hU hV hXU hXV ω ⟨ht.1,lt_of_le_of_ne ht.2 hne⟩

end SHE.ControlledReferenceRemainderContinuity

