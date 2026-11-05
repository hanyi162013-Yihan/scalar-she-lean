module

public import SHE.ControlledReferenceLevel
public import SHE.RecursiveHeatBounds
public import SHE.ControlledReferenceRecursiveBounds
public import SHE.ControlledReferenceRecursiveContinuity
public import SHE.ControlledReferenceRecursiveBackward
public import SHE.JointWordHessian
public import SHE.ControlledReferenceRecursiveFields
public import SHE.JointInsertionBounds
public import SHE.GaussianParameterContinuity

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section

namespace SHE.ControlledReferenceRecursiveRemainder
open Set MeasureTheory StoppedFourier WordRecursion ControlledProfile ControlledReferenceLevel
open CutoffWordLevel CutoffWordHistories CutoffInsertionCore GaussianItoTest SmoothCylinders SmoothWords UniformSmooth
open Classical
open scoped NNReal
local instance controlledReferenceRecursiveRemainder_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance controlledReferenceRecursiveRemainder_circleSigma : MeasurableSpace CircleL2 := borel _
local instance controlledReferenceRecursiveRemainder_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable (P : CanonicalCovariance.ProfileParameters) (A : ℝ→ℝ) (hA : BoundedSmooth A)
variable (Λ θ : ℝ) (v b : ℝ≥0) (hvb : v≤b)
variable {n : ℕ} (Z : Fin n→Observation)
variable (htarget : ∀ i,(b:ℝ)≤(Z i).target) (hstop : ∀ i,(b:ℝ)≤(Z i).stop)
variable (F : WordRecursion.State n→ℝ) (hF : BoundedSmooth F)
variable (δ : ℝ) (hδ : 0<δ)

local notation "R" => referenceData P A hA Λ θ v b hvb
local notation "L" => ControlledReferenceRecursiveBounds.level P A hA Λ θ v b hvb Z htarget hstop F hF δ hδ
variable (hsmall : ProfileStability.memoryConstant P.lower P.holder P.exponent*
  ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)

variable {Ω : Type*} [MeasurableSpace Ω]
variable (U V : Ω×ℝ→CircleL2) (XU XV : Ω×(ℝ×HeatCircle)→ℝ)

variable (hU : Measurable U) (hV : Measurable V) (hXU : Measurable XU) (hXV : Measurable XV)

def spatial (p : Inputs) (ε : ℝ≥0) (k : ℕ) (h : History Unit k) (ω : Ω) (t : ℝ) : ℝ :=
  ∫ x : HeatCircle,JointWordAnalytic.insertion (L p ε k) Λ U V XU XV h ω t x ∂AddCircle.haarAddCircle

include hsmall hU hV hXU hXV in
theorem continuous_spatial (hΛ : 0≤Λ) (ε : ℝ≥0) (k : ℕ) (h : History Unit k) (ω : Ω)
    {t : ℝ} (ht : t∈Ioo (v:ℝ) ((L (0,0) ε k).terminal h)) :
    Continuous (fun p : Inputs => spatial P A hA Λ θ v b hvb Z htarget hstop F hF δ hδ U V XU XV p ε k h ω t) := by
  obtain ⟨a,ha⟩ := hA.norm_bound
  have han : 0≤a := (norm_nonneg _).trans (ha 0)
  obtain ⟨C,hCn,hC⟩ := (ControlledReferenceRecursiveBounds.test_uniform P A hA Λ θ v b hvb Z htarget hstop F hF δ hδ k).norm_bound
  obtain ⟨D,hDn,hD⟩ := (ControlledReferenceRecursiveBounds.test_uniform P A hA Λ θ v b hvb Z htarget hstop F hF δ hδ k).fderiv.norm_bound
  obtain ⟨B,hBn,hB⟩ := (ControlledReferenceRecursiveBounds.test_uniform P A hA Λ θ v b hvb Z htarget hstop F hF δ hδ k).fderiv.fderiv.norm_bound
  let T := (L (0,0) ε k).terminal h
  let K := ((1/2:ℝ)*(a+P.upper)*B)*(Real.sqrt ((n+k:ℕ):ℝ)*CovarianceMatrix.heatRowBound (T-t))^2
  apply continuous_of_dominated (bound := fun _ : HeatCircle => K)
  · intro p
    have hm := JointWordAnalytic.insertion_measurable (L p ε k) Λ hU hV hXU hXV
    have hh := hm.comp ((measurable_const (a := ((h,ω),t))).prodMk measurable_id)
    exact hh.aestronglyMeasurable
  · intro p
    exact ae_of_all _ (fun x => by
      have hpT : (L p ε k).terminal h=T :=
        ControlledReferenceRecursiveBounds.terminal_eq P A hA Λ θ v b hvb Z htarget hstop F hF δ hδ p (0,0) ε ε k h
      have ht' : t∈Ioo ((L p ε k).window h).left ((L p ε k).window h).right := by
        change t∈Ioo (v:ℝ) ((L p ε k).terminal h)
        rw [hpT]
        exact ht
      have hH : ‖GaussianTaylor.hessian (GaussianItoTest.backward ((L p ε k).window h) ((L p ε k).test h) t)
          (JointWordAnalytic.state (L p ε k) Λ U V XU XV h ω t)‖≤B :=
        BackwardRegularity.gaussian_state_hessian_bound _ (((L p ε k).test_uniform.smooth h).of_le (by simp))
          (hC (p,(ε,h))) (hD (p,(ε,h))) (hB (p,(ε,h))) _
      have hi := JointInsertionBounds.pointwise_bound ((L p ε k).window h) han
        (fun z => by change |A z|≤a; simpa only [Real.norm_eq_abs] using ha z)
        hBn (fun z => XV (ω,z)) ht'
        (GaussianItoTest.backward ((L p ε k).window h) ((L p ε k).test h) t)
        (JointWordAnalytic.state (L p ε k) Λ U V XU XV h ω t) hH x
      have hr := UniformInsertions.heatRow_norm_bound ((L p ε k).observations.observations h) (t := t)
        (sub_pos.mpr ht.2) (fun i => by
          have hh := (L p ε k).targets_after h i
          rw [hpT] at hh
          linarith) x
      exact hi.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hr 2)
        (mul_nonneg (mul_nonneg (by norm_num) (add_nonneg han P.upper_nonneg)) hBn)))
  · exact integrable_const _
  · exact ae_of_all _ (fun x => ControlledReferenceRecursiveFields.continuous_insertion P A hA Λ θ v b hvb Z htarget hstop F hF δ hδ hsmall U V XU XV hΛ ε k h ω t x)

include hsmall hU hV hXU hXV in
/-- The full actual time-space insertion of the genuinely moving
recursive word is continuous in the two past-state inputs. The terminal
heat singularity is integrated through the real inverse-square-root
majorant; it is not replaced by an unproved uniform endpoint bound. -/
theorem continuous_remainder (hΛ : 0≤Λ) (ε : ℝ≥0) (k : ℕ) (h : History Unit k) (ω : Ω) :
    Continuous (fun p : Inputs => JointWordAnalytic.remainder (L p ε k) Λ U V XU XV h ω) := by
  obtain ⟨a,ha⟩ := hA.norm_bound
  have han : 0≤a := (norm_nonneg _).trans (ha 0)
  obtain ⟨C,hCn,hC⟩ := (ControlledReferenceRecursiveBounds.test_uniform P A hA Λ θ v b hvb Z htarget hstop F hF δ hδ k).norm_bound
  obtain ⟨D,hDn,hD⟩ := (ControlledReferenceRecursiveBounds.test_uniform P A hA Λ θ v b hvb Z htarget hstop F hF δ hδ k).fderiv.norm_bound
  obtain ⟨B,hBn,hB⟩ := (ControlledReferenceRecursiveBounds.test_uniform P A hA Λ θ v b hvb Z htarget hstop F hF δ hδ k).fderiv.fderiv.norm_bound
  let T := (L (0,0) ε k).terminal h
  let K := ((1/2:ℝ)*(a+P.upper)*B*((n+k:ℕ):ℝ))
  have hvT : (v:ℝ)≤T := (L (0,0) ε k).terminal_base h
  have he : (fun p : Inputs => JointWordAnalytic.remainder (L p ε k) Λ U V XU XV h ω)=
      fun p => ∫ t,spatial P A hA Λ θ v b hvb Z htarget hstop F hF δ hδ U V XU XV p ε k h ω t
        ∂volume.restrict (Ioc (v:ℝ) T) := by
    funext p
    unfold JointWordAnalytic.remainder
    rw [ControlledReferenceRecursiveBounds.terminal_eq P A hA Λ θ v b hvb Z htarget hstop F hF δ hδ p (0,0) ε ε k h]
    exact intervalIntegral.integral_of_le hvT
  rw [he]
  apply continuous_of_dominated (bound := fun t : ℝ => K*(1+heatConstant*(T-t)^(-(1/2:ℝ))))
  · intro p
    have hs := (JointWordAnalytic.insertion_measurable (L p ε k) Λ hU hV hXU hXV).stronglyMeasurable.integral_prod_right'
      (ν := AddCircle.haarAddCircle (T:=2*Real.pi))
    have hh := hs.measurable.comp ((measurable_const (a := (h,ω))).prodMk measurable_id)
    exact hh.aestronglyMeasurable
  · intro p
    filter_upwards [ae_restrict_mem measurableSet_Ioc,ae_restrict_of_ae (volume.ae_ne T)] with t ht hne
    have hpT : (L p ε k).terminal h=T :=
      ControlledReferenceRecursiveBounds.terminal_eq P A hA Λ θ v b hvb Z htarget hstop F hF δ hδ p (0,0) ε ε k h
    have ht' : t∈Ioo ((L p ε k).window h).left ((L p ε k).window h).right := by
      change t∈Ioo (v:ℝ) ((L p ε k).terminal h)
      rw [hpT]
      exact ⟨ht.1,lt_of_le_of_ne ht.2 hne⟩
    have hH : ‖GaussianTaylor.hessian (GaussianItoTest.backward ((L p ε k).window h) ((L p ε k).test h) t)
        (JointWordAnalytic.state (L p ε k) Λ U V XU XV h ω t)‖≤B :=
      BackwardRegularity.gaussian_state_hessian_bound _ (((L p ε k).test_uniform.smooth h).of_le (by simp))
        (hC (p,(ε,h))) (hD (p,(ε,h))) (hB (p,(ε,h))) _
    have hh := JointInsertionBounds.spatial_bound ((L p ε k).window h) han
      (fun z => by change |A z|≤a; simpa only [Real.norm_eq_abs] using ha z)
      hBn (fun z => XV (ω,z)) ht'
      (GaussianItoTest.backward ((L p ε k).window h) ((L p ε k).test h) t)
      (JointWordAnalytic.state (L p ε k) Λ U V XU XV h ω t) hH
    change ‖spatial P A hA Λ θ v b hvb Z htarget hstop F hF δ hδ U V XU XV p ε k h ω t‖≤_
    convert hh using 1
    · rfl
    · change K*(1+heatConstant*(T-t)^(-(1/2:ℝ)))=
      K*(1+heatConstant*((L p ε k).terminal h-t)^(-(1/2:ℝ)))
      rw [hpT]
  · exact (CovarianceEndpoint.endpoint_majorant_integrable (q := (v:ℝ)) (s := T) K).1
  · filter_upwards [ae_restrict_mem measurableSet_Ioc,ae_restrict_of_ae (volume.ae_ne T)] with t ht hne
    exact continuous_spatial P A hA Λ θ v b hvb Z htarget hstop F hF δ hδ hsmall U V XU XV hU hV hXU hXV
      hΛ ε k h ω ⟨ht.1,lt_of_le_of_ne ht.2 hne⟩

end SHE.ControlledReferenceRecursiveRemainder

