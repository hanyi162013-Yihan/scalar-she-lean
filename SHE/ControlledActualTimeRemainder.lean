module
public import SHE.ControlledActualRemainder

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
namespace SHE.ControlledActualTimeRemainder
open Set MeasureTheory StoppedFourier WordRecursion ControlledProfile ControlledReferenceLevel
  CutoffWordLevel CutoffWordHistories CutoffInsertionCore GaussianItoTest SmoothCylinders
  SmoothWords UniformSmooth PhysicalIto PhysicalRemainderBound PhysicalRemainderMass Filter Topology
open scoped NNReal
local instance controlledActualTimeRemainder_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance controlledActualTimeRemainder_sigma : MeasurableSpace CircleL2 := borel _
local instance controlledActualTimeRemainder_borel : BorelSpace CircleL2 := ⟨rfl⟩
variable (P : CanonicalCovariance.ProfileParameters) (A : ℝ→ℝ) (hA : BoundedSmooth A)
variable (Λ θ : ℝ) (v b : ℝ≥0) (hvb : v≤b)
variable {Y : Type} [MeasurableSpace Y] {n : ℕ} (Z : VariableObservations.Family Y n)
variable (htarget : ∀ y i,(b:ℝ)≤(Z.observations y i).target)
variable (hstop : ∀ y i,(b:ℝ)≤(Z.observations y i).stop)
variable (F : Y→WordRecursion.State n→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun q : Y×WordRecursion.State n => F q.1 q.2))
local notation "Base" => ControlledReferenceFamilyLevel.level P A hA Λ θ v b hvb Z htarget hstop F hF hFm
local notation "NL" => (fun p k => UncutWordEvaluation.normalizedLevel (Base p) k)
variable {Ω : Type} [MeasurableSpace Ω]
variable (a : ℝ→ℝ) (ha : Measurable a) {M : ℝ} (hM : 0≤M) (haM : ∀z,|a z|≤M)
variable (U : Ω×ℝ→CircleL2) (X : Ω×(ℝ×HeatCircle)→ℝ)

include hM haM in
theorem spatial_bound (k : ℕ) : ∃K:ℝ,0≤K∧∀p:Inputs,∀h ω t,
    t∈Ioo (v:ℝ) ((NL (0,0) k).terminal h)→
      ‖ControlledActualRemainder.spatial P A hA Λ θ v b hvb Z htarget hstop F hF hFm a U X p k h ω t‖≤
        K*(1+heatConstant*((NL (0,0) k).terminal h-t)^(-(1/2:ℝ))) := by
  obtain ⟨C,_,hC⟩ := (ControlledReferenceFamilyBounds.normalized_uniform P A hA Λ θ v b hvb Z htarget hstop F hF hFm k).norm_bound
  obtain ⟨D,_,hD⟩ := (ControlledReferenceFamilyBounds.normalized_uniform P A hA Λ θ v b hvb Z htarget hstop F hF hFm k).fderiv.norm_bound
  obtain ⟨B,hBn,hB⟩ := (ControlledReferenceFamilyBounds.normalized_uniform P A hA Λ θ v b hvb Z htarget hstop F hF hFm k).fderiv.fderiv.norm_bound
  let K:=(1/2:ℝ)*(M+P.upper)*B*((n+k:ℕ):ℝ)
  refine ⟨K,mul_nonneg (mul_nonneg (mul_nonneg (by norm_num)
    (add_nonneg hM P.upper_nonneg)) hBn) (Nat.cast_nonneg _),fun p h ω t ht=>?_⟩
  have hte:t∈Ioo ((NL p k).window h).left ((NL p k).window h).right := by
    change t∈Ioo (v:ℝ) ((CutoffCarriers.carrier (Base p) k).terminal h)
    rw [ControlledReferenceFamilyBounds.carrier_terminal_eq P A hA Λ θ v b hvb Z htarget hstop F hF hFm p (0,0) k h]
    exact ht
  have hHb:∀z,‖GaussianTaylor.hessian (backward ((NL p k).window h) ((NL p k).test h) t) z‖≤B :=
    fun z=>BackwardRegularity.gaussian_state_hessian_bound _
      (((NL p k).test_uniform.smooth h).of_le (by simp)) (hC (p,h)) (hD (p,h)) (hB (p,h)) z
  have hh:=inserted_spatial_norm_bound ((NL p k).window h) hM haM hBn
    (fun s=>U (ω,s)) (fun q=>X (ω,q)) hte
    (backward ((NL p k).window h) ((NL p k).test h) t) hHb
  change ‖ControlledActualRemainder.spatial P A hA Λ θ v b hvb Z htarget hstop F hF hFm a U X p k h ω t‖≤
    K*(1+heatConstant*((CutoffCarriers.carrier (Base p) k).terminal h-t)^(-(1/2:ℝ))) at hh
  rw [ControlledReferenceFamilyBounds.carrier_terminal_eq P A hA Λ θ v b hvb Z htarget hstop F hF hFm p (0,0) k h] at hh
  exact hh

include hM haM in
/-- Fixed smooth-depth constants are uniform over all past inputs;
the actual bracket needs only its pointwise variance bound. -/
theorem remainder_bound (k : ℕ) : ∃K:ℝ,0≤K∧∀p:Inputs,∀h ω,
    ‖wordRemainder ((NL p k).window h) a (fun t=>U (ω,t)) (fun q=>X (ω,q)) ((NL p k).test h)‖≤K := by
  obtain ⟨C,_,hC⟩ := (ControlledReferenceFamilyBounds.normalized_uniform P A hA Λ θ v b hvb Z htarget hstop F hF hFm k).norm_bound
  obtain ⟨D,_,hD⟩ := (ControlledReferenceFamilyBounds.normalized_uniform P A hA Λ θ v b hvb Z htarget hstop F hF hFm k).fderiv.norm_bound
  obtain ⟨B,hBn,hB⟩ := (ControlledReferenceFamilyBounds.normalized_uniform P A hA Λ θ v b hvb Z htarget hstop F hF hFm k).fderiv.fderiv.norm_bound
  let K:=((1/2:ℝ)*(M+P.upper)*B*((n+k:ℕ):ℝ))*heatMass (b:ℝ)
  refine ⟨K,mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num)
    (add_nonneg hM P.upper_nonneg)) hBn) (Nat.cast_nonneg _))
    (heatMass_nonneg b.coe_nonneg),fun p h ω=>?_⟩
  exact remainder_horizon_bound ((NL p k).window h) hM haM hBn le_rfl
    v.coe_nonneg ((NL p k).terminal_horizon h) (fun t=>U (ω,t)) (fun q=>X (ω,q))
    (((NL p k).test_uniform.smooth h).of_le (by simp)) (hC (p,h)) (hD (p,h)) (hB (p,h))

variable (hsmall : ProfileStability.memoryConstant P.lower P.holder P.exponent*
  ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)

include ha hM haM hsmall in
/-- The full ordinary-U remainder is continuous in the reference
past inputs after integrating the genuine endpoint singularity. -/
theorem remainder_continuous (hΛ : 0≤Λ) (hU : Measurable U) (hX : Measurable X)
    (k : ℕ) (h : History Y k) (ω : Ω) :
    Continuous (fun p:Inputs=>wordRemainder ((NL p k).window h) a
      (fun t=>U (ω,t)) (fun q=>X (ω,q)) ((NL p k).test h)) := by
  obtain ⟨K,hK,hKb⟩:=spatial_bound P A hA Λ θ v b hvb Z htarget hstop F hF hFm a hM haM U X k
  let s:=(NL (0,0) k).terminal h
  have hs:(v:ℝ)≤s:=(NL (0,0) k).terminal_base h
  have he:(fun p:Inputs=>wordRemainder ((NL p k).window h) a
      (fun t=>U (ω,t)) (fun q=>X (ω,q)) ((NL p k).test h))=
      fun p=>∫t,ControlledActualRemainder.spatial P A hA Λ θ v b hvb Z htarget hstop F hF hFm a U X p k h ω t
        ∂volume.restrict (Ioc (v:ℝ) s) := by
    funext p
    change (∫t in (v:ℝ)..(CutoffCarriers.carrier (Base p) k).terminal h,
      ControlledActualRemainder.spatial P A hA Λ θ v b hvb Z htarget hstop F hF hFm a U X p k h ω t)=_
    rw [ControlledReferenceFamilyBounds.carrier_terminal_eq P A hA Λ θ v b hvb Z htarget hstop F hF hFm p (0,0) k h]
    exact intervalIntegral.integral_of_le hs
  rw [he]
  apply continuous_of_dominated (bound:=fun t:ℝ=>K*(1+heatConstant*(s-t)^(-(1/2:ℝ))))
  · intro p
    have hp:Measurable (fun t:ℝ=>((h,ω),t)):=measurable_const.prodMk measurable_id
    have hm := (ControlledActualRemainder.spatial_measurable P A hA Λ θ v b hvb Z htarget hstop F hF hFm a ha U X hU hX p k).comp hp
    exact hm.aestronglyMeasurable
  · intro p
    filter_upwards [ae_restrict_mem measurableSet_Ioc,ae_restrict_of_ae (volume.ae_ne s)] with t ht hts
    exact hKb p h ω t ⟨ht.1,lt_of_le_of_ne ht.2 hts⟩
  · exact (CovarianceEndpoint.endpoint_majorant_integrable (q:=(v:ℝ)) (s:=s) K).1
  · filter_upwards [ae_restrict_mem measurableSet_Ioc,ae_restrict_of_ae (volume.ae_ne s)] with t ht hts
    exact ControlledActualRemainder.spatial_continuous P A hA Λ θ v b hvb Z htarget hstop F hF hFm hsmall
      a ha hM haM U X hΛ hU hX k h ω ⟨ht.1,lt_of_le_of_ne ht.2 hts⟩

include ha hM haM hsmall in
theorem value_continuous (hΛ : 0≤Λ) (hU : Measurable U) (hX : Measurable X)
    (k : ℕ) (h : History Y k) (ω : Ω) :
    Continuous (fun p:Inputs=>ActualUncutRemainder.value (Base p) a U X k h ω) := by
  have hc:=(remainder_continuous P A hA Λ θ v b hvb Z htarget hstop F hF hFm
    a ha hM haM U X hsmall hΛ hU hX k h ω).const_smul (UncutSmoothWords.weight (Base (0,0)) k h)
  convert! hc using 1
  funext p
  rw [ActualUncutRemainder.value,ControlledReferenceFamilyBounds.weight_eq P A hA Λ θ v b hvb Z htarget hstop F hF hFm p (0,0) k h]
  rfl

end SHE.ControlledActualTimeRemainder
