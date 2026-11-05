module
public import SHE.ControlledReferenceFamilyBackward
public import SHE.ActualUncutRemainder
public import SHE.ActualRootRemainder

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
namespace SHE.ControlledActualRemainder
open Set MeasureTheory StoppedFourier WordRecursion ControlledProfile ControlledReferenceLevel
  CutoffWordLevel CutoffWordHistories CutoffInsertionCore GaussianItoTest SmoothCylinders
  SmoothWords UniformSmooth PhysicalIto PhysicalRemainderBound PhysicalRemainderMass Filter Topology
open scoped NNReal
local instance controlledActualRemainder_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance controlledActualRemainder_sigma : MeasurableSpace CircleL2 := borel _
local instance controlledActualRemainder_borel : BorelSpace CircleL2 := ⟨rfl⟩
variable (P : CanonicalCovariance.ProfileParameters) (A : ℝ→ℝ) (hA : BoundedSmooth A)
variable (Λ θ : ℝ) (v b : ℝ≥0) (hvb : v≤b)
variable {Y : Type} [MeasurableSpace Y] {n : ℕ} (Z : VariableObservations.Family Y n)
variable (htarget : ∀ y i,(b:ℝ)≤(Z.observations y i).target)
variable (hstop : ∀ y i,(b:ℝ)≤(Z.observations y i).stop)
variable (F : Y→WordRecursion.State n→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun q : Y×WordRecursion.State n => F q.1 q.2))
local notation "Base" => ControlledReferenceFamilyLevel.level P A hA Λ θ v b hvb Z htarget hstop F hF hFm
local notation "NL" => (fun p k => UncutWordEvaluation.normalizedLevel (Base p) k)
variable (hsmall : ProfileStability.memoryConstant P.lower P.holder P.exponent*
  ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
variable {Ω : Type} [MeasurableSpace Ω]
variable (a : ℝ→ℝ) (ha : Measurable a) {M : ℝ} (hM : 0≤M) (haM : ∀z,|a z|≤M)
variable (U : Ω×ℝ→CircleL2) (X : Ω×(ℝ×HeatCircle)→ℝ)

include hsmall in
/-- Moving the reference inputs leaves the actual rough coefficient
at the fixed current state. No continuity of that coefficient is used. -/
theorem inserted_continuous (hΛ : 0≤Λ) (k : ℕ) (h : History Y k)
    (ω : Ω) (t : ℝ) (x : HeatCircle) :
    Continuous (fun p : Inputs => insertedWord ((NL p k).window h) a
      (fun s=>U (ω,s)) (fun q=>X (ω,q)) ((NL p k).test h) t x) := by
  let Z₀ := (CutoffCarriers.carrier (Base (0,0)) k).observations.observations h
  let y := observe (fun s=>U (ω,s)) (fun q=>X (ω,q)) Z₀ t
  let r := heatRow Z₀ t x
  have hH := (ControlledReferenceFamilyBackward.hessian_continuous P A hA Λ θ v b hvb
    Z htarget hstop F hF hFm hsmall hΛ k h t).comp
      (continuous_id.prodMk (continuous_const (y:=y)))
  have hc := (continuous_const (y:=a (X (ω,(t,x))))).sub
    (ControlledReferenceWindows.coefficient_inputs_continuous P Λ θ v hΛ hsmall (t,x))
  have hh := ((continuous_const (y:=(1/2:ℝ))).mul hc).mul
    ((hH.clm_apply (continuous_const (y:=r))).clm_apply (continuous_const (y:=r)))
  convert! hh using 1
  funext p
  unfold PhysicalIto.insertedWord
  rw [insertion_observe]
  change _ = (1/2:ℝ)*(a (X (ω,(t,x)))-ControlledReferenceWindows.coefficient P Λ θ v p (t,x))*_
  have he : ((NL p k).window h).observations=Z₀ :=
    ControlledReferenceFamilyBounds.carrier_observations_eq P A hA Λ θ v b hvb
      Z htarget hstop F hF hFm p (0,0) k h
  rw [he]
  rfl

def spatial (p : Inputs) (k : ℕ) (h : History Y k) (ω : Ω) (t : ℝ) : ℝ :=
  ∫x:HeatCircle,insertedWord ((NL p k).window h) a
    (fun s=>U (ω,s)) (fun q=>X (ω,q)) ((NL p k).test h) t x ∂AddCircle.haarAddCircle

include ha in
theorem spatial_measurable (hU : Measurable U) (hX : Measurable X) (p : Inputs) (k : ℕ) :
    Measurable (fun z:(History Y k×Ω)×ℝ=>
      spatial P A hA Λ θ v b hvb Z htarget hstop F hF hFm a U X p k z.1.1 z.1.2 z.2) :=
  (ActualVarianceLevel.insertion_measurable (NL p k) a ha U hU X hX).stronglyMeasurable.integral_prod_right'.measurable

include ha hM haM hsmall in
theorem spatial_continuous (hΛ : 0≤Λ) (hU : Measurable U) (hX : Measurable X)
    (k : ℕ) (h : History Y k) (ω : Ω) {t : ℝ}
    (ht : t∈Ioo (v:ℝ) ((NL (0,0) k).terminal h)) :
    Continuous (fun p : Inputs=>spatial P A hA Λ θ v b hvb Z htarget hstop F hF hFm a U X p k h ω t) := by
  obtain ⟨C,_,hC⟩ := (ControlledReferenceFamilyBounds.normalized_uniform P A hA Λ θ v b hvb Z htarget hstop F hF hFm k).norm_bound
  obtain ⟨D,_,hD⟩ := (ControlledReferenceFamilyBounds.normalized_uniform P A hA Λ θ v b hvb Z htarget hstop F hF hFm k).fderiv.norm_bound
  obtain ⟨B,hBn,hB⟩ := (ControlledReferenceFamilyBounds.normalized_uniform P A hA Λ θ v b hvb Z htarget hstop F hF hFm k).fderiv.fderiv.norm_bound
  let s := (NL (0,0) k).terminal h
  let Q := Real.sqrt ((n+k:ℕ):ℝ)*CovarianceMatrix.heatRowBound (s-t)
  let K := (1/2:ℝ)*(M+P.upper)*B*Q^2
  have hb(p:Inputs)(x:HeatCircle):‖insertedWord ((NL p k).window h) a
      (fun s=>U (ω,s)) (fun q=>X (ω,q)) ((NL p k).test h) t x‖≤K := by
    have hte:t∈Ioo ((NL p k).window h).left ((NL p k).window h).right := by
      change t∈Ioo (v:ℝ) ((CutoffCarriers.carrier (Base p) k).terminal h)
      rw [ControlledReferenceFamilyBounds.carrier_terminal_eq P A hA Λ θ v b hvb Z htarget hstop F hF hFm p (0,0) k h]
      exact ht
    have hHb:∀z,‖GaussianTaylor.hessian (backward ((NL p k).window h) ((NL p k).test h) t) z‖≤B :=
      fun z=>BackwardRegularity.gaussian_state_hessian_bound _
        (((NL p k).test_uniform.smooth h).of_le (by simp)) (hC (p,h)) (hD (p,h)) (hB (p,h)) z
    have hh:=inserted_pointwise_bound ((NL p k).window h) hM haM hBn
      (fun s=>U (ω,s)) (fun q=>X (ω,q)) hte
      (backward ((NL p k).window h) ((NL p k).test h) t) hHb x
    have hr:‖heatRow ((NL p k).observations.observations h) t x‖≤Q := by
      apply UniformInsertions.heatRow_norm_bound _ (sub_pos.mpr ht.2)
      intro i
      have htarg:=(NL p k).targets_after h i
      change (CutoffCarriers.carrier (Base p) k).terminal h≤_ at htarg
      rw [ControlledReferenceFamilyBounds.carrier_terminal_eq P A hA Λ θ v b hvb Z htarget hstop F hF hFm p (0,0) k h] at htarg
      exact sub_le_sub_right htarg t
    exact hh.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hr 2)
      (mul_nonneg (mul_nonneg (by norm_num) (add_nonneg hM P.upper_nonneg)) hBn))
  apply continuous_of_dominated (bound:=fun _:HeatCircle=>K)
  · intro p
    exact ((ActualVarianceLevel.insertion_measurable (NL p k) a ha U hU X hX).comp
      ((measurable_const (a:=((h,ω),t))).prodMk measurable_id)).aestronglyMeasurable
  · exact fun p=>Eventually.of_forall (hb p)
  · exact integrable_const _
  · exact Eventually.of_forall (inserted_continuous P A hA Λ θ v b hvb Z htarget hstop F hF hFm hsmall a U X hΛ k h ω t)

end SHE.ControlledActualRemainder
