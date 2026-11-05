module

public import SHE.ControlledReferenceLevel

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option quotPrecheck false
noncomputable section

namespace SHE.ControlledReferenceInsertionContinuity
open Set MeasureTheory StoppedFourier WordRecursion ControlledProfile ControlledReferenceLevel
open ControlledReferenceWindows GaussianItoTest GaussianTaylor JointWordAnalytic
open Filter Topology
open scoped NNReal
local instance controlledReferenceInsertionContinuity_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance controlledReferenceInsertionContinuity_circleSigma : MeasurableSpace CircleL2 := borel _
local instance controlledReferenceInsertionContinuity_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
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
theorem continuous_insertion (ω : Ω) (t : ℝ) (x : HeatCircle) :
    Continuous (fun p : Inputs => JointWordAnalytic.insertion (L p) Λ U V XU XV () ω t x) := by
  let y := JointWordObserve.evaluate Λ (fun s => U (ω,s)) (fun s => V (ω,s))
    (fun z => XU (ω,z)) (fun z => XV (ω,z)) Z t
  let r := heatRow Z t x
  have hH := (ControlledReferenceCovariance.hessian_inputs_continuous P hΛ θ v hsmall Z b htarget
    (by exact_mod_cast hvb) hF t).comp (continuous_id.prodMk (continuous_const (y := y)))
  have hc := (continuous_const (y := A (XV (ω,(t,x))))).sub (coefficient_inputs_continuous P Λ θ v hΛ hsmall (t,x))
  have hh := ((continuous_const (y := (1/2:ℝ))).mul hc).mul ((hH.clm_apply (continuous_const (y := r))).clm_apply (continuous_const (y := r)))
  convert hh using 1
  funext p
  exact JointPhysicalInsertion.insertion_appendState A (coefficient P Λ θ v p) Z t x _ _ _

def spatial (p : Inputs) (ω : Ω) (t : ℝ) : ℝ :=
  ∫ x : HeatCircle,JointWordAnalytic.insertion (L p) Λ U V XU XV () ω t x ∂AddCircle.haarAddCircle

include hΛ hsmall in
theorem continuous_spatial (hU : Measurable U) (hV : Measurable V) (hXU : Measurable XU) (hXV : Measurable XV)
    (ω : Ω) {t : ℝ} (ht : t∈Ioo (v:ℝ) (b:ℝ)) :
    Continuous (fun p => spatial (Λ := Λ) P A hAs θ v b hvb Z htarget hstop F hF U V XU XV p ω t) := by
  obtain ⟨a,ha⟩ := hAs.norm_bound
  have han : 0≤a := (norm_nonneg _).trans (ha 0)
  obtain ⟨C,hC⟩ := hF.norm_bound
  obtain ⟨D,hD⟩ := hF.fderiv.norm_bound
  obtain ⟨B,hB⟩ := hF.fderiv.fderiv.norm_bound
  have hBn : 0≤B := (norm_nonneg _).trans (hB 0)
  let Q := Real.sqrt n*CovarianceMatrix.heatRowBound ((b:ℝ)-t)
  have hQ : 0≤Q := mul_nonneg (Real.sqrt_nonneg _) (CovarianceMatrix.heatRowBound_pos (sub_pos.mpr ht.2)).le
  let K := (1/2:ℝ)*(a+P.upper)*B*Q^2
  have hb (p : Inputs) (x : HeatCircle) :
      ‖JointWordAnalytic.insertion (L p) Λ U V XU XV () ω t x‖≤K := by
    have hH : ‖GaussianTaylor.hessian (backward (W p) F t) (JointWordAnalytic.state (L p) Λ U V XU XV () ω t)‖≤B :=
      BackwardRegularity.gaussian_state_hessian_bound _ (hF.smooth.of_le (by simp)) hC hD hB _
    have hh := JointInsertionBounds.pointwise_bound (W p) han
      (fun z => by simpa only [Real.norm_eq_abs] using ha z) hBn (fun z => XV (ω,z)) ht
      (backward (W p) F t) (JointWordAnalytic.state (L p) Λ U V XU XV () ω t) hH x
    have hr : ‖heatRow Z t x‖≤Q := UniformInsertions.heatRow_norm_bound Z (sub_pos.mpr ht.2)
      (fun i => by linarith [htarget i]) x
    exact hh.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hr 2)
      (mul_nonneg (mul_nonneg (by norm_num) (add_nonneg han P.upper_nonneg)) hBn))
  apply continuous_of_dominated (bound := fun _ : HeatCircle => K)
  · intro p
    exact ((JointWordAnalytic.insertion_measurable (L p) Λ hU hV hXU hXV).comp
      ((measurable_const (a := (((),ω),t))).prodMk measurable_id)).aestronglyMeasurable
  · exact fun p => Eventually.of_forall (hb p)
  · exact integrable_const _
  · exact Eventually.of_forall (continuous_insertion P A hAs hΛ θ v b hvb Z htarget hstop F hF hsmall U V XU XV ω t)

end SHE.ControlledReferenceInsertionContinuity
