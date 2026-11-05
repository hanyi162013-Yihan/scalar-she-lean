module

public import SHEStochastic.NativeFourierHeatCoordinate
public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
public import Mathlib.MeasureTheory.Function.AEEqOfIntegral

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.ScalarFourierL1Separation
open MeasureTheory Set SHE SHE.StoppedFourier AddCircle
open scoped NNReal ENNReal

local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local notation "ν" => haarAddCircle (T := 2*Real.pi)
local notation "w" => NativeFourierHeatCoordinate.weight

variable (f : HeatCircle → ℝ) (hf : Integrable f ν)

private def complexTest : C(HeatCircle,ℂ) →L[ℂ] ℂ := by
  have hg : Integrable (fun x => (f x : ℂ)) ν := Complex.ofRealCLM.integrable_comp hf
  have hi (q : C(HeatCircle,ℂ)) : Integrable (fun x => q x*(f x : ℂ)) ν :=
    hg.bdd_mul q.continuous.aestronglyMeasurable (ae_of_all _ (ContinuousMap.norm_coe_le_norm q))
  let L : C(HeatCircle,ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun q => ∫ x,q x*(f x : ℂ) ∂ν
      map_add' := fun p q => by
        simp only [ContinuousMap.add_apply,add_mul]
        exact integral_add (hi p) (hi q)
      map_smul' := fun a p => by
        simp only [ContinuousMap.smul_apply,smul_eq_mul,RingHom.id_apply,mul_assoc]
        exact integral_const_mul _ _ }
  refine L.mkContinuous (∫ x,‖f x‖ ∂ν) ?_
  intro q
  change ‖∫ x,q x*(f x : ℂ) ∂ν‖≤(∫ x,‖f x‖ ∂ν)*‖q‖
  calc
    _ ≤ ∫ x,‖q x*(f x : ℂ)‖ ∂ν := norm_integral_le_integral_norm _
    _ ≤ ∫ x,‖q‖*‖f x‖ ∂ν := by
      apply integral_mono (hi q).norm (hf.norm.const_mul _)
      intro x
      change ‖q x*(f x : ℂ)‖≤‖q‖*‖f x‖
      rw [norm_mul,Complex.norm_real]
      exact mul_le_mul_of_nonneg_right (ContinuousMap.norm_coe_le_norm q x) (norm_nonneg _)
    _ = _ := by rw [integral_const_mul,mul_comm]

private theorem complexTest_apply (q : C(HeatCircle,ℂ)) :
    complexTest f hf q=∫ x,q x*(f x : ℂ) ∂ν := rfl

include hf in
/-- Fourier tests determine every continuous test even when the spatial
product is only integrable. -/
theorem continuous_zero
    (hre : ∀ n,∫ x,w Complex.reCLM n x*f x ∂ν=0)
    (him : ∀ n,∫ x,w Complex.imCLM n x*f x ∂ν=0)
    (p : C(HeatCircle,ℝ)) : ∫ x,p x*f x ∂ν=0 := by
  let L := complexTest f hf
  have hg : Integrable (fun x => (f x : ℂ)) ν := Complex.ofRealCLM.integrable_comp hf
  have hi (q : C(HeatCircle,ℂ)) : Integrable (fun x => q x*(f x : ℂ)) ν :=
    hg.bdd_mul q.continuous.aestronglyMeasurable (ae_of_all _ (ContinuousMap.norm_coe_le_norm q))
  have hfour (n : ℤ) : L (fourier n)=0 := by
    apply Complex.ext
    · change Complex.reCLM (L (fourier n))=0
      rw [complexTest_apply,←Complex.reCLM.integral_comp_comm (hi (fourier n))]
      have he (x : HeatCircle) : Complex.reCLM (fourier n x*(f x : ℂ)) =
          w Complex.reCLM (-n) x*f x := by
        simp [NativeFourierHeatCoordinate.weight,NativeScalarFourierWeight.value,Complex.mul_re]
      simp_rw [he]
      exact hre (-n)
    · change Complex.imCLM (L (fourier n))=0
      rw [complexTest_apply,←Complex.imCLM.integral_comp_comm (hi (fourier n))]
      have he (x : HeatCircle) : Complex.imCLM (fourier n x*(f x : ℂ)) =
          w Complex.imCLM (-n) x*f x := by
        simp [NativeFourierHeatCoordinate.weight,NativeScalarFourierWeight.value,Complex.mul_im]
      simp_rw [he]
      exact him (-n)
  have hSpan : Submodule.span ℂ (range (fourier (T := 2*Real.pi)))≤LinearMap.ker L.toLinearMap :=
    Submodule.span_le.mpr (fun q hq => by
      obtain ⟨n,rfl⟩ := hq
      exact hfour n)
  have hClosed : IsClosed (LinearMap.ker L.toLinearMap : Set C(HeatCircle,ℂ)) :=
    isClosed_eq L.continuous continuous_const
  have hall : (⊤ : Submodule ℂ C(HeatCircle,ℂ))≤LinearMap.ker L.toLinearMap := by
    rw [←span_fourier_closure_eq_top]
    exact closure_minimal hSpan hClosed
  let q : C(HeatCircle,ℂ) := ⟨fun x => (p x : ℂ),Complex.continuous_ofReal.comp p.continuous⟩
  have hq : L q=0 := hall (Submodule.mem_top : q∈⊤)
  have he := congrArg Complex.reCLM hq
  change Complex.reCLM (L q)=0 at he
  rw [complexTest_apply,←Complex.reCLM.integral_comp_comm (hi q)] at he
  simpa only [q,ContinuousMap.coe_mk,Complex.reCLM_apply,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    mul_zero,sub_zero] using he

include hf in
/-- The two real Fourier tests separate an arbitrary integrable real
function on the physical circle. -/
theorem ae_zero (hm : Measurable f)
    (hre : ∀ n,∫ x,w Complex.reCLM n x*f x ∂ν=0)
    (him : ∀ n,∫ x,w Complex.imCLM n x*f x ∂ν=0) : f =ᵐ[ν] (fun _ => 0) := by
  let p (x : HeatCircle) := max (f x) 0
  let q (x : HeatCircle) := max (-f x) 0
  have hp : Measurable p := hm.max measurable_const
  have hq : Measurable q := hm.neg.max measurable_const
  have hp₀ (x : HeatCircle) : 0≤p x := le_max_right _ _
  have hq₀ (x : HeatCircle) : 0≤q x := le_max_right _ _
  have hd (x : HeatCircle) : p x-q x=f x := by
    dsimp [p,q]
    rcases le_total (f x) 0 with h|h
    · rw [max_eq_right h,max_eq_left (by linarith)]
      ring
    · rw [max_eq_left h,max_eq_right (by linarith),sub_zero]
  have hpI : Integrable p ν := hf.sup (integrable_const 0)
  have hqI : Integrable q ν := hf.neg.sup (integrable_const 0)
  let μ := (ν).withDensity (fun x => ENNReal.ofReal (p x))
  let η := (ν).withDensity (fun x => ENNReal.ofReal (q x))
  let _ : IsFiniteMeasure μ := ⟨by
    rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
      ←ofReal_integral_eq_lintegral_ofReal hpI (ae_of_all _ hp₀)]
    exact ENNReal.ofReal_lt_top⟩
  let _ : IsFiniteMeasure η := ⟨by
    rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
      ←ofReal_integral_eq_lintegral_ofReal hqI (ae_of_all _ hq₀)]
    exact ENNReal.ofReal_lt_top⟩
  have hEq : μ=η := by
    apply Measure.ext_of_integral_eq_on_compactlySupported
    intro u
    rw [integral_withDensity_eq_integral_toReal_smul hp.ennreal_ofReal (by simp) u,
      integral_withDensity_eq_integral_toReal_smul hq.ennreal_ofReal (by simp) u]
    simp_rw [ENNReal.toReal_ofReal (hp₀ _),ENNReal.toReal_ofReal (hq₀ _),smul_eq_mul]
    have hi (r : HeatCircle → ℝ) (hr : Integrable r ν) :
        Integrable (fun x => r x*u x) ν :=
      hr.mul_bdd u.continuous.aestronglyMeasurable
        (ae_of_all _ (ContinuousMap.norm_coe_le_norm u.toContinuousMap))
    apply sub_eq_zero.mp
    rw [←integral_sub (hi p hpI) (hi q hqI)]
    have hh (x : HeatCircle) : p x*u x-q x*u x=u x*f x := by rw [←sub_mul,hd,mul_comm]
    simp_rw [hh]
    exact continuous_zero f hf hre him u.toContinuousMap
  have hpq : p =ᵐ[ν] q := by
    apply Integrable.ae_eq_of_forall_setIntegral_eq p q hpI hqI
    intro s hs _
    have he := congrArg (fun m : Measure HeatCircle => m s) hEq
    change μ s=η s at he
    rw [withDensity_apply _ hs,withDensity_apply _ hs,
      ←ofReal_integral_eq_lintegral_ofReal hpI.integrableOn (ae_of_all _ hp₀),
      ←ofReal_integral_eq_lintegral_ofReal hqI.integrableOn (ae_of_all _ hq₀)] at he
    exact (ENNReal.ofReal_eq_ofReal_iff
      (integral_nonneg hp₀) (integral_nonneg hq₀)).mp he
  filter_upwards [hpq] with x hx
  exact (hd x).symm.trans (sub_eq_zero.mpr hx)

end SHEStochastic.ScalarFourierL1Separation
