module

public import SHE.CorrelatedKernelInput
public import SHE.JointInterpolationFields

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.HeatedCurrentInput
open Set Filter MeasureTheory ProbabilityTheory AddCircle Real StoppedFourier
  NativeHeatObservation DyadicApproximation
open scoped ENNReal
local instance heatedCurrentInput_unitPositive : Fact (0<(1:ℝ)) := ⟨zero_lt_one⟩
local instance heatedCurrentInput_nativePositive : Fact (0<2*π) := ⟨by positivity⟩
local instance heatedCurrentInput_exponentFinite : Fact ((2:ENNReal)≠⊤) := ⟨by simp⟩
local instance heatedCurrentInput_realSigma : MeasurableSpace RealL2 := borel _
local instance heatedCurrentInput_realBorel : BorelSpace RealL2 := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]

attribute [local irreducible] NativeHeatObservation.functional

def field (τ : ℝ) (V : Ω→RealL2) (p : Ω×HeatCircle) : ℝ := functional τ p.2 (V p.1)

def value (τ : ℝ) (V : Ω→RealL2) (ω : Ω) : CircleL2 := embed (heat τ (V ω))

theorem field_measurable (τ : ℝ) {V : Ω→RealL2} (hV : Measurable V) :
    Measurable (field τ V) := by
  have hm : Measurable (fun p : Ω×HeatCircle=>(V p.1,(τ,p.2))) :=
    (hV.comp measurable_fst).prodMk (measurable_const.prodMk measurable_snd)
  change Measurable (fun p : Ω×HeatCircle=>functional τ p.2 (V p.1))
  exact functional_joint_measurable.comp hm

/-- The quarter-smoothed scalar input is the exact native L² heat
image of the original current difference, not a point evaluation of an
arbitrary L² representative. -/
theorem value_ae {τ : ℝ} (hτ : 0<τ) (V : Ω→RealL2) (ω : Ω) :
    (value τ V ω : HeatCircle→ℂ)=ᵐ[haarAddCircle] fun x=>(field τ V (ω,x):ℂ) := by
  have hr : ∀ᵐ x ∂(haarAddCircle (T:=1)),(realEmbed (heat τ (V ω)) x).im=0 :=
    (realEmbed_ae _).mono (fun x hx=>by rw [hx];exact Complex.ofReal_im _)
  have hn : ∀ᵐ x ∂(haarAddCircle (T:=2*π)),(value τ V ω x).im=0 :=
    CircleNormalization.push_ae_property _ (fun z : ℂ=>z.im=0) hr
  have he := heat_kernel_inner_ae hτ (embed (V ω))
  rw [←embed_heat hτ.le] at he
  filter_upwards [he,hn] with x hx hreal
  change inner ℂ (circleHeat τ x) (embed (V ω))=value τ V ω x at hx
  change value τ V ω x=(functional τ x (V ω):ℂ)
  rw [functional_apply,hx]
  exact Complex.ext (by rfl) (by simpa only [Complex.ofReal_im] using hreal)

theorem value_norm_le (τ : ℝ) (V : Ω→RealL2) (ω : Ω) : ‖value τ V ω‖≤‖V ω‖ := by
  rw [value,embed_norm]
  exact RealHeat.realHeat_contraction _ _

theorem field_bound (τ : ℝ) (V : Ω→RealL2) (ω : Ω) (x : HeatCircle) :
    |field τ V (ω,x)|≤‖circleHeat τ 0‖*‖V ω‖ := by
  have hc : ‖circleHeat τ x‖=‖circleHeat τ 0‖ :=
    (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (circleHeat_norm_sq_center τ x 0)
  exact (functional_norm_bound τ x (V ω)).trans_eq (by rw [hc])

/-- True global low-moment smallness is preserved by the right heat.
No spatial supremum estimate is used in the sharp input factor. -/
theorem expected_field_mass (μ : Measure Ω) [IsProbabilityMeasure μ]
    {τ : ℝ} (hτ : 0<τ) (V : Ω→RealL2) (hV : Measurable V)
    (hiV : Integrable (fun ω=>‖V ω‖^2) μ) :
    (∀ x,MemLp (fun ω=>field τ V (ω,x)) 2 μ) ∧
      Integrable (fun x=>∫ ω,field τ V (ω,x)^2 ∂μ) haarAddCircle ∧
      (∫ x,∫ ω,field τ V (ω,x)^2 ∂μ ∂haarAddCircle)≤∫ ω,‖V ω‖^2 ∂μ := by
  have hF := field_measurable τ hV
  have hcap : Integrable (fun ω=>(‖circleHeat τ 0‖*‖V ω‖)^2) μ := by
    simpa only [mul_pow] using hiV.const_mul (‖circleHeat τ 0‖^2)
  have hpoint (ω : Ω) (x : HeatCircle) : field τ V (ω,x)^2≤(‖circleHeat τ 0‖*‖V ω‖)^2 :=
    (sq_abs _).symm.le.trans (pow_le_pow_left₀ (abs_nonneg _) (field_bound τ V ω x) 2)
  have hprod : Integrable (fun p : Ω×HeatCircle=>field τ V p^2) (μ.prod haarAddCircle) := by
    apply (hcap.comp_fst haarAddCircle).mono' (hF.pow_const 2).aestronglyMeasurable
    exact ae_of_all _ (fun z=>by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact hpoint z.1 z.2)
  have hi (x : HeatCircle) : MemLp (fun ω=>field τ V (ω,x)) 2 μ := by
    apply (memLp_two_iff_integrable_sq
      ((hF.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable)).mpr
    apply hcap.mono' ((hF.comp (measurable_id.prodMk measurable_const)).pow_const 2).aestronglyMeasurable
    exact ae_of_all _ (fun ω=>by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact hpoint ω x)
  refine ⟨hi,hprod.integral_prod_right,?_⟩
  rw [←integral_integral_swap hprod]
  apply integral_mono hprod.integral_prod_left hiV
  intro ω
  have he : (∫ x,field τ V (ω,x)^2 ∂haarAddCircle)=‖value τ V ω‖^2 := by
    rw [L2_norm_sq_eq_integral]
    apply integral_congr_ae
    filter_upwards [value_ae hτ V ω] with x hx
    rw [hx,Complex.norm_real,Real.norm_eq_abs,sq_abs]
  change (∫ x,field τ V (ω,x)^2 ∂haarAddCircle)≤‖V ω‖^2
  rw [he]
  exact pow_le_pow_left₀ (norm_nonneg _) (value_norm_le τ V ω) 2

end SHE.HeatedCurrentInput
