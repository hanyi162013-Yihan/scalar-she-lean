module

public import SHE.ControlledProfileFamilies
public import SHE.ControlledScoreRates

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.ControlledProfile
open Set Filter MeasureTheory ProbabilityTheory Real AddCircle StoppedFourier ProfileL2
  ProfilePointwise ProfileStability ProfileParameter ControlledScoreRates
open scoped NNReal
local instance randomProfileDerivative_periodPositive : Fact (0<2*π) := ⟨by positivity⟩
variable {W : Type*} [MeasurableSpace W] [MeasurableSpace CircleL2] [BorelSpace CircleL2]
variable (P : CanonicalCovariance.ProfileParameters) {Λ : ℝ} (hΛ : 0≤Λ)
variable (u d : W→CircleL2) (hu : Measurable u) (hd : Measurable d)
variable (hsmallPoint : memoryConstant P.lower P.holder P.exponent*
  ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
variable (hsmallL2 : memoryConstant P.lower P.holder P.exponent*
  ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)

include hΛ hu hd hsmallPoint in
theorem random_derivative_measurable :
    Measurable (fun z : (W×Domain)×ℝ=>derivative P Λ (u z.1.1) (d z.1.1) (z.1.2,z.2)) := by
  have hm : Measurable (fun z : (W×Domain)×ℝ => (((u z.1.1,d z.1.1),z.1.2),z.2)) :=
    ((((hu.prodMk hd).comp measurable_fst.fst).prodMk measurable_fst.snd).prodMk measurable_snd)
  convert! (derivative_joint_measurable P hΛ hsmallPoint).comp hm using 1

include hΛ hu hd hsmallPoint hsmallL2 in
/-- Rademacher and Fubini are applied to the ACTUAL joint random-input
family, before the sharp deterministic spatial estimate. There is no
substitution of a random input into a fixed-input exceptional set. -/
theorem random_ae_derivative_l2 (μ : Measure W) [SFinite μ] :
    ∀ᵐ θ ∂volume,∀ᵐ ω ∂μ,∀ᵐ r ∂volume.restrict (Ioc 0 P.horizon),
      MemLp (fun x=>derivative P Λ (u ω) (d ω) ((r,x),θ)) 2 haarAddCircle ∧
      normTwo haarAddCircle (fun x=>derivative P Λ (u ω) (d ω) ((r,x),θ))≤
        sharpConstant P (d ω)*r^((P.exponent-1)/4) := by
  let F : (W×Domain)→ℝ→ℝ := fun z θ=>profile P Λ (u z.1) (d z.1) (θ,z.2)
  have hm : Measurable F.uncurry := by
    convert! (random_profile_measurable P hu hd Λ).comp
      ((measurable_fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd) using 1
  have hlip (z : W×Domain) := profile_curve_lipschitz P hΛ (u z.1) (d z.1) hsmallPoint z.2
  have he := MeasuredRealCurves.ae_ae_hasDerivAt
    (μ.prod ((volume.restrict (Ioc 0 P.horizon)).prod (haarAddCircle (T:=2*π)))) hm hlip
  filter_upwards [he] with θ hθ
  filter_upwards [Measure.ae_ae_of_ae_prod hθ] with ω hω
  filter_upwards [Measure.ae_ae_of_ae_prod hω,ae_restrict_mem measurableSet_Ioc] with r hr hrmem
  exact derivative_l2_bound P hΛ (u ω) (d ω) hsmallPoint hsmallL2 hrmem hr

include hΛ hu hd hsmallPoint hsmallL2 in
/-- The sharp random-input estimate on the whole nonnegative time line,
with exact zero extension outside the native profile horizon. -/
theorem random_ae_derivative_sharp_power (μ : Measure W) [SFinite μ] :
    ∀ᵐ θ ∂volume,∀ᵐ ω ∂μ,∀ᵐ r ∂volume.restrict (Ici (0:ℝ)),
      MemLp (fun x=>derivative P Λ (u ω) (d ω) ((r,x),θ)) 2 haarAddCircle ∧
      normTwo haarAddCircle (fun x=>derivative P Λ (u ω) (d ω) ((r,x),θ))≤
        sharpConstant P (d ω)*r^((P.exponent-1)/4) := by
  filter_upwards [random_ae_derivative_l2 P hΛ u d hu hd hsmallPoint hsmallL2 μ] with θ hθ
  filter_upwards [hθ] with ω hω
  rw [ae_restrict_iff' measurableSet_Ioc] at hω
  filter_upwards [ae_restrict_of_ae hω,ae_restrict_mem measurableSet_Ici] with r hr hr0
  by_cases hp : r∈Ioc 0 P.horizon
  · exact hr hp
  · have hz : (fun x=>derivative P Λ (u ω) (d ω) ((r,x),θ))=fun _=>0 :=
      funext (fun x=>derivative_outside P Λ (u ω) (d ω) (r,x) hp θ)
    rw [hz]
    refine ⟨MemLp.zero,?_⟩
    simp only [normTwo,zero_pow (by decide : 2≠0),integral_zero,sqrt_zero]
    exact mul_nonneg (sharpConstant_nonneg P (d ω)) (rpow_nonneg hr0 _)

end SHE.ControlledProfile
