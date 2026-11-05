module

public import SHE.ControlledScoreRates

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.ControlledScoreRates
open Set Filter MeasureTheory ProbabilityTheory Real AddCircle StoppedFourier
  ProfilePointwise ProfileStability ProfileL2 ControlledProfile
open scoped NNReal
local instance shiftedControlledScoreRates_periodPos : Fact (0<2*π) := ⟨by positivity⟩

/-- Relative-time derivative, with the irrelevant time-zero section set
to zero. The future-history measure does not see this section. -/
def shiftedDerivative (P : CanonicalCovariance.ProfileParameters) (Λ : ℝ)
    (u d : CircleL2) (q θ : ℝ) (p : ControlledProfile.Domain) : ℝ :=
  if 0<p.1 then ControlledProfile.derivative P Λ u d ((q+p.1,p.2),θ) else 0

theorem shiftedDerivative_measurable (P : CanonicalCovariance.ProfileParameters)
    {Λ : ℝ} (hΛ : 0≤Λ) (u d : CircleL2)
    (hsmall : memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (q θ : ℝ) : Measurable (shiftedDerivative P Λ u d q θ) := by
  exact Measurable.ite (measurableSet_lt measurable_const measurable_fst)
    ((derivative_measurable P hΛ u d hsmall).comp
      (((measurable_const.add measurable_fst).prodMk measurable_snd).prodMk measurable_const))
    measurable_const

theorem shiftedDerivative_coarse (P : CanonicalCovariance.ProfileParameters)
    {Λ : ℝ} (hΛ : 0≤Λ) (u d : CircleL2)
    (hsmall : memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    {q : ℝ} (hq : 0≤q) (θ : ℝ) (p : ControlledProfile.Domain) (hp : 0≤p.1) :
    |shiftedDerivative P Λ u d q θ p|≤coarseConstant P d*p.1^((P.exponent-2)/4) := by
  unfold shiftedDerivative
  split_ifs with ht
  · exact (derivative_coarse_power P hΛ u d hsmall θ (q+p.1,p.2) (add_nonneg hq hp)).trans
      (mul_le_mul_of_nonneg_left
        (rpow_le_rpow_of_nonpos ht (by linarith) (by linarith [P.exponent_le_one]))
        (coarseConstant_nonneg P d))
  · simpa only [abs_zero] using mul_nonneg (coarseConstant_nonneg P d) (rpow_nonneg hp _)

/-- One parameter event works for EVERY nonnegative restart time.
Translation of null time sets is proved before choosing that time; no
exceptional-set diagonal is used. -/
theorem ae_shiftedDerivative_sharp (P : CanonicalCovariance.ProfileParameters)
    {Λ : ℝ} (hΛ : 0≤Λ) (u d : CircleL2)
    (hsmallPoint : memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hsmallL2 : memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2) :
    ∀ᵐ θ ∂volume,∀ q : ℝ,0≤q → ∀ᵐ r ∂volume.restrict (Ici (0:ℝ)),
      normTwo haarAddCircle (fun x=>shiftedDerivative P Λ u d q θ (r,x))≤
        sharpConstant P d*r^((P.exponent-1)/4) := by
  filter_upwards [ae_derivative_sharp_power P hΛ u d hsmallPoint hsmallL2] with θ hθ
  intro q hq
  rw [ae_restrict_iff' measurableSet_Ici] at hθ
  have hshift := (quasiMeasurePreserving_add_left volume q).ae hθ
  filter_upwards [ae_restrict_of_ae hshift,ae_restrict_mem measurableSet_Ici] with r hr hr0
  by_cases ht : 0<r
  · have he : (fun x=>shiftedDerivative P Λ u d q θ (r,x))=
        (fun x=>ControlledProfile.derivative P Λ u d ((q+r,x),θ)) := by
      funext x
      simp only [shiftedDerivative,ht,ite_true]
    rw [he]
    exact (hr (add_nonneg hq hr0)).trans (mul_le_mul_of_nonneg_left
      (rpow_le_rpow_of_nonpos ht (by linarith) (by linarith [P.exponent_le_one]))
      (sharpConstant_nonneg P d))
  · have he : (fun x=>shiftedDerivative P Λ u d q θ (r,x))=fun _=>0 := by
      funext x
      simp only [shiftedDerivative,ht,ite_false]
    rw [he]
    simp only [normTwo,zero_pow (by decide : 2≠0),integral_zero,sqrt_zero]
    exact mul_nonneg (sharpConstant_nonneg P d) (rpow_nonneg hr0 _)

end SHE.ControlledScoreRates
