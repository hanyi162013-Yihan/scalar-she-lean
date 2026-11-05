module

public import SHE.RandomProfileDerivative
public import SHE.ShiftedControlledScoreRates

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.ControlledScoreRates
open Set Filter MeasureTheory ProbabilityTheory Real AddCircle StoppedFourier
  ProfilePointwise ProfileStability ProfileL2 ControlledProfile
open scoped NNReal
local instance : Fact (0<2*π) := ⟨by positivity⟩
variable {W : Type*} [MeasurableSpace W] [MeasurableSpace CircleL2] [BorelSpace CircleL2]

/-- One parameter event and then one sample event suffice for EVERY
relative restart time and geometry of the actual random profile input.
The random data are included before Rademacher/Fubini is applied. -/
theorem random_shifted_sharp (P : CanonicalCovariance.ProfileParameters)
    {Λ : ℝ} (hΛ : 0≤Λ) (u d : W→CircleL2) (hu : Measurable u) (hd : Measurable d)
    (hsmallPoint : memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hsmallL2 : memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)
    (μ : Measure W) [SFinite μ] :
    ∀ᵐ θ ∂volume,∀ᵐ ω ∂μ,∀ q : ℝ,0≤q→∀ᵐ r ∂volume.restrict (Ici (0:ℝ)),
      normTwo haarAddCircle (fun x=>shiftedDerivative P Λ (u ω) (d ω) q θ (r,x))≤
        sharpConstant P (d ω)*r^((P.exponent-1)/4) := by
  filter_upwards [random_ae_derivative_sharp_power P hΛ u d hu hd hsmallPoint hsmallL2 μ] with θ hθ
  filter_upwards [hθ] with ω hω
  have hθ := hω.mono (fun _ h=>h.2)
  intro q hq
  rw [ae_restrict_iff' measurableSet_Ici] at hθ
  have hshift := (quasiMeasurePreserving_add_left volume q).ae hθ
  filter_upwards [ae_restrict_of_ae hshift,ae_restrict_mem measurableSet_Ici] with r hr hr0
  by_cases ht : 0<r
  · have he : (fun x=>shiftedDerivative P Λ (u ω) (d ω) q θ (r,x))=
        (fun x=>ControlledProfile.derivative P Λ (u ω) (d ω) ((q+r,x),θ)) := by
      funext x
      simp only [shiftedDerivative,ht,ite_true]
    rw [he]
    exact (hr (add_nonneg hq hr0)).trans (mul_le_mul_of_nonneg_left
      (rpow_le_rpow_of_nonpos ht (by linarith) (by linarith [P.exponent_le_one]))
      (sharpConstant_nonneg P (d ω)))
  · have he : (fun x=>shiftedDerivative P Λ (u ω) (d ω) q θ (r,x))=fun _=>0 := by
      funext x
      simp only [shiftedDerivative,ht,ite_false]
    rw [he]
    simp only [normTwo,zero_pow (by decide : 2≠0),integral_zero,sqrt_zero]
    exact mul_nonneg (sharpConstant_nonneg P (d ω)) (rpow_nonneg hr0 _)


end SHE.ControlledScoreRates
