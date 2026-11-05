module

public import SHE.ScalarFibreRMS
public import SHE.SpatialMarkAveraging

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2300000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.RandomScoreSpatialAverage
open Set Filter MeasureTheory ProfileL2
variable {Ω X W : Type*} [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace W]
variable (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure X) [IsProbabilityMeasure ν]
variable (η : Measure W) [IsProbabilityMeasure η]

/-- A true conditional score-mass estimate transfers through output
and old-space averaging. Random mass stays inside its sample expectation;
the old positive density is integrated once before squaring. -/
theorem average_energy (F M : (Ω×X)×W→ℝ) (hF : Measurable F) (hM : Measurable M)
    (K : W→ℝ) (hKm : Measurable K) (hKi : Integrable K η) (hK : ∀ w,0≤K w)
    {C E : ℝ} (hC : 0≤C) (hE : 0≤E)
    (hMass : ∀ᵐ w ∂η,Integrable (fun z : Ω×X=>|M (z,w)|^2) (μ.prod ν) ∧
      (∫ z : Ω×X,|M (z,w)|^2 ∂μ.prod ν)≤E)
    (hPoint : ∀ᵐ w ∂η,∀ᵐ x ∂ν,
      Integrable (fun ω=>|M ((ω,x),w)|^2) μ→
        Integrable (fun ω=>|F ((ω,x),w)|^2) μ ∧
        (∫ ω,|F ((ω,x),w)|^2 ∂μ)≤C*(K w)^2*(∫ ω,|M ((ω,x),w)|^2 ∂μ)) :
    Integrable (fun z : Ω×X=>|∫ w,F (z,w) ∂η|^2) (μ.prod ν) ∧
      (∫ z : Ω×X,|∫ w,F (z,w) ∂η|^2 ∂μ.prod ν)≤C*E*(∫ w,K w ∂η)^2 := by
  have hs : ∀ᵐ w ∂η,Integrable (fun z : Ω×X=>|F (z,w)|^2) (μ.prod ν) ∧
      (∫ z : Ω×X,|F (z,w)|^2 ∂μ.prod ν)≤(C*E)*(K w)^2 := by
    filter_upwards [hMass,hPoint] with w hw hp
    let G : Ω×X→ℝ := fun z=>M (z,w)
    let A : Ω×X→ℝ := fun z=>F (z,w)
    have hGm : Measurable G := by
      convert! hM.comp (measurable_id.prodMk measurable_const) using 1
    have hAm : Measurable A := by
      convert! hF.comp (measurable_id.prodMk measurable_const) using 1
    have hGi := hw.1
    have hsections : ∀ᵐ x ∂ν,Integrable (fun ω=>|G (ω,x)|^2) μ :=
      ((integrable_prod_iff' (((continuous_abs.measurable.comp hGm).pow_const 2).aestronglyMeasurable)).mp hGi).1
    have hpoint : ∀ᵐ x ∂ν,Integrable (fun ω=>|A (ω,x)|^2) μ ∧
        (∫ ω,|A (ω,x)|^2 ∂μ)≤(C*(K w)^2)*(ScalarFibreRMS.rms μ G x)^2 := by
      filter_upwards [hsections,hp] with x hx hpx
      have hh := hpx hx
      rw [ScalarFibreRMS.sq]
      exact hh
    have hR := ScalarFibreRMS.memLp_energy μ ν G hGm hGi
    have hb := SpatialMarkAveraging.variable_fiber_second_moment μ ν A hAm
      (ScalarFibreRMS.rms μ G) hR.1 (mul_nonneg hC (sq_nonneg _))
      (hpoint.mono (fun _ h=>h.1)) (hpoint.mono (fun _ h=>h.2))
    refine ⟨hb.1,?_⟩
    rw [hR.2] at hb
    exact (hb.2.trans (mul_le_mul_of_nonneg_left hw.2 (mul_nonneg hC (sq_nonneg _)))).trans_eq (by ring)
  have hh := WeightedSpatialMoments.nonnegative_envelope (μ.prod ν) η F hF K hKm hKi hK
    1 (by decide) (C*E) (mul_nonneg hC hE)
    (by simpa only [mul_one] using hs.mono (fun _ h=>h.1))
    (by simpa only [mul_one] using hs.mono (fun _ h=>h.2))
  simpa only [mul_one] using hh

end SHE.RandomScoreSpatialAverage
