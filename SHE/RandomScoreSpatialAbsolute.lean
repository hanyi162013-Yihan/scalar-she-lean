module

public import SHE.ScalarFibreRMS
public import SHE.SpatialMarkAveraging
public import SHE.ConditionalSquareL1

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2300000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.RandomScoreSpatialAbsolute
open Set Filter MeasureTheory ProfileL2
variable {Ω X W : Type*} [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace W]
variable (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure X) [IsProbabilityMeasure ν]
variable (η : Measure W) [IsProbabilityMeasure η]

/-- The actual conditional random-score envelope implies honest absolute
old-space/sample/output integrability BEFORE any signed spatial average. -/
theorem joint_integrable (F M : (Ω×X)×W→ℝ) (hF : Measurable F) (hM : Measurable M)
    (K : W→ℝ) (hKm : Measurable K) (hKi : Integrable K η) (hK : ∀ w,0≤K w)
    {C E : ℝ} (hC : 0≤C) (hE : 0≤E)
    (hMass : ∀ᵐ w ∂η,Integrable (fun z : Ω×X=>|M (z,w)|^2) (μ.prod ν) ∧
      (∫ z : Ω×X,|M (z,w)|^2 ∂μ.prod ν)≤E)
    (hPoint : ∀ᵐ w ∂η,∀ᵐ x ∂ν,
      Integrable (fun ω=>|M ((ω,x),w)|^2) μ→
        Integrable (fun ω=>|F ((ω,x),w)|^2) μ ∧
        (∫ ω,|F ((ω,x),w)|^2 ∂μ)≤C*(K w)^2*(∫ ω,|M ((ω,x),w)|^2 ∂μ)) :
    Integrable F ((μ.prod ν).prod η) ∧
      (∫ z,|F z| ∂(μ.prod ν).prod η)≤Real.sqrt (C*E)*(∫ w,K w ∂η) := by
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
  exact ConditionalSquareL1.joint_integrable (μ.prod ν) η F hF K hKi hK
    (mul_nonneg hC hE) (hs.mono (fun _ h=>h.1)) (hs.mono (fun _ h=>h.2))

end SHE.RandomScoreSpatialAbsolute
