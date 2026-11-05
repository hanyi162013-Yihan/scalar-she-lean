module

public import SHE.SectionEnergy

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SHE.TripleEnergy
open MeasureTheory
open scoped ENNReal

/-- A jointly Borel three-parameter Hilbert field with a finite true
Tonelli energy bound is genuinely square integrable on the original
product measure, with the same real-valued energy bound. -/
theorem from_bound {X Y Z E : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure X) (ν : Measure Y) (ξ : Measure Z) [SFinite μ] [SFinite ν] [SFinite ξ]
    (F : X×(Y×Z)→E) (hF : Measurable F) {C : ℝ} (hC : 0≤C)
    (hbound : (∫⁻ x,∫⁻ y,∫⁻ z,ENNReal.ofReal (‖F (x,(y,z))‖^2) ∂ξ ∂ν ∂μ)≤ENNReal.ofReal C) :
    Integrable (fun p=>‖F p‖^2) (μ.prod (ν.prod ξ)) ∧
      (∫ p,‖F p‖^2 ∂μ.prod (ν.prod ξ))≤C := by
  have hm : Measurable (fun p=>‖F p‖^2):=hF.norm.pow_const 2
  have he : (∫⁻ p,ENNReal.ofReal (‖F p‖^2) ∂μ.prod (ν.prod ξ))=
      ∫⁻ x,∫⁻ y,∫⁻ z,ENNReal.ofReal (‖F (x,(y,z))‖^2) ∂ξ ∂ν ∂μ := by
    calc
      _=(∫⁻ x,∫⁻ yz,ENNReal.ofReal (‖F (x,yz)‖^2) ∂ν.prod ξ ∂μ):=
        lintegral_prod _ (ENNReal.measurable_ofReal.comp hm).aemeasurable
      _=_:=by
        apply lintegral_congr_ae
        filter_upwards [] with x
        exact lintegral_prod _ ((ENNReal.measurable_ofReal.comp hm).comp
          (measurable_const.prodMk measurable_id)).aemeasurable
  have hi : Integrable (fun p=>‖F p‖^2) (μ.prod (ν.prod ξ)) := by
    refine ⟨hm.aestronglyMeasurable,?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun _=>sq_nonneg _)),he]
    exact hbound.trans_lt ENNReal.ofReal_lt_top
  refine ⟨hi,(ENNReal.ofReal_le_ofReal_iff hC).mp ?_⟩
  rw [ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ (fun _=>sq_nonneg _)),he]
  exact hbound

end SHE.TripleEnergy
