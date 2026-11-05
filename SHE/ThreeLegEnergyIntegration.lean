module

public import SHE.NegativeThreeLeg

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000

namespace SHE.ThreeLegEnergyIntegration
open MeasureTheory AddCircle StoppedFourier
local instance threeLegEnergyIntegration_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
variable {A B Ω : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace Ω]
variable (α : Measure A) [SFinite α] (β : Measure B) [SFinite β] (μ : Measure Ω) [SFinite μ]

theorem collapse_integral (C : A×(B×(Ω×HeatCircle))→ℝ)
    (hi : Integrable C (α.prod (β.prod (μ.prod haarAddCircle)))) :
    Integrable (fun z : A×(B×Ω)=>∫ x,C (z.1,(z.2.1,(z.2.2,x))) ∂haarAddCircle)
      (α.prod (β.prod μ)) ∧
      (∫ z : A×(B×Ω),(∫ x,C (z.1,(z.2.1,(z.2.2,x))) ∂haarAddCircle) ∂α.prod (β.prod μ))=
        ∫ z,C z ∂α.prod (β.prod (μ.prod haarAddCircle)) := by
  have hp:=((MeasurePreserving.id α).prod (measurePreserving_prodAssoc β μ
      (haarAddCircle : Measure HeatCircle))).comp
    (measurePreserving_prodAssoc α (β.prod μ) (haarAddCircle : Measure HeatCircle))
  have hi' : Integrable (fun z : (A×(B×Ω))×HeatCircle=>C (z.1.1,(z.1.2.1,(z.1.2.2,z.2))))
      ((α.prod (β.prod μ)).prod haarAddCircle) := by
    convert! (hp.integrable_comp hi.aestronglyMeasurable).mpr hi using 1
  refine ⟨hi'.integral_prod_left,?_⟩
  calc
    _=∫ z : (A×(B×Ω))×HeatCircle,C (z.1.1,(z.1.2.1,(z.1.2.2,z.2)))
        ∂(α.prod (β.prod μ)).prod haarAddCircle:=(integral_prod _ hi').symm
    _=∫ z,C z ∂α.prod (β.prod (μ.prod haarAddCircle)):=by
      have he:=integral_map hp.measurable.aemeasurable
        (by rw [hp.map_eq];exact hi.aestronglyMeasurable)
      rw [hp.map_eq] at he
      convert! he.symm using 1

/-- A sectionwise physical energy comparison integrates against the
actual past/current/sample measures. No measurability of a separately
chosen lower representative or probability normalization is assumed. -/
theorem from_sections (C D : A×(B×(Ω×HeatCircle))→ℝ) (M : A×(B×Ω)→ℝ)
    (hCm : Measurable C) (hDm : Measurable D) (hMm : Measurable M)
    (hCi : Integrable C (α.prod (β.prod (μ.prod haarAddCircle))))
    (hDi : Integrable D (α.prod (β.prod (μ.prod haarAddCircle))))
    (hMi : Integrable M (α.prod (β.prod μ)))
    (hC0 : ∀ z,0≤C z) (hD0 : ∀ z,0≤D z) (hM0 : ∀ z,0≤M z)
    (K L : ℝ) (hK : 0≤K) (hL : 0≤L) (E : A→B→Ω→ℝ)
    (hb : ∀ a b,∀ᵐ ω ∂μ,E a b ω≤
      K*((∫ x,C (a,(b,(ω,x))) ∂haarAddCircle)+(∫ x,D (a,(b,(ω,x))) ∂haarAddCircle))+L*M (a,(b,ω))) :
    (∫⁻ a,∫⁻ b,∫⁻ ω,ENNReal.ofReal (E a b ω) ∂μ ∂β ∂α)≤
      ENNReal.ofReal (K*((∫ z,C z ∂α.prod (β.prod (μ.prod haarAddCircle)))+
        (∫ z,D z ∂α.prod (β.prod (μ.prod haarAddCircle))))+
          L*(∫ z,M z ∂α.prod (β.prod μ))) := by
  let c : A×(B×Ω)→ℝ:=fun z=>∫ x,C (z.1,(z.2.1,(z.2.2,x))) ∂haarAddCircle
  let d : A×(B×Ω)→ℝ:=fun z=>∫ x,D (z.1,(z.2.1,(z.2.2,x))) ∂haarAddCircle
  let U : A×(B×Ω)→ℝ:=fun z=>K*(c z+d z)+L*M z
  have hmC : Measurable (fun z : (A×(B×Ω))×HeatCircle=>C (z.1.1,(z.1.2.1,(z.1.2.2,z.2)))):=
    hCm.comp (measurable_fst.fst.prodMk (measurable_fst.snd.fst.prodMk
      (measurable_fst.snd.snd.prodMk measurable_snd)))
  have hmD : Measurable (fun z : (A×(B×Ω))×HeatCircle=>D (z.1.1,(z.1.2.1,(z.1.2.2,z.2)))):=
    hDm.comp (measurable_fst.fst.prodMk (measurable_fst.snd.fst.prodMk
      (measurable_fst.snd.snd.prodMk measurable_snd)))
  have hcm : Measurable c:=hmC.stronglyMeasurable.integral_prod_right'.measurable
  have hdm : Measurable d:=hmD.stronglyMeasurable.integral_prod_right'.measurable
  have hUm : Measurable U:=((hcm.add hdm).const_mul K).add (hMm.const_mul L)
  have hc:=collapse_integral α β μ C hCi
  have hd:=collapse_integral α β μ D hDi
  have hUi : Integrable U (α.prod (β.prod μ)):=((hc.1.add hd.1).const_mul K).add (hMi.const_mul L)
  have hU0 (z) : 0≤U z:=add_nonneg (mul_nonneg hK (add_nonneg
    (integral_nonneg (fun x=>hC0 _)) (integral_nonneg (fun x=>hD0 _)))) (mul_nonneg hL (hM0 z))
  have hUint : (∫ z,U z ∂α.prod (β.prod μ))=
      K*((∫ z,C z ∂α.prod (β.prod (μ.prod haarAddCircle)))+
        (∫ z,D z ∂α.prod (β.prod (μ.prod haarAddCircle))))+L*(∫ z,M z ∂α.prod (β.prod μ)) := by
    calc
      _=(∫ z,K*(c z+d z) ∂α.prod (β.prod μ))+(∫ z,L*M z ∂α.prod (β.prod μ)):=
        integral_add ((hc.1.add hd.1).const_mul K) (hMi.const_mul L)
      _=K*((∫ z,c z ∂α.prod (β.prod μ))+(∫ z,d z ∂α.prod (β.prod μ)))+
          L*(∫ z,M z ∂α.prod (β.prod μ)):=by
        rw [integral_const_mul,integral_const_mul]
        exact congrArg (fun r=>K*r+L*(∫ z,M z ∂α.prod (β.prod μ))) (integral_add hc.1 hd.1)
      _=_:=by rw [hc.2,hd.2]
  calc
    _≤∫⁻ a,∫⁻ b,∫⁻ ω,ENNReal.ofReal (U (a,(b,ω))) ∂μ ∂β ∂α:=by
      apply lintegral_mono
      intro a
      apply lintegral_mono
      intro b
      exact lintegral_mono_ae ((hb a b).mono (fun _ h=>ENNReal.ofReal_le_ofReal h))
    _=∫⁻ z,ENNReal.ofReal (U z) ∂α.prod (β.prod μ):=by
      calc
        _=∫⁻ a,∫⁻ z : B×Ω,ENNReal.ofReal (U (a,z)) ∂β.prod μ ∂α:=by
          apply lintegral_congr
          intro a
          exact (lintegral_prod (fun z : B×Ω=>ENNReal.ofReal (U (a,z)))
            (((ENNReal.measurable_ofReal.comp hUm).comp
              (measurable_const.prodMk measurable_id)).aemeasurable)).symm
        _=_:=(lintegral_prod (fun z=>ENNReal.ofReal (U z))
          (ENNReal.measurable_ofReal.comp hUm).aemeasurable).symm
    _=ENNReal.ofReal (∫ z,U z ∂α.prod (β.prod μ)):=
      (ofReal_integral_eq_lintegral_ofReal hUi (ae_of_all _ hU0)).symm
    _=_:=congrArg ENNReal.ofReal hUint

end SHE.ThreeLegEnergyIntegration
