module
public import SHE.MeasurableL2Field
public import Mathlib.MeasureTheory.Function.L2Space
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace SHE.MeasurableL2FieldAE
open MeasureTheory Set
open scoped ENNReal
variable {P X:Type*}[MeasurableSpace P][MeasurableSpace X]
variable (ν:Measure X)[SFinite ν]

def squareMass (F:P×X→ℂ)(p:P):ℝ≥0∞:=∫⁻x,ENNReal.ofReal (‖F (p,x)‖^2) ∂ν

def clean (F:P×X→ℂ)(z:P×X):ℂ:=by
  classical
  exact if squareMass ν F z.1<∞ then F z else 0

theorem mass_measurable (F:P×X→ℂ)(hF:Measurable F):Measurable (squareMass ν F):=
  ((hF.norm.pow_const 2).ennreal_ofReal).lintegral_prod_right'

theorem section_memLp_iff (F:P×X→ℂ)(hF:Measurable F)(p:P):
    MemLp (fun x=>F (p,x)) 2 ν ↔ squareMass ν F p<∞:=by
  have hs:StronglyMeasurable (fun x=>F (p,x)):=
    (hF.comp (measurable_const.prodMk measurable_id)).stronglyMeasurable
  rw [memLp_two_iff_integrable_sq_norm hs.aestronglyMeasurable]
  constructor
  · intro hi
    exact (hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun x=>sq_nonneg ‖F (p,x)‖))).mp hi.hasFiniteIntegral
  · intro hi
    exact ⟨(hs.norm.pow 2).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun x=>sq_nonneg ‖F (p,x)‖))).mpr hi⟩

theorem clean_measurable (F:P×X→ℂ)(hF:Measurable F):Measurable (clean ν F):=by
  classical
  exact hF.ite ((measurableSet_lt (mass_measurable ν F hF) measurable_const).preimage measurable_fst) measurable_const

theorem clean_sections (F:P×X→ℂ)(hF:Measurable F)(p:P):MemLp (fun x=>clean ν F (p,x)) 2 ν:=by
  classical
  by_cases hp:squareMass ν F p<∞
  · simpa only [clean,if_pos hp] using (section_memLp_iff ν F hF p).mpr hp
  · simp only [clean,if_neg hp]
    exact MemLp.zero'

def realization (F:P×X→ℂ)(p:P):Lp ℂ 2 ν:=MeasurableL2Field.realizeL2 (ν:=ν) (clean ν F) p

variable [SecondCountableTopology (Lp ℂ 2 ν)][MeasurableSpace (Lp ℂ 2 ν)][BorelSpace (Lp ℂ 2 ν)]

/-- A genuine joint scalar field with only AE square-integrable sections
has a Borel map into SPATIAL L2, using zero on the measurable bad set.
This never assumes separability of an unrelated probability-L2 space. -/
theorem realization_measurable (F:P×X→ℂ)(hF:Measurable F):Measurable (realization ν F):=
  MeasurableL2Field.realizeL2_measurable (clean_measurable ν F hF) (clean_sections ν F hF)

theorem realization_ae (F:P×X→ℂ)(hF:Measurable F)(p:P)(hp:squareMass ν F p<∞):
    realization ν F p=ᵐ[ν] fun x=>F (p,x):=by
  classical
  have he:=MeasurableL2Field.realizeL2_ae (clean ν F) (clean_sections ν F hF) p
  simpa only [realization,clean,if_pos hp] using he

theorem good_ae (η:Measure P)(F:P×X→ℂ)(hF:Measurable F)
    (hE:(∫⁻p,squareMass ν F p ∂η)<∞):∀ᵐp∂η,squareMass ν F p<∞:=
  ae_lt_top (mass_measurable ν F hF) hE.ne

theorem realization_ae_ae (η:Measure P)(F:P×X→ℂ)(hF:Measurable F)
    (hE:(∫⁻p,squareMass ν F p ∂η)<∞):
    ∀ᵐp∂η,realization ν F p=ᵐ[ν] fun x=>F (p,x):=by
  filter_upwards [good_ae ν η F hF hE] with p hp
  exact realization_ae ν F hF p hp
end SHE.MeasurableL2FieldAE
