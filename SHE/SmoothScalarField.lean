module
public import SHE.CoefficientFields
public import SHE.PredictableScalarField
public import SHE.NativeBesselFieldAE
public import SHE.SmoothCylinders
public import SHE.ScalarHeatBands
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace SHE.SmoothScalarField
open MeasureTheory AddCircle DyadicApproximation FiniteHaar SmoothCylinders
open scoped NNReal ENNReal
local instance : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance : MeasurableSpace RealL2:=borel _
local instance : BorelSpace RealL2:=⟨rfl⟩
local instance : MeasurableSpace CircleHeat.CircleL2:=borel _
local instance : BorelSpace CircleHeat.CircleL2:=⟨rfl⟩
local instance : MeasurableSpace StoppedFourier.CircleL2:=borel _
local instance : BorelSpace StoppedFourier.CircleL2:=⟨rfl⟩
local instance : SecondCountableTopology StoppedFourier.CircleL2:=
  (_root_.fourierBasis (T:=2*Real.pi)).repr.toHomeomorph.secondCountableTopology
variable {a b:ℝ→ℝ}

def cap(ha:BoundedSmooth a):ℝ:=Classical.choose ha.norm_bound
theorem bound(ha:BoundedSmooth a)(x:ℝ):|a x|≤cap ha:=by
  simpa only [cap,Real.norm_eq_abs] using Classical.choose_spec ha.norm_bound x
def value(ha:BoundedSmooth a)(U:RealL2):CircleHeat.CircleL2:=
  CoefficientFields.coefficient a ha.smooth.continuous.measurable (cap ha) (bound ha) U
theorem ae(ha:BoundedSmooth a)(U:RealL2):
    value ha U=ᵐ[haarAddCircle] (fun x=>(a (U x):ℂ)):=
  CoefficientFields.coefficient_ae a ha.smooth.continuous.measurable (cap ha) (bound ha) U

theorem eq_coefficient(ha:BoundedSmooth a)(ha':Measurable a)(B:ℝ)
    (hB:∀x,|a x|≤B)(U:RealL2):
    value ha U=CoefficientFields.coefficient a ha' B hB U:=
  Lp.ext ((ae ha U).trans (CoefficientFields.coefficient_ae a ha' B hB U).symm)

/-- Uniform scalar errors give the same honest spatial L2 error,
independently of the states and of the auxiliary field representatives. -/
theorem error(ha:BoundedSmooth a)(hb:BoundedSmooth b)(U:RealL2)
    {ε:ℝ}(hε:0≤ε)(he:∀x,|a x-b x|≤ε):‖value ha U-value hb U‖≤ε:=
  CoefficientFields.coefficient_uniform_error a b ha.smooth.continuous.measurable
    hb.smooth.continuous.measurable (cap ha) (cap hb) (bound ha) (bound hb) U hε he

theorem sub(ha:BoundedSmooth a)(hb:BoundedSmooth b)(U:RealL2):
    value (ha.sub hb) U=value ha U-value hb U:=by
  apply Lp.ext
  filter_upwards [ae (ha.sub hb) U,ae ha U,ae hb U,
    Lp.coeFn_sub (value ha U) (value hb U)] with x hab ha hb hs
  rw [hs,Pi.sub_apply,hab,ha,hb]
  simp only [Pi.sub_apply,Complex.ofReal_sub]

theorem native_ae(ha:BoundedSmooth a){P:Type*}(U:P→RealL2)(p:P):
    CircleNormalization.push (value ha (U p))=ᵐ[haarAddCircle (T:=2*Real.pi)]
      (fun x=>(a (PredictableScalarField.nativeField U (p,x)):ℂ)):=by
  have hc:=(CircleNormalization.scale_measurePreserving (2*Real.pi) 1).quasiMeasurePreserving.ae (ae ha (U p))
  filter_upwards [CircleNormalization.push_ae (value ha (U p)),hc,
    PredictableScalarField.nativeField_ae_unit U p] with x hp hc hx
  rw [hp,hc,hx]

variable {P:Type*}[MeasurableSpace P]
variable (Λ ρ:ℝ)(hΛ:1≤Λ)(hρ:0≤ρ)

/-- Exact identification of the literal native Borel Bessel realization
with the actual nonlinear spatial L2 fields at both endpoints. -/
theorem bessel_native(ha:BoundedSmooth a)(U V:P→RealL2)
    (hU:Measurable U)(hV:Measurable V)(p:P):
    NativeBesselFieldAE.value Λ ρ hΛ hρ
      (fun z:P×StoppedFourier.HeatCircle=>(a (PredictableScalarField.nativeField V z)-
        a (PredictableScalarField.nativeField U z):ℝ)) p=
      OneInputOperator.besselHalf Λ ρ hΛ hρ
        (CircleNormalization.push (value ha (V p)-value ha (U p))):=by
  let F:P×StoppedFourier.HeatCircle→ℂ:=fun z=>(a (PredictableScalarField.nativeField V z)-
    a (PredictableScalarField.nativeField U z):ℝ)
  have hF:Measurable F:=Complex.measurable_ofReal.comp
    ((ha.smooth.continuous.measurable.comp (PredictableScalarField.nativeField_measurable hV)).sub
      (ha.smooth.continuous.measurable.comp (PredictableScalarField.nativeField_measurable hU)))
  have he:CircleNormalization.push (value ha (V p)-value ha (U p))=ᵐ[haarAddCircle (T:=2*Real.pi)]
      (fun x=>F (p,x)):=by
    rw [map_sub]
    filter_upwards [Lp.coeFn_sub (CircleNormalization.push (value ha (V p)))
      (CircleNormalization.push (value ha (U p))),native_ae ha V p,native_ae ha U p] with x hs hv hu
    rw [hs,Pi.sub_apply,hv,hu]
    simp only [F,Complex.ofReal_sub]
  have hm:MemLp (fun x=>F (p,x)) 2 (haarAddCircle (T:=2*Real.pi)):=
    (Lp.memLp (CircleNormalization.push (value ha (V p)-value ha (U p)))).ae_eq he
  have hg:MeasurableL2FieldAE.squareMass (haarAddCircle (T:=2*Real.pi)) F p<⊤:=
    (MeasurableL2FieldAE.section_memLp_iff _ F hF p).mp hm
  have hr:MeasurableL2FieldAE.realization (haarAddCircle (T:=2*Real.pi)) F p=
      CircleNormalization.push (value ha (V p)-value ha (U p)):=
    Lp.ext ((MeasurableL2FieldAE.realization_ae _ F hF p hg).trans he.symm)
  change OneInputOperator.besselHalf Λ ρ hΛ hρ
    (MeasurableL2FieldAE.realization _ F p)=_
  rw [hr]

end SHE.SmoothScalarField
