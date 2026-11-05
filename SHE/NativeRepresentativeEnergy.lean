module

public import SHE.PredictableScalarField
public import SHE.ProcessEnergy

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section

namespace SHE.NativeRepresentativeEnergy
open MeasureTheory AddCircle NativeHeatObservation PredictableL2 DyadicApproximation
open scoped ENNReal NNReal
local instance nativeRepresentativeEnergy_unitPositive : Fact (0<(1:ℝ)) := ⟨by norm_num⟩
local instance nativeRepresentativeEnergy_nativePositive : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance nativeRepresentativeEnergy_realSigma : MeasurableSpace RealL2 := borel _
local instance nativeRepresentativeEnergy_realBorel : BorelSpace RealL2 := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]

/-- The actual jointly chosen scalar representatives preserve the TRUE
Hilbert difference energy on the native circle, including zero heat age. -/
theorem section_energy (U V : Ω→RealL2) (ω : Ω) :
    (∫x:StoppedFourier.HeatCircle,
      (PredictableScalarField.nativeField V (ω,x)-PredictableScalarField.nativeField U (ω,x))^2
        ∂haarAddCircle)=‖V ω-U ω‖^2 := by
  have he := (CircleNormalization.scale_measurePreserving (2*Real.pi) 1).quasiMeasurePreserving.ae
    (Lp.coeFn_sub (V ω) (U ω))
  calc
    _=(∫x:StoppedFourier.HeatCircle,
        ((V ω-U ω) (CircleNormalization.scale (2*Real.pi) 1 x))^2 ∂haarAddCircle) := by
      apply integral_congr_ae
      filter_upwards [PredictableScalarField.nativeField_ae_unit V ω,
        PredictableScalarField.nativeField_ae_unit U ω,he] with x hv hu hx
      simp only [Pi.sub_apply] at hx
      rw [hv,hu,hx]
    _=(∫x:AddCircle (1:ℝ),((V ω-U ω) x)^2 ∂haarAddCircle) := by
      convert! (CircleNormalization.scale_measurePreserving (2*Real.pi) 1).integral_comp
        (CircleNormalization.scaleMeasurableEquiv (2*Real.pi) 1).measurableEmbedding
        (fun x:AddCircle (1:ℝ)=>((V ω-U ω) x)^2) using 1
    _=‖V ω-U ω‖^2 := by
      simpa only [Real.norm_eq_abs,sq_abs] using (realLp_norm_sq (V ω-U ω)).symm

theorem section_integrable (U V : Ω→RealL2) (ω : Ω) :
    Integrable (fun x:StoppedFourier.HeatCircle=>
      (PredictableScalarField.nativeField V (ω,x)-PredictableScalarField.nativeField U (ω,x))^2)
        haarAddCircle := by
  have he := (CircleNormalization.scale_measurePreserving (2*Real.pi) 1).quasiMeasurePreserving.ae
    (Lp.coeFn_sub (V ω) (U ω))
  have hi : Integrable (fun x:AddCircle (1:ℝ)=>((V ω-U ω) x)^2) haarAddCircle :=
    (Lp.memLp (V ω-U ω)).integrable_sq
  have ht := ((CircleNormalization.scale_measurePreserving (2*Real.pi) 1).integrable_comp
    hi.aestronglyMeasurable).mpr hi
  apply ht.congr
  filter_upwards [PredictableScalarField.nativeField_ae_unit V ω,
    PredictableScalarField.nativeField_ae_unit U ω,he] with x hv hu hx
  simp only [Function.comp_apply,Pi.sub_apply] at hx ⊢
  rw [hv,hu,hx]

/-- Tonelli/Fubini identifies the sample/spatial scalar input with the
actual global Hilbert energy; the chosen representatives introduce no
additional moment assumption or pointwise spatial bound. -/
theorem product_energy (μ : Measure Ω) [SFinite μ]
    (U V : Ω→RealL2) (hU : Measurable U) (hV : Measurable V)
    (hi : Integrable (fun ω=>‖V ω-U ω‖^2) μ) :
    let f:=fun y:Ω×StoppedFourier.HeatCircle=>
      PredictableScalarField.nativeField V y-PredictableScalarField.nativeField U y
    Integrable (fun y=>f y^2) (μ.prod haarAddCircle) ∧
      (∫y,f y^2 ∂μ.prod haarAddCircle)=(∫ω,‖V ω-U ω‖^2 ∂μ) := by
  intro f
  have hm : Measurable (fun y=>f y^2) :=
    ((PredictableScalarField.nativeField_measurable hV).sub
      (PredictableScalarField.nativeField_measurable hU)).pow_const 2
  have hsec : ∀ω,Integrable (fun x=>f (ω,x)^2) haarAddCircle :=section_integrable U V
  have hs : ∀ω,(∫x,f (ω,x)^2 ∂haarAddCircle)=‖V ω-U ω‖^2 :=section_energy U V
  have hp : Integrable (fun y=>f y^2) (μ.prod haarAddCircle) := by
    apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
    refine ⟨ae_of_all _ hsec,?_⟩
    simpa only [Real.norm_eq_abs,abs_pow,sq_abs,hs] using hi
  refine ⟨hp,?_⟩
  rw [integral_prod _ hp]
  exact integral_congr_ae (ae_of_all _ hs)

end SHE.NativeRepresentativeEnergy
