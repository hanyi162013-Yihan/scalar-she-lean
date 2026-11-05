module

public import SHE.NativeScalarFieldAlgebra
public import SHE.NativeCurrentPathEnergy
public import SHE.NativeCorrectedCurrentFields

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1700000
namespace SHE.NativeCurrentRootIdentity
open scoped NNReal ENNReal
open Set MeasureTheory AddCircle Real NativeHeatObservation StoppedFourier DyadicApproximation
local instance nativeCurrentRootIdentity_period : Fact (0<2*π):=⟨by positivity⟩
local instance nativeCurrentRootIdentity_unit : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩

theorem sub_smul (u v : RealL2) (a : ℝ) :
    (fun x=>PredictableScalarField.nativeField (fun _ : Unit=>u-a • v) ((),x))=ᵐ[haarAddCircle]
      (fun x=>PredictableScalarField.nativeField (fun _ : Unit=>u) ((),x)-
        a*PredictableScalarField.nativeField (fun _ : Unit=>v) ((),x)):=by
  have hsub:=(CircleNormalization.scale_measurePreserving (2*π) 1).quasiMeasurePreserving.ae
    (Lp.coeFn_sub u (a • v))
  have hsmul:=(CircleNormalization.scale_measurePreserving (2*π) 1).quasiMeasurePreserving.ae
    (Lp.coeFn_smul a v)
  filter_upwards [PredictableScalarField.nativeField_ae_unit (fun _ : Unit=>u-a • v) (),
    PredictableScalarField.nativeField_ae_unit (fun _ : Unit=>u) (),
    PredictableScalarField.nativeField_ae_unit (fun _ : Unit=>v) (),hsub,hsmul] with x hw hu hv hs hm
  rw [hw,hu,hv,hs,Pi.sub_apply,hm,Pi.smul_apply]
  rfl

/-- The corrected physical Hilbert current has exactly the scalar root
used by the moving-past sharp estimate, with its old compensator intact. -/
theorem corrected_ae {τ s Λ : ℝ} (hτ : 0<τ) (hs : 0≤s) (u dc dOld : RealL2) :
    (fun x=>PredictableScalarField.nativeField (fun _ : Unit=>heat τ u+
      NativeCurrentDifference.currentDifference Λ s τ dc dOld) ((),x))=ᵐ[haarAddCircle]
      (fun x=>functional τ x u+functional τ x dc-
        (exp (-Λ*s)*(1-exp (-Λ*τ)))*functional (s+τ) x dOld):=by
  have hst:0<s+τ:=by linarith
  filter_upwards [NativeScalarFieldAlgebra.add (fun _ : Unit=>heat τ u)
      (fun _ : Unit=>NativeCurrentDifference.currentDifference Λ s τ dc dOld) (),
    sub_smul (heat τ dc) (heat (s+τ) dOld) (exp (-Λ*s)*(1-exp (-Λ*τ))),
    NativeHeatFunctionalEnergy.functional_ae hτ u,
    NativeHeatFunctionalEnergy.functional_ae hτ dc,
    NativeHeatFunctionalEnergy.functional_ae hst dOld] with x hadd hsub hu hc ho
  change _=_ at hadd
  rw [hadd]
  change PredictableScalarField.nativeField (fun _ : Unit=>heat τ u) ((),x)+
    PredictableScalarField.nativeField (fun _ : Unit=>heat τ dc-
      (exp (-Λ*s)*(1-exp (-Λ*τ))) • heat (s+τ) dOld) ((),x)=_
  rw [hsub,←hu,←hc,←ho]
  ring

variable {Ω : Type*} [MeasurableSpace Ω] (U V : ℝ≥0×Ω→RealL2) (Λ : ℝ) (v b q : ℝ≥0)

theorem actual_current_ae (hvq : v<q) (hqb : q<b) (ω : Ω) :
    (fun x=>PredictableScalarField.nativeField (NativeCorrectedCurrentFields.state U V Λ 1 v b) ((q,ω),x))=ᵐ[haarAddCircle]
      (fun x=>functional ((b:ℝ)-(q:ℝ)) x (U (q,ω))+
        functional ((b:ℝ)-(q:ℝ)) x (V (q,ω)-U (q,ω))-
          (exp (-Λ*((q:ℝ)-(v:ℝ)))*(1-exp (-Λ*((b:ℝ)-(q:ℝ)))))*
            functional ((b:ℝ)-(v:ℝ)) x (V (v,ω)-U (v,ω))):=by
  have he : NativeCorrectedCurrentFields.state U V Λ 1 v b (q,ω)=
      heat ((b:ℝ)-(q:ℝ)) (U (q,ω))+
      NativeCurrentDifference.currentDifference Λ ((q:ℝ)-(v:ℝ)) ((b:ℝ)-(q:ℝ))
        (V (q,ω)-U (q,ω)) (V (v,ω)-U (v,ω)):=by
    simp only [NativeCorrectedCurrentFields.state,one_smul,NativeCorrectedCurrentFields.pastD,
      PredictablePastParameter.held,if_pos hvq,NativeCurrentDifference.currentDifference,
      show ((q:ℝ)-(v:ℝ))+((b:ℝ)-(q:ℝ))=(b:ℝ)-(v:ℝ) by ring]
  have hh:=corrected_ae (show 0<(b:ℝ)-(q:ℝ) from sub_pos.mpr (by exact_mod_cast hqb))
    (show 0≤(q:ℝ)-(v:ℝ) from sub_nonneg.mpr (by exact_mod_cast hvq.le))
    (Λ:=Λ) (U (q,ω)) (V (q,ω)-U (q,ω)) (V (v,ω)-U (v,ω))
  simp only [show ((q:ℝ)-(v:ℝ))+((b:ℝ)-(q:ℝ))=(b:ℝ)-(v:ℝ) by ring] at hh
  refine hh.mono (fun x hx=>?_)
  change PredictableScalarField.nativeField (fun _ : Unit=>NativeCorrectedCurrentFields.state U V Λ 1 v b (q,ω)) ((),x)=_
  rw [he]
  exact hx

end SHE.NativeCurrentRootIdentity
