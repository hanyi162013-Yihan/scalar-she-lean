module
public import SHE.NativeCurrentRootIdentity
public import SHE.NativeMovingCurrentGamma
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SHE.NativeCurrentPathApplicability
open Set MeasureTheory Real NativeHeatObservation NativeMovingCurrentGamma DyadicApproximation StoppedFourier
open scoped NNReal ENNReal
local instance nativeCurrentPathApplicability_period : Fact (0<2*π):=⟨by positivity⟩
local instance nativeCurrentPathApplicability_realSigma : MeasurableSpace RealL2:=borel _
local instance nativeCurrentPathApplicability_realBorel : BorelSpace RealL2:=⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]
/-- On every covered moving window the zeroextended path used in the
sharp budget gives exactly the original corrected physical current.
The endpoint/initial clocks are not silently identified. -/
theorem corrected_ae (U V : ℝ≥0×Ω→RealL2) (Λ : ℝ) (H : ℝ≥0)
    {v h τ : ℝ} (hv:0<v) (hvh:v+h≤H) (hτ:τ∈Ioo (0:ℝ) h) (ω:Ω) :
    (fun x=>PredictableScalarField.nativeField
      (NativeCorrectedCurrentFields.state U V Λ 1 v.toNNReal (v+h).toNNReal)
      (((v+h-τ).toNNReal,ω),x))=ᵐ[AddCircle.haarAddCircle]
      (fun x=>current (fun z:ℝ×Ω=>U (z.1.toNNReal,z.2)) h (τ,((v,ω),x))+
        correction (NativePathZeroExtension.extend H (fun z=>V z-U z)) Λ h (τ,((v,ω),x))) := by
  have hq:0<v+h-τ:=by linarith [hτ.2]
  have hb:0<v+h:=by linarith [hτ.1,hτ.2]
  have hvq:v.toNNReal<(v+h-τ).toNNReal:=by
    exact_mod_cast (show (v.toNNReal:ℝ)<((v+h-τ).toNNReal:ℝ) by
      rw [Real.coe_toNNReal _ hv.le,Real.coe_toNNReal _ hq.le];linarith [hτ.2])
  have hqb:(v+h-τ).toNNReal<(v+h).toNNReal:=by
    exact_mod_cast (show ((v+h-τ).toNNReal:ℝ)<((v+h).toNNReal:ℝ) by
      rw [Real.coe_toNNReal _ hq.le,Real.coe_toNNReal _ hb.le];linarith [hτ.1])
  have he:=NativeCurrentRootIdentity.actual_current_ae U V Λ v.toNNReal (v+h).toNNReal
    (v+h-τ).toNNReal hvq hqb ω
  have hvH:v∈Ioc (0:ℝ) (H:ℝ):=⟨hv,by linarith [hτ.1,hτ.2]⟩
  have hqH:v+(h-τ)∈Ioc (0:ℝ) (H:ℝ):=⟨by linarith [hτ.2],by linarith [hτ.1]⟩
  refine he.mono (fun x hx=>?_)
  rw [hx]
  simp only [current,correction,NativeCurrentPathEnergy.direction,NativePathZeroExtension.extend,
    indicator_of_mem hvH,indicator_of_mem hqH,
    Real.coe_toNNReal _ hv.le,Real.coe_toNNReal _ hq.le,Real.coe_toNNReal _ hb.le,
    show (v+h)-(v+h-τ)=τ by ring,show (v+h-τ)-v=h-τ by ring,
    show (v+h)-v=h by ring,show h-τ+τ=h by ring,
    show v+(h-τ)=v+h-τ by ring]
  have hqH':v+h-τ∈Ioc (0:ℝ) (H:ℝ):=⟨hq,by linarith [hτ.1]⟩
  rw [indicator_of_mem hqH']
  ring
end SHE.NativeCurrentPathApplicability
