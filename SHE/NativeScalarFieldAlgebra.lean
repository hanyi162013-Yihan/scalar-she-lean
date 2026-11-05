module

public import SHE.NativeFrozenSpatialObservation
public import SHE.NativeCanonicalReferenceField

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1300000
namespace SHE.NativeScalarFieldAlgebra
open MeasureTheory AddCircle StoppedFourier DyadicApproximation NativeHeatObservation FiniteHaar
open scoped NNReal ENNReal
local instance nativeScalarFieldAlgebra_period : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance nativeScalarFieldAlgebra_unit : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
variable {P : Type*}

theorem add (U V : P→RealL2) (p : P) :
    (fun x=>PredictableScalarField.nativeField (fun p=>U p+V p) (p,x))=ᵐ[haarAddCircle]
      (fun x=>PredictableScalarField.nativeField U (p,x)+PredictableScalarField.nativeField V (p,x)) := by
  have he:=(CircleNormalization.scale_measurePreserving (2*Real.pi) 1).quasiMeasurePreserving.ae
    (Lp.coeFn_add (U p) (V p))
  filter_upwards [PredictableScalarField.nativeField_ae_unit (fun p=>U p+V p) p,
    PredictableScalarField.nativeField_ae_unit U p,PredictableScalarField.nativeField_ae_unit V p,he]
    with x hu hv hw he
  rw [hu,hv,hw,he]
  rfl

theorem congr (U V : P→RealL2) (p : P) (h : U p=V p) (x : HeatCircle) :
    PredictableScalarField.nativeField U (p,x)=PredictableScalarField.nativeField V (p,x):=by
  unfold PredictableScalarField.nativeField PredictableScalarField.unitField
  rw [h]

variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H b q v : ℝ≥0)
variable {ell M : ℝ} (hell : 0<ell) (hM : 0≤M)
variable (f : ℝ≥0×Ω→EllipticField ell M) (hf : StronglyMeasurable[𝓕.predictable] f)
variable (hbH : b≤H) (hb1 : (b:ℝ)≤1) (hqb : q≤b)
variable (I : StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)
variable (J : StandardTerminalIto (C:=RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ : NativeObservationNaturality.StandardScalarNaturality I J)

include hIJ in
/-- The actual continuous Hilbert frozen martingale's spatial field is
the SAME scalar-J frozen observation. The full terminal b and the
partial current stop q remain distinct. -/
theorem noise_observation (hb0 : 0<b) (B : ℝ≥0) (hBDG : StandardTerminalBDG16 I B) :
    ∀ᵐ x : HeatCircle∂haarAddCircle,∀ᵐ ω∂μ,
      PredictableScalarField.nativeField
        (fun ω=>NativeFrozenHilbertField.noise 𝓕 μ H b v hell hM f hf hbH hb1 I q ω) (ω,x)=
      J.integral (NativeFrozenSpatialObservation.row 𝓕 μ H b q v hell hM f hf hbH hqb x 0) ω := by
  have hn:=NativeFrozenHilbertField.noise_ae 𝓕 μ H b v hell hM f hf hbH hb1 I hb0 B hBDG q hqb
  have hp:=NativeFrozenSpatialObservation.physical_observation 𝓕 μ H b q v hell hM f hf hbH hb1 hqb I J hIJ
  filter_upwards [hp] with x hx
  filter_upwards [hn,hx] with ω hn hx
  exact (congr _ _ ω hn x).trans hx

end SHE.NativeScalarFieldAlgebra
