module

public import SHE.NativeFrozenHilbertField
public import SHE.FrozenReferenceFields
public import SHE.AdditiveHaarForcing
public import SHE.PastFrozenPrefixRows

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
namespace SHE.NativeCanonicalReferenceField
open Set MeasureTheory PredictableL2 FiniteHaar NativeHeatObservation DyadicApproximation StoppedFourier
open scoped NNReal ENNReal
local instance nativeCanonicalReferenceField_unit : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance nativeCanonicalReferenceField_period : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance nativeCanonicalReferenceField_realSigma : MeasurableSpace RealL2:=borel _
local instance nativeCanonicalReferenceField_realBorel : BorelSpace RealL2:=⟨rfl⟩
local instance nativeCanonicalReferenceField_circleSigma : MeasurableSpace CircleL2:=borel _
local instance nativeCanonicalReferenceField_circleBorel : BorelSpace CircleL2:=⟨rfl⟩
local instance nativeCanonicalReferenceField_unitSigma : MeasurableSpace CircleHeat.CircleL2:=borel _
local instance nativeCanonicalReferenceField_unitBorel : BorelSpace CircleHeat.CircleL2:=⟨rfl⟩
local instance nativeCanonicalReferenceField_columnsSigma : MeasurableSpace RealHaarIntegrand.Columns:=borel _
local instance nativeCanonicalReferenceField_columnsBorel : BorelSpace RealHaarIntegrand.Columns:=⟨rfl⟩
local instance nativeCanonicalReferenceField_circleSecond : SecondCountableTopology CircleHeat.CircleL2:=
  (_root_.fourierBasis (T:=(1:ℝ))).repr.toHomeomorph.secondCountableTopology
local instance nativeCanonicalReferenceField_realSecond : SecondCountableTopology RealL2:=
  realCircleIdentification.toHomeomorph.secondCountableTopology
variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H b v : ℝ≥0)
variable (P : CanonicalCovariance.ProfileParameters) (Λ κ : ℝ) (hκ : 0<κ) (hκP : κ<P.lower)
variable (u d : Ω→RealL2) (hu : Measurable[𝓕 v] u) (hd : Measurable[𝓕 v] d)
variable (hbH : b≤H) (hb1 : (b:ℝ)≤1)
variable (I0 I1 : StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)

def data (ω : Ω) : ControlledProfile.Inputs:=(embed (u ω),embed (d ω))

include hu hd in
theorem data_measurable : Measurable[𝓕 v] (data u d):=
  (embed.continuous.measurable.comp hu).prodMk (embed.continuous.measurable.comp hd)

def initial (θ : ℝ) (ω : Ω) : RealL2:=
  heat ((b:ℝ)-(v:ℝ)) (u ω+(θ*Real.exp (-Λ*((b:ℝ)-(v:ℝ)))) • d ω)

include hu hd in
theorem initial_measurable (θ : ℝ) : Measurable[𝓕 v] (initial (b:=b) (v:=v) (Λ:=Λ) (u:=u) (d:=d) θ) :=
  (heat ((b:ℝ)-(v:ℝ))).continuous.measurable.comp (hu.add
    ((measurable_const : Measurable[𝓕 v] (fun _ : Ω=>(θ*Real.exp (-Λ*((b:ℝ)-(v:ℝ))) : ℝ))).smul hd))

local notation "Residual" θ=>FrozenReferenceFields.field P Λ κ θ hκP v (data u d)
local notation "hResidual" θ=>FrozenReferenceFields.field_predictable 𝓕 P Λ κ θ hκP v (data u d)
  (data_measurable 𝓕 v u d hu hd)

def state (θ : ℝ) (p : ℝ≥0×Ω) : RealL2:=
  NativeFrozenHilbertField.field 𝓕 μ H b v (sub_pos.mpr hκP)
    (PastFrozenPrefixRows.residual_upper_nonneg P κ hκP) (Residual θ) (hResidual θ) hbH hb1 I1
    (initial (b:=b) (v:=v) (Λ:=Λ) (u:=u) (d:=d) θ) p+
  NativeFrozenHilbertField.noise 𝓕 μ H b v hκ hκ.le
    (fun _=>AdditiveHaarForcing.constantField κ hκ) stronglyMeasurable_const hbH hb1 I0 p.1 p.2

include hu hd in
theorem state_predictable (hb0 : 0<b) (hnull : NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (B0 B1 : ℝ≥0) (hBDG0 : StandardTerminalBDG16 I0 B0) (hBDG1 : StandardTerminalBDG16 I1 B1)
    (θ : ℝ) : StronglyMeasurable[𝓕.predictable] (state 𝓕 μ H b v P Λ κ hκ hκP u d hu hd hbH hb1 I0 I1 θ) :=
  (NativeFrozenHilbertField.field_predictable 𝓕 μ H b v (sub_pos.mpr hκP)
    (PastFrozenPrefixRows.residual_upper_nonneg P κ hκP) (Residual θ) (hResidual θ) hbH hb1 I1
    hb0 hnull B1 hBDG1 (initial (b:=b) (v:=v) (Λ:=Λ) (u:=u) (d:=d) θ) (initial_measurable (𝓕:=𝓕) (v:=v) (b:=b) (Λ:=Λ) (u:=u) (d:=d) (hu:=hu) (hd:=hd) θ)).add
    (NativeFrozenHilbertField.noise_predictable 𝓕 μ H b v hκ hκ.le
      (fun _=>AdditiveHaarForcing.constantField κ hκ) stronglyMeasurable_const hbH hb1 I0 hb0 hnull B0 hBDG0)

include hu hd in
/-- Literal jointly predictable own-profile reference field. Both
channels are from the original pair, the additive noise is common,
and the full target b is kept for every current time q. -/
theorem scalar_predictable (hb0 : 0<b) (hnull : NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (B0 B1 : ℝ≥0) (hBDG0 : StandardTerminalBDG16 I0 B0) (hBDG1 : StandardTerminalBDG16 I1 B1)
    (θ : ℝ) :
    @Measurable ((ℝ≥0×Ω)×HeatCircle) ℝ (𝓕.predictable.prod inferInstance) _
      (PredictableScalarField.nativeField (state 𝓕 μ H b v P Λ κ hκ hκP u d hu hd hbH hb1 I0 I1 θ)) :=
  PredictableScalarField.nativeField_predictable 𝓕
    (state_predictable 𝓕 μ H b v P Λ κ hκ hκP u d hu hd hbH hb1 I0 I1 hb0 hnull B0 B1 hBDG0 hBDG1 θ)

end SHE.NativeCanonicalReferenceField
