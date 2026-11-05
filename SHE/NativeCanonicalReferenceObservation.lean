module

public import SHE.NativeCanonicalReferenceField
public import SHE.NativeScalarProductAlgebra

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
namespace SHE.NativeCanonicalReferenceObservation
open Set MeasureTheory PredictableL2 FiniteHaar NativeHeatObservation DyadicApproximation StoppedFourier
open scoped NNReal ENNReal
local instance nativeCanonicalReferenceObservation_unit : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance nativeCanonicalReferenceObservation_period : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance nativeCanonicalReferenceObservation_realSigma : MeasurableSpace RealL2:=borel _
local instance nativeCanonicalReferenceObservation_realBorel : BorelSpace RealL2:=⟨rfl⟩
local instance nativeCanonicalReferenceObservation_circleSigma : MeasurableSpace CircleL2:=borel _
local instance nativeCanonicalReferenceObservation_circleBorel : BorelSpace CircleL2:=⟨rfl⟩
local instance nativeCanonicalReferenceObservation_unitSigma : MeasurableSpace CircleHeat.CircleL2:=borel _
local instance nativeCanonicalReferenceObservation_unitBorel : BorelSpace CircleHeat.CircleL2:=⟨rfl⟩
local instance nativeCanonicalReferenceObservation_columnsSigma : MeasurableSpace RealHaarIntegrand.Columns:=borel _
local instance nativeCanonicalReferenceObservation_columnsBorel : BorelSpace RealHaarIntegrand.Columns:=⟨rfl⟩
local instance nativeCanonicalReferenceObservation_circleSecond : SecondCountableTopology CircleHeat.CircleL2:=
  (_root_.fourierBasis (T:=(1:ℝ))).repr.toHomeomorph.secondCountableTopology
local instance nativeCanonicalReferenceObservation_realSecond : SecondCountableTopology RealL2:=
  realCircleIdentification.toHomeomorph.secondCountableTopology
local instance nativeCanonicalReferenceObservation_rowSigma : MeasurableSpace RealHaarInput:=borel _
local instance nativeCanonicalReferenceObservation_rowBorel : BorelSpace RealHaarInput:=⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H b v : ℝ≥0)
variable (P : CanonicalCovariance.ProfileParameters) (Λ κ : ℝ) (hκ : 0<κ) (hκP : κ<P.lower)
variable (u d : Ω→RealL2) (hu : Measurable[𝓕 v] u) (hd : Measurable[𝓕 v] d)
variable (hbH : b≤H) (hb1 : (b:ℝ)≤1)
variable (I0 I1 : StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)

variable (J : StandardTerminalIto (C:=OrthogonalItoChannels.Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ0 : NativeObservationNaturality.StandardScalarNaturality I0 (OrthogonalItoChannels.leftIntegral 𝓕 μ H J))
variable (hIJ1 : NativeObservationNaturality.StandardScalarNaturality I1 (OrthogonalItoChannels.rightIntegral 𝓕 μ H J))
local notation "Data"=>NativeCanonicalReferenceField.data u d
local notation "DataM"=>NativeCanonicalReferenceField.data_measurable 𝓕 v u d hu hd
local notation "Fres" θ=>FrozenReferenceFields.field P Λ κ θ hκP v Data
local notation "FresM" θ=>FrozenReferenceFields.field_predictable 𝓕 P Λ κ θ hκP v Data DataM
local notation "Mres"=>PastFrozenPrefixRows.residual_upper_nonneg P κ hκP
local notation "Init" θ=>NativeCanonicalReferenceField.initial (b:=b) (v:=v) (Λ:=Λ) (u:=u) (d:=d) θ
local notation "Ref" θ=>NativeCanonicalReferenceField.state 𝓕 μ H b v P Λ κ hκ hκP u d hu hd hbH hb1 I0 I1 θ

include hIJ0 hIJ1 in
/-- Exact absolute physical reference, including the original full-target
damped old value and the SAME two original noise channels. This is an
identity of the genuine jointly predictable canonical field. -/
theorem observation (q : ℝ≥0) (hvq : v<q) (hqb : q≤b) (B0 B1 : ℝ≥0)
    (hBDG0 : StandardTerminalBDG16 I0 B0) (hBDG1 : StandardTerminalBDG16 I1 B1) (θ : ℝ) :
    ∀ᵐ x : HeatCircle∂AddCircle.haarAddCircle,∀ᵐ ω∂μ,
      PredictableScalarField.nativeField (fun ω=>(Ref θ) (q,ω)) (ω,x)=
        functional ((b:ℝ)-(v:ℝ)) x (u ω+(θ*Real.exp (-Λ*((b:ℝ)-(v:ℝ)))) • d ω)+
        (OrthogonalItoChannels.leftIntegral 𝓕 μ H J).integral
          (NativeFrozenSpatialObservation.row 𝓕 μ H b q v hκ hκ.le
            (fun _=>AdditiveHaarForcing.constantField κ hκ) stronglyMeasurable_const hbH hqb x 0) ω+
        (OrthogonalItoChannels.rightIntegral 𝓕 μ H J).integral
          (NativeFrozenSpatialObservation.row 𝓕 μ H b q v (sub_pos.mpr hκP) Mres (Fres θ) (FresM θ) hbH hqb x 0) ω := by
  have hb0 : 0<b:=lt_of_le_of_lt (show (0:ℝ≥0)≤v from by exact_mod_cast v.coe_nonneg) (hvq.trans_le hqb)
  let In0:=NativeFixedHaarSemigroup.stopped 𝓕 μ H hκ hκ.le
    (fun _=>AdditiveHaarForcing.constantField κ hκ) stronglyMeasurable_const b hbH hb1 v q
  let In1:=NativeFixedHaarSemigroup.stopped 𝓕 μ H (sub_pos.mpr hκP) Mres (Fres θ) (FresM θ) b hbH hb1 v q
  let N0:Ω→RealL2:=I0.integral In0
  let N1:Ω→RealL2:=I1.integral In1
  have hN0:Measurable N0:=(Lp.stronglyMeasurable _).measurable
  have hN1:Measurable N1:=(Lp.stronglyMeasurable _).measurable
  have hZ:Measurable (Init θ):=(NativeCanonicalReferenceField.initial_measurable
    (𝓕:=𝓕) (v:=v) (b:=b) (Λ:=Λ) (u:=u) (d:=d) (hu:=hu) (hd:=hd) θ).mono (𝓕.le v) le_rfl
  have hn0:=NativeFrozenHilbertField.noise_ae 𝓕 μ H b v hκ hκ.le
    (fun _=>AdditiveHaarForcing.constantField κ hκ) stronglyMeasurable_const hbH hb1 I0 hb0 B0 hBDG0 q hqb
  have hn1:=NativeFrozenHilbertField.noise_ae 𝓕 μ H b v (sub_pos.mpr hκP) Mres (Fres θ) (FresM θ)
    hbH hb1 I1 hb0 B1 hBDG1 q hqb
  have hstate : (fun ω=>(Ref θ) (q,ω))=ᵐ[μ] (fun ω=>(Init θ) ω+N1 ω+N0 ω):=by
    filter_upwards [hn0,hn1] with ω hn0 hn1
    simp only [NativeCanonicalReferenceField.state,NativeFrozenHilbertField.field,
      PredictablePastParameter.held_eq (p:=(q,ω)) _ _ hvq]
    rw [hn0,hn1]
    rfl
  have ha:=NativeScalarProductAlgebra.add_ae μ (fun ω=>(Init θ) ω+N1 ω) N0 (hZ.add hN1) hN0
  have ha1:=NativeScalarProductAlgebra.add_ae μ (Init θ) N1 hZ hN1
  have hinit:∀ᵐ x : HeatCircle∂AddCircle.haarAddCircle,∀ᵐ ω∂μ,
      PredictableScalarField.nativeField (Init θ) (ω,x)=
        functional ((b:ℝ)-(v:ℝ)) x (u ω+(θ*Real.exp (-Λ*((b:ℝ)-(v:ℝ)))) • d ω):=by
    exact NativeScalarProductAlgebra.heat_ae μ _
      ((hu.mono (𝓕.le v) le_rfl).add
        ((measurable_const : Measurable (fun _ : Ω=>(θ*Real.exp (-Λ*((b:ℝ)-(v:ℝ))) : ℝ))).smul
          (hd.mono (𝓕.le v) le_rfl)))
      (sub_pos.mpr (by exact_mod_cast hvq.trans_le hqb))
  have h0:=NativeFrozenSpatialObservation.physical_observation 𝓕 μ H b q v hκ hκ.le
    (fun _=>AdditiveHaarForcing.constantField κ hκ) stronglyMeasurable_const hbH hb1 hqb I0 _ hIJ0
  have h1:=NativeFrozenSpatialObservation.physical_observation 𝓕 μ H b q v (sub_pos.mpr hκP) Mres
    (Fres θ) (FresM θ) hbH hb1 hqb I1 _ hIJ1
  filter_upwards [ha,ha1,hinit,h0,h1] with x ha ha1 hi h0 h1
  filter_upwards [hstate,ha,ha1,hi,h0,h1] with ω hs ha ha1 hi h0 h1
  rw [NativeScalarFieldAlgebra.congr (fun ω=>(Ref θ) (q,ω)) (fun ω=>(Init θ) ω+N1 ω+N0 ω) ω hs x,ha,ha1,hi,h0,h1]
  ring

end SHE.NativeCanonicalReferenceObservation

