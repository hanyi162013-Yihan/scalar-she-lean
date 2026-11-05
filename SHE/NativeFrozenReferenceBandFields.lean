module

public import SHE.NativeFrozenReferenceBand
public import SHE.NativeFrozenPairReference
public import SHE.NativeCanonicalReferenceObservation
public import SHE.NativeCanonicalReferenceField
public import SHE.NativeFrozenGaussianObservations
public import SHE.NativeFrozenBandCovariance
public import SHE.NativeScalarProductAlgebra

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
namespace SHE.NativeFrozenReferenceBandFields
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
local instance nativeNullSingleton : NullSingletonClass (@AddCircle.haarAddCircle (2*Real.pi) _) where
  measure_singleton x:=by
    have hv:(volume:Measure HeatCircle) {x}=0:=by
      rw [←Metric.closedBall_zero,AddCircle.volume_closedBall]
      norm_num
    rw [AddCircle.volume_eq_smul_haarAddCircle,Measure.smul_apply,smul_eq_mul] at hv
    exact (mul_eq_zero.mp hv).resolve_left (by positivity)
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




local notation "Field"=>NativeFrozenReferenceBand.field 𝓕 μ H b v P Λ κ hκ hκP u d hu hd hbH hb1 I0 I1
local notation "Diff"=>NativeFrozenReferenceBand.difference 𝓕 μ H b v P Λ κ hκ hκP u d hu hd hbH hb1 I0 I1
local notation "Amp"=>NativeFrozenReferenceBand.amplitude 𝓕 μ H b v P Λ κ hκ hκP u d hu hd hbH hb1 I0 I1

theorem field_measurable (hb0:0<b)(hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (B0 B1:ℝ≥0)(hBDG0:StandardTerminalBDG16 I0 B0)(hBDG1:StandardTerminalBDG16 I1 B1)(θ:ℝ):
    Measurable (Field θ):=by
  have hs:=NativeCanonicalReferenceField.state_predictable 𝓕 μ H b v P Λ κ hκ hκP
    u d hu hd hbH hb1 I0 I1 hb0 hnull B0 B1 hBDG0 hBDG1 θ
  have hm:Measurable (fun ω=>NativeCanonicalReferenceField.state 𝓕 μ H b v P Λ κ hκ hκP
      u d hu hd hbH hb1 I0 I1 θ (b,ω)):=
    ((hs.mono (predictable_le_product 𝓕)).measurable).comp (measurable_const.prodMk measurable_id)
  exact PredictableScalarField.nativeField_measurable hm

theorem difference_measurable (hb0:0<b)(hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (B0 B1:ℝ≥0)(hBDG0:StandardTerminalBDG16 I0 B0)(hBDG1:StandardTerminalBDG16 I1 B1)
    {a:ℝ→ℝ}(ha:SmoothCylinders.BoundedSmooth a)(j:ℕ)(θ η:ℝ):Measurable (Diff a j θ η):=by
  have hb:Measurable (ScalarHeatBands.band a (j+1)):=
    (ScalarHeatBands.band_boundedSmooth ha (j+1)).smooth.continuous.measurable
  exact (hb.comp (field_measurable 𝓕 μ H b v P Λ κ hκ hκP u d hu hd hbH hb1 I0 I1 hb0 hnull B0 B1 hBDG0 hBDG1 θ)).sub
    (hb.comp (field_measurable 𝓕 μ H b v P Λ κ hκ hκP u d hu hd hbH hb1 I0 I1 hb0 hnull B0 B1 hBDG0 hBDG1 η))

theorem amplitude_measurable (hb0:0<b)(hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (B0 B1:ℝ≥0)(hBDG0:StandardTerminalBDG16 I0 B0)(hBDG1:StandardTerminalBDG16 I1 B1)
    (j:ℕ)(θ η:ℝ):Measurable (Amp j θ η):=by
  have hsub:Measurable (fun z=>Field θ z-Field η z):=
    (field_measurable 𝓕 μ H b v P Λ κ hκ hκP u d hu hd hbH hb1 I0 I1 hb0 hnull B0 B1 hBDG0 hBDG1 θ).sub
      (field_measurable 𝓕 μ H b v P Λ κ hκ hκP u d hu hd hbH hb1 I0 I1 hb0 hnull B0 B1 hBDG0 hBDG1 η)
  exact measurable_const.min ((continuous_abs.measurable.comp hsub).div_const _)

theorem difference_bound {a:ℝ→ℝ}{M:ℝ}(hM:∀z,|a z|≤M)(j:ℕ)(θ η:ℝ)(z:Ω×HeatCircle):
    |Diff a j θ η z|≤4*M:=by
  have he:=GaussianHeatBandTranslations.bounded hM j (Field θ z) (Field η z) 0
  simpa only [NativeFrozenReferenceBand.difference,GaussianHeatBandTranslations.difference,zero_add] using he

theorem amplitude_nonneg (j:ℕ)(θ η:ℝ)(z:Ω×HeatCircle):0≤Amp j θ η z:=
  le_min zero_le_one (div_nonneg (abs_nonneg _) (CompactMollifier.radius_pos _).le)

theorem amplitude_le_one (j:ℕ)(θ η:ℝ)(z:Ω×HeatCircle):Amp j θ η z≤1:=min_le_left _ _

end SHE.NativeFrozenReferenceBandFields
