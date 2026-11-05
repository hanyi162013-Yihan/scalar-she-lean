module

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
namespace SHE.NativeFrozenReferenceBand
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



def field (θ:ℝ) (z:Ω×HeatCircle):ℝ:=
  PredictableScalarField.nativeField (fun ω=>(Ref θ) (b,ω)) z

def difference (a:ℝ→ℝ) (j:ℕ) (θ η:ℝ) (z:Ω×HeatCircle):ℝ:=
  ScalarHeatBands.band a (j+1) (field 𝓕 μ H b v P Λ κ hκ hκP u d hu hd hbH hb1 I0 I1 θ z)-
    ScalarHeatBands.band a (j+1) (field 𝓕 μ H b v P Λ κ hκ hκP u d hu hd hbH hb1 I0 I1 η z)

def amplitude (j:ℕ) (θ η:ℝ) (z:Ω×HeatCircle):ℝ:=
  min 1 (|field 𝓕 μ H b v P Λ κ hκ hκP u d hu hd hbH hb1 I0 I1 θ z-
    field 𝓕 μ H b v P Λ κ hκ hκP u d hu hd hbH hb1 I0 I1 η z|/CompactMollifier.radius (j+1))

local notation "T"=>fun θ η x y=>NativeFrozenGaussianLaw.terminal 𝓕 μ v b P Λ κ hκ hκP
  NativeFrozenBandCovariance.sides (NativeFrozenBandCovariance.parameters θ η)
  (NativeFrozenBandCovariance.centers x y) H hbH Data DataM J
  (NativeFrozenPairReference.means (b:=b) (v:=v) Λ θ η x y)
local notation "Df"=>difference 𝓕 μ H b v P Λ κ hκ hκP u d hu hd hbH hb1 I0 I1
local notation "Amp"=>amplitude 𝓕 μ H b v P Λ κ hκ hκP u d hu hd hbH hb1 I0 I1

include hIJ0 hIJ1 in
/-- True uncentered covariance of the literal compatible terminal
reference bands. Both dependent displacement minima stay inside the
original sample expectation before the spatial Schur estimate. -/
theorem covariance (hvb:v<b) (hΛ:0≤Λ)
    (hsmall:ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hsmalltime:(b:ℝ)-(v:ℝ)≤NativeTwoPointCovariance.horizon)
    (hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (B B0 B1:ℝ≥0) (hBDG:StandardTerminalBDG16 J B)
    (hBDG0:StandardTerminalBDG16 I0 B0)(hBDG1:StandardTerminalBDG16 I1 B1)
    (hJ:StandardFiniteIto.Universal 𝓕 μ H J)(hlocal:StandardTerminalPastLocality J)
    (θ η:ℝ){a:ℝ→ℝ}(ha:SmoothCylinders.BoundedSmooth a){M K β:ℝ}
    (hM:∀z,|a z|≤M)(hK:0≤K)(hβ:0≤β)(hβ1:β≤1)
    (hh:∀z w,|a z-a w|≤K*|z-w|^β)(j:ℕ):
    ∀ᵐx:HeatCircle∂AddCircle.haarAddCircle,∀ᵐy:HeatCircle∂AddCircle.haarAddCircle,
      let σ:ℝ≥0:=(κ*min (dist x y) (Real.sqrt ((b:ℝ)-(v:ℝ)))/128).toNNReal
      |∫ω,Df a j θ η (ω,x)*Df a j θ η (ω,y) ∂μ|≤
        ((2*K*GaussianHeatBandRootEnvelope.constant β)*CompactMollifier.radius (j+1)^β*
          ScalarHeatBandEnvelope.decay (CompactMollifier.radius (j+1)) σ ((2-β)/2))^2*
        ∫ω,Amp j θ η (ω,x)*Amp j θ η (ω,y) ∂μ:=by
  have he:=NativeFrozenPairReference.sums_eq_reference 𝓕 μ H b v P Λ κ hκ hκP
    u d hu hd hbH hb1 I0 I1 J hIJ0 hIJ1 hvb B0 B1 hBDG0 hBDG1 θ η
  have hb0:0<b:=(show (0:ℝ≥0)≤v from zero_le).trans_lt hvb
  filter_upwards [he] with x hx
  filter_upwards [hx,(AddCircle.haarAddCircle:Measure HeatCircle).ae_ne x] with y hy hxy
  have ht:=NativeFrozenBandCovariance.bound 𝓕 μ v b hvb.le P Λ κ hκ hκP θ η x y hΛ hsmall
    H hbH Data DataM J hb0 hb1 hnull B hBDG hJ hlocal
    (NativeFrozenPairReference.means (b:=b) (v:=v) Λ θ η x y)
    (NativeFrozenPairReference.means_continuous b v Λ hvb θ η x y) hvb hsmalltime (Ne.symm hxy)
    ha hM hK hβ hβ1 hh j
  have hp:(fun ω=>GaussianSeparatedBand.pair a j ((T θ η x y) ω))=ᵐ[μ]
      fun ω=>Df a j θ η (ω,x)*Df a j θ η (ω,y):=by
    filter_upwards [hy] with ω hω
    rcases hω with ⟨h0,h1,h2,h3⟩
    unfold GaussianSeparatedBand.pair
    rw [h0,h1,h2,h3]
    rfl
  have hm:(fun ω=>GaussianSeparatedBand.amplitude j ((T θ η x y) ω))=ᵐ[μ]
      fun ω=>Amp j θ η (ω,x)*Amp j θ η (ω,y):=by
    filter_upwards [hy] with ω hω
    rcases hω with ⟨h0,h1,h2,h3⟩
    have hd0:((T θ η x y) ω) 2-((T θ η x y) ω) 4=
        field 𝓕 μ H b v P Λ κ hκ hκP u d hu hd hbH hb1 I0 I1 θ (ω,x)-
        field 𝓕 μ H b v P Λ κ hκ hκP u d hu hd hbH hb1 I0 I1 η (ω,x):=by
      unfold field
      linarith
    have hd1:((T θ η x y) ω) 3-((T θ η x y) ω) 5=
        field 𝓕 μ H b v P Λ κ hκ hκP u d hu hd hbH hb1 I0 I1 θ (ω,y)-
        field 𝓕 μ H b v P Λ κ hκ hκP u d hu hd hbH hb1 I0 I1 η (ω,y):=by
      unfold field
      linarith
    unfold GaussianSeparatedBand.amplitude
    rw [hd0,hd1]
    rfl
  rwa [integral_congr_ae hp,integral_congr_ae hm] at ht

end SHE.NativeFrozenReferenceBand
