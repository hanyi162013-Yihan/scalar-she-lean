module

public import SHE.NativeGaussianBesselFieldEnergy
public import SHE.NativeFrozenReferenceCovarianceKernel
public import SHE.NativeFrozenReferenceBandFields
public import SHE.NativeFrozenBandCost
public import SHE.BoundedSpatialCovariance
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
namespace SHE.NativeFrozenReferenceBesselEnergy
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





local notation "Diff"=>NativeFrozenReferenceBand.difference 𝓕 μ H b v P Λ κ hκ hκP u d hu hd hbH hb1 I0 I1
local notation "Scaled"=>NativeFrozenReferenceCovarianceKernel.scaledAmplitude 𝓕 μ H b v P Λ κ hκ hκP u d hu hd hbH hb1 I0 I1

def value (ρ:ℝ)(hΛ:1≤Λ)(hρ:0≤ρ)(a:ℝ→ℝ)(j:ℕ)(θ η:ℝ):Ω→CircleL2:=
  NativeBesselFieldAE.value Λ ρ hΛ hρ (fun z=>(Diff a j θ η z:ℂ))

include hIJ0 hIJ1 in
/-- The canonical compatible terminal reference band has genuine native
Bessel energy. The polynomial spatial gain, constant mode and finite
window floor are all explicit, and random displacements remain paired. -/
theorem energy (hvb:v<b) (hΛ:1≤Λ) (ρ:ℝ)(hρ:0<ρ)(hρhalf:ρ<1/2)
    (hsmall:ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hsmalltime:(b:ℝ)-(v:ℝ)≤NativeTwoPointCovariance.horizon)
    (hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (B B0 B1:ℝ≥0) (hBDG:StandardTerminalBDG16 J B)
    (hBDG0:StandardTerminalBDG16 I0 B0)(hBDG1:StandardTerminalBDG16 I1 B1)
    (hJ:StandardFiniteIto.Universal 𝓕 μ H J)(hlocal:StandardTerminalPastLocality J)
    (θ η:ℝ){a:ℝ→ℝ}(ha:SmoothCylinders.BoundedSmooth a){M K β:ℝ}
    (hM:∀z,|a z|≤M)(hK:0≤K)(hβ:0≤β)(hβ1:β<1)
    (hh:∀z w,|a z-a w|≤K*|z-w|^β)(j:ℕ):
    let r:=CompactMollifier.radius (j+1)
    let L:=κ/(128*r^2)
    let tail:=GaussianCircleMass.decay (2-β) L (Real.sqrt ((b:ℝ)-(v:ℝ)))
    Integrable (fun ω=>‖value 𝓕 μ H b v P Λ κ hκ hκP u d hu hd hbH hb1 I0 I1 ρ hΛ hρ.le a j θ η ω‖^2) μ ∧
      (∫ω,‖value 𝓕 μ H b v P Λ κ hκ hκP u d hu hd hbH hb1 I0 I1 ρ hΛ hρ.le a j θ η ω‖^2 ∂μ)≤
        NativeGaussianBesselCost.bound (2-β) L Λ ρ tail*
          (∫ω,∫x:HeatCircle,(Scaled K β j θ η (ω,x))^2 ∂AddCircle.haarAddCircle ∂μ):=by
  intro r L tail
  have hb0:0<b:=bot_le.trans_lt hvb
  have hDm:=NativeFrozenReferenceBandFields.difference_measurable 𝓕 μ H b v P Λ κ hκ hκP
    u d hu hd hbH hb1 I0 I1 hb0 hnull B0 B1 hBDG0 hBDG1 ha j θ η
  have hAm:=NativeFrozenReferenceBandFields.amplitude_measurable 𝓕 μ H b v P Λ κ hκ hκP
    u d hu hd hbH hb1 I0 I1 hb0 hnull B0 B1 hBDG0 hBDG1 j θ η
  have hSm:Measurable (Scaled K β j θ η):=measurable_const.mul hAm
  have hp:0≤NativeFrozenReferenceCovarianceKernel.prefactor K β j:=by
    unfold NativeFrozenReferenceCovarianceKernel.prefactor
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hK)
      (GaussianHeatBandRootEnvelope.constant_nonneg β))
      (Real.rpow_nonneg (CompactMollifier.radius_pos (j+1)).le _)
  have hSb(z:Ω×HeatCircle):|Scaled K β j θ η z|≤
      NativeFrozenReferenceCovarianceKernel.prefactor K β j:=by
    unfold NativeFrozenReferenceCovarianceKernel.scaledAmplitude
    rw [abs_mul,abs_of_nonneg hp,abs_of_nonneg
      (NativeFrozenReferenceBandFields.amplitude_nonneg 𝓕 μ H b v P Λ κ hκ hκP u d hu hd hbH hb1 I0 I1 j θ η z)]
    exact mul_le_of_le_one_right hp
      (NativeFrozenReferenceBandFields.amplitude_le_one 𝓕 μ H b v P Λ κ hκ hκP u d hu hd hbH hb1 I0 I1 j θ η z)
  have hM0:0≤M:=(abs_nonneg (a 0)).trans (hM 0)
  have hL:0<L:=by dsimp [L,r];positivity [CompactMollifier.radius_pos (j+1)]
  have htail:0≤tail:=GaussianCircleMass.decay_nonneg hL.le (Real.sqrt_nonneg _)
  have hc:=NativeFrozenReferenceCovarianceKernel.covariance 𝓕 μ H b v P Λ κ hκ hκP
    u d hu hd hbH hb1 I0 I1 J hIJ0 hIJ1 hvb (zero_le_one.trans hΛ) hsmall hsmalltime
    hnull B B0 B1 hBDG hBDG0 hBDG1 hJ hlocal θ η ha hM hK hβ hβ1.le hh j
  exact NativeGaussianBesselFieldEnergy.bound μ (by linarith) hL hΛ hρ hρhalf htail
    (by positivity) hp (Diff a j θ η) (Scaled K β j θ η) hDm hSm
    (NativeFrozenReferenceBandFields.difference_bound 𝓕 μ H b v P Λ κ hκ hκP
      u d hu hd hbH hb1 I0 I1 hM j θ η) hSb hc
end SHE.NativeFrozenReferenceBesselEnergy
