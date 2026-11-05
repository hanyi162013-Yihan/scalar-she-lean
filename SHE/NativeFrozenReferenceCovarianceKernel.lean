module

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
namespace SHE.NativeFrozenReferenceCovarianceKernel
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




def prefactor (K β:ℝ)(j:ℕ):ℝ:=
  (2*K*GaussianHeatBandRootEnvelope.constant β)*CompactMollifier.radius (j+1)^β
local notation "Diff"=>NativeFrozenReferenceBand.difference 𝓕 μ H b v P Λ κ hκ hκP u d hu hd hbH hb1 I0 I1
local notation "Amp"=>NativeFrozenReferenceBand.amplitude 𝓕 μ H b v P Λ κ hκ hκP u d hu hd hbH hb1 I0 I1

def scaledAmplitude (K β:ℝ)(j:ℕ)(θ η:ℝ)(z:Ω×HeatCircle):ℝ:=prefactor K β j*Amp j θ η z
local notation "Scaled"=>scaledAmplitude 𝓕 μ H b v P Λ κ hκ hκP u d hu hd hbH hb1 I0 I1

include hIJ0 hIJ1 in
/-- Direct input for the actual native positive-kernel Schur theorem:
true uncentered frozen-band covariance is bounded by the radial
polynomial kernel plus its explicit window floor, with both dependent
random displacement factors still averaged together. -/
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
    let r:=CompactMollifier.radius (j+1)
    let L:=κ/(128*r^2)
    let tail:=GaussianCircleMass.decay (2-β) L (Real.sqrt ((b:ℝ)-(v:ℝ)))
    ∀ᵐz:HeatCircle×HeatCircle∂AddCircle.haarAddCircle.prod AddCircle.haarAddCircle,
      BoundedSpatialCovariance.value μ (Diff a j θ η) z≤
        (NativeGaussianCircleMass.G (2-β) L z+tail)*
          BoundedSpatialCovariance.value μ (Scaled K β j θ η) z:=by
  intro r L tail
  have hb0:0<b:=(show (0:ℝ≥0)≤v from zero_le).trans_lt hvb
  have hDm:=NativeFrozenReferenceBandFields.difference_measurable 𝓕 μ H b v P Λ κ hκ hκP
    u d hu hd hbH hb1 I0 I1 hb0 hnull B0 B1 hBDG0 hBDG1 ha j θ η
  have hAm:=NativeFrozenReferenceBandFields.amplitude_measurable 𝓕 μ H b v P Λ κ hκ hκP
    u d hu hd hbH hb1 I0 I1 hb0 hnull B0 B1 hBDG0 hBDG1 j θ η
  have hSm:Measurable (Scaled K β j θ η):=measurable_const.mul hAm
  apply (Measure.ae_prod_iff_ae_ae
    (measurableSet_le (BoundedSpatialCovariance.measurable μ _ hDm)
      (((NativeGaussianCircleMass.measurable_G (2-β) L).add_const tail).mul
        (BoundedSpatialCovariance.measurable μ _ hSm)))).mpr
  have hcov:=NativeFrozenReferenceBand.covariance 𝓕 μ H b v P Λ κ hκ hκP u d hu hd hbH hb1 I0 I1 J
    hIJ0 hIJ1 hvb hΛ hsmall hsmalltime hnull B B0 B1 hBDG hBDG0 hBDG1 hJ hlocal
    θ η ha hM hK hβ hβ1 hh j
  filter_upwards [hcov] with x hx
  filter_upwards [hx] with y hy
  have hnon:0≤BoundedSpatialCovariance.value μ (Amp j θ η) (x,y):=by
    apply integral_nonneg
    intro ω
    exact mul_nonneg (NativeFrozenReferenceBandFields.amplitude_nonneg 𝓕 μ H b v P Λ κ hκ hκP
      u d hu hd hbH hb1 I0 I1 j θ η (ω,x))
      (NativeFrozenReferenceBandFields.amplitude_nonneg 𝓕 μ H b v P Λ κ hκ hκP
        u d hu hd hbH hb1 I0 I1 j θ η (ω,y))
  have hscaled:BoundedSpatialCovariance.value μ (Scaled K β j θ η) (x,y)=
      (prefactor K β j)^2*BoundedSpatialCovariance.value μ (Amp j θ η) (x,y):=by
    unfold BoundedSpatialCovariance.value scaledAmplitude
    rw [←integral_const_mul]
    apply integral_congr_ae
    filter_upwards with ω
    ring
  have hspan:0≤(b:ℝ)-(v:ℝ):=sub_nonneg.mpr (by exact_mod_cast hvb.le)
  have hs:0≤κ*min (dist x y) (Real.sqrt ((b:ℝ)-(v:ℝ)))/128:=
    div_nonneg (mul_nonneg hκ.le (le_min dist_nonneg (Real.sqrt_nonneg _))) (by norm_num)
  have hk:=NativeFrozenBandCost.kernel (s:=2-β) hκ.le (CompactMollifier.radius_pos (j+1)) hspan (dist_nonneg (x:=x) (y:=y))
  have hy':BoundedSpatialCovariance.value μ (Diff a j θ η) (x,y)≤
      (prefactor K β j)^2*
        (ScalarHeatBandEnvelope.decay r (κ*min (dist x y) (Real.sqrt ((b:ℝ)-(v:ℝ)))/128) ((2-β)/2))^2*
        BoundedSpatialCovariance.value μ (Amp j θ η) (x,y):=by
    have he:=(le_abs_self (BoundedSpatialCovariance.value μ (Diff a j θ η) (x,y))).trans hy
    simpa only [BoundedSpatialCovariance.value,prefactor,Real.coe_toNNReal _ hs,mul_pow] using he
  calc
    _≤_:=hy'
    _=(ScalarHeatBandEnvelope.decay r (κ*min (dist x y) (Real.sqrt ((b:ℝ)-(v:ℝ)))/128) ((2-β)/2))^2*
        ((prefactor K β j)^2*BoundedSpatialCovariance.value μ (Amp j θ η) (x,y)):=by ring
    _≤(NativeGaussianCircleMass.G (2-β) L (x,y)+tail)*
        ((prefactor K β j)^2*BoundedSpatialCovariance.value μ (Amp j θ η) (x,y)):=
      mul_le_mul_of_nonneg_right hk (mul_nonneg (sq_nonneg _) hnon)
    _=_:=by
      dsimp only [Pi.mul_apply]
      rw [hscaled]

end SHE.NativeFrozenReferenceCovarianceKernel
