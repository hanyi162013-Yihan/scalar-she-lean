module
public import SHE.NativeScalarFieldAlgebra
public import SHE.NativeScalarProductAlgebra
public import SHE.OrthogonalItoChannels
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SHE.CanonicalReferenceIntegral
open Set MeasureTheory PredictableL2 FiniteHaar StoppedFourier NativeHeatObservation
open OrthogonalItoChannels DyadicApproximation
open scoped NNReal ENNReal
local instance canonicalReferenceIntegral_unit : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance canonicalReferenceIntegral_period : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance canonicalReferenceIntegral_realSigma : MeasurableSpace RealL2:=borel _
local instance canonicalReferenceIntegral_realBorel : BorelSpace RealL2:=⟨rfl⟩
local instance canonicalReferenceIntegral_circleSigma : MeasurableSpace CircleL2:=borel _
local instance canonicalReferenceIntegral_circleBorel : BorelSpace CircleL2:=⟨rfl⟩
local instance canonicalReferenceIntegral_rowSigma : MeasurableSpace RealHaarInput:=borel _
local instance canonicalReferenceIntegral_rowBorel : BorelSpace RealHaarInput:=⟨rfl⟩
local instance canonicalReferenceIntegral_bothSigma : MeasurableSpace (Both RealHaarInput):=borel _
local instance canonicalReferenceIntegral_bothBorel : BorelSpace (Both RealHaarInput):=⟨rfl⟩
local instance canonicalReferenceIntegral_unitSecond : SecondCountableTopology CircleHeat.CircleL2:=
  (_root_.fourierBasis (T:=(1:ℝ))).repr.toHomeomorph.secondCountableTopology
local instance canonicalReferenceIntegral_realSecond : SecondCountableTopology RealL2:=
  realCircleIdentification.toHomeomorph.secondCountableTopology
variable {Ω:Type*}[MeasurableSpace Ω]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)[IsProbabilityMeasure μ](H b v:ℝ≥0)
variable (P:CanonicalCovariance.ProfileParameters)(Λ κ:ℝ)(hκ:0<κ)(hκP:κ<P.lower)
variable (u d:Ω→RealL2)(hu:Measurable[𝓕 v] u)(hd:Measurable[𝓕 v] d)
variable (hbH:b≤H)(hb1:(b:ℝ)≤1)
variable (I0 I1:StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)
variable (J:StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ0:NativeObservationNaturality.StandardScalarNaturality I0 (leftIntegral 𝓕 μ H J))
variable (hIJ1:NativeObservationNaturality.StandardScalarNaturality I1 (rightIntegral 𝓕 μ H J))
variable (hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ)
variable (B0 B1:ℝ≥0)(hBDG0:StandardTerminalBDG16 I0 B0)(hBDG1:StandardTerminalBDG16 I1 B1)
local notation "Fres" θ=>FrozenReferenceFields.field P Λ κ θ hκP v (NativeCanonicalReferenceField.data u d)
local notation "FresM" θ=>FrozenReferenceFields.field_predictable 𝓕 P Λ κ θ hκP v _
  (NativeCanonicalReferenceField.data_measurable 𝓕 v u d hu hd)
local notation "Mres"=>PastFrozenPrefixRows.residual_upper_nonneg P κ hκP
attribute [local irreducible] functional

include hIJ0 hIJ1 hBDG0 hBDG1 hnull in
/-- The literal canonical full-target reference is the sum of its
original full-target old mean and the two SAME-J post-past stopped
integrals. The endpoint q=b is included. -/
theorem reference_integral (θ:ℝ)(q:ℝ≥0)(hvq:v<q)(hqb:q≤b):
    ∀ᵐ x:HeatCircle∂AddCircle.haarAddCircle,∀ᵐω∂μ,
      PredictableScalarField.nativeField
        (fun ω=>NativeCanonicalReferenceField.state 𝓕 μ H b v P Λ κ hκ hκP
          u d hu hd hbH hb1 I0 I1 θ (q,ω)) (ω,x)=
      functional ((b:ℝ)-(v:ℝ)) x
        (u ω+(θ*Real.exp (-Λ*((b:ℝ)-(v:ℝ)))) • d ω)+
      (rightIntegral 𝓕 μ H J).integral
        (NativeFrozenSpatialObservation.row 𝓕 μ H b q v (sub_pos.mpr hκP) Mres
          (Fres θ) (FresM θ) hbH hqb x 0) ω+
      (leftIntegral 𝓕 μ H J).integral
        (NativeFrozenSpatialObservation.row 𝓕 μ H b q v hκ hκ.le
          (fun _=>AdditiveHaarForcing.constantField κ hκ) stronglyMeasurable_const hbH hqb x 0) ω:=by
  have hb0:0<b:=(show (0:ℝ≥0)≤v from zero_le).trans_lt (hvq.trans_le hqb)
  let Init:Ω→RealL2:=NativeCanonicalReferenceField.initial (b:=b) (v:=v) (Λ:=Λ) (u:=u) (d:=d) θ
  let Rnoise:Ω→RealL2:=fun ω=>NativeFrozenHilbertField.noise 𝓕 μ H b v
    (sub_pos.mpr hκP) Mres (Fres θ) (FresM θ) hbH hb1 I1 q ω
  let Anoise:Ω→RealL2:=fun ω=>NativeFrozenHilbertField.noise 𝓕 μ H b v hκ hκ.le
    (fun _=>AdditiveHaarForcing.constantField κ hκ) stronglyMeasurable_const hbH hb1 I0 q ω
  have hi:Measurable Init:=(NativeCanonicalReferenceField.initial_measurable
    (𝓕:=𝓕) (v:=v) (b:=b) (Λ:=Λ) (u:=u) (d:=d) (hu:=hu) (hd:=hd) θ).mono (𝓕.le v) le_rfl
  have hr:Measurable Rnoise:=(((NativeFrozenHilbertField.noise_predictable 𝓕 μ H b v
    (sub_pos.mpr hκP) Mres (Fres θ) (FresM θ) hbH hb1 I1 hb0 hnull B1 hBDG1).mono
      (predictable_le_product 𝓕)).measurable).comp (measurable_const.prodMk measurable_id)
  have ha:Measurable Anoise:=(((NativeFrozenHilbertField.noise_predictable 𝓕 μ H b v hκ hκ.le
    (fun _=>AdditiveHaarForcing.constantField κ hκ) stronglyMeasurable_const hbH hb1 I0 hb0
      hnull B0 hBDG0).mono (predictable_le_product 𝓕)).measurable).comp
        (measurable_const.prodMk measurable_id)
  have hs1:=NativeScalarProductAlgebra.add_ae μ Init Rnoise hi hr
  have hs2:=NativeScalarProductAlgebra.add_ae μ (fun ω=>Init ω+Rnoise ω) Anoise (hi.add hr) ha
  have hh:=NativeScalarProductAlgebra.heat_ae μ
    (fun ω=>u ω+(θ*Real.exp (-Λ*((b:ℝ)-(v:ℝ)))) • d ω)
    (((hu).mono (𝓕.le v) le_rfl).add
      (((hd).mono (𝓕.le v) le_rfl).const_smul (θ*Real.exp (-Λ*((b:ℝ)-(v:ℝ))))))
    (sub_pos.mpr (show (v:ℝ)<(b:ℝ) by exact_mod_cast hvq.trans_le hqb))
  have hrn:=NativeScalarFieldAlgebra.noise_observation 𝓕 μ H b q v (sub_pos.mpr hκP) Mres
    (Fres θ) (FresM θ) hbH hb1 hqb I1 (rightIntegral 𝓕 μ H J) hIJ1 hb0 B1 hBDG1
  have han:=NativeScalarFieldAlgebra.noise_observation 𝓕 μ H b q v hκ hκ.le
    (fun _=>AdditiveHaarForcing.constantField κ hκ) stronglyMeasurable_const hbH hb1 hqb
      I0 (leftIntegral 𝓕 μ H J) hIJ0 hb0 B0 hBDG0
  filter_upwards [hs1,hs2,hh,hrn,han] with x hs1 hs2 hh hrn han
  filter_upwards [hs1,hs2,hh,hrn,han] with ω hs1 hs2 hh hrn han
  have he:NativeCanonicalReferenceField.state 𝓕 μ H b v P Λ κ hκ hκP
      u d hu hd hbH hb1 I0 I1 θ (q,ω)=(Init ω+Rnoise ω)+Anoise ω:=by
    simp only [NativeCanonicalReferenceField.state,NativeFrozenHilbertField.field,
      PredictablePastParameter.held_eq (p:=(q,ω)) _ _ hvq]
    rfl
  rw [NativeScalarFieldAlgebra.congr _ (fun ω=>(Init ω+Rnoise ω)+Anoise ω) ω he x,hs2,hs1]
  change PredictableScalarField.nativeField (fun ω=>heat ((b:ℝ)-(v:ℝ))
    (u ω+(θ*Real.exp (-Λ*((b:ℝ)-(v:ℝ)))) • d ω)) (ω,x)+
    PredictableScalarField.nativeField Rnoise (ω,x)+PredictableScalarField.nativeField Anoise (ω,x)=_
  rw [hh,hrn,han]
end SHE.CanonicalReferenceIntegral
