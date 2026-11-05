module

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
namespace SHE.NativeFrozenPairReference
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


def means (θ η:ℝ) (x y:HeatCircle) (p:ControlledProfile.Inputs):WordRecursion.State 6:=
  WithLp.toLp 2 ![0,0,ControlledProfile.mean Λ p.1 p.2 (θ,((b:ℝ)-(v:ℝ),x)),
    ControlledProfile.mean Λ p.1 p.2 (θ,((b:ℝ)-(v:ℝ),y)),
    ControlledProfile.mean Λ p.1 p.2 (η,((b:ℝ)-(v:ℝ),x)),
    ControlledProfile.mean Λ p.1 p.2 (η,((b:ℝ)-(v:ℝ),y))]

include b v in
theorem means_continuous (hvb:v<b) (θ η:ℝ) (x y:HeatCircle):
    Continuous (means (b:=b) (v:=v) Λ θ η x y):=by
  have hr:0<(b:ℝ)-(v:ℝ):=sub_pos.mpr (by exact_mod_cast hvb)
  have hc(θ:ℝ)(x:HeatCircle):Continuous (fun p:ControlledProfile.Inputs=>
      ControlledProfile.mean Λ p.1 p.2 (θ,((b:ℝ)-(v:ℝ),x))):=by
    unfold ControlledProfile.mean
    simp_rw [PhysicalProfile.physicalHeatMean_eq hr]
    exact (Complex.continuous_re.comp (continuous_const.inner (𝕜:=ℂ) continuous_fst)).add
      ((Complex.continuous_re.comp (continuous_const.inner (𝕜:=ℂ) continuous_snd)).const_mul _)
  unfold means
  apply (PiLp.continuous_toLp 2 (fun _:Fin 6=>ℝ)).comp
  apply continuous_pi
  intro i
  fin_cases i
  · exact continuous_const
  · exact continuous_const
  · exact hc θ x
  · exact hc θ y
  · exact hc η x
  · exact hc η y

local notation "R"=>fun θ η x y=>NativeFrozenGaussianRows.rows 𝓕 μ H v b P Λ κ hκ hκP
  NativeFrozenBandCovariance.sides (NativeFrozenBandCovariance.parameters θ η)
  (NativeFrozenBandCovariance.centers x y) Data DataM hbH
local notation "T"=>fun θ η x y=>NativeFrozenGaussianLaw.terminal 𝓕 μ v b P Λ κ hκ hκP
  NativeFrozenBandCovariance.sides (NativeFrozenBandCovariance.parameters θ η)
  (NativeFrozenBandCovariance.centers x y) H hbH Data DataM J (means (b:=b) (v:=v) Λ θ η x y)

include hIJ0 hIJ1 in
/-- The six actual Gaussian coordinates reconstruct the literal native
compatible reference pair, on the genuine two-spatial-point sample event. -/
theorem sums_eq_reference (hvb:v<b) (B0 B1:ℝ≥0)
    (hBDG0:StandardTerminalBDG16 I0 B0) (hBDG1:StandardTerminalBDG16 I1 B1) (θ η:ℝ):
    ∀ᵐx:HeatCircle∂AddCircle.haarAddCircle,∀ᵐy:HeatCircle∂AddCircle.haarAddCircle,∀ᵐω∂μ,
      let z:WordRecursion.State 6:=(T θ η x y) ω
      z 0+z 2=PredictableScalarField.nativeField (fun ω=>(Ref θ) (b,ω)) (ω,x) ∧
      z 1+z 3=PredictableScalarField.nativeField (fun ω=>(Ref θ) (b,ω)) (ω,y) ∧
      z 0+z 4=PredictableScalarField.nativeField (fun ω=>(Ref η) (b,ω)) (ω,x) ∧
      z 1+z 5=PredictableScalarField.nativeField (fun ω=>(Ref η) (b,ω)) (ω,y):=by
  have hoθ:=NativeCanonicalReferenceObservation.observation 𝓕 μ H b v P Λ κ hκ hκP
    u d hu hd hbH hb1 I0 I1 J hIJ0 hIJ1 b hvb le_rfl B0 B1 hBDG0 hBDG1 θ
  have hoη:=NativeCanonicalReferenceObservation.observation 𝓕 μ H b v P Λ κ hκ hκP
    u d hu hd hbH hb1 I0 I1 J hIJ0 hIJ1 b hvb le_rfl B0 B1 hBDG0 hBDG1 η
  have hr:0<(b:ℝ)-(v:ℝ):=sub_pos.mpr (by exact_mod_cast hvb)
  have hmean(ξ:ℝ)(x:HeatCircle)(ω:Ω):ControlledProfile.mean Λ (Data ω).1 (Data ω).2
      (ξ,((b:ℝ)-(v:ℝ),x))=functional ((b:ℝ)-(v:ℝ)) x
        (u ω+(ξ*Real.exp (-Λ*((b:ℝ)-(v:ℝ))))•d ω):=by
    unfold ControlledProfile.mean NativeCanonicalReferenceField.data
    rw [PhysicalProfile.physicalHeatMean_eq hr,PhysicalProfile.physicalHeatMean_eq hr]
    change functional ((b:ℝ)-(v:ℝ)) x (u ω)+ξ*Real.exp (-Λ*((b:ℝ)-(v:ℝ)))*
      functional ((b:ℝ)-(v:ℝ)) x (d ω)=_
    rw [map_add,map_smul]
    rfl
  filter_upwards [hoθ,hoη] with x hxθ hxη
  filter_upwards [hoθ,hoη] with y hyθ hyη
  filter_upwards [hxθ,hxη,hyθ,hyη] with ω hxθ hxη hyθ hyη
  have hc(i:Fin 6):GaussianStoppedRows.terminal 𝓕 μ H v b (R θ η x y) J 0 ω i=
      if NativeFrozenBandCovariance.sides i then
        (OrthogonalItoChannels.rightIntegral 𝓕 μ H J).integral
          (NativeFrozenGaussianObservations.scalarRow 𝓕 μ v b P Λ κ hκ hκP
            NativeFrozenBandCovariance.sides (NativeFrozenBandCovariance.parameters θ η)
            (NativeFrozenBandCovariance.centers x y) H hbH Data DataM i) ω
      else (OrthogonalItoChannels.leftIntegral 𝓕 μ H J).integral
          (NativeFrozenGaussianObservations.scalarRow 𝓕 μ v b P Λ κ hκ hκP
            NativeFrozenBandCovariance.sides (NativeFrozenBandCovariance.parameters θ η)
            (NativeFrozenBandCovariance.centers x y) H hbH Data DataM i) ω:=
    NativeFrozenGaussianObservations.terminal_coordinate 𝓕 μ v b P Λ κ hκ hκP
      NativeFrozenBandCovariance.sides (NativeFrozenBandCovariance.parameters θ η)
      (NativeFrozenBandCovariance.centers x y) H hbH Data DataM J i ω
  have h0:=hc 0
  have h1:=hc 1
  have h2:=hc 2
  have h3:=hc 3
  have h4:=hc 4
  have h5:=hc 5
  simp [NativeFrozenBandCovariance.sides,NativeFrozenBandCovariance.parameters,
    NativeFrozenBandCovariance.centers,NativeFrozenGaussianObservations.scalarRow] at h0 h1 h2 h3 h4 h5
  dsimp only [NativeFrozenGaussianLaw.terminal,means,PiLp.add_apply,WithLp.ofLp_toLp,
    NativeFrozenBandCovariance.sides,NativeFrozenBandCovariance.parameters,NativeFrozenBandCovariance.centers]
  rw [h0,h1,h2,h3,h4,h5]
  simp [hmean]
  simp only [map_add,map_smul,smul_eq_mul,neg_mul] at hxθ hxη hyθ hyη
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

end SHE.NativeFrozenPairReference
