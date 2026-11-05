module
public import SHE.MixedNativeFullLeafHilbert
public import SHE.FullOrdinaryClockIdentity
public import SHE.FullOrdinaryHeatBandError
public import SHE.FullOrdinaryErrorOutput
public import SHE.ScalarHeatBandHolder
public import SHE.MixedFirstDefectActualBound
public import SHE.ScalarHeatRootBands
public import SHE.JointGammaRootHilbertPair
public import SHE.MixedFirstDefectNativeBound
public import SHE.MixedFirstDefectEnvelopeIdentity

public import SHE.MixedFirstDefectNormEnvelope
public import SHE.MixedFirstDefectConvolutionTransport
public import SHE.MixedFirstDefectMinkowski
public import SHE.MixedFirstDefectDisintegration
public import SHE.NativeBesselParameterSection
public import SHE.MixedFirstDefectIntegral
public import SHE.MixedJointActiveVolume
public import SHE.MixedFirstDefectRMS
public import SHE.ControlledReferenceFamilyDefectL1
public import SHE.RootHistoryCurrentMeasure
public import SHE.NativeBesselParameterAverageAE
public import SHE.HistoryMeasureGeometry
public import SHE.MixedCanonicalRootFields
public import SHE.DefectRelativeFactor
public import SHE.DefectCombinedTime
public import SHE.NativeBesselFieldAE
public import SHE.NativeSignedHaarProcess
public import SHE.ControlledScalarReference
public import SHE.ControlledThetaDefectEnvelope
public import SHE.MixedJointUncutDefectTrace

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1800000

namespace SHE.FullLeafClockIdentity
open Set MeasureTheory Real AddCircle StoppedFourier OrthogonalItoChannels DyadicApproximation PredictableL2
  NativeHeatObservation CutoffWordLevel CutoffWordHistories CutoffCarriers ControlledProfile
  ControlledReferenceLevel PhysicalChainArrays PhysicalParentGeometry PhysicalScoreChain HistoryProductMeasure
  CoveredControlledLaw
open scoped NNReal ENNReal BigOperators
open Classical
local instance mixedFirstDefectRMS_period:Fact (0<2*π):=⟨by positivity⟩
local instance mixedFirstDefectRMS_unit:Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance mixedFirstDefectRMS_sigma:MeasurableSpace CircleL2:=borel _
local instance mixedFirstDefectRMS_borel:BorelSpace CircleL2:=⟨rfl⟩
variable {Ω:Type}[MeasurableSpace Ω]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)[IsProbabilityMeasure μ](H:ℝ≥0)
variable (Λ κ:ℝ)(hκ:0<κ){aU aV:ℝ→ℝ}(haU:Measurable aU)(haV:Measurable aV){ell M:ℝ}
variable (hell:0<ell)(hbU:∀z,ell≤aU z ∧ aU z≤M)(hbV:∀z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁:StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)
variable (u₀:RealL2)
variable (S:MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)
variable (P:CanonicalCovariance.ProfileParameters)(hAs:SmoothCylinders.BoundedSmooth (fun z=>κ+aV z))
variable (θ:ℝ)(v b:ℝ≥0)(hvb:v≤b)
variable {a:ℝ→ℝ}(ha:SmoothCylinders.BoundedSmooth a)
local notation "Family"=>ControlledScalarReference.observations b
local notation "Root" j:max=>(fun z:WordRecursion.State 1=>ScalarHeatBands.band a (j+1) (z 0))
local notation "RootSmooth" j:max=>(ScalarHeatBands.band_boundedSmooth ha (j+1)).comp_right (EuclideanSpace.proj (0:Fin 1))
local notation "RootFamily" j:max=>(fun _:HeatCircle=>Root j)
local notation "RootUniform" j:max=>UniformSmooth.UniformBoundedSmooth.fixed (P:=HeatCircle) (RootSmooth j)
local notation "RootMeasurable" j:max=>(RootSmooth j).smooth.continuous.measurable.comp
  (measurable_snd:Measurable (Prod.snd:HeatCircle×WordRecursion.State 1→WordRecursion.State 1))
local notation "JT" j:max=>MixedCanonicalRootHilbertExpansion.term 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
  P hAs 1 v b hvb Family (JointGammaRootHilbertPair.scalarTargetBound b) (JointGammaRootHilbertPair.scalarStopBound b)
    (RootFamily j) (RootUniform j) (RootMeasurable j)


open FiniteHaar
local instance : MeasurableSpace RealL2:=borel _
local instance : BorelSpace RealL2:=⟨rfl⟩
local instance : MeasurableSpace RealHaarInput:=borel _
local instance : BorelSpace RealHaarInput:=⟨rfl⟩
local instance : MeasurableSpace (Both RealHaarInput):=borel _
local instance : BorelSpace (Both RealHaarInput):=⟨rfl⟩
variable (haP:SmoothCylinders.BoundedSmooth P.coefficient)
variable (J:StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ₀:NativeObservationNaturality.StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁:NativeObservationNaturality.StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))
variable (hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ)(hJ:StandardFiniteIto.Universal 𝓕 μ H J)
variable (hsmall:ProfileStability.memoryConstant P.lower P.holder P.exponent*
  ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)


/-- The bare Gaussian root with its original full-time native terminal
leaf, pulled back to the original nonnegative output clock. -/
def value(w:ℝ≥0)(j depth:ℕ)(hL:1≤Λ)(ρ:ℝ)(hρ:0≤ρ)(z:ℝ≥0×Ω):CircleL2:=
  MixedNativeFullLeafHilbert.field 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP w (RootFamily j) (RootUniform j) (RootMeasurable j) hL hρ depth ((z.1:ℝ),z.2)
local notation "Val"=>value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P ha haP

/-- This is literally the terminal Leaf of ActualFiniteGaussianComparison,
with the genuine joint endpoint minus the genuine ordinary-U endpoint. -/
def original(w:ℝ≥0)(j depth:ℕ)(hL:1≤Λ)(ρ:ℝ)(hρ:0≤ρ)(z:ℝ≥0×Ω):CircleL2:=
  MixedNativePairedHilbertExpansion.leaf
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S J hIJ₀ hIJ₁ hnull hJ P hAs
    (z.1-w) z.1 tsub_le_self (ControlledScalarReference.observations z.1)
    (fun _=>rfl) (fun _=>rfl) (RootFamily j) (RootUniform j) (RootMeasurable j)
    hL hρ depth z.2
local notation "Original"=>original
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P hAs ha J hIJ₀ hIJ₁ hnull hJ

include hsmall in
/-- ONE original sample event identifies the actual full-time terminal
leaf at every positive original output time, including the initial strip.
Every band keeps its own window; no same-window substitution is made. -/
theorem identity_ae(hcoeff:P.coefficient=(fun z=>κ+aV z))
    (w:ℝ≥0)(j depth:ℕ)(hL:1≤Λ)(ρ:ℝ)(hρ:0≤ρ):
    ∀ᵐω∂μ,∀t:ℝ≥0,0<t→t≤H→
      Val w j depth hL ρ hρ (t,ω)=Original w j depth hL ρ hρ (t,ω):=by
  filter_upwards [MixedNativeFullLeafHilbert.initial_ae
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP w
    (RootFamily j) (RootUniform j) (RootMeasurable j) J hIJ₀ hIJ₁ hL hρ
    hnull hJ hAs hsmall hcoeff] with ω hω
  intro t ht htH
  unfold value original
  by_cases htw:t≤w
  · simpa only [tsub_eq_zero_of_le htw] using hω t ht htw depth
  · have hwt:w<t:=lt_of_not_ge htw
    have hv:0<t-w:=tsub_pos_iff_lt.mpr hwt
    have hvt:t-w+w=t:=tsub_add_cancel_of_le hwt.le
    have hh: t-w+w≤H:=hvt.trans_le htH
    have he:=MixedNativeFullLeafHilbert.complete_eq
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP w
      (RootFamily j) (RootUniform j) (RootMeasurable j) J hIJ₀ hIJ₁ hL hρ
      hnull hJ hAs hsmall hcoeff (t-w) hv hh depth ω
    simpa only [FullOrdinaryClockIdentity.observations_shift,hvt] using he
end SHE.FullLeafClockIdentity
