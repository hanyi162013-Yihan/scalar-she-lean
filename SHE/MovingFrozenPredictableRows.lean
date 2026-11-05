module
public import SHE.MovingCanonicalFrozenRows
public import SHE.ParametricFrozenPredictableVersion
public import SHE.ItoStoppedParameterChannels
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SHE.MovingFrozenPredictableRows
open Set MeasureTheory PredictableL2 FiniteHaar StoppedFourier NativeHeatObservation
open OrthogonalItoChannels DyadicApproximation MovingCanonicalFrozenRows
open scoped NNReal ENNReal
local instance movingFrozenPredictableRows_unit : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance movingFrozenPredictableRows_period : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance movingFrozenPredictableRows_realSigma : MeasurableSpace RealL2:=borel _
local instance movingFrozenPredictableRows_realBorel : BorelSpace RealL2:=⟨rfl⟩
local instance movingFrozenPredictableRows_circleSigma : MeasurableSpace CircleL2:=borel _
local instance movingFrozenPredictableRows_circleBorel : BorelSpace CircleL2:=⟨rfl⟩
local instance movingFrozenPredictableRows_rowSigma : MeasurableSpace RealHaarInput:=borel _
local instance movingFrozenPredictableRows_rowBorel : BorelSpace RealHaarInput:=⟨rfl⟩
local instance movingFrozenPredictableRows_bothSigma : MeasurableSpace (Both RealHaarInput):=borel _
local instance movingFrozenPredictableRows_bothBorel : BorelSpace (Both RealHaarInput):=⟨rfl⟩
variable {Ω:Type}[MeasurableSpace Ω]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)[IsProbabilityMeasure μ](H:ℝ≥0)
variable (Λ κ:ℝ)(hκ:0<κ){aU aV:ℝ→ℝ}(haU:Measurable aU)(haV:Measurable aV){ell M:ℝ}
variable (hell:0<ell)(hbU:∀z,ell≤aU z∧aU z≤M)(hbV:∀z,ell≤aV z∧aV z≤M)
variable (I₀ I₁:StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)(u₀ v₀:RealL2)
variable (S:MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)
variable (P:CanonicalCovariance.ProfileParameters)(θ:ℝ)(hκP:κ<P.lower)(W h:ℝ)
variable (hW:0≤W)(hh:0≤h)(hcover:W+h≤H)(hH:(H:ℝ)≤1)
local notation "Field"=>MovingCanonicalFrozenRows.field 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P θ hκP W
local notation "Hfield"=>MovingCanonicalFrozenRows.field_predictable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P θ hκP W
local notation "covered"=>(fun x:Parameters=>NativeMovingGammaClock.terminal_le hW hh H hcover x.1)

/-- Genuine moving-past SAME-J residual stopped reference version.
Only the explicitly documented ordinary stopped package4 component is
assumed; every analytic SPDE-kernel condition is discharged. -/
def residual_version (ν:Measure Parameters)[IsFiniteMeasure ν]
    (J:StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
    (hF:StandardItoStoppedParameterFubini J)(hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ):=
  ParametricFrozenPredictableVersion.exists_version 𝓕 μ H (sub_pos.mpr hκP)
    (PastFrozenPrefixRows.residual_upper_nonneg P κ hκP) (past W) (terminal W h) center
    Field Hfield (past_measurable W) (terminal_measurable W h) measurable_snd.snd covered hH ν
    (rightIntegral 𝓕 μ H J) (StandardItoStoppedParameterFubini.right 𝓕 μ H J hF) hnull

/-- The common additive stopped version comes from the original LEFT
channel of the same J; no independent stochastic input is introduced. -/
def additive_version (ν:Measure Parameters)[IsFiniteMeasure ν]
    (J:StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
    (hF:StandardItoStoppedParameterFubini J)(hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ):=
  ParametricFrozenPredictableVersion.exists_version 𝓕 μ H hκ hκ.le
    (past W) (terminal W h) center
    (fun _=>AdditiveHaarForcing.constantField κ hκ) stronglyMeasurable_const
    (past_measurable W) (terminal_measurable W h) measurable_snd.snd covered hH ν
    (leftIntegral 𝓕 μ H J) (StandardItoStoppedParameterFubini.left 𝓕 μ H J hF) hnull
end SHE.MovingFrozenPredictableRows
