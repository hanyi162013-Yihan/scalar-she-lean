module
public import SHE.ParametricStoppedHaarVersion
public import SHE.JointFrozenReferenceFields
public import SHE.ItoParameterFubiniChannels
public import SHE.NativeMovingGammaClock
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SHE.MovingCanonicalFrozenRows
open Set MeasureTheory PredictableL2 FiniteHaar StoppedFourier NativeHeatObservation
open OrthogonalItoChannels DyadicApproximation
open scoped NNReal ENNReal
local instance movingCanonicalFrozenRows_unit : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance movingCanonicalFrozenRows_period : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance movingCanonicalFrozenRows_realSigma : MeasurableSpace RealL2:=borel _
local instance movingCanonicalFrozenRows_realBorel : BorelSpace RealL2:=⟨rfl⟩
local instance movingCanonicalFrozenRows_circleSigma : MeasurableSpace CircleL2:=borel _
local instance movingCanonicalFrozenRows_circleBorel : BorelSpace CircleL2:=⟨rfl⟩
local instance movingCanonicalFrozenRows_unitSigma : MeasurableSpace CircleHeat.CircleL2:=borel _
local instance movingCanonicalFrozenRows_unitBorel : BorelSpace CircleHeat.CircleL2:=⟨rfl⟩
local instance movingCanonicalFrozenRows_rowSigma : MeasurableSpace RealHaarInput:=borel _
local instance movingCanonicalFrozenRows_rowBorel : BorelSpace RealHaarInput:=⟨rfl⟩
local instance movingCanonicalFrozenRows_bothSigma : MeasurableSpace (Both RealHaarInput):=borel _
local instance movingCanonicalFrozenRows_bothBorel : BorelSpace (Both RealHaarInput):=⟨rfl⟩

abbrev Parameters:=ℝ×(ℝ≥0×HeatCircle)
def past (W:ℝ)(x:Parameters):ℝ≥0:=NativeMovingGammaClock.past W x.1
def terminal (W h:ℝ)(x:Parameters):ℝ≥0:=NativeMovingGammaClock.terminal W h x.1
def current (W h:ℝ)(x:Parameters):ℝ≥0:=min (terminal W h x) (max (past W x) x.2.1)
def center (x:Parameters):HeatCircle:=x.2.2

theorem past_measurable (W:ℝ):Measurable (past W):=
  (NativeMovingGammaClock.past_measurable W).comp measurable_fst
theorem terminal_measurable (W h:ℝ):Measurable (terminal W h):=
  (NativeMovingGammaClock.terminal_measurable W h).comp measurable_fst
theorem current_measurable (W h:ℝ):Measurable (current W h):=
  (terminal_measurable W h).min ((past_measurable W).max measurable_snd.fst)
theorem current_le (W h:ℝ)(x:Parameters):current W h x≤terminal W h x:=min_le_left _ _
theorem current_eq {W h:ℝ}(x:Parameters)(hv:past W x≤x.2.1)(hb:x.2.1≤terminal W h x):
    current W h x=x.2.1:=by rw [current,max_eq_right hv,min_eq_right hb]

variable {Ω:Type}[MeasurableSpace Ω]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)[IsProbabilityMeasure μ](H:ℝ≥0)
variable (Λ κ:ℝ)(hκ:0<κ){aU aV:ℝ→ℝ}(haU:Measurable aU)(haV:Measurable aV){ell M:ℝ}
variable (hell:0<ell)(hbU:∀z,ell≤aU z∧aU z≤M)(hbV:∀z,ell≤aV z∧aV z≤M)
variable (I₀ I₁:StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)(u₀ v₀:RealL2)
variable (S:MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)
variable (P:CanonicalCovariance.ProfileParameters)(θ:ℝ)(hκP:κ<P.lower)(W h:ℝ)

def field (z:Parameters×(ℝ≥0×Ω)):EllipticField (P.lower-κ) (P.upper-κ):=
  FrozenReferenceFields.field P Λ κ θ hκP (past W z.1)
    (MixedNativeFrozenPrefixIto.data 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (past W z.1)) z.2

theorem field_predictable:
    StronglyMeasurable[((inferInstance:MeasurableSpace Parameters).prod 𝓕.predictable)]
      (field 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P θ hκP W):=by
  letI:MeasurableSpace (ℝ≥0×Ω):=𝓕.predictable
  have hf:=JointFrozenReferenceFields.actual_field_predictable 𝓕 P Λ κ θ hκP μ H hκ
    haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
  have hp:Measurable (fun z:Parameters×(ℝ≥0×Ω)=>(past W z.1,z.2)):=
    ((past_measurable W).comp measurable_fst).prodMk measurable_snd
  have hc:=hf.comp_measurable hp
  exact hc

local notation "Field"=>field 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P θ hκP W
local notation "Hfield"=>field_predictable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P θ hκP W
variable (hW:0≤W)(hh:0≤h)(hcover:W+h≤H)(hH:(H:ℝ)≤1)
local notation "covered"=>(fun x:Parameters=>NativeMovingGammaClock.terminal_le hW hh H hcover x.1)

/-- SAME-original-J joint parameter versions for the actual residual
frozen reference rows. All joint predictability and finite parameter
square-energy conditions are proved, including the endpoint stop. -/
def residual_version (ν:Measure Parameters)[IsFiniteMeasure ν]
    (J:StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)(hF:StandardItoParameterFubini J):=
  ParametricStoppedHaarVersion.exists_version 𝓕 μ H (sub_pos.mpr hκP)
    (PastFrozenPrefixRows.residual_upper_nonneg P κ hκP)
    (past W) (terminal W h) (current W h) center Field Hfield
    (past_measurable W) (terminal_measurable W h) (current_measurable W h) measurable_snd.snd
    (current_le W h) covered hH ν (rightIntegral 𝓕 μ H J)
    (StandardItoParameterFubini.right 𝓕 μ H J hF)

/-- The additive channel is derived from the SAME full J as well;
no independently supplied scalar stochastic-Fubini package is used. -/
def additive_version (ν:Measure Parameters)[IsFiniteMeasure ν]
    (J:StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)(hF:StandardItoParameterFubini J):=
  ParametricStoppedHaarVersion.exists_version 𝓕 μ H hκ hκ.le
    (past W) (terminal W h) (current W h) center
    (fun _=>AdditiveHaarForcing.constantField κ hκ) stronglyMeasurable_const
    (past_measurable W) (terminal_measurable W h) (current_measurable W h) measurable_snd.snd
    (current_le W h) covered hH ν (leftIntegral 𝓕 μ H J)
    (StandardItoParameterFubini.left 𝓕 μ H J hF)
end SHE.MovingCanonicalFrozenRows
