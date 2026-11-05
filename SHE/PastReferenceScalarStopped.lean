module

public import SHE.PastReferenceScalarObservation
public import SHE.TwoChannelPastDifference
public import SHE.PastFrozenPrefixRows
public import SHE.NativeObservationNaturality
public import SHE.PastReferencePropagation
public import SHE.NativeColumnHeatSemigroup
public import SHE.HilbertItoNaturality
public import SHE.PastReferenceStopped
public import SHE.PastReferenceIntegral
public import SHE.PastReferenceInput
public import SHE.PastItoAlgebra
public import SHE.RealMomentBound

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2100000
set_option backward.isDefEq.respectTransparency true
noncomputable section

namespace SHE.PastReferenceScalarStopped
open Set MeasureTheory PredictableL2 ControlledProfile StoppedFourier PastItoInputs PastReferenceBracket StoppedItoInputs
open scoped NNReal ENNReal
local instance pastReferencePropagatedIntegral_instance1 : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance pastReferencePropagatedIntegral_instance2 : Fact ((2:ENNReal)≠⊤) := ⟨by simp⟩
local instance pastReferencePropagatedIntegral_instance3 : MeasurableSpace CircleL2 := borel _
local instance pastReferencePropagatedIntegral_instance4 : BorelSpace CircleL2 := ⟨rfl⟩
local instance pastReferencePropagatedIntegral_instance5 : MeasurableSpace RealHaarIntegrand.Columns := borel _
local instance pastReferencePropagatedIntegral_instance6 : BorelSpace RealHaarIntegrand.Columns := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
variable (P : CanonicalCovariance.ProfileParameters) {Λ κ : ℝ} (hΛ : 0≤Λ) (hκ : κ<P.lower)
variable (θ η : ℝ)
variable (hsmall : ProfileStability.memoryConstant P.lower P.holder P.exponent *
  ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)
variable (H v b : ℝ≥0) (hvb : v<b) (hbH : b≤H) (hsmallTime : (b:ℝ)-(v:ℝ)≤P.horizon)
variable (data : Ω → Inputs) (hdata : Measurable[𝓕 v] data)
variable (hdi : Integrable (fun ω => ‖(data ω).2‖^2) μ)
local notation "Input" => input 𝓕 μ P hΛ hκ θ η hsmall H v b hvb hbH hsmallTime data hdata hdi
local notation "Cref" => energyConstant P κ θ η ((b:ℝ)-(v:ℝ))

attribute [local irreducible] PastReferenceBracket.input
open NativeHeatObservation NativeColumnHeatSemigroup
local instance pastReferencePropagatedIntegral_unitPositive : Fact (0<(1:ℝ)) := ⟨zero_lt_one⟩

local instance pastReferencePropagatedIntegral_realSigma : MeasurableSpace DyadicApproximation.RealL2 := borel _
local instance pastReferencePropagatedIntegral_realBorel : BorelSpace DyadicApproximation.RealL2 := ⟨rfl⟩
local instance pastReferencePropagatedIntegral_rowSigma : MeasurableSpace FiniteHaar.RealHaarInput := borel _
local instance pastReferencePropagatedIntegral_rowBorel : BorelSpace FiniteHaar.RealHaarInput := ⟨rfl⟩


local notation "Row"=>PastReferenceScalarObservation.row 𝓕 μ P (Λ:=Λ) hκ H v b data hdata

theorem row_stopped (T:ℝ) (ht:(b:ℝ)<T) (ξ:ℝ) (x:HeatCircle):
    stop 𝓕 μ H b (Row T ht ξ x)=Row T ht ξ x:=by
  apply PastItoAlgebra.eq_of_ambient_ae
  have hr:=NativeObservationProcess.process_ae 𝓕 μ H (sub_pos.mpr hκ)
    (PastFrozenPrefixRows.residual_upper_nonneg P κ hκ)
    (FrozenReferenceFields.field P Λ κ ξ hκ v data)
    (FrozenReferenceFields.field_predictable 𝓕 P Λ κ ξ hκ v data hdata) ht x
  filter_upwards [stop_ae 𝓕 μ H b (Row T ht ξ x),hr] with z hs hr
  change Row T ht ξ x z=_ at hr
  rw [hs]
  by_cases hz:z∈before (Ω:=Ω) (b:ℝ)
  · rw [indicator_of_mem hz]
  · rw [indicator_of_notMem hz,hr,NativeObservationProcess.integrand_eq (sub_pos.mpr hκ)
      (FrozenReferenceFields.field P Λ κ ξ hκ v data) ht]
    rw [if_neg (show ¬(z.1:ℝ)<(b:ℝ) from hz)]

/-- Exact stopped two-channel version of the scalar observation identity.
The original common additive channel cancels, while the residual is the
SAME original Hilbert Ito input already used for compatible moments. -/
theorem observe_two_channel
    (I:StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=DyadicApproximation.RealL2) 𝓕 μ H)
    (J:StandardTerminalIto (C:=OrthogonalItoChannels.Both FiniteHaar.RealHaarInput) (E:=ℝ) 𝓕 μ H)
    (hIJ:NativeObservationNaturality.StandardScalarNaturality I (OrthogonalItoChannels.rightIntegral 𝓕 μ H J))
    (A:Process (E:=FiniteHaar.RealHaarInput) 𝓕 μ H)
    (T:ℝ) (ht:(b:ℝ)<T) (x:HeatCircle):
    (fun ω=>functional (T-(b:ℝ)) x (I.integral Input ω))=ᵐ[μ]
      (fun ω=>J.integral (stop 𝓕 μ H b (post 𝓕 μ H v
        (TwoChannelItoRows.block 𝓕 μ H A (Row T ht θ x)))) ω-
      J.integral (stop 𝓕 μ H b (post 𝓕 μ H v
        (TwoChannelItoRows.block 𝓕 μ H A (Row T ht η x)))) ω):=by
  have hs:stop 𝓕 μ H b (post 𝓕 μ H v (Row T ht θ x-Row T ht η x))=
      post 𝓕 μ H v (Row T ht θ x-Row T ht η x):=by
    rw [TwoChannelPastDifference.stop_post,StoppedDampingClock.stop_sub,
      row_stopped 𝓕 μ P hκ H v b data hdata T ht θ x,
      row_stopped 𝓕 μ P hκ H v b data hdata T ht η x]
  have he:=PastReferenceScalarObservation.observe_integral
    𝓕 μ P hΛ hκ θ η hsmall H v b hvb hbH hsmallTime data hdata hdi I
    (OrthogonalItoChannels.rightIntegral 𝓕 μ H J) hIJ T ht x
  rw [←hs] at he
  have hd:=TwoChannelPastDifference.integral_difference 𝓕 μ H J v b A (Row T ht θ x) (Row T ht η x)
  have hc:=Lp.coeFn_sub
    (J.integral (stop 𝓕 μ H b (post 𝓕 μ H v (TwoChannelItoRows.block 𝓕 μ H A (Row T ht θ x)))))
    (J.integral (stop 𝓕 μ H b (post 𝓕 μ H v (TwoChannelItoRows.block 𝓕 μ H A (Row T ht η x)))))
  rw [hd] at hc
  exact he.trans hc

end SHE.PastReferenceScalarStopped
