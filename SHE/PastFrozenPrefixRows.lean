module

public import SHE.FrozenReferenceFields
public import SHE.AdditiveHaarForcing
public import SHE.NativeObservationCaps
public import SHE.FiniteReferenceSplice

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
namespace SHE.PastFrozenPrefixRows
open MeasureTheory Set PredictableL2 FiniteHaar StoppedFourier OrthogonalItoChannels ControlledProfile
open scoped NNReal ENNReal
local instance pastFrozenPrefixRows_periodPositive : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance pastFrozenPrefixRows_circleSigma : MeasurableSpace CircleL2 := borel _
local instance pastFrozenPrefixRows_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance pastFrozenPrefixRows_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance pastFrozenPrefixRows_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance pastFrozenPrefixRows_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance pastFrozenPrefixRows_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (P : CanonicalCovariance.ProfileParameters) (Λ κ θ : ℝ) (hκ0 : 0<κ) (hκP : κ<P.lower)
variable (v : ℝ≥0) (data : Ω → Inputs) (hdata : Measurable[𝓕 v] data)
variable {n : ℕ} (Z : Fin n→WordRecursion.Observation) (c : ℝ≥0)
variable (hgap : ∀ i,(c:ℝ)<(Z i).target)

include hκP in
theorem residual_upper_nonneg : 0≤P.upper-κ := by
  have := P.lower_bound 0
  have := P.upper_bound 0
  linarith

/-- Literal common additive plus F_v-frozen residual reference rows on
a positive-gap prefix of their ORIGINAL heat targets. -/
def rows (i : Fin n) : Process (E:=Both RealHaarInput) 𝓕 μ H :=
  TwoChannelItoRows.block 𝓕 μ H
    (NativeObservationProcess.process 𝓕 μ H hκ0 hκ0.le
      (fun _ => AdditiveHaarForcing.constantField κ hκ0) stronglyMeasurable_const (hgap i) (Z i).center)
    (NativeObservationProcess.process 𝓕 μ H (sub_pos.mpr hκP) (residual_upper_nonneg P κ hκP)
      (FrozenReferenceFields.field P Λ κ θ hκP v data)
      (FrozenReferenceFields.field_predictable 𝓕 P Λ κ θ hκP v data hdata) (hgap i) (Z i).center)

/-- Every row bound is derived from true coefficient ellipticity. The
past data may be unbounded and correlated with all later rows. -/
theorem rows_bound (i : Fin n) :
    ∀ᵐ p ∂energyMeasure μ H,‖rows 𝓕 μ H P Λ κ θ hκ0 hκP v data hdata Z c hgap i p‖^2≤
      NativeObservationCaps.cap P.upper ((Z i).target-(c:ℝ)) := by
  have h0 := NativeObservationCaps.process_bound 𝓕 μ H hκ0 hκ0.le
    (fun _ => AdditiveHaarForcing.constantField κ hκ0) stronglyMeasurable_const (hgap i) (Z i).center
  have h1 := NativeObservationCaps.process_bound 𝓕 μ H (sub_pos.mpr hκP) (residual_upper_nonneg P κ hκP)
    (FrozenReferenceFields.field P Λ κ θ hκP v data)
    (FrozenReferenceFields.field_predictable 𝓕 P Λ κ θ hκP v data hdata) (hgap i) (Z i).center
  have hh := NativeObservationCaps.block_bound 𝓕 μ H _ _ h0 h1
  filter_upwards [hh] with p hp
  exact hp.trans_eq (by unfold NativeObservationCaps.cap; ring)

end SHE.PastFrozenPrefixRows
