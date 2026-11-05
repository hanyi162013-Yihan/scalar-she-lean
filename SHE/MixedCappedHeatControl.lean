module

public import SHE.MixedCappedControl
public import SHE.NativeHeatColumnAction
public import SHE.MovingPastFractional
public import SHE.MeanCurrentFields
public import SHE.ControlledMeans
public import SHE.TimeMeasureMass
public import SHE.MixedMovingEnergy
public import SHE.MixedAdditiveControl
public import SHE.CappedStochasticExponential

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.MixedCappedHeatControl
open Set MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
  FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation ControlledProfile
open scoped NNReal ENNReal
local instance mixedMovingEnergy_instance1 : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance mixedMovingEnergy_instance2 : Fact ((2:ENNReal)≠⊤) := ⟨by simp⟩
local instance mixedMovingEnergy_instance3 : MeasurableSpace RealL2 := borel _
local instance mixedMovingEnergy_instance4 : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedMovingEnergy_instance5 : MeasurableSpace CircleL2 := borel _
local instance mixedMovingEnergy_instance6 : BorelSpace CircleL2 := ⟨rfl⟩
local instance mixedMovingEnergy_instance7 : MeasurableSpace RealHaarInput := borel _
local instance mixedMovingEnergy_instance8 : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedMovingEnergy_instance9 : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedMovingEnergy_instance10 : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
local instance mixedMovingEnergy_instance11 : MeasurableSpace RealHaarIntegrand.Columns := borel _
local instance mixedMovingEnergy_instance12 : BorelSpace RealHaarIntegrand.Columns := ⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)
variable (u₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)


local notation "Raw"=>MixedCappedControl.raw 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
local notation "Cap"=>PredictableEnergyCap.capped Raw

/-- The original additive heat row paired with the actual Haar control
is precisely the negative heated damping drift. -/
theorem additive(L:RealL2→L[ℝ]ℝ)(t:ℝ)(s:ℝ≥0)(hst:(s:ℝ)<t)(ω:Ω):
    inner ℝ (HilbertColumns.mapCLM L (NativeHeatObservation.kernel κ κ hκ
      (t-(s:ℝ),AdditiveHaarForcing.constantField κ hκ))) ((Raw s ω).ofLp.1)=
      -Λ*L (NativeHeatObservation.heat (t-(s:ℝ)) (S.second s ω-S.first s ω)):=by
  rw [NativeHeatColumnAction.additive hκ (sub_pos.mpr hst),
    MixedCappedControl.reconstruct]
  simp only [map_neg,map_smul,smul_eq_mul,neg_mul]

/-- The actual control has no residual-noise component. -/
theorem residual(R:RealHaarInput)(s:ℝ≥0)(ω:Ω):
    inner ℝ R ((Raw s ω).ofLp.2)=0:=by
  change inner ℝ R (0:RealHaarInput)=0
  exact inner_zero_right _

/-- Both original channels retain the same drift identity after the
energy stopping cap, with the literal accumulated-control indicator. -/
theorem capped_additive(L:RealL2→L[ℝ]ℝ)(t:ℝ)(s:ℝ≥0)(hst:(s:ℝ)<t)(ω:Ω):
    inner ℝ (HilbertColumns.mapCLM L (NativeHeatObservation.kernel κ κ hκ
      (t-(s:ℝ),AdditiveHaarForcing.constantField κ hκ))) ((Cap s ω).ofLp.1)=
      if PredictableEnergyCap.accumulated Raw s ω<1 then
        -Λ*L (NativeHeatObservation.heat (t-(s:ℝ)) (S.second s ω-S.first s ω)) else 0:=by
  unfold PredictableEnergyCap.capped
  split_ifs with hs
  · exact additive 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S L t s hst ω
  · change inner ℝ _ (0:RealHaarInput)=0
    exact inner_zero_right _

theorem capped_residual(R:RealHaarInput)(s:ℝ≥0)(ω:Ω):
    inner ℝ R ((Cap s ω).ofLp.2)=0:=by
  unfold PredictableEnergyCap.capped
  split_ifs
  · exact residual 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S R s ω
  · change inner ℝ R (0:RealHaarInput)=0
    exact inner_zero_right _

/-- Exact original two-channel scalar Girsanov drift, for any residual
row and every deterministic continuous linear observation. -/
theorem capped_channels(L:RealL2→L[ℝ]ℝ)(R:RealHaarInput)(t:ℝ)(s:ℝ≥0)
    (hst:(s:ℝ)<t)(ω:Ω):
    inner ℝ (left (HilbertColumns.mapCLM L (NativeHeatObservation.kernel κ κ hκ
      (t-(s:ℝ),AdditiveHaarForcing.constantField κ hκ)))+right R) (Cap s ω)=
      if PredictableEnergyCap.accumulated Raw s ω<1 then
        -Λ*L (NativeHeatObservation.heat (t-(s:ℝ)) (S.second s ω-S.first s ω)) else 0:=by
  rw [inner_add_left,WithLp.prod_inner_apply,WithLp.prod_inner_apply]
  change (inner ℝ (HilbertColumns.mapCLM L (NativeHeatObservation.kernel κ κ hκ
      (t-(s:ℝ),AdditiveHaarForcing.constantField κ hκ))) ((Cap s ω).ofLp.1)+
    inner ℝ (0:RealHaarInput) ((Cap s ω).ofLp.2))+
    (inner ℝ (0:RealHaarInput) ((Cap s ω).ofLp.1)+inner ℝ R ((Cap s ω).ofLp.2))=_
  simp only [inner_zero_left,zero_add,add_zero]
  rw [capped_additive 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S L t s hst ω,
    capped_residual 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S R s ω,add_zero]

end SHE.MixedCappedHeatControl
