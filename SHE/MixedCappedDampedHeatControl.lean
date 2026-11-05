module

public import SHE.MixedCappedHeatControl
public import SHE.NativeControlMass
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
set_option backward.isDefEq.respectTransparency true
noncomputable section

namespace SHE.MixedCappedDampedHeatControl
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

/-- Literal scalar damping drift of the capped original control. -/
def drift(L:RealL2→L[ℝ]ℝ)(t:ℝ≥0)(s:ℝ≥0)(ω:Ω):ℝ:=
  if s<t ∧ PredictableEnergyCap.accumulated Raw s ω<1 then
    Real.exp (-Λ*((t:ℝ)-(s:ℝ)))*L (NativeHeatObservation.heat ((t:ℝ)-(s:ℝ))
      (S.second s ω-S.first s ω)) else 0

/-- The heat-row/control identity is causal, with both original channels
and the actual energy-cap indicator retained pointwise. -/
theorem channels(L:RealL2→L[ℝ]ℝ)(t s:ℝ≥0)(ω:Ω):
    inner ℝ (WithLp.toLp 2
      (HilbertColumns.mapCLM L (Real.exp (-Λ*((t:ℝ)-(s:ℝ))) •
        NativeHeatObservation.kernel κ κ hκ ((t:ℝ)-(s:ℝ),AdditiveHaarForcing.constantField κ hκ)),
       HilbertColumns.mapCLM L (Real.exp (-Λ*((t:ℝ)-(s:ℝ))) •
        NativeHeatObservation.kernel ell M hell ((t:ℝ)-(s:ℝ),
          ContinuousHeatMild.coefficientFunction haV hell hbV S.second (s,ω))))) (Cap s ω)=
      -Λ*drift 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S L t s ω:=by
  by_cases hst:s<t
  · rw [WithLp.prod_inner_apply]
    change inner ℝ (HilbertColumns.mapCLM L (Real.exp (-Λ*((t:ℝ)-(s:ℝ))) •
        NativeHeatObservation.kernel κ κ hκ ((t:ℝ)-(s:ℝ),AdditiveHaarForcing.constantField κ hκ)))
      ((Cap s ω).ofLp.1)+inner ℝ (HilbertColumns.mapCLM L (Real.exp (-Λ*((t:ℝ)-(s:ℝ))) •
        NativeHeatObservation.kernel ell M hell ((t:ℝ)-(s:ℝ),
          ContinuousHeatMild.coefficientFunction haV hell hbV S.second (s,ω)))) ((Cap s ω).ofLp.2)=_
    rw [map_smul,map_smul,real_inner_smul_left,real_inner_smul_left,
      MixedCappedHeatControl.capped_residual,mul_zero,add_zero,
      MixedCappedHeatControl.capped_additive 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S L
        t s (by exact_mod_cast hst) ω]
    unfold drift
    by_cases hc:PredictableEnergyCap.accumulated Raw s ω<1
    · rw [if_pos hc,if_pos ⟨hst,hc⟩]
      ring
    · rw [if_neg hc,if_neg (by tauto : ¬(s<t ∧ PredictableEnergyCap.accumulated Raw s ω<1))]
      ring
  · have hh:(t:ℝ)-(s:ℝ)≤0:=sub_nonpos.mpr (by exact_mod_cast le_of_not_gt hst)
    rw [NativeHeatObservation.kernel_zero hκ hh,NativeHeatObservation.kernel_zero hell hh]
    simp only [smul_zero,map_zero]
    change inner ℝ (0:Both RealHaarInput) (Cap s ω)=_
    rw [inner_zero_left,drift,if_neg (by tauto : ¬(s<t ∧ PredictableEnergyCap.accumulated Raw s ω<1)),mul_zero]

/-- The actual stopped scalar drift has genuine full-horizon time L1
on every continuous sample path, without a moment substitution. -/
theorem drift_integrable(L:RealL2→L[ℝ]ℝ)(t:ℝ≥0)(ω:Ω):
    Integrable (fun s=>drift 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S L t s ω) (timeMeasure H):=by
  have hD:Continuous (fun s:ℝ≥0=>S.second s ω-S.first s ω):=
    (S.second_continuous ω).sub (S.first_continuous ω)
  have hmap:Continuous (fun s:ℝ≥0=>(((t:ℝ)-(s:ℝ))/NativeHeatObservation.timeScale,
      S.second s ω-S.first s ω)):=
    ((continuous_const.sub continuous_subtype_val).div_const NativeHeatObservation.timeScale).prodMk hD
  have hh:=RealHeat.continuous_realHeat_action.comp hmap
  have hb:Continuous (fun s:ℝ≥0=>Real.exp (-Λ*((t:ℝ)-(s:ℝ)))*
      L (NativeHeatObservation.heat ((t:ℝ)-(s:ℝ)) (S.second s ω-S.first s ω))):=
    (show Continuous (fun s:ℝ≥0=>Real.exp (-Λ*((t:ℝ)-(s:ℝ)))) by fun_prop).mul (L.continuous.comp hh)
  have hm:MeasurableSet {s:ℝ≥0|s<t ∧ PredictableEnergyCap.accumulated Raw s ω<1}:=
    measurableSet_Iio.inter (measurableSet_lt
      (PredictableEnergyCap.accumulated_continuous Raw
        (MixedCappedControl.continuous 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S) ω).measurable measurable_const)
  apply ((NativeControlMass.continuous_integrable H hb).indicator hm).congr
  apply ae_of_all
  intro s
  by_cases hs:s<t ∧ PredictableEnergyCap.accumulated Raw s ω<1
  · have hs' : s∈{r:ℝ≥0 | r<t ∧ PredictableEnergyCap.accumulated Raw r ω<1} := hs
    simp only [Set.indicator_of_mem hs', drift, if_pos hs]
  · have hs' : s∉{r:ℝ≥0 | r<t ∧ PredictableEnergyCap.accumulated Raw r ω<1} := hs
    simp only [Set.indicator_of_notMem hs', drift, if_neg hs]
end SHE.MixedCappedDampedHeatControl
