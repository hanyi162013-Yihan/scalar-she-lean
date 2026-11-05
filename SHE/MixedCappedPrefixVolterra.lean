module

public import SHE.MixedGirsanovVectorMild
public import SHE.TimeMeasureRestriction
public import SHE.HilbertItoNaturality
public import SHE.NativeGirsanovTwoChannelTransport
public import SHE.NativeDampedHaarInput
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

namespace SHE.MixedCappedPrefixVolterra
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


local notation "F0"=>fun _:ℝ≥0×Ω=>AdditiveHaarForcing.constantField κ hκ
local notation "F1"=>ContinuousHeatMild.coefficientFunction haV hell hbV S.second
local notation "Drift"=>MixedCappedDampedHeatControl.drift
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S


local instance : SecondCountableTopology RealL2:=realCircleIdentification.toHomeomorph.secondCountableTopology


local notation "Vec"=>MixedGirsanovVectorMild.vector 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S

/-- On the actual no-exit event the capped drift is precisely the
original damped heat Volterra convolution, with its native clock. -/
theorem no_exit(t:ℝ≥0)(ht:t≤H)(ω:Ω)
    (hcost:PredictableEnergyCap.accumulated Raw t ω<1):
    (∫s,Vec t s ω ∂timeMeasure H)=
      NativeClock.volterra Λ (fun s=>S.second s ω-S.first s ω) t:=by
  let F:ℝ≥0→RealL2:=fun s=>Real.exp (-Λ*((t:ℝ)-(s:ℝ))) •
    NativeHeatObservation.heat ((t:ℝ)-(s:ℝ)) (S.second s ω-S.first s ω)
  have hraw:=MixedCappedControl.continuous 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  have hc(s:ℝ≥0)(hs:s≤t):PredictableEnergyCap.accumulated Raw s ω<1:=by
    have hm:=CumulativeEnergyCap.monotone_cumulative
      (PredictableEnergyCap.continuous_energy Raw hraw ω)
      (fun r=>sq_nonneg ‖Raw r.toNNReal ω‖) s.2 t.2
      (show (s:ℝ)≤t by exact_mod_cast hs)
    exact hm.trans_lt hcost
  have he:(fun s=>Vec t s ω)=ᵐ[timeMeasure H] (Ioc 0 t).indicator F:=by
    filter_upwards [timeMeasure_ae_mem H,(timeMeasure H).ae_ne t] with s hs hn
    by_cases hst:s<t
    · have hmem:s∈Ioc 0 t:=⟨hs.1,hst.le⟩
      rw [Set.indicator_of_mem hmem,MixedGirsanovVectorMild.vector,if_pos ⟨hst,hc s hst.le⟩]
    · have hnot:s∉Ioc 0 t:=by
        intro hh
        exact hn (le_antisymm hh.2 (le_of_not_gt hst))
      rw [Set.indicator_of_notMem hnot,MixedGirsanovVectorMild.vector,if_neg (by tauto)]
  rw [integral_congr_ae he,integral_indicator measurableSet_Ioc,timeMeasure_restrict ht,timeMeasure_integral]
  have hv:=intervalIntegral.integral_of_le (μ:=(volume:Measure ℝ))
    (f:=fun s:ℝ=>Real.exp (-Λ*((t:ℝ)-s)) • NativeHeatObservation.heat ((t:ℝ)-s)
      (S.second s.toNNReal ω-S.first s.toNNReal ω)) t.2
  trans (∫s in Ioc (0:ℝ) (t:ℝ),Real.exp (-Λ*((t:ℝ)-s)) •
      NativeHeatObservation.heat ((t:ℝ)-s) (S.second s.toNNReal ω-S.first s.toNNReal ω))
  · apply setIntegral_congr_fun measurableSet_Ioc
    intro r hr
    dsimp only [F]
    rw [Real.coe_toNNReal _ hr.1.le]
  · exact hv.symm
end SHE.MixedCappedPrefixVolterra
