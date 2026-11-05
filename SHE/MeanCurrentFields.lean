module

public import SHE.MeanInputTimeFields

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.ActualMeanKernel
open Set MeasureTheory Real StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
  CutoffCarriers PhysicalScoreChain HistoryProductMeasure QuarterSpatialEvent
local instance meanCurrentFields_nativePositive0 : Fact (0<2*π) := ⟨by positivity⟩
variable {Ω : Type} [MeasurableSpace Ω] {R : ReferenceData}
variable (L : CutoffWordLevel.Level R HeatCircle 1)

theorem meanInput_zero_after_terminal (T : ℝ) (hT : ∀ p,L.terminal p=T)
    (k : ℕ) (mass ρ : ℝ) (hmass : 1≤mass) (hρ : 0≤ρ)
    (damping q : ℝ) (hq : T≤q) (m : Ω→History HeatCircle k→WordRecursion.State (1+k))
    (V : Ω→DyadicApproximation.RealL2) (t : Fin k→ℝ) (ω : Ω) :
    meanInput L k mass ρ hmass hρ damping q m V (t,ω)=0 := by
  apply meanInput_zero_of_not_active L T hT k mass ρ hmass hρ damping q m V t
  intro ha
  have hterm : fixedTerminal (R:=R) T k t≤T := by
    rw [←terminal_separated L T hT k t (0:HeatCircle) (fun _ => (0:HeatCircle))]
    simpa only [PhysicalScoreChain.initialTerminal,HistoryProductMeasure.root_separated,hT] using
      PhysicalScoreChain.terminal_le_initial L k
        (HistoryProductMeasure.separated k ((0:HeatCircle),t,fun _ => (0:HeatCircle)))
  exact (not_lt_of_ge (hterm.trans hq)) ha.2

theorem meanAverage_zero_after_terminal (T : ℝ) (hT : ∀ p,L.terminal p=T)
    (k : ℕ) (ν : Measure (Fin k→ℝ)) (mass ρ : ℝ) (hmass : 1≤mass) (hρ : 0≤ρ)
    (damping q : ℝ) (hq : T≤q) (m : Ω→History HeatCircle k→WordRecursion.State (1+k))
    (V : Ω→DyadicApproximation.RealL2) (ω : Ω) :
    meanAverage L k ν mass ρ hmass hρ damping q m V ω=0 := by
  unfold meanAverage
  simp only [meanInput_zero_after_terminal L T hT k mass ρ hmass hρ damping q hq m V,integral_zero]

end SHE.ActualMeanKernel

namespace SHE.ActualInterpolatedMeanFields
open Set Filter MeasureTheory ProbabilityTheory Real AddCircle PredictableL2 NativeHeatObservation
  OrthogonalItoChannels DyadicApproximation StoppedFourier WordRecursion CutoffWordLevel
  CutoffWordHistories CutoffCarriers ActualMeanKernel FullResidualInterpolatedWeightedMoments
open scoped NNReal ENNReal
local instance meanCurrentFields_nativePositive : Fact (0<2*π) := ⟨by positivity⟩
local instance meanCurrentFields_finiteExponent : Fact ((2:ℝ≥0∞)≠⊤) := ⟨by simp⟩
local instance meanCurrentFields_realSigma : MeasurableSpace RealL2 := borel _
local instance meanCurrentFields_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance meanCurrentFields_nativeSigma : MeasurableSpace CircleL2 := borel _
local instance meanCurrentFields_nativeBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)
variable (P : CanonicalCovariance.ProfileParameters) (haP : SmoothCylinders.BoundedSmooth P.coefficient)
variable (θ : ℝ)
variable (L : CutoffWordLevel.Level
  (ControlledWordLevel.referenceData P haP Λ (embed u₀) (embed (v₀-u₀)) θ) HeatCircle 1)

/-- True joint current-time/sample/history measurability of the literal
theta mean; its covariance and current state remain at the same q. -/
theorem actual_mean_time_measurable (k : ℕ) :
    Measurable (fun z : (ℝ≥0×Ω)×History HeatCircle k=>actualMean
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P haP θ L k z.1.1 z.1.2 z.2) := by
  have hU := ((S.first_predictable.mono (predictable_le_product 𝓕)).measurable)
  have hV := ((S.second_predictable.mono (predictable_le_product 𝓕)).measurable)
  exact JointInterpolationAlgebra.current_variable_time_measurable (carrier L k).observations
    Λ θ (fun z : ℝ≥0×Ω=>(z.1:ℝ)) (measurable_subtype_coe.comp measurable_fst)
    (fun z=>S.first z.1 z.2) (fun z=>S.second z.1 z.2) hU hV

theorem current_energy_measurable :
    Measurable (fun q : ℝ≥0=>∫ ω,‖S.second q ω-S.first q ω‖^2 ∂μ) := by
  have hD := ((S.second_predictable.mono (predictable_le_product 𝓕)).measurable).sub
    ((S.first_predictable.mono (predictable_le_product 𝓕)).measurable)
  exact (hD.norm.pow_const 2).stronglyMeasurable.integral_prod_right'.measurable

attribute [local irreducible] FullResidualInterpolatedWeightedMoments.actualMean

theorem actual_meanAverage_time_measurable (T : ℝ) (hT : ∀ x,L.terminal x=T)
    (k : ℕ) (ν : Measure (Fin k→ℝ)) [SFinite ν] (hΛ : 0≤Λ)
    (mass ρ : ℝ) (hmass : 1≤mass) (hρ : 0≤ρ) :
    Measurable (fun z : ℝ≥0×Ω=>meanAverage L k ν mass ρ hmass hρ Λ z.1
      (actualMean 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P haP θ L k z.1)
      (fun ω=>S.second z.1 ω-S.first z.1 ω) z.2) := by
  let m := actualMean 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P haP θ L k
  have hm : Measurable (fun z : (ℝ≥0×Ω)×History HeatCircle k=>m z.1.1 z.1.2 z.2) :=
    actual_mean_time_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S P haP θ L k
  let V : ℝ≥0×Ω→RealL2 := fun z=>S.second z.1 z.2-S.first z.1 z.2
  have hV : Measurable V :=
    ((S.second_predictable.mono (predictable_le_product 𝓕)).measurable).sub
      ((S.first_predictable.mono (predictable_le_product 𝓕)).measurable)
  have hmean := meanAverage_time_measurable L T hT k ν mass ρ hmass hρ Λ hΛ m hm V hV
  convert! hmean using 1

end SHE.ActualInterpolatedMeanFields
