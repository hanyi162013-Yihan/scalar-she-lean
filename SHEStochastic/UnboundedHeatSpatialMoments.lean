module

public import SHEStochastic.UnboundedHeatFamily

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
noncomputable section

namespace SHEStochastic.UnboundedHeatSpatialMoments
open MeasureTheory SHE SHE.PredictableL2 SHE.StoppedFourier SHE.NativeHeatSpan AddCircle
open UnboundedHeatFamily
open scoped NNReal ENNReal

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

variable {Ω E V : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
  (U : ℝ≥0 × Ω → Lp E 2 (haarAddCircle (T := 2 * Real.pi)))
  (hU : StronglyMeasurable[F.predictable] U)
  {G : E → V} {C β : ℝ≥0} (hG : HolderWith C β G) (hβ : 0 < β) (hβ1 : β < 1)

def energyCap (G : E → V) (C β : ℝ≥0) (R : ℝ) (T : ℝ≥0) (a b : HeatCircle) : ℝ≥0∞ :=
  ENNReal.ofReal (2 * (‖G 0‖ + (C : ℝ)) ^ 2 * 4 ^ (β : ℝ) *
    SublinearHeatSpatialIncrement.smallTimeConstant ^ (1 + (β : ℝ)) *
      (‖unitCenter a - unitCenter b‖ ^ 2) ^ ((1 - (β : ℝ)) / 4)) *
        SublinearHeatIntegratedEnergy.stateFactor R β *
          ENNReal.ofReal ((T : ℝ) ^ ((1 - (β : ℝ)) / 4) / ((1 - (β : ℝ)) / 4))

theorem family_bracket_bound (μ : Measure Ω) [IsProbabilityMeasure μ] (H T : ℝ≥0)
    (hTH : T ≤ H) (hT : (T : ℝ) ≤ 1) (a b : HeatCircle) {R : ℝ}
    (hbound : ∀ᵐ p ∂energyMeasure μ H, ‖U p‖ ≤ R) :
    ∀ᵐ ω ∂μ, (∫⁻ s, ENNReal.ofReal
      (‖family F U hU hG hβ hβ1 T a (s, ω) - family F U hU hG hβ hβ1 T b (s, ω)‖ ^ 2) ∂timeMeasure H) ≤
        energyCap G C β R T a b := by
  have hs := (Measure.measurePreserving_swap (μ := μ) (ν := timeMeasure H)).quasiMeasurePreserving.ae hbound
  filter_upwards [Measure.ae_ae_of_ae_prod hs] with ω hω
  have hh := SublinearHeatIntegratedEnergy.spatial_bound hG hβ1 T H hTH hT a b (fun s ↦ U (s, ω)) hω
  change _ ≤ energyCap G C β R T a b at hh
  exact (lintegral_congr fun s ↦ spatial_energy F U hU hG hβ hβ1 T a b (s, ω)).trans_le hh

theorem input_bracket_bound (μ : Measure Ω) [IsProbabilityMeasure μ] (H T : ℝ≥0)
    (hTH : T ≤ H) (hT : (T : ℝ) ≤ 1) (a b : HeatCircle) {R : ℝ}
    (hbound : ∀ᵐ p ∂energyMeasure μ H, ‖U p‖ ≤ R) :
    ∀ᵐ ω ∂μ, (∫⁻ s, ENNReal.ofReal
      (‖(input F U hU hG hβ hβ1 μ H T hTH hT a hbound -
        input F U hU hG hβ hβ1 μ H T hTH hT b hbound) (s, ω)‖ ^ 2) ∂timeMeasure H) ≤
          energyCap G C β R T a b := by
  let va := input F U hU hG hβ hβ1 μ H T hTH hT a hbound
  let vb := input F U hU hG hβ hβ1 μ H T hTH hT b hbound
  have he : va - vb =ᵐ[energyMeasure μ H] fun p ↦
      family F U hU hG hβ hβ1 T a p - family F U hU hG hβ hβ1 T b p := by
    filter_upwards [ae_eq_of_ae_eq_trim (Lp.coeFn_sub va vb),
      input_ae F U hU hG hβ hβ1 μ H T hTH hT a hbound,
      input_ae F U hU hG hβ hβ1 μ H T hTH hT b hbound] with p hs ha hb
    simp only [Pi.sub_apply] at hs
    exact hs.trans (by rw [ha, hb])
  have hs := (Measure.measurePreserving_swap (μ := μ) (ν := timeMeasure H)).quasiMeasurePreserving.ae he
  filter_upwards [Measure.ae_ae_of_ae_prod hs,
    family_bracket_bound F U hU hG hβ hβ1 μ H T hTH hT a b hbound] with ω he hb
  exact (lintegral_congr_ae (he.mono fun _ hx ↦ congrArg (fun v ↦ ENNReal.ofReal (‖v‖ ^ 2)) hx)).trans_le hb

/-- Spatial differences of the ACTUAL native stochastic observations
have arbitrary dyadic moments, with explicit positive distance powers. -/
theorem native_moment (μ : Measure Ω) [IsProbabilityMeasure μ] (H T : ℝ≥0)
    (hTH : T ≤ H) (hT : (T : ℝ) ≤ 1) (a b : HeatCircle) {R : ℝ}
    (hbound : ∀ᵐ p ∂energyMeasure μ H, ‖U p‖ ≤ R)
    {ι : Type*} [Countable ι] [DecidableEq ι] (P : FiniteScalarIto.Family F μ H ι)
    (e : HilbertBasis ι ℝ (Lp V 2 (haarAddCircle (T := 2 * Real.pi)))) (k : ℕ) :
    (∫⁻ ω, ENNReal.ofReal
      (‖(FiniteCylindricalIto.terminalIto P.toCoordinates e).integral
          (input F U hU hG hβ hβ1 μ H T hTH hT a hbound) ω -
        (FiniteCylindricalIto.terminalIto P.toCoordinates e).integral
          (input F U hU hG hβ hβ1 μ H T hTH hT b hbound) ω‖ ^ (2 * 2 ^ k)) ∂μ) ≤
      (NativeScalarBDG.constant k : ℝ≥0∞) * energyCap G C β R T a b ^ (2 ^ k) :=
  NativeScalarBDG.difference_moment_of_bracket_bound P e k _ _
    (input_bracket_bound F U hU hG hβ hβ1 μ H T hTH hT a b hbound)

end SHEStochastic.UnboundedHeatSpatialMoments
