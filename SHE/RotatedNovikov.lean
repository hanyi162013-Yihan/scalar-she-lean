module
public import SHE.StandardTerminalNovikov
public import SHE.PredictableItoRotation
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
namespace SHE.PredictableItoRotation
open MeasureTheory PredictableL2 StochasticExponential
open scoped NNReal ENNReal
variable {Ω A C : Type*} [MeasurableSpace Ω]
variable [NormedAddCommGroup A] [InnerProductSpace ℝ A] [MeasurableSpace A] [BorelSpace A]
variable [NormedAddCommGroup C] [InnerProductSpace ℝ C] [MeasurableSpace C] [BorelSpace C]
variable [SecondCountableTopology C]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [SFinite μ] (H : ℝ≥0)
variable (Φ : (ℝ≥0 × Ω) → A →ₗᵢ[ℝ] C)
variable (hΦ : @Measurable ((ℝ≥0 × Ω) × A) C
  (𝓕.predictable.prod ‹MeasurableSpace A›) ‹MeasurableSpace C› (fun p => Φ p.1 p.2))

theorem real_bracket_ae (u : Process (E:=A) 𝓕 μ H) :
    StochasticExponential.bracket 𝓕 μ H (processIsometry 𝓕 μ H Φ hΦ u) =ᵐ[μ]
      StochasticExponential.bracket 𝓕 μ H u := by
  have hh := (Measure.measurePreserving_swap (μ:=μ) (ν:=timeMeasure H)).quasiMeasurePreserving.ae
    (processIsometry_ae 𝓕 μ H Φ hΦ u)
  filter_upwards [Measure.ae_ae_of_ae_prod hh] with ω hω
  apply integral_congr_ae
  filter_upwards [hω] with s hs
  dsimp only [Prod.swap] at hs
  rw [hs,(Φ (s,ω)).norm_map]

/-- The ordinary Novikov input is inherited by the actual predictable
noise rotation. Its density and bracket are the SAME original ones. -/
theorem novikov (B : StandardTerminalIto (C:=C) (E:=ℝ) 𝓕 μ H)
    (hB : StandardTerminalNovikov B) :
    StandardTerminalNovikov (integral 𝓕 μ H Φ hΦ B) := by
  intro u hExp
  have hbr := real_bracket_ae 𝓕 μ H Φ hΦ u
  have he : (fun ω => Real.exp (StochasticExponential.bracket 𝓕 μ H
      (processIsometry 𝓕 μ H Φ hΦ u) ω/2)) =ᵐ[μ]
      (fun ω => Real.exp (StochasticExponential.bracket 𝓕 μ H u ω/2)) := by
    filter_upwards [hbr] with ω hω
    rw [hω]
  obtain ⟨hi,hm⟩ := hB (processIsometry 𝓕 μ H Φ hΦ u) (hExp.congr he.symm)
  have hd : StochasticExponential.density 𝓕 μ H (integral 𝓕 μ H Φ hΦ B) u =ᵐ[μ]
      StochasticExponential.density 𝓕 μ H B (processIsometry 𝓕 μ H Φ hΦ u) := by
    filter_upwards [hbr] with ω hω
    change Real.exp (-B.integral (processIsometry 𝓕 μ H Φ hΦ u) ω-bracket 𝓕 μ H u ω/2) =
      Real.exp (-B.integral (processIsometry 𝓕 μ H Φ hΦ u) ω-
        bracket 𝓕 μ H (processIsometry 𝓕 μ H Φ hΦ u) ω/2)
    rw [hω]
  exact ⟨hi.congr hd.symm,(integral_congr_ae hd).trans hm⟩
end SHE.PredictableItoRotation
