module
public import SHE.IndependentNoiseCompletion
public import SHE.StandardTerminalIto
public import SHE.StandardTerminalPastLocality
public import SHE.OrthogonalItoChannels
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace SHE
open MeasureTheory PredictableL2 OrthogonalItoChannels
open scoped NNReal ENNReal
variable {Ω Ξ C:Type*}[MeasurableSpace Ω][MeasurableSpace Ξ]
variable [NormedAddCommGroup C][InnerProductSpace ℝ C]

/-- Exact generic first-coordinate naturality of ordinary product Ito. -/
def IndependentProductFirstCompatible
    (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(𝓖:Filtration ℝ≥0 ‹MeasurableSpace Ξ›)
    (μ:Measure Ω)(ν:Measure Ξ)[IsProbabilityMeasure μ][IsProbabilityMeasure ν](H:ℝ≥0)
    (J:StandardTerminalIto (C:=C) (E:=ℝ) 𝓕 μ H)
    (B:StandardTerminalIto (C:=Both C) (E:=ℝ)
      (IndependentNoiseCompletion.filtration μ ν 𝓕 𝓖) (IndependentNoiseCompletion.measure μ ν) H):Prop:=
  (∀(f:Process (E:=C) 𝓕 μ H)
      (g:Process (E:=Both C) (IndependentNoiseCompletion.filtration μ ν 𝓕 𝓖)
        (IndependentNoiseCompletion.measure μ ν) H),
      (g=ᵐ[energyMeasure (IndependentNoiseCompletion.measure μ ν) H]
        fun p=>WithLp.toLp 2 (f (p.1,p.2.1),0))→
      (B.integral g=ᵐ[IndependentNoiseCompletion.measure μ ν] fun z=>J.integral f z.1))

/-- Exact generic second-coordinate naturality of ordinary product Ito. -/
def IndependentProductSecondCompatible
    (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(𝓖:Filtration ℝ≥0 ‹MeasurableSpace Ξ›)
    (μ:Measure Ω)(ν:Measure Ξ)[IsProbabilityMeasure μ][IsProbabilityMeasure ν](H:ℝ≥0)
    (K:StandardTerminalIto (C:=C) (E:=ℝ) 𝓖 ν H)
    (B:StandardTerminalIto (C:=Both C) (E:=ℝ)
      (IndependentNoiseCompletion.filtration μ ν 𝓕 𝓖) (IndependentNoiseCompletion.measure μ ν) H):Prop:=
  (∀(f:Process (E:=C) 𝓖 ν H)
      (g:Process (E:=Both C) (IndependentNoiseCompletion.filtration μ ν 𝓕 𝓖)
        (IndependentNoiseCompletion.measure μ ν) H),
      (g=ᵐ[energyMeasure (IndependentNoiseCompletion.measure μ ν) H]
        fun p=>WithLp.toLp 2 (0,f (p.1,p.2.2)))→
      (B.integral g=ᵐ[IndependentNoiseCompletion.measure μ ν] fun z=>K.integral f z.2))

/-- Explicit ordinary PRODUCT-CONSTRUCTION component of accepted stochastic
package 1, assumed only at supplied genuine cylindrical Ito maps J,K.
The conclusion is an ordinary Ito map for the independent pair on the
internally defined completed product filtration. For every original
predictable L2 input, its enlarged first/second-coordinate integral is
exactly the pullback of its supplied original integral. This is an explicit
external standard-calculus property, NOT a theorem from terminal isometry.
There is no heat, coefficient, SPDE, solution law, approximation or restart
assertion here. All raw-equality applicability is proved by actual clients. -/
def StandardIndependentProductIto
    (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(𝓖:Filtration ℝ≥0 ‹MeasurableSpace Ξ›)
    (μ:Measure Ω)(ν:Measure Ξ)[IsProbabilityMeasure μ][IsProbabilityMeasure ν](H:ℝ≥0)
    (J:StandardTerminalIto (C:=C) (E:=ℝ) 𝓕 μ H)
    (K:StandardTerminalIto (C:=C) (E:=ℝ) 𝓖 ν H):Prop:=
  ∃B:StandardTerminalIto (C:=Both C) (E:=ℝ)
      (IndependentNoiseCompletion.filtration μ ν 𝓕 𝓖) (IndependentNoiseCompletion.measure μ ν) H,
    IndependentProductFirstCompatible 𝓕 𝓖 μ ν H J B ∧
    IndependentProductSecondCompatible 𝓕 𝓖 μ ν H K B ∧
    StandardTerminalPastLocality B
/-- A coherent witness of the ordinary constructor, used internally to
retain the exact chosen product integral throughout model transport. -/
structure IndependentProductItoData
    (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(𝓖:Filtration ℝ≥0 ‹MeasurableSpace Ξ›)
    (μ:Measure Ω)(ν:Measure Ξ)[IsProbabilityMeasure μ][IsProbabilityMeasure ν](H:ℝ≥0)
    (J:StandardTerminalIto (C:=C) (E:=ℝ) 𝓕 μ H)
    (K:StandardTerminalIto (C:=C) (E:=ℝ) 𝓖 ν H) where
  integral:StandardTerminalIto (C:=Both C) (E:=ℝ)
    (IndependentNoiseCompletion.filtration μ ν 𝓕 𝓖) (IndependentNoiseCompletion.measure μ ν) H
  first:IndependentProductFirstCompatible 𝓕 𝓖 μ ν H J integral
  second:IndependentProductSecondCompatible 𝓕 𝓖 μ ν H K integral
  locality:StandardTerminalPastLocality integral

theorem StandardIndependentProductIto.exists_data
    {𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›}{𝓖:Filtration ℝ≥0 ‹MeasurableSpace Ξ›}
    {μ:Measure Ω}{ν:Measure Ξ}[IsProbabilityMeasure μ][IsProbabilityMeasure ν]{H:ℝ≥0}
    {J:StandardTerminalIto (C:=C) (E:=ℝ) 𝓕 μ H}
    {K:StandardTerminalIto (C:=C) (E:=ℝ) 𝓖 ν H}
    (h:StandardIndependentProductIto 𝓕 𝓖 μ ν H J K):
    Nonempty (IndependentProductItoData 𝓕 𝓖 μ ν H J K):=by
  obtain ⟨B,h0,h1,hl⟩:=h
  exact ⟨⟨B,h0,h1,hl⟩⟩
end SHE
