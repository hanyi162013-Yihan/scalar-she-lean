module
public import SHE.DyadicStoppingPrefix
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace SHE.DyadicStoppingStrict
open Set MeasureTheory PredictableL2
open scoped NNReal ENNReal
variable {Ω C E:Type*}[MeasurableSpace Ω]
variable[NormedAddCommGroup C][InnerProductSpace ℝ C][NormedAddCommGroup E][InnerProductSpace ℝ E]
variable(𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)[IsProbabilityMeasure μ](H:ℝ≥0)
/-- The genuine strict no-exit event is covered by countably many
strictly smaller thresholds; no boundary convention is assumed. -/
theorem vanish
    (J:StandardTerminalIto (C:=C) (E:=E) 𝓕 μ H)(hlocal:StandardTerminalPastLocality J)
    (A:ℝ≥0→Ω→ℝ)(ha:StronglyAdapted 𝓕 A)(hc:∀ω,Continuous (fun s=>A s ω))
    (hm:∀ω,Monotone (fun s=>A s ω))(r:ℝ)(hH:0<H)
    (q:ℝ≥0)(hq:q≤H)(f:Process (E:=C) 𝓕 μ H)
    (hf:∀ᵐp∂energyMeasure μ H,(q<p.1 ∨ A p.1 p.2<r)→f p=0):
    ∀ᵐω∂μ,A q ω<r→J.integral f ω=0:=by
  have he(l:ℚ):∀ᵐω∂μ,(l:ℝ)<r→A q ω≤l→J.integral f ω=0:=by
    by_cases hl:(l:ℝ)<r
    · have hz:∀ᵐp∂energyMeasure μ H,(q<p.1 ∨ A p.1 p.2≤l)→f p=0:=by
        filter_upwards [hf] with p hp h
        apply hp
        exact h.imp id (fun ha=>(ha.trans_lt hl))
      exact (DyadicStoppingPrefix.vanish 𝓕 μ H J hlocal A ha hc hm l hH q hq f hz).mono
        (fun _ h _=>h)
    · exact ae_of_all _ (fun _ h=>False.elim (hl h))
  filter_upwards [ae_all_iff.mpr he] with ω hω hA
  obtain ⟨l,hAl,hlr⟩:=exists_rat_btwn hA
  exact hω l hlr hAl.le
end SHE.DyadicStoppingStrict
