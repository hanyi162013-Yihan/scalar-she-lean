module
public import SHE.DyadicStoppingLocality
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace SHE.DyadicStoppingPrefix
open Set MeasureTheory PredictableL2
open scoped NNReal ENNReal
variable {Ω C E:Type*}[MeasurableSpace Ω]
variable[NormedAddCommGroup C][InnerProductSpace ℝ C][NormedAddCommGroup E][InnerProductSpace ℝ E]
variable(𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)[IsProbabilityMeasure μ](H:ℝ≥0)
/-- Random locality at an arbitrary deterministic prefix, while retaining
the SAME full-horizon integral. -/
theorem vanish
    (J:StandardTerminalIto (C:=C) (E:=E) 𝓕 μ H)(hlocal:StandardTerminalPastLocality J)
    (A:ℝ≥0→Ω→ℝ)(ha:StronglyAdapted 𝓕 A)(hc:∀ω,Continuous (fun s=>A s ω))
    (hm:∀ω,Monotone (fun s=>A s ω))(r:ℝ)(hH:0<H)
    (q:ℝ≥0)(hq:q≤H)(f:Process (E:=C) 𝓕 μ H)
    (hf:∀ᵐp∂energyMeasure μ H,(q<p.1 ∨ A p.1 p.2≤r)→f p=0):
    ∀ᵐω∂μ,A q ω≤r→J.integral f ω=0:=by
  let B:ℝ≥0→Ω→ℝ:=fun s ω=>A (min s q) ω
  have hb:StronglyAdapted 𝓕 B:=fun s=>(ha _).mono (𝓕.mono (min_le_left _ _))
  have hbc:∀ω,Continuous (fun s=>B s ω):=fun ω=>(hc ω).comp (continuous_id.min continuous_const)
  have hbm:∀ω,Monotone (fun s=>B s ω):=fun ω s t hst=>hm ω (min_le_min_right q hst)
  have hzero:∀ᵐp∂energyMeasure μ H,B p.1 p.2≤r→f p=0:=by
    filter_upwards [hf] with p hp hB
    by_cases hs:p.1≤q
    · exact hp (Or.inr (by simpa only [B,min_eq_left hs] using hB))
    · exact hp (Or.inl (lt_of_not_ge hs))
  have he:=DyadicStoppingLocality.vanish 𝓕 μ H J hlocal B hb hbc hbm r hH f hzero
  simpa only [B,min_eq_right hq] using he
end SHE.DyadicStoppingPrefix
