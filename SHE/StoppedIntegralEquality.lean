module
public import SHE.DyadicStoppingStrict
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace SHE.StoppedIntegralEquality
open Set MeasureTheory PredictableL2
open scoped NNReal ENNReal
variable {Ω C E:Type*}[MeasurableSpace Ω]
variable[NormedAddCommGroup C][InnerProductSpace ℝ C][NormedAddCommGroup E][InnerProductSpace ℝ E]
variable(𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)[IsProbabilityMeasure μ](H:ℝ≥0)
/-- Input replacement before an adapted continuous increasing clock
exits its threshold is proved for the SAME original Hilbert integral. -/
theorem equal
    (J:StandardTerminalIto (C:=C) (E:=E) 𝓕 μ H)(hlocal:StandardTerminalPastLocality J)
    (A:ℝ≥0→Ω→ℝ)(ha:StronglyAdapted 𝓕 A)(hc:∀ω,Continuous (fun s=>A s ω))
    (hm:∀ω,Monotone (fun s=>A s ω))(r:ℝ)(hH:0<H)
    (q:ℝ≥0)(hq:q≤H)(f g:Process (E:=C) 𝓕 μ H)
    (hfg:∀ᵐp∂energyMeasure μ H,(q<p.1 ∨ A p.1 p.2<r)→f p=g p):
    ∀ᵐω∂μ,A q ω<r→J.integral f ω=J.integral g ω:=by
  have hd:∀ᵐp∂energyMeasure μ H,(q<p.1 ∨ A p.1 p.2<r)→(f-g) p=0:=by
    filter_upwards [hfg,ae_eq_of_ae_eq_trim (Lp.coeFn_sub f g)] with p hp hd h
    rw [hd]
    change f p-g p=0
    exact sub_eq_zero.mpr (hp h)
  have hz:=DyadicStoppingStrict.vanish 𝓕 μ H J hlocal A ha hc hm r hH q hq (f-g) hd
  have he:=Lp.coeFn_sub (J.integral f) (J.integral g)
  rw [map_sub] at hz
  filter_upwards [hz,he] with ω hω he hA
  have hz':J.integral f ω-J.integral g ω=0:=he.symm.trans (hω hA)
  exact sub_eq_zero.mp hz' 
end SHE.StoppedIntegralEquality
