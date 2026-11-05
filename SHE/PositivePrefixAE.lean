module
public import SHE.NativeObservationEndpoint
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace SHE.PositivePrefixAE
open Set Filter MeasureTheory
open scoped NNReal Topology

/-- A countable positive-prefix exhaustion removes the terminal-prefix
restriction on a genuine parameter/sample event. No uncountable
intersection or measurable-predicate assumption is used. -/
theorem exhaust {X P:Type*} [MeasurableSpace X] [MeasurableSpace P]
    (ν:Measure X) (μ:Measure P) (v b:ℝ≥0) (hb0:0<b) (t:P→ℝ≥0)
    {Q:X→P→Prop}
    (h:∀c:ℝ≥0,0<c→c<b→∀ᵐx∂ν,∀ᵐp∂μ,v<t p→t p<c→Q x p):
    ∀ᵐx∂ν,∀ᵐp∂μ,v<t p→t p<b→Q x p:=by
  let c:ℕ→ℝ≥0:=fun n=>(NativeObservationEndpoint.approach b n).toNNReal
  have hcb(n:ℕ):c n<b:=by
    by_cases hn:0≤NativeObservationEndpoint.approach b n
    · exact (Real.toNNReal_lt_iff_lt_coe hn).2 (NativeObservationEndpoint.approach_lt b n)
    · have he:c n=0:=Real.toNNReal_eq_zero.mpr (le_of_not_ge hn)
      simpa only [he] using hb0
  have ha(n:ℕ):∀ᵐx∂ν,∀ᵐp∂μ,v<t p→t p<c n→Q x p:=by
    by_cases hc0:0<c n
    · exact h (c n) hc0 (hcb n)
    · have he:c n=0:=le_antisymm (le_of_not_gt hc0) bot_le
      exact ae_of_all _ (fun _=>ae_of_all _ (fun p _ hp=>
        (not_lt_of_ge (show (0:ℝ≥0)≤t p from bot_le) (by simpa only [he] using hp)).elim))
  filter_upwards [ae_all_iff.mpr ha] with x hx
  filter_upwards [ae_all_iff.mpr hx] with p hp hvp hpb
  have he:∀ᶠn:ℕ in atTop,(t p:ℝ)<NativeObservationEndpoint.approach b n:=
    (NativeObservationEndpoint.approach_tendsto b).eventually
      (lt_mem_nhds (show (t p:ℝ)<(b:ℝ) by exact_mod_cast hpb))
  obtain ⟨n,hn⟩:=he.exists
  have ht:t p<c n:=by
    change (t p:ℝ)<(c n:ℝ)
    rw [show (c n:ℝ)=NativeObservationEndpoint.approach b n from
      Real.coe_toNNReal _ ((t p).coe_nonneg.trans hn.le)]
    exact hn
  exact hp n hvp ht

end SHE.PositivePrefixAE
