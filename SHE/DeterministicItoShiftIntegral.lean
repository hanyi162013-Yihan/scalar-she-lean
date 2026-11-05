module
public import SHE.DeterministicItoShiftIsometry
public import SHE.StandardTerminalIto
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace SHE.DeterministicItoShift
open MeasureTheory Set PredictableL2
open scoped NNReal ENNReal
variable{Ω C E:Type*}[MeasurableSpace Ω]
variable[NormedAddCommGroup C][InnerProductSpace ℝ C]
variable[MeasurableSpace C][BorelSpace C][SecondCountableTopology C]
variable[NormedAddCommGroup E][InnerProductSpace ℝ E]
variable(𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(μ:Measure Ω)[SFinite μ]
variable(H v h:ℝ≥0)(hvh:v+h≤H)
include hvh

/-- Deterministic local stopping is the SAME original stopping time
v+l after zero extension, including l beyond the local horizon. -/
theorem input_supported(l:ℝ≥0)(f:Process (E:=C) (filtration 𝓕 v) μ h)
    (hf:∀ᵐp∂energyMeasure μ h,l<p.1→f p=0):
    ∀ᵐp∂energyMeasure μ H,v+l<p.1→input 𝓕 μ H v h hvh f p=0:=by
  classical
  let g:ℝ≥0×Ω→C:=((after (Ω:=Ω) l)ᶜ).indicator f
  have hg:@Measurable _ _ (filtration 𝓕 v).predictable _ g:=
    (Lp.stronglyMeasurable f).measurable.indicator (after_measurable (filtration 𝓕 v) l).compl
  have hfg:f=ᵐ[energyMeasure μ h] g:=by
    filter_upwards [hf] with p hp
    by_cases hl:l<p.1
    · have hn:p∉(after (Ω:=Ω) l)ᶜ:=by simp only [mem_compl_iff,after,mem_prod,mem_Ioi,mem_univ,and_true,not_not];exact hl
      rw [show g p=0 from Set.indicator_of_notMem hn f]
      exact hp hl
    · have hn:p∈(after (Ω:=Ω) l)ᶜ:=by simp only [mem_compl_iff,after,mem_prod,mem_Ioi,mem_univ,and_true];exact hl
      exact (Set.indicator_of_mem hn f).symm
  have he:=extend_ae 𝓕 μ H v h hvh (Lp.stronglyMeasurable f).measurable hg hfg
  filter_upwards [input_ae 𝓕 μ H v h hvh f,he] with p hp he hl
  rw [hp,he]
  by_cases hv:v<p.1
  · by_cases hu:p.1≤v+h
    · have hs:l<(relative v p).1:=(relative_order v l p.1 hv).mpr hl
      have hn:relative v p∉(after (Ω:=Ω) l)ᶜ:=by
        simp only [mem_compl_iff,after,mem_prod,mem_Ioi,mem_univ,and_true,not_not]
        exact hs
      simp only [extend,ite_eq_left hv,ite_eq_left hu,g,Set.indicator_of_notMem hn]
    · simp only [extend,ite_eq_left hv,ite_eq_right hu]
  · simp only [extend,ite_eq_right hv]

/-- The deterministic shifted integral is the original J applied to
its literal window extension. Isometry, centering and adaptedness are
inherited from that SAME original integral; nothing is conditioned. -/
def integral(J:StandardTerminalIto (C:=C) (E:=E) 𝓕 μ H):
    StandardTerminalIto (C:=C) (E:=E) (filtration 𝓕 v) μ h where
  integral:=J.integral.comp (inputIsometry 𝓕 μ H v h hvh)
  adapted l f hf:=J.adapted (v+l) _ (input_supported 𝓕 μ H v h hvh l f hf)
  centered f:=J.centered _

theorem integral_eq(J:StandardTerminalIto (C:=C) (E:=E) 𝓕 μ H)
    (f:Process (E:=C) (filtration 𝓕 v) μ h):
    (integral 𝓕 μ H v h hvh J).integral f=J.integral (input 𝓕 μ H v h hvh f):=rfl

end SHE.DeterministicItoShift
