module
public import SHE.AllHorizonOriginalConditionalBrownian
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1800000
namespace SHE.AllHorizonStatePrefixBrownian
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal ProbabilityTheory MeasureTheory
variable{Ω E ι C:Type*}[MeasurableSpace Ω][Countable ι][DecidableEq ι]
variable[NormedAddCommGroup E][InnerProductSpace ℝ E][CompleteSpace E]
variable[MeasurableSpace E][BorelSpace E][SecondCountableTopology E]
variable[NormedAddCommGroup C][InnerProductSpace ℝ C]
variable[MeasurableSpace C][BorelSpace C][SecondCountableTopology C]
variable(𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ:Measure Ω)[IsProbabilityMeasure μ](H:ℝ≥0)
variable(U:ℝ≥0→Ω→E) (hc:∀ω,Continuous (fun t=>U t ω))
variable(hU:∀t,Measurable[𝓕 t] (U t))
variable(e:ι→C) (he:Orthonormal ℝ e) (J:StandardTerminalIto (C:=C) (E:=ℝ) 𝓕 μ H)
variable(B:ℝ≥0) (hBDG:StandardTerminalBDG16 J B) (hpos:0<H)
variable(hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ) (hLevy:StandardTerminalLevy J)

include hU in
theorem adapted(v:ℝ≥0):Measurable[𝓕 v] (NativeContinuousPath.path v U hc):=by
  letI:MeasurableSpace Ω:=𝓕 v
  apply ContinuousMap.measurable_iff_eval.mpr
  intro t
  have ht:t.val.toNNReal≤v:=by
    simpa only[Real.toNNReal_coe] using Real.toNNReal_le_toNNReal t.property.2
  exact (hU _).mono (𝓕.mono ht) le_rfl

include hU he hBDG hpos hnull hLevy in
/-- Final continuation conditions on STATE PREFIX ONLY. The conditional
future Brownian filtration still retains both future state and driver. -/
theorem law(v h:ℝ≥0) (hvh:v+h≤H):
    ∀ᵐp∂μ.map (NativeContinuousPath.path v U hc),∀n (a:Fin n→ι),
      FiniteBrownianLawOn (CanonicalStateDriverFiltration.filtration (E:=E) (ι:=ι) h)
        (condDistrib (AllHorizonOriginalConditionalBrownian.bundle 𝓕 μ H U hc e J hpos v h)
          (NativeContinuousPath.path v U hc) μ p) h
        (fun i=>CanonicalStateDriverFiltration.coordinate h (a i))
        (fun i j=>if a i=a j then 1 else 0):=by
  exact AllHorizonOriginalConditionalBrownian.law 𝓕 μ H U hc hU e he J B hBDG hpos
    hnull hLevy v h hvh _ (adapted 𝓕 U hc hU v)
end SHE.AllHorizonStatePrefixBrownian
