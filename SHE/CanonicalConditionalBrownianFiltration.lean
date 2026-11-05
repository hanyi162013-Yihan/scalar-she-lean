module
public import SHE.ConditionalDriverClockClosure
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2200000
namespace SHE.CanonicalConditionalBrownianFiltration
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal ProbabilityTheory MeasureTheory
variable{Ω P E ι:Type*}[MeasurableSpace Ω][MeasurableSpace P][Countable ι][DecidableEq ι]
variable[NormedAddCommGroup E][InnerProductSpace ℝ E][CompleteSpace E]
variable[MeasurableSpace E][BorelSpace E][SecondCountableTopology E]
variable(𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ:Measure Ω)[IsProbabilityMeasure μ](H:ℝ≥0)
variable(U:ℝ≥0→Ω→E) (hc:∀ω,Continuous (fun t=>U t ω))
variable(X:ι→ℝ≥0→Ω→ℝ) (hd:∀i ω,Continuous (fun t=>X i t ω))
variable(hU:∀t,Measurable[𝓕 t] (U t)) (hX:∀i t,Measurable[𝓕 t] (X i t))
variable(hBrown:∀n (a:Fin n→ι),FiniteBrownianLawOn 𝓕 μ H (fun i=>X (a i))
  (fun i j=>if a i=a j then 1 else 0))

include hU hX hBrown in
/-- One actual conditional-prefix event supports Brownian increment
independence from the FULL canonical future STATE+DRIVER filtration at
EVERY real clock. Rational reduction and continuity are proved inside. -/
theorem all_clocks(v h:ℝ≥0) (hvh:v+h≤H) (Z:Ω→P) (hZ:Measurable[𝓕 v] Z):
    ∀ᵐp∂μ.map Z,∀n (a:Fin n→ι) (s t:Icc (0:ℝ) (h:ℝ)),s≤t→
      IndepFun (CanonicalFutureStateDriver.past (E:=E) (ι:=ι) s)
        (CanonicalFutureStateDriver.increment (E:=E) a s t)
        (condDistrib (CanonicalFutureStateDriver.bundle U hc X hd v h) Z μ p):=by
  filter_upwards[CanonicalConditionalRationalDriver.increments 𝓕 μ H U hc X hd
    hU hX hBrown v h hvh Z hZ] with p hp
  intro n a s t hst
  exact ConditionalDriverClockClosure.independent h _ hp a s t hst
end SHE.CanonicalConditionalBrownianFiltration
