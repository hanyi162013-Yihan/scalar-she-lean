module
public import SHE.CanonicalFutureStateDriver
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2200000
namespace SHE.CanonicalConditionalRationalDriver
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

abbrev Times(h:ℝ≥0):= {q:ℚ // 0≤q ∧ (q:ℝ)≤h}

def time{h:ℝ≥0}(q:Times h):Icc (0:ℝ) (h:ℝ):=
  ⟨q.val,by exact_mod_cast q.property.1,q.property.2⟩

include hU hX hBrown in
/-- ONE canonical prefix event supports every rational restart clock,
all finite coordinate families and their increments. This is an actual
conditional law consequence, not a countable collection assumed as
external Brownian data. -/
theorem increments(v h:ℝ≥0) (hvh:v+h≤H) (Z:Ω→P) (hZ:Measurable[𝓕 v] Z):
    ∀ᵐp∂μ.map Z,∀n (a:Fin n→ι) (s t:Times h),s≤t→
      IndepFun (CanonicalFutureStateDriver.past (E:=E) (ι:=ι) (time s))
        (CanonicalFutureStateDriver.increment (E:=E) a (time s) (time t))
        (condDistrib (CanonicalFutureStateDriver.bundle U hc X hd v h) Z μ p):=by
  apply ae_all_iff.mpr
  intro n
  apply ae_all_iff.mpr
  intro a
  apply ae_all_iff.mpr
  intro s
  apply ae_all_iff.mpr
  intro t
  by_cases hst:s≤t
  · filter_upwards[CanonicalFutureStateDriver.conditional_increment 𝓕 μ H U hc X hd
      hU hX hBrown v h hvh Z hZ a (time s) (time t)
      (show time s≤time t by
        change (s.val:ℝ)≤(t.val:ℝ)
        exact_mod_cast (show s.val≤t.val from hst))] with p hp
    exact fun _=>hp
  · exact ae_of_all _ (fun _ h=>False.elim (hst h))
end SHE.CanonicalConditionalRationalDriver
