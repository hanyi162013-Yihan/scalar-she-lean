module
public import SHE.BrownianConditionalHistory
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2200000
namespace SHE.CanonicalFutureStateDriver
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

abbrev Space(h:ℝ≥0):=CanonicalContinuousStateDriver.Space (E:=E) (ι:=ι) h

def bundle(v h:ℝ≥0) (ω:Ω):Space (E:=E) (ι:=ι) h:=
  (⟨fun t=>U (v+t.val.toNNReal) ω,
    (hc ω).comp (continuous_const.add (continuous_real_toNNReal.comp continuous_subtype_val))⟩,
   BrownianFuturePath.value X hd v h ω)

include hU hX in
theorem measurable_bundle(v h:ℝ≥0):Measurable (bundle U hc X hd v h):=by
  apply Measurable.prodMk
  · apply ContinuousMap.measurable_iff_eval.mpr
    intro t
    exact (hU _).mono (𝓕.le _) le_rfl
  · exact BrownianFuturePath.measurable 𝓕 X hd hX v h

def stopTime{h:ℝ≥0}(u:Icc (0:ℝ) (h:ℝ)) (t:Icc (0:ℝ) (h:ℝ)):
    Icc (0:ℝ) (h:ℝ):=
  ⟨min t.val u.val,le_min t.property.1 u.property.1,(min_le_left _ _).trans t.property.2⟩

def past{h:ℝ≥0}(u:Icc (0:ℝ) (h:ℝ)) (r:Space (E:=E) (ι:=ι) h):Space (E:=E) (ι:=ι) h:=
  (⟨fun t=>r.1 (stopTime u t),r.1.continuous.comp
    ((continuous_subtype_val.min continuous_const).subtype_mk _)⟩,
   fun i=>⟨fun t=>r.2 i (stopTime u t),(r.2 i).continuous.comp
    ((continuous_subtype_val.min continuous_const).subtype_mk _)⟩)

theorem measurable_past{h:ℝ≥0}(u:Icc (0:ℝ) (h:ℝ)):
    Measurable (past (E:=E) (ι:=ι) u):=by
  apply Measurable.prodMk
  · apply ContinuousMap.measurable_iff_eval.mpr
    intro t
    exact (ContinuousMap.measurable_eval (stopTime u t)).comp
      (show Measurable (fun r:Space (E:=E) (ι:=ι) h=>r.1) from measurable_fst)
  · apply measurable_pi_iff.mpr
    intro i
    apply ContinuousMap.measurable_iff_eval.mpr
    intro t
    exact (ContinuousMap.measurable_eval (stopTime u t)).comp
      ((measurable_pi_apply i).comp
        (show Measurable (fun r:Space (E:=E) (ι:=ι) h=>r.2) from measurable_snd))

include hU hX in
/-- The retained canonical future STATE and DRIVER history is measurable
in the actual original filtration at the later deterministic time. -/
theorem adapted_past(v h:ℝ≥0) (u:Icc (0:ℝ) (h:ℝ)):
    Measurable[𝓕 (v+u.val.toNNReal)]
      (past (E:=E) (ι:=ι) u ∘ bundle U hc X hd v h):=by
  have ht(t:Icc (0:ℝ) (h:ℝ)):v+(stopTime u t).val.toNNReal≤v+u.val.toNNReal:=by
    apply add_le_add_right
    exact Real.toNNReal_le_toNNReal (min_le_right _ _)
  have hv:v≤v+u.val.toNNReal:=le_add_of_nonneg_right (by positivity)
  letI:MeasurableSpace Ω:=𝓕 (v+u.val.toNNReal)
  apply Measurable.prodMk
  · apply ContinuousMap.measurable_iff_eval.mpr
    intro t
    exact (hU _).mono (𝓕.mono (ht t)) le_rfl
  · apply measurable_pi_iff.mpr
    intro i
    apply ContinuousMap.measurable_iff_eval.mpr
    intro t
    exact ((hX i _).mono (𝓕.mono (ht t)) le_rfl).sub
      ((hX i v).mono (𝓕.mono hv) le_rfl)

def increment{h:ℝ≥0}{n:ℕ}(a:Fin n→ι) (s t:Icc (0:ℝ) (h:ℝ))
    (r:Space (E:=E) (ι:=ι) h):WordRecursion.State n:=
  WithLp.toLp 2 (fun i=>r.2 (a i) t-r.2 (a i) s)

theorem measurable_increment{h:ℝ≥0}{n:ℕ}(a:Fin n→ι) (s t:Icc (0:ℝ) (h:ℝ)):
    Measurable (increment (E:=E) a s t):=by
  apply (WithLp.measurable_toLp 2 (Fin n→ℝ)).comp
  apply measurable_pi_iff.mpr
  intro i
  exact ((ContinuousMap.measurable_eval t).comp ((measurable_pi_apply (a i)).comp measurable_snd)).sub
    ((ContinuousMap.measurable_eval s).comp ((measurable_pi_apply (a i)).comp measurable_snd))

include hU hX hBrown in
/-- Conditional future increments are independent of the actual retained
STATE+DRIVER future history. This follows from original full-filtration
Brownian independence, then genuine canonical disintegration. -/
theorem conditional_increment(v h:ℝ≥0) (hvh:v+h≤H)
    (Z:Ω→P) (hZ:Measurable[𝓕 v] Z){n:ℕ}(a:Fin n→ι)
    (s t:Icc (0:ℝ) (h:ℝ)) (hst:s≤t):
    ∀ᵐp∂μ.map Z,IndepFun (past (E:=E) (ι:=ι) s)
      (increment (E:=E) a s t) (condDistrib (bundle U hc X hd v h) Z μ p):=by
  apply BrownianConditionalHistory.increment 𝓕 μ H (fun i=>X (a i)) _ (hBrown n a)
    v (v+s.val.toNNReal) (v+t.val.toNNReal)
    (le_add_of_nonneg_right (by positivity))
    (add_le_add_right (Real.toNNReal_le_toNNReal hst) v)
    ((add_le_add_right (show t.val.toNNReal≤h by
      simpa only[Real.toNNReal_coe] using Real.toNNReal_le_toNNReal t.property.2) v).trans hvh)
    Z (bundle U hc X hd v h) (past s) (increment a s t) hZ
    (measurable_bundle 𝓕 U hc X hd hU hX v h) (measurable_past s)
    (measurable_increment a s t) (adapted_past 𝓕 U hc X hd hU hX v h s)
  intro ω
  apply PiLp.ext
  intro i
  change (X (a i) (v+t.val.toNNReal) ω-X (a i) v ω)-
    (X (a i) (v+s.val.toNNReal) ω-X (a i) v ω)=_
  abel
end SHE.CanonicalFutureStateDriver
