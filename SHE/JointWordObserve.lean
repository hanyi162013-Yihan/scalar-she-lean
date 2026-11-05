module

public import SHE.JointPhysicalInsertion
public import SHE.VariableObservations

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section

namespace SHE.JointWordObserve
open MeasureTheory Set StoppedFourier WordRecursion VariableObservations
abbrev State (n : ℕ) := WordRecursion.State n
local instance jointWordObserve_periodPositive : Fact (0<2*Real.pi) := ⟨by positivity⟩

/-- Joint coordinates evaluated from their actual two physical states.
Their original stop controls the exponential and their original target
controls the heat age. The actual point fields supply zero-age leaves. -/
def evaluate {n : ℕ} (Λ : ℝ) (U V : ℝ→CircleL2) (XU XV : ℝ×HeatCircle→ℝ)
    (Z : Fin n→Observation) (t : ℝ) : State n := WithLp.toLp 2 (fun i =>
  observe U XU Z t i+Real.exp (-Λ*((Z i).stop-t))*(observe V XV Z t i-observe U XU Z t i))

theorem append_zero {n : ℕ} (Λ : ℝ) (U V : ℝ→CircleL2) (XU XV : ℝ×HeatCircle→ℝ)
    (Z : Fin n→Observation) (t : ℝ) (x : HeatCircle) :
    evaluate Λ U V XU XV (appendObservation Z t x) t 0=XV (t,x) := by
  simp only [evaluate,WithLp.ofLp_toLp,observe_append_zero,appendObservation,Fin.cases_zero,
    sub_self,mul_zero,Real.exp_zero,one_mul]
  ring

theorem append_succ {n : ℕ} (Λ : ℝ) (U V : ℝ→CircleL2) (XU XV : ℝ×HeatCircle→ℝ)
    (Z : Fin n→Observation) (t : ℝ) (x : HeatCircle) (i : Fin n) :
    evaluate Λ U V XU XV (appendObservation Z t x) t i.succ=evaluate Λ U V XU XV Z t i := by
  simp only [evaluate,WithLp.ofLp_toLp,observe_append_succ,appendObservation,Fin.cases_succ]

/-- Every local insertion appends the actual V point and preserves the
entire old joint state, exactly as required by the recursive words. -/
theorem evaluate_append {n : ℕ} (Λ : ℝ) (U V : ℝ→CircleL2) (XU XV : ℝ×HeatCircle→ℝ)
    (Z : Fin n→Observation) (t : ℝ) (x : HeatCircle) :
    evaluate Λ U V XU XV (appendObservation Z t x) t=
      JointPhysicalInsertion.appendState (XV (t,x)) (evaluate Λ U V XU XV Z t) := by
  apply PiLp.ext
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact append_zero Λ U V XU XV Z t x
  · exact append_succ Λ U V XU XV Z t x j

theorem evaluate_measurable {P : Type*} [MeasurableSpace P]
    [MeasurableSpace CircleL2] [BorelSpace CircleL2] {n : ℕ} (Z : Family P n) (Λ : ℝ)
    {U V : P×ℝ→CircleL2} (hU : Measurable U) (hV : Measurable V)
    {XU XV : P×(ℝ×HeatCircle)→ℝ} (hXU : Measurable XU) (hXV : Measurable XV) :
    Measurable (fun p : P×ℝ => evaluate Λ (fun t => U (p.1,t)) (fun t => V (p.1,t))
      (fun q => XU (p.1,q)) (fun q => XV (p.1,q)) (Z.observations p.1) p.2) := by
  have hu := Z.observe_measurable hU hXU
  have hv := Z.observe_measurable hV hXV
  apply (WithLp.measurable_toLp 2 (Fin n→ℝ)).comp
  apply Measurable.of_eval
  intro i
  have he := ((((Z.stop_measurable i).comp measurable_fst).sub measurable_snd).const_mul (-Λ)).exp
  have hui := (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => ℝ) i).continuous.measurable.comp hu
  have hvi := (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => ℝ) i).continuous.measurable.comp hv
  exact hui.add (he.mul (hvi.sub hui))

end SHE.JointWordObserve
