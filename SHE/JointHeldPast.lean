module
public import SHE.ContinuousPredictable
public import SHE.PredictablePastParameter
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace SHE.JointHeldPast
open MeasureTheory Set Filter ContinuousPredictable ApproximationCells
open scoped NNReal Topology
variable {Ω E:Type*}[MeasurableSpace Ω][NormedAddCommGroup E]
  [MeasurableSpace E][BorelSpace E][SecondCountableTopology E]
variable (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(u:ℝ≥0→Ω→E)(e:E)

theorem leftPoint_le (n:ℕ)(v:ℝ≥0):ContinuousPredictable.leftPoint n v≤v:=by
  by_cases hv:v=0
  · subst v
    rw [ContinuousPredictable.leftPoint_zero]
  · have hp:0<v:=lt_of_le_of_ne zero_le (Ne.symm hv)
    have hh:= (ApproximationClock.left_bounds n (show (0:ℝ)<v by exact_mod_cast hp)).2.1.le
    rw [ApproximationCells.left_eq_point n hp] at hh
    exact_mod_cast hh

def approximation (n:ℕ)(z:ℝ≥0×(ℝ≥0×Ω)):E:=
  if z.1<z.2.1 then
    PredictablePastParameter.held (ContinuousPredictable.leftPoint n z.1)
      (u (ContinuousPredictable.leftPoint n z.1)) e z.2
  else e

theorem approximation_measurable (ha:StronglyAdapted 𝓕 u)(n:ℕ):
    @Measurable (ℝ≥0×(ℝ≥0×Ω)) E ((inferInstance:MeasurableSpace ℝ≥0).prod 𝓕.predictable) _
      (approximation u e n):=by
  letI:MeasurableSpace (ℝ≥0×Ω):=𝓕.predictable
  have hi:Measurable (fun v:ℝ≥0=>ApproximationCells.index n v-1):=by
    unfold ApproximationCells.index
    fun_prop
  have hh:Measurable (fun z:ℕ×(ℝ≥0×Ω)=>
      PredictablePastParameter.held (ApproximationCells.point n z.1)
        (u (ApproximationCells.point n z.1)) e z.2):=
    measurable_from_prod_countable_right (fun k=>
      PredictablePastParameter.held_measurable 𝓕 (ApproximationCells.point n k)
        (u (ApproximationCells.point n k)) (ha _).measurable e)
  have hs:Measurable (fun z:ℝ≥0×(ℝ≥0×Ω)=>
      PredictablePastParameter.held (ContinuousPredictable.leftPoint n z.1)
        (u (ContinuousPredictable.leftPoint n z.1)) e z.2):=
    hh.comp ((hi.comp measurable_fst).prodMk measurable_snd)
  exact hs.ite (measurableSet_lt measurable_fst
    ((PredictableClock.time_measurable 𝓕).comp measurable_snd)) measurable_const

/-- A continuous adapted process evaluated at a MOVING old time v is
jointly predictable in (v;(q,omega)) strictly after that old time.
The proof is an explicit countable left-known approximation; ambient
joint Borel measurability is never substituted for predictability. -/
theorem stronglyMeasurable (ha:StronglyAdapted 𝓕 u)
    (hc:∀ω,Continuous (fun t=>u t ω)):
    StronglyMeasurable[((inferInstance:MeasurableSpace ℝ≥0).prod 𝓕.predictable)]
      (fun z=>PredictablePastParameter.held z.1 (u z.1) e z.2):=by
  apply stronglyMeasurable_of_tendsto atTop
    (fun n=>(approximation_measurable 𝓕 u e ha n).stronglyMeasurable)
  apply tendsto_pi_nhds.mpr
  intro z
  by_cases hz:z.1<z.2.1
  · have he:∀n,approximation u e n z=u (ContinuousPredictable.leftPoint n z.1) z.2.2:=by
      intro n
      rw [approximation,if_pos hz,PredictablePastParameter.held_eq _ _
        ((leftPoint_le n z.1).trans_lt hz)]
    simp only [he,PredictablePastParameter.held,if_pos hz]
    exact (hc z.2.2).continuousAt.tendsto.comp (ContinuousPredictable.leftPoint_tendsto z.1)
  · simp only [approximation,PredictablePastParameter.held,if_neg hz]
    exact tendsto_const_nhds
end SHE.JointHeldPast
