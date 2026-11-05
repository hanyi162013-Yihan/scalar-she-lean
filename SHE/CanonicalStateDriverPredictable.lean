module
public import SHE.CanonicalStateDriverFiltration
public import SHE.ContinuousPredictable
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
namespace SHE.CanonicalStateDriverFiltration
open MeasureTheory Set PredictableL2
open scoped NNReal
variable{E ι:Type*}[Countable ι][DecidableEq ι]
variable[NormedAddCommGroup E][InnerProductSpace ℝ E][CompleteSpace E]
variable[MeasurableSpace E][BorelSpace E][SecondCountableTopology E]
variable(h:ℝ≥0)
local notation "R"=>CanonicalFutureStateDriver.Space (E:=E) (ι:=ι) h

/-- The actual canonical state, held at the end of its native horizon. -/
def state(t:ℝ≥0)(r:R):E:=r.1 (clock h t)

theorem state_adapted(t:ℝ≥0):
    Measurable[filtration (E:=E) (ι:=ι) h t] (state (E:=E) (ι:=ι) h t):=by
  have hm:Measurable (fun r:R=>r.1 (clock h t)):=
    (ContinuousMap.measurable_eval (clock h t)).comp measurable_fst
  have he:(fun r:R=>r.1 (clock h t)) ∘ history h t=state (E:=E) (ι:=ι) h t:=by
    funext r
    simp[state,history,CanonicalFutureStateDriver.past,CanonicalFutureStateDriver.stopTime]
  have hh:@Measurable R E (MeasurableSpace.comap (history h t) inferInstance) _
      ((fun r:R=>r.1 (clock h t))∘history h t):=
    hm.comp (Measurable.of_comap_le le_rfl)
  rwa[he] at hh

theorem state_continuous(r:R):Continuous (fun t=>state (E:=E) (ι:=ι) h t r):=
  r.1.continuous.comp ((continuous_subtype_val.min continuous_const).subtype_mk _)

theorem state_stronglyAdapted:
    StronglyAdapted (filtration (E:=E) (ι:=ι) h) (state (E:=E) (ι:=ι) h):=
  fun t=>(state_adapted (E:=E) (ι:=ι) h t).stronglyMeasurable

theorem coordinate_stronglyAdapted(i:ι):
    StronglyAdapted (filtration (E:=E) (ι:=ι) h) (coordinate (E:=E) h i):=
  fun t=>(coordinate_adapted (E:=E) h i t).stronglyMeasurable

/-- Genuine predictability follows from actual continuous adapted paths,
with respect to the full state-and-driver filtration. -/
theorem state_predictable:
    IsStronglyPredictable (filtration (E:=E) (ι:=ι) h) (state (E:=E) (ι:=ι) h):=
  ContinuousPredictable.isStronglyPredictable _ _ (state_stronglyAdapted h) (state_continuous h)

theorem coordinate_predictable(i:ι):
    IsStronglyPredictable (filtration (E:=E) (ι:=ι) h) (coordinate (E:=E) h i):=
  ContinuousPredictable.isStronglyPredictable _ _
    (coordinate_stronglyAdapted h i) (coordinate_continuous h i)

theorem state_joint_measurable:
    Measurable (Function.uncurry (state (E:=E) (ι:=ι) h)):=
  ((state_predictable (E:=E) (ι:=ι) h).mono (predictable_le_product _)).measurable

theorem coordinate_joint_measurable(i:ι):
    Measurable (Function.uncurry (coordinate (E:=E) h i)):=
  ((coordinate_predictable (E:=E) h i).mono (predictable_le_product _)).measurable

theorem state_eval(t:ℝ≥0)(ht:t≤h)(r:R):
    state (E:=E) (ι:=ι) h t r=r.1 ⟨t,t.2,by exact_mod_cast ht⟩:=by
  unfold state clock
  congr 1
  apply Subtype.ext
  exact min_eq_left (by exact_mod_cast ht)

theorem coordinate_eval(i:ι)(t:ℝ≥0)(ht:t≤h)(r:R):
    coordinate (E:=E) h i t r=r.2 i ⟨t,t.2,by exact_mod_cast ht⟩:=by
  unfold coordinate clock
  congr 1
  apply Subtype.ext
  exact min_eq_left (by exact_mod_cast ht)

section Actual
variable{Ω:Type*}[MeasurableSpace Ω]
variable(U:ℝ≥0→Ω→E)(hc:∀ω,Continuous (fun t=>U t ω))
variable(X:ι→ℝ≥0→Ω→ℝ)(hd:∀i ω,Continuous (fun t=>X i t ω))

theorem state_bundle(v t:ℝ≥0)(ht:t≤h)(ω:Ω):
    state (E:=E) (ι:=ι) h t (CanonicalFutureStateDriver.bundle U hc X hd v h ω)=U (v+t) ω:=by
  rw[state_eval h t ht]
  change U (v+(t:ℝ).toNNReal) ω=U (v+t) ω
  rw[Real.toNNReal_coe]

theorem coordinate_bundle(v t:ℝ≥0)(ht:t≤h)(i:ι)(ω:Ω):
    coordinate (E:=E) h i t (CanonicalFutureStateDriver.bundle U hc X hd v h ω)=
      X i (v+t) ω-X i v ω:=by
  rw[coordinate_eval h i t ht]
  change X i (v+(t:ℝ).toNNReal) ω-X i v ω=X i (v+t) ω-X i v ω
  rw[Real.toNNReal_coe]
end Actual
end SHE.CanonicalStateDriverFiltration
