module
public import SHE.CanonicalFutureStateDriver
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1800000
namespace SHE.CanonicalStateDriverFiltration
open MeasureTheory ProbabilityTheory Set
open scoped NNReal
variable{E ι:Type*}[Countable ι][DecidableEq ι]
variable[NormedAddCommGroup E][InnerProductSpace ℝ E][CompleteSpace E]
variable[MeasurableSpace E][BorelSpace E][SecondCountableTopology E]
variable(h:ℝ≥0)
local notation "R"=>CanonicalFutureStateDriver.Space (E:=E) (ι:=ι) h

def clock(t:ℝ≥0):Icc (0:ℝ) (h:ℝ):=
  ⟨min (t:ℝ) (h:ℝ),le_min t.property h.property,min_le_right _ _⟩

def history(t:ℝ≥0):R→R:=CanonicalFutureStateDriver.past (clock h t)

theorem history_measurable(t:ℝ≥0):Measurable (history (E:=E) (ι:=ι) h t):=
  CanonicalFutureStateDriver.measurable_past (clock h t)

theorem history_comp(s t:ℝ≥0) (hst:s≤t):
    history (E:=E) (ι:=ι) h s ∘ history h t=history h s:=by
  have hc:(clock h s).val≤(clock h t).val:=min_le_min_right _ (by exact_mod_cast hst)
  funext r
  apply Prod.ext
  · apply ContinuousMap.ext
    intro u
    change r.1 ⟨min (min u.val (clock h s).val) (clock h t).val,_⟩=
      r.1 ⟨min u.val (clock h s).val,_⟩
    congr 2
    exact min_eq_left ((min_le_right _ _).trans hc)
  · funext i
    apply ContinuousMap.ext
    intro u
    change r.2 i ⟨min (min u.val (clock h s).val) (clock h t).val,_⟩=
      r.2 i ⟨min u.val (clock h s).val,_⟩
    congr 2
    exact min_eq_left ((min_le_right _ _).trans hc)

/-- The genuine canonical future filtration includes both state and
noise history. It is NOT replaced by the driver-only filtration. -/
def filtration:Filtration ℝ≥0 (inferInstance:MeasurableSpace R) where
  seq t:=MeasurableSpace.comap (history h t) inferInstance
  mono' s t hst:=by
    have hc:=history_comp (E:=E) (ι:=ι) h s t hst
    calc
      _=MeasurableSpace.comap (history h t)
        (MeasurableSpace.comap (history h s) inferInstance):=by
          rw[MeasurableSpace.comap_comp,hc]
      _≤_:=MeasurableSpace.comap_mono (history_measurable (E:=E) (ι:=ι) h s).comap_le
  le' t:=(history_measurable h t).comap_le

def coordinate(i:ι) (t:ℝ≥0) (r:R):ℝ:=r.2 i (clock h t)

theorem coordinate_adapted(i:ι) (t:ℝ≥0):
    Measurable[filtration (E:=E) (ι:=ι) h t] (coordinate h i t):=by
  have hm:Measurable (fun r:R=>r.2 i (clock h t)):=
    (ContinuousMap.measurable_eval (clock h t)).comp ((measurable_pi_apply i).comp measurable_snd)
  have he:(fun r:R=>r.2 i (clock h t)) ∘ history h t=coordinate h i t:=by
    funext r
    simp[coordinate,history,CanonicalFutureStateDriver.past,CanonicalFutureStateDriver.stopTime]
  have hh:@Measurable R ℝ (MeasurableSpace.comap (history h t) inferInstance) _
      ((fun r:R=>r.2 i (clock h t))∘history h t):=
    hm.comp (Measurable.of_comap_le le_rfl)
  rwa[he] at hh

theorem coordinate_continuous(i:ι) (r:R):Continuous (fun t=>coordinate h i t r):=
  (r.2 i).continuous.comp ((continuous_subtype_val.min continuous_const).subtype_mk _)
end SHE.CanonicalStateDriverFiltration
