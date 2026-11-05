module

public import SHEStochastic.JointStateDriverPath
public import SHEStochastic.JointDriverCharacteristic

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section

namespace SHEStochastic.JointPathFiltration
open MeasureTheory ProbabilityTheory StoppedPathPasting AdaptedCanonicalPathTests
open scoped NNReal

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [Countable ι] [DecidableEq ι] (H : ℝ≥0)

abbrev Space := Path H (JointStateDriverPath.State E ι)

def history (q : ℝ≥0) : Space (E := E) (ι := ι) H → Space (E := E) (ι := ι) H :=
  stopped H (clock H q)

theorem continuous_history (q : ℝ≥0) : Continuous (history (E := E) (ι := ι) H q) :=
  (continuous_stopped H).comp (continuous_const.prodMk continuous_id)

theorem history_comp (s t : ℝ≥0) (hst : s ≤ t) :
    history (E := E) (ι := ι) H s ∘ history H t = history H s := by
  have hc : (clock H s).val ≤ (clock H t).val := min_le_min_right _ (by exact_mod_cast hst)
  funext x
  apply ContinuousMap.ext
  intro q
  change x (pastTime H (clock H t) (pastTime H (clock H s) q)) = x (pastTime H (clock H s) q)
  congr 1
  apply Subtype.ext
  exact min_eq_left ((min_le_right _ _).trans hc)

/-- The full canonical filtration retains the state and every driver
coordinate through the current time. -/
def filtration : Filtration ℝ≥0 (inferInstance : MeasurableSpace (Space (E := E) (ι := ι) H)) where
  seq q := MeasurableSpace.comap (history H q) inferInstance
  mono' s t hst := by
    have hc := history_comp (E := E) (ι := ι) H s t hst
    calc
      _ = MeasurableSpace.comap (history H t) (MeasurableSpace.comap (history H s) inferInstance) := by
        rw [MeasurableSpace.comap_comp, hc]
      _ ≤ _ := MeasurableSpace.comap_mono (continuous_history H s).measurable.comap_le
  le' q := (continuous_history H q).measurable.comap_le

theorem evaluation_adapted (t : Time H) :
    Measurable[filtration (E := E) (ι := ι) H (toNN H t)] (fun x : Space (E := E) (ι := ι) H ↦ x t) := by
  have hm := ContinuousMap.measurable_eval t (Y := JointStateDriverPath.State E ι)
  have he : (fun x : Space (E := E) (ι := ι) H ↦ x t) ∘ history H (toNN H t) = fun x ↦ x t := by
    funext x
    change x (pastTime H (clock H (toNN H t)) t) = x t
    rw [clock_toNN]
    congr 1
    exact Subtype.ext (min_self t.val)
  have hh := hm.comp (Measurable.of_comap_le (show
    MeasurableSpace.comap (history (E := E) (ι := ι) H (toNN H t)) inferInstance ≤
      filtration H (toNN H t) from le_rfl))
  rwa [he] at hh

def driver (i : ι) (q : ℝ≥0) (x : Space (E := E) (ι := ι) H) : ℝ :=
  (x (clock H q)).2 i-(x (origin H)).2 i

theorem driver_adapted (i : ι) (q : ℝ≥0) :
    Measurable[filtration (E := E) (ι := ι) H q] (driver H i q) := by
  have hq := (evaluation_adapted (E := E) (ι := ι) H (clock H q)).mono
    ((filtration H).mono (show toNN H (clock H q) ≤ q from min_le_left _ _)) le_rfl
  have hzero := (evaluation_adapted (E := E) (ι := ι) H (origin H)).mono
    ((filtration H).mono (show toNN H (origin H) ≤ q from zero_le)) le_rfl
  exact ((measurable_pi_apply i).comp hq.snd).sub ((measurable_pi_apply i).comp hzero.snd)

theorem driver_continuous (i : ι) (x : Space (E := E) (ι := ι) H) :
    Continuous (fun q ↦ driver H i q x) :=
  (((continuous_apply i).comp continuous_snd).comp (x.continuous.comp (continuous_clock H))).sub continuous_const

@[simp] theorem driver_zero (i : ι) (x : Space (E := E) (ι := ι) H) : driver H i 0 x = 0 := by
  have hz : clock H 0 = origin H := Subtype.ext (min_eq_left H.property)
  simp only [driver, hz, sub_self]

end SHEStochastic.JointPathFiltration
