module

public import SHE.NullCompleteFiltration
public import SHE.PredictableTime

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section

namespace SHE.PredictableTimeDilation
open MeasureTheory Set PredictableL2
open scoped NNReal
variable {Ω : Type*} [MeasurableSpace Ω]

/-- Multiplication by a strictly positive deterministic clock rate. -/
def clock (c : ℝ≥0) (hc : 0<c) : ℝ≥0 ≃o ℝ≥0 where
  toFun t := c*t
  invFun t := c⁻¹*t
  left_inv t := by simp only [← mul_assoc,inv_mul_cancel₀ (ne_of_gt hc),one_mul]
  right_inv t := by simp only [← mul_assoc,mul_inv_cancel₀ (ne_of_gt hc),one_mul]
  map_rel_iff' := by intro s t; exact mul_le_mul_iff_right₀ hc

theorem clock_continuous (c : ℝ≥0) (hc : 0<c) : Continuous (clock c hc) :=
  continuous_const.mul continuous_id

theorem clock_symm_continuous (c : ℝ≥0) (hc : 0<c) : Continuous (clock c hc).symm :=
  continuous_const.mul continuous_id

def filtration (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (e : ℝ≥0≃oℝ≥0) :
    Filtration ℝ≥0 ‹MeasurableSpace Ω› where
  seq t := 𝓕 (e.symm t)
  mono' := 𝓕.mono'.comp e.symm.monotone
  le' t := 𝓕.le (e.symm t)

theorem filtration_clock (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (e : ℝ≥0≃oℝ≥0) (t : ℝ≥0) :
    filtration 𝓕 e (e t)=𝓕 t := by simp only [filtration,OrderIso.symm_apply_apply]

/-- The predictable sigma algebra transports under the actual clock,
including the initial-time generators. -/
theorem measurable_clock (𝓕 𝓖 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (e : ℝ≥0≃oℝ≥0)
    (hFG : ∀ t,𝓖 (e t)=𝓕 t) :
    @Measurable (ℝ≥0×Ω) (ℝ≥0×Ω) 𝓕.predictable 𝓖.predictable (fun p => (e p.1,p.2)) := by
  rw [measurable_iff_comap_le,MeasurableSpace.comap_le_iff_le_map]
  apply measurableSpace_le_predictable_of_measurableSet
  · intro A hA
    have hA' : MeasurableSet[𝓕 0] A := by
      have he0 : e (0 : ℝ≥0)=0 := e.map_bot
      have h0 : 𝓖 0=𝓕 0 := by simpa only [he0] using hFG 0
      exact h0 ▸ hA
    change MeasurableSet[𝓕.predictable] ((fun p : ℝ≥0×Ω => (e p.1,p.2)) ⁻¹' ({0}×ˢA))
    have he : (fun p : ℝ≥0×Ω => (e p.1,p.2)) ⁻¹' ({0}×ˢA)=({0}:Set ℝ≥0)×ˢA := by
      ext p
      simp only [mem_preimage,mem_prod,mem_singleton_iff]
      have he0 : e (0 : ℝ≥0)=0 := e.map_bot
      exact and_congr_left (fun _ => ⟨fun h => e.injective (h.trans he0.symm),fun h => by rw [h,he0]⟩)
    rw [he]
    exact measurableSet_predictable_singleton_bot_prod hA'
  · intro t A hA
    have hA' : MeasurableSet[𝓕 (e.symm t)] A := by
      have hh := hFG (e.symm t)
      simp only [OrderIso.apply_symm_apply] at hh
      rwa [← hh]
    change MeasurableSet[𝓕.predictable] ((fun p : ℝ≥0×Ω => (e p.1,p.2)) ⁻¹' (Ioi t×ˢA))
    have he : (fun p : ℝ≥0×Ω => (e p.1,p.2)) ⁻¹' (Ioi t×ˢA)=Ioi (e.symm t)×ˢA := by
      ext p
      simp only [mem_preimage,mem_prod,mem_Ioi]
      exact and_congr_left (fun _ => by
        simpa only [OrderIso.apply_symm_apply] using (e.lt_iff_lt (x := e.symm t) (y := p.1)))
    rw [he]
    exact measurableSet_predictable_Ioi_prod hA'

theorem measurable_forward (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (e : ℝ≥0≃oℝ≥0) :
    @Measurable (ℝ≥0×Ω) (ℝ≥0×Ω) 𝓕.predictable (filtration 𝓕 e).predictable
      (fun p => (e p.1,p.2)) := measurable_clock 𝓕 (filtration 𝓕 e) e (filtration_clock 𝓕 e)

theorem measurable_backward (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (e : ℝ≥0≃oℝ≥0) :
    @Measurable (ℝ≥0×Ω) (ℝ≥0×Ω) (filtration 𝓕 e).predictable 𝓕.predictable
      (fun p => (e.symm p.1,p.2)) := by
  exact measurable_clock (filtration 𝓕 e) 𝓕 e.symm (fun _ => rfl)

theorem containsNullSets (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (e : ℝ≥0≃oℝ≥0)
    (μ : Measure Ω) (hnull : NullCompleteFiltration.ContainsNullSets 𝓕 μ) :
    NullCompleteFiltration.ContainsNullSets (filtration 𝓕 e) μ := by
  intro t A hA
  exact hnull (e.symm t) A hA

end SHE.PredictableTimeDilation
