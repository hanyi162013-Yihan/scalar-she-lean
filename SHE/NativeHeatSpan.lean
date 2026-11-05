module

public import SHE.HeatMarkov
public import SHE.GlobalTorusHeatSpan

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.NativeHeatSpan
open Set Filter MeasureTheory ProbabilityTheory AddCircle StoppedFourier HeatTorusKernel
open scoped BigOperators
local instance nativeHeatSpan_nativePositive : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
local instance nativeHeatSpan_unitPositive : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

def clock (t : ℝ) : ℝ := t / (4 * Real.pi ^ 2)
def unitCenter (x : HeatCircle) : UnitAddCircle := CircleNormalization.scale (2*Real.pi) 1 x
def weight (t : ℝ) (a x : HeatCircle) : ℝ :=
  GlobalTorusHeatSpan.weight (clock t) (unitCenter a) (unitCenter x)

theorem clock_pos {t : ℝ} (ht : 0 < t) : 0 < clock t := div_pos ht (by positivity)
theorem weight_nonneg (t : ℝ) (a x : HeatCircle) : 0 ≤ weight t a x := by
  unfold weight GlobalTorusHeatSpan.weight
  positivity

theorem scale_inverse (x : HeatCircle) :
    CircleNormalization.scale 1 (2*Real.pi) (unitCenter x) = x := by
  induction x using Quotient.inductionOn with
  | _ r =>
    simp only [unitCenter, CircleNormalization.scale, AddCircle.equivAddCircle_apply_mk]
    congr 1
    field_simp

theorem push_unit_kernel (t : ℝ) (a : HeatCircle) :
    CircleNormalization.push (unitHeatKernel (clock t) (unitCenter a)) = circleHeat t a := by
  rw [HeatMarkov.push_unitHeatKernel, scale_inverse]
  congr 1
  unfold clock
  field_simp

theorem native_heat_sum_envelope (q : ℕ) :
    ∃ H C : ℝ, 0 < H ∧ 0 < C ∧
      ∀ (t : Fin q → ℝ) (a : Fin q → HeatCircle) (z : Fin q → ℂ),
      (∀ i, 0 < t i) → (∀ i, t i ≤ H) →
      ∀ᵐ x : HeatCircle ∂haarAddCircle,
        ‖(∑ i, z i • circleHeat (t i) (a i)) x‖ ^ 2 ≤
          C * ‖∑ i, z i • circleHeat (t i) (a i)‖ ^ 2 * ∑ i, weight (t i) (a i) x := by
  obtain ⟨h, C, hh, _, hC, henv⟩ := GlobalTorusHeatSpan.finite_torus_heat_span_envelope_ae q
  refine ⟨4*Real.pi^2*h, C, by positivity, hC, ?_⟩
  intro t a z ht hth
  let F := ∑ i, z i • unitHeatKernel (clock (t i)) (unitCenter (a i))
  have hspan : F ∈ Submodule.span ℂ (Set.range (fun i => unitHeatKernel (clock (t i)) (unitCenter (a i)))) := by
    apply Submodule.sum_mem
    intro i hi
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hsmall (i : Fin q) : clock (t i) ≤ h := (div_le_iff₀ (by positivity : 0 < 4*Real.pi^2)).mpr (by
    simpa only [mul_comm, clock] using hth i)
  have hF := henv (fun i => clock (t i)) (fun i => unitCenter (a i)) (fun i => clock_pos (ht i)) hsmall F hspan
  have hpush : CircleNormalization.push F = ∑ i, z i • circleHeat (t i) (a i) := by
    simp only [F, map_sum, map_smul, push_unit_kernel]
  have hnorm : ‖F‖ = ‖∑ i, z i • circleHeat (t i) (a i)‖ := by
    rw [← hpush, CircleNormalization.push.norm_map]
  have hpoint := CircleNormalization.push_ae F
  rw [hpush] at hpoint
  have hp := (CircleNormalization.scale_measurePreserving (2*Real.pi) 1).quasiMeasurePreserving.ae hF
  filter_upwards [hp, hpoint] with x hx he
  rw [he]
  simpa only [hnorm, weight, unitCenter] using hx

end SHE.NativeHeatSpan
