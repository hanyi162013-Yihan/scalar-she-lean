module
public import SHE.OriginalScalarInputContinuity
public import SHE.HeatAgeContinuity
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace SHE.OriginalNativeRowContinuity
open MeasureTheory CircleHeat FiniteHaar DyadicApproximation AddCircle Filter
open OriginalScalarInputContinuity
open scoped ENNReal Topology
local instance originalRowContinuity_unit : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩
local instance originalRowContinuity_realSigma : MeasurableSpace RealL2 := borel _
local instance originalRowContinuity_realBorel : BorelSpace RealL2 := ⟨rfl⟩
variable (D : SmoothApproximation.ScalarData)

theorem test_tendsto {α : Type*} {l : Filter α} (τ : α→ℝ) {τ₀ : ℝ}
    (hτ : Tendsto τ l (𝓝 τ₀)) (hτ₀ : 0<τ₀) (x : StoppedFourier.HeatCircle) :
    Tendsto (fun a=>ScalarHaarHeatRows.test (τ a) x) l (𝓝 (ScalarHaarHeatRows.test τ₀ x)) := by
  have hh := (HeatAgeContinuity.continuousAt_circleHeat_age hτ₀ x).tendsto.comp hτ
  have hp := CircleNormalization.push.symm.continuous.tendsto _ |>.comp hh
  exact (Complex.reCLM.compLpL 2 haarAddCircle).continuous.tendsto _ |>.comp hp

theorem heat_input_tendsto {α : Type*} {l : Filter α}
    (τ : α→ℝ) (u : α→RealL2) {τ₀ : ℝ} (u₀ : RealL2)
    (hτ : Tendsto τ l (𝓝 τ₀)) (hu : Tendsto u l (𝓝 u₀))
    (hτ₀ : 0<τ₀) (x : StoppedFourier.HeatCircle) :
    Tendsto (fun a=>input D (u a) (ScalarHaarHeatRows.test (τ a) x)) l
      (𝓝 (input D u₀ (ScalarHaarHeatRows.test τ₀ x))) :=
  input_tendsto D u (fun a=>ScalarHaarHeatRows.test (τ a) x) u₀
    (ScalarHaarHeatRows.test τ₀ x) hu (test_tendsto τ hτ hτ₀ x) _ (heat_test_bound hτ₀ x)

/-- Literal physical g(U) row before the prescribed observation target. -/
def row (T : ℝ) (x : StoppedFourier.HeatCircle) (r : ℝ) (u : RealL2) : RealL2 :=
  input D u (ScalarHaarHeatRows.test (T-r) x)

theorem continuousAt_row (T r : ℝ) (hr : r<T) (u : RealL2) (x : StoppedFourier.HeatCircle) :
    ContinuousAt (fun p:ℝ×RealL2=>row D T x p.1 p.2) (r,u) := by
  exact heat_input_tendsto D (fun p:ℝ×RealL2=>T-p.1) Prod.snd u
    (tendsto_const_nhds.sub continuous_fst.continuousAt.tendsto)
    continuous_snd.continuousAt.tendsto (sub_pos.mpr hr) x

theorem test_norm {τ : ℝ} (hτ : 0<τ) (x : StoppedFourier.HeatCircle) :
    ‖ScalarHaarHeatRows.test τ x‖=‖StoppedFourier.circleHeat τ x‖ := by
  have he := congrArg norm (ScalarHaarHeatRows.embed_test hτ x)
  simpa only [realEmbed_norm_eq,LinearIsometryEquiv.norm_map] using he

/-- A positive observation gap bounds the original row uniformly in
the state, the physical clock and all left-frozen approximations. -/
theorem row_norm_sq_bound (T r q : ℝ) (hrq : r≤q) (hqT : q<T)
    (u : RealL2) (x : StoppedFourier.HeatCircle) :
    ‖row D T x r u‖^2≤D.upper^2*(1+StoppedFourier.heatConstant*(T-q)^(-(1/2:ℝ))) := by
  have hτ : 0<T-r := lt_of_lt_of_le (sub_pos.mpr hqT) (sub_le_sub_left hrq T)
  have hu : 0≤D.upper := (abs_nonneg _).trans (D.bounds 0).2
  have hi := input_norm_le D u (ScalarHaarHeatRows.test (T-r) x)
  have hc := StoppedFourier.circleHeat_norm_sq_bound hτ x
  have hp := Real.rpow_le_rpow_of_nonpos (sub_pos.mpr hqT) (sub_le_sub_left hrq T)
    (by norm_num : -(1/2:ℝ)≤0)
  calc
    ‖row D T x r u‖^2≤(D.upper*‖ScalarHaarHeatRows.test (T-r) x‖)^2 :=
      pow_le_pow_left₀ (norm_nonneg _) hi 2
    _=D.upper^2*‖StoppedFourier.circleHeat (T-r) x‖^2 := by rw [mul_pow,test_norm hτ]
    _≤D.upper^2*(1+StoppedFourier.heatConstant*(T-q)^(-(1/2:ℝ))) :=
      mul_le_mul_of_nonneg_left (hc.trans (add_le_add le_rfl
        (mul_le_mul_of_nonneg_left hp StoppedFourier.heatConstant_pos.le))) (sq_nonneg _)
end SHE.OriginalNativeRowContinuity
