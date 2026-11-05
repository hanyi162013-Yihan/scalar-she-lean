module

public import SHE.NativeHeatConvolution

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.NativeHeatAction
open Set MeasureTheory AddCircle StoppedFourier NativeHeatSpan
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩

def edge (t : ℝ) (ht : 0 < t) (a x : HeatCircle) : ℝ := ‖kernel t ht a x‖

theorem continuous_edge {t : ℝ} (ht : 0 < t) :
    Continuous (fun p : HeatCircle × HeatCircle => edge t ht p.1 p.2) := by
  have he : (fun p : HeatCircle × HeatCircle => edge t ht p.1 p.2) =
      fun p => ‖ProfileVariance.heatPhysical t p.1 p.2‖ := by
    funext p
    rw [edge,kernel_eq_physical]
  rw [he]
  exact (continuous_heatPhysical_space ht).norm

theorem edge_mass {t : ℝ} (ht : 0 < t) (a : HeatCircle) :
    (∫ x,edge t ht a x ∂haarAddCircle) = 1 := kernel_norm_mass ht a

def action (t : ℝ) (ht : 0 < t) (F : HeatCircle → ℝ) (a : HeatCircle) : ℝ :=
  ∫ x,edge t ht a x*F x ∂haarAddCircle

theorem action_const {t : ℝ} (ht : 0 < t) (b : ℝ) (a : HeatCircle) :
    action t ht (fun _ => b) a = b := by
  rw [action,integral_mul_const,edge_mass ht a,one_mul]

theorem action_measurable {t : ℝ} (ht : 0 < t) {F : HeatCircle → ℝ} (hF : Measurable F) :
    Measurable (action t ht F) := by
  have hm : Measurable (fun p : HeatCircle × HeatCircle => edge t ht p.1 p.2*F p.2) :=
    (continuous_edge ht).measurable.mul (hF.comp measurable_snd)
  exact hm.stronglyMeasurable.integral_prod_right.measurable

theorem action_integrable {t : ℝ} (ht : 0 < t) {F : HeatCircle → ℝ}
    (hF : Measurable F) {B : ℝ} (hb : ∀ x,|F x| ≤ B) (a : HeatCircle) :
    Integrable (fun x => edge t ht a x*F x) haarAddCircle := by
  have hk : Integrable (fun x => edge t ht a x) haarAddCircle :=
    ((continuous_edge ht).comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  exact hk.mul_bdd hF.aestronglyMeasurable (ae_of_all _ (fun x => by
    simpa only [Real.norm_eq_abs] using hb x))

theorem action_abs_bound {t : ℝ} (ht : 0 < t) {F : HeatCircle → ℝ}
    (hF : Measurable F) {B : ℝ} (hB : 0 ≤ B) (hb : ∀ x,|F x| ≤ B) (a : HeatCircle) :
    |action t ht F a| ≤ B := by
  have hk : Integrable (fun x => edge t ht a x*B) haarAddCircle :=
    action_integrable ht (F := fun _ => B) measurable_const (B := B)
      (fun _ => by rw [abs_of_nonneg hB]) a
  have hi := action_integrable ht hF hb a
  have hh := norm_integral_le_of_norm_le (f := fun x => edge t ht a x*F x) hk
    (ae_of_all _ (fun x => by
      rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (show 0 ≤ edge t ht a x from norm_nonneg _)]
      exact mul_le_mul_of_nonneg_left (hb x) (norm_nonneg _)))
  simpa only [action,Real.norm_eq_abs,integral_mul_const,edge_mass ht a,one_mul] using hh

/-- Genuine semigroup composition for arbitrary bounded Borel endpoint
tests, preserving both original physical heat ages. -/
theorem action_add {s t : ℝ} (hs : 0 < s) (ht : 0 < t) {F : HeatCircle → ℝ}
    (hF : Measurable F) {B : ℝ} (hb : ∀ x,|F x| ≤ B) (a : HeatCircle) :
    action s hs (action t ht F) a = action (s+t) (add_pos hs ht) F a := by
  have hK : Continuous (fun p : HeatCircle × HeatCircle => edge s hs a p.1*edge t ht p.1 p.2) :=
    ((continuous_edge hs).comp (continuous_const.prodMk continuous_fst)).mul (continuous_edge ht)
  have hi : Integrable (fun p : HeatCircle × HeatCircle =>
      edge s hs a p.1*edge t ht p.1 p.2*F p.2) (haarAddCircle.prod haarAddCircle) :=
    (hK.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).mul_bdd
      (hF.comp measurable_snd).aestronglyMeasurable (ae_of_all _ (fun p => by
        simpa only [Real.norm_eq_abs] using hb p.2))
  calc
    _ = ∫ x : HeatCircle,∫ y : HeatCircle,edge s hs a x*edge t ht x y*F y
        ∂haarAddCircle ∂haarAddCircle := by
      unfold action
      apply integral_congr_ae
      exact ae_of_all _ (fun x => by dsimp only; rw [← integral_const_mul]; congr 1; funext y; ring)
    _ = ∫ y : HeatCircle,∫ x : HeatCircle,edge s hs a x*edge t ht x y*F y
        ∂haarAddCircle ∂haarAddCircle := integral_integral_swap hi
    _ = action (s+t) (add_pos hs ht) F a := by
      unfold action
      apply integral_congr_ae
      exact ae_of_all _ (fun y => by
        dsimp only
        rw [integral_mul_const]
        exact congrArg (fun z : ℝ => z*F y) (kernel_norm_convolution hs ht a y))

end SHE.NativeHeatAction
