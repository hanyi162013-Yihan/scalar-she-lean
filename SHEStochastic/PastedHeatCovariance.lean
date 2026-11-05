module

public import SHEStochastic.PathIntegratedCovariance

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section

namespace SHEStochastic.PastedHeatCovariance
open MeasureTheory StoppedPathPasting PastedGeneratorFunctional
open scoped NNReal

variable {E : Type*} [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E] [T2Space E]
  (H : ℝ≥0) (rate : ℝ) (hrate : 0 ≤ rate) (b : BoundedContinuousFunction E ℝ)

def value (x : Path H E) (t : Time H) : ℝ :=
  PathIntegratedCovariance.value H (PathIntegratedCovariance.exponential H rate hrate) b x t

theorem value_eq (x : Path H E) (t : Time H) :
    value H rate hrate b x t = ∫ s in 0..t.val, Real.exp (rate*s)*b (read H x s) := by
  apply intervalIntegral.integral_congr_Ioo_of_le t.property.1
  intro s hs
  dsimp only
  rw [PathIntegratedCovariance.exponential_apply H rate hrate s ⟨hs.1.le, hs.2.le.trans t.property.2⟩]
  rw [mul_comm s rate]

@[simp] theorem value_origin (x : Path H E) : value H rate hrate b x (origin H) = 0 := by
  simp [value_eq, origin]

theorem continuous_value : Continuous (fun p : Path H E × Time H ↦ value H rate hrate b p.1 p.2) :=
  PathIntegratedCovariance.continuous_value H _ b

theorem norm_bound (x : Path H E) (t : Time H) :
    ‖value H rate hrate b x t‖ ≤ ‖PathIntegratedCovariance.exponential H rate hrate‖*‖b‖*H :=
  PathIntegratedCovariance.norm_bound H _ b x t

theorem value_before (r t : Time H) (x y : Path H E) (ht : t.val ≤ r.val) :
    value H rate hrate b (paste H r x y) t = value H rate hrate b x t := by
  rw [value_eq, value_eq]
  apply intervalIntegral.integral_congr_Ioo_of_le t.property.1
  intro s hs
  dsimp only
  rw [read_before H r x y s ⟨hs.1.le, hs.2.le.trans ht⟩]

theorem value_after (r t : Time H) (x y : Path H E) (ht : r.val ≤ t.val)
    (hjoin : y (origin H) = x r) :
    value H rate hrate b (paste H r x y) t =
      value H rate hrate b x r+Real.exp (rate*r.val)*value H rate hrate b y (futureTime H r t) := by
  have hi (u v : ℝ) : IntervalIntegrable
      (fun s ↦ Real.exp (rate*s)*b (read H (paste H r x y) s)) volume u v :=
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
      (b.continuous.comp (continuous_read H (paste H r x y)))).intervalIntegrable u v
  have hpre : (∫ s in 0..r.val, Real.exp (rate*s)*b (read H (paste H r x y) s)) =
      value H rate hrate b x r := (value_eq H rate hrate b (paste H r x y) r).symm.trans
        (value_before H rate hrate b r r x y le_rfl)
  have hpost : (∫ s in r.val..t.val, Real.exp (rate*s)*b (read H (paste H r x y) s)) =
      Real.exp (rate*r.val)*value H rate hrate b y (futureTime H r t) := by
    calc
      _ = ∫ s in r.val..t.val,
          Real.exp (rate*r.val)*(Real.exp (rate*(s-r.val))*b (read H y (s-r.val))) := by
        apply intervalIntegral.integral_congr_Ioo_of_le ht
        intro s hs
        dsimp only
        rw [read_after H r x y hjoin s ⟨hs.1.le, hs.2.le.trans t.property.2⟩]
        have he : Real.exp (rate*s) = Real.exp (rate*r.val)*Real.exp (rate*(s-r.val)) := by
          rw [← Real.exp_add]
          congr 1
          ring
        rw [he, mul_assoc]
      _ = Real.exp (rate*r.val)*(∫ s in 0..(t.val-r.val), Real.exp (rate*s)*b (read H y s)) := by
        rw [intervalIntegral.integral_const_mul]
        congr 1
        simpa only [sub_self] using
          (intervalIntegral.integral_comp_sub_right (fun s ↦ Real.exp (rate*s)*b (read H y s))
            (a := r.val) (b := t.val) r.val)
      _ = _ := by
        rw [value_eq]
        change _ = Real.exp (rate*r.val)*(∫ s in 0..max (t.val-r.val) 0, Real.exp (rate*s)*b (read H y s))
        rw [max_eq_left (sub_nonneg.mpr ht)]
  rw [value_eq, ← intervalIntegral.integral_add_adjacent_intervals (hi 0 r.val) (hi r.val t.val), hpre, hpost]

theorem value_paste (r t : Time H) (x y : Path H E) (hjoin : y (origin H) = x r) :
    value H rate hrate b (paste H r x y) t =
      value H rate hrate b x (pastTime H r t)+
        Real.exp (rate*r.val)*value H rate hrate b y (futureTime H r t) := by
  rcases le_total t.val r.val with ht | ht
  · have hp : pastTime H r t = t := Subtype.ext (min_eq_left ht)
    have hf : futureTime H r t = origin H := Subtype.ext (max_eq_right (sub_nonpos.mpr ht))
    rw [hp, hf, value_origin, mul_zero, add_zero]
    exact value_before H rate hrate b r t x y ht
  · rw [show pastTime H r t = r from Subtype.ext (min_eq_right ht)]
    exact value_after H rate hrate b r t x y ht hjoin

theorem increment_paste (r s t : Time H) (x y : Path H E) (hjoin : y (origin H) = x r) :
    value H rate hrate b (paste H r x y) t-value H rate hrate b (paste H r x y) s =
      (value H rate hrate b x (pastTime H r t)-value H rate hrate b x (pastTime H r s))+
        Real.exp (rate*r.val)*(value H rate hrate b y (futureTime H r t)-
          value H rate hrate b y (futureTime H r s)) := by
  rw [value_paste H rate hrate b r t x y hjoin, value_paste H rate hrate b r s x y hjoin]
  ring

end SHEStochastic.PastedHeatCovariance
