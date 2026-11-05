module

public import SHE.UniformSmooth
public import Mathlib.Topology.UniformSpace.UniformApproximation

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section

namespace SHE.ParameterSmoothContinuity
open Set Filter Topology
variable {X : Type*} {E G : Type} [TopologicalSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem first_order_remainder {F : E → G} (hF : ContDiff ℝ 2 F)
    {B : ℝ} (hB : 0 ≤ B) (hDD : ∀ z,‖fderiv ℝ (fderiv ℝ F) z‖ ≤ B) (z x : E) :
    ‖F (z+x)-F z-fderiv ℝ F z x‖ ≤ B*‖x‖^2 := by
  have hF1 : ContDiff ℝ 1 (fderiv ℝ F) := hF.fderiv_right (by norm_num)
  have hgrad (v w : E) : ‖fderiv ℝ F w-fderiv ℝ F v‖ ≤ B*‖w-v‖ :=
    Convex.norm_image_sub_le_of_norm_fderiv_le
      (fun y _ => hF1.differentiable (by norm_num) y) (fun y _ => hDD y)
      convex_univ (mem_univ v) (mem_univ w)
  let g : ℝ → G := fun t => F (z+t • x)-F z-t • fderiv ℝ F z x
  have hg (t : ℝ) : HasDerivAt g ((fderiv ℝ F (z+t • x)-fderiv ℝ F z) x) t := by
    have hl : HasDerivAt (fun t : ℝ => z+t • x) x t := by
      simpa only [one_smul,id_eq] using ((hasDerivAt_id t).smul_const x).const_add z
    have hh := ((hF.differentiable (by norm_num) (z+t • x)).hasFDerivAt.comp_hasDerivAt t hl).sub_const (F z)
    convert hh.sub ((hasDerivAt_id t).smul_const (fderiv ℝ F z x)) using 1
    · rfl
    · simp only [ContinuousLinearMap.sub_apply,one_smul]
  have hb (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
      ‖(fderiv ℝ F (z+t • x)-fderiv ℝ F z) x‖ ≤ B*‖x‖^2 := by
    calc
      _ ≤ ‖fderiv ℝ F (z+t • x)-fderiv ℝ F z‖*‖x‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (B*‖(z+t • x)-z‖)*‖x‖ := mul_le_mul_of_nonneg_right (hgrad z _) (norm_nonneg _)
      _ = t*(B*‖x‖^2) := by
        rw [add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_nonneg ht.1]
        ring
      _ ≤ _ := mul_le_of_le_one_left (by positivity) ht.2
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t _ => (hg t).hasDerivWithinAt) hb (convex_Icc (0:ℝ) 1)
    (show (0:ℝ) ∈ Icc 0 1 by norm_num) (show (1:ℝ) ∈ Icc 0 1 by norm_num)
  simpa only [g,zero_smul,add_zero,sub_self,sub_zero,one_smul,norm_one,mul_one] using hh

theorem difference_quotient_bound {F : E → G} (hF : ContDiff ℝ 2 F)
    {B s : ℝ} (hB : 0 ≤ B) (hDD : ∀ z,‖fderiv ℝ (fderiv ℝ F) z‖ ≤ B)
    (hs : 0 < s) (z v : E) :
    ‖s⁻¹ • (F (z+s • v)-F z)-fderiv ℝ F z v‖ ≤ B*s*‖v‖^2 := by
  have he : s⁻¹ • (F (z+s • v)-F z)-fderiv ℝ F z v=
      s⁻¹ • (F (z+s • v)-F z-fderiv ℝ F z (s • v)) := by
    simp only [map_smul,smul_sub,smul_smul,inv_mul_cancel₀ hs.ne',one_smul]
  rw [he,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hs)]
  have hb := mul_le_mul_of_nonneg_left (first_order_remainder hF hB hDD z (s • v)) (inv_nonneg.mpr hs.le)
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos hs] at hb
  convert hb using 1 <;> field_simp <;> ring

/-- Joint continuity of a family and a uniform second derivative bound
imply joint continuity of its genuine first derivative. A finite
difference argument avoids any differentiability in the parameter. -/
theorem continuous_fderiv [FiniteDimensional ℝ E] (F : X → E → G)
    (hF : Continuous (fun p : X × E => F p.1 p.2))
    (hFs : ∀ p,ContDiff ℝ 2 (F p)) {B : ℝ} (hB : 0 ≤ B)
    (hDD : ∀ p z,‖fderiv ℝ (fderiv ℝ (F p)) z‖ ≤ B) :
    Continuous (fun p : X × E => fderiv ℝ (F p.1) p.2) := by
  rw [continuous_clm_apply]
  intro v
  let s : ℕ → ℝ := fun n => 1/((n:ℝ)+1)
  have hs (n : ℕ) : 0 < s n := by dsimp [s]; positivity
  let Q : ℕ → X × E → G := fun n p => (s n)⁻¹ • (F p.1 (p.2+s n • v)-F p.1 p.2)
  have hQ (n : ℕ) : Continuous (Q n) := by
    exact ((hF.comp (continuous_fst.prodMk (continuous_snd.add continuous_const))).sub hF).const_smul _
  have he : Tendsto (fun n => B*s n*‖v‖^2) atTop (𝓝 0) := by
    have hh := (tendsto_const_nhds (x := B)).mul
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    have hh' := hh.mul_const (‖v‖^2)
    simpa only [mul_zero,zero_mul] using hh'
  have hu : TendstoUniformly Q (fun p : X × E => fderiv ℝ (F p.1) p.2 v) atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    filter_upwards [he.eventually (gt_mem_nhds hε)] with n hn
    intro p
    rw [dist_eq_norm,norm_sub_rev]
    exact (difference_quotient_bound (hFs p.1) hB (hDD p.1) (hs n) p.2 v).trans_lt hn
  exact hu.continuous (Eventually.of_forall hQ).frequently

/-- In particular a uniformly bounded smooth family needs only joint
continuity of its values to obtain joint continuity of its Hessians. -/
theorem continuous_hessian [FiniteDimensional ℝ E] (F : X → E → G)
    (hF : Continuous (fun p : X × E => F p.1 p.2))
    (hFs : UniformSmooth.UniformBoundedSmooth F) :
    Continuous (fun p : X × E => fderiv ℝ (fderiv ℝ (F p.1)) p.2) := by
  obtain ⟨B,hB,hDb⟩ := hFs.fderiv.fderiv.norm_bound
  have hd := continuous_fderiv F hF (fun p => (hFs.smooth p).of_le (by simp)) hB hDb
  obtain ⟨C,hC,hDc⟩ := hFs.fderiv.fderiv.fderiv.norm_bound
  exact continuous_fderiv (fun p => fderiv ℝ (F p)) hd
    (fun p => (hFs.fderiv.smooth p).of_le (by simp)) hC hDc

end SHE.ParameterSmoothContinuity
