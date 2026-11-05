module

public import SHE.GaussianCovariancePath

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-! A genuine diagonal-curve chain rule from a uniform mean Taylor
remainder. Separate partial derivatives alone are not used as a chain rule. -/
namespace SHE.MovingMeanChain
open Set Filter Asymptotics
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem hasDerivAt {f : ℝ → E → ℝ} {m : ℝ → E} {G : ℝ → E →L[ℝ] ℝ}
    {θ a B : ℝ} {d : E}
    (hf : HasDerivAt (fun s => f s (m θ)) a θ) (hm : HasDerivAt m d θ)
    (hG : ContinuousAt G θ) (hB : 0 ≤ B)
    (hTaylor : ∀ s x, ‖f s (m θ + x) - f s (m θ) - G s x‖ ≤ B * ‖x‖ ^ 2) :
    HasDerivAt (fun s => f s (m s)) (a + G θ d) θ := by
  let Δ : ℝ → E := fun s => m s - m θ
  let R : ℝ → ℝ := fun s => f s (m s) - f s (m θ) - G θ (Δ s)
  let b : ℝ → ℝ := fun s => B * ‖Δ s‖ + ‖G s - G θ‖
  have hΔ : Tendsto Δ (nhds θ) (nhds 0) := by
    simpa only [Δ, sub_self] using hm.continuousAt.tendsto.sub_const (m θ)
  have hΔO : (fun s => ‖Δ s‖) =O[nhds θ] (fun s => s - θ) := hm.isBigO_sub.norm_left
  have hb : Tendsto b (nhds θ) (nhds 0) := by
    have hh := (hΔ.norm.const_mul B).add ((hG.tendsto.sub_const (G θ)).norm)
    simpa only [b, sub_self, norm_zero, mul_zero, add_zero] using hh
  have hb0 (s : ℝ) : 0 ≤ b s := add_nonneg (mul_nonneg hB (norm_nonneg _)) (norm_nonneg _)
  have hpoint (s : ℝ) : ‖R s‖ ≤ ‖Δ s‖ * b s := by
    have ht := hTaylor s (Δ s)
    have he : R s = (f s (m θ + Δ s) - f s (m θ) - G s (Δ s)) + (G s - G θ) (Δ s) := by
      dsimp [R, Δ]
      rw [add_sub_cancel, sub_apply]
      ring
    rw [he]
    calc
      _ ≤ ‖f s (m θ + Δ s) - f s (m θ) - G s (Δ s)‖ + ‖(G s - G θ) (Δ s)‖ := norm_add_le _ _
      _ ≤ B * ‖Δ s‖ ^ 2 + ‖G s - G θ‖ * ‖Δ s‖ := add_le_add ht ((G s - G θ).le_opNorm _)
      _ = _ := by dsimp [b]; ring
  have hRO : R =O[nhds θ] (fun s => ‖Δ s‖ * b s) := by
    refine isBigO_iff.mpr ⟨1, Eventually.of_forall (fun s => ?_)⟩
    simpa only [one_mul, norm_mul, Real.norm_eq_abs, abs_norm, abs_of_nonneg (hb0 s)] using hpoint s
  have hprod : (fun s => ‖Δ s‖ * b s) =o[nhds θ] (fun s => s - θ) := by
    simpa only [mul_one] using hΔO.mul_isLittleO ((isLittleO_one_iff ℝ).mpr hb)
  have hR := hRO.trans_isLittleO hprod
  have hl := ((G θ).hasFDerivAt.comp_hasDerivAt θ hm).sub_const (G θ (m θ))
  have hq := hf.add hl
  have hh := hR.add hq.isLittleO
  apply HasDerivAt.of_isLittleO
  convert! hh using 1
  funext s
  dsimp only [R, Δ, Function.comp_def, Pi.add_apply]
  rw [map_sub]
  ring

end SHE.MovingMeanChain
