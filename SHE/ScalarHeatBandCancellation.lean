module

public import SHE.ScalarHeatBands
public import SHE.ScalarGaussianJetScale
public import SHE.ScalarGaussianHeatEquation

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
namespace SHE.ScalarHeatBandCancellation
open Set MeasureTheory ProbabilityTheory Filter Topology Real GaussianAudit SmoothCylinders ScalarGaussianSemigroup ScalarGaussianJetScale
open scoped NNReal ENNReal

theorem variance_lipschitz {a : ℝ→ℝ} (ha : BoundedSmooth a) {H β lo : ℝ}
    (hH : 0≤H) (hβ : 0≤β) (hβ1 : β≤1) (hlo : 0<lo)
    (hh : ∀ x y,|a x-a y|≤H*|x-y|^β) (n : ℕ) (x : ℝ)
    {v w : ℝ} (hv : lo≤v) (hw : lo≤w) :
    |iteratedDeriv n (heat w.toNNReal a) x-iteratedDeriv n (heat v.toNNReal a) x|≤
      ((1/2:ℝ)*H*constant β (n+1)*lo^((β-(n:ℝ)-2)/2))*|w-v| := by
  let f : ℝ→ℝ:=fun t=>iteratedDeriv n (heat t.toNNReal a) x
  have hd (t : ℝ) (ht : t∈Ici lo) := ScalarGaussianHeatEquation.hasDerivAt_jet ha (hlo.trans_le ht) n x
  have hb (t : ℝ) (ht : t∈Ici lo) : ‖deriv f t‖≤
      (1/2:ℝ)*H*constant β (n+1)*lo^((β-(n:ℝ)-2)/2) := by
    rw [(hd t ht).deriv]
    rw [norm_mul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<1/2)]
    have hh':=jet_holder t.toNNReal ((Real.toNNReal_pos.mpr (hlo.trans_le ht)).ne') ha hH hβ hh (n+1) x
    have hp : (t.toNNReal:ℝ)=t:=Real.coe_toNNReal _ (hlo.le.trans ht)
    simp only [hp,Nat.cast_add,Nat.cast_one] at hh'
    rw [show (β-((n:ℝ)+1)-1)/2=(β-(n:ℝ)-2)/2 by ring] at hh'
    have hr : t^((β-(n:ℝ)-2)/2)≤lo^((β-(n:ℝ)-2)/2):=
      Real.rpow_le_rpow_of_nonpos hlo ht (by have hn : 0≤(n:ℝ):=Nat.cast_nonneg n; linarith)
    have hc : 0≤H*constant β (n+1):=mul_nonneg hH (constant_nonneg β (n+1))
    have hjet : |iteratedDeriv (n+2) (heat t.toNNReal a) x|≤H*constant β (n+1)*lo^((β-(n:ℝ)-2)/2):=by
      convert! hh'.trans (mul_le_mul_of_nonneg_left hr hc) using 1 <;> congr 2 <;> ring
    simpa only [Real.norm_eq_abs,mul_assoc] using mul_le_mul_of_nonneg_left hjet (by norm_num : (0:ℝ)≤1/2)
  have hi:=Convex.norm_image_sub_le_of_norm_deriv_le
    (f:=f) (s:=Ici lo) (fun t ht=>(hd t ht).differentiableAt) hb (convex_Ici lo) hv hw
  simpa only [f,Real.norm_eq_abs] using hi

theorem heat_sub (σ : ℝ≥0) {a b : ℝ→ℝ} (ha : BoundedSmooth a) (hb : BoundedSmooth b) :
    heat σ (a-b)=heat σ a-heat σ b := by
  obtain ⟨A,hA⟩:=ha.norm_bound
  obtain ⟨B,hB⟩:=hb.norm_bound
  funext x
  change (∫ z,a (x+z)-b (x+z) ∂gaussianReal 0 σ)=_
  exact integral_sub
    (GaussianSmooth.integrable_translate (gaussianReal 0 σ) ha.smooth.continuous hA x)
    (GaussianSmooth.integrable_translate (gaussianReal 0 σ) hb.smooth.continuous hB x)

theorem heat_band {a : ℝ→ℝ} (ha : BoundedSmooth a) (σ : ℝ≥0) (j : ℕ) :
    heat σ (ScalarHeatBands.band a (j+1))=
      heat (σ+ScalarHeatBands.variance (j+1)) a-heat (σ+ScalarHeatBands.variance j) a := by
  change heat σ (ScalarHeatBands.smooth a (j+1)-ScalarHeatBands.smooth a j)=_
  rw [heat_sub σ (ScalarHeatBands.smooth_boundedSmooth ha (j+1)) (ScalarHeatBands.smooth_boundedSmooth ha j)]
  obtain ⟨B,hB⟩:=ha.norm_bound
  have hb (x : ℝ) : |a x|≤B:=by simpa only [Real.norm_eq_abs] using hB x
  rw [ScalarHeatBands.smooth,ScalarHeatBands.smooth,heat_heat σ _ ha.smooth.continuous.measurable hb,
    heat_heat σ _ ha.smooth.continuous.measurable hb]

/-- Actual Gaussian-heat bands have polynomial cancellation at every
positive future variance. This is proved from the scalar heat equation;
no annular Fourier support or exponential decay is assumed. -/
theorem jet_cancellation {a : ℝ→ℝ} (ha : BoundedSmooth a) {H β : ℝ}
    (hH : 0≤H) (hβ : 0≤β) (hβ1 : β≤1)
    (hh : ∀ x y,|a x-a y|≤H*|x-y|^β) (σ : ℝ≥0) (hσ : 0<σ)
    (j n : ℕ) (x : ℝ) :
    |iteratedDeriv n (heat σ (ScalarHeatBands.band a (j+1))) x|≤
      2*H*constant β (n+1)*CompactMollifier.radius (j+1)^2*(σ:ℝ)^((β-(n:ℝ)-2)/2) := by
  rw [heat_band ha σ j,iteratedDeriv_sub
    ((heat_boundedSmooth _ ha).smooth.of_le (by simp)).contDiffAt
    ((heat_boundedSmooth _ ha).smooth.of_le (by simp)).contDiffAt]
  have hs : 0<(σ:ℝ):=by exact_mod_cast hσ
  have hl:=variance_lipschitz ha hH hβ hβ1 hs hh n x
    (v:=(σ:ℝ)+(ScalarHeatBands.variance j:ℝ))
    (w:=(σ:ℝ)+(ScalarHeatBands.variance (j+1):ℝ))
    (le_add_of_nonneg_right (ScalarHeatBands.variance j).2)
    (le_add_of_nonneg_right (ScalarHeatBands.variance (j+1)).2)
  simp only [←NNReal.coe_add,Real.toNNReal_coe] at hl
  have hrad:=ScalarDyadicBands.radius_antitone j
  have hpow:=sq_le_sq₀ (CompactMollifier.radius_pos (j+1)).le (CompactMollifier.radius_pos j).le |>.2 hrad
  have hdiff : |((σ:ℝ)+(ScalarHeatBands.variance (j+1):ℝ))-((σ:ℝ)+(ScalarHeatBands.variance j:ℝ))|≤
      4*CompactMollifier.radius (j+1)^2:=by
    change |((σ:ℝ)+CompactMollifier.radius (j+1)^2)-((σ:ℝ)+CompactMollifier.radius j^2)|≤_
    rw [add_sub_add_left_eq_sub]
    rw [abs_of_nonpos (sub_nonpos.mpr hpow),ScalarDyadicBands.radius_succ j]
    nlinarith [sq_nonneg (CompactMollifier.radius (j+1))]
  have hc : 0≤(1/2:ℝ)*H*constant β (n+1)*(σ:ℝ)^((β-(n:ℝ)-2)/2):=by
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hH) (constant_nonneg β (n+1))) (rpow_nonneg hs.le _)
  exact hl.trans ((mul_le_mul_of_nonneg_left hdiff hc).trans_eq (by ring))

end SHE.ScalarHeatBandCancellation
