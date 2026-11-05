module

public import SHE.LineGaussianLocal

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.GaussianPeriodizedLocal
open Set MeasureTheory AddCircle HeatLine HeatPeriodization FourierHeatLine LineGaussianLocal TopologicalSpace HeatCluster
local instance gaussianPeriodizedLocal_periodPos : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩

theorem heatEntire_real (t r : ℝ) : heatEntire t 0 (r:ℂ)=(gaussian t r:ℂ) := by
  simp only [heatEntire,Complex.ofReal_zero,sub_zero,gaussian]
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  rfl

theorem heatEntire_norm (t r : ℝ) : ‖heatEntire t 0 (r:ℂ)‖=gaussian t r := by
  rw [heatEntire_real,Complex.norm_real,Real.norm_eq_abs]
  exact abs_of_pos (Real.exp_pos _)

theorem gaussian_summable {t : ℝ} (ht : 0 < t) (r : ℝ) :
    Summable (fun n : ℤ => gaussian t (r+(n:ℝ))) := by
  let K : Compacts ℝ := ⟨{r},isCompact_singleton⟩
  let F : ℤ → C(K,ℂ) := fun n =>
    ((⟨fun x : ℝ => heatEntire t 0 (x:ℂ),continuous_heat_span
      (fun _ : Fin 1 => t) (fun _ => 0) (heatEntire t 0) (HeatMarkov.singleHeat_span t)⟩ : C(ℝ,ℂ)).comp
      (ContinuousMap.addRight (n:ℝ))).restrict K
  have hs : Summable (fun n => ‖F n‖) :=
    heat_span_locally_summable_translates (fun _ : Fin 1 => t) (fun _ => 0) (fun _ => ht)
      (heatEntire t 0) (HeatMarkov.singleHeat_span t) K
  have hnonneg : ∀ n : ℤ,0 ≤ gaussian t (r+(n:ℝ)) := fun _ => (Real.exp_pos _).le
  apply Summable.of_nonneg_of_le hnonneg _ hs
  intro n
  have hb := (F n).norm_coe_le_norm (⟨r,by change r ∈ ({r}:Set ℝ); simp⟩ : K)
  change ‖heatEntire t 0 ((r+(n:ℝ):ℝ):ℂ)‖ ≤ ‖F n‖ at hb
  simpa only [heatEntire_norm] using hb

/-- Literal Gaussian series formula for the actual normalized unit-circle
heat kernel. -/
theorem kernel_coe_real {t : ℝ} (ht : 0 < t) (r : ℝ) :
    HeatMarkov.kernel t ht (r:AddCircle (1:ℝ))=
      (((heatMass t)⁻¹ * ∑' n : ℤ,gaussian t (r+(n:ℝ)) : ℝ):ℂ) := by
  change (heatMass t:ℂ)⁻¹ * circlePeriodize (fun _ : Fin 1 => t) (fun _ => 0)
    (fun _ => ht) (heatEntire t 0) (HeatMarkov.singleHeat_span t) (r:AddCircle (1:ℝ))=_
  rw [circlePeriodize_coe]
  unfold periodize
  simp_rw [heatEntire_real]
  rw [← Complex.ofReal_tsum,← Complex.ofReal_inv,← Complex.ofReal_mul]

theorem kernel_coe_norm {t : ℝ} (ht : 0 < t) (r : ℝ) :
    ‖HeatMarkov.kernel t ht (r:AddCircle (1:ℝ))‖=
      (heatMass t)⁻¹ * ∑' n : ℤ,gaussian t (r+(n:ℝ)) := by
  rw [kernel_coe_real ht r,Complex.norm_real,Real.norm_eq_abs]
  apply abs_of_nonneg
  exact mul_nonneg (inv_nonneg.mpr (heatMass_pos ht).le) (tsum_nonneg (fun _ => (Real.exp_pos _).le))

theorem mass_scale_eight {t : ℝ} (ht : 0 < t) : heatMass (8*t)=Real.sqrt 8*heatMass t := by
  unfold heatMass
  rw [← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 8)]
  congr 1
  ring

/-- Periodization preserves the enlarged-Gaussian local Lipschitz
envelope, including its spatial localization and correct time scale. -/
theorem kernel_difference_bound {t a x y : ℝ} (ht : 0 < t)
    (hx : |x-a| ≤ Real.sqrt t) (hy : |y-a| ≤ Real.sqrt t) :
    ‖HeatMarkov.kernel t ht (x:AddCircle (1:ℝ))-
      HeatMarkov.kernel t ht (y:AddCircle (1:ℝ))‖ ≤
      ((Real.sqrt 8*Real.exp (1/4:ℝ)/Real.sqrt t)*
        ‖HeatMarkov.kernel (8*t) (by positivity) (a:AddCircle (1:ℝ))‖)*|x-y| := by
  have ht8 : 0 < 8*t := by positivity
  have hsx := gaussian_summable ht x
  have hsy := gaussian_summable ht y
  have hsa := gaussian_summable ht8 a
  have hdiff := hsx.sub hsy
  have hbound (n : ℤ) :
      ‖gaussian t (x+(n:ℝ))-gaussian t (y+(n:ℝ))‖ ≤
        (Real.exp (1/4:ℝ)/Real.sqrt t)*gaussian (8*t) (a+(n:ℝ))*|x-y| := by
    have hh := difference_bound (a := a+(n:ℝ)) (x := x+(n:ℝ)) (y := y+(n:ℝ)) ht
      (by simpa only [show x+(n:ℝ)-(a+(n:ℝ))=x-a by ring] using hx)
      (by simpa only [show y+(n:ℝ)-(a+(n:ℝ))=y-a by ring] using hy)
    simpa only [Real.norm_eq_abs,gaussian,
      show x+(n:ℝ)-(y+(n:ℝ))=x-y by ring,
      show 4*(8*t)=32*t by ring] using hh
  have hsum : ‖(∑' n : ℤ,gaussian t (x+(n:ℝ)))-(∑' n : ℤ,gaussian t (y+(n:ℝ)))‖ ≤
      (Real.exp (1/4:ℝ)/Real.sqrt t)*(∑' n : ℤ,gaussian (8*t) (a+(n:ℝ)))*|x-y| := by
    rw [← hsx.tsum_sub hsy]
    calc
      _ ≤ ∑' n : ℤ,‖gaussian t (x+(n:ℝ))-gaussian t (y+(n:ℝ))‖ := norm_tsum_le_tsum_norm hdiff.norm
      _ ≤ ∑' n : ℤ,(Real.exp (1/4:ℝ)/Real.sqrt t)*gaussian (8*t) (a+(n:ℝ))*|x-y| :=
        hdiff.norm.tsum_le_tsum hbound ((hsa.mul_left _).mul_right _)
      _ = _ := by rw [tsum_mul_right,tsum_mul_left]
  rw [kernel_coe_real ht x,kernel_coe_real ht y,← Complex.ofReal_sub,Complex.norm_real]
  rw [← mul_sub]
  change ‖(heatMass t)⁻¹*((∑' n : ℤ,gaussian t (x+(n:ℝ)))-
    (∑' n : ℤ,gaussian t (y+(n:ℝ))))‖ ≤ _
  have hmassnorm : ‖(heatMass t)⁻¹‖=(heatMass t)⁻¹ :=
    Real.norm_of_nonneg (inv_nonneg.mpr (heatMass_pos ht).le)
  rw [norm_mul,hmassnorm,kernel_coe_norm ht8 a]
  have hm := mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr (heatMass_pos ht).le)
  have he : (heatMass t)⁻¹*((Real.exp (1/4:ℝ)/Real.sqrt t)*
      (∑' n : ℤ,gaussian (8*t) (a+(n:ℝ)))*|x-y|)=
      (Real.sqrt 8*Real.exp (1/4:ℝ)/Real.sqrt t)*
        ((heatMass (8*t))⁻¹*(∑' n : ℤ,gaussian (8*t) (a+(n:ℝ))))*|x-y| := by
    rw [mass_scale_eight ht]
    field_simp
  exact hm.trans_eq he

end SHE.GaussianPeriodizedLocal
