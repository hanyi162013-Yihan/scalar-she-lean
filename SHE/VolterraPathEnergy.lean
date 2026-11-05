module

public import SHE.IntegralEnergy

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.VolterraPathEnergy
open MeasureTheory Set LowBands VolterraPath
open scoped NNReal ENNReal
local instance volterraPathEnergy_pFinite : Fact ((2:ENNReal) ≠ ⊤) := ⟨by simp⟩

theorem continuous_memLp_interval {E : Type*} [NormedAddCommGroup E]
    (F : ℝ → E) (hF : Continuous F) (t : ℝ≥0) :
    MemLp F 2 ((volume:Measure ℝ).restrict (Icc 0 (t:ℝ))) := by
  obtain ⟨C,hC⟩ := (isCompact_Icc : IsCompact (Icc (0:ℝ) (t:ℝ))).bddAbove_image hF.norm.continuousOn
  apply MemLp.of_bound hF.aestronglyMeasurable C
  filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
  exact hC (mem_image_of_mem (fun r => ‖F r‖) hr)

/-- The actual deterministic heat convolution has the causal L² energy
bound, uniform in every nonnegative damping parameter. -/
theorem value_energy {Λ : ℝ} (hΛ : 0 ≤ Λ) (U : ℝ≥0 → StateL2)
    (hU : Continuous U) (t : ℝ≥0) :
    ‖value Λ U t‖^2 ≤ (t:ℝ)*(∫ r in Icc (0:ℝ) (t:ℝ),‖U r.toNNReal‖^2) := by
  let F : ℝ → StateL2 := fun r => Real.exp (-Λ*((t:ℝ)-r)) •
    RealHeat.realHeat ((t:ℝ)-r) (U r.toNNReal)
  have hparam : Continuous (fun r : ℝ => ((t:ℝ)-r,U r.toNNReal)) := by fun_prop
  have hheat := RealHeat.continuous_realHeat_action.comp hparam
  change Continuous (fun r : ℝ => RealHeat.realHeat ((t:ℝ)-r) (U r.toNNReal)) at hheat
  have hscalar : Continuous (fun r : ℝ => Real.exp (-Λ*((t:ℝ)-r))) := by fun_prop
  have hF : Continuous F := hscalar.smul hheat
  have hf2 := continuous_memLp_interval F hF t
  have hu2 := continuous_memLp_interval (fun r : ℝ => U r.toNNReal) (by fun_prop) t
  have hnorm (r : ℝ) (hr : r ∈ Icc (0:ℝ) (t:ℝ)) : ‖F r‖ ≤ ‖U r.toNNReal‖ := by
    have he : Real.exp (-Λ*((t:ℝ)-r)) ≤ 1 := Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hΛ) (sub_nonneg.mpr hr.2))
    change ‖Real.exp (-Λ*((t:ℝ)-r)) • RealHeat.realHeat ((t:ℝ)-r) (U r.toNNReal)‖ ≤ _
    rw [norm_smul,Real.norm_of_nonneg (Real.exp_pos _).le]
    exact (mul_le_of_le_one_left (norm_nonneg _) he).trans
      (RealHeat.realHeat_contraction _ _)
  have hint : (∫ r in Icc (0:ℝ) (t:ℝ),‖F r‖^2) ≤
      ∫ r in Icc (0:ℝ) (t:ℝ),‖U r.toNNReal‖^2 := by
    apply integral_mono_ae hf2.norm.integrable_sq hu2.norm.integrable_sq
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    exact pow_le_pow_left₀ (norm_nonneg _) (hnorm r hr) 2
  have hCS := IntegralEnergy.norm_integral_sq ((volume:Measure ℝ).restrict (Icc 0 (t:ℝ))) F hf2
  have hmass : ((volume:Measure ℝ).restrict (Icc 0 (t:ℝ))).real univ=(t:ℝ) := by
    simp [Measure.real,Real.volume_Icc,t.2]
  rw [hmass] at hCS
  have hval : value Λ U t=∫ r in Icc (0:ℝ) (t:ℝ),F r := by
    change (∫ r in (0:ℝ)..(t:ℝ),F r)=∫ r in Icc (0:ℝ) (t:ℝ),F r
    have hi : (∫ r in (0:ℝ)..(t:ℝ),F r)=∫ r in Ioc (0:ℝ) (t:ℝ),F r :=
      intervalIntegral.integral_of_le t.2
    have hj : (∫ r in Icc (0:ℝ) (t:ℝ),F r)=∫ r in Ioc (0:ℝ) (t:ℝ),F r :=
      integral_Icc_eq_integral_Ioc
    exact hi.trans hj.symm
  rw [hval]
  exact hCS.trans (mul_le_mul_of_nonneg_left hint t.2)

end SHE.VolterraPathEnergy
