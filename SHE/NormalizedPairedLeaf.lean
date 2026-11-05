module

public import SHE.PairedEndpointLeaf
public import SHE.PairedLeafCapMoments

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.NormalizedPairedLeaf
open Set MeasureTheory ProbabilityTheory Real

def source (H β χ newMean oldMean newBaseline oldBaseline : ℝ) : ℝ :=
  H^(χ/β)*|newMean-oldMean|^χ+|newBaseline-oldBaseline|^(χ/β)

def value (a : ℝ→ℝ) (H β χ newMean oldMean newBaseline oldBaseline noise : ℝ) : ℝ :=
  if source H β χ newMean oldMean newBaseline oldBaseline=0 then 0 else
    ((a (newMean+noise)-newBaseline)-(a (oldMean+noise)-oldBaseline))/
      source H β χ newMean oldMean newBaseline oldBaseline

theorem source_nonneg {H : ℝ} (hH : 0≤H) (β χ newMean oldMean newBaseline oldBaseline : ℝ) :
    0≤source H β χ newMean oldMean newBaseline oldBaseline :=
  add_nonneg (mul_nonneg (rpow_nonneg hH _) (rpow_nonneg (abs_nonneg _) _))
    (rpow_nonneg (abs_nonneg _) _)

theorem pair_bound (a : ℝ→ℝ) {H β χ : ℝ} (hH : 0≤H) (hβ : 0<β)
    (hχ : 0≤χ) (hχβ : χ≤β) (hholder : ∀z w,|a z-a w|≤H*|z-w|^β)
    (newMean oldMean newBaseline oldBaseline noise : ℝ) :
    |(a (newMean+noise)-newBaseline)-(a (oldMean+noise)-oldBaseline)|≤
      source H β χ newMean oldMean newBaseline oldBaseline*
        (|a (newMean+noise)-newBaseline|+|a (oldMean+noise)-oldBaseline|)^(1-χ/β) := by
  have hh:=PairedEndpointLeaf.bound a hH hβ hχ hχβ hholder oldMean
    (newMean-oldMean) noise oldBaseline newBaseline
  simpa only [show oldMean+(newMean-oldMean)=newMean by ring,source] using hh

/-- The source is removed BEFORE the conditional Gaussian moment, so
its actual current-state dependence remains available for outer Holder. -/
theorem value_bound (a : ℝ→ℝ) {H β χ : ℝ} (hH : 0≤H) (hβ : 0<β)
    (hχ : 0≤χ) (hχβ : χ≤β) (hholder : ∀z w,|a z-a w|≤H*|z-w|^β)
    (newMean oldMean newBaseline oldBaseline noise : ℝ) :
    |value a H β χ newMean oldMean newBaseline oldBaseline noise|≤
      (|a (newMean+noise)-newBaseline|+|a (oldMean+noise)-oldBaseline|)^(1-χ/β) := by
  have hh:=pair_bound a hH hβ hχ hχβ hholder newMean oldMean newBaseline oldBaseline noise
  unfold value
  split_ifs with hs
  · simp only [abs_zero]
    exact rpow_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _)) _
  · have hpos : 0<source H β χ newMean oldMean newBaseline oldBaseline :=
      lt_of_le_of_ne (source_nonneg hH _ _ _ _ _ _) (Ne.symm hs)
    rw [abs_div,abs_of_pos hpos]
    exact (div_le_iff₀ hpos).mpr (by simpa only [mul_comm] using hh)

theorem factorization (a : ℝ→ℝ) {H β χ : ℝ} (hH : 0≤H) (hβ : 0<β)
    (hχ : 0≤χ) (hχβ : χ≤β) (hholder : ∀z w,|a z-a w|≤H*|z-w|^β)
    (newMean oldMean newBaseline oldBaseline noise : ℝ) :
    source H β χ newMean oldMean newBaseline oldBaseline*
      value a H β χ newMean oldMean newBaseline oldBaseline noise=
        (a (newMean+noise)-newBaseline)-(a (oldMean+noise)-oldBaseline) := by
  unfold value
  split_ifs with hs
  · have hh:=pair_bound a hH hβ hχ hχβ hholder newMean oldMean newBaseline oldBaseline noise
    rw [hs,zero_mul] at hh
    have hz:=abs_eq_zero.mp (le_antisymm hh (abs_nonneg _))
    simp only [mul_zero,hz]
  · exact mul_div_cancel₀ _ hs

/-- A true endpoint-normalized slot has the complementary rough age
power, with only affine dependence on both endpoint offset budgets.
Neither endpoint cap is imposed at an inconsistent interpolated mean. -/
theorem even_moment {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (noise : Ω→ℝ) (hn : Measurable noise) (a : ℝ→ℝ) (ha : Measurable a)
    {H β χ : ℝ} (hH : 0≤H) (hβ : 0<β) (hχ : 0≤χ) (hχβ : χ≤β)
    (hholder : ∀z w,|a z-a w|≤H*|z-w|^β)
    (newMean oldMean newBaseline oldBaseline : ℝ) (p : ℕ)
    {C0 C1 S : ℝ} (hC0 : 0≤C0) (hC1 : 0≤C1) (hS : 0≤S)
    (hOld : Integrable (fun ω=>|a (oldMean+noise ω)-oldBaseline|^(2*p)) μ)
    (hNew : Integrable (fun ω=>|a (newMean+noise ω)-newBaseline|^(2*p)) μ)
    (hbOld : (∫ ω,|a (oldMean+noise ω)-oldBaseline|^(2*p) ∂μ)≤C0*S^(2*p))
    (hbNew : (∫ ω,|a (newMean+noise ω)-newBaseline|^(2*p) ∂μ)≤C1*S^(2*p)) :
    Integrable (fun ω=>|value a H β χ newMean oldMean newBaseline oldBaseline (noise ω)|^(2*p)) μ ∧
      (∫ ω,|value a H β χ newMean oldMean newBaseline oldBaseline (noise ω)|^(2*p) ∂μ)≤
        (1+(2:ℝ)^(2*p-1)*(C0+C1))*(S^(1-χ/β))^(2*p) := by
  have hpow0 : 0≤1-χ/β:=sub_nonneg.mpr ((div_le_one hβ).mpr hχβ)
  have hpow1 : 1-χ/β≤1:=by linarith [div_nonneg hχ hβ.le]
  let f:=fun ω=>a (oldMean+noise ω)-oldBaseline
  let g:=fun ω=>a (newMean+noise ω)-newBaseline
  have hf : Measurable f:=(ha.comp (measurable_const.add hn)).sub_const _
  have hg : Measurable g:=(ha.comp (measurable_const.add hn)).sub_const _
  have hh:=PairedLeafCapMoments.fractional_even_moment μ f g hf hg p hpow0 hpow1 hC0 hC1 hS
    hOld hNew hbOld hbNew
  have hm : Measurable (fun ω=>value a H β χ newMean oldMean newBaseline oldBaseline (noise ω)) := by
    unfold value
    split_ifs <;> fun_prop
  have hpoint (ω : Ω) : |value a H β χ newMean oldMean newBaseline oldBaseline (noise ω)|^(2*p)≤
      ((|f ω|+|g ω|)^(1-χ/β))^(2*p) := by
    apply pow_le_pow_left₀ (abs_nonneg _)
    convert! value_bound a hH hβ hχ hχβ hholder newMean oldMean newBaseline oldBaseline (noise ω) using 1
    dsimp [f,g]
    rw [add_comm]
  have hi : Integrable (fun ω=>|value a H β χ newMean oldMean newBaseline oldBaseline (noise ω)|^(2*p)) μ :=
    hh.1.mono' ((continuous_abs.measurable.comp hm).pow_const (2*p)).aestronglyMeasurable
    (ae_of_all _ (fun ω=>by
      rw [Real.norm_of_nonneg (pow_nonneg (abs_nonneg _) _)]
      exact hpoint ω))
  exact ⟨hi,(integral_mono hi hh.1 hpoint).trans hh.2⟩

end SHE.NormalizedPairedLeaf
