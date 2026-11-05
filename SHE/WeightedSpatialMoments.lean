module

public import SHE.UniformFiberMoments
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section

namespace SHE.WeightedSpatialMoments
open Set Filter MeasureTheory ProbabilityTheory Real
open scoped Topology
variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
variable (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure X) [IsProbabilityMeasure ν]

/-- Normalize the spatial envelope itself into a probability density.
This gives a moment of the spatial average at the power of its L1 mass,
with no spatial supremum or independence assumption. -/
theorem positive_envelope (F : Ω × X → ℝ) (hF : Measurable F)
    (H : X → ℝ) (hHm : Measurable H) (hHi : Integrable H ν)
    (hH : ∀ x, 0 < H x) (hMass : 0 < ∫ x,H x ∂ν)
    (b : ℕ) (hb : 0 < b) (C : ℝ) (hC : 0 ≤ C)
    (hi : ∀ᵐ x ∂ν, Integrable (fun ω => |F (ω,x)|^(2*b)) μ)
    (hbound : ∀ᵐ x ∂ν, (∫ ω,|F (ω,x)|^(2*b) ∂μ) ≤ C*(H x)^(2*b)) :
    Integrable (fun ω => |∫ x,F (ω,x) ∂ν|^(2*b)) μ ∧
      (∫ ω,|∫ x,F (ω,x) ∂ν|^(2*b) ∂μ) ≤ C*(∫ x,H x ∂ν)^(2*b) := by
  let D := ∫ x,H x ∂ν
  have hD : 0 < D := hMass
  let density := fun x => ENNReal.ofReal (H x/D)
  have hd : Measurable density := ENNReal.measurable_ofReal.comp (hHm.div_const D)
  let η := ν.withDensity density
  have hm : η univ=1 := by
    rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
    rw [←ofReal_integral_eq_lintegral_ofReal (hHi.div_const D)
      (ae_of_all _ (fun x => (div_pos (hH x) hD).le)),integral_div]
    simp only [D,div_self hD.ne',ENNReal.ofReal_one]
  letI : IsProbabilityMeasure η := ⟨hm⟩
  let A := fun z : Ω × X => F z/H z.2
  have hA : Measurable A := hF.div (hHm.comp measurable_snd)
  have hiA : ∀ᵐ x ∂η, Integrable (fun ω => |A (ω,x)|^(2*b)) μ := by
    filter_upwards [(withDensity_absolutelyContinuous ν density).ae_le hi] with x hx
    simpa only [A,abs_div,div_pow,abs_of_pos (hH x)] using hx.div_const ((H x)^(2*b))
  have hbA : ∀ᵐ x ∂η, (∫ ω,|A (ω,x)|^(2*b) ∂μ) ≤ C := by
    filter_upwards [(withDensity_absolutelyContinuous ν density).ae_le hbound] with x hx
    simp only [A,abs_div,div_pow,abs_of_pos (hH x),integral_div]
    exact (div_le_iff₀ (pow_pos (hH x) _)).mpr hx
  have hjoint : Integrable (fun z : Ω × X => |A z|^(2*b)) (μ.prod η) := by
    simpa only [one_pow,one_mul] using weighted_kernel_moment_integrable μ η A (fun _ => 1)
      (2*b) C hC hA measurable_const (by simpa using (integrable_const (1:ℝ) : Integrable (fun _ : X => (1:ℝ)) η)) hiA hbA
  have hjointBound : (∫ z : Ω × X,|A z|^(2*b) ∂μ.prod η) ≤ C := by
    simpa only [one_pow,one_mul,integral_const,probReal_univ,mul_one,smul_eq_mul] using
      weighted_kernel_moment_bound μ η A (fun _ => 1) (2*b) C hC hA
        measurable_const (by simpa using (integrable_const (1:ℝ) : Integrable (fun _ : X => (1:ℝ)) η)) hiA hbA
  have hi1 := integrable_norm_pow_of_le hA.aestronglyMeasurable (by omega : 1 ≤ 2*b)
    (by simpa only [Real.norm_eq_abs] using hjoint)
  have hiA1 : Integrable A (μ.prod η) := (integrable_norm_iff hA.aestronglyMeasurable).mp
    (by simpa only [pow_one] using hi1)
  have havg := UniformFiberMoments.average_even_moment μ η A hiA1 b hjoint
  have hid (ω : Ω) : (∫ x,A (ω,x) ∂η)=(∫ x,F (ω,x) ∂ν)/D := by
    rw [integral_withDensity_eq_integral_toReal_smul hd
      (ae_of_all _ (fun x => ENNReal.ofReal_lt_top))]
    have he (x : X) : (density x).toReal*A (ω,x)=F (ω,x)/D := by
      dsimp only [density,A]
      rw [ENNReal.toReal_ofReal (div_pos (hH x) hD).le]
      field_simp [(hH x).ne',hD.ne']
    simp_rw [smul_eq_mul,he]
    exact integral_div _ _
  have hp (ω : Ω) : |∫ x,F (ω,x) ∂ν|^(2*b)=D^(2*b)*|∫ x,A (ω,x) ∂η|^(2*b) := by
    rw [hid,abs_div,div_pow,abs_of_pos hD]
    field_simp [hD.ne']
  have hiF : Integrable (fun ω => |∫ x,F (ω,x) ∂ν|^(2*b)) μ := by
    simpa only [←hp] using havg.1.const_mul (D^(2*b))
  refine ⟨hiF,?_⟩
  simp_rw [hp]
  rw [integral_const_mul]
  have hh := mul_le_mul_of_nonneg_left (havg.2.trans hjointBound) (pow_nonneg hD.le (2*b))
  simpa only [mul_comm C] using hh


/-- Nonnegative envelopes, including vanishing spatial or deterministic
clips, follow by applying the positive-density estimate to H+epsilon and
passing to zero. The old-space averaging still uses only the L1 mass. -/
theorem nonnegative_envelope (F : Ω × X → ℝ) (hF : Measurable F)
    (H : X → ℝ) (hHm : Measurable H) (hHi : Integrable H ν) (hH : ∀ x, 0 ≤ H x)
    (b : ℕ) (hb : 0 < b) (C : ℝ) (hC : 0 ≤ C)
    (hi : ∀ᵐ x ∂ν, Integrable (fun ω => |F (ω,x)|^(2*b)) μ)
    (hbound : ∀ᵐ x ∂ν, (∫ ω,|F (ω,x)|^(2*b) ∂μ) ≤ C*(H x)^(2*b)) :
    Integrable (fun ω => |∫ x,F (ω,x) ∂ν|^(2*b)) μ ∧
      (∫ ω,|∫ x,F (ω,x) ∂ν|^(2*b) ∂μ) ≤ C*(∫ x,H x ∂ν)^(2*b) := by
  have hs (e : ℝ) (he : 0 < e) :
      Integrable (fun ω => |∫ x,F (ω,x) ∂ν|^(2*b)) μ ∧
        (∫ ω,|∫ x,F (ω,x) ∂ν|^(2*b) ∂μ) ≤ C*((∫ x,H x ∂ν)+e)^(2*b) := by
    have hmass : (∫ x,H x+e ∂ν)=(∫ x,H x ∂ν)+e := by
      rw [integral_add hHi (integrable_const e)]
      simp only [integral_const,probReal_univ,smul_eq_mul,one_mul]
    have hmasspos : 0 < ∫ x,H x+e ∂ν := by
      rw [hmass]
      exact add_pos_of_nonneg_of_pos (integral_nonneg hH) he
    have hb' : ∀ᵐ x ∂ν, (∫ ω,|F (ω,x)|^(2*b) ∂μ) ≤ C*(H x+e)^(2*b) := by
      filter_upwards [hbound] with x hx
      exact hx.trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (hH x) (by linarith : H x ≤ H x+e) _) hC)
    have hh := positive_envelope μ ν F hF (fun x => H x+e) (hHm.add_const e)
      (hHi.add (integrable_const e)) (fun x => add_pos_of_nonneg_of_pos (hH x) he)
      hmasspos b hb C hC hi hb'
    simpa only [hmass] using hh
  refine ⟨(hs 1 zero_lt_one).1,?_⟩
  have ht : Tendsto (fun e : ℝ => C*((∫ x,H x ∂ν)+e)^(2*b)) (𝓝[>] (0:ℝ))
      (𝓝 (C*(∫ x,H x ∂ν)^(2*b))) := by
    have hc : ContinuousAt (fun e : ℝ => C*((∫ x,H x ∂ν)+e)^(2*b)) 0 := by fun_prop
    simpa only [add_zero] using hc.tendsto.mono_left nhdsWithin_le_nhds
  apply ge_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin] with e he
  exact (hs e he).2

end SHE.WeightedSpatialMoments
