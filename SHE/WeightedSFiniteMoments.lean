module

public import SHE.WeightedSpatialMoments
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section

namespace SHE.WeightedSFiniteMoments
open Set Filter MeasureTheory ProbabilityTheory Real
open scoped Topology
variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
variable (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure X) [SFinite ν]

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


/-- At zero envelope the actual random integrand vanishes on one
genuine product event. No pointwise-in-omega bound or independence is
inferred from separate expectations. -/
theorem zero_weight_vanishes (F : Ω×X→ℝ) (hF : Measurable F)
    (H : X→ℝ) (hHm : Measurable H) (b : ℕ) (hb : 0<b) (C : ℝ)
    (hi : ∀ᵐ x ∂ν,Integrable (fun ω=>|F (ω,x)|^(2*b)) μ)
    (hbound : ∀ᵐ x ∂ν,(∫ ω,|F (ω,x)|^(2*b) ∂μ)≤C*(H x)^(2*b)) :
    ∀ᵐ ω ∂μ,∀ᵐ x ∂ν,H x=0 → F (ω,x)=0 := by
  have hx : ∀ᵐ x ∂ν,∀ᵐ ω ∂μ,H x=0 → F (ω,x)=0 := by
    filter_upwards [hi,hbound] with x hix hbx
    by_cases hz : H x=0
    · have hzero : (∫ ω,|F (ω,x)|^(2*b) ∂μ)=0 := by
        apply le_antisymm
        · simpa only [hz,zero_pow (by omega : 2*b≠0),mul_zero] using hbx
        · exact integral_nonneg (fun _=>pow_nonneg (abs_nonneg _) _)
      have ha := (integral_eq_zero_iff_of_nonneg (fun _=>pow_nonneg (abs_nonneg _) _) hix).mp hzero
      filter_upwards [ha] with ω hω _
      exact abs_eq_zero.mp (eq_zero_of_pow_eq_zero hω)
    · exact ae_of_all _ (fun _ h=>False.elim (hz h))
  have hm : MeasurableSet {z : Ω×X | H z.2=0 → F z=0} := by
    have he : {z : Ω×X | H z.2=0 → F z=0}=
        ({z : Ω×X | H z.2=0}ᶜ∪{z : Ω×X | F z=0}) := by
      ext z
      simp only [Set.mem_setOf_eq,Set.mem_union,Set.mem_compl_iff,imp_iff_not_or]
    rw [he]
    simpa only [Function.comp_def] using
      (measurableSet_eq_fun (hHm.comp measurable_snd) measurable_const).compl.union
        (measurableSet_eq_fun hF measurable_const)
  exact (Measure.ae_ae_comm hm).mpr hx

/-- Density averaging for a possibly infinite physical history measure.
Only the true L1 envelope mass enters the estimate. Its integrability
and the pointwise moment hypotheses suffice to prove integrability of
the random average, even where the envelope vanishes. -/
theorem nonnegative_envelope (F : Ω×X→ℝ) (hF : Measurable F)
    (H : X→ℝ) (hHm : Measurable H) (hHi : Integrable H ν) (hH : ∀ x,0≤H x)
    (b : ℕ) (hb : 0<b) (C : ℝ) (hC : 0≤C)
    (hi : ∀ᵐ x ∂ν,Integrable (fun ω=>|F (ω,x)|^(2*b)) μ)
    (hbound : ∀ᵐ x ∂ν,(∫ ω,|F (ω,x)|^(2*b) ∂μ)≤C*(H x)^(2*b)) :
    Integrable (fun ω=>|∫ x,F (ω,x) ∂ν|^(2*b)) μ ∧
      (∫ ω,|∫ x,F (ω,x) ∂ν|^(2*b) ∂μ)≤C*(∫ x,H x ∂ν)^(2*b) := by
  have hzero := zero_weight_vanishes μ ν F hF H hHm b hb C hi hbound
  by_cases hMass : 0<∫ x,H x ∂ν
  · let s : Set X := {x | 0<H x}
    have hs : MeasurableSet s := measurableSet_lt measurable_const hHm
    let J : X→ℝ := fun x=>if x∈s then H x else 1
    have hJ : Measurable J := Measurable.ite hs hHm measurable_const
    have hJpos (x : X) : 0<J x := by
      by_cases hx : x∈s
      · have hxpos : 0<H x := hx
        simpa only [J,ite_eq_left hx] using hxpos
      · simp only [J,ite_eq_right hx,zero_lt_one]
    have heJ : J=ᵐ[ν.restrict s] H := by
      filter_upwards [ae_restrict_mem hs] with x hx
      exact ite_eq_left hx
    have hJi : Integrable J (ν.restrict s) := hHi.restrict.congr heJ.symm
    have heH : s.indicator H=H := by
      funext x
      by_cases hx : x∈s
      · exact indicator_of_mem hx H
      · have h0 : H x=0 := le_antisymm (le_of_not_gt hx) (hH x)
        simp only [indicator_of_notMem hx,h0]
    have hmass : (∫ x,J x ∂ν.restrict s)=∫ x,H x ∂ν := by
      rw [integral_congr_ae heJ,←integral_indicator hs,heH]
    have hbi : ∀ᵐ x ∂ν.restrict s,(∫ ω,|F (ω,x)|^(2*b) ∂μ)≤C*(J x)^(2*b) := by
      filter_upwards [ae_restrict_of_ae hbound,heJ] with x hx he
      simpa only [he] using hx
    have hh := positive_envelope μ (ν.restrict s) F hF J hJ hJi hJpos
      (by rw [hmass];exact hMass) b hb C hC (ae_restrict_of_ae hi) hbi
    have heAvg : (fun ω=>∫ x,F (ω,x) ∂ν)=ᵐ[μ] fun ω=>∫ x,F (ω,x) ∂ν.restrict s := by
      filter_upwards [hzero] with ω hω
      have he : s.indicator (fun x=>F (ω,x))=ᵐ[ν] fun x=>F (ω,x) := by
        filter_upwards [hω] with x hx
        by_cases hsx : x∈s
        · exact indicator_of_mem hsx _
        · have h0 : H x=0 := le_antisymm (le_of_not_gt hsx) (hH x)
          simp only [indicator_of_notMem hsx,hx h0]
      rw [←integral_congr_ae he,integral_indicator hs]
    have hp := heAvg.fun_comp (fun z : ℝ=>|z|^(2*b))
    exact ⟨hh.1.congr hp.symm,(integral_congr_ae hp).trans_le (by simpa only [hmass,Function.comp_def] using hh.2)⟩
  · have hmass : (∫ x,H x ∂ν)=0 := le_antisymm (le_of_not_gt hMass) (integral_nonneg hH)
    have hzH := (integral_eq_zero_iff_of_nonneg hH hHi).mp hmass
    have hzAvg : (fun ω=>∫ x,F (ω,x) ∂ν)=ᵐ[μ] fun _=>0 := by
      filter_upwards [hzero] with ω hω
      have he : (fun x=>F (ω,x))=ᵐ[ν] fun _=>0 := by
        filter_upwards [hω,hzH] with x hx he
        exact hx he
      rw [integral_congr_ae he,integral_zero]
    have hp : (fun ω=>|∫ x,F (ω,x) ∂ν|^(2*b))=ᵐ[μ] fun _=>0 := by
      filter_upwards [hzAvg] with ω hω
      simp only [hω,abs_zero,zero_pow (by omega : 2*b≠0)]
    refine ⟨(integrable_const (0:ℝ)).congr hp.symm,?_⟩
    rw [integral_congr_ae hp,integral_zero,hmass,zero_pow (by omega : 2*b≠0),mul_zero]

end SHE.WeightedSFiniteMoments
