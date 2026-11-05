module

public import SHE.NativeRandomKernel
public import SHE.NodeKernelLocal

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.NativeRootPartition
open Set Filter MeasureTheory ProbabilityTheory AddCircle Real StoppedFourier
open scoped BigOperators ENNReal
local instance nativeRootPartition_nativePositive : Fact (0 < 2*π) := ⟨by positivity⟩

variable {I Ω : Type*} [Fintype I] [Nonempty I] [MeasurableSpace Ω]

def mass (t : I → ℝ) (a : I → HeatCircle → HeatCircle) (i : I)
    (p : HeatCircle × HeatCircle) : ℝ := ‖ProfileVariance.heatPhysical (8*t i) (a i p.1) p.2‖

def total (t : I → ℝ) (a : I → HeatCircle → HeatCircle) (p : HeatCircle × HeatCircle) : ℝ :=
  ∑ i, mass t a i p

def weight (t : I → ℝ) (a : I → HeatCircle → HeatCircle) (i : I)
    (p : HeatCircle × HeatCircle) : ℝ := mass t a i p / total t a p

theorem mass_pos (t : I → ℝ) (a : I → HeatCircle → HeatCircle)
    (ht : ∀ i, 0 < t i) (i : I) (p : HeatCircle × HeatCircle) : 0 < mass t a i p := by
  rw [mass,← NativeHeatSpan.kernel_eq_physical (mul_pos (by norm_num) (ht i))]
  exact NodeKernelLocal.kernel_norm_pos (NativeHeatSpan.clock_pos (mul_pos (by norm_num) (ht i))) _

theorem total_pos (t : I → ℝ) (a : I → HeatCircle → HeatCircle)
    (ht : ∀ i, 0 < t i) (p : HeatCircle × HeatCircle) : 0 < total t a p := by
  classical
  exact Finset.sum_pos (fun i _ => mass_pos t a ht i p) Finset.univ_nonempty

theorem weight_nonneg (t : I → ℝ) (a : I → HeatCircle → HeatCircle)
    (ht : ∀ i, 0 < t i) (i : I) (p : HeatCircle × HeatCircle) : 0 ≤ weight t a i p :=
  div_nonneg (mass_pos t a ht i p).le (total_pos t a ht p).le

theorem weight_le_one (t : I → ℝ) (a : I → HeatCircle → HeatCircle)
    (ht : ∀ i, 0 < t i) (i : I) (p : HeatCircle × HeatCircle) : weight t a i p ≤ 1 := by
  classical
  apply (div_le_one (total_pos t a ht p)).mpr
  exact Finset.single_le_sum (fun j _ => (mass_pos t a ht j p).le) (Finset.mem_univ i)

theorem weight_sum (t : I → ℝ) (a : I → HeatCircle → HeatCircle)
    (ht : ∀ i, 0 < t i) (p : HeatCircle × HeatCircle) : ∑ i, weight t a i p = 1 := by
  simp only [weight,← Finset.sum_div]
  exact div_self (total_pos t a ht p).ne'

theorem weight_measurable (t : I → ℝ) (a : I → HeatCircle → HeatCircle)
    (ht : ∀ i, 0 < t i) (ha : ∀ i, Measurable (a i)) (i : I) : Measurable (weight t a i) := by
  have hm (j : I) : Measurable (mass t a j) :=
    ((NativeHeatSpan.continuous_heatPhysical_space (mul_pos (by norm_num) (ht j))).measurable.comp
      ((ha j).comp measurable_fst |>.prodMk measurable_snd)).norm
  exact (hm i).div (Finset.measurable_sum Finset.univ (fun j _ => hm j))

/-- A deterministic partition of the actual random field among its
original-root envelopes. Every component retains all original randomness. -/
def component (t : I → ℝ) (a : I → HeatCircle → HeatCircle)
    (F : Ω × (HeatCircle × HeatCircle) → ℂ) (i : I)
    (p : Ω × (HeatCircle × HeatCircle)) : ℂ := (weight t a i p.2 : ℂ)*F p

theorem component_measurable (t : I → ℝ) (a : I → HeatCircle → HeatCircle)
    (ht : ∀ i, 0 < t i) (ha : ∀ i, Measurable (a i))
    {F : Ω × (HeatCircle × HeatCircle) → ℂ} (hF : Measurable F) (i : I) :
    Measurable (component t a F i) :=
  (Complex.continuous_ofReal.measurable.comp ((weight_measurable t a ht ha i).comp measurable_snd)).mul hF

theorem component_bound (t : I → ℝ) (a : I → HeatCircle → HeatCircle)
    (ht : ∀ i, 0 < t i) {F : Ω × (HeatCircle × HeatCircle) → ℂ}
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ ω y x, ‖F (ω,(y,x))‖ ≤ B)
    (i : I) (ω : Ω) (y x : HeatCircle) : ‖component t a F i (ω,(y,x))‖ ≤ B := by
  rw [component,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (weight_nonneg t a ht i (y,x))]
  exact (mul_le_mul_of_nonneg_left (hb ω y x) (weight_nonneg t a ht i (y,x))).trans
    ((mul_le_mul_of_nonneg_right (weight_le_one t a ht i (y,x)) hB).trans_eq (one_mul B))

theorem component_sum (t : I → ℝ) (a : I → HeatCircle → HeatCircle)
    (ht : ∀ i, 0 < t i) (F : Ω × (HeatCircle × HeatCircle) → ℂ)
    (p : Ω × (HeatCircle × HeatCircle)) : ∑ i, component t a F i p=F p := by
  simp only [component,← Finset.sum_mul,← Complex.ofReal_sum,weight_sum t a ht,Complex.ofReal_one,one_mul]

/-- Each actual component has its own sharp RMS envelope at its original
age and center; neither independence nor comparability of ages is used. -/
theorem component_rms_bound (μ : Measure Ω) [IsProbabilityMeasure μ]
    (t : I → ℝ) (a : I → HeatCircle → HeatCircle)
    (ht : ∀ i, 0 < t i)
    {F : Ω × (HeatCircle × HeatCircle) → ℂ} (hF : Measurable F)
    {B K : ℝ} (hb : ∀ ω y x, ‖F (ω,(y,x))‖ ≤ B)
    (hsharp : ∀ y x, ProfileL2.normTwo μ (fun ω => ‖F (ω,(y,x))‖) ≤ K*total t a (y,x))
    (i : I) (y x : HeatCircle) :
    ProfileL2.normTwo μ (fun ω => ‖component t a F i (ω,(y,x))‖) ≤ K*mass t a i (y,x) := by
  have hm : MemLp (fun ω => ‖F (ω,(y,x))‖) 2 μ :=
    (MemLp.of_bound (hF.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable B
      (ae_of_all _ (fun ω => hb ω y x))).norm
  simp only [component,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (weight_nonneg t a ht i (y,x))]
  rw [ProfileL2.normTwo_const_mul hm,abs_of_nonneg (weight_nonneg t a ht i (y,x))]
  calc
    _ ≤ weight t a i (y,x)*(K*total t a (y,x)) :=
      mul_le_mul_of_nonneg_left (hsharp y x) (weight_nonneg t a ht i (y,x))
    _ = _ := by
      unfold weight
      field_simp [(total_pos t a ht (y,x)).ne']

end SHE.NativeRootPartition
