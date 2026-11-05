module

public import SHE.PastItoInputs
public import SHE.PredictableItoRotation
public import SHE.PredictableContraction

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.PastItoAlgebra
open MeasureTheory Set PredictableL2 PastItoInputs StoppedItoInputs
open scoped NNReal ENNReal
variable {Ω C : Type*} [MeasurableSpace Ω] [NormedAddCommGroup C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) (H : ℝ≥0)

theorem eq_of_ambient_ae {u w : Process (E := C) 𝓕 μ H}
    (h : u=ᵐ[energyMeasure μ H] w) : u=w := by
  apply Lp.ext
  exact ae_eq_trim_of_measurable (predictable_le_product 𝓕)
    (Lp.stronglyMeasurable _).measurable (Lp.stronglyMeasurable _).measurable h

theorem post_add (v : ℝ≥0) (u w : Process (E := C) 𝓕 μ H) :
    post 𝓕 μ H v (u+w)=post 𝓕 μ H v u+post 𝓕 μ H v w := by
  apply eq_of_ambient_ae
  filter_upwards [post_ae 𝓕 μ H v (u+w),post_ae 𝓕 μ H v u,post_ae 𝓕 μ H v w,
    ae_eq_of_ae_eq_trim (Lp.coeFn_add u w),
    ae_eq_of_ae_eq_trim (Lp.coeFn_add (post 𝓕 μ H v u) (post 𝓕 μ H v w))] with p hp hu hw hi ho
  rw [hp,ho]
  simp only [Pi.add_apply,hu,hw]
  by_cases h : v<p.1 <;> simp only [h,ite_true,ite_false,zero_add,hi,Pi.add_apply]

theorem post_sub (v : ℝ≥0) (u w : Process (E := C) 𝓕 μ H) :
    post 𝓕 μ H v (u-w)=post 𝓕 μ H v u-post 𝓕 μ H v w := by
  apply eq_of_ambient_ae
  filter_upwards [post_ae 𝓕 μ H v (u-w),post_ae 𝓕 μ H v u,post_ae 𝓕 μ H v w,
    ae_eq_of_ae_eq_trim (Lp.coeFn_sub u w),
    ae_eq_of_ae_eq_trim (Lp.coeFn_sub (post 𝓕 μ H v u) (post 𝓕 μ H v w))] with p hp hu hw hi ho
  rw [hp,ho]
  simp only [Pi.sub_apply,hu,hw]
  by_cases h : v<p.1 <;> simp only [h,ite_true,ite_false,sub_self,hi,Pi.sub_apply]

variable [NormedSpace ℝ C]

theorem post_smul (v : ℝ≥0) (a : ℝ) (u : Process (E := C) 𝓕 μ H) :
    post 𝓕 μ H v (a • u)=a • post 𝓕 μ H v u := by
  apply eq_of_ambient_ae
  filter_upwards [post_ae 𝓕 μ H v (a • u),post_ae 𝓕 μ H v u,
    ae_eq_of_ae_eq_trim (Lp.coeFn_smul a u),
    ae_eq_of_ae_eq_trim (Lp.coeFn_smul a (post 𝓕 μ H v u))] with p hp hu hi ho
  rw [hp,ho]
  simp only [Pi.smul_apply,hu,RingHom.id_apply]
  by_cases h : v<p.1 <;> simp only [h,ite_true,ite_false,smul_zero,hi,Pi.smul_apply,RingHom.id_apply]

theorem post_weighted (v : ℝ≥0) (a : ℝ≥0×Ω→ℝ) (ha : StronglyMeasurable[𝓕.predictable] a)
    (hb : ∀ p,|a p|≤1) (u : Process (E := C) 𝓕 μ H) :
    post 𝓕 μ H v (PredictableContraction.weighted 𝓕 μ H a ha hb u)=
      PredictableContraction.weighted 𝓕 μ H a ha hb (post 𝓕 μ H v u) := by
  apply eq_of_ambient_ae
  filter_upwards [post_ae 𝓕 μ H v (PredictableContraction.weighted 𝓕 μ H a ha hb u),
    post_ae 𝓕 μ H v u,PredictableContraction.weighted_ae 𝓕 μ H a ha hb u,
    PredictableContraction.weighted_ae 𝓕 μ H a ha hb (post 𝓕 μ H v u)] with p hp hu hi ho
  rw [hp,ho,hu]
  by_cases h : v<p.1 <;> simp only [h,ite_true,ite_false,smul_zero,hi]

section Isometry
variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [MeasurableSpace A] [BorelSpace A]
variable (Φ : ℝ≥0×Ω→A→ₗᵢ[ℝ]C)
variable (hΦ : @Measurable ((ℝ≥0×Ω)×A) C (𝓕.predictable.prod ‹MeasurableSpace A›) ‹MeasurableSpace C›
  (fun p => Φ p.1 p.2))

theorem post_isometry (v : ℝ≥0) (u : Process (E := A) 𝓕 μ H) :
    post 𝓕 μ H v (PredictableItoRotation.processIsometry 𝓕 μ H Φ hΦ u)=
      PredictableItoRotation.processIsometry 𝓕 μ H Φ hΦ (post 𝓕 μ H v u) := by
  apply eq_of_ambient_ae
  filter_upwards [post_ae 𝓕 μ H v (PredictableItoRotation.processIsometry 𝓕 μ H Φ hΦ u),
    post_ae 𝓕 μ H v u,PredictableItoRotation.processIsometry_ae 𝓕 μ H Φ hΦ u,
    PredictableItoRotation.processIsometry_ae 𝓕 μ H Φ hΦ (post 𝓕 μ H v u)] with p hp hu hi ho
  rw [hp,ho,hu]
  by_cases h : v<p.1 <;> simp only [h,ite_true,ite_false,map_zero,hi]

end Isometry

variable [SFinite μ]

/-- Ordinary increment algebra inside the original predictable L2
space, including the deterministic endpoint null set. -/
theorem post_stop_eq_sub (v q : ℝ≥0) (hvq : v≤q) (u : Process (E := C) 𝓕 μ H) :
    post 𝓕 μ H v (stop 𝓕 μ H (q:ℝ) u)=stop 𝓕 μ H (q:ℝ) u-stop 𝓕 μ H (v:ℝ) u := by
  apply eq_of_ambient_ae
  have hne : ∀ᵐ p ∂energyMeasure μ H,p.1≠v :=
    Measure.quasiMeasurePreserving_fst.ae ((timeMeasure H).ae_ne v)
  filter_upwards [post_ae 𝓕 μ H v (stop 𝓕 μ H (q:ℝ) u),stop_ae 𝓕 μ H (q:ℝ) u,
    stop_ae 𝓕 μ H (v:ℝ) u,ae_eq_of_ae_eq_trim
      (Lp.coeFn_sub (stop 𝓕 μ H (q:ℝ) u) (stop 𝓕 μ H (v:ℝ) u)),hne] with p hp hq hv ho hn
  rw [hp,ho]
  simp only [Pi.sub_apply,hq,hv,Set.indicator,before,mem_setOf_eq,NNReal.coe_lt_coe]
  by_cases h₁ : p.1<q <;> by_cases h₂ : p.1<v <;> by_cases h₃ : v<p.1 <;>
    simp only [h₁,h₂,h₃,ite_true,ite_false,sub_zero,sub_self,zero_sub] <;> order

end SHE.PastItoAlgebra
