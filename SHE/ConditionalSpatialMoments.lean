module

public import SHE.WeightedSFiniteMoments
public import SHE.PastEventWeights

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section

namespace SHE.ConditionalSpatialMoments
open Set Filter MeasureTheory Real
open scoped ENNReal
variable {Ω X : Type*} [m0 : MeasurableSpace Ω] [MeasurableSpace X]
variable (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure X) [SFinite ν]

/-- Genuine conditional spatial density averaging. The restricted past
measure is not treated as a probability measure: applying ordinary
probability-space Jensen to the event indicator preserves its exact
mass, including the zero-mass event. -/
theorem on_event (F : Ω×X→ℝ) (hF : Measurable F)
    (H : X→ℝ) (hHm : Measurable H) (hHi : Integrable H ν) (hH : ∀ x,0 ≤ H x)
    (b : ℕ) (hb : 0<b) (C : ℝ) (hC : 0 ≤ C)
    (A : Set Ω) (hA : MeasurableSet A)
    (hi : ∀ᵐ x ∂ν,Integrable (fun ω=>|F (ω,x)|^(2*b)) (μ.restrict A))
    (hbound : ∀ᵐ x ∂ν,(∫ ω in A,|F (ω,x)|^(2*b) ∂μ) ≤ C*(H x)^(2*b)*μ.real A) :
    Integrable (fun ω=>|∫ x,F (ω,x) ∂ν|^(2*b)) (μ.restrict A) ∧
      (∫ ω in A,|∫ x,F (ω,x) ∂ν|^(2*b) ∂μ) ≤ C*(∫ x,H x ∂ν)^(2*b)*μ.real A := by
  classical
  let FA : Ω×X→ℝ:=fun z=>if z.1∈A then F z else 0
  have hFA : Measurable FA:=hF.ite (hA.preimage measurable_fst) measurable_const
  have hpow (x:X) : (fun ω=>|FA (ω,x)|^(2*b))=A.indicator (fun ω=>|F (ω,x)|^(2*b)) := by
    funext ω
    by_cases hω:ω∈A
    · simp only [FA,ite_eq_left hω,indicator_of_mem hω]
    · simp only [FA,ite_eq_right hω,indicator_of_notMem hω,abs_zero,zero_pow (by omega:2*b≠0)]
  have hiFA : ∀ᵐ x ∂ν,Integrable (fun ω=>|FA (ω,x)|^(2*b)) μ := by
    filter_upwards [hi] with x hx
    rw [hpow]
    exact (integrable_indicator_iff hA).mpr hx
  have hbFA : ∀ᵐ x ∂ν,(∫ ω,|FA (ω,x)|^(2*b) ∂μ) ≤ (C*μ.real A)*(H x)^(2*b) := by
    filter_upwards [hbound] with x hx
    rw [hpow,integral_indicator hA]
    convert! hx using 1 <;> ring
  have hh:=WeightedSFiniteMoments.nonnegative_envelope μ ν FA hFA H hHm hHi hH b hb
    (C*μ.real A) (mul_nonneg hC measureReal_nonneg) hiFA hbFA
  have havg (ω:Ω) : (∫ x,FA (ω,x) ∂ν)=if ω∈A then ∫ x,F (ω,x) ∂ν else 0 := by
    by_cases hω:ω∈A <;> simp only [FA,hω,ite_true,ite_false,integral_zero]
  have he : (fun ω=>|∫ x,FA (ω,x) ∂ν|^(2*b))=
      A.indicator (fun ω=>|∫ x,F (ω,x) ∂ν|^(2*b)) := by
    funext ω
    rw [havg]
    by_cases hω:ω∈A
    · simp only [ite_eq_left hω,indicator_of_mem hω]
    · simp only [ite_eq_right hω,indicator_of_notMem hω,abs_zero,zero_pow (by omega:2*b≠0)]
  rw [he] at hh
  refine ⟨(integrable_indicator_iff hA).mp hh.1,?_⟩
  rw [integral_indicator hA] at hh
  convert! hh.2 using 1 <;> ring

/-- The conditional density estimate preserves an arbitrary integrable
nonnegative past-measurable weight. The field, its Gaussian reference
and the weight can all depend on the same original past state. -/
theorem with_past_weight (F : Ω×X→ℝ) (hF : Measurable F)
    (H : X→ℝ) (hHm : Measurable H) (hHi : Integrable H ν) (hH : ∀ x,0 ≤ H x)
    (b : ℕ) (hb : 0<b) (C : ℝ) (hC : 0 ≤ C)
    {m : MeasurableSpace Ω} (hm : m ≤ m0)
    (hpoint : ∀ᵐ x ∂ν,∀ A : Set Ω,MeasurableSet[m] A →
      Integrable (fun ω=>|F (ω,x)|^(2*b)) (μ.restrict A) ∧
        (∫ ω in A,|F (ω,x)|^(2*b) ∂μ) ≤ C*(H x)^(2*b)*μ.real A)
    (weight : Ω→ℝ) (hw : Measurable[m] weight) (hw0 : ∀ ω,0 ≤ weight ω)
    (hwi : Integrable weight μ) :
    Integrable (fun ω=>weight ω*|∫ x,F (ω,x) ∂ν|^(2*b)) μ ∧
      (∫ ω,weight ω*|∫ x,F (ω,x) ∂ν|^(2*b) ∂μ) ≤ 
        C*(∫ x,H x ∂ν)^(2*b)*(∫ ω,weight ω ∂μ) := by
  classical
  letI : MeasurableSpace Ω := m0
  have hevent (A:Set Ω) (hA:MeasurableSet[m] A):=
    on_event μ ν F hF H hHm hHi hH b hb C hC A (hm A hA)
      (hpoint.mono (fun _ hx=>(hx A hA).1)) (hpoint.mono (fun _ hx=>(hx A hA).2))
  have hi : Integrable (fun ω=>|∫ x,F (ω,x) ∂ν|^(2*b)) μ := by
    simpa only [Measure.restrict_univ] using (hevent univ MeasurableSet.univ).1
  have hmeas : Measurable (fun ω=>|∫ x,F (ω,x) ∂ν|^(2*b)) :=
    (continuous_abs.measurable.comp hF.stronglyMeasurable.integral_prod_right'.measurable).pow_const _
  exact PastEventWeights.weighted_integral μ hm _ hmeas hi
    (fun _=>pow_nonneg (abs_nonneg _) _) _
    (mul_nonneg hC (pow_nonneg (integral_nonneg hH) _))
    (fun A hA=>(hevent A hA).2) weight hw hw0 hwi

end SHE.ConditionalSpatialMoments
