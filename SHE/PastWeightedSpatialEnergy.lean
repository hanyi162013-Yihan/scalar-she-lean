module

public import SHE.PastEventWeights
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section

namespace SHE.PastWeightedSpatialEnergy
open Set MeasureTheory Real
variable {Ω X:Type*} {m m0:MeasurableSpace Ω} [MeasurableSpace X]

/-- A genuine conditional normalized-word bound pairs with an arbitrary
PAST-measurable spatial source. The source remains correlated with the
future word; product Fubini is derived from its true spatial energy. -/
theorem energy (μ:@Measure Ω m0) [IsFiniteMeasure μ] (hm:m≤m0)
    (ν:Measure X) [SFinite ν] (F source:Ω×X→ℝ)
    (hF:Measurable[m0.prod inferInstance] F)
    (hs:Measurable[m.prod inferInstance] source)
    (hsi:Integrable (fun y=>source y^2) (μ.prod ν))
    {C:ℝ} (hC:0≤C)
    (hMom:∀ᵐ x ∂ν,∀A:Set Ω,MeasurableSet[m] A→
      Integrable (fun ω=>|F (ω,x)|^2) (μ.restrict A) ∧
      (∫ω in A,|F (ω,x)|^2 ∂μ)≤C*μ.real A) :
    Integrable (fun y=>|source y*F y|^2) (μ.prod ν) ∧
      (∫y,|source y*F y|^2 ∂μ.prod ν)≤C*(∫y,source y^2 ∂μ.prod ν) := by
  letI:MeasurableSpace Ω:=m0
  have hid : @Measurable Ω Ω m0 m id := fun s hs=>hm s hs
  have hsa:Measurable source:=by
    convert! hs.comp (hid.prodMap (measurable_id (α:=X))) using 1
  let W:Ω×X→ℝ:=fun y=>source y^2*F y^2
  have hW:Measurable W:=(hsa.pow_const 2).mul (hF.pow_const 2)
  have hsec:∀ᵐ x ∂ν,Integrable (fun ω=>W (ω,x)) μ ∧
      (∫ω,W (ω,x) ∂μ)≤C*(∫ω,source (ω,x)^2 ∂μ) := by
    filter_upwards [hMom,hsi.prod_left_ae] with x hx hix
    have hfm:Measurable (fun ω=>|F (ω,x)|^2):=
      (continuous_abs.measurable.comp (hF.comp (measurable_id.prodMk measurable_const))).pow_const 2
    have hsm:Measurable[m] (fun ω=>source (ω,x)^2):=
      (hs.comp (measurable_id.prodMk measurable_const)).pow_const 2
    have hh:=PastEventWeights.weighted_integral μ hm (fun ω=>|F (ω,x)|^2) hfm
      (by simpa only [Measure.restrict_univ] using (hx univ MeasurableSet.univ).1)
      (fun _=>sq_nonneg _) C hC (fun A hA=>(hx A hA).2)
      (fun ω=>source (ω,x)^2) hsm (fun _=>sq_nonneg _) hix
    simpa only [W,sq_abs] using hh
  have hWi:Integrable W (μ.prod ν) := by
    apply (integrable_prod_iff' hW.aestronglyMeasurable).mpr
    refine ⟨hsec.mono (fun _ h=>h.1),?_⟩
    apply (hsi.integral_prod_right.const_mul C).mono'
      hW.norm.stronglyMeasurable.integral_prod_left'.aestronglyMeasurable
    filter_upwards [hsec] with x hx
    simp only [Real.norm_eq_abs,abs_of_nonneg (integral_nonneg
      (fun _=>abs_nonneg _))]
    have he:(∫ω,|W (ω,x)| ∂μ)=(∫ω,W (ω,x) ∂μ):=by
      apply integral_congr_ae
      exact ae_of_all _ (fun ω=>abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)))
    rw [he]
    exact hx.2
  have hb:(∫y,W y ∂μ.prod ν)≤C*(∫y,source y^2 ∂μ.prod ν) := by
    rw [integral_prod_symm _ hWi,integral_prod_symm _ hsi,←integral_const_mul]
    exact integral_mono_ae hWi.integral_prod_right (hsi.integral_prod_right.const_mul C)
      (hsec.mono (fun _ h=>h.2))
  simpa only [W,abs_mul,mul_pow,sq_abs] using And.intro hWi hb

end SHE.PastWeightedSpatialEnergy
