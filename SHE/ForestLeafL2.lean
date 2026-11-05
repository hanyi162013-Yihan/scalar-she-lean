module

public import SHE.ForestLeafInput
public import SHE.WeightedSFiniteMoments

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.ForestLeafInput
open Set Filter MeasureTheory ProbabilityTheory Real AddCircle StoppedFourier
  ProfileL2 StoppedScoreLeverage OrderedHeatForests
local instance forestLeafL2_periodPos : Fact (0<2*π) := ⟨by positivity⟩
variable {W : Type*} [MeasurableSpace W]

/-- The actual positive translated envelope is jointly integrable from
its L¹ weight and an L² spatial input. No bounded input representative
is needed to justify Fubini or the subsequent density Jensen. -/
theorem averaged_leaf_joint_integrable (μ : Measure W) [SFinite μ]
    (K : W→ℝ) (hKm : Measurable K) (hKi : Integrable K μ) (hK : ∀ w,0≤K w)
    (z : W→HeatCircle) (hz : Measurable z) (f : HeatCircle→ℝ) (hf : Measurable f)
    (hfi : MemLp f 2 haarAddCircle) :
    Integrable (fun p : HeatCircle×W=>K p.2*|f (p.1+z p.2)|) (haarAddCircle.prod μ) := by
  let F : HeatCircle×W→ℝ:=fun p=>K p.2*|f (p.1+z p.2)|
  have hF : Measurable F:=(hKm.comp measurable_snd).mul
    ((continuous_abs.measurable.comp hf).comp (measurable_fst.add (hz.comp measurable_snd)))
  have hsection (w:W) : Integrable (fun x:HeatCircle=>F (x,w)) haarAddCircle :=
    (((hfi.comp_measurePreserving (measurePreserving_add_right haarAddCircle (z w))).integrable
      (by norm_num)).norm.const_mul (K w)).congr
        (ae_of_all _ (fun _=>by simp only [F,Real.norm_eq_abs,Function.comp_apply]))
  apply (integrable_prod_iff' hF.aestronglyMeasurable).mpr
  refine ⟨ae_of_all _ hsection,?_⟩
  have he (w:W) : (∫ x:HeatCircle,‖F (x,w)‖ ∂haarAddCircle)=
      K w*(∫ x:HeatCircle,|f x| ∂haarAddCircle) := by
    simp only [F,Real.norm_eq_abs,abs_mul,abs_abs,abs_of_nonneg (hK w),integral_const_mul]
    rw [integral_add_right_eq_self (μ:=haarAddCircle) (fun x:HeatCircle=>|f x|) (z w)]
  simpa only [he] using hKi.mul_const (∫ x:HeatCircle,|f x| ∂haarAddCircle)

/-- Positive translated averaging is an actual L² contraction at its
L¹ mass. The input needs ONLY L², not a spatial supremum or a bounded
representative. Joint and section integrability are proved by Jensen. -/
theorem averaged_leaf_L2 (μ : Measure W) [SFinite μ]
    (K : W→ℝ) (hKm : Measurable K) (hKi : Integrable K μ) (hK : ∀ w,0≤K w)
    (z : W→HeatCircle) (hz : Measurable z) (f : HeatCircle→ℝ) (hf : Measurable f)
    (hfi : MemLp f 2 haarAddCircle) :
    MemLp (fun x=>∫ w,K w*|f (x+z w)| ∂μ) 2 haarAddCircle ∧
      normTwo haarAddCircle (fun x=>∫ w,K w*|f (x+z w)| ∂μ)≤
        (∫ w,K w ∂μ)*normTwo haarAddCircle f := by
  let F : HeatCircle×W→ℝ:=fun p=>K p.2*|f (p.1+z p.2)|
  have hF : Measurable F:=(hKm.comp measurable_snd).mul
    ((continuous_abs.measurable.comp hf).comp (measurable_fst.add (hz.comp measurable_snd)))
  have hshift (w:W) : MemLp (fun x:HeatCircle=>f (x+z w)) 2 haarAddCircle:=
    hfi.comp_measurePreserving (measurePreserving_add_right haarAddCircle (z w))
  have hi (w:W) : Integrable (fun x:HeatCircle=>|F (x,w)|^2) haarAddCircle := by
    have hh:=(hshift w).integrable_sq.const_mul ((K w)^2)
    simpa only [F,abs_mul,mul_pow,sq_abs] using hh
  have hb (w:W) : (∫ x:HeatCircle,|F (x,w)|^2 ∂haarAddCircle)≤
      (normTwo haarAddCircle f)^2*(K w)^2 := by
    simp only [F,abs_mul,mul_pow,sq_abs,integral_const_mul,normTwo_sq]
    rw [integral_add_right_eq_self (μ:=haarAddCircle) (fun x:HeatCircle=>(f x)^2) (z w)]
    exact (mul_comm _ _).le
  have hh:=WeightedSFiniteMoments.nonnegative_envelope haarAddCircle μ F hF K hKm hKi hK
    1 zero_lt_one ((normTwo haarAddCircle f)^2) (sq_nonneg _)
    (ae_of_all _ hi) (ae_of_all _ hb)
  have hm : Measurable (fun x=>∫ w,F (x,w) ∂μ):=
    hF.stronglyMeasurable.integral_prod_right'.measurable
  have hmem : MemLp (fun x=>∫ w,F (x,w) ∂μ) 2 haarAddCircle:=by
    apply (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr
    simpa only [mul_one,one_mul,sq_abs] using hh.1
  refine ⟨hmem,?_⟩
  apply (sq_le_sq₀ (normTwo_nonneg _ _) (mul_nonneg (integral_nonneg hK) (normTwo_nonneg _ _))).mp
  rw [normTwo_sq]
  have h0:=hh.2
  simpa only [F,mul_one,one_mul,sq_abs,mul_pow,mul_comm] using h0

/-- The ORIGINAL full parent forest transfers an arbitrary L² leaf
input with no new time loss and only its exact finite forest mass. -/
theorem parent_leaf_L2 {m k : ℕ} (κ : ℝ) (hκ : 0<κ)
    (t : Fin (m+k)→ℝ) (ht : OrderedTimes k t) (aRoot : Fin m→HeatCircle)
    (j : Fin (m+k)) (f : HeatCircle→ℝ) (hf : Measurable f) (hfi : MemLp f 2 haarAddCircle) :
    MemLp (fun x=>∫ w:Fin k→HeatCircle,
      parentDensity κ hκ k t ht (values aRoot k w)*|f (x+values aRoot k w j)|
        ∂Measure.pi (fun _=>haarAddCircle)) 2 haarAddCircle ∧
    normTwo haarAddCircle (fun x=>∫ w:Fin k→HeatCircle,
      parentDensity κ hκ k t ht (values aRoot k w)*|f (x+values aRoot k w j)|
        ∂Measure.pi (fun _=>haarAddCircle))≤
      (Fintype.card (Choices m k):ℝ)*normTwo haarAddCircle f := by
  have hKc:=(ForestedScoreInput.parentDensity_continuous κ hκ k t ht).comp (values_continuous aRoot k)
  have hKi : Integrable (fun w:Fin k→HeatCircle=>parentDensity κ hκ k t ht (values aRoot k w))
      (Measure.pi (fun _=>haarAddCircle)):=
    hKc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hK (w:Fin k→HeatCircle) : 0≤parentDensity κ hκ k t ht (values aRoot k w):=by
    rw [←sum_density_eq κ hκ k t ht]
    exact Finset.sum_nonneg (fun Q _=>density_nonneg _ _)
  have hz : Measurable (fun w:Fin k→HeatCircle=>values aRoot k w j):=
    (continuous_apply j).measurable.comp (values_continuous aRoot k).measurable
  have hh:=averaged_leaf_L2 (Measure.pi (fun _ : Fin k=>haarAddCircle)) _ hKc.measurable hKi hK
    _ hz f hf hfi
  simpa only [Function.comp_apply,ForestedScoreInput.parentDensity_mass] using hh

end SHE.ForestLeafInput
