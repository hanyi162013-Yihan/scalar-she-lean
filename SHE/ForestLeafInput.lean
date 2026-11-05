module

public import SHE.ParentScoreInput

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.ForestLeafInput
open Set Filter MeasureTheory ProbabilityTheory Real AddCircle StoppedFourier
  ProfileL2 StoppedScoreLeverage OrderedHeatForests
local instance forestLeafInput_periodPos : Fact (0<2*π) := ⟨by positivity⟩
variable {W : Type*} [MeasurableSpace W]

/-- A leaf input may depend on the same old relative location as the
forest. Averaging preserves its L2 gain by physical translation and
Minkowski, without a spatial supremum in the final bound. -/
theorem averaged_leaf_normTwo (μ : Measure W) [SFinite μ]
    (K : W→ℝ) (hKm : Measurable K) (hKi : Integrable K μ) (hK : ∀ w,0≤K w)
    (z : W→HeatCircle) (hz : Measurable z) (f : HeatCircle→ℝ) (hf : Measurable f)
    {B : ℝ} (hB : 0≤B) (hfb : ∀ x,|f x|≤B) :
    normTwo haarAddCircle (fun x=>∫ w,K w*|f (x+z w)| ∂μ)≤
      (∫ w,K w ∂μ)*normTwo haarAddCircle f := by
  let a := normTwo haarAddCircle f
  have ha : 0≤a := normTwo_nonneg _ _
  have hF : Measurable (fun p : W×HeatCircle=>K p.1*|f (p.2+z p.1)|) :=
    (hKm.comp measurable_fst).mul ((continuous_abs.measurable.comp hf).comp
      (measurable_snd.add (hz.comp measurable_fst)))
  have hG (w : W) : MemLp (fun x : HeatCircle=>|f (x+z w)|) 2 haarAddCircle := by
    have hm : Measurable (fun x : HeatCircle=>|f (x+z w)|) :=
      (continuous_abs.measurable.comp hf).comp (measurable_id.add_const (z w))
    exact bounded_memLp hm (fun x=>by rw [abs_abs];exact hfb _)
  have hh := bounded_minkowski_two hF (hKi.mul_const a) (hKi.mul_const B)
    (ae_of_all _ (fun w=>mul_nonneg (hK w) ha))
    (ae_of_all _ (fun w=>mul_nonneg (hK w) hB))
    (ae_of_all _ (fun w x=>by
      change |K w * (|f (x+z w)|)|≤K w*B
      rw [abs_of_nonneg (mul_nonneg (hK w) (abs_nonneg _))]
      exact mul_le_mul_of_nonneg_left (hfb _) (hK w)))
    (ae_of_all _ (fun w=>by
      rw [normTwo_const_mul (hG w) (K w),abs_of_nonneg (hK w),normTwo_abs_add]
      ))
  simpa only [integral_mul_const,a] using hh

/-- The whole old parent forest transfers one omitted-leaf baseline
input with exactly its finite forest count and no new time singularity. -/
theorem parent_leaf_normTwo {m k : ℕ} (κ : ℝ) (hκ : 0<κ)
    (t : Fin (m+k)→ℝ) (ht : OrderedTimes k t) (aRoot : Fin m→HeatCircle)
    (j : Fin (m+k)) (f : HeatCircle→ℝ) (hf : Measurable f)
    {B : ℝ} (hB : 0≤B) (hfb : ∀ x,|f x|≤B) :
    normTwo haarAddCircle (fun x=>∫ w : Fin k→HeatCircle,
      parentDensity κ hκ k t ht (values aRoot k w)*|f (x+values aRoot k w j)|
        ∂Measure.pi (fun _=>haarAddCircle))≤
      (Fintype.card (Choices m k):ℝ)*normTwo haarAddCircle f := by
  have hKc := (ForestedScoreInput.parentDensity_continuous κ hκ k t ht).comp (values_continuous aRoot k)
  have hKi : Integrable (fun w : Fin k→HeatCircle=>parentDensity κ hκ k t ht (values aRoot k w))
      (Measure.pi (fun _=>haarAddCircle)) :=
    hKc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hK (w : Fin k→HeatCircle) : 0≤parentDensity κ hκ k t ht (values aRoot k w) := by
    rw [←sum_density_eq κ hκ k t ht]
    exact Finset.sum_nonneg (fun Q _=>density_nonneg _ _)
  have hz : Measurable (fun w : Fin k→HeatCircle=>values aRoot k w j) :=
    (continuous_apply j).measurable.comp (values_continuous aRoot k).measurable
  have hh := averaged_leaf_normTwo (Measure.pi (fun _ : Fin k=>haarAddCircle))
    (fun w=>parentDensity κ hκ k t ht (values aRoot k w)) hKc.measurable hKi hK
    (fun w=>values aRoot k w j) hz f hf hB hfb
  simpa only [ForestedScoreInput.parentDensity_mass] using hh

end SHE.ForestLeafInput
