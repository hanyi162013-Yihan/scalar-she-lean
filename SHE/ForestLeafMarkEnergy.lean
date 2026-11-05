module

public import SHE.ForestLeafL2
public import SHE.ScalarFibreRMS
public import SHE.SpatialMarkAE

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.ForestLeafMarkEnergy
open Set Filter MeasureTheory ProbabilityTheory Real AddCircle StoppedFourier ProfileL2 OrderedHeatForests
local instance forestLeafMarkEnergy_period : Fact (0<2*π) := ⟨by positivity⟩
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- A genuine correlated random leaf input passes through the ORIGINAL
physical parent forest, with old-space averaging BEFORE sample/output
L². Only its actual sample/spatial energy enters; no spatial supremum,
independence or separate random-factor estimate is used. -/
theorem leaf_mark_energy {m k : ℕ} (κ : ℝ) (hκ : 0<κ)
    (t : Fin (m+k)→ℝ) (ht : OrderedTimes k t) (aRoot : Fin m→HeatCircle) (j : Fin (m+k))
    (e : Ω×HeatCircle→ℝ) (he : Measurable e)
    (hei : Integrable (fun z=>|e z|^2) (μ.prod haarAddCircle))
    (F : (Ω×HeatCircle)×(Fin k→HeatCircle)→ℝ) (hF : Measurable F)
    (C : ℝ) (hC : 0≤C)
    (hi : ∀ᵐ x:HeatCircle ∂haarAddCircle,∀ᵐ w:Fin k→HeatCircle ∂Measure.pi (fun _=>haarAddCircle),
      Integrable (fun ω=>|F ((ω,x),w)|^2) μ)
    (hb : ∀ᵐ x:HeatCircle ∂haarAddCircle,∀ᵐ w:Fin k→HeatCircle ∂Measure.pi (fun _=>haarAddCircle),
      (∫ ω,|F ((ω,x),w)|^2 ∂μ)≤C*
        (parentDensity κ hκ k t ht (values aRoot k w)*
          ScalarFibreRMS.rms μ e (x+values aRoot k w j))^2) :
    Integrable (fun z:Ω×HeatCircle=>|∫ w:Fin k→HeatCircle,F (z,w)
      ∂Measure.pi (fun _=>haarAddCircle)|^2) (μ.prod haarAddCircle) ∧
      (∫ z:Ω×HeatCircle,|∫ w:Fin k→HeatCircle,F (z,w)
        ∂Measure.pi (fun _=>haarAddCircle)|^2 ∂μ.prod haarAddCircle)≤
        C*(Fintype.card (Choices m k):ℝ)^2*(∫ z,|e z|^2 ∂μ.prod haarAddCircle) := by
  let η:=Measure.pi (fun _ : Fin k=>haarAddCircle (T:=2*π))
  let f:=ScalarFibreRMS.rms μ e
  let K:=fun w:Fin k→HeatCircle=>parentDensity κ hκ k t ht (values aRoot k w)
  let z:=fun w:Fin k→HeatCircle=>values aRoot k w j
  let H:=fun p:HeatCircle×(Fin k→HeatCircle)=>K p.2*f (p.1+z p.2)
  have hf : Measurable f:=ScalarFibreRMS.measurable μ e he
  have hf0 (x) : 0≤f x:=ScalarFibreRMS.nonneg μ e x
  have hfe:=ScalarFibreRMS.memLp_energy μ haarAddCircle e he hei
  have hKc:=(ForestedScoreInput.parentDensity_continuous κ hκ k t ht).comp (values_continuous aRoot k)
  have hKi : Integrable K η:=hKc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hK0 (w) : 0≤K w:=by
    dsimp only [K]
    rw [←sum_density_eq κ hκ k t ht]
    exact Finset.sum_nonneg (fun Q _=>density_nonneg _ _)
  have hz : Measurable z:=(continuous_apply j).measurable.comp (values_continuous aRoot k).measurable
  have hHm : Measurable H:=(hKc.measurable.comp measurable_snd).mul
    (hf.comp (measurable_fst.add (hz.comp measurable_snd)))
  have hH0 (x) (w) : 0≤H (x,w):=mul_nonneg (hK0 w) (hf0 _)
  have hHi : ∀ᵐ x:HeatCircle ∂haarAddCircle,Integrable (fun w=>H (x,w)) η := by
    have hh:=ForestLeafInput.averaged_leaf_joint_integrable η K hKc.measurable hKi hK0 z hz f hf hfe.1
    simpa only [abs_of_nonneg (hf0 _)] using hh.prod_right_ae
  have hyoung:=ForestLeafInput.parent_leaf_L2 κ hκ t ht aRoot j f hf hfe.1
  have hG : MemLp (fun x=>∫ w,H (x,w) ∂η) 2 haarAddCircle := by
    simpa only [H,K,z,η,abs_of_nonneg (hf0 _)] using hyoung.1
  have hGn : normTwo haarAddCircle (fun x=>∫ w,H (x,w) ∂η)≤
      (Fintype.card (Choices m k):ℝ)*normTwo haarAddCircle f := by
    simpa only [H,K,z,η,abs_of_nonneg (hf0 _)] using hyoung.2
  have havg:=SpatialMarkAveraging.averaged_second_moment_ae μ haarAddCircle η F hF H hHm hH0 hHi hG hC hi hb
  refine ⟨havg.1,havg.2.trans ?_⟩
  have hh:=mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (normTwo_nonneg _ _) hGn 2) hC
  rw [mul_pow,hfe.2] at hh
  simpa only [mul_assoc] using hh

end SHE.ForestLeafMarkEnergy
