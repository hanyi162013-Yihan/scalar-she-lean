module

public import SHE.ForestLeafMarkEnergy
public import SHE.ConditionalSquareL1

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1200000
noncomputable section

namespace SHE.ForestLeafAbsolute
open Set Filter MeasureTheory ProbabilityTheory Real AddCircle StoppedFourier ProfileL2 OrderedHeatForests
local instance forestLeafAbsolute_period : Fact (0<2*π) := ⟨by positivity⟩
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- The original parent forest and a genuine sample/spatial L2 leaf
input give ABSOLUTE integrability before old-space averaging. This
justifies finite baseline sums and history Fubini, rather than inferring
it from a bound on the already-averaged signed field. -/
theorem joint_integrable {m k : ℕ} (κ : ℝ) (hκ : 0<κ)
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
    Integrable F ((μ.prod haarAddCircle).prod (Measure.pi (fun _ : Fin k=>haarAddCircle))) := by
  let η:=Measure.pi (fun _ : Fin k=>haarAddCircle (T:=2*π))
  let f:=ScalarFibreRMS.rms μ e
  let K:=fun w:Fin k→HeatCircle=>parentDensity κ hκ k t ht (values aRoot k w)
  let z:=fun w:Fin k→HeatCircle=>values aRoot k w j
  let H:=fun p:HeatCircle×(Fin k→HeatCircle)=>K p.2*f (p.1+z p.2)
  let G:=fun p:Ω×(HeatCircle×(Fin k→HeatCircle))=>F ((p.1,p.2.1),p.2.2)
  have hG : Measurable G:=hF.comp ((measurable_fst.prodMk measurable_snd.fst).prodMk measurable_snd.snd)
  have hf : Measurable f:=ScalarFibreRMS.measurable μ e he
  have hf0 (x) : 0≤f x:=ScalarFibreRMS.nonneg μ e x
  have hfi:=ScalarFibreRMS.memLp_energy μ haarAddCircle e he hei
  have hKc:=(ForestedScoreInput.parentDensity_continuous κ hκ k t ht).comp (values_continuous aRoot k)
  have hKi : Integrable K η:=hKc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hK0 (w) : 0≤K w:=by
    dsimp only [K]
    rw [←sum_density_eq κ hκ k t ht]
    exact Finset.sum_nonneg (fun Q _=>density_nonneg _ _)
  have hz : Measurable z:=(continuous_apply j).measurable.comp (values_continuous aRoot k).measurable
  have hH : Measurable H:=(hKc.measurable.comp measurable_snd).mul
    (hf.comp (measurable_fst.add (hz.comp measurable_snd)))
  have hH0 (p) : 0≤H p:=mul_nonneg (hK0 _) (ScalarFibreRMS.nonneg μ e _)
  have hHi : Integrable H (haarAddCircle.prod η):=by
    simpa only [H,abs_of_nonneg (hf0 _)] using
      ForestLeafInput.averaged_leaf_joint_integrable η K hKc.measurable hKi hK0 z hz f hf hfi.1
  have hia : ∀ᵐ p : HeatCircle×(Fin k→HeatCircle) ∂haarAddCircle.prod η,
      Integrable (fun ω=>|G (ω,p)|^2) μ:=by
    apply (Measure.ae_prod_iff_ae_ae ?_).mpr hi
    have hm : Measurable (fun p : (HeatCircle×(Fin k→HeatCircle))×Ω=>|G (p.2,p.1)|^2):=
      (continuous_abs.measurable.comp (hG.comp measurable_swap)).pow_const 2
    exact _root_.measurableSet_integrable hm.stronglyMeasurable
  have hba : ∀ᵐ p : HeatCircle×(Fin k→HeatCircle) ∂haarAddCircle.prod η,
      (∫ ω,|G (ω,p)|^2 ∂μ)≤C*(H p)^2:=by
    apply (Measure.ae_prod_iff_ae_ae ?_).mpr hb
    exact measurableSet_le
      ((continuous_abs.measurable.comp hG).pow_const (2:ℕ)).stronglyMeasurable.integral_prod_left'.measurable
      ((hH.pow_const 2).const_mul C)
  have hh:=ConditionalSquareL1.joint_integrable μ (haarAddCircle.prod η) G hG H hHi hH0 hC hia hba
  have heq:=(measurePreserving_prodAssoc μ haarAddCircle η).integrable_comp_of_integrable hh.1
  convert! heq using 1

end SHE.ForestLeafAbsolute
