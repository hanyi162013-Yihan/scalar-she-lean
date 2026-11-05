module
public import SHE.InitialOrdinaryNewestFibre
public import SHE.InitialNativeOldCube

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace SHE.InitialOrdinaryNewestIntegration
open Set MeasureTheory Real
open scoped BigOperators

/-- Exact variable-terminal current restriction inside one fixed
initial horizon; no value outside the initial triangle contributes. -/
theorem current_restrict{h T:ℝ}(hT:T≤h)(f:ℝ→ℝ):
    (∫q in Ioc (0:ℝ) h,if q≤T then f q else 0)=∫q in Ioc (0:ℝ) T,f q:=by
  have hset:Iic T∩Ioc (0:ℝ) h=Ioc 0 T:=by
    ext q
    simp only [mem_inter_iff,mem_Iic,mem_Ioc]
    constructor
    · exact fun h=>⟨h.2.1,h.1⟩
    · exact fun h=>⟨h.2,h.1,h.2.trans hT⟩
  change (∫q,(Iic T).indicator f q ∂volume.restrict (Ioc (0:ℝ) h))=_
  rw [integral_indicator measurableSet_Iic,Measure.restrict_restrict measurableSet_Iic,hset]

/-- Every original old time is restricted to the actual initial
terminal, even though the Borel parameter field uses one fixed cube. -/
theorem old_cube_restrict{h T:ℝ}(hT:T≤h)(k:ℕ)(f:(Fin k→ℝ)→ℝ):
    (∫t,if ∀i,t i≤T then f t else 0
      ∂Measure.pi (fun _:Fin k=>volume.restrict (Ioc 0 h)))=
    ∫t,f t ∂Measure.pi (fun _:Fin k=>volume.restrict (Ioc 0 T)):=by
  let box:=Set.univ.pi (fun _:Fin k=>Iic T)
  have hb:MeasurableSet box:=MeasurableSet.univ_pi (fun _=>measurableSet_Iic)
  have hset:Iic T∩Ioc (0:ℝ) h=Ioc 0 T:=by
    ext q
    simp only [mem_inter_iff,mem_Iic,mem_Ioc]
    constructor
    · exact fun h=>⟨h.2.1,h.1⟩
    · exact fun h=>⟨h.2,h.1,h.2.trans hT⟩
  have he:Measure.pi (fun _:Fin k=>volume.restrict (Ioc 0 T))=
      (Measure.pi (fun _:Fin k=>volume.restrict (Ioc 0 h))).restrict box:=by
    rw [Measure.restrict_pi_pi]
    congr 1
    funext i
    rw [Measure.restrict_restrict measurableSet_Iic,hset]
  rw [he,←integral_indicator hb]
  apply integral_congr_ae
  filter_upwards [] with t
  by_cases ht:∀i,t i≤T
  · have hm:t∈box:=fun i _=>ht i
    simp only [if_pos ht,Set.indicator_of_mem hm]
  · have hm:t∉box:=by
      intro hc
      apply ht
      intro i
      exact hc i (mem_univ i)
    simp only [if_neg ht,Set.indicator_of_notMem hm]

end SHE.InitialOrdinaryNewestIntegration
