module
public import SHE.NativeContinuousPath
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace SHE.ContinuousPathCylindricalLaw
open MeasureTheory Set
open scoped NNReal ENNReal
variable {Ω Ω' E:Type*}[MeasurableSpace Ω][MeasurableSpace Ω']
variable [NormedAddCommGroup E][InnerProductSpace ℝ E][CompleteSpace E]
variable [MeasurableSpace E][BorelSpace E][SecondCountableTopology E]
variable(H:ℝ≥0)(μ:Measure Ω)(ν:Measure Ω')
variable(U:ℝ≥0→Ω→E)(V:ℝ≥0→Ω'→E)
variable(hc:∀ω,Continuous (fun t=>U t ω))(hd:∀ω,Continuous (fun t=>V t ω))
variable(hU:Measurable (Function.uncurry U))(hV:Measurable (Function.uncurry V))

include hU hV in
theorem paths
    (hLaw:μ.map (fun ω=>fun t=>U t ω)=ν.map (fun ω=>fun t=>V t ω)):
    μ.map (NativeContinuousPath.path H U hc)=ν.map (NativeContinuousPath.path H V hd):=by
  let ev:C(Icc (0:ℝ) (H:ℝ),E)→(Icc (0:ℝ) (H:ℝ)→E):=fun f t=>f t
  have he:Measurable ev:=measurable_pi_iff.mpr (fun t=>ContinuousMap.measurable_eval t)
  have hco:MeasurableSpace.comap ev (inferInstance:MeasurableSpace (Icc (0:ℝ) (H:ℝ)→E))=
      (inferInstance:MeasurableSpace C(Icc (0:ℝ) (H:ℝ),E)):=by
    rw [MeasurableSpace.pi,MeasurableSpace.comap_iSup]
    simpa only [MeasurableSpace.comap_comp,Function.comp_def] using
      (ContinuousMap.measurableSpace_eq_iSup_comap_eval (X:=Icc (0:ℝ) (H:ℝ)) (Y:=E)).symm
  have hm:Measurable (fun f:ℝ≥0→E=>fun t:Icc (0:ℝ) (H:ℝ)=>f t.val.toNNReal):=
    measurable_pi_iff.mpr (fun t=>measurable_pi_apply t.val.toNNReal)
  have hh:=congrArg (fun P:Measure (ℝ≥0→E)=>P.map (fun f=>fun t:Icc (0:ℝ) (H:ℝ)=>f t.val.toNNReal)) hLaw
  have hu:Measurable (fun ω=>fun t=>U t ω):=by
    apply measurable_pi_iff.mpr
    intro t
    exact hU.comp (show Measurable (fun ω:Ω=>(t,ω)) from measurable_const.prodMk measurable_id)
  have hv:Measurable (fun ω=>fun t=>V t ω):=by
    apply measurable_pi_iff.mpr
    intro t
    exact hV.comp (show Measurable (fun ω:Ω'=>(t,ω)) from measurable_const.prodMk measurable_id)
  rw [Measure.map_map hm hu,Measure.map_map hm hv] at hh
  have hh':(μ.map (NativeContinuousPath.path H U hc)).map ev=
      (ν.map (NativeContinuousPath.path H V hd)).map ev:=by
    rw [Measure.map_map he (NativeContinuousPath.measurable_path H U hc hU),
      Measure.map_map he (NativeContinuousPath.measurable_path H V hd hV)]
    exact hh
  ext s hs
  have hs':@MeasurableSet C(Icc (0:ℝ) (H:ℝ),E)
      (MeasurableSpace.comap ev inferInstance) s:=hco.symm ▸ hs
  obtain ⟨t,ht,rfl⟩:=hs'
  have hval:=congrArg (fun P:Measure (Icc (0:ℝ) (H:ℝ)→E)=>P t) hh'
  rw [Measure.map_apply he ht,Measure.map_apply he ht] at hval
  exact hval

local instance : MeasurableSpace (Lp E 2 (SHE.timeMeasure (H:ℝ))):=borel _
local instance : BorelSpace (Lp E 2 (SHE.timeMeasure (H:ℝ))):=⟨rfl⟩

include hU hV in
theorem integrated
    (hLaw:μ.map (fun ω=>fun t=>U t ω)=ν.map (fun ω=>fun t=>V t ω)):
    μ.map (NativeContinuousPath.integrated H U hc)=ν.map (NativeContinuousPath.integrated H V hd):=by
  have hh:=congrArg (fun P:Measure C(Icc (0:ℝ) (H:ℝ),E)=>
    P.map (ContinuousMap.toLp (E:=E) 2 (SHE.timeMeasure (H:ℝ)) ℝ)) (paths H μ ν U V hc hd hU hV hLaw)
  rw [Measure.map_map (ContinuousMap.toLp (E:=E) 2 (SHE.timeMeasure (H:ℝ)) ℝ).continuous.measurable
      (NativeContinuousPath.measurable_path H U hc hU),
    Measure.map_map (ContinuousMap.toLp (E:=E) 2 (SHE.timeMeasure (H:ℝ)) ℝ).continuous.measurable
      (NativeContinuousPath.measurable_path H V hd hV)] at hh
  exact hh
end SHE.ContinuousPathCylindricalLaw
