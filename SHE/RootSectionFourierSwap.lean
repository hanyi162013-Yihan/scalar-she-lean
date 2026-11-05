module
public import SHE.RootDensityHistory
public import SHE.NativeScalarFourierWeight
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
namespace SHE.RootSectionFourierSwap
open MeasureTheory Set AddCircle StoppedFourier CutoffWordLevel CutoffWordHistories HistoryProductMeasure
local instance : Fact (0<2*Real.pi):=⟨by positivity⟩
variable {Ω:Type*}[MeasurableSpace Ω]

/-- Exact original-root/old-time Fubini for a bounded signed root test.
Only original-history absolute mass is used; no pointwise old-time
integrability or new exceptional-version choice is assumed. -/
theorem weighted(R:ReferenceData)(k:ℕ)(F:Ω×History HeatCircle k→ℝ)(ω:Ω)
    (hi:Integrable (fun h=>F (ω,h)) (historyMeasure R haarAddCircle k))
    (g:HeatCircle→ℝ)(hg:Measurable g)(B:ℝ)(hb:∀x,‖g x‖≤B):
    Integrable (fun t:Fin k→ℝ=>∫x:HeatCircle,g x*
      (∫w:Fin k→HeatCircle,F (ω,separated k (x,t,w))
        ∂Measure.pi (fun _=>haarAddCircle)) ∂haarAddCircle)
      (Measure.pi (fun _=>volume.restrict (Ioc R.base R.horizon))) ∧
    (∫x:HeatCircle,g x*RootSectionAverage.average R k F (ω,x) ∂haarAddCircle)=
      ∫t:Fin k→ℝ,∫x:HeatCircle,g x*
        (∫w:Fin k→HeatCircle,F (ω,separated k (x,t,w))
          ∂Measure.pi (fun _=>haarAddCircle)) ∂haarAddCircle
        ∂Measure.pi (fun _=>volume.restrict (Ioc R.base R.horizon)):=by
  let T:=Measure.pi (fun _:Fin k=>volume.restrict (Ioc R.base R.horizon))
  let W:=Measure.pi (fun _:Fin k=>haarAddCircle (T:=2*Real.pi))
  have hp:=separated_measurePreserving R (haarAddCircle:Measure HeatCircle) k
  have hG:Integrable (fun z:HeatCircle×((Fin k→ℝ)×(Fin k→HeatCircle))=>
      F (ω,separated k z)) (haarAddCircle.prod (T.prod W)):=
    (hp.integrable_comp hi.aestronglyMeasurable).mpr hi
  have hA:Integrable (fun z:(HeatCircle×(Fin k→ℝ))×(Fin k→HeatCircle)=>
      F (ω,separated k (z.1.1,z.1.2,z.2))) ((haarAddCircle.prod T).prod W):=
    (measurePreserving_prodAssoc haarAddCircle T W).integrable_comp_of_integrable hG
  have hB:=hA.integral_prod_left.bdd_mul
    (hg.comp measurable_fst).aestronglyMeasurable (ae_of_all _ (fun z=>hb z.1))
  refine ⟨hB.integral_prod_right,?_⟩
  calc
    _=∫x:HeatCircle,∫t:Fin k→ℝ,g x*
        (∫w:Fin k→HeatCircle,F (ω,separated k (x,t,w)) ∂W) ∂T ∂haarAddCircle:=by
      apply integral_congr_ae
      filter_upwards with x
      exact (integral_const_mul (g x) _).symm
    _=_:=integral_integral_swap hB

/-- The literal real Fourier test of the retained-root average equals
the old-time integral of the corresponding old-space Fourier tests. -/
theorem fourier(R:ReferenceData)(k:ℕ)(F:Ω×History HeatCircle k→ℝ)(ω:Ω)
    (hi:Integrable (fun h=>F (ω,h)) (historyMeasure R haarAddCircle k))
    (w:ℝ)(a:ℂ→L[ℝ]ℝ)(l:ℤ):
    Integrable (fun t:Fin k→ℝ=>∫x:HeatCircle,NativeScalarFourierWeight.value w a l x*
      (∫y:Fin k→HeatCircle,F (ω,separated k (x,t,y))
        ∂Measure.pi (fun _=>haarAddCircle)) ∂haarAddCircle)
      (Measure.pi (fun _=>volume.restrict (Ioc R.base R.horizon))) ∧
    w*a (fourierCoeff (fun x:HeatCircle=>(RootSectionAverage.average R k F (ω,x):ℂ)) l)=
      ∫t:Fin k→ℝ,∫x:HeatCircle,NativeScalarFourierWeight.value w a l x*
        (∫y:Fin k→HeatCircle,F (ω,separated k (x,t,y))
          ∂Measure.pi (fun _=>haarAddCircle)) ∂haarAddCircle
        ∂Measure.pi (fun _=>volume.restrict (Ioc R.base R.horizon)):=by
  have hswap:=weighted R k F ω hi (NativeScalarFourierWeight.value w a l)
    (NativeScalarFourierWeight.measurable w a l) (‖w‖*‖a‖)
    (NativeScalarFourierWeight.bound w a l)
  refine ⟨hswap.1,?_⟩
  rw [←NativeScalarFourierWeight.integral _
    (RootDensityHistory.average_integrable R haarAddCircle k F ω hi) w a l]
  exact hswap.2
end SHE.RootSectionFourierSwap
