module
public import SHE.NativeClock
public import SHE.PredictableTime
public import Mathlib.MeasureTheory.Integral.Prod
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace SHE.NativeVolterraFields
open MeasureTheory Set PredictableL2 NativeHeatObservation StoppedFourier DyadicApproximation FiniteHaar
open scoped NNReal ENNReal
local instance : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance : SecondCountableTopology CircleHeat.CircleL2 :=
  (fourierBasis (T:=1)).repr.toHomeomorph.secondCountableTopology
local instance : SecondCountableTopology RealL2 :=
  realCircleIdentification.toHomeomorph.secondCountableTopology
local instance : MeasurableSpace RealL2:=borel _
local instance : BorelSpace RealL2:=⟨rfl⟩
variable {Ω:Type*}[MeasurableSpace Ω]

theorem measurable (Λ:ℝ)(U:ℝ≥0→Ω→RealL2)
    (hU:Measurable (Function.uncurry U))(t:ℝ≥0):
    Measurable (fun ω=>NativeClock.volterra Λ (fun s=>U s ω) t):=by
  have hu:Measurable (fun z:ℝ×Ω=>U z.1.toNNReal z.2):=
    hU.comp (measurable_fst.real_toNNReal.prodMk measurable_snd)
  have hh:=RealHeat.continuous_realHeat_action.measurable.comp
    ((show Measurable (fun z:ℝ×Ω=>((t:ℝ)-z.1)/timeScale) by fun_prop).prodMk hu)
  have he:Measurable (fun z:ℝ×Ω=>Real.exp (-Λ*((t:ℝ)-z.1))):=by fun_prop
  have hm:StronglyMeasurable (fun z:ℝ×Ω=>Real.exp (-Λ*((t:ℝ)-z.1)) •
      NativeHeatObservation.heat ((t:ℝ)-z.1) (U z.1.toNNReal z.2)):=
    (he.smul hh).stronglyMeasurable
  have hm':StronglyMeasurable (Function.uncurry (fun (r:ℝ) (ω:Ω)=>
      Real.exp (-Λ*((t:ℝ)-r)) • NativeHeatObservation.heat ((t:ℝ)-r) (U r.toNNReal ω))):=hm
  have hi:=hm'.integral_prod_left (μ:=volume.restrict (Ioc (0:ℝ) (t:ℝ)))
  convert! hi.measurable using 1
  funext ω
  exact intervalIntegral.integral_of_le (μ:=(volume:Measure ℝ))
    (f:=fun s:ℝ=>Real.exp (-Λ*((t:ℝ)-s)) •
      NativeHeatObservation.heat ((t:ℝ)-s) (U s.toNNReal ω)) t.2
end SHE.NativeVolterraFields
