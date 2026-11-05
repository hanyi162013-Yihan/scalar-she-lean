module

public import SHE.InitialTerminalLevel
public import SHE.HistoryProductMeasure
public import SHE.PhysicalGapIntegration

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
namespace SHE.InitialTerminalFields
open Set MeasureTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories CutoffCarriers
open SmoothCylinders UniformSmooth PhysicalParentGeometry
open Classical
local instance initialTerminalFields_period:Fact (0<2*Real.pi):=⟨by positivity⟩
variable (R:ReferenceData)
variable (F:HeatCircle→WordRecursion.State 1→ℝ) (hF:UniformBoundedSmooth F)
variable (hFm:Measurable (fun z:HeatCircle×WordRecursion.State 1=>F z.1 z.2))
local notation "L"=>InitialTerminalLevel.level R F hF hFm

def lift (T:Icc R.base R.horizon) (k:ℕ) (p:History HeatCircle k):History (InitialTerminalLevel.Root R) k:=
  WordRootReindex.history (InitialTerminalLevel.fibre R T) k p

theorem lift_measurable (k:ℕ):Measurable (fun z:Icc R.base R.horizon×History HeatCircle k=>lift R z.1 k z.2):=by
  induction k with
  | zero=>exact measurable_id
  | succ k ih=>
    exact (ih.comp (measurable_fst.prodMk measurable_snd.fst)).prodMk measurable_snd.snd

variable {Ω:Type} [MeasurableSpace Ω] [MeasurableSpace CircleL2] [BorelSpace CircleL2]
variable (Λ:ℝ) (U V:Ω×ℝ→CircleL2) (XU XV:Ω×(ℝ×HeatCircle)→ℝ)

/-- Literal native terminal recursive word difference on the initial
output triangle, with its variable output terminal retained. -/
def point (k:ℕ) (T:Icc R.base R.horizon) (p:History HeatCircle k) (ω:Ω):ℝ:=
  let a:=lift R T k p
  if StrictHistory L k a then
    UncutSmoothWords.test L k a (JointWordAnalytic.state (carrier L k) Λ U V XU XV a ω ((carrier L k).terminal a))-
    UncutSmoothWords.test L k a (JointWordAnalytic.state (carrier L k) Λ U U XU XU a ω ((carrier L k).terminal a))
  else 0

variable (hU:Measurable U) (hV:Measurable V) (hXU:Measurable XU) (hXV:Measurable XV)
include hU hV hXU hXV in
theorem point_measurable (k:ℕ):
    Measurable (fun z:(Icc R.base R.horizon×History HeatCircle k)×Ω=>
      point R F hF hFm Λ U V XU XV k z.1.1 z.1.2 z.2):=by
  have hm:Measurable (fun z:(Icc R.base R.horizon×History HeatCircle k)×Ω=>
      (lift R z.1.1 k z.1.2,z.2)):=((lift_measurable R k).comp measurable_fst).prodMk measurable_snd
  have hn:=(InitialTerminalLevel.terminal_word_measurable R F hF hFm Λ U V XU XV hU hV hXU hXV k).comp hm
  have ho:=(InitialTerminalLevel.terminal_word_measurable R F hF hFm Λ U U XU XU hU hU hXU hXU k).comp hm
  exact (hn.sub ho).ite ((strictHistory_measurableSet L k).preimage ((lift_measurable R k).comp measurable_fst)) measurable_const

def value (k:ℕ) (T:Icc R.base R.horizon) (ω:Ω):ℝ:=
  ∫p,point R F hF hFm Λ U V XU XV k T p ω ∂historyMeasure R AddCircle.haarAddCircle k

include hU hV hXU hXV in
theorem value_measurable (k:ℕ):
    Measurable (fun z:Icc R.base R.horizon×Ω=>value R F hF hFm Λ U V XU XV k z.1 z.2):=by
  have hm:Measurable (fun z:(Icc R.base R.horizon×Ω)×History HeatCircle k=>
      point R F hF hFm Λ U V XU XV k z.1.1 z.2 z.1.2):=
    (point_measurable R F hF hFm Λ U V XU XV hU hV hXU hXV k).comp
      ((measurable_fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd)
  exact (hm.stronglyMeasurable.integral_prod_right' (ν:=historyMeasure R AddCircle.haarAddCircle k)).measurable

end SHE.InitialTerminalFields
