module

public import SHE.WordRootReindex
public import SHE.JointWordAnalytic
public import SHE.PhysicalParentGeometry

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
namespace SHE.InitialTerminalLevel
open Set MeasureTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories CutoffCarriers
open SmoothCylinders UniformSmooth
variable (R:ReferenceData)
abbrev Root := Icc R.base R.horizon × HeatCircle
variable (F:HeatCircle→WordRecursion.State 1→ℝ) (hF:UniformBoundedSmooth F)
variable (hFm:Measurable (fun z:HeatCircle×WordRecursion.State 1=>F z.1 z.2))

/-- A scalar native root whose terminal is itself a measurable output
parameter, under one FIXED reference horizon. -/
def level:Level R (Root R) 1 where
  observations:={
    observations:=fun z _=>Observation.mk z.1 z.1 z.2
    stop_measurable:=fun _=>measurable_subtype_coe.comp measurable_fst
    target_measurable:=fun _=>measurable_subtype_coe.comp measurable_fst
    center_measurable:=fun _=>measurable_snd}
  terminal:=fun z=>z.1
  terminal_measurable:=measurable_subtype_coe.comp measurable_fst
  terminal_base:=fun z=>z.1.2.1
  terminal_horizon:=fun z=>z.1.2.2
  targets_after:=fun _ _=>le_rfl
  stops_after:=fun _ _=>le_rfl
  test:=fun z=>F z.2
  test_uniform:=uniform_reindex hF Prod.snd
  test_measurable:=hFm.comp (measurable_fst.snd.prodMk measurable_snd)

def fibre (T:Icc R.base R.horizon):HeatCircle→Root R:=fun x=>(T,x)

theorem fibre_measurable (T:Icc R.base R.horizon):Measurable (fibre R T):=
  measurable_const.prodMk measurable_id

variable {Q:ReferenceData} (K:Level Q HeatCircle 1)
variable (T:Icc R.base R.horizon) (hb:Q.base=R.base)
variable (hT:∀x,K.terminal x=(T:ℝ))
variable (hZ:∀x,K.observations.observations x=fun _=>Observation.mk T T x)
variable (hc:Q.reference=R.reference) (hV:Q.totalVariance=R.totalVariance)
variable (hK:∀x,K.test x=F x)

include hb hT hZ hc hV hK in
/-- Exact canonical fixed-terminal fibre equality, including every
recursive insertion, covariance, native leaf, and zero extension. -/
theorem test_fibre (k:ℕ) (p:History HeatCircle k):
    UncutSmoothWords.test K k p=
      UncutSmoothWords.test (level R F hF hFm) k (WordRootReindex.history (fibre R T) k p):=by
  exact WordRootReindex.test (level R F hF hFm) K (fibre R T) hb hT hZ hc hV hK k p

/-- The actual terminal-current word under the fixed-horizon variable
root is jointly Borel before output-time integration. -/
theorem terminal_word_measurable {Ω:Type} [MeasurableSpace Ω]
    [MeasurableSpace CircleL2] [BorelSpace CircleL2] (Λ:ℝ)
    (U V:Ω×ℝ→CircleL2) (XU XV:Ω×(ℝ×HeatCircle)→ℝ)
    (hU:Measurable U) (hV:Measurable V) (hXU:Measurable XU) (hXV:Measurable XV) (k:ℕ):
    Measurable (fun z:History (Root R) k×Ω=>
      UncutSmoothWords.test (level R F hF hFm) k z.1
        (JointWordAnalytic.state (carrier (level R F hF hFm) k) Λ U V XU XV z.1 z.2
          ((carrier (level R F hF hFm) k).terminal z.1))):=by
  have hs:Measurable (fun z:History (Root R) k×Ω=>
      JointWordAnalytic.state (carrier (level R F hF hFm) k) Λ U V XU XV z.1 z.2
        ((carrier (level R F hF hFm) k).terminal z.1)):=by
    exact (JointWordAnalytic.state_measurable (carrier (level R F hF hFm) k) Λ hU hV hXU hXV).comp
      (measurable_id.prodMk ((carrier (level R F hF hFm) k).terminal_measurable.comp measurable_fst))
  exact (UncutSmoothWords.test_measurable (level R F hF hFm) k).comp (measurable_fst.prodMk hs)

end SHE.InitialTerminalLevel
