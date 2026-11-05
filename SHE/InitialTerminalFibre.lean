module

public import SHE.InitialTerminalFields
public import SHE.WordRootState
public import SHE.HistoryHorizonIntegration

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
namespace SHE.InitialTerminalFibre
open Set MeasureTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories CutoffCarriers
  PhysicalParentGeometry SmoothCylinders UniformSmooth
open Classical
local instance initialTerminalFibre_period:Fact (0<2*Real.pi):=⟨by positivity⟩
variable (R:ReferenceData) (F:HeatCircle→WordRecursion.State 1→ℝ) (hF:UniformBoundedSmooth F)
variable (hFm:Measurable (fun z:HeatCircle×WordRecursion.State 1=>F z.1 z.2))
variable {Q:ReferenceData} (K:Level Q HeatCircle 1) (T:Icc R.base R.horizon)
variable (hb:Q.base=R.base) (hT:∀x,K.terminal x=(T:ℝ))
variable (hZ:∀x,K.observations.observations x=fun _=>Observation.mk T T x)
variable (hc:Q.reference=R.reference) (hV:Q.totalVariance=R.totalVariance) (hK:∀x,K.test x=F x)
variable {Ω:Type} [MeasurableSpace Ω] [MeasurableSpace CircleL2] [BorelSpace CircleL2]
variable (Λ:ℝ) (U V:Ω×ℝ→CircleL2) (XU XV:Ω×(ℝ×HeatCircle)→ℝ)
include hb hT hZ hc hV hK

/-- Pointwise exact variable-output fibre identity, including literal
joint current states and the original strict-history zero extension. -/
theorem point (k:ℕ) (p:History HeatCircle k) (ω:Ω):
    InitialTerminalFields.point R F hF hFm Λ U V XU XV k T p ω=
      if StrictHistory K k p then
        UncutSmoothWords.test K k p (JointWordAnalytic.state (carrier K k) Λ U V XU XV p ω ((carrier K k).terminal p))-
        UncutSmoothWords.test K k p (JointWordAnalytic.state (carrier K k) Λ U U XU XU p ω ((carrier K k).terminal p)) else 0:=by
  let L:=InitialTerminalLevel.level R F hF hFm
  let f:=InitialTerminalLevel.fibre R T
  have hs:=WordRootReindex.strict_iff L K f hb hT k p
  have ht:=WordRootReindex.test L K f hb hT hZ hc hV hK k p
  have hn:=WordRootReindex.current L K f hb hT hZ Λ U V XU XV k p ω
  have ho:=WordRootReindex.current L K f hb hT hZ Λ U U XU XU k p ω
  unfold InitialTerminalFields.point InitialTerminalFields.lift
  dsimp only
  change (if StrictHistory L k (WordRootReindex.history f k p) then _ else 0)=_
  rw [←hs]
  split_ifs
  · rw [←ht,←hn,←ho]
  · rfl

include hb hT hZ hc hV hK in
/-- Exact ORIGINAL history average at output T. Enlarging the ambient
reference horizon changes no actual initial-triangle value. -/
theorem value (hQ:Q.horizon=(T:ℝ)) (k:ℕ) (ω:Ω):
    InitialTerminalFields.value R F hF hFm Λ U V XU XV k T ω=
      ∫p:History HeatCircle k,if StrictHistory K k p then
        UncutSmoothWords.test K k p (JointWordAnalytic.state (carrier K k) Λ U V XU XV p ω ((carrier K k).terminal p))-
        UncutSmoothWords.test K k p (JointWordAnalytic.state (carrier K k) Λ U U XU XU p ω ((carrier K k).terminal p)) else 0
        ∂historyMeasure Q AddCircle.haarAddCircle k:=by
  rw [InitialTerminalFields.value]
  simp_rw [point R F hF hFm K T hb hT hZ hc hV hK Λ U V XU XV k _ ω]
  apply (HistoryHorizonIntegration.integral_eq Q R hb (by rw [hQ];exact T.2.2)
    AddCircle.haarAddCircle k _ _).symm
  intro p hp
  have hn:¬StrictHistory K k p:=by
    intro hs
    apply hp
    exact HistoryHorizonIntegration.strict_mem K Q.horizon (fun x=>by rw [hQ,hT]) k p hs
  simp only [if_neg hn]

end SHE.InitialTerminalFibre
