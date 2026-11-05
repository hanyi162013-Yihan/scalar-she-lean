module
public import SHE.NativeContinuousPath
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.Topology.ContinuousMap.Compact
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace SHE.ContinuousPathRestriction
open Set MeasureTheory
open scoped NNReal
variable {E:Type*}[MetricSpace E][CompleteSpace E][SecondCountableTopology E]
  [MeasurableSpace E][BorelSpace E]

abbrev Interval(H:ℝ≥0):=Icc (0:ℝ) (H:ℝ)

def prefixTime(v h:ℝ≥0):C(Interval v,Interval (v+h)) where
  toFun t:=⟨t.val,by
    constructor
    · exact t.property.1
    · simpa only [NNReal.coe_add] using le_trans t.property.2 (le_add_of_nonneg_right h.coe_nonneg)⟩
  continuous_toFun:=continuous_subtype_val.subtype_mk _

def futureTime(v h:ℝ≥0):C(Interval h,Interval (v+h)) where
  toFun t:=⟨(v:ℝ)+t.val,by
    constructor
    · exact add_nonneg v.coe_nonneg t.property.1
    · change (v:ℝ)+t.val≤(v:ℝ)+(h:ℝ)
      linarith only [t.property.2]⟩
  continuous_toFun:=(continuous_const.add continuous_subtype_val).subtype_mk _

def past(v h:ℝ≥0)(f:C(Interval (v+h),E)):C(Interval v,E):=f.comp (prefixTime v h)
def future(v h:ℝ≥0)(f:C(Interval (v+h),E)):C(Interval h,E):=f.comp (futureTime v h)
def split(v h:ℝ≥0)(f:C(Interval (v+h),E)):
    C(Interval v,E)×C(Interval h,E):=(past v h f,future v h f)

theorem continuous_past(v h:ℝ≥0):Continuous (past (E:=E) v h):=
  ContinuousMap.continuous_precomp (prefixTime v h)
theorem continuous_future(v h:ℝ≥0):Continuous (future (E:=E) v h):=
  ContinuousMap.continuous_precomp (futureTime v h)
theorem continuous_split(v h:ℝ≥0):Continuous (split (E:=E) v h):=
  (continuous_past v h).prodMk (continuous_future v h)

/-- The prefix and shifted future determine every point of the actual
full continuous path, including their shared endpoint. -/
theorem split_injective(v h:ℝ≥0):Function.Injective (split (E:=E) v h):=by
  intro f g he
  ext t
  by_cases ht:t.val≤(v:ℝ)
  · let s:Interval v:=⟨t.val,t.property.1,ht⟩
    have hh:=congrArg (fun p:C(Interval v,E)×C(Interval h,E)=>p.1 s) he
    exact hh
  · let s:Interval h:=⟨t.val-(v:ℝ),by
      constructor
      · linarith only [not_le.mp ht]
      · have ht':t.val≤(v:ℝ)+(h:ℝ):=by simpa only [NNReal.coe_add] using t.property.2
        linarith only [ht']⟩
    have hh:=congrArg (fun p:C(Interval v,E)×C(Interval h,E)=>p.2 s) he
    have hs:futureTime v h s=t:=by
      apply Subtype.ext
      change (v:ℝ)+(t.val-(v:ℝ))=t.val
      ring
    change f (futureTime v h s)=g (futureTime v h s) at hh
    simpa only [hs] using hh

/-- Restriction is a genuine Borel measurable embedding, so no arbitrary
concatenation needs to be selected on incompatible segment pairs. -/
theorem embedding(v h:ℝ≥0):MeasurableEmbedding (split (E:=E) v h):=
  (continuous_split v h).measurableEmbedding (split_injective v h)

theorem map_injective(v h:ℝ≥0):
    Function.Injective (Measure.map (split (E:=E) v h)):=
  (embedding v h).map_injective
end SHE.ContinuousPathRestriction
