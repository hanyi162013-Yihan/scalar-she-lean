module
public import SHE.NativePathLawComparison
public import SHE.NativePairClock
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1600000
namespace SHE.NativePathLawClock
open MeasureTheory Set
open scoped NNReal ENNReal
variable{Ω Ω' E D:Type*}[MeasurableSpace Ω][MeasurableSpace Ω']
variable[NormedAddCommGroup E][InnerProductSpace ℝ E][CompleteSpace E]
variable[MeasurableSpace E][BorelSpace E][SecondCountableTopology E]
variable[NormedAddCommGroup D][InnerProductSpace ℝ D][CompleteSpace D]
variable[MeasurableSpace D][BorelSpace D][SecondCountableTopology D]
variable(H T:ℝ≥0)(τ:ℝ≥0→ℝ≥0)(hτ:Continuous τ)(hbound:∀s,s≤T→τ s≤H)

def timeMap(t:Icc (0:ℝ) (T:ℝ)):Icc (0:ℝ) (H:ℝ):=
  ⟨(τ t.val.toNNReal:ℝ),⟨(τ t.val.toNNReal).2,by
    apply_mod_cast hbound t.val.toNNReal
    exact (Real.toNNReal_le_iff_le_coe).mpr t.2.2⟩⟩

include hτ in
theorem timeMap_continuous:Continuous (timeMap H T τ hbound):=by
  apply Continuous.subtype_mk
  exact continuous_subtype_val.comp (hτ.comp (continuous_real_toNNReal.comp continuous_subtype_val))

def mapPath(L:E→L[ℝ]D)(p:C(Icc (0:ℝ) (H:ℝ),E)):C(Icc (0:ℝ) (T:ℝ),D):=
  ⟨fun t=>L (p (timeMap H T τ hbound t)),
    L.continuous.comp (p.continuous.comp (timeMap_continuous H T τ hτ hbound))⟩

theorem mapPath_measurable(L:E→L[ℝ]D):Measurable (mapPath H T τ hτ hbound L):=by
  apply ContinuousMap.measurable_iff_eval.mpr
  intro t
  exact L.continuous.measurable.comp (ContinuousMap.measurable_eval (timeMap H T τ hbound t))

include hbound in
/-- Deterministic clock and state maps preserve actual continuous path
laws on their genuine compact output interval. -/
theorem law
    (μ:Measure Ω)(ν:Measure Ω')[IsProbabilityMeasure μ][IsProbabilityMeasure ν]
    (U:ℝ≥0→Ω→E)(V:ℝ≥0→Ω'→E)
    (hc:∀ω,Continuous (fun t=>U t ω))(hd:∀ω,Continuous (fun t=>V t ω))
    (hU:Measurable (Function.uncurry U))(hV:Measurable (Function.uncurry V))
    (L:E→L[ℝ]D)
    (he:NativePathLawComparison.law H μ U hc=NativePathLawComparison.law H ν V hd):
    NativePathLawComparison.law T μ (fun t ω=>L (U (τ t) ω))
        (fun ω=>L.continuous.comp ((hc ω).comp hτ))=
      NativePathLawComparison.law T ν (fun t ω=>L (V (τ t) ω))
        (fun ω=>L.continuous.comp ((hd ω).comp hτ)):=by
  apply Subtype.ext
  have hh:=congrArg (fun p:ProbabilityMeasure C(Icc (0:ℝ) (H:ℝ),E)=>
    (p:Measure _).map (mapPath H T τ hτ hbound L)) he
  change (μ.map (NativeContinuousPath.path H U hc)).map (mapPath H T τ hτ hbound L)=
    (ν.map (NativeContinuousPath.path H V hd)).map (mapPath H T τ hτ hbound L) at hh
  rw [Measure.map_map (mapPath_measurable H T τ hτ hbound L) (NativeContinuousPath.measurable_path H U hc hU),
    Measure.map_map (mapPath_measurable H T τ hτ hbound L) (NativeContinuousPath.measurable_path H V hd hV)] at hh
  have hu:mapPath H T τ hτ hbound L ∘ NativeContinuousPath.path H U hc=
      NativeContinuousPath.path T (fun t ω=>L (U (τ t) ω))
        (fun ω=>L.continuous.comp ((hc ω).comp hτ)):=by
    funext ω
    apply ContinuousMap.ext
    intro t
    change L (U (Real.toNNReal (τ t.val.toNNReal:ℝ)) ω)=_
    rw [Real.toNNReal_coe]
    rfl
  have hv:mapPath H T τ hτ hbound L ∘ NativeContinuousPath.path H V hd=
      NativeContinuousPath.path T (fun t ω=>L (V (τ t) ω))
        (fun ω=>L.continuous.comp ((hd ω).comp hτ)):=by
    funext ω
    apply ContinuousMap.ext
    intro t
    change L (V (Real.toNNReal (τ t.val.toNNReal:ℝ)) ω)=_
    rw [Real.toNNReal_coe]
    rfl
  rw [hu,hv] at hh
  exact hh
end SHE.NativePathLawClock

namespace SHE.NativePathLawClock
open MeasureTheory LowBands
open scoped NNReal ENNReal
local instance : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩
local instance : MeasurableSpace StateL2:=borel _
local instance : BorelSpace StateL2:=⟨rfl⟩
local instance : SecondCountableTopology CircleHeat.CircleL2:=
  (_root_.fourierBasis (T:=(1:ℝ))).repr.toHomeomorph.secondCountableTopology
local instance : SecondCountableTopology StateL2:=
  FiniteHaar.realCircleIdentification.toHomeomorph.secondCountableTopology
variable{Ω Ω' D:Type*}[MeasurableSpace Ω][MeasurableSpace Ω']
variable[NormedAddCommGroup D][InnerProductSpace ℝ D][CompleteSpace D]
variable[MeasurableSpace D][BorelSpace D][SecondCountableTopology D]
/-- The actual native time change, including any continuous linear
state realization, carries the proved smooth path law unchanged. -/
theorem native (H:ℝ≥0)(μ:Measure Ω)(ν:Measure Ω')[IsProbabilityMeasure μ][IsProbabilityMeasure ν]
    (U:ℝ≥0→Ω→StateL2)(V:ℝ≥0→Ω'→StateL2)
    (hc:∀ω,Continuous (fun t=>U t ω))(hd:∀ω,Continuous (fun t=>V t ω))
    (hU:Measurable (Function.uncurry U))(hV:Measurable (Function.uncurry V))
    (L:StateL2→L[ℝ]D)
    (he:NativePathLawComparison.law H μ U hc=NativePathLawComparison.law H ν V hd):
    NativePathLawComparison.law (NativeClock.rate*H) μ
        (fun t ω=>L (NativePairClock.path U t ω))
        (fun ω=>L.continuous.comp (NativePairClock.path_continuous U hc ω))=
      NativePathLawComparison.law (NativeClock.rate*H) ν
        (fun t ω=>L (NativePairClock.path V t ω))
        (fun ω=>L.continuous.comp (NativePairClock.path_continuous V hd ω)):=by
  have ht:Continuous NativeClock.time:=PredictableTimeDilation.clock_symm_continuous NativeClock.rate NativeClock.rate_pos
  have hb:∀s:ℝ≥0,s≤NativeClock.rate*H→NativeClock.time s≤H:=
    fun s hs=>ClockedPairIntegral.time_le NativeClock.rate NativeClock.rate_pos H hs
  exact law H (NativeClock.rate*H) NativeClock.time ht hb μ ν U V hc hd hU hV L he
end SHE.NativePathLawClock
