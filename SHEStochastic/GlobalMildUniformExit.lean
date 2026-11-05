module

public import SHEStochastic.VariableAgeUniformNorm
public import SHEStochastic.NativePhysicalState
public import SHEStochastic.GlobalHeatParameter
public import SHEStochastic.UniformCoefficientExit
public import SHEStochastic.AdaptedCanonicalPathTests
public import SHE.NativeContinuousPath

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.GlobalMildUniformExit
open MeasureTheory SHE SHE.StoppedFourier SHE.DyadicApproximation AddCircle Filter
open HeatParameterCover HeatParameterPullback StoppedPathPasting AdaptedCanonicalPathTests
open scoped NNReal ENNReal Topology

local instance : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance : Fact (0<(1:ℝ)) := ⟨zero_lt_one⟩

/-- Deterministic regularity of an actual mild path on any finite
horizon. Its normalized time parameter does not change its physical heat age. -/
theorem regular_path (H : ℝ≥0) (hH : 0<H) (x : Path H RealL2)
    (u : RealL2) (M : ℝ) (hM : 0≤M)
    (hu : L2ExtendedUniformNorm.value (haarAddCircle (T:=1)) u=ENNReal.ofReal M)
    (Y : C(Parameter,ℝ)) (hz : ∀ p, Y (HeatParameterCoordinates.zeroTime p)=0)
    (he : ∀ t : Time H, NativePhysicalState.push (x t)=
      PhysicalHeatState.state t.val (NativeHeatObservation.embed u)+
        PhysicalHeatParameterSection.value 2 Y (GlobalHeatParameter.normalized H hH t)) :
    Continuous (fun t ↦ L2ExtendedUniformNorm.realValue (haarAddCircle (T:=1)) (x t)) ∧
      ∀ t, L2ExtendedUniformNorm.value (haarAddCircle (T:=1)) (x t)≠⊤ := by
  let age (s : ShortTime) : ℝ := (H:ℝ)*s.val
  have ha : Continuous age := continuous_const.mul continuous_subtype_val
  have ha0 : age initialTime=0 := mul_zero _
  have han (s : ShortTime) : 0≤age s := mul_nonneg H.property s.property.1
  have hap (s : ShortTime) (hs : 0<s.val) : 0<age s := mul_pos hH hs
  have hd := NativePhysicalState.embed_bound u M
    ((L2ExtendedUniformNorm.le_ofReal_iff _ u M hM).mp hu.le)
  have h0 : L2ExtendedUniformNorm.value haarAddCircle
      (PhysicalHeatState.state 0 (NativeHeatObservation.embed u))=ENNReal.ofReal M := by
    rw [PhysicalHeatState.state_zero,←NativePhysicalState.push_eq_realPart,NativePhysicalState.uniform_norm_push,hu]
  have hj := GlobalHeatParameter.continuous_normalized H hH
  have hage (t : Time H) : age (GlobalHeatParameter.normalized H hH t)=t.val := by
    change (H:ℝ)*(t.val/(H:ℝ))=t.val
    field_simp [show (H:ℝ)≠0 from ne_of_gt hH]
  have hstate (t : Time H) : PhysicalHeatState.state (age (GlobalHeatParameter.normalized H hH t))
      (NativeHeatObservation.embed u)+PhysicalHeatParameterSection.value 2 Y (GlobalHeatParameter.normalized H hH t)=
        NativePhysicalState.push (x t) := by rw [hage]; exact (he t).symm
  constructor
  · have hc := (VariableAgeUniformNorm.continuous_realNorm age ha ha0 han hap
      (NativeHeatObservation.embed u) M hM hd h0 Y hz).comp hj
    convert hc using 1
    funext t
    exact (NativePhysicalState.real_uniform_norm_push _).symm.trans
      (congrArg (L2ExtendedUniformNorm.realValue (haarAddCircle (T:=2*Real.pi))) (hstate t).symm)
  · intro t
    rw [←NativePhysicalState.uniform_norm_push,he t]
    have hb := UniformExitEnvelope.bound (fun s ↦ PhysicalHeatState.state (age s) (NativeHeatObservation.embed u))
      M hM (fun s ↦ PhysicalHeatState.state_bound (han s) _ M hM hd) Y
      (GlobalHeatParameter.normalized H hH t)
    rw [hage] at hb
    exact ne_of_lt (hb.trans_lt ENNReal.ofReal_lt_top)

end SHEStochastic.GlobalMildUniformExit
