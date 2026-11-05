module

public import SHEStochastic.PhysicalHeatState

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.VariableAgeUniformNorm
open MeasureTheory SHE SHE.StoppedFourier AddCircle Filter Set
open HeatParameterCover HeatParameterPullback
open scoped ENNReal Topology

local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩

/-- Uniform-norm continuity is unaffected by a positive continuous
change of heat age. The heat orbit itself need only be L2 continuous
at the initial time. -/
theorem continuous_norm (age : ShortTime → ℝ) (ha : Continuous age)
    (ha0 : age initialTime=0) (han : ∀ t, 0≤age t)
    (hap : ∀ t, 0<t.val → 0<age t)
    (d : CircleL2) (M : ℝ) (hM : 0≤M)
    (hd : ∀ᵐ x ∂haarAddCircle, ‖d x‖≤M)
    (h0 : L2ExtendedUniformNorm.value haarAddCircle (PhysicalHeatState.state 0 d)=ENNReal.ofReal M)
    (Y : C(Parameter,ℝ)) (hz : ∀ p, Y (HeatParameterCoordinates.zeroTime p)=0) :
    Continuous (fun t : ShortTime ↦ L2ExtendedUniformNorm.value haarAddCircle
      (PhysicalHeatState.state (age t) d+PhysicalHeatParameterSection.value 2 Y t)) := by
  rw [continuous_iff_continuousAt]
  intro t
  by_cases ht : t.val=0
  · have he : t=initialTime := Subtype.ext ht
    subst t
    apply UniformExitEnvelope.initial_norm_continuity (fun s ↦ PhysicalHeatState.state (age s) d)
      ((PhysicalHeatState.continuous_state d).comp ha).continuousAt M hM
      (fun s ↦ PhysicalHeatState.state_bound (han s) d M hM hd) ?_ Y hz
    rw [ha0]
    exact h0
  · have hpos := hap t (lt_of_le_of_ne t.property.1 (Ne.symm ht))
    have hc : ContinuousAt (fun s : ShortTime ↦ PhysicalHeatState.positiveUniform (age s) d) t :=
      ((PhysicalHeatState.continuousOn_positiveUniform d).continuousAt (Ioi_mem_nhds hpos)).comp ha.continuousAt
    have hh := ENNReal.continuous_ofReal.continuousAt.comp
      (hc.add (PhysicalHeatParameterSection.uniformContinuous_value ∞ Y).continuous.continuousAt).norm
    apply hh.congr_of_eventuallyEq
    have hn : ∀ᶠ s : ShortTime in 𝓝 t, 0<age s := (ha.tendsto t) (eventually_gt_nhds hpos)
    filter_upwards [hn] with s hs
    exact PhysicalHeatState.mild_norm_eq hs d Y s

theorem continuous_realNorm (age : ShortTime → ℝ) (ha : Continuous age)
    (ha0 : age initialTime=0) (han : ∀ t, 0≤age t)
    (hap : ∀ t, 0<t.val → 0<age t)
    (d : CircleL2) (M : ℝ) (hM : 0≤M)
    (hd : ∀ᵐ x ∂haarAddCircle, ‖d x‖≤M)
    (h0 : L2ExtendedUniformNorm.value haarAddCircle (PhysicalHeatState.state 0 d)=ENNReal.ofReal M)
    (Y : C(Parameter,ℝ)) (hz : ∀ p, Y (HeatParameterCoordinates.zeroTime p)=0) :
    Continuous (fun t : ShortTime ↦ L2ExtendedUniformNorm.realValue haarAddCircle
      (PhysicalHeatState.state (age t) d+PhysicalHeatParameterSection.value 2 Y t)) := by
  rw [continuous_iff_continuousAt]
  intro t
  apply (ENNReal.continuousAt_toReal ?_).comp
    (continuous_norm age ha ha0 han hap d M hM hd h0 Y hz).continuousAt
  exact ne_of_lt ((UniformExitEnvelope.bound (fun s ↦ PhysicalHeatState.state (age s) d) M hM
    (fun s ↦ PhysicalHeatState.state_bound (han s) d M hM hd) Y t).trans_lt ENNReal.ofReal_lt_top)

end SHEStochastic.VariableAgeUniformNorm
