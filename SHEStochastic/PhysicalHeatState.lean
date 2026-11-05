module

public import SHEStochastic.PhysicalHeatSmoothing
public import SHEStochastic.HeatUniformBound
public import SHEStochastic.UniformExitEnvelope

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section

namespace SHEStochastic.PhysicalHeatState
open MeasureTheory SHE SHE.StoppedFourier SHE.PhysicalProfile AddCircle Filter Set
open HeatParameterCover HeatParameterPullback
open scoped ENNReal Topology

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

/-- The physical real L2 heat state, defined at time zero as well. -/
def state (r : ℝ) (d : CircleL2) : Lp ℝ 2 (haarAddCircle (T := 2 * Real.pi)) :=
  Complex.reCLM.compLp (HeatAgeContinuity.heat r d)

theorem continuous_state (d : CircleL2) : Continuous (fun r : ℝ ↦ state r d) := by
  have hs : Continuous (fun r : ℝ ↦ (r, d)) := continuous_id.prodMk continuous_const
  have hh := HeatAgeContinuity.continuous_heat_action.comp hs
  have hc := (Complex.reCLM.compLpL 2 (haarAddCircle (T := 2 * Real.pi))).continuous.comp hh
  convert hc using 1 <;> rfl

theorem heat_zero (d : CircleL2) : HeatAgeContinuity.heat 0 d = d := by
  simp only [HeatAgeContinuity.heat, zero_div, CircleHeat.heat_zero,
    ContinuousLinearMap.id_apply, LinearIsometryEquiv.apply_symm_apply]

theorem state_zero (d : CircleL2) : state 0 d = Complex.reCLM.compLp d := by
  rw [state, heat_zero]

theorem state_eq_value {r : ℝ} (hr : 0 < r) (d : CircleL2) :
    state r d = PhysicalHeatSmoothing.value 2 r hr d := by
  apply Lp.ext
  filter_upwards [Complex.reCLM.coeFn_compLp (HeatAgeContinuity.heat r d),
    heat_kernel_inner_ae hr d, PhysicalHeatSmoothing.value_ae 2 r hr d] with x hx hkernel hvalue
  change (Complex.reCLM.compLp (HeatAgeContinuity.heat r d)) x = _
  rw [hx, HeatAgeContinuity.heat_eq hr.le, ← hkernel, hvalue, physicalHeatMean_eq hr]
  rfl

/-- Uniform contraction is inherited from the proved normalized heat
convolution bound through the measure-preserving circle rescaling. -/
theorem heat_bound {r : ℝ} (hr : 0 ≤ r) (d : CircleL2) (M : ℝ)
    (hd : ∀ᵐ x ∂haarAddCircle, ‖d x‖ ≤ M) :
    ∀ᵐ x ∂haarAddCircle, ‖HeatAgeContinuity.heat r d x‖ ≤ M := by
  rcases hr.eq_or_lt with hzero | hpos
  · subst r
    simpa only [heat_zero] using hd
  · have hu := CircleNormalization.push_symm_ae_property d (fun z ↦ ‖z‖ ≤ M) hd
    have hh := HeatUniformBound.heat_ae_bound
      (div_pos hpos NativeHeatObservation.timeScale_pos) (CircleNormalization.push.symm d) M hu
    exact CircleNormalization.push_ae_property _ (fun z ↦ ‖z‖ ≤ M) hh

theorem state_bound {r : ℝ} (hr : 0 ≤ r) (d : CircleL2) (M : ℝ) (hM : 0 ≤ M)
    (hd : ∀ᵐ x ∂haarAddCircle, ‖d x‖ ≤ M) :
    L2ExtendedUniformNorm.value haarAddCircle (state r d) ≤ ENNReal.ofReal M := by
  apply (L2ExtendedUniformNorm.le_iff haarAddCircle _ _).mpr
  filter_upwards [Complex.reCLM.coeFn_compLp (HeatAgeContinuity.heat r d),
    heat_bound hr d M hd] with x hx hb
  change ‖(Complex.reCLM.compLp (HeatAgeContinuity.heat r d)) x‖ₑ ≤ _
  rw [hx, ← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal ((Complex.abs_re_le_norm _).trans hb)

/-- A measurable extension of the positive-time uniform lift. Only its
restriction to positive times is used as a heat state. -/
def positiveUniform (r : ℝ) (d : CircleL2) : Lp ℝ ∞ (haarAddCircle (T := 2 * Real.pi)) :=
  if hr : 0 < r then PhysicalHeatSmoothing.value ∞ r hr d else 0

theorem continuousOn_positiveUniform (d : CircleL2) :
    ContinuousOn (fun r ↦ positiveUniform r d) (Ioi 0) := by
  rw [continuousOn_iff_continuous_domRestrict]
  convert PhysicalHeatSmoothing.continuous_value ∞ d using 1
  funext t
  change (if hr : 0 < t.val then PhysicalHeatSmoothing.value ∞ t.val hr d else 0) = _
  split_ifs with ht
  · rfl
  · exact False.elim (ht t.property)

theorem mild_norm_eq {r : ℝ} (hr : 0 < r) (d : CircleL2)
    (Y : C(Parameter, ℝ)) (t : ShortTime) :
    L2ExtendedUniformNorm.value haarAddCircle
      (state r d + PhysicalHeatParameterSection.value 2 Y t) =
      ENNReal.ofReal ‖positiveUniform r d + PhysicalHeatParameterSection.value ∞ Y t‖ := by
  let u2 : Lp ℝ 2 (haarAddCircle (T := 2 * Real.pi)) := state r d + PhysicalHeatParameterSection.value 2 Y t
  let uinf : Lp ℝ ∞ (haarAddCircle (T := 2 * Real.pi)) := positiveUniform r d + PhysicalHeatParameterSection.value ∞ Y t
  have he : (u2 : HeatCircle → ℝ) =ᵐ[haarAddCircle] (uinf : HeatCircle → ℝ) := by
    dsimp only [u2, uinf]
    rw [state_eq_value hr, positiveUniform, dif_pos hr]
    filter_upwards [Lp.coeFn_add (PhysicalHeatSmoothing.value 2 r hr d)
        (PhysicalHeatParameterSection.value 2 Y t),
      Lp.coeFn_add (PhysicalHeatSmoothing.value ∞ r hr d) (PhysicalHeatParameterSection.value ∞ Y t),
      PhysicalHeatSmoothing.value_ae 2 r hr d, PhysicalHeatSmoothing.value_ae ∞ r hr d,
      PhysicalHeatParameterSection.value_ae 2 Y t, PhysicalHeatParameterSection.value_ae ∞ Y t]
      with x h2 hinf hh2 hhinf hy2 hyinf
    simp only [h2, hinf, Pi.add_apply, hh2, hhinf, hy2, hyinf]
  change eLpNorm (u2 : HeatCircle → ℝ) ∞ haarAddCircle = ENNReal.ofReal ‖uinf‖
  rw [eLpNorm_congr_ae he, ← Lp.enorm_def, ← ofReal_norm]

/-- The scalar essential uniform norm of the actual mild trajectory is
continuous on the whole short interval. The initial heat orbit itself
is required to be continuous only in L2. -/
theorem continuous_mild_norm (d : CircleL2) (M : ℝ) (hM : 0 ≤ M)
    (hd : ∀ᵐ x ∂haarAddCircle, ‖d x‖ ≤ M)
    (h0 : L2ExtendedUniformNorm.value haarAddCircle (state 0 d) = ENNReal.ofReal M)
    (Y : C(Parameter, ℝ)) (hz : ∀ p, Y (HeatParameterCoordinates.zeroTime p) = 0) :
    Continuous (fun t : ShortTime ↦ L2ExtendedUniformNorm.value haarAddCircle
      (state t.val d + PhysicalHeatParameterSection.value 2 Y t)) := by
  rw [continuous_iff_continuousAt]
  intro t
  by_cases ht : t.val = 0
  · have he : t = initialTime := Subtype.ext ht
    subst t
    exact UniformExitEnvelope.initial_norm_continuity (fun s ↦ state s.val d)
      ((continuous_state d).comp continuous_subtype_val).continuousAt M hM
      (fun s ↦ state_bound s.property.1 d M hM hd) h0 Y hz
  · have hpos : 0 < t.val := lt_of_le_of_ne t.property.1 (Ne.symm ht)
    have hc : ContinuousAt (fun s : ShortTime ↦ positiveUniform s.val d) t :=
      ((continuousOn_positiveUniform d).continuousAt (Ioi_mem_nhds hpos)).comp
        continuous_subtype_val.continuousAt
    have hh := ENNReal.continuous_ofReal.continuousAt.comp
      (hc.add (PhysicalHeatParameterSection.uniformContinuous_value ∞ Y).continuous.continuousAt).norm
    apply hh.congr_of_eventuallyEq
    have hn : ∀ᶠ s : ShortTime in 𝓝 t, 0 < s.val :=
      (continuous_subtype_val.tendsto t) (eventually_gt_nhds hpos)
    filter_upwards [hn] with s hs
    exact mild_norm_eq hs d Y s

theorem continuous_mild_realNorm (d : CircleL2) (M : ℝ) (hM : 0 ≤ M)
    (hd : ∀ᵐ x ∂haarAddCircle, ‖d x‖ ≤ M)
    (h0 : L2ExtendedUniformNorm.value haarAddCircle (state 0 d) = ENNReal.ofReal M)
    (Y : C(Parameter, ℝ)) (hz : ∀ p, Y (HeatParameterCoordinates.zeroTime p) = 0) :
    Continuous (fun t : ShortTime ↦ L2ExtendedUniformNorm.realValue haarAddCircle
      (state t.val d + PhysicalHeatParameterSection.value 2 Y t)) := by
  rw [continuous_iff_continuousAt]
  intro t
  apply (ENNReal.continuousAt_toReal ?_).comp
    (continuous_mild_norm d M hM hd h0 Y hz).continuousAt
  exact ne_of_lt ((UniformExitEnvelope.bound (fun s ↦ state s.val d) M hM
    (fun s ↦ state_bound s.property.1 d M hM hd) Y t).trans_lt ENNReal.ofReal_lt_top)

end SHEStochastic.PhysicalHeatState
