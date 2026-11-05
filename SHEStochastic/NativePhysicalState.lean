module

public import SHEStochastic.PhysicalHeatState
public import SHEStochastic.RealCausalHeatKernel

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section

namespace SHEStochastic.NativePhysicalState
open MeasureTheory SHE SHE.StoppedFourier SHE.DyadicApproximation AddCircle Filter
open HeatParameterCover HeatParameterPullback
open scoped ENNReal Topology

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

/-- The original native real state in the physical period-2pi circle.
This is the existing measure-preserving Lp pullback, hence an isometry. -/
def push : RealL2 →ₗᵢ[ℝ] Lp ℝ 2 (haarAddCircle (T := 2 * Real.pi)) :=
  Lp.compMeasurePreservingₗᵢ ℝ (CircleNormalization.scale (2 * Real.pi) 1)
    (CircleNormalization.scale_measurePreserving (2 * Real.pi) 1)

theorem push_ae (u : RealL2) : push u =ᵐ[haarAddCircle]
    fun x ↦ u (CircleNormalization.scale (2 * Real.pi) 1 x) :=
  Lp.coeFn_compMeasurePreserving u (CircleNormalization.scale_measurePreserving (2 * Real.pi) 1)

def pull : Lp ℝ 2 (haarAddCircle (T := 2 * Real.pi)) →ₗᵢ[ℝ] RealL2 :=
  Lp.compMeasurePreservingₗᵢ ℝ (CircleNormalization.scale 1 (2 * Real.pi))
    (CircleNormalization.scale_measurePreserving 1 (2 * Real.pi))

theorem pull_ae (u : Lp ℝ 2 (haarAddCircle (T := 2 * Real.pi))) : pull u =ᵐ[haarAddCircle]
    fun x ↦ u (CircleNormalization.scale 1 (2 * Real.pi) x) :=
  Lp.coeFn_compMeasurePreserving u (CircleNormalization.scale_measurePreserving 1 (2 * Real.pi))

theorem push_pull (u : Lp ℝ 2 (haarAddCircle (T := 2 * Real.pi))) : push (pull u) = u := by
  apply Lp.ext
  have hh := (CircleNormalization.scale_measurePreserving (2 * Real.pi) 1).quasiMeasurePreserving.ae (pull_ae u)
  filter_upwards [push_ae (pull u), hh] with x hp hq
  rw [hp, hq]
  exact congrArg (fun a : HeatCircle ↦ u a) (SHE.NativeHeatSpan.scale_inverse x)

def equivalence : RealL2 ≃ₗᵢ[ℝ] Lp ℝ 2 (haarAddCircle (T := 2 * Real.pi)) :=
  LinearIsometryEquiv.ofSurjective push (fun u ↦ ⟨pull u, push_pull u⟩)

theorem embed_ae (u : RealL2) : NativeHeatObservation.embed u =ᵐ[haarAddCircle]
    fun x ↦ (u (CircleNormalization.scale (2 * Real.pi) 1 x) : ℂ) := by
  have hr := (CircleNormalization.scale_measurePreserving (2 * Real.pi) 1).quasiMeasurePreserving.ae
    (realEmbed_ae u)
  filter_upwards [CircleNormalization.push_ae (realEmbed u), hr] with x hx hy
  exact hx.trans hy

theorem embed_eq_push (u : RealL2) : NativeHeatObservation.embed u =ᵐ[haarAddCircle]
    fun x ↦ (push u x : ℂ) := by
  filter_upwards [embed_ae u, push_ae u] with x hc hr
  exact hc.trans (congrArg Complex.ofReal hr.symm)

/-- Each native positive heat observation is the literal real heat
convolution of the physical L2 state. This is the interface used to
recover the mild state from scalar stochastic observations. -/
theorem functional_integral {r : ℝ} (hr : 0 < r) (x : HeatCircle) (u : RealL2) :
    NativeHeatObservation.functional r x u =
      ∫ a : HeatCircle, RealCausalHeatKernel.value x r a * push u a ∂haarAddCircle := by
  have he : inner ℂ (circleHeat r x) (NativeHeatObservation.embed u) =
      ((∫ a : HeatCircle, RealCausalHeatKernel.value x r a * push u a ∂haarAddCircle : ℝ) : ℂ) := by
    rw [L2.inner_def, ← _root_.integral_complex_ofReal]
    apply integral_congr_ae
    have hk := (SHE.NativeHeatSpan.kernel_physical_ae hr x).trans (SHE.ProfileVariance.heatPhysical_ae hr x)
    filter_upwards [hk, embed_ae u, push_ae u] with a ha hb hc
    rw [← ha, RealCausalHeatKernel.complex_eq hr, hb, RCLike.inner_apply, Complex.conj_ofReal, hc]
    push_cast
    ring
  change (inner ℂ (circleHeat r x) (NativeHeatObservation.embed u)).re = _
  rw [he]
  rfl

theorem push_eq_realPart (u : RealL2) : push u = Complex.reCLM.compLp (NativeHeatObservation.embed u) := by
  apply Lp.ext
  filter_upwards [push_ae u, Complex.reCLM.coeFn_compLp (NativeHeatObservation.embed u), embed_ae u]
    with x hp hc he
  rw [hp, hc, he]
  rfl

/-- Both circle conventions give exactly the same essential uniform
norm, including unbounded L2 states. -/
theorem uniform_norm_push (u : RealL2) :
    L2ExtendedUniformNorm.value (haarAddCircle (T := 2 * Real.pi)) (push u) =
      L2ExtendedUniformNorm.value (haarAddCircle (T := 1)) u := by
  change eLpNorm (push u) ∞ haarAddCircle = eLpNorm u ∞ haarAddCircle
  rw [eLpNorm_congr_ae (push_ae u)]
  exact eLpNorm_comp_measurePreserving (Lp.aestronglyMeasurable u)
    (CircleNormalization.scale_measurePreserving (2 * Real.pi) 1)

theorem real_uniform_norm_push (u : RealL2) :
    L2ExtendedUniformNorm.realValue (haarAddCircle (T := 2 * Real.pi)) (push u) =
      L2ExtendedUniformNorm.realValue (haarAddCircle (T := 1)) u :=
  congrArg ENNReal.toReal (uniform_norm_push u)

theorem push_heat {t : ℝ} (ht : 0 ≤ t) (u : RealL2) :
    push (NativeHeatObservation.heat t u) = PhysicalHeatState.state t (NativeHeatObservation.embed u) := by
  rw [push_eq_realPart, NativeHeatObservation.embed_heat ht, ← HeatAgeContinuity.heat_eq ht]
  rfl

theorem embed_bound (u : RealL2) (M : ℝ)
    (hu : ∀ᵐ x ∂haarAddCircle, ‖u x‖ ≤ M) :
    ∀ᵐ x ∂haarAddCircle, ‖NativeHeatObservation.embed u x‖ ≤ M := by
  have hh := (CircleNormalization.scale_measurePreserving (2 * Real.pi) 1).quasiMeasurePreserving.ae hu
  filter_upwards [embed_ae u, hh] with x hx hb
  simpa only [hx, Complex.norm_real] using hb

/-- The uniform-norm regularity needed for the exit argument now uses
only the literal native bounded initial state and the continuous native
stochastic remainder. No extra initial regularity is supplied. -/
theorem continuous_mild_realNorm (u : RealL2) (M : ℝ) (hM : 0 ≤ M)
    (hu : L2ExtendedUniformNorm.value (haarAddCircle (T := 1)) u = ENNReal.ofReal M)
    (Y : C(Parameter, ℝ)) (hz : ∀ p, Y (HeatParameterCoordinates.zeroTime p) = 0) :
    Continuous (fun t : ShortTime ↦ L2ExtendedUniformNorm.realValue haarAddCircle
      (PhysicalHeatState.state t.val (NativeHeatObservation.embed u) +
        PhysicalHeatParameterSection.value 2 Y t)) := by
  apply PhysicalHeatState.continuous_mild_realNorm (NativeHeatObservation.embed u) M hM
    (embed_bound u M ((L2ExtendedUniformNorm.le_ofReal_iff _ u M hM).mp hu.le)) ?_ Y hz
  rw [PhysicalHeatState.state_zero, ← push_eq_realPart, uniform_norm_push, hu]

end SHEStochastic.NativePhysicalState
