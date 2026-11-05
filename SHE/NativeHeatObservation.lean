module

public import SHE.RealHaarIntegrand
public import SHE.CircleNormalization
public import SHE.PhysicalProfile
public import SHE.ObservationHeatCovariance
public import SHE.HilbertColumnMap

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! Actual heat-observation functionals on the literal real physical
L² state. The unit-circle semigroup is rescaled by (2π)² explicitly,
so the native period-2π observation ages have precisely the manuscript's
heat generator. All identities involve actual common-Haar columns. -/
noncomputable section
namespace SHE.NativeHeatObservation
open MeasureTheory AddCircle CircleHeat FiniteHaar DyadicApproximation
open scoped ENNReal
local instance nativeHeatObservation_unitPositive : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩
local instance nativeHeatObservation_periodPositive : Fact (0 < 2*Real.pi) := ⟨by positivity⟩

def timeScale : ℝ := (2*Real.pi)^2
theorem timeScale_pos : 0 < timeScale := by unfold timeScale; positivity

def embed : RealL2 →L[ℝ] StoppedFourier.CircleL2 :=
  (CircleNormalization.push.toContinuousLinearEquiv.toContinuousLinearMap.restrictScalars ℝ).comp realEmbed

theorem embed_apply (v : RealL2) : embed v=CircleNormalization.push (realEmbed v) := rfl

theorem embed_norm (v : RealL2) : ‖embed v‖=‖v‖ := by
  rw [embed_apply,LinearIsometryEquiv.norm_map,realEmbed_norm_eq]

def heat (t : ℝ) : RealL2 →L[ℝ] RealL2 := RealHeat.realHeat (t/timeScale)

theorem embed_heat {t : ℝ} (ht : 0 ≤ t) (v : RealL2) :
    embed (heat t v)=StoppedFourier.circleHeatOperator t ht (embed v) := by
  have hage : 0 ≤ t/timeScale := div_nonneg ht timeScale_pos.le
  rw [embed_apply,heat,RealHeat.realEmbed_realHeat,CircleNormalization.push_heat _ hage]
  have he : (2*Real.pi)^2*(t/timeScale)=t := by
    change timeScale*(t/timeScale)=t
    field_simp [timeScale_pos.ne']
  simp only [he,embed_apply]

def functional (τ : ℝ) (x : StoppedFourier.HeatCircle) : RealL2 →L[ℝ] ℝ :=
  Complex.reCLM.comp (((innerSL ℂ (StoppedFourier.circleHeat τ x)).restrictScalars ℝ).comp embed)

theorem functional_apply (τ : ℝ) (x : StoppedFourier.HeatCircle) (v : RealL2) :
    functional τ x v=(inner ℂ (StoppedFourier.circleHeat τ x) (embed v)).re := rfl

theorem functional_physical {τ : ℝ} (hτ : 0 < τ) (x : StoppedFourier.HeatCircle) (v : RealL2) :
    functional τ x v=PhysicalProfile.physicalHeatMean (embed v) (τ,x) :=
  (PhysicalProfile.physicalHeatMean_eq hτ (embed v) x).symm

/-- Exact propagation of the physical observation through the rescaled
native heat semigroup, with no supplied observation identity. -/
theorem functional_heat {τ t : ℝ} (hτ : 0 < τ) (ht : 0 ≤ t)
    (x : StoppedFourier.HeatCircle) (v : RealL2) :
    functional τ x (heat t v)=functional (τ+t) x v := by
  rw [functional_apply,embed_heat ht,← StoppedFourier.circleHeatOperator_self_adjoint t ht,
    StoppedFourier.circleHeatOperator_heat ht hτ]
  rw [add_comm t τ]
  rfl

theorem functional_norm_bound (τ : ℝ) (x : StoppedFourier.HeatCircle) (v : RealL2) :
    |functional τ x v| ≤ ‖StoppedFourier.circleHeat τ x‖*‖v‖ := by
  rw [functional_apply]
  exact (Complex.abs_re_le_norm _).trans (by simpa only [embed_norm] using
    (norm_inner_le_norm (𝕜 := ℂ) (StoppedFourier.circleHeat τ x) (embed v)))

def kernel (ell M : ℝ) (hell : 0 < ell) (p : ℝ × EllipticField ell M) : RealHaarIntegrand.Columns :=
  RealHaarIntegrand.kernel ell M hell (p.1/timeScale,p.2)

theorem realEmbed_realPart_of_real (v : CircleL2) (hv : ∀ᵐ x ∂haarAddCircle,(v x).im=0) :
    realEmbed (realPart v)=v := by
  let w : realCircleSpace := ⟨v,(mem_realCircleSpace v).mpr hv⟩
  exact congrArg Subtype.val (realCircleIdentification.apply_symm_apply w)

theorem kernel_column {ell M t : ℝ} (hell : 0 < ell) (ht : 0 < t)
    (f : EllipticField ell M) (q : HaarNode) :
    embed (kernel ell M hell (t,f) q)=StoppedFourier.circleHeatOperator t ht.le
      (CircleNormalization.push (globalHaarColumn q f.1)) := by
  have hage : 0 < t/timeScale := div_pos ht timeScale_pos
  change CircleNormalization.push (realEmbed (realPart
    (HaarHeatIntegrand.kernel ell M hell (t/timeScale,f) q)))=_
  rw [realEmbed_realPart_of_real _ (RealHaarIntegrand.kernel_column_real hell _ q),
    HaarHeatIntegrand.kernel_apply,ite_eq_left hage,CircleNormalization.push_heat _ hage.le]
  have he : (2*Real.pi)^2*(t/timeScale)=t := by
    change timeScale*(t/timeScale)=t
    field_simp [timeScale_pos.ne']
  simp only [he]

theorem functional_kernel_column {ell M τ t : ℝ} (hell : 0 < ell) (hτ : 0 < τ) (ht : 0 < t)
    (f : EllipticField ell M) (x : StoppedFourier.HeatCircle) (q : HaarNode) :
    functional τ x (kernel ell M hell (t,f) q)=
      (nativeFactorAnalysis f.1 ell M hell f.2.1 f.2.2 (StoppedFourier.circleHeat (τ+t) x) q).re := by
  rw [functional_apply,kernel_column hell ht,← StoppedFourier.circleHeatOperator_self_adjoint t ht.le,
    StoppedFourier.circleHeatOperator_heat ht.le hτ]
  rw [add_comm t τ]
  change (inner ℂ (StoppedFourier.circleHeat (τ+t) x) (CircleNormalization.push (globalHaarColumn q f.1))).re =
    (inner ℂ (globalHaarColumn q f.1) (CircleNormalization.push.symm (StoppedFourier.circleHeat (τ+t) x))).re
  have he := CircleNormalization.push.inner_map_map (globalHaarColumn q f.1)
    (CircleNormalization.push.symm (StoppedFourier.circleHeat (τ+t) x))
  rw [LinearIsometryEquiv.apply_symm_apply] at he
  rw [← he]
  have hc := congrArg Complex.re (inner_conj_symm (StoppedFourier.circleHeat (τ+t) x)
    (CircleNormalization.push (globalHaarColumn q f.1)))
  simpa only [Complex.conj_re] using hc.symm

def columnFunctional (τ : ℝ) (x : StoppedFourier.HeatCircle) :
    RealHaarIntegrand.Columns →L[ℝ] RealHaarInput := HilbertColumns.mapCLM (functional τ x)

theorem observed_kernel_eq {ell M τ t : ℝ} (hell : 0 < ell) (hτ : 0 < τ) (ht : 0 < t)
    (f : EllipticField ell M) (x : StoppedFourier.HeatCircle) :
    columnFunctional τ x (kernel ell M hell (t,f))=
      realInputPart (nativeFactorAnalysis f.1 ell M hell f.2.1 f.2.2 (StoppedFourier.circleHeat (τ+t) x)) := by
  apply lp.ext
  funext q
  exact functional_kernel_column hell hτ ht f x q

theorem kernel_zero {ell M t : ℝ} (hell : 0 < ell) (ht : t ≤ 0) (f : EllipticField ell M) :
    kernel ell M hell (t,f)=0 := by
  apply lp.ext
  funext q
  have hage : ¬ 0 < t/timeScale := not_lt.mpr (div_nonpos_of_nonpos_of_nonneg ht timeScale_pos.le)
  change realPart (HaarHeatIntegrand.kernel ell M hell (t/timeScale,f) q)=0
  rw [HaarHeatIntegrand.kernel_apply,ite_eq_right hage]
  exact map_zero (Complex.reCLM.compLpL 2 haarAddCircle)

/-- At any intermediate observation time the stochastic heat column
reduces to a stopped row depending only on the original target T.
This is the deterministic integrand identity behind the observation
martingale; no semimartingale identity is assumed here. -/
theorem stopped_observed_kernel {ell M T t r : ℝ} (hell : 0 < ell) (ht : t < T)
    (f : EllipticField ell M) (x : StoppedFourier.HeatCircle) :
    columnFunctional (T-t) x (kernel ell M hell (t-r,f)) = if r < t then
      realInputPart (nativeFactorAnalysis f.1 ell M hell f.2.1 f.2.2
        (StoppedFourier.circleHeat (T-r) x)) else 0 := by
  by_cases hr : r < t
  · rw [ite_eq_left hr,observed_kernel_eq hell (sub_pos.mpr ht) (sub_pos.mpr hr)]
    rw [show T-t+(t-r)=T-r by ring]
  · rw [ite_eq_right hr,kernel_zero hell (sub_nonpos.mpr (le_of_not_gt hr)),map_zero]

end SHE.NativeHeatObservation
