module

public import SHE.RealHaarIntegrand
public import SHE.CompanionEnergy

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.NonlinearHaarIntegrand
open MeasureTheory Set AddCircle CircleHeat FiniteHaar LowBands CoefficientFields
open scoped NNReal ENNReal Topology
local instance nonlinearHaarIntegrand_periodPos : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩
local instance nonlinearHaarIntegrand_pFinite : Fact ((2:ENNReal) ≠ ⊤) := ⟨by simp⟩
local instance nonlinearHaarIntegrand_circleSigma : MeasurableSpace CircleL2 := borel CircleL2
local instance nonlinearHaarIntegrand_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance nonlinearHaarIntegrand_stateSigma : MeasurableSpace StateL2 := borel StateL2
local instance nonlinearHaarIntegrand_stateBorel : BorelSpace StateL2 := ⟨rfl⟩
local instance nonlinearHaarIntegrand_columnsSigma : MeasurableSpace RealHaarIntegrand.Columns := borel RealHaarIntegrand.Columns
local instance nonlinearHaarIntegrand_columnsBorel : BorelSpace RealHaarIntegrand.Columns := ⟨rfl⟩

theorem absBound {a : ℝ → ℝ} {ell M : ℝ} (hell : 0 < ell) (hb : ∀ z,ell ≤ a z ∧ a z ≤ M) :
    ∀ z,|a z| ≤ M := fun z => by rw [abs_of_nonneg (hell.le.trans (hb z).1)]; exact (hb z).2

def coefficientField (a : ℝ → ℝ) (ha : Measurable a) (ell M : ℝ) (hell : 0 < ell)
    (hb : ∀ z,ell ≤ a z ∧ a z ≤ M) (u : StateL2) : EllipticField ell M :=
  ⟨coefficient a ha M (absBound hell hb) u,coefficient_real _ _ _ _ u,
    coefficient_elliptic _ _ _ _ u ell M hb⟩

def kernel (a : ℝ → ℝ) (ha : Measurable a) (ell M : ℝ) (hell : 0 < ell)
    (hb : ∀ z,ell ≤ a z ∧ a z ≤ M) (p : ℝ × StateL2) : RealHaarIntegrand.Columns :=
  RealHaarIntegrand.kernel ell M hell (p.1,coefficientField a ha ell M hell hb p.2)

theorem coefficientField_measurable {a : ℝ → ℝ} (ha : Measurable a) {ell M H β : ℝ}
    (hell : 0 < ell) (hb : ∀ z,ell ≤ a z ∧ a z ≤ M) (hβ : 0 < β) (hH : 0 ≤ H)
    (hholder : ∀ z w,|a z-a w| ≤ H*|z-w|^β) :
    Measurable (coefficientField a ha ell M hell hb) :=
  (measurable_coefficient hβ hH a ha (absBound hell hb) hholder).subtype_mk

theorem kernel_measurable {a : ℝ → ℝ} (ha : Measurable a) {ell M H β : ℝ}
    (hell : 0 < ell) (hb : ∀ z,ell ≤ a z ∧ a z ≤ M) (hβ : 0 < β) (hH : 0 ≤ H)
    (hholder : ∀ z w,|a z-a w| ≤ H*|z-w|^β) :
    Measurable (kernel a ha ell M hell hb) :=
  (RealHaarIntegrand.kernel_measurable ell M hell).comp
    (measurable_fst.prodMk ((coefficientField_measurable ha hell hb hβ hH hholder).comp measurable_snd))

theorem kernel_difference_norm_sq {a : ℝ → ℝ} (ha : Measurable a) {ell M t : ℝ}
    (hell : 0 < ell) (hb : ∀ z,ell ≤ a z ∧ a z ≤ M) (ht : 0 < t) (u v : StateL2) :
    ‖kernel a ha ell M hell hb (t,u)-kernel a ha ell M hell hb (t,v)‖^2=
      CompanionHeat.columnEnergy a ha M (absBound hell hb) u v t := by
  unfold kernel
  rw [RealHaarIntegrand.kernel_difference_norm_sq,
    HaarHeatIntegrand.kernel_difference_norm_sq hell ht]
  rfl

theorem kernel_norm_sq_bound {a : ℝ → ℝ} (ha : Measurable a) {ell M t : ℝ}
    (hell : 0 < ell) (hb : ∀ z,ell ≤ a z ∧ a z ≤ M) (ht : 0 < t) (u : StateL2) :
    ‖kernel a ha ell M hell hb (t,u)‖^2 ≤
      M*(1+2*HeatTrace.fractionalGaussianIntegral 0*t^(-(1/2:ℝ))) := by
  unfold kernel
  rw [RealHaarIntegrand.kernel_norm_sq]
  exact HaarHeatIntegrand.kernel_norm_sq_bound hell ht _

theorem kernel_predictable {Ω : Type*} [MeasurableSpace Ω]
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) {a : ℝ → ℝ} (ha : Measurable a) {ell M H β : ℝ}
    (hell : 0 < ell) (hb : ∀ z,ell ≤ a z ∧ a z ≤ M) (hβ : 0 < β) (hH : 0 ≤ H)
    (hholder : ∀ z w,|a z-a w| ≤ H*|z-w|^β)
    (u : ℝ≥0 → Ω → StateL2) (hu : IsStronglyPredictable 𝓕 u) (t : ℝ) :
    IsStronglyPredictable 𝓕 (fun s ω => kernel a ha ell M hell hb (t-(s:ℝ),u s ω)) := by
  exact ((kernel_measurable ha hell hb hβ hH hholder).comp
    ((measurable_const.sub (PredictableClock.real_time_measurable 𝓕)).prodMk hu.measurable)).stronglyMeasurable

end SHE.NonlinearHaarIntegrand
