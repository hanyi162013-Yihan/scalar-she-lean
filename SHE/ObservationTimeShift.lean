module

public import SHE.OldIntervalSum
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Group.MeasurableEquiv

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

/-! Exact changes from absolute time to time measured from an arbitrary
past. Each observation keeps its own stop and target. Both common-window
and full individually stopped Gaussian covariances are transported by a
measure-preserving translation, including singular Gaussian laws. -/
namespace SHE.ObservationTimeShift
open Set MeasureTheory ProbabilityTheory AddCircle WordRecursion
  StoppedGaussianFeatures OldIntervalCovariance StoppedFourier
open scoped Topology BigOperators
local instance observationTimeShift_period : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
variable {n r : ℕ}

/-- Physical time translation, with the spatial point unchanged. -/
def translation (v : ℝ) : Domain ≃ᵐ Domain :=
  (MeasurableEquiv.addRight v).prodCongr (MeasurableEquiv.refl _)

@[simp] theorem translation_apply (v : ℝ) (p : Domain) :
    translation v p = (p.1+v,p.2) := rfl

/-- An absolute-time profile corresponding to a relative-time profile. -/
def profile (v : ℝ) (c : Domain → ℝ) (p : Domain) : ℝ := c (p.1-v,p.2)

@[simp] theorem profile_translation (v : ℝ) (c : Domain → ℝ) (p : Domain) :
    profile v c (translation v p)=c p := by
  simp only [profile,translation_apply,add_sub_cancel_right]

theorem measurable_profile (v : ℝ) {c : Domain → ℝ} (hc : Measurable c) :
    Measurable (profile v c) := hc.comp
      ((measurable_fst.sub_const v).prodMk measurable_snd)

/-- Stops and targets are translated separately, without a common-stop
replacement. -/
def observations (v : ℝ) (Z : Fin n → Observation) (i : Fin n) : Observation :=
  ⟨(Z i).stop+v,(Z i).target+v,(Z i).center⟩

@[simp] theorem observations_stop (v : ℝ) (Z : Fin n → Observation) (i : Fin n) :
    (observations v Z i).stop=(Z i).stop+v := rfl
@[simp] theorem observations_target (v : ℝ) (Z : Fin n → Observation) (i : Fin n) :
    (observations v Z i).target=(Z i).target+v := rfl
@[simp] theorem observations_center (v : ℝ) (Z : Fin n → Observation) (i : Fin n) :
    (observations v Z i).center=(Z i).center := rfl

theorem heatRow_translation (v t : ℝ) (Z : Fin n → Observation) (x : HeatCircle) :
    heatRow (observations v Z) (t+v) x=heatRow Z t x := by
  unfold heatRow
  congr 1
  funext i
  simp only [observations_target,observations_center,add_sub_add_right_eq_sub]

theorem stoppedRow_translation (v : ℝ) (σ target : Fin n → ℝ)
    (center : Fin n → HeatCircle) (p : Domain) :
    stoppedRow (fun i => σ i+v) (fun i => target i+v) center (translation v p)=
      stoppedRow σ target center p := by
  unfold stoppedRow
  congr 1
  funext i
  simp only [translation_apply,add_lt_add_iff_right,add_sub_add_right_eq_sub]

theorem history_translation (v q : ℝ) : MeasurePreserving (translation v)
    (historyMeasure q) (historyMeasure (q+v)) := by
  have ht := (measurePreserving_add_right (volume : Measure ℝ) v).restrict_preimage
    (measurableSet_Ici : MeasurableSet (Ici (q+v)))
  have he : (fun t : ℝ => t+v) ⁻¹' Ici (q+v)=Ici q := by
    ext t
    simp only [mem_preimage,mem_Ici,add_le_add_iff_right]
  rw [he] at ht
  exact ht.prod (MeasurePreserving.id (haarAddCircle (T:=2*Real.pi)))

/-- The actual full-history time-space measure is translated exactly. -/
theorem integral_history_translation {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (v q : ℝ) (f : Domain → E) :
    (∫ p, f (translation v p) ∂historyMeasure q)=
      ∫ p, f p ∂historyMeasure (q+v) :=
  (history_translation v q).integral_comp' f

theorem covarianceDensity_translation (v t : ℝ) (c : Domain → ℝ)
    (Z : Fin n → Observation) (i j : Fin n) :
    covarianceDensity (profile v c) (observations v Z) (t+v) i j=
      covarianceDensity c Z t i j := by
  unfold covarianceDensity
  apply integral_congr_ae
  filter_upwards with x
  simp only [heatRow_translation,profile,add_sub_cancel_right]

theorem covariance_translation (v q s : ℝ) (c : Domain → ℝ)
    (Z : Fin n → Observation) :
    WordRecursion.covariance (profile v c) (observations v Z) (q+v) (s+v)=covariance c Z q s := by
  ext i j
  unfold WordRecursion.covariance
  rw [← intervalIntegral.integral_comp_add_right]
  simp_rw [covarianceDensity_translation]

theorem gaussianSemigroup_translation (v q s : ℝ) (c : Domain → ℝ)
    (Z : Fin n → Observation) (F : State n → ℝ) (z : State n) :
    gaussianSemigroup (profile v c) (observations v Z) (q+v) (s+v) F z=
      gaussianSemigroup c Z q s F z := by
  unfold gaussianSemigroup
  rw [covariance_translation]

/-- This identity is for the full individually stopped covariance, and
therefore preserves asynchronous stops and every collision exactly. -/
theorem stoppedCovariance_translation (v q : ℝ) (σ target : Fin n → ℝ)
    (center : Fin n → HeatCircle) (c : Domain → ℝ) :
    StoppedGaussianFeatures.stoppedCovariance (fun i => σ i+v) (fun i => target i+v) center
      (profile v c) (q+v)=StoppedGaussianFeatures.stoppedCovariance σ target center c q := by
  ext i j
  unfold StoppedGaussianFeatures.stoppedCovariance
  rw [← integral_history_translation v q]
  apply integral_congr_ae
  apply ae_of_all
  intro p
  simp only [profile_translation,stoppedRow_translation]

theorem stoppedGaussian_translation (v q : ℝ) (σ target : Fin n → ℝ)
    (center : Fin n → HeatCircle) (c : Domain → ℝ) :
    multivariateGaussian (0 : State n)
      (StoppedGaussianFeatures.stoppedCovariance (fun i => σ i+v) (fun i => target i+v) center
        (profile v c) (q+v))=
    multivariateGaussian (0 : State n) (StoppedGaussianFeatures.stoppedCovariance σ target center c q) := by
  rw [stoppedCovariance_translation]

theorem intervalProfile_translation (v lo hi : ℝ) (c : Domain → ℝ) :
    intervalProfile (profile v c) (lo+v) (hi+v)=profile v (intervalProfile c lo hi) := by
  funext p
  have hm : p ∈ timeSet (lo+v) (hi+v) ↔ (p.1-v,p.2) ∈ timeSet lo hi := by
    simp only [timeSet,mem_prod,mem_Ioc,mem_univ,and_true]
    constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith
  by_cases hp : p ∈ timeSet (lo+v) (hi+v)
  · simp only [intervalProfile,Set.indicator_of_mem hp,profile,
      Set.indicator_of_mem (hm.mp hp)]
  · simp only [intervalProfile,Set.indicator_of_notMem hp,profile,
      Set.indicator_of_notMem (fun h => hp (hm.mpr h))]

theorem sumProfile_translation (v : ℝ) (lo hi : Fin r → ℝ) (c : Domain → ℝ) :
    sumProfile (profile v c) (fun j => lo j+v) (fun j => hi j+v)=
      profile v (sumProfile c lo hi) := by
  funext p
  unfold sumProfile
  simp_rw [intervalProfile_translation]
  rfl

theorem oldCovariance_translation (v q lo hi : ℝ) (σ target : Fin n → ℝ)
    (center : Fin n → HeatCircle) (c : Domain → ℝ) :
    StoppedGaussianFeatures.stoppedCovariance (fun i => σ i+v) (fun i => target i+v) center
      (intervalProfile (profile v c) (lo+v) (hi+v)) (q+v)=
    StoppedGaussianFeatures.stoppedCovariance σ target center (intervalProfile c lo hi) q := by
  rw [intervalProfile_translation,stoppedCovariance_translation]

end SHE.ObservationTimeShift
