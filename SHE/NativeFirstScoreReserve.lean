module

public import SHE.ControlledJointWeightedWord
public import SHE.StoppedCovarianceSplit

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section

namespace SHE.NativeFirstScoreReserve
open Set MeasureTheory ProbabilityTheory GaussianIncrement ControlledProfile StoppedFourier
  StoppedGaussianFeatures StoppedGaussianScore
local instance : Fact (0<2*Real.pi):=⟨by positivity⟩
variable {n:ℕ}

def floor (P:CanonicalCovariance.ProfileParameters):ℝ:=P.lower/8

def oldProfile (P:CanonicalCovariance.ProfileParameters) (old:ControlledProfile.Domain→ℝ) (p:ControlledProfile.Domain):ℝ:=
  old p+floor P

def covariance (P:CanonicalCovariance.ProfileParameters) (σ target:Fin n→ℝ)
    (center:Fin n→HeatCircle) (q:ℝ):Matrix (Fin n) (Fin n) ℝ:=
  stoppedCovariance σ target center (fun _=>floor P) q

theorem oldProfile_measurable (P:CanonicalCovariance.ProfileParameters) {old:ControlledProfile.Domain→ℝ}
    (hold:Measurable old):Measurable (oldProfile P old):=hold.add_const _

theorem oldProfile_bounds (P:CanonicalCovariance.ProfileParameters) {old:ControlledProfile.Domain→ℝ}
    (hold:∀p,0≤old p ∧ old p≤P.lower/2) (p:ControlledProfile.Domain):
    0≤oldProfile P old p ∧ oldProfile P old p≤5*P.lower/8:=by
  have hp:=hold p
  dsimp only [oldProfile,floor]
  constructor <;> linarith [P.lower_pos]

theorem residual_bounds (P:CanonicalCovariance.ProfileParameters) (Λ:ℝ) (u d:CircleL2)
    {old:ControlledProfile.Domain→ℝ} (hold:∀p,0≤old p ∧ old p≤P.lower/2) (θ:ℝ) (p:ControlledProfile.Domain):
    3*P.lower/8≤ControlledFixedReserve.coefficient P Λ u d (oldProfile P old) θ p ∧
      ControlledFixedReserve.coefficient P Λ u d (oldProfile P old) θ p≤P.upper:=by
  have hh:=ControlledFixedReserve.coefficient_bounds P Λ u d (oldProfile P old)
    (oldProfile_bounds P hold) θ p
  constructor <;> linarith

/-- An independent fixed native first-score fraction leaves a uniform
three-eighths residual floor, without altering any original old interval. -/
theorem covariance_split (P:CanonicalCovariance.ProfileParameters) (Λ:ℝ) (u d:CircleL2)
    {old:ControlledProfile.Domain→ℝ} (hold:Measurable old) (holdb:∀p,0≤old p ∧ old p≤P.lower/2)
    (σ target:Fin n→ℝ) (center:Fin n→HeatCircle)
    (hσ:∀i,0<σ i) (hσ1:∀i,σ i≤1) (hages:∀i,σ i≤target i) (q:ℝ) (hq:0≤q) (θ:ℝ):
    covariance P σ target center q+
      ControlledFixedReserve.covariance P Λ u d (oldProfile P old) σ target center q θ=
        ControlledFixedReserve.covariance P Λ u d old σ target center q θ:=by
  have hcm:Measurable (ControlledFixedReserve.coefficient P Λ u d (oldProfile P old) θ):=
    ((ControlledProfile.profile_measurable P Λ u d).comp (measurable_const.prodMk measurable_id)).sub
      (oldProfile_measurable P hold)
  have hcb:∀p,|ControlledFixedReserve.coefficient P Λ u d (oldProfile P old) θ p|≤P.upper:=by
    intro p
    rw [abs_of_nonneg ((by have := P.lower_pos; positivity:0≤3*P.lower/8).trans (residual_bounds P Λ u d holdb θ p).1)]
    exact (residual_bounds P Λ u d holdb θ p).2
  have hi:=StoppedCovarianceSplit.covariance_add σ target center hages q
    (c:=fun _=>floor P) (d:=ControlledFixedReserve.coefficient P Λ u d (oldProfile P old) θ)
    measurable_const hcm (M:=floor P) (N:=P.upper)
    (fun _=>by rw [abs_of_pos (by have := P.lower_pos; dsimp [floor];positivity)]) hcb
  have he:(fun p:ControlledProfile.Domain=>floor P+ControlledFixedReserve.coefficient P Λ u d (oldProfile P old) θ p)=
      ControlledFixedReserve.coefficient P Λ u d old θ:=by
    funext p
    dsimp only [ControlledFixedReserve.coefficient,oldProfile]
    ring
  rw [he] at hi
  exact hi.symm

theorem covariance_posSemidef (P:CanonicalCovariance.ProfileParameters)
    (σ target:Fin n→ℝ) (center:Fin n→HeatCircle) (hages:∀i,σ i≤target i) (q:ℝ):
    (covariance P σ target center q).PosSemidef:=
  StoppedCovarianceSplit.covariance_posSemidef σ target center hages q measurable_const
    (fun _=>⟨by have := P.lower_pos; dsimp [floor];positivity,le_rfl⟩)

end SHE.NativeFirstScoreReserve
