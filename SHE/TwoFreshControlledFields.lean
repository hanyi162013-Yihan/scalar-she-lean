module

public import SHE.TwoFreshGaussianFields
public import SHE.VaryingControlledGaussianFields

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1800000
noncomputable section
namespace SHE.TwoFreshControlledFields
open Set MeasureTheory ProbabilityTheory StoppedFourier StoppedGaussianFeatures ControlledOldIntervals
  OldIntervalCovariance GaussianIncrement TwoFreshFullResidualMoments
open scoped BigOperators
local instance twoFreshControlledFields_period : Fact (0<2*Real.pi):=⟨by positivity⟩
variable {Ω:Type*} [MeasurableSpace Ω] [MeasurableSpace CircleL2] [BorelSpace CircleL2]
variable {n d r m:ℕ}

/-- The actual additional native Gaussian reserve is fixed before the
past states, while the remaining controlled residual varies jointly. -/
theorem residual_covariance_measurable (P:CanonicalCovariance.ProfileParameters) (Λ θ q:ℝ)
    (u d0:Ω→CircleL2) (hu:Measurable u) (hd:Measurable d0)
    (σ target:Fin n→ℝ) (center:Fin n→HeatCircle) (lo hi:Fin r→ℝ):
    Measurable (fun ω=>ControlledFixedReserve.covariance P Λ (u ω) (d0 ω)
      (NativeFirstScoreReserve.oldProfile P (fixedProfile P Λ (u ω) (d0 ω) lo hi)) σ target center q θ):=by
  convert! StoppedGaussianFields.covariance_measurable
    (VaryingControlledGaussianFields.family (Ω:=Ω) σ target center)
    ((VaryingControlledGaussianFields.profile_measurable P Λ θ u d0 hu hd).sub
      ((VaryingControlledGaussianFields.fixed_profile_measurable P Λ u d0 hu hd lo hi).add_const
        (NativeFirstScoreReserve.floor P))) (measurable_const (a:=q)) using 1

/-- Genuine Borel dependence of the complete actual varying-reference
Gaussian fibre, with native first score and fresh mean/covariance score. -/
theorem fibreAverage_measurable (P:CanonicalCovariance.ProfileParameters) (Λ θ q:ℝ)
    (u d0:Ω→CircleL2) (hu:Measurable u) (hd:Measurable d0)
    (σ target:Fin n→ℝ) (center:Fin n→HeatCircle) (lo hi:Fin r→ℝ)
    (mean:Ω→State n) (hm:Measurable mean) (second:Bool)
    (D:Ω→Fin r→State n) (hD:∀j,Measurable (fun ω=>D ω j))
    (E V:Ω→State n) (hE:Measurable E) (hV:Measurable V)
    (g:Fin d→Fin n) (leaf:Fin m→Fin n) (choices:List (Fin r×Fin (m+1)))
    (F:State d→ℝ) (hF:Measurable F):
    Measurable (fun ω=>fibreAverage P Λ (u ω) (d0 ω) θ q σ target center lo hi (mean ω)
      second (D ω) (E ω) (V ω) g leaf choices F):=by
  have hbase(j:Fin m):Measurable (fun ω=>ControlledProfile.profile P Λ (u ω) (d0 ω)
      (θ,(target (leaf j),center (leaf j)))):=by
    convert! (VaryingControlledGaussianFields.profile_measurable P Λ θ u d0 hu hd).comp
      (measurable_id.prodMk (measurable_const (a:=(target (leaf j),center (leaf j))))) using 1
  exact TwoFreshGaussianFields.word_average_measurable _
    (fun j=>VaryingControlledGaussianFields.old_covariance_measurable P Λ u d0 hu hd σ target center lo hi j)
    D hD _ _ measurable_const (residual_covariance_measurable P Λ θ q u d0 hu hd σ target center lo hi)
    E V hE hV second choices P.coefficient P.measurable F hF mean hm g leaf _ hbase

end SHE.TwoFreshControlledFields
