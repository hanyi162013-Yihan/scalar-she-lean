module

public import SHE.ControlledWindowDecomposition

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
namespace SHE.BoundedWindowDecomposition
open Set MeasureTheory ProbabilityTheory Real GaussianIncrement GaussianAssignmentBlocks
  StoppedGaussianFeatures StoppedFourier OldIntervalCovariance ControlledOldIntervals
open scoped BigOperators
local instance : Fact (0<2*π):=⟨by positivity⟩
variable {n r : ℕ}

def residual (P : CanonicalCovariance.ProfileParameters) (Λ : ℝ) (u d : CircleL2)
    (lo hi : Fin r→ℝ) (c : Domain→ℝ) : Domain→ℝ :=
  fun p=>c p-fixedProfile P Λ u d lo hi p

theorem residual_bounds (P : CanonicalCovariance.ProfileParameters) (Λ : ℝ) (u d : CircleL2)
    (lo hi : Fin r→ℝ) (hdisjoint : ∀ j k,j≠k→hi j≤lo k ∨ hi k≤lo j)
    (c : Domain→ℝ) (hb : ∀ p,P.lower≤c p ∧ c p≤P.upper) (p : Domain) :
    P.lower/2≤residual P Λ u d lo hi c p ∧ residual P Λ u d lo hi c p≤P.upper := by
  have hf:=fixedProfile_bounds P Λ u d lo hi hdisjoint p
  have hc:=hb p
  dsimp [residual]
  constructor <;> linarith

theorem residual_measurable (P : CanonicalCovariance.ProfileParameters) (Λ : ℝ) (u d : CircleL2)
    (lo hi : Fin r→ℝ) (c : Domain→ℝ) (hc : Measurable c) :
    Measurable (residual P Λ u d lo hi c):=hc.sub (fixedProfile_measurable P Λ u d lo hi)

/-- A bounded elliptic common future law need not itself solve a
profile fixed point. Its original old intervals and residual reconstruct
its exact stopped covariance, retaining the fixed old profile. -/
theorem covariance_sum_residual (P : CanonicalCovariance.ProfileParameters)
    (Λ : ℝ) (u d : CircleL2) (lo hi : Fin r→ℝ)
    (hdisjoint : ∀ j k,j≠k→hi j≤lo k ∨ hi k≤lo j)
    (c : Domain→ℝ) (hc : Measurable c) (hb : ∀ p,P.lower≤c p ∧ c p≤P.upper)
    (σ target : Fin n→ℝ) (center : Fin n→HeatCircle) (hages : ∀ i,σ i≤target i)
    {q : ℝ} (hq : 0≤q) (hlo : ∀ j,q≤lo j) :
    (∑ j,familyCovariance σ target center (referenceProfile P Λ u d) lo hi j)+
      stoppedCovariance σ target center (residual P Λ u d lo hi c) q=
      stoppedCovariance σ target center c q := by
  rw [←ControlledOldIntervals.covariance_sum P Λ u d σ target center hages lo hi]
  have hfixed : stoppedCovariance σ target center (fixedProfile P Λ u d lo hi) 0=
      stoppedCovariance σ target center (fixedProfile P Λ u d lo hi) q := by
    rw [←FutureWindowDomination.covariance_eq σ target center _ hq,
      ControlledWindowDecomposition.fixedProfile_window P Λ u d lo hi hlo]
  rw [hfixed]
  have ho (p : Domain) : |fixedProfile P Λ u d lo hi p|≤P.lower/2 := by
    rw [abs_of_nonneg (fixedProfile_bounds P Λ u d lo hi hdisjoint p).1]
    exact (fixedProfile_bounds P Λ u d lo hi hdisjoint p).2
  have hr (p : Domain) : |residual P Λ u d lo hi c p|≤P.upper := by
    rw [abs_of_nonneg ((half_pos P.lower_pos).le.trans (residual_bounds P Λ u d lo hi hdisjoint c hb p).1)]
    exact (residual_bounds P Λ u d lo hi hdisjoint c hb p).2
  rw [←StoppedCovarianceSplit.covariance_add σ target center hages q
    (fixedProfile_measurable P Λ u d lo hi) (residual_measurable P Λ u d lo hi c hc) ho hr]
  congr 1
  funext p
  simp only [Pi.add_apply,residual]
  ring

theorem suppressed_diagonal_le (P : CanonicalCovariance.ProfileParameters)
    (Λ : ℝ) (u d : CircleL2) (lo hi : Fin r→ℝ)
    (hdisjoint : ∀ j k,j≠k→hi j≤lo k ∨ hi k≤lo j)
    (c : Domain→ℝ) (hc : Measurable c) (hb : ∀ p,P.lower≤c p ∧ c p≤P.upper)
    (σ target : Fin n→ℝ) (center : Fin n→HeatCircle) (hages : ∀ i,σ i≤target i)
    {q : ℝ} (hq : 0≤q) (hlo : ∀ j,q≤lo j) (is : List (Fin r)) (i : Fin n) :
    SuppressedGaussianLaw.covariance is
      (familyCovariance σ target center (referenceProfile P Λ u d) lo hi)
      (stoppedCovariance σ target center (residual P Λ u d lo hi c) q) i i≤
      stoppedCovariance σ target center c 0 i i := by
  have hcref (p : Domain) : 0≤referenceProfile P Λ u d p ∧ referenceProfile P Λ u d p≤P.lower/2 :=
    ⟨(mul_nonneg (fraction_pos P).le P.lower_pos.le).trans (referenceProfile_bounds P Λ u d p).1,
      (referenceProfile_bounds P Λ u d p).2⟩
  have hA (j : Fin r):=OldIntervalCovariance.covariance_posSemidef σ target center hages _
    (referenceProfile_measurable P Λ u d) hcref (lo j) (hi j)
  have hh:=SuppressedGaussianLaw.coordinate_domination is
    (familyCovariance σ target center (referenceProfile P Λ u d) lo hi) hA
    (stoppedCovariance σ target center (residual P Λ u d lo hi c) q) i
  rw [covariance_sum_residual P Λ u d lo hi hdisjoint c hc hb σ target center hages hq hlo] at hh
  exact hh.trans (FutureWindowDomination.diagonal_le σ target center hages c hc
    (fun p=>⟨P.lower_pos.le.trans (hb p).1,(hb p).2⟩) hq i)

def convexProfile (P : CanonicalCovariance.ProfileParameters) (Λ : ℝ) (u d : CircleL2)
    (θ η ζ : ℝ) (p : Domain) : ℝ :=
  (1-ζ)*ControlledProfile.profile P Λ u d (θ,p)+ζ*ControlledProfile.profile P Λ u d (η,p)

theorem convexProfile_measurable (P : CanonicalCovariance.ProfileParameters) (Λ : ℝ) (u d : CircleL2)
    (θ η ζ : ℝ) : Measurable (convexProfile P Λ u d θ η ζ) := by
  have hm (a : ℝ) : Measurable (fun z : Domain=>ControlledProfile.profile P Λ u d (a,z)) :=
    (ControlledProfile.profile_measurable P Λ u d).comp (measurable_const.prodMk measurable_id)
  exact ((hm θ).const_mul (1-ζ)).add ((hm η).const_mul ζ)

theorem convexProfile_bounds (P : CanonicalCovariance.ProfileParameters) (Λ : ℝ) (u d : CircleL2)
    (θ η : ℝ) {ζ : ℝ} (hζ : 0≤ζ) (hζ1 : ζ≤1) (p : Domain) :
    P.lower≤convexProfile P Λ u d θ η ζ p ∧ convexProfile P Λ u d θ η ζ p≤P.upper := by
  have hθ:=ControlledProfile.profile_bounds P Λ u d (θ,p)
  have hη:=ControlledProfile.profile_bounds P Λ u d (η,p)
  dsimp [convexProfile]
  constructor
  · nlinarith [mul_nonneg (sub_nonneg.mpr hζ1) (sub_nonneg.mpr hθ.1),
      mul_nonneg hζ (sub_nonneg.mpr hη.1)]
  · nlinarith [mul_nonneg (sub_nonneg.mpr hζ1) (sub_nonneg.mpr hθ.2),
      mul_nonneg hζ (sub_nonneg.mpr hη.2)]

end SHE.BoundedWindowDecomposition
