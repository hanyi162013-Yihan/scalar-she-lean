module

public import SHE.FutureWindowDomination

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1900000
noncomputable section

namespace SHE.ControlledWindowDecomposition
open Set MeasureTheory ProbabilityTheory Real GaussianIncrement GaussianAssignmentBlocks
  StoppedGaussianFeatures StoppedFourier OldIntervalCovariance ControlledOldIntervals
open scoped BigOperators
local instance : Fact (0<2*π) := ⟨by positivity⟩
variable {n r : ℕ}

theorem fixedProfile_window (P : CanonicalCovariance.ProfileParameters)
    (Λ : ℝ) (u d : CircleL2) (lo hi : Fin r→ℝ) {q : ℝ} (hlo : ∀ j,q≤lo j) :
    FutureWindowDomination.profile (fixedProfile P Λ u d lo hi) q=
      fixedProfile P Λ u d lo hi := by
  funext p
  by_cases hp : p∈FutureWindowDomination.timeSet q
  · simp only [FutureWindowDomination.profile,indicator_of_mem hp]
  · have ht : p.1<q := lt_of_not_ge (fun hh => hp ⟨hh,mem_univ _⟩)
    have hzero : fixedProfile P Λ u d lo hi p=0 := by
      unfold fixedProfile OldIntervalCovariance.sumProfile
      apply Finset.sum_eq_zero
      intro j _
      apply indicator_of_notMem
      intro hm
      exact (not_lt_of_ge ((hlo j).trans hm.1.1.le)) ht
    rw [FutureWindowDomination.profile,indicator_of_notMem hp,hzero]

/-- The actual old intervals after q plus the positive residual on the
q-window reconstruct exactly the full conditional future covariance.
No pre-q covariance is inserted into the Gaussian future. -/
theorem covariance_sum_residual (P : CanonicalCovariance.ProfileParameters)
    (Λ : ℝ) (u d : CircleL2) (θ : ℝ) (lo hi : Fin r→ℝ)
    (hdisjoint : ∀ j k,j≠k → hi j≤lo k ∨ hi k≤lo j)
    (σ target : Fin n→ℝ) (center : Fin n→HeatCircle) (hages : ∀ i,σ i≤target i)
    {q : ℝ} (hq : 0≤q) (hlo : ∀ j,q≤lo j) :
    (∑ j,familyCovariance σ target center (referenceProfile P Λ u d) lo hi j)+
      ControlledFixedReserve.covariance P Λ u d (fixedProfile P Λ u d lo hi)
        σ target center q θ=
      stoppedCovariance σ target center (fun p => ControlledProfile.profile P Λ u d (θ,p)) q := by
  rw [←covariance_sum P Λ u d σ target center hages lo hi]
  have hfixed : stoppedCovariance σ target center (fixedProfile P Λ u d lo hi) 0=
      stoppedCovariance σ target center (fixedProfile P Λ u d lo hi) q := by
    rw [←FutureWindowDomination.covariance_eq σ target center _ hq,
      fixedProfile_window P Λ u d lo hi hlo]
  rw [hfixed]
  have hc : Measurable (fun p => ControlledProfile.profile P Λ u d (θ,p)) :=
    (ControlledProfile.profile_measurable P Λ u d).comp (measurable_const.prodMk measurable_id)
  have hr := hc.sub (fixedProfile_measurable P Λ u d lo hi)
  have ho (p : ControlledProfile.Domain) : |fixedProfile P Λ u d lo hi p|≤P.lower/2 :=
    (abs_of_nonneg (fixedProfile_bounds P Λ u d lo hi hdisjoint p).1).trans_le
      (fixedProfile_bounds P Λ u d lo hi hdisjoint p).2
  have hb (p : ControlledProfile.Domain) :
      |ControlledProfile.profile P Λ u d (θ,p)-fixedProfile P Λ u d lo hi p|≤P.upper :=
    (abs_of_nonneg ((half_pos P.lower_pos).le.trans (residual_bounds P Λ u d lo hi hdisjoint θ p).1)).trans_le
      (residual_bounds P Λ u d lo hi hdisjoint θ p).2
  have he := StoppedCovarianceSplit.covariance_add σ target center hages q
    (fixedProfile_measurable P Λ u d lo hi) hr ho hb
  have hfun : ((fun p => ControlledProfile.profile P Λ u d (θ,p))-fixedProfile P Λ u d lo hi)=
      (fun p => ControlledProfile.profile P Λ u d (θ,p)-fixedProfile P Λ u d lo hi p) := by
    funext p
    rfl
  rw [hfun] at he
  change _+stoppedCovariance σ target center
    (fun p => ControlledProfile.profile P Λ u d (θ,p)-fixedProfile P Λ u d lo hi p) q=_
  rw [←he]
  congr 1
  funext p
  ring

/-- Every suppressed physical old/residual leaf at q has variance at
most the FULL profile variance at zero, which supplies its unchanged
baseline. Actual mean displacement is a separate issue. -/
theorem suppressed_diagonal_le (P : CanonicalCovariance.ProfileParameters)
    (Λ : ℝ) (u d : CircleL2) (θ : ℝ) (lo hi : Fin r→ℝ)
    (hdisjoint : ∀ j k,j≠k → hi j≤lo k ∨ hi k≤lo j)
    (σ target : Fin n→ℝ) (center : Fin n→HeatCircle) (hages : ∀ i,σ i≤target i)
    {q : ℝ} (hq : 0≤q) (hlo : ∀ j,q≤lo j) (is : List (Fin r)) (i : Fin n) :
    SuppressedGaussianLaw.covariance is
      (familyCovariance σ target center (referenceProfile P Λ u d) lo hi)
      (ControlledFixedReserve.covariance P Λ u d (fixedProfile P Λ u d lo hi) σ target center q θ) i i≤
      stoppedCovariance σ target center (fun p => ControlledProfile.profile P Λ u d (θ,p)) 0 i i := by
  have hcref (p : ControlledProfile.Domain) : 0≤referenceProfile P Λ u d p ∧
      referenceProfile P Λ u d p≤P.lower/2 :=
    ⟨(mul_nonneg (fraction_pos P).le P.lower_pos.le).trans (referenceProfile_bounds P Λ u d p).1,
      (referenceProfile_bounds P Λ u d p).2⟩
  have hA (j : Fin r) := OldIntervalCovariance.covariance_posSemidef σ target center hages _
    (referenceProfile_measurable P Λ u d) hcref (lo j) (hi j)
  have hh := SuppressedGaussianLaw.coordinate_domination is
    (familyCovariance σ target center (referenceProfile P Λ u d) lo hi) hA
    (ControlledFixedReserve.covariance P Λ u d (fixedProfile P Λ u d lo hi) σ target center q θ) i
  rw [covariance_sum_residual P Λ u d θ lo hi hdisjoint σ target center hages hq hlo] at hh
  apply hh.trans
  exact FutureWindowDomination.diagonal_le σ target center hages _
    ((ControlledProfile.profile_measurable P Λ u d).comp (measurable_const.prodMk measurable_id))
    (fun p => ⟨P.lower_pos.le.trans (ControlledProfile.profile_bounds P Λ u d (θ,p)).1,
      (ControlledProfile.profile_bounds P Λ u d (θ,p)).2⟩) hq i

end SHE.ControlledWindowDecomposition
