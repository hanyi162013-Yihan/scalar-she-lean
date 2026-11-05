module

public import SHE.ControlledAssignedLeaf
public import SHE.GaussianProfileCoordinates

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section

namespace SHE.ControlledStoppedLeaf
open Set MeasureTheory ProbabilityTheory Real GaussianIncrement GaussianAssignmentBlocks
  GaussianCenteredLeafMoments ControlledOldIntervals OldIntervalCovariance ControlledAssignedLeaf
  StoppedGaussianFeatures StoppedFourier ProfileVariance GaussianAudit
open scoped BigOperators
local instance : Fact (0 < 2 * π) := ⟨by positivity⟩
variable {n r k : ℕ}

theorem covariance_decomposition (P : CanonicalCovariance.ProfileParameters)
    (Λ : ℝ) (u d : CircleL2) (θ : ℝ) (lo hi : Fin r → ℝ)
    (hdisjoint : ∀ j l, j ≠ l → hi j ≤ lo l ∨ hi l ≤ lo j)
    (σ target : Fin n → ℝ) (center : Fin n → HeatCircle) (hages : ∀ i, σ i ≤ target i) :
    (∑ j, familyCovariance σ target center (referenceProfile P Λ u d) lo hi j) +
      ControlledFixedReserve.covariance P Λ u d (fixedProfile P Λ u d lo hi)
        σ target center 0 θ =
      stoppedCovariance σ target center (fun p => ControlledProfile.profile P Λ u d (θ,p)) 0 := by
  rw [← covariance_sum P Λ u d σ target center hages lo hi]
  have hc : Measurable (fun p => ControlledProfile.profile P Λ u d (θ,p)) :=
    (ControlledProfile.profile_measurable P Λ u d).comp (measurable_const.prodMk measurable_id)
  have hr := hc.sub (fixedProfile_measurable P Λ u d lo hi)
  have ho (q : ControlledProfile.Domain) : |fixedProfile P Λ u d lo hi q| ≤ P.lower/2 :=
    (abs_of_nonneg (fixedProfile_bounds P Λ u d lo hi hdisjoint q).1).trans_le
      (fixedProfile_bounds P Λ u d lo hi hdisjoint q).2
  have hb (q : ControlledProfile.Domain) :
      |ControlledProfile.profile P Λ u d (θ,q)-fixedProfile P Λ u d lo hi q| ≤ P.upper :=
    (abs_of_nonneg ((half_pos P.lower_pos).le.trans (residual_bounds P Λ u d lo hi hdisjoint θ q).1)).trans_le
      (residual_bounds P Λ u d lo hi hdisjoint θ q).2
  have he := StoppedCovarianceSplit.covariance_add σ target center hages 0
    (fixedProfile_measurable P Λ u d lo hi) hr ho hb
  have hfun : ((fun q => ControlledProfile.profile P Λ u d (θ,q)) - fixedProfile P Λ u d lo hi) =
      (fun q => ControlledProfile.profile P Λ u d (θ,q)-fixedProfile P Λ u d lo hi q) := by
    funext q
    rfl
  rw [hfun] at he
  change _ + stoppedCovariance σ target center
    (fun q => ControlledProfile.profile P Λ u d (θ,q)-fixedProfile P Λ u d lo hi q) 0 = _
  rw [← he]
  congr 1
  funext q
  ring

/-- A native rough leaf has its full-age moment under the actual
suppressed old/residual law. Other observations retain arbitrary original
targets and individual stops; only this leaf's own mean is compatible. -/
theorem native_leaf_even_moment (P : CanonicalCovariance.ProfileParameters)
    (Λ : ℝ) (u d : CircleL2) (θ : ℝ) (lo hi : Fin r → ℝ)
    (hdisjoint : ∀ j l, j ≠ l → hi j ≤ lo l ∨ hi l ≤ lo j)
    (σ target : Fin n → ℝ) (center : Fin n → HeatCircle) (hages : ∀ j, σ j ≤ target j)
    (i : Fin n) (hnative : σ i = target i) (ht : target i ∈ Ioc 0 P.horizon)
    (m : State n) (hm : m i = ControlledProfile.mean Λ u d (θ,(target i,center i)))
    (is : List (Fin r)) (p : ℕ) :
    let A := familyCovariance σ target center (referenceProfile P Λ u d) lo hi
    let B := ControlledFixedReserve.covariance P Λ u d (fixedProfile P Λ u d lo hi)
      σ target center 0 θ
    let μ := (Measure.pi (fun j => multivariateGaussian (0 : State n) (A j))).prod
      (multivariateGaussian (0 : State n) B)
    let F := fun x : (Fin r → State n) × State n =>
      P.coefficient (m i + ((∑ j, suppress is x.1 j) + x.2) i) -
        ControlledProfile.profile P Λ u d (θ,(target i,center i))
    Integrable (fun x => |F x|^(2*p)) μ ∧
      (∫ x, |F x|^(2*p) ∂μ) ≤ leafMomentConstant p P.exponent*
        (P.holder*(upperConstant*P.upper)^(P.exponent/2)*(target i)^(P.exponent/4))^(2*p) := by
  intro A B μ F
  have hcref (q : ControlledProfile.Domain) : 0 ≤ referenceProfile P Λ u d q ∧
      referenceProfile P Λ u d q ≤ P.lower/2 :=
    ⟨(mul_nonneg (fraction_pos P).le P.lower_pos.le).trans (referenceProfile_bounds P Λ u d q).1,
      (referenceProfile_bounds P Λ u d q).2⟩
  have hA (j : Fin r) : (A j).PosSemidef := covariance_posSemidef σ target center hages _
    (referenceProfile_measurable P Λ u d) hcref (lo j) (hi j)
  have hc : Measurable (fun q => ControlledProfile.profile P Λ u d (θ,q)) :=
    (ControlledProfile.profile_measurable P Λ u d).comp (measurable_const.prodMk measurable_id)
  have hcb (q : ControlledProfile.Domain) : 0 ≤ ControlledProfile.profile P Λ u d (θ,q) ∧
      ControlledProfile.profile P Λ u d (θ,q) ≤ P.upper :=
    ⟨P.lower_pos.le.trans (ControlledProfile.profile_bounds P Λ u d (θ,q)).1,
      (ControlledProfile.profile_bounds P Λ u d (θ,q)).2⟩
  have hB : B.PosSemidef := by
    apply StoppedCovarianceSplit.covariance_posSemidef σ target center hages 0
      (hc.sub (fixedProfile_measurable P Λ u d lo hi))
    intro q
    exact ⟨(half_pos P.lower_pos).le.trans (residual_bounds P Λ u d lo hi hdisjoint θ q).1,
      (residual_bounds P Λ u d lo hi hdisjoint θ q).2⟩
  let C := stoppedCovariance σ target center (fun q => ControlledProfile.profile P Λ u d (θ,q)) 0
  have hC : C.PosSemidef := StoppedCovarianceSplit.covariance_posSemidef σ target center hages 0 hc hcb
  have hsum : (∑ j, A j) + B = C := covariance_decomposition P Λ u d θ lo hi hdisjoint σ target center hages
  have hbound (z : ℝ) : |P.coefficient z| ≤ P.upper := by
    rw [abs_of_nonneg (P.lower_pos.le.trans (P.lower_bound z))]
    exact P.upper_bound z
  have hbase : GaussianProfile.gaussianAverage P.coefficient (m i) (C i i) =
      ControlledProfile.profile P Λ u d (θ,(target i,center i)) := by
    have hh := GaussianProfileBaseline.controlled_coordinate_baseline P Λ u d θ σ target center
      hages i hnative ht m hm
    change (∫ y : State n, P.coefficient ((m+y) i) ∂multivariateGaussian 0 C) = _ at hh
    simp only [PiLp.add_apply] at hh
    rw [NativeFirstWordRepresentation.coordinate_average hC i P.coefficient P.measurable (m i)] at hh
    exact hh
  have hh := SuppressedReferenceMoments.reference_leaf_even_moment is A hA B hB i
    P.coefficient P.measurable P.upper P.holder P.exponent hbound P.holder_nonneg
    P.exponent_pos.le P.holder_bound (m i) p
  dsimp only at hh
  rw [hsum, hbase] at hh
  refine ⟨hh.1, hh.2.trans ?_⟩
  have hdiag : C i i = varianceMap (fun q => ControlledProfile.profile P Λ u d (θ,q)) (target i) (center i) :=
    GaussianProfileBaseline.coordinate_covariance_eq_native σ target center _ hc P.upper hcb
      i hnative ht.1 (ht.2.trans P.horizon_le_one)
  have hv : C i i ≤ upperConstant*P.upper*(target i)^(1/2 : ℝ) := by
    rw [hdiag]
    exact (varianceMap_elliptic hc ht.1 (ht.2.trans P.horizon_le_one) (by norm_num : 0 ≤ (0 : ℝ))
      P.upper_nonneg (fun s _ y => (hcb (s,y)).1) (fun s _ y => (hcb (s,y)).2) (center i)).2
  have hp := PhysicalOldBlockMoments.physical_variance_power hC.diag_nonneg P.upper_nonneg
    ht.1 P.exponent_pos.le hv
  have hs : P.holder*(C i i)^(P.exponent/2) ≤
      P.holder*(upperConstant*P.upper)^(P.exponent/2)*(target i)^(P.exponent/4) := by
    convert! mul_le_mul_of_nonneg_left hp P.holder_nonneg using 1
    ring
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀
    (mul_nonneg P.holder_nonneg (rpow_nonneg hC.diag_nonneg _)) hs _) (leafMomentConstant_nonneg _ _)

end SHE.ControlledStoppedLeaf
