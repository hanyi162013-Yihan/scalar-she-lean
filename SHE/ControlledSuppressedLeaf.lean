module

public import SHE.SuppressedReferenceMoments
public import SHE.OldIntervalLaw
public import SHE.GaussianProfileBaseline
public import SHE.PhysicalOldBlockMoments

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section

namespace SHE.ControlledSuppressedLeaf
open Set MeasureTheory ProbabilityTheory Real GaussianIncrement GaussianAssignmentBlocks
  GaussianCenteredLeafMoments ControlledOldIntervals StoppedGaussianFeatures StoppedFourier
  OldIntervalCovariance ProfileVariance
open scoped BigOperators NNReal
local instance : Fact (0 < 2 * π) := ⟨by positivity⟩
variable [MeasurableSpace CircleL2] [BorelSpace CircleL2] {n r : ℕ}

omit [MeasurableSpace CircleL2] [BorelSpace CircleL2] in
theorem covariance_decomposition (P : CanonicalCovariance.ProfileParameters)
    (Λ : ℝ) (u d : CircleL2) (θ : ℝ) (lo hi : Fin r → ℝ)
    (target : Fin n → ℝ) (center : Fin n → HeatCircle) :
    (∑ j, familyCovariance target target center (referenceProfile P Λ u d) lo hi j) +
      ControlledFixedReserve.covariance P Λ u d (fixedProfile P Λ u d lo hi)
        target target center 0 θ =
      stoppedCovariance target target center (fun p => ControlledProfile.profile P Λ u d (θ,p)) 0 := by
  rw [← covariance_sum P Λ u d target target center (fun _ => le_rfl) lo hi]
  have hc : Measurable (fun p => ControlledProfile.profile P Λ u d (θ,p)) :=
    (ControlledProfile.profile_measurable P Λ u d).comp (measurable_const.prodMk measurable_id)
  have hco (p : ControlledProfile.Domain) : |ControlledProfile.profile P Λ u d (θ,p)| ≤ P.upper :=
    (abs_of_nonneg (P.lower_pos.le.trans (ControlledProfile.profile_bounds P Λ u d (θ,p)).1)).trans_le
      (ControlledProfile.profile_bounds P Λ u d (θ,p)).2
  have hb : ∃ M, ∀ p, |fixedProfile P Λ u d lo hi p| ≤ M := by
    refine ⟨(r : ℝ)*(P.lower/2), ?_⟩
    intro p
    unfold fixedProfile sumProfile
    calc
      _ ≤ ∑ j : Fin r, |intervalProfile (referenceProfile P Λ u d) (lo j) (hi j) p| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : Fin r, P.lower/2 := by
        apply Finset.sum_le_sum
        intro j _
        by_cases hp : p ∈ timeSet (lo j) (hi j)
        · rw [intervalProfile, Set.indicator_of_mem hp, abs_of_nonneg
            ((mul_nonneg (fraction_pos P).le P.lower_pos.le).trans (referenceProfile_bounds P Λ u d p).1)]
          exact (referenceProfile_bounds P Λ u d p).2
        · simp only [intervalProfile, Set.indicator_of_notMem hp, abs_zero]
          exact div_nonneg P.lower_pos.le (by norm_num)
      _ = _ := by simp
  obtain ⟨M, hM⟩ := hb
  have he := StoppedCovarianceSplit.covariance_sub target target center (fun _ => le_rfl) 0
    hc (fixedProfile_measurable P Λ u d lo hi) hco hM
  change _ + stoppedCovariance target target center
    (fun p => ControlledProfile.profile P Λ u d (θ,p)-fixedProfile P Λ u d lo hi p) 0 = _
  rw [he]
  abel

/-- Every unassigned leaf of the actual controlled old/residual word has
its full-age rough gain after arbitrary foreign suppression. Its baseline
is the original self-consistent profile, never a reduced-law expectation. -/
theorem leaf_even_moment (P : CanonicalCovariance.ProfileParameters)
    (Λ : ℝ) (u d : CircleL2) (θ : ℝ) (lo hi : Fin r → ℝ)
    (hdisjoint : ∀ j k, j ≠ k → hi j ≤ lo k ∨ hi k ≤ lo j)
    (target : Fin n → ℝ) (center : Fin n → HeatCircle)
    (ht : ∀ i, target i ∈ Ioc 0 P.horizon) (m : State n)
    (hm : ∀ i, m i = ControlledProfile.mean Λ u d (θ,(target i,center i)))
    (is : List (Fin r)) (i : Fin n) (p : ℕ) :
    let A := familyCovariance target target center (referenceProfile P Λ u d) lo hi
    let B := ControlledFixedReserve.covariance P Λ u d (fixedProfile P Λ u d lo hi)
      target target center 0 θ
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
  have hA (j : Fin r) : (A j).PosSemidef :=
    covariance_posSemidef target target center (fun _ => le_rfl) _
      (referenceProfile_measurable P Λ u d) hcref (lo j) (hi j)
  have hc : Measurable (fun q => ControlledProfile.profile P Λ u d (θ,q)) :=
    (ControlledProfile.profile_measurable P Λ u d).comp (measurable_const.prodMk measurable_id)
  have hcb (q : ControlledProfile.Domain) : 0 ≤ ControlledProfile.profile P Λ u d (θ,q) ∧
      ControlledProfile.profile P Λ u d (θ,q) ≤ P.upper :=
    ⟨P.lower_pos.le.trans (ControlledProfile.profile_bounds P Λ u d (θ,q)).1,
      (ControlledProfile.profile_bounds P Λ u d (θ,q)).2⟩
  have hB : B.PosSemidef := by
    apply StoppedCovarianceSplit.covariance_posSemidef target target center (fun _ => le_rfl) 0
      (hc.sub (fixedProfile_measurable P Λ u d lo hi))
    intro q
    exact ⟨(half_pos P.lower_pos).le.trans (residual_bounds P Λ u d lo hi hdisjoint θ q).1,
      (residual_bounds P Λ u d lo hi hdisjoint θ q).2⟩
  let C := stoppedCovariance target target center (fun q => ControlledProfile.profile P Λ u d (θ,q)) 0
  have hC : C.PosSemidef :=
    StoppedCovarianceSplit.covariance_posSemidef target target center (fun _ => le_rfl) 0 hc hcb
  have hsum : (∑ j, A j) + B = C := covariance_decomposition P Λ u d θ lo hi target center
  have hbound (z : ℝ) : |P.coefficient z| ≤ P.upper := by
    rw [abs_of_nonneg (P.lower_pos.le.trans (P.lower_bound z))]
    exact P.upper_bound z
  have hbase : GaussianProfile.gaussianAverage P.coefficient (m i) (C i i) =
      ControlledProfile.profile P Λ u d (θ,(target i,center i)) := by
    have hh := GaussianProfileBaseline.controlled_native_baseline P Λ u d θ target center ht m hm i
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
  have hv := StoppedGaussianMarginals.native_coordinate_variance_bound target center
    (fun j => (ht j).1) (fun j => (ht j).2.trans P.horizon_le_one) _ hc P.upper hcb i
  have hdiag : Var[EuclideanSpace.proj (𝕜 := ℝ) i; multivariateGaussian 0 C] = C i i :=
    variance_eval_multivariateGaussian hC i
  change Var[EuclideanSpace.proj (𝕜 := ℝ) i; multivariateGaussian 0 C] ≤ _ at hv
  rw [hdiag] at hv
  have hp := PhysicalOldBlockMoments.physical_variance_power hC.diag_nonneg P.upper_nonneg
    (ht i).1 P.exponent_pos.le hv
  have hs : P.holder*(C i i)^(P.exponent/2) ≤
      P.holder*(upperConstant*P.upper)^(P.exponent/2)*(target i)^(P.exponent/4) := by
    convert! mul_le_mul_of_nonneg_left hp P.holder_nonneg using 1
    ring
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀
    (mul_nonneg P.holder_nonneg (rpow_nonneg hC.diag_nonneg _)) hs _)
    (leafMomentConstant_nonneg _ _)

end SHE.ControlledSuppressedLeaf
