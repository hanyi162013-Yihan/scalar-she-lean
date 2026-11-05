module
public import SHE.PastReferenceBandConstants

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace SHE.PastReferenceConstantUniform
open SHE.PastReferenceBandConstants
open scoped NNReal

theorem word (P Q:CanonicalCovariance.ProfileParameters)(hu:P.upper=Q.upper)(he:P.exponent=Q.exponent)
    (r m b:ℕ)(C:ℝ):MixedPastWordMoments.momentConstant P r m b C=
      MixedPastWordMoments.momentConstant Q r m b C:=by
  simp only [MixedPastWordMoments.momentConstant,FullResidualAssignedMoments.constant,
    OffsetAssignedLeafMoments.leafConstant,hu,he]

theorem omitted(P Q:CanonicalCovariance.ProfileParameters)(hu:P.upper=Q.upper)(he:P.exponent=Q.exponent)
    (r m b:ℕ)(j:Fin m)(C:ℝ):MixedPastOmittedWord.momentConstant P r m b j C=
      MixedPastOmittedWord.momentConstant Q r m b j C:=by
  simp only [MixedPastOmittedWord.momentConstant,OmittedAssignedMoments.constant,
    OffsetAssignedLeafMoments.leafConstant,hu,he]

theorem time_eq(P Q:CanonicalCovariance.ProfileParameters)
    (hl:P.lower=Q.lower)(hu:P.upper=Q.upper)(hh:P.holder=Q.holder)(he:P.exponent=Q.exponent)(k:ℕ)(η:ℝ):
    time P k η=time Q k η:=by
  simp only [time,TerminalCovarianceBudget.constant,PairedBudgetFactors.coefficient,
    PhysicalAssignmentGapScale.prefactor,PhysicalAssignmentGapScale.leafPrefactor,
    PastMeanTimeFactors.frequencyRootConstant,ControlledOldIntervals.fraction,Fin.cases_zero,hl,hu,hh,he]

theorem covariance_eq(P Q:CanonicalCovariance.ProfileParameters)
    (hl:P.lower=Q.lower)(hu:P.upper=Q.upper)(hh:P.holder=Q.holder)(he:P.exponent=Q.exponent)
    (κ M:ℝ)(k:ℕ)(B:ℝ≥0)(η:ℝ):covariance P κ M k B η=covariance Q κ M k B η:=by
  unfold covariance
  rw [he,word P Q hu he,time_eq P Q hl hu hh he]
  simp only [PastCovarianceRMS.coefficient,PastCovarianceRMS.unitGain,
    NativeKernelConstantCongruence.sharp P Q hl hh he,MarkedProfileTimeFactors.freshDegree,hl,he]

theorem baseline_eq(P Q:CanonicalCovariance.ProfileParameters)
    (hl:P.lower=Q.lower)(hu:P.upper=Q.upper)(hh:P.holder=Q.holder)(he:P.exponent=Q.exponent)
    (κ M:ℝ)(k:ℕ)(B:ℝ≥0)(η:ℝ):baseline P κ M k B η=baseline Q κ M k B η:=by
  unfold baseline MixedPastBaselineRMS.momentConstant
  rw [he,time_eq P Q hl hu hh he,NativeKernelConstantCongruence.baseline P Q hl he]
  simp_rw [omitted P Q hu he]

theorem mean_eq(P Q:CanonicalCovariance.ProfileParameters)
    (hl:P.lower=Q.lower)(hu:P.upper=Q.upper)(hh:P.holder=Q.holder)(he:P.exponent=Q.exponent)
    (κ M:ℝ)(k p:ℕ)(B:ℝ≥0)(ρ χ ε η:ℝ):mean P κ M k p B ρ χ ε η=mean Q κ M k p B ρ χ ε η:=by
  unfold mean
  dsimp only
  rw [he,word P Q hu he,time_eq P Q hl hu hh he]
  simp only [PastMeanRMS.coefficient,hl]

variable (D:SmoothApproximation.ScalarData){T:ℝ}(hT:0<T)(hT1:T≤1)
    (hsmall:GaussianProfile.contractionConstant D.ell D.holderConstant D.beta*T^(D.beta/4)≤1/2)
local notation "Smooth"=>ControlledSmoothLimit.smoothTotalParameters D hT hT1 hsmall
local notation "Rough"=>ControlledSmoothLimit.roughTotalParameters D hT hT1 hsmall

/-- These are the exact reference-energy coefficients, chosen from one
numerical template before the smooth companion index and damping. -/
theorem canonical(n:ℕ)(κ M:ℝ)(k p:ℕ)(Babs B0:ℝ≥0)(ρ χ ε η:ℝ):
    covariance (Smooth n) κ M k Babs η=covariance Rough κ M k Babs η ∧
    baseline (Smooth n) κ M k Babs η=baseline Rough κ M k Babs η ∧
    mean (Smooth n) κ M k p B0 ρ χ ε η=mean Rough κ M k p B0 ρ χ ε η:=by
  refine ⟨covariance_eq _ _ rfl rfl rfl rfl _ _ _ _ _,
    baseline_eq _ _ rfl rfl rfl rfl _ _ _ _ _,mean_eq _ _ rfl rfl rfl rfl _ _ _ _ _ _ _ _ _⟩

end SHE.PastReferenceConstantUniform
