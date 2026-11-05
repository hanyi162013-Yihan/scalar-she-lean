module
public import SHE.MixedNativePairedReferenceRate
public import SHE.NativeKernelConstantCongruence

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SHE.PastReferenceBandConstants
open Real ControlledOldIntervals
open scoped NNReal

def time (P:CanonicalCovariance.ProfileParameters)(k:ℕ)(η:ℝ):ℝ:=
  TerminalCovarianceBudget.constant P (fraction P*P.lower) (PhysicalScoreChain.uniformConstant 1) k η

def covariance(P:CanonicalCovariance.ProfileParameters)(κ M:ℝ)(k:ℕ)(Babs:ℝ≥0)(η:ℝ):ℝ:=
  (PastCovarianceRMS.coefficient P k (MixedPastWordMoments.momentConstant P k k 1
    ((k:ℝ)*(NativeHybridMoments.momentConstant (k+2) Babs κ M)^P.exponent)))^2*
    (time P k η/MarkedProfileTimeFactors.freshDegree P)^2

def baseline(P:CanonicalCovariance.ProfileParameters)(κ M:ℝ)(k:ℕ)(Babs:ℝ≥0)(η:ℝ):ℝ:=
  MixedPastBaselineRMS.momentConstant P k ((NativeHybridMoments.momentConstant (k+2) Babs κ M)^P.exponent)*
    (Fintype.card (OrderedHeatForests.Choices 1 k):ℝ)^2*BaselineOriginalGain.unitCoefficient P^2*
      (time P k η/(3/4:ℝ))^2

def mean(P:CanonicalCovariance.ProfileParameters)(κ M:ℝ)(k p:ℕ)(B0:ℝ≥0)(ρ χ ε η:ℝ):ℝ:=
  let N:=(2*p)*(k+2)
  let CG:=MixedPastWordMoments.momentConstant P k k (2*p)
    ((k:ℝ)*(NativeHybridMoments.momentConstant N B0 κ M)^P.exponent)
  let CD:=MixedHeatedDifferenceMoments.momentConstant N B0 κ M^((1-χ)/(k+2:ℝ))
  (PastMeanRMS.coefficient P k ρ (((CD+CG)/2)^(1/(p:ℝ))))^2*
    ((4:ℝ)^ε)^2*(time P k η/(1/2-ε))^2

theorem covariance_nonneg(P:CanonicalCovariance.ProfileParameters)(κ M:ℝ)(k:ℕ)(B:ℝ≥0)(η:ℝ):
    0≤covariance P κ M k B η:=by unfold covariance; positivity

theorem baseline_nonneg(P:CanonicalCovariance.ProfileParameters)(κ M:ℝ)(k:ℕ)(B:ℝ≥0)(η:ℝ):
    0≤baseline P κ M k B η:=by
  unfold baseline
  exact mul_nonneg (mul_nonneg (mul_nonneg
    (MixedPastBaselineRMS.momentConstant_nonneg P k _) (sq_nonneg _)) (sq_nonneg _)) (sq_nonneg _)

theorem mean_nonneg(P:CanonicalCovariance.ProfileParameters)(κ M:ℝ)(k p:ℕ)(B:ℝ≥0)(ρ χ ε η:ℝ):
    0≤mean P κ M k p B ρ χ ε η:=by unfold mean; positivity

end SHE.PastReferenceBandConstants
