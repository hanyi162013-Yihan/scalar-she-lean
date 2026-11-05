module
public import SHE.ActualGaussianMasterParameters
public import SHE.CanonicalCompanionHorizon
public import SHE.CommonComparisonCutoff
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace SHE.CanonicalActualComparisonRecipe
open Real
open scoped NNReal
/-- All numerical choices and the common profile horizon precede every
original probability space, damping value and companion index. -/
theorem exists_recipe(D:SmoothApproximation.ScalarData)(H:ℝ≥0)(hH:0<H):
    ∃(T:ℝ)(hT:0<T)(hT1:T≤1)
      (hprofile:GaussianProfile.contractionConstant D.ell D.holderConstant D.beta*T^(D.beta/4)≤1/2),
    ∃ζ:ℝ,∃p:ℕ,
      (0<ζ ∧ ζ≤D.beta/100 ∧ 0<p ∧
       0<SHE.rho D.beta+ζ ∧ SHE.rho D.beta+ζ<1/2 ∧
       1≤(p:ℝ)*(1-SHE.chi D.beta) ∧
       1≤(p:ℝ)*(1-ActualReferenceMasterClosure.referenceExponent D.beta) ∧
       (20:ℝ)≤ζ*(2*((p-1:ℕ):ℝ)) ∧
       0<NativeBandFrequencyRates.currentDegree D.beta (SHE.rho D.beta) (SHE.chi D.beta) ζ ∧
       0<NativeBandFrequencyRates.pastDegree D.beta ζ ∧
       0<SignedNativeBandFrequency.goodDegree D.beta ζ ζ ∧
       (16:ℝ)<SignedNativeBandFrequency.badDegree D.beta 20 ζ) ∧
      (∀n:ℕ,let P:=ControlledSmoothLimit.smoothTotalParameters D hT hT1 hprofile n;
        (ProfileStability.memoryConstant P.lower P.holder P.exponent*
          ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2) ∧
        (ProfileStability.memoryConstant P.lower P.holder P.exponent*
          ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)) ∧
      ∃B:ℝ,1≤B ∧ ∀Λ:ℝ,B≤Λ→∃J:ℕ,
        Λ^(1/4:ℝ)<(2:ℝ)^J ∧ (2:ℝ)^J≤2*Λ^(1/4:ℝ) ∧
        Λ^(1/4:ℝ)<(2:ℝ)^(J+1) ∧ (2:ℝ)^(J+1)≤4*Λ^(1/4:ℝ) ∧
        CommonComparisonCutoff.Ready D.ell D.cap D.ell_pos D.cap_nonneg
          (SHE.rho D.beta) (by dsimp [SHE.rho];linarith [D.beta_le])
          (by dsimp [SHE.rho];linarith [D.beta_pos])
          D hT hT1 hprofile H hH (SHE.depth D.beta+1) J:=by
  obtain ⟨T,hT,hT1,hprofile,hsmall⟩:=CanonicalCompanionHorizon.common D
  obtain ⟨ζ,p,hparams⟩:=ActualGaussianMasterParameters.exists_parameters D.beta_pos D.beta_le
  have hr:0<SHE.rho D.beta:=by dsimp [SHE.rho];linarith [D.beta_le]
  have hrh:SHE.rho D.beta<1/2:=by dsimp [SHE.rho];linarith [D.beta_pos]
  obtain ⟨B,hB,hcut⟩:=CommonComparisonCutoff.exists_threshold D.ell D.cap D.ell_pos D.cap_nonneg
    (SHE.rho D.beta) hr hrh D hT hT1 hprofile H hH (SHE.depth D.beta+1)
  exact ⟨T,hT,hT1,hprofile,ζ,p,hparams,hsmall,B,hB,hcut⟩
end SHE.CanonicalActualComparisonRecipe
