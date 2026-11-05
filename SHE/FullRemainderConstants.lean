module

public import SHE.FullScalarRemainderTail
public import SHE.HilbertDyadicConvergence
public import SHE.SmoothComparisonParameters

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
namespace SHE.FullRemainderConstants
open Real SmoothApproximation
open scoped NNReal

/-- Explicit common all-time comparison constant. It contains no
smooth coefficient derivative, no band index and no band window. -/
def comparison (P:CanonicalCovariance.ProfileParameters) (κ M H:ℝ) (N:ℕ)
    (χ η:ℝ) (order:ℕ) (B0 B1 Bcov:ℝ≥0):ℝ:=
  let Cp:=PairedBudgetFrequency.constant P κ M (ControlledOldIntervals.fraction P*P.lower)
    (PhysicalScoreChain.uniformConstant 1) N χ η order B0
  let Cc:=TerminalCovarianceBudget.constant P (ControlledOldIntervals.fraction P*P.lower)
    (PhysicalScoreChain.uniformConstant 1) N η
  let CC:=MixedPastWordMoments.momentConstant P N N 1
    ((N:ℝ)*(NativeHybridMoments.momentConstant (N+2) Bcov κ M)^P.exponent)
  let Cm:=2*P.holder*(3*((N:ℝ)/(P.lower/2)))
  let base:=CC*Cm^2*(Fintype.card (OrderedHeatForests.Choices 1 N):ℝ)^2
  let cap:=max 1 (MixedHeatedDifferenceMoments.momentConstant 1 B1 κ M*H)
  2*base*(Cc/2)^2*cap^(P.exponent-χ)*H^(1-P.exponent)+12*Cp^2*H^(1-χ)

/-- Prefactor before the genuine coupled global-energy power and the
explicit geometric R_J^-8 tail. -/
def prefactor (P:CanonicalCovariance.ProfileParameters) (κ M H Λ ρ:ℝ) (N:ℕ)
    (χ η:ℝ) (order:ℕ) (B0 B1 Bcov:ℝ≥0):ℝ:=
  Λ^(-ρ)*comparison P κ M H N χ η order B0 B1 Bcov*
    (ScalarHeatBandBernstein.amplitude P.upper P.holder P.exponent (N+1))^2*
      (2:ℝ)^(2*(P.exponent/2+η))

variable (D:ScalarData) {T0:ℝ} (hT0:0<T0) (hT1:T0≤1)
variable (hsmall:GaussianProfile.contractionConstant D.ell D.holderConstant D.beta*T0^(D.beta/4)≤1/2)
local notation "Smooth"=>ControlledSmoothLimit.smoothTotalParameters D hT0 hT1 hsmall
local notation "Rough"=>ControlledSmoothLimit.roughTotalParameters D hT0 hT1 hsmall

/-- The ENTIRE actual high-finite-order remainder constant is uniform
in the smooth companion index. Only the original numerical scalar
ellipticity, boundedness and Hölder parameters enter. -/
theorem comparison_smooth (n:ℕ) (κ M H:ℝ) (N:ℕ) (χ η:ℝ) (order:ℕ) (B0 B1 Bcov:ℝ≥0):
    comparison (Smooth n) κ M H N χ η order B0 B1 Bcov=
      comparison Rough κ M H N χ η order B0 B1 Bcov:=by rfl

theorem prefactor_smooth (n:ℕ) (κ M H Λ ρ:ℝ) (N:ℕ) (χ η:ℝ) (order:ℕ) (B0 B1 Bcov:ℝ≥0):
    prefactor (Smooth n) κ M H Λ ρ N χ η order B0 B1 Bcov=
      prefactor Rough κ M H Λ ρ N χ η order B0 B1 Bcov:=by rfl

theorem span_smooth (n j:ℕ):
    RemainderBandSpans.span (Smooth n).exponent j=RemainderBandSpans.span (Rough).exponent j:=rfl

theorem depth_smooth (n:ℕ):SHE.depth (Smooth n).exponent=SHE.depth (Rough).exponent:=rfl

end SHE.FullRemainderConstants
