module
public import SHE.ControlledDefectConstantUniform
public import SHE.DefectGapFiniteCoefficient
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1000000
namespace SHE.CanonicalDefectCosts
open SmoothApproximation
variable (D:ScalarData){T0:ℝ}(hT0:0<T0)(hT1:T0≤1)
variable (hsmall:GaussianProfile.contractionConstant D.ell D.holderConstant D.beta*T0^(D.beta/4)≤1/2)
local notation "Smooth"=>ControlledSmoothLimit.smoothTotalParameters D hT0 hT1 hsmall
local notation "Rough"=>ControlledSmoothLimit.roughTotalParameters D hT0 hT1 hsmall
local notation "δ" P:max=>ControlledOldIntervals.fraction P*(P).lower

/-- The complete old collision/root-frequency cost is literally the
same numerical constant for every canonical smoothing index. -/
theorem frequency_constant (n k:ℕ)(A η:ℝ):
    DefectGapFrequency.constant (Smooth n) (δ (Smooth n)) (PhysicalScoreChain.uniformConstant 1) k A η=
      DefectGapFrequency.constant Rough (δ Rough) (PhysicalScoreChain.uniformConstant 1) k A η:=rfl

variable (m W:ℝ)(hm:0<m)(hW:0≤W)(ρ:ℝ)(hρ:0<ρ)(hρhalf:ρ<1/2)

/-- The full finite-depth first-defect coefficient is fixed before
choosing any smoothing index, damping parameter or band. -/
theorem finite_constant (n N:ℕ)(A η:ℝ):
    DefectGapFiniteCoefficient.constant (Smooth n) (δ (Smooth n)) (PhysicalScoreChain.uniformConstant 1) A η N
      (fun i=>ControlledDefectConstants.constant m W hm hW ρ hρ hρhalf i (Smooth n))=
    DefectGapFiniteCoefficient.constant Rough (δ Rough) (PhysicalScoreChain.uniformConstant 1) A η N
      (fun i=>ControlledDefectConstants.constant m W hm hW ρ hρ hρhalf i Rough):=rfl
end SHE.CanonicalDefectCosts
