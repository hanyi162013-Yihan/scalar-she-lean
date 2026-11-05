module

public import SHE.PhysicalNodeScoreHeat

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1700000
noncomputable section

namespace SHE.PhysicalScoreChain
open Set MeasureTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
  CutoffCarriers FixedOldScoreSupport MeasurableGaussianScores StoppedGaussianFeatures
open scoped BigOperators
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
attribute [local irreducible] MeasurableGaussianScores.coefficient
  MeasurableGeneralizedInverse.generalizedInverse
variable {P : Type} [MeasurableSpace P] {R : ReferenceData} {n : ℕ}
variable (L : CutoffWordLevel.Level R P n)

def nodeEnergy (c : Domain → ℝ) (k : ℕ) (p : History P (k+1)) : ℝ :=
  scoreVariance (profileCovariances L c k p) (row L k p)

def nodeHeat (k : ℕ) (p : History P (k+1)) : ℝ :=
  ∑ i : Fin (n+k), ‖ProfileVariance.heatPhysical
    (2*(((carrier L k).observations.observations p.1 i).target-(carrier L k).nodeTime p))
    ((carrier L k).observations.observations p.1 i).center p.2.2‖

theorem nodeEnergy_measurable (c : Domain → ℝ) (hc : Measurable c) (k : ℕ) :
    Measurable (nodeEnergy L c k) :=
  scoreVariance_measurable.comp ((profileCovariances_measurable L c hc k).prodMk (row_measurable L k))

theorem nodeHeat_measurable (k : ℕ) : Measurable (nodeHeat L k) := by
  apply Finset.measurable_sum
  intro i _
  have ha : Measurable (fun p : History P (k+1) =>
      2*(((carrier L k).observations.observations p.1 i).target-(carrier L k).nodeTime p)) :=
    measurable_const.mul (((carrier L k).observations.target_measurable i).comp measurable_fst |>.sub
      (carrier L k).nodeTime_measurable)
  have hc : Measurable (fun p : History P (k+1) =>
      (((carrier L k).observations.observations p.1 i).center,p.2.2)) :=
    (((carrier L k).observations.center_measurable i).comp measurable_fst).prodMk measurable_snd.snd
  exact (VariableObservations.heatPhysical_joint_measurable.comp (ha.prodMk hc)).norm

theorem nodeHeat_nonneg (k : ℕ) (p : History P (k+1)) : 0 ≤ nodeHeat L k p :=
  Finset.sum_nonneg (fun _ _ => norm_nonneg _)

end SHE.PhysicalScoreChain
