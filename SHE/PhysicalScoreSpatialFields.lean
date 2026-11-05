module

public import SHE.PhysicalScoreForestAE
public import SHE.HistorySpatialSections
public import SHE.PredictablePhysicalFields

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1900000
noncomputable section

namespace SHE.PhysicalScoreChain
open Set Filter MeasureTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
  CutoffCarriers FixedOldScoreSupport MeasurableGaussianScores StoppedGaussianFeatures
  PhysicalParentGeometry PhysicalChainArrays HistoryProductMeasure
open scoped BigOperators
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
attribute [local irreducible] MeasurableGaussianScores.coefficient
  MeasurableGeneralizedInverse.generalizedInverse PhysicalChainArrays.covariances
  PhysicalChainArrays.directions
variable {P : Type} [MeasurableSpace P] {R : ReferenceData} {n N : ℕ}
variable (L : CutoffWordLevel.Level R P n)

theorem scoreProduct_measurable (c : Domain → ℝ) (hc : Measurable c) (k : ℕ) :
    Measurable (fun p : History P k => scoreProduct L ((carrier L k).observations.observations p) c k p) := by
  unfold scoreProduct
  apply Finset.measurable_prod
  intro j _
  exact scoreVariance_measurable.comp
    ((old_covariances_measurable L c hc k j).prodMk (old_directions_measurable L k j))

theorem scoreProduct_nonneg (c : Domain → ℝ) (hc : Measurable c)
    {ell : ℝ} (hell : 0 < ell) (hb : ∀ r, ell ≤ c r ∧ c r ≤ R.reference r)
    (hages : ∀ p i, (L.observations.observations p i).stop ≤ (L.observations.observations p i).target)
    (Z : Fin N → Observation) (hZ : ∀ i, (Z i).stop ≤ (Z i).target)
    (k : ℕ) (p : History P k) (g : Fin (n+k) → Fin N) (hg : Function.Injective g)
    (hsel : Selection L Z k p g)
    (hsup : RecursiveGaussianScores.Supported L (profileCovariances L c)
      (profileCovariances L (fun r => R.reference r-c r)) k p) :
    0 ≤ scoreProduct L Z c k p := by
  induction k with
  | zero => exact zero_le_one
  | succ k ih =>
    rw [scoreProduct_step]
    apply mul_nonneg
    · exact ih p.1 (fun i => g i.succ) (hg.comp (Fin.succ_injective _)) hsel.tail hsup.1
    · have hcb (r : Domain) : 0 ≤ c r ∧ c r ≤ R.upper :=
        ⟨hell.le.trans (hb r).1,(hb r).2.trans ((le_abs_self _).trans (R.reference_bound r))⟩
      rw [node_scoreVariance_eq L c hc hcb hages Z hZ g hg hsel hsup.2.2.2.2]
      exact scoreVariance_nonneg hsup.2.1 hsup.2.2.2.2

theorem actual_scoreProduct_nonneg_ae (c : Domain → ℝ) (hc : Measurable c)
    {ell : ℝ} (hell : 0 < ell) (hb : ∀ r, ell ≤ c r ∧ c r ≤ R.reference r)
    (hages : ∀ p i, (L.observations.observations p i).stop ≤ (L.observations.observations p i).target)
    (μ : Measure P) [IsFiniteMeasure μ] (k : ℕ) :
    ∀ᵐ p ∂CutoffWordHistories.historyMeasure R μ k,
      0 ≤ scoreProduct L ((carrier L k).observations.observations p) c k p := by
  filter_upwards [supported_ae L c hc hell hb hages μ k] with p hp
  apply scoreProduct_nonneg L c hc hell hb hages _ (RecursiveScoreSupport.carrier_ages L hages k p)
    k p (fun i => i) (fun _ _ h => h) _ hp
  exact ⟨fun _ => rfl,fun j hj => False.elim (hj ⟨j,rfl⟩)⟩

end SHE.PhysicalScoreChain
