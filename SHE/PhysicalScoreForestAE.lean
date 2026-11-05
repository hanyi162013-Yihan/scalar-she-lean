module

public import SHE.PhysicalScoreProduct

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2100000
noncomputable section

namespace SHE.PhysicalScoreChain
open Set Filter MeasureTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
  CutoffCarriers FixedOldScoreSupport MeasurableGaussianScores StoppedGaussianFeatures
  PhysicalParentGeometry OrderedHeatForests
open scoped BigOperators
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
attribute [local irreducible] MeasurableGaussianScores.coefficient
  MeasurableGeneralizedInverse.generalizedInverse
variable {P : Type} [MeasurableSpace P] {R : ReferenceData} {n : ℕ}
variable (L : CutoffWordLevel.Level R P n)

/-- The actual growing-history old Gaussian score product has the literal
parent-forest envelope almost everywhere. Every range, frame-extension and
spatial exceptional-set condition is discharged from the original physical
model. The remaining small-age condition is the stated analytic horizon. -/
theorem actual_score_forest_ae :
    ∃ H C : ℕ → ℝ, (∀ k, 0 < H k) ∧ (∀ k, 0 < C k) ∧
    ∀ (c : Domain → ℝ), Measurable c → ∀ {ell : ℝ}, 0 < ell →
    (∀ r, ell ≤ c r ∧ c r ≤ R.reference r) →
    ∀ (hages : ∀ p i, (L.observations.observations p i).stop ≤ (L.observations.observations p i).target),
    ∀ (μ : Measure P) [IsFiniteMeasure μ] (k : ℕ),
    ∀ᵐ p ∂CutoffWordHistories.historyMeasure R μ k,
      ∀ (hp : StrictHistory L k p), SmallHistory L H k p →
      scoreProduct L ((carrier L k).observations.observations p) c k p ≤
        timeWeight L ell C k p * parentDensity 2 (by norm_num) k
          (fun i => ((carrier L k).observations.observations p i).target)
          (carrier_orderedTimes L hages k p hp)
          (fun i => ((carrier L k).observations.observations p i).center) := by
  obtain ⟨H,C,hH,hC,hV⟩ := allNodeBounds_ae L
  refine ⟨H,C,hH,hC,?_⟩
  intro c hc ell hell hb hages μ _ k
  filter_upwards [hV c hc hell hb hages μ k,supported_ae L c hc hell hb hages μ k]
    with p hbound hsup
  intro hp hsmall
  let Z := (carrier L k).observations.observations p
  have hsel : Selection L Z k p (fun i => i) :=
    ⟨fun _ => rfl,fun j hj => False.elim (hj ⟨j,rfl⟩)⟩
  have hh := scoreProduct_heat_bound L c hc hell hb hages H C (fun j => (hC j).le)
    Z (RecursiveScoreSupport.carrier_ages L hages k p) k p (fun i => i)
    (fun _ _ h => h) hsel hp hsmall hbound hsup
  rw [activeHeatProduct_eq_parentDensity L hages Z k p (fun i => i) (fun _ _ h => h) hsel hp] at hh
  exact hh

end SHE.PhysicalScoreChain
