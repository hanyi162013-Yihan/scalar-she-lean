module

public import SHE.PhysicalNodeScoreAE
public import SHE.PhysicalParentProduct

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1900000
noncomputable section

namespace SHE.PhysicalScoreChain
open Set Filter MeasureTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
  CutoffCarriers FixedOldScoreSupport MeasurableGaussianScores StoppedGaussianFeatures
open scoped BigOperators
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
attribute [local irreducible] MeasurableGaussianScores.coefficient
  MeasurableGeneralizedInverse.generalizedInverse
variable {P : Type} [MeasurableSpace P] {R : ReferenceData} {n : ℕ}
variable (L : CutoffWordLevel.Level R P n)

def AllNodeBounds (c : Domain → ℝ) (ell : ℝ) (H C : ℕ → ℝ) : (k : ℕ) → History P k → Prop
  | 0,_ => True
  | k+1,p => AllNodeBounds c ell H C k p.1 ∧ NodeBound L c ell (H k) (C k) k p

theorem allNodeBounds_measurableSet (c : Domain → ℝ) (hc : Measurable c)
    (ell : ℝ) (H C : ℕ → ℝ) (k : ℕ) :
    MeasurableSet {p | AllNodeBounds L c ell H C k p} := by
  induction k with
  | zero => exact MeasurableSet.univ
  | succ k ih => exact (ih.preimage measurable_fst).inter (nodeBound_measurableSet L c hc ell _ _ k)

/-- One family of positive dimensional constants gives the genuine local
score heat estimate at every ancestor, almost everywhere under the actual
recursive history measure. Constants are independent of profile and mean. -/
theorem allNodeBounds_ae :
    ∃ H C : ℕ → ℝ, (∀ k, 0 < H k) ∧ (∀ k, 0 < C k) ∧
    ∀ (c : Domain → ℝ), Measurable c → ∀ {ell : ℝ}, 0 < ell →
    (∀ r, ell ≤ c r ∧ c r ≤ R.reference r) →
    (∀ p i, (L.observations.observations p i).stop ≤ (L.observations.observations p i).target) →
    ∀ (μ : Measure P) [IsFiniteMeasure μ] (k : ℕ),
    ∀ᵐ p ∂CutoffWordHistories.historyMeasure R μ k, AllNodeBounds L c ell H C k p := by
  choose H C hH hC hV using (fun k : ℕ => nodeBound_ae L k)
  refine ⟨H,C,hH,hC,?_⟩
  intro c hc ell hell hb hages μ _ k
  induction k with
  | zero => exact ae_of_all _ (fun _ => trivial)
  | succ k ih =>
    have hprev : ∀ᵐ p ∂CutoffWordHistories.historyMeasure R μ (k+1),
        AllNodeBounds L c ell H C k p.1 :=
      (Measure.quasiMeasurePreserving_fst (μ := CutoffWordHistories.historyMeasure R μ k)
        (ν := nodeMeasure R)).ae ih
    filter_upwards [hprev,hV k c hc hell hb hages μ] with p hp hcur
    exact ⟨hp,hcur⟩

end SHE.PhysicalScoreChain
