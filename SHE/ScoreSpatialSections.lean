module

public import SHE.ScoreSpatialIntegral

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2400000
noncomputable section

namespace SHE.PhysicalScoreChain
open Set Filter MeasureTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
  CutoffCarriers PhysicalParentGeometry OrderedHeatForests HistoryProductMeasure
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
variable {P : Type} [MeasurableSpace P] {R : ReferenceData} {n : ℕ}
variable (L : CutoffWordLevel.Level R P n)

/-- The actual full old-score product has its spatial envelope on one
joint history event, disintegrated over all original times and spaces.
The output is valid for every strict small history in that time section. -/
theorem actual_score_spatial_ae :
    ∃ H C : ℕ → ℝ, (∀ k, 0 < H k) ∧ (∀ k, 0 < C k) ∧
    ∀ (c : StoppedGaussianFeatures.Domain → ℝ), Measurable c → ∀ {ell : ℝ}, 0 < ell →
    (∀ r, ell ≤ c r ∧ c r ≤ R.reference r) →
    ∀ (hages : ∀ p i, (L.observations.observations p i).stop ≤ (L.observations.observations p i).target),
    ∀ (μ : Measure P) [IsFiniteMeasure μ] (k : ℕ),
    ∀ᵐ p ∂μ, ∀ᵐ t : Fin k → ℝ ∂Measure.pi (fun _ => volume.restrict (Ioc R.base R.horizon)),
      let p₀ := separated k (p,t,fun _ => (0:HeatCircle))
      ∀ (hp : StrictHistory L k p₀), SmallHistory L H k p₀ →
        (∀ᵐ x : Fin k → HeatCircle ∂Measure.pi (fun _ => AddCircle.haarAddCircle),
          0 ≤ spatialScore L c k p₀ x) ∧
        (∀ᵐ x : Fin k → HeatCircle ∂Measure.pi (fun _ => AddCircle.haarAddCircle),
          spatialScore L c k p₀ x ≤ timeWeight L ell C k p₀*parentEnvelope L hages k p₀ hp x) := by
  obtain ⟨H,C,hH,hC,hall⟩ := actual_score_forest_ae L
  refine ⟨H,C,hH,hC,?_⟩
  intro c hc ell hell hb hages μ _ k
  have hs := ae_replaceSpace_sections R μ k (hall c hc hell hb hages μ k)
  have hn := ae_replaceSpace_sections R μ k (actual_scoreProduct_nonneg_ae L c hc hell hb hages μ k)
  filter_upwards [hs,hn] with p hp hn
  filter_upwards [hp,hn] with t ht htn
  intro p₀ hp hsmall
  refine ⟨htn,?_⟩
  filter_upwards [ht] with x hx
  have hp' : StrictHistory L k (replaceSpace k p₀ x) :=
    (replaceSpace_strict_iff L k p₀ x).mpr hp
  have hsmall' : SmallHistory L H k (replaceSpace k p₀ x) :=
    (smallHistory_replaceSpace_iff L H k p₀ x).mpr hsmall
  have hh := hx hp' hsmall'
  simpa only [spatialScore,timeWeight_replaceSpace,replaceSpace_targets,parentEnvelope] using hh

/-- Consequently the old spatial score mass is integrable for almost
every original root/time section, with no unproved envelope premise. -/
theorem actual_score_spatial_mass_ae :
    ∃ H C : ℕ → ℝ, (∀ k, 0 < H k) ∧ (∀ k, 0 < C k) ∧
    ∀ (c : StoppedGaussianFeatures.Domain → ℝ), Measurable c → ∀ {ell : ℝ}, 0 < ell →
    (∀ r, ell ≤ c r ∧ c r ≤ R.reference r) →
    ∀ (hages : ∀ p i, (L.observations.observations p i).stop ≤ (L.observations.observations p i).target),
    ∀ (μ : Measure P) [IsFiniteMeasure μ] (k : ℕ),
    ∀ᵐ p ∂μ, ∀ᵐ t : Fin k → ℝ ∂Measure.pi (fun _ => volume.restrict (Ioc R.base R.horizon)),
      let p₀ := separated k (p,t,fun _ => (0:HeatCircle))
      ∀ (hp : StrictHistory L k p₀), SmallHistory L H k p₀ →
        Integrable (spatialScore L c k p₀) (Measure.pi (fun _ => AddCircle.haarAddCircle)) ∧
          (∫ x : Fin k → HeatCircle, spatialScore L c k p₀ x
            ∂Measure.pi (fun _ => AddCircle.haarAddCircle)) ≤
              timeWeight L ell C k p₀*(Fintype.card (Choices n k) : ℝ) := by
  obtain ⟨H,C,hH,hC,hall⟩ := actual_score_spatial_ae L
  refine ⟨H,C,hH,hC,?_⟩
  intro c hc ell hell hb hages μ _ k
  filter_upwards [hall c hc hell hb hages μ k] with p hp
  filter_upwards [hp] with t ht
  intro p₀ hp hsmall
  exact spatialScore_mass L c hc hages k p₀ hp _ (ht hp hsmall).1 (ht hp hsmall).2

end SHE.PhysicalScoreChain
