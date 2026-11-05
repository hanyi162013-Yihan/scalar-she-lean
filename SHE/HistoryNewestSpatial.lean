module

public import SHE.HistoryProductMeasure

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section

namespace SHE.HistoryNewestSpatial
open Set MeasureTheory StoppedFourier CutoffWordLevel CutoffWordHistories
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
variable {X : Type} [MeasurableSpace X]

/-- Genuine newest-coordinate Fubini for the original recursive history
measure. The measurable event is fixed before any time or spatial section
is selected, so a separately AE fixed-center assertion is never evaluated
on an adaptive diagonal. -/
theorem ae_succ_iff (R : ReferenceData) (ρ : Measure X) [IsFiniteMeasure ρ] (k : ℕ)
    (P : History X (k+1) → Prop) (hP : MeasurableSet {h | P h}) :
    (∀ᵐ h ∂historyMeasure R ρ (k+1), P h) ↔
      ∀ᵐ old ∂historyMeasure R ρ k,
        ∀ᵐ t ∂volume.restrict (Ioc R.base R.horizon),
          ∀ᵐ x : HeatCircle ∂AddCircle.haarAddCircle, P (old, (t, x)) := by
  constructor
  · intro h
    have hh := Measure.ae_ae_of_ae_prod h
    filter_upwards [hh] with old hold
    exact Measure.ae_ae_of_ae_prod hold
  · intro h
    apply (Measure.ae_prod_iff_ae_ae hP).mpr
    filter_upwards [h] with old hold
    have hp : MeasurableSet {z : ℝ × HeatCircle | P (old, z)} :=
      hP.preimage (measurable_const.prodMk measurable_id)
    exact (Measure.ae_prod_iff_ae_ae hp).mpr hold

/-- Any original common-history event and a genuine measurable newest
spatial section bound may be combined before choosing terminal inputs. -/
theorem ae_refine (R : ReferenceData) (ρ : Measure X) [IsFiniteMeasure ρ] (k : ℕ)
    (P Q : History X (k+1) → Prop) (hQ : MeasurableSet {h | Q h})
    (hP : ∀ᵐ h ∂historyMeasure R ρ (k+1), P h)
    (hnew : ∀ᵐ old ∂historyMeasure R ρ k,
      ∀ᵐ t ∂volume.restrict (Ioc R.base R.horizon),
        ∀ᵐ x : HeatCircle ∂AddCircle.haarAddCircle, Q (old, (t, x))) :
    ∀ᵐ h ∂historyMeasure R ρ (k+1), P h ∧ Q h := by
  exact hP.and ((ae_succ_iff R ρ k Q hQ).mpr hnew)

end SHE.HistoryNewestSpatial
