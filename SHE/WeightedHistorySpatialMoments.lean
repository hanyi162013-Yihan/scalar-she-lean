module

public import SHE.WeightedKernelSpatialMoments
public import SHE.RowSpatialHistoryMoments
public import SHE.HistoryInputSections
public import SHE.GlobalPointDensity
public import SHE.StrictHistoryFields
public import SHE.ScoreSpatialSections

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2400000
noncomputable section

namespace SHE.ScalarMeanEnvelope
open Set Filter MeasureTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
  CutoffCarriers PhysicalParentGeometry PhysicalScoreChain HistoryProductMeasure ActualMeanKernel
local instance weightedHistorySpatialMoments_nativePositive : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
variable {P Ω : Type} [MeasurableSpace P] [MeasurableSpace Ω] {R : ReferenceData}
variable (L : CutoffWordLevel.Level R P 1)

/-- The direction-row time may depend on the same old history as the
Gaussian law and current mean. This is joint measurability before Fubini. -/
theorem weightedPoint_historyRow_measurable (k : ℕ) (Λ q : ℝ)
    (r : History P k → ℝ) (hr : Measurable r)
    (m : Ω → History P k → WordRecursion.State (1+k))
    (hm : Measurable (fun z : Ω × History P k => m z.1 z.2)) :
    Measurable (fun z : Ω × (History P k × HeatCircle) =>
      weightedPoint L k Λ q (r z.2.1) (m z.1) z.2.1 z.2.2) := by
  let M : (Ω × History P k) → History P k → WordRecursion.State (1+k) :=
    fun z _ => m z.1 z.2
  have hM : Measurable (fun z : (Ω × History P k) × History P k => M z.1 z.2) :=
    hm.comp measurable_fst
  have hh := weightedPoint_variable_measurable L k Λ (fun _ : Ω × History P k => q)
    (fun z => r z.2) measurable_const (hr.comp measurable_snd) M hM
  have hd : Measurable (fun z : Ω × (History P k × HeatCircle) =>
      (((z.1,z.2.1),z.2.1),z.2.2)) :=
    ((measurable_fst.prodMk measurable_snd.fst).prodMk measurable_snd.fst).prodMk measurable_snd.snd
  convert! hh.comp hd using 1

/-- Actual history/input Fubini and weighted spatial Jensen, with the
old-score forest derived on the same genuine history event. The sole sharp
point input is written explicitly; it is supplied by Gaussian word moments.
No fixed-center exceptional set is evaluated at an adaptive center. -/
theorem weighted_spatial_history_moment :
    ∃ H A : ℕ → ℝ,(∀ j,0 < H j) ∧ (∀ j,0 < A j) ∧
    ∀ (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : ℝ) (hT : ∀ p,L.terminal p=T) {Λ : ℝ} (hΛ : 0≤Λ)
    (c : StoppedGaussianFeatures.Domain → ℝ) (hc : Measurable c)
    {ell : ℝ} (hell : 0 < ell) (hcb : ∀ z,ell ≤ c z ∧ c z ≤ R.reference z)
    (hages : ∀ p i,(L.observations.observations p i).stop ≤ (L.observations.observations p i).target)
    (ρ : Measure P) [IsFiniteMeasure ρ] (k : ℕ)
    (m : Ω → History P k → WordRecursion.State (1+k))
    (hm : Measurable (fun z : Ω × History P k => m z.1 z.2))
    (q : ℝ) (r : History P k → ℝ) (hr : Measurable r)
    (hri : ∀ p x,r (replaceSpace k p x)=r p)
    (D : History P k → ℝ) (hD : Measurable D) (hD0 : ∀ p,0 ≤ D p)
    (hDi : ∀ p x,D (replaceSpace k p x)=D p)
    (C : ℝ) (hC : 0 ≤ C) (b : ℕ) (hb : 0 < b)
    (hpoint : ∀ᵐ p ∂historyMeasure R ρ k,∀ᵐ y : HeatCircle ∂AddCircle.haarAddCircle,
      StrictHistory L k p ∧ r p < (carrier L k).terminal p →
      (∫ ω,|weightedPoint L k Λ q (r p) (m ω) p y|^(2*b) ∂μ) ≤
        C*(D p*globalDensity L c k p (r p) y)^(2*b)),
      ∀ᵐ p ∂ρ,∀ᵐ t : Fin k → ℝ ∂Measure.pi (fun _ => volume.restrict (Ioc R.base R.horizon)),
        let p₀ := separated k (p,t,fun _ => (0:HeatCircle))
        ∀ hp : StrictHistory L k p₀,r p₀ < (carrier L k).terminal p₀ → SmallHistory L H k p₀ →
          ∀ᵐ y : HeatCircle ∂AddCircle.haarAddCircle,
            Integrable (fun ω => ‖weightedSpatial L k Λ q (r p₀) m t ω y p‖^(2*b)) μ ∧
            (∫ ω,‖weightedSpatial L k Λ q (r p₀) m t ω y p‖^(2*b) ∂μ) ≤
              C*(D p₀*massBudget L k p₀ (timeWeight L ell A k p₀) (r p₀) y)^(2*b) := by
  obtain ⟨H,A,hH,hA,hscore⟩ := actual_score_spatial_ae L
  refine ⟨H,A,hH,hA,?_⟩
  intro μ _ T hT Λ hΛ c hc ell hell hcb hages ρ _ k m hm q r hr hri D hD hD0 hDi C hC b hb hpoint
  let F : History P k × HeatCircle → Prop := fun z =>
    StrictHistory L k z.1 ∧ r z.1 < (carrier L k).terminal z.1 →
      (∫ ω,|weightedPoint L k Λ q (r z.1) (m ω) z.1 z.2|^(2*b) ∂μ) ≤
        C*(D z.1*globalDensity L c k z.1 (r z.1) z.2)^(2*b)
  have hK : Measurable (fun z : Ω × (History P k × HeatCircle) =>
      weightedPoint L k Λ q (r z.2.1) (m z.1) z.2.1 z.2.2) :=
    weightedPoint_historyRow_measurable L k Λ q r hr m hm
  have hmoment := measurable_abs_moment μ _ hK (2*b)
  have hbound : Measurable (fun z : History P k × HeatCircle =>
      C*(D z.1*globalDensity L c k z.1 (r z.1) z.2)^(2*b)) :=
    (((hD.comp measurable_fst).mul (globalDensity_variable_measurable L c hc k r hr)).pow_const (2*b)).const_mul C
  have hactive : MeasurableSet {z : History P k × HeatCircle |
      StrictHistory L k z.1 ∧ r z.1 < (carrier L k).terminal z.1} :=
    ((strictHistory_measurableSet L k).preimage measurable_fst).inter
      (measurableSet_lt (hr.comp measurable_fst) ((carrier L k).terminal_measurable.comp measurable_fst))
  have hF : MeasurableSet {z | F z} := by
    convert hactive.compl.union (measurableSet_le hmoment hbound) using 1
    ext z
    simp only [F,mem_setOf_eq,mem_union,mem_compl_iff,imp_iff_not_or]
  have hsections := ae_input_sections R ρ k F hF hpoint
  filter_upwards [hsections,hscore c hc hell hcb hages ρ k] with p hp hs
  filter_upwards [hp,hs] with t ht hst
  intro p₀ hstrict hrow hsmall
  have hsc := hst hstrict hsmall
  filter_upwards [ht] with y hy
  apply weighted_spatial_moment_of_point_moment L μ hΛ T hT c hc hages k t p
    (timeWeight L ell A k p₀) (D p₀) C
    (timeWeight_nonneg L hell A (fun j => (hA j).le) k p₀ hstrict)
    (hD0 p₀) hC m hm q (r p₀) y b hb hstrict hrow hsc.1 hsc.2
  filter_upwards [hy] with x hx
  have hpx : separated k (p,t,x)=replaceSpace k p₀ x :=
    (replaceSpace_separated k p t (fun _ => (0:HeatCircle)) x).symm
  have hstrictx : StrictHistory L k (separated k (p,t,x)) := by
    rw [hpx]
    exact (replaceSpace_strict_iff L k p₀ x).mpr hstrict
  have hrx : r (separated k (p,t,x)) < (carrier L k).terminal (separated k (p,t,x)) := by
    simpa only [hpx,hri,replaceSpace_terminal] using hrow
  have hh := hx ⟨hstrictx,hrx⟩
  simpa only [F,hpx,hri,hDi,globalDensity_replaceSpace] using hh

end SHE.ScalarMeanEnvelope
