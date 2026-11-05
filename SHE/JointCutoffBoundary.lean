module

public import SHE.JointCutoffStep
public import SHE.PhysicalBoundaryLimit

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! The correction in the concrete recursive word identity is exactly
the omitted terminal time strip. This identification uses actual finite
product Fubini and actual heat domination, not a formal series identity. -/
noncomputable section
namespace SHE.JointCutoffBoundary
open Set MeasureTheory ProbabilityTheory Filter StoppedFourier
open WordRecursion CovarianceEndpoint GaussianItoTest PhysicalIto PhysicalRemainderBound PhysicalRemainderMass
open CutoffWordLevel CutoffWordHistories JointWordAnalytic JointCutoffStep
open Classical
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
variable {P Ω : Type*} [MeasurableSpace P] [MeasurableSpace Ω]
variable [MeasurableSpace CircleL2] [BorelSpace CircleL2]
variable {R : ReferenceData} {n : ℕ} (L : Level R P n) (Λ : ℝ)
variable {U V : Ω×ℝ→CircleL2} (hU : Measurable U) (hV : Measurable V)
variable {XU XV : Ω×(ℝ×HeatCircle)→ℝ} (hXU : Measurable XU) (hXV : Measurable XV)
include hU hV hXU hXV

def strip (δ : ℝ) (p : P) (ω : Ω) : ℝ :=
  ∫ t in max R.base (L.terminal p-δ)..L.terminal p,
    ∫ x,JointWordAnalytic.insertion L Λ U V XU XV p ω t x ∂AddCircle.haarAddCircle

theorem child_integral_eq (δ : ℝ) (hδ : 0 < δ) (p : P) (ω : Ω) :
    (∫ z, childLeaf L Λ δ U V XU XV (p,z) ω ∂nodeMeasure R) =
      ∫ t in R.base..max R.base (L.terminal p-δ),
        ∫ x, JointWordAnalytic.insertion L Λ U V XU XV p ω t x ∂AddCircle.haarAddCircle := by
  let q : ℝ := max R.base (L.terminal p-δ)
  have hq : q ≤ R.horizon := max_le (R.ordered) (by linarith [L.terminal_horizon p])
  have hsub : Ioc R.base q ⊆ Ioc R.base R.horizon := fun t ht => ⟨ht.1,ht.2.trans hq⟩
  have hm := (childLeaf_measurable L Λ δ hU hV hXU hXV hδ).comp
    (((measurable_const (a := p)).prodMk measurable_id).prodMk (measurable_const (a := ω)))
  obtain ⟨C,hCn,hC⟩ := childLeaf_uniform_bound (U := U) (V := V) (XU := XU) (XV := XV) L Λ δ hδ
  have hi : Integrable (fun z => childLeaf L Λ δ U V XU XV (p,z) ω) (nodeMeasure R) :=
    (integrable_const C).mono' hm.aestronglyMeasurable (Eventually.of_forall (fun z => hC (p,z) ω))
  rw [show nodeMeasure R = (volume.restrict (Ioc R.base R.horizon)).prod AddCircle.haarAddCircle from rfl,
    integral_prod _ hi]
  have heq : (fun t => ∫ x, childLeaf L Λ δ U V XU XV (p,(t,x)) ω ∂AddCircle.haarAddCircle) =
      (Ioc R.base q).indicator (fun t => ∫ x, JointWordAnalytic.insertion L Λ U V XU XV p ω t x ∂AddCircle.haarAddCircle) := by
    funext t
    have hg : (R.base < t ∧ t ≤ L.terminal p-δ) ↔ t ∈ Ioc R.base q := by
      dsimp [q]
      constructor
      · intro ht; exact ⟨ht.1,ht.2.trans (le_max_right _ _)⟩
      · intro ht
        refine ⟨ht.1,?_⟩
        rcases le_max_iff.mp ht.2 with h | h
        · linarith [ht.1]
        · exact h
    by_cases ht : t ∈ Ioc R.base q
    · have hgood := hg.mpr ht
      simp only [Set.indicator_of_mem ht]
      apply integral_congr_ae
      filter_upwards with x
      rw [childLeaf_eq (U := U) (V := V) (XU := XU) (XV := XV) L Λ δ hδ]
      simp only [Level.Good,hgood.1,hgood.2,true_and,ite_true]
    · simp only [Set.indicator_of_notMem ht]
      have hgood := mt hg.mp ht
      have hz : (fun x : HeatCircle => childLeaf L Λ δ U V XU XV (p,(t,x)) ω) = 0 := by
        funext x
        rw [childLeaf_eq (U := U) (V := V) (XU := XU) (XV := XV) L Λ δ hδ]
        simp only [Level.Good,hgood,ite_false,Pi.zero_apply]
      rw [hz]
      simp
  rw [heq,integral_indicator measurableSet_Ioc,Measure.restrict_restrict_of_subset hsub]
  exact (intervalIntegral.integral_of_le (le_max_left R.base (L.terminal p-δ))).symm

theorem correction_eq_strip (δ : ℝ) (hδ : 0 < δ) (p : P) (ω : Ω) :
    correction L Λ δ U V XU XV p ω = strip (U := U) (V := V) (XU := XU) (XV := XV) L Λ δ p ω := by
  let q := max R.base (L.terminal p-δ)
  have hq : q ∈ Icc R.base (L.terminal p) := ⟨le_max_left _ _,max_le (L.terminal_base p) (by linarith)⟩
  have hi := JointInsertionIntegrability.time_integrable L Λ hU hV hXU hXV p ω
  have hi₁ := hi.mono_set (c := R.base) (d := q)
    (by rw [uIcc_of_le hq.1,uIcc_of_le (L.terminal_base p)]; exact Icc_subset_Icc le_rfl hq.2)
  have hi₂ := hi.mono_set (c := q) (d := L.terminal p)
    (by rw [uIcc_of_le hq.2,uIcc_of_le (L.terminal_base p)]; exact Icc_subset_Icc hq.1 le_rfl)
  have he := intervalIntegral.integral_add_adjacent_intervals hi₁ hi₂
  unfold correction
  rw [child_integral_eq L Λ hU hV hXU hXV δ hδ p ω]
  change (∫ t in R.base..L.terminal p, _) - (∫ t in R.base..q, _) = ∫ t in q..L.terminal p, _
  linarith only [he]

end SHE.JointCutoffBoundary
