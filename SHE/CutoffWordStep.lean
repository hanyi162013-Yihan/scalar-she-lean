module

public import SHE.CutoffWordAnalytic
public import SHE.CutoffWordHistories

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! An exact integrated recursive step for actual cutoff words. The
cutoff correction is retained explicitly; no assertion that a boundary
strip vanishes, or that an infinite word series converges, is assumed. -/
noncomputable section
namespace SHE.CutoffWordStep
open Set MeasureTheory ProbabilityTheory StoppedFourier
open WordRecursion GaussianItoTest CutoffWordLevel CutoffWordHistories CutoffWordAnalytic
open IntegratedPhysicalStep
open Classical
variable {P Ω : Type*} [MeasurableSpace P] [MeasurableSpace Ω]
variable [MeasurableSpace CircleL2] [BorelSpace CircleL2]
variable {R : ReferenceData} {n : ℕ} (L : Level R P n)
variable (δ : ℝ) (hδ : 0 < δ)
include hδ
variable (U : Ω × ℝ → CircleL2) (X : Ω × (ℝ × HeatCircle) → ℝ)

def childLeaf (p : P × (ℝ × HeatCircle)) (ω : Ω) : ℝ :=
  L.childTest δ p (observe (fun t => U (ω,t)) (fun q => X (ω,q))
    (L.childObservations.observations p) (L.nodeTime p))

theorem childLeaf_measurable (hU : Measurable U) (hX : Measurable X) :
    Measurable (fun p : (P × (ℝ × HeatCircle)) × Ω => childLeaf L δ U X p.1 p.2) :=
  physical_leaf_measurable (L.extend δ hδ) hU hX (fun _ _ _ => 0)

theorem childLeaf_uniform_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ p ω, ‖childLeaf L δ U X p ω‖ ≤ C := by
  obtain ⟨C,hCn,hC⟩ := (L.childTest_uniform hδ).norm_bound
  exact ⟨C,hCn,fun p ω => hC p _⟩

def cutoffCorrection (p : P) (ω : Ω) : ℝ :=
  PhysicalIto.wordRemainder (L.window p) R.totalVariance (fun t => U (ω,t))
    (fun q => X (ω,q)) (L.test p) - ∫ z, childLeaf L δ U X (p,z) ω ∂nodeMeasure R

theorem cutoffCorrection_measurable (hU : Measurable U) (hX : Measurable X) :
    Measurable (fun p : P × Ω => cutoffCorrection L δ U X p.1 p.2) := by
  have hchild : Measurable (fun p : (P × Ω) × (ℝ × HeatCircle) => childLeaf L δ U X (p.1.1,p.2) p.1.2) :=
    (childLeaf_measurable L δ hδ U X hU hX).comp
      ((measurable_fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd)
  have hi := hchild.stronglyMeasurable.integral_prod_right' (ν := nodeMeasure R)
  exact (physical_remainder_measurable L hU hX (fun _ _ _ => 0)).sub hi.measurable

/-- The child is the actual physical insertion of the true Gaussian
backward test at every separated node; outside this domain it is zero. -/
theorem childLeaf_eq (p : P × (ℝ × HeatCircle)) (ω : Ω) :
    childLeaf L δ U X p ω = if L.Good δ p then
      PhysicalIto.insertedWord (L.window p.1) R.totalVariance (fun t => U (ω,t))
        (fun q => X (ω,q)) (L.test p.1) p.2.1 p.2.2 else 0 := by
  classical
  unfold childLeaf
  rw [L.childTest_eq hδ p]
  by_cases hp : L.Good δ p
  · simp only [hp, ite_true]
    have ht := L.nodeTime_eq hδ hp
    change insertion R.totalVariance R.reference (L.observations.observations p.1) p.2.1 p.2.2
      (gaussianSemigroup R.reference (L.observations.observations p.1) p.2.1 (L.terminal p.1) (L.test p.1))
      (observe _ _ (appendObservation _ (L.nodeTime p) p.2.2) (L.nodeTime p)) = _
    rw [ht]
    rw [PhysicalIto.insertedWord, PhysicalIto.backward_eq_semigroup (L.window p.1) (L.test p.1)
      (Ioo_subset_Icc_self (L.good_time hδ hp))]
    rfl
  · simp only [hp, ite_false, Pi.zero_apply]

theorem integrated_recursive_step (hU : Measurable U) (hX : Measurable X)
    (N : P → (ℝ → WordRecursion.State n → ℝ) → Ω → ℝ)
    (μ : Measure P) [IsFiniteMeasure μ] (τ : Measure Ω) [IsProbabilityMeasure τ]
    (hIto : ItoConditions (physicalLevel L U X N) τ) :
    Integrable ((physicalLevel L U X N).integratedNoise μ) τ ∧
      (∫ ω, (physicalLevel L U X N).integratedNoise μ ω ∂τ) = 0 ∧
      ∀ ω, (∫ p, (physicalLevel L U X N).leaf p ω ∂μ) =
        (∫ p, (physicalLevel L U X N).reference p ω ∂μ) +
          (physicalLevel L U X N).integratedNoise μ ω +
          (∫ p, childLeaf L δ U X p ω ∂μ.prod (nodeMeasure R)) +
          ∫ p, cutoffCorrection L δ U X p ω ∂μ := by
  have hA := physical_analyticConditions L hU hX N
  obtain ⟨hNi,hNz,hNe,hstep⟩ := integrated_level (physicalLevel L U X N) hA μ τ hIto
  obtain ⟨K,hKn,hK⟩ := uniform_level_bound (physicalLevel L U X N) hA
  obtain ⟨C,hCn,hC⟩ := childLeaf_uniform_bound L δ hδ U X
  refine ⟨hNi,hNz,fun ω => ?_⟩
  have hcm := (childLeaf_measurable L δ hδ U X hU hX).comp
    (measurable_id.prodMk (measurable_const (a := ω)))
  have hci : Integrable (fun p : P × (ℝ × HeatCircle) => childLeaf L δ U X p ω)
      (μ.prod (nodeMeasure R)) :=
    (integrable_const C).mono' hcm.aestronglyMeasurable (Filter.Eventually.of_forall (fun p => hC p ω))
  have hri : Integrable (fun p => (physicalLevel L U X N).remainder p ω) μ :=
    (integrable_const K).mono'
      (hA.remainder_measurable.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun p => (hK p ω).2.2.1))
  have he := integral_sub hri hci.integral_prod_left
  change (∫ p, cutoffCorrection L δ U X p ω ∂μ) = _ at he
  rw [← integral_prod _ hci] at he
  linarith only [hstep ω,he]

end SHE.CutoffWordStep
