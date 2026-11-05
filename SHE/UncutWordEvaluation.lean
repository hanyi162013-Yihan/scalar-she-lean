module

public import SHE.CutoffUncutComparison
public import SHE.RecursiveReferenceLimit
public import SHE.CutoffWordAnalytic

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.UncutWordEvaluation
open Set MeasureTheory Filter StoppedFourier WordRecursion
open CutoffWordLevel CutoffWordHistories CutoffCarriers CutoffUncutComparison
open CutoffWordAnalytic GaussianConvolution CutoffReferenceTree
open Classical
local instance : MeasurableSpace CircleL2 := borel _
local instance : BorelSpace CircleL2 := ⟨rfl⟩
variable {P Ω : Type} [MeasurableSpace P] [MeasurableSpace Ω] {R : ReferenceData} {n : ℕ}
variable (L : CutoffWordLevel.Level R P n)

def leaf (U : Ω×ℝ→CircleL2) (X : Ω×(ℝ×HeatCircle)→ℝ)
    (k : ℕ) (p : History P k) (ω : Ω) : ℝ :=
  UncutSmoothWords.test L k p (observe (fun t => U (ω,t)) (fun q => X (ω,q))
    ((carrier L k).observations.observations p) ((carrier L k).terminal p))

def reference (u : CircleL2) (k : ℕ) (p : History P k) : ℝ :=
  GaussianSmooth.average (ProbabilityTheory.multivariateGaussian 0
    ((carrier L k).nodeCovariance (p,(R.base,0))).val) (UncutSmoothWords.test L k p)
    (CanonicalConditional.initialMean ((carrier L k).observations.observations p) R.base u)

theorem test_continuous (k : ℕ) (p : History P k) : Continuous (UncutSmoothWords.test L k p) := by
  rw [UncutSmoothWords.test_eq_weight_normalized]
  exact continuous_const.smul ((UncutSmoothWords.normalized_uniform L k).smooth p).continuous

def normalizedLevel (k : ℕ) : CutoffWordLevel.Level R (History P k) (n+k) :=
  {carrier L k with
    test := UncutSmoothWords.normalized L k
    test_uniform := UncutSmoothWords.normalized_uniform L k
    test_measurable := UncutSmoothWords.normalized_measurable L k}

theorem reference_eq_weight (u : CircleL2) (k : ℕ) (p : History P k) :
    reference L u k p=UncutSmoothWords.weight L k p*deterministicReference (normalizedLevel L k) u p := by
  have hh := RecursiveReferenceLimit.reference_eq_average (normalizedLevel L k) 1 zero_lt_one 0 0 p u
  change deterministicReference (normalizedLevel L k) u p=
    GaussianSmooth.average (ProbabilityTheory.multivariateGaussian 0
      ((carrier L k).nodeCovariance (p,(R.base,0))).val) (UncutSmoothWords.normalized L k p)
      (CanonicalConditional.initialMean ((carrier L k).observations.observations p) R.base u) at hh
  rw [reference,UncutSmoothWords.test_eq_weight_normalized,NormalizedInsertion.average_smul,hh]
  rfl

theorem leaf_measurable {U : Ω×ℝ→CircleL2} (hU : Measurable U)
    {X : Ω×(ℝ×HeatCircle)→ℝ} (hX : Measurable X) (k : ℕ) :
    Measurable (fun q : History P k×Ω => leaf L U X k q.1 q.2) := by
  have hY := (physical_observe_measurable (carrier L k) hU hX).comp
    (measurable_id.prodMk ((carrier L k).terminal_measurable.comp measurable_fst))
  exact (UncutSmoothWords.test_measurable L k).comp (measurable_fst.prodMk hY)

theorem reference_measurable (u : CircleL2) (k : ℕ) : Measurable (reference L u k) := by
  have hh := (UncutSmoothWords.weight_measurable L k).mul
    (deterministicReference_measurable (normalizedLevel L k) u)
  convert hh using 1
  funext p
  exact reference_eq_weight L u k p

theorem cutoff_leaf_eq {δ : ℝ} (hδ : 0<δ) (U : Ω×ℝ→CircleL2) (X : Ω×(ℝ×HeatCircle)→ℝ)
    (k : ℕ) (p : History P k) (ω : Ω) :
    (RecursiveHeatBounds.level L δ hδ 0 k).test p
      (observe (fun t => U (ω,t)) (fun q => X (ω,q))
        ((RecursiveHeatBounds.level L δ hδ 0 k).observations.observations p)
        ((RecursiveHeatBounds.level L δ hδ 0 k).terminal p))=
      if Active L δ k p then leaf L U X k p ω else 0 := by
  rw [test_eq_active L hδ k p,observations_eq L hδ zero_lt_one k p,
    terminal_eq L hδ zero_lt_one k p]
  by_cases hp : Active L δ k p <;> simp only [hp,ite_true,ite_false,Pi.zero_apply] <;> rfl

theorem cutoff_reference_eq {δ : ℝ} (hδ : 0<δ) (u : CircleL2) (k : ℕ) (p : History P k) :
    deterministicReference (RecursiveHeatBounds.level L δ hδ 0 k) u p=
      if Active L δ k p then reference L u k p else 0 := by
  rw [RecursiveReferenceLimit.reference_eq_average L δ hδ 0 k p u,
    nodeCovariance_eq L hδ zero_lt_one k (p,(R.base,0)),observations_eq L hδ zero_lt_one k p,
    test_eq_active L hδ k p]
  by_cases hp : Active L δ k p
  · simp only [hp,ite_true]; rfl
  · simp only [hp,ite_false]
    exact integral_zero _ _

theorem evaluation_norm_bounds (k : ℕ) : ∃ M : ℝ, 0≤M ∧
    (∀ (U : Ω×ℝ→CircleL2) (X : Ω×(ℝ×HeatCircle)→ℝ) p ω,
      ‖leaf L U X k p ω‖≤M*UncutSmoothWords.weight L k p) ∧
    (∀ u p, ‖reference L u k p‖≤M*UncutSmoothWords.weight L k p) := by
  obtain ⟨M,hMn,hM⟩ := UncutSmoothWords.test_norm_bound L k
  refine ⟨M,hMn,fun _ _ p _ => hM p _,fun u p => ?_⟩
  exact GaussianSmooth.average_norm_bound _ (hM p) _

end SHE.UncutWordEvaluation
