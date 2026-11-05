module

public import SHE.UncutWordEvaluation
public import SHE.JointRecursiveReferenceLimit

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section

namespace SHE.JointUncutWordEvaluation
open Set MeasureTheory Filter StoppedFourier WordRecursion
open CutoffWordLevel CutoffWordHistories CutoffCarriers CutoffUncutComparison
open JointWordAnalytic GaussianConvolution UncutWordEvaluation
open Classical
local instance jointUncutWordEvaluation_sigma : MeasurableSpace CircleL2 := borel _
local instance jointUncutWordEvaluation_borel : BorelSpace CircleL2 := ⟨rfl⟩
variable {P Ω : Type} [MeasurableSpace P] [MeasurableSpace Ω] {R : ReferenceData} {n : ℕ}
variable (L : Level R P n) (Λ : ℝ)
variable (U V : Ω×ℝ→CircleL2) (XU XV : Ω×(ℝ×HeatCircle)→ℝ)

def leaf (k : ℕ) (p : History P k) (ω : Ω) : ℝ :=
  UncutSmoothWords.test L k p (state (carrier L k) Λ U V XU XV p ω ((carrier L k).terminal p))

def reference (k : ℕ) (p : History P k) (ω : Ω) : ℝ :=
  GaussianSmooth.average (ProbabilityTheory.multivariateGaussian 0
    ((carrier L k).nodeCovariance (p,(R.base,0))).val) (UncutSmoothWords.test L k p)
    (state (carrier L k) Λ U V XU XV p ω R.base)

theorem reference_eq_weight (k : ℕ) (p : History P k) (ω : Ω) :
    reference L Λ U V XU XV k p ω=UncutSmoothWords.weight L k p*
      JointWordAnalytic.reference (normalizedLevel L k) Λ U V XU XV p ω := by
  have hh := JointRecursiveReferenceLimit.reference_eq_average (normalizedLevel L k) 1 zero_lt_one Λ U V XU XV 0 0 p ω
  change JointWordAnalytic.reference (normalizedLevel L k) Λ U V XU XV p ω=
    GaussianSmooth.average (ProbabilityTheory.multivariateGaussian 0
      ((carrier L k).nodeCovariance (p,(R.base,0))).val) (UncutSmoothWords.normalized L k p)
      (state (carrier L k) Λ U V XU XV p ω R.base) at hh
  rw [reference,UncutSmoothWords.test_eq_weight_normalized,NormalizedInsertion.average_smul,hh]
  rfl

theorem leaf_measurable {U V XU XV} (hU : Measurable U) (hV : Measurable V)
    (hXU : Measurable XU) (hXV : Measurable XV) (k : ℕ) :
    Measurable (fun q : History P k×Ω => leaf L Λ U V XU XV k q.1 q.2) := by
  have hY := (JointWordAnalytic.state_measurable (carrier L k) Λ hU hV hXU hXV).comp
    (measurable_id.prodMk ((carrier L k).terminal_measurable.comp measurable_fst))
  exact (UncutSmoothWords.test_measurable L k).comp (measurable_fst.prodMk hY)

theorem reference_measurable {U V XU XV} (hU : Measurable U) (hV : Measurable V)
    (hXU : Measurable XU) (hXV : Measurable XV) (k : ℕ) :
    Measurable (fun q : History P k×Ω => reference L Λ U V XU XV k q.1 q.2) := by
  have hh := ((UncutSmoothWords.weight_measurable L k).comp measurable_fst).mul
    (JointWordAnalytic.reference_measurable (normalizedLevel L k) Λ hU hV hXU hXV)
  convert hh using 1
  funext q
  exact reference_eq_weight L Λ U V XU XV k q.1 q.2

theorem cutoff_leaf_eq {δ : ℝ} (hδ : 0<δ) (k : ℕ) (p : History P k) (ω : Ω) :
    JointWordAnalytic.leaf (RecursiveHeatBounds.level L δ hδ 0 k) Λ U V XU XV p ω=
      if Active L δ k p then leaf L Λ U V XU XV k p ω else 0 := by
  unfold JointWordAnalytic.leaf JointWordAnalytic.state
  rw [test_eq_active L hδ k p,observations_eq L hδ zero_lt_one k p,
    terminal_eq L hδ zero_lt_one k p]
  by_cases hp : Active L δ k p <;> simp only [hp,ite_true,ite_false,Pi.zero_apply] <;> rfl

theorem cutoff_reference_eq {δ : ℝ} (hδ : 0<δ) (k : ℕ) (p : History P k) (ω : Ω) :
    JointWordAnalytic.reference (RecursiveHeatBounds.level L δ hδ 0 k) Λ U V XU XV p ω=
      if Active L δ k p then reference L Λ U V XU XV k p ω else 0 := by
  rw [JointRecursiveReferenceLimit.reference_eq_average L δ hδ Λ U V XU XV 0 k p ω,
    nodeCovariance_eq L hδ zero_lt_one k (p,(R.base,0)),test_eq_active L hδ k p]
  unfold JointWordAnalytic.state
  rw [observations_eq L hδ zero_lt_one k p]
  by_cases hp : Active L δ k p
  · simp only [hp,ite_true]; rfl
  · simp only [hp,ite_false]
    exact integral_zero _ _

/-- Uniformity over all actual old joint values follows directly from
the uncut normalized test, with its integrable history weight retained. -/
theorem evaluation_norm_bounds (k : ℕ) : ∃ M : ℝ,0≤M ∧
    (∀ p ω,‖leaf L Λ U V XU XV k p ω‖≤M*UncutSmoothWords.weight L k p) ∧
    (∀ p ω,‖reference L Λ U V XU XV k p ω‖≤M*UncutSmoothWords.weight L k p) := by
  obtain ⟨M,hMn,hM⟩ := UncutSmoothWords.test_norm_bound L k
  exact ⟨M,hMn,fun p _ => hM p _,fun p _ => GaussianSmooth.average_norm_bound _ (hM p) _⟩

end SHE.JointUncutWordEvaluation
