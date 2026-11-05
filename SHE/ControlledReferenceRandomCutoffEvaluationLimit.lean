module

public import SHE.ControlledReferenceLevel
public import SHE.RecursiveHeatBounds
public import SHE.UncutSmoothWords
public import SHE.UncutHistoryMass
public import SHE.ControlledReferenceUncutBounds
public import SHE.ControlledReferenceRecursiveContinuity
public import SHE.GaussianParameterContinuity
public import SHE.ControlledReferenceUncutContinuity
public import SHE.ControlledReferenceRecursiveFields
public import SHE.JointUncutWordEvaluation
public import SHE.PastParameterDiagonal
public import SHE.ControlledReferenceRandomUncutEvaluation
public import SHE.JointUncutEvaluationLimit
public import SHE.DominatedCutoffLimit

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section

namespace SHE.ControlledReferenceRandomCutoffEvaluationLimit
open Set MeasureTheory StoppedFourier WordRecursion ControlledProfile ControlledReferenceLevel
open CutoffWordLevel CutoffWordHistories CutoffInsertionCore GaussianItoTest SmoothCylinders SmoothWords UniformSmooth
open Classical Filter Topology
open scoped NNReal
local instance controlledReferenceRandomCutoffEvaluationLimit_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance controlledReferenceRandomCutoffEvaluationLimit_circleSigma : MeasurableSpace CircleL2 := borel _
local instance controlledReferenceRandomCutoffEvaluationLimit_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable (P : CanonicalCovariance.ProfileParameters) (A : ℝ→ℝ) (hA : BoundedSmooth A)
variable (Λ θ : ℝ) (v b : ℝ≥0) (hvb : v≤b)
variable {n : ℕ} (Z : Fin n→Observation)
variable (htarget : ∀ i,(b:ℝ)≤(Z i).target) (hstop : ∀ i,(b:ℝ)≤(Z i).stop)
variable (F : WordRecursion.State n→ℝ) (hF : BoundedSmooth F)
local notation "Base" => ControlledReferenceLevel.level P A hA Λ θ v b hvb Z htarget hstop F hF

variable (hsmall : ProfileStability.memoryConstant P.lower P.holder P.exponent*
  ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)

local instance controlledReferenceRandomCutoffEvaluationLimit_secondCountable : SecondCountableTopology CircleL2 :=
  (_root_.fourierBasis (T:=2*Real.pi)).repr.toHomeomorph.secondCountableTopology
variable {Ω : Type} [MeasurableSpace Ω]
variable (U V : Ω×ℝ→CircleL2) (XU XV : Ω×(ℝ×HeatCircle)→ℝ)
variable (hU : Measurable U) (hV : Measurable V) (hXU : Measurable XU) (hXV : Measurable XV)

variable (u : Ω→Inputs) (hu : StronglyMeasurable u)
local notation "R₀" => ControlledReferenceLevel.referenceData P A hA Λ θ v b hvb (0,0)
local notation "uncutLeaf" => ControlledReferenceRandomUncutEvaluation.leaf P A hA Λ θ v b hvb Z htarget hstop F hF U V XU XV
local notation "uncutRef" => ControlledReferenceRandomUncutEvaluation.reference P A hA Λ θ v b hvb Z htarget hstop F hF U V XU XV
local notation "cutLeaf" => (fun δ k h ω => JointUncutEvaluationLimit.cutoffLeaf (Base (u ω)) Λ U V XU XV δ k h ω)
local notation "cutRef" => (fun δ k h ω => JointUncutEvaluationLimit.cutoffReference (Base (u ω)) Λ U V XU XV δ k h ω)

include hsmall hU hV hXU hXV hu in
theorem cutoff_measurable (hΛ : 0≤Λ) (δ : ℝ) (hδ : 0<δ) (k : ℕ) :
    Measurable (fun q : History Unit k×Ω => cutLeaf δ k q.1 q.2) ∧
    Measurable (fun q : History Unit k×Ω => cutRef δ k q.1 q.2) := by
  let Q := History Unit k×Ω
  let L := ControlledReferenceRecursiveBounds.level P A hA Λ θ v b hvb Z htarget hstop F hF δ hδ
  have huQ : StronglyMeasurable (fun q : Q => u q.2) := hu.comp_measurable measurable_snd
  have hL (p : Inputs) : Measurable (fun q : Q => JointWordAnalytic.leaf (L p 0 k) Λ U V XU XV q.1 q.2) :=
    JointWordAnalytic.leaf_measurable (L p 0 k) Λ hU hV hXU hXV
  have hR (p : Inputs) : Measurable (fun q : Q => JointWordAnalytic.reference (L p 0 k) Λ U V XU XV q.1 q.2) :=
    JointWordAnalytic.reference_measurable (L p 0 k) Λ hU hV hXU hXV
  have hl := PastParameterDiagonal.stronglyMeasurable_diagonal (inferInstance : MeasurableSpace Q) le_rfl
    (fun p q => JointWordAnalytic.leaf (L p 0 k) Λ U V XU XV q.1 q.2) hL huQ
    (fun q => ControlledReferenceRecursiveFields.continuous_leaf P A hA Λ θ v b hvb Z htarget hstop F hF δ hδ hsmall U V XU XV hΛ 0 k q.1 q.2)
  have hr := PastParameterDiagonal.stronglyMeasurable_diagonal (inferInstance : MeasurableSpace Q) le_rfl
    (fun p q => JointWordAnalytic.reference (L p 0 k) Λ U V XU XV q.1 q.2) hR huQ
    (fun q => ControlledReferenceRecursiveFields.continuous_reference P A hA Λ θ v b hvb Z htarget hstop F hF δ hδ hsmall U V XU XV hΛ 0 k q.1 q.2)
  exact ⟨by simpa only [JointUncutEvaluationLimit.cutoffLeaf,dif_pos hδ,L,ControlledReferenceRecursiveBounds.level] using hl.measurable,
    by simpa only [JointUncutEvaluationLimit.cutoffReference,dif_pos hδ,L,ControlledReferenceRecursiveBounds.level] using hr.measurable⟩

include hsmall hU hV hXU hXV hu in
/-- Full L¹ and integral cutoff removal for the actual random-reference
leaf, with one integrable uncut weight uniform over both past inputs.
The constants retain their dependence on the smooth coefficient and
fixed depth; no order-uniform or rough-coefficient limit is asserted. -/
theorem leaf_converges (hΛ : 0≤Λ) (ν : Measure Unit) [IsFiniteMeasure ν]
    (μ : Measure Ω) [IsFiniteMeasure μ] (k : ℕ) :
    Tendsto (fun δ : ℝ => ∫ q : History Unit k×Ω,
      |cutLeaf δ k q.1 q.2-uncutLeaf (u q.2) k q.1 q.2|
      ∂(historyMeasure R₀ ν k).prod μ) (𝓝[>] (0:ℝ)) (𝓝 0) ∧
    Tendsto (fun δ : ℝ => ∫ q : History Unit k×Ω,cutLeaf δ k q.1 q.2
      ∂(historyMeasure R₀ ν k).prod μ) (𝓝[>] (0:ℝ))
      (𝓝 (∫ q : History Unit k×Ω,uncutLeaf (u q.2) k q.1 q.2 ∂(historyMeasure R₀ ν k).prod μ)) := by
  let σ := (historyMeasure R₀ ν k).prod μ
  let W := fun q : History Unit k×Ω => UncutSmoothWords.weight (Base (0,0)) k q.1
  have hW : Integrable W σ := (UncutHistoryMass.weight_integrable (Base (0,0)) ν k).comp_fst μ
  obtain ⟨C,hCn,hC⟩ := ControlledReferenceRandomUncutEvaluation.evaluation_bound P A hA Λ θ v b hvb Z htarget hstop F hF U V XU XV k
  have hm := ControlledReferenceRandomUncutEvaluation.diagonal_measurable P A hA Λ θ v b hvb Z htarget hstop F hF hsmall U V XU XV hU hV hXU hXV hΛ u hu k
  have hFm (δ : ℝ) (hδ : 0<δ) := (cutoff_measurable P A hA Λ θ v b hvb Z htarget hstop F hF hsmall U V XU XV hU hV hXU hXV u hu hΛ δ hδ k).1
  have hb (δ : ℝ) (hδ : 0<δ) (q : History Unit k×Ω) : ‖cutLeaf δ k q.1 q.2‖≤C*W q := by
    change ‖JointUncutEvaluationLimit.cutoffLeaf (Base (u q.2)) Λ U V XU XV δ k q.1 q.2‖≤C*W q
    rw [JointUncutEvaluationLimit.cutoffLeaf,dif_pos hδ,JointUncutWordEvaluation.cutoff_leaf_eq (Base (u q.2)) Λ U V XU XV hδ k q.1 q.2]
    by_cases hg : CutoffUncutComparison.Active (Base (u q.2)) δ k q.1
    · simpa only [hg,ite_true,ControlledReferenceRandomUncutEvaluation.leaf,W] using (hC (u q.2) q.1 q.2).1
    · simp only [hg,ite_false,norm_zero]
      exact mul_nonneg hCn (UncutSmoothWords.weight_nonneg (Base (0,0)) k q.1)
  have he (q : History Unit k×Ω) := JointUncutEvaluationLimit.leaf_eventually_eq (Base (u q.2)) Λ U V XU XV k q.1 q.2
  exact ⟨DominatedCutoffLimit.integral_abs_sub_tendsto_zero σ hW hm.1 hFm (fun q => (hC (u q.2) q.1 q.2).1) hb he,
    DominatedCutoffLimit.integral_tendsto σ hW hFm hb he⟩

include hsmall hU hV hXU hXV hu in
theorem reference_converges (hΛ : 0≤Λ) (ν : Measure Unit) [IsFiniteMeasure ν]
    (μ : Measure Ω) [IsFiniteMeasure μ] (k : ℕ) :
    Tendsto (fun δ : ℝ => ∫ q : History Unit k×Ω,
      |cutRef δ k q.1 q.2-uncutRef (u q.2) k q.1 q.2|
      ∂(historyMeasure R₀ ν k).prod μ) (𝓝[>] (0:ℝ)) (𝓝 0) ∧
    Tendsto (fun δ : ℝ => ∫ q : History Unit k×Ω,cutRef δ k q.1 q.2
      ∂(historyMeasure R₀ ν k).prod μ) (𝓝[>] (0:ℝ))
      (𝓝 (∫ q : History Unit k×Ω,uncutRef (u q.2) k q.1 q.2 ∂(historyMeasure R₀ ν k).prod μ)) := by
  let σ := (historyMeasure R₀ ν k).prod μ
  let W := fun q : History Unit k×Ω => UncutSmoothWords.weight (Base (0,0)) k q.1
  have hW : Integrable W σ := (UncutHistoryMass.weight_integrable (Base (0,0)) ν k).comp_fst μ
  obtain ⟨C,hCn,hC⟩ := ControlledReferenceRandomUncutEvaluation.evaluation_bound P A hA Λ θ v b hvb Z htarget hstop F hF U V XU XV k
  have hm := ControlledReferenceRandomUncutEvaluation.diagonal_measurable P A hA Λ θ v b hvb Z htarget hstop F hF hsmall U V XU XV hU hV hXU hXV hΛ u hu k
  have hFm (δ : ℝ) (hδ : 0<δ) := (cutoff_measurable P A hA Λ θ v b hvb Z htarget hstop F hF hsmall U V XU XV hU hV hXU hXV u hu hΛ δ hδ k).2
  have hb (δ : ℝ) (hδ : 0<δ) (q : History Unit k×Ω) : ‖cutRef δ k q.1 q.2‖≤C*W q := by
    change ‖JointUncutEvaluationLimit.cutoffReference (Base (u q.2)) Λ U V XU XV δ k q.1 q.2‖≤C*W q
    rw [JointUncutEvaluationLimit.cutoffReference,dif_pos hδ,JointUncutWordEvaluation.cutoff_reference_eq (Base (u q.2)) Λ U V XU XV hδ k q.1 q.2]
    by_cases hg : CutoffUncutComparison.Active (Base (u q.2)) δ k q.1
    · simpa only [hg,ite_true,ControlledReferenceRandomUncutEvaluation.reference,W] using (hC (u q.2) q.1 q.2).2
    · simp only [hg,ite_false,norm_zero]
      exact mul_nonneg hCn (UncutSmoothWords.weight_nonneg (Base (0,0)) k q.1)
  have he (q : History Unit k×Ω) := JointUncutEvaluationLimit.reference_eventually_eq (Base (u q.2)) Λ U V XU XV k q.1 q.2
  exact ⟨DominatedCutoffLimit.integral_abs_sub_tendsto_zero σ hW hm.2 hFm (fun q => (hC (u q.2) q.1 q.2).2) hb he,
    DominatedCutoffLimit.integral_tendsto σ hW hFm hb he⟩

end SHE.ControlledReferenceRandomCutoffEvaluationLimit
