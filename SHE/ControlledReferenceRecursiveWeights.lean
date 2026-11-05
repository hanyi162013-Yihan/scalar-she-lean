module

public import SHE.ControlledReferenceLevel
public import SHE.RecursiveHeatBounds
public import SHE.ControlledReferenceRecursiveBounds
public import SHE.ControlledReferenceRecursiveContinuity
public import SHE.ControlledReferenceRecursiveBackward
public import SHE.ControlledReferenceRecursiveAverages
public import SHE.ControlledReferenceRecursiveFields
public import SHE.JointStateSpatialLimit
public import SHE.PastParameterDiagonal
public import SHE.GaussianParameterContinuity

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section

namespace SHE.ControlledReferenceRecursiveWeights
open Set MeasureTheory StoppedFourier WordRecursion ControlledProfile ControlledReferenceLevel
open CutoffWordLevel CutoffWordHistories CutoffInsertionCore GaussianItoTest SmoothCylinders SmoothWords UniformSmooth
open Classical
open scoped NNReal
local instance controlledReferenceRecursiveWeights_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance controlledReferenceRecursiveWeights_circleSigma : MeasurableSpace CircleL2 := borel _
local instance controlledReferenceRecursiveWeights_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable (P : CanonicalCovariance.ProfileParameters) (A : ℝ→ℝ) (hA : BoundedSmooth A)
variable (Λ θ : ℝ) (v b : ℝ≥0) (hvb : v≤b)
variable {n : ℕ} (Z : Fin n→Observation)
variable (htarget : ∀ i,(b:ℝ)≤(Z i).target) (hstop : ∀ i,(b:ℝ)≤(Z i).stop)
variable (F : WordRecursion.State n→ℝ) (hF : BoundedSmooth F)
variable (δ : ℝ) (hδ : 0<δ)

local notation "R" => referenceData P A hA Λ θ v b hvb
local notation "L" => ControlledReferenceRecursiveBounds.level P A hA Λ θ v b hvb Z htarget hstop F hF δ hδ
variable (hsmall : ProfileStability.memoryConstant P.lower P.holder P.exponent*
  ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)

local instance controlledReferenceRecursiveWeights_secondCountable : SecondCountableTopology CircleL2 :=
  (_root_.fourierBasis (T:=2*Real.pi)).repr.toHomeomorph.secondCountableTopology
variable {Ω : Type*} [MeasurableSpace Ω]
variable {𝓕 : MeasureTheory.Filtration ℝ≥0 ‹MeasurableSpace Ω›} {τ : Measure Ω} [IsProbabilityMeasure τ] {H : ℝ≥0}
variable (dU dV : PredictableWordState.Data 𝓕 τ H)

theorem nodeClock_eq (p p' : Inputs) (ε : ℝ≥0) (k : ℕ) (q : (History Unit k×Ω)×ℝ) :
    JointStateSpatialLimit.nodeClock (L p ε k) q=JointStateSpatialLimit.nodeClock (L p' ε k) q := by
  change ClippedCovariance.clip (v:ℝ) ((L p ε k).terminal q.1.1) q.2=
    ClippedCovariance.clip (v:ℝ) ((L p' ε k).terminal q.1.1) q.2
  rw [ControlledReferenceRecursiveBounds.terminal_eq P A hA Λ θ v b hvb Z htarget hstop F hF δ hδ p p' ε ε k q.1.1]

theorem oldState_eq (p p' : Inputs) (ε : ℝ≥0) (k : ℕ) (q : (History Unit k×Ω)×ℝ) :
    JointStateSpatialLimit.oldState (L p ε k) dU dV Λ q=JointStateSpatialLimit.oldState (L p' ε k) dU dV Λ q := by
  unfold JointStateSpatialLimit.oldState
  rw [nodeClock_eq P A hA Λ θ v b hvb Z htarget hstop F hF δ hδ p p' ε k q]
  exact ControlledReferenceRecursiveFields.state_eq P A hA Λ θ v b hvb Z htarget hstop F hF δ hδ
    dU.physicalState dV.physicalState dU.physicalField dV.physicalField p p' ε k q.1.1 q.1.2 _

include hsmall in
theorem weight_continuous (hΛ : 0≤Λ) (ε : ℝ≥0) (k : ℕ) (q : ((History Unit k×Ω)×ℝ)×HeatCircle) :
    Continuous (fun p : Inputs => JointStateSpatialLimit.weight (L p ε k) dU dV Λ δ q) := by
  let hp := JointStateSpatialLimit.historyPoint q
  let z := JointStateSpatialLimit.oldState (L (0,0) ε k) dU dV Λ q.1
  have hH := (ControlledReferenceRecursiveAverages.averaged_hessian_continuous P A hA Λ θ v b hvb Z htarget hstop F hF δ hδ hsmall hΛ ε k hp).comp
    (continuous_id.prodMk (continuous_const (y := z)))
  have hr : Continuous (fun p : Inputs => (L p ε k).cutoffRow δ hp) := by
    have he : (fun p : Inputs => (L p ε k).cutoffRow δ hp)=fun _ => (L (0,0) ε k).cutoffRow δ hp := by
      funext p
      exact ControlledReferenceRecursiveContinuity.cutoffRow_eq P A hA Λ θ v b hvb Z htarget hstop F hF δ hδ p (0,0) ε k hp
    rw [he]
    exact continuous_const
  have hh := ((hH.clm_apply hr).clm_apply hr).const_mul (1/2:ℝ)
  convert hh using 1
  funext p
  unfold JointStateSpatialLimit.weight WordRecursion.directionalSecond
  rw [oldState_eq P A hA Λ θ v b hvb Z htarget hstop F hF δ hδ dU dV p (0,0) ε k q.1]
  rfl

/-- The true moving spatial Hessian weight admits a bound uniform over
both random-reference inputs, all heat ages and finite histories. -/
theorem weight_bounded (k : ℕ) : ∃ C : ℝ,0≤C ∧ ∀ (p : Inputs) (ε : ℝ≥0) q,
    |JointStateSpatialLimit.weight (L p ε k) dU dV Λ δ q|≤C := by
  obtain ⟨B,hBn,hB⟩ := (ControlledReferenceRecursiveAverages.averagedTest_uniform P A hA Λ θ v b hvb Z htarget hstop F hF δ hδ k).fderiv.fderiv.norm_bound
  let Q := Real.sqrt ((n+k:ℕ):ℝ)*CovarianceMatrix.heatRowBound δ
  have hQ : 0≤Q := mul_nonneg (Real.sqrt_nonneg _) (CovarianceMatrix.heatRowBound_pos hδ).le
  refine ⟨(1/2:ℝ)*B*Q^2,by positivity,fun p ε q => ?_⟩
  let T := GaussianTaylor.hessian ((L p ε k).averagedTest (JointStateSpatialLimit.historyPoint q))
    (JointStateSpatialLimit.oldState (L p ε k) dU dV Λ q.1)
  let r := (L p ε k).cutoffRow δ (JointStateSpatialLimit.historyPoint q)
  have hr : ‖r‖≤Q := (L p ε k).cutoffRow_bound hδ _
  have hT : ‖T‖≤B := hB (p,(ε,JointStateSpatialLimit.historyPoint q)) _
  have hh : ‖T r r‖≤B*Q^2 := by
    have he := (GaussianTaylor.bilinear_norm_le T r r).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hT (norm_nonneg r)) (norm_nonneg r))
    have hs := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg r) hr 2) hBn
    exact he.trans (by nlinarith only [hs])
  change |(1/2:ℝ)*T r r|≤_
  rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<1/2)]
  exact (mul_le_mul_of_nonneg_left hh (by norm_num : (0:ℝ)≤1/2)).trans_eq (by ring)

include hsmall in
/-- An actual measurable random-reference diagonal for the moving
Hessian weight. Only the supplied measurable state parameter is used;
the profile and word continuity/measurability are proved above. -/
theorem weight_diagonal_measurable (hΛ : 0≤Λ) (u : Ω→Inputs) (hu : StronglyMeasurable u) (ε : ℝ≥0) (k : ℕ) :
    Measurable (fun q : ((History Unit k×Ω)×ℝ)×HeatCircle =>
      JointStateSpatialLimit.weight (L (u q.1.1.2) ε k) dU dV Λ δ q) := by
  let Q := ((History Unit k×Ω)×ℝ)×HeatCircle
  let K := fun (p : Inputs) (q : Q) => JointStateSpatialLimit.weight (L p ε k) dU dV Λ δ q
  have hK (p : Inputs) : Measurable (K p) := JointStateSpatialLimit.weight_measurable (L p ε k) dU dV Λ δ
  have huQ : StronglyMeasurable (fun q : Q => u q.1.1.2) := hu.comp_measurable measurable_fst.fst.snd
  have hh := PastParameterDiagonal.stronglyMeasurable_diagonal (inferInstance : MeasurableSpace Q) le_rfl K hK huQ
    (fun q => weight_continuous P A hA Λ θ v b hvb Z htarget hstop F hF δ hδ hsmall dU dV hΛ ε k q)
  exact hh.measurable

end SHE.ControlledReferenceRecursiveWeights
