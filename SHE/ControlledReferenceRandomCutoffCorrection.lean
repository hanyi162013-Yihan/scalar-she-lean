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
public import SHE.ControlledReferenceCutoffBounds
public import SHE.JointBoundaryStripBound

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section

namespace SHE.ControlledReferenceRandomCutoffCorrection
open Set MeasureTheory StoppedFourier WordRecursion ControlledProfile ControlledReferenceLevel
open CutoffWordLevel CutoffWordHistories CutoffInsertionCore GaussianItoTest SmoothCylinders SmoothWords UniformSmooth
open Classical Filter Topology
open scoped NNReal
local instance controlledReferenceRandomCutoffCorrection_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance controlledReferenceRandomCutoffCorrection_circleSigma : MeasurableSpace CircleL2 := borel _
local instance controlledReferenceRandomCutoffCorrection_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable (P : CanonicalCovariance.ProfileParameters) (A : ℝ→ℝ) (hA : BoundedSmooth A)
variable (Λ θ : ℝ) (v b : ℝ≥0) (hvb : v≤b)
variable {n : ℕ} (Z : Fin n→Observation)
variable (htarget : ∀ i,(b:ℝ)≤(Z i).target) (hstop : ∀ i,(b:ℝ)≤(Z i).stop)
variable (F : WordRecursion.State n→ℝ) (hF : BoundedSmooth F)
local notation "Base" => ControlledReferenceLevel.level P A hA Λ θ v b hvb Z htarget hstop F hF

variable (hsmall : ProfileStability.memoryConstant P.lower P.holder P.exponent*
  ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)

local instance controlledReferenceRandomCutoffCorrection_secondCountable : SecondCountableTopology CircleL2 :=
  (_root_.fourierBasis (T:=2*Real.pi)).repr.toHomeomorph.secondCountableTopology
variable {Ω : Type} [MeasurableSpace Ω]
variable (U V : Ω×ℝ→CircleL2) (XU XV : Ω×(ℝ×HeatCircle)→ℝ)
variable (hU : Measurable U) (hV : Measurable V) (hXU : Measurable XU) (hXV : Measurable XV)

open PhysicalRemainderMass JointCutoffStep

include hU hV hXU hXV in
/-- The literal recursive terminal-strip correction has a true uncut
history majorant, uniformly in its time cutoff and BOTH past inputs.
The coefficient derivatives and fixed depth remain in the constant. -/
theorem weighted_bound (k : ℕ) : ∃ K : ℝ,0≤K ∧ ∀ (p : Inputs) (δ : ℝ) (hδ : 0<δ) h ω,
    ‖correction (RecursiveHeatBounds.level (Base p) δ hδ 0 k) Λ δ U V XU XV h ω‖≤
      K*UncutSmoothWords.weight (Base (0,0)) k h*heatMass δ := by
  obtain ⟨A₀,hAn,hAb⟩ := (UniformBoundedSmooth.fixed (P := Unit) hA).norm_bound
  obtain ⟨C,hCn,hC⟩ := ControlledReferenceCutoffBounds.test_norm_bound P A hA Λ θ v b hvb Z htarget hstop F hF k
  obtain ⟨D,hDn,hD⟩ := ControlledReferenceCutoffBounds.fderiv_bound P A hA Λ θ v b hvb Z htarget hstop F hF k
  obtain ⟨B,hBn,hB⟩ := ControlledReferenceCutoffBounds.hessian_bound P A hA Λ θ v b hvb Z htarget hstop F hF k
  let K := (1/2:ℝ)*(A₀+P.upper)*B*((n+k:ℕ):ℝ)
  have hKn : 0≤K := mul_nonneg
    (mul_nonneg (mul_nonneg (by norm_num) (add_nonneg hAn P.upper_nonneg)) hBn) (Nat.cast_nonneg _)
  refine ⟨K,hKn,fun p δ hδ h ω => ?_⟩
  rw [JointCutoffBoundary.correction_eq_strip _ Λ hU hV hXU hXV δ hδ]
  have hh := JointBoundaryStripBound.strip_bound (RecursiveHeatBounds.level (Base p) δ hδ 0 k) Λ U V XU XV
    hAn (fun z => by change |A z|≤A₀; simpa only [Real.norm_eq_abs] using hAb () z)
    (mul_nonneg hBn (UncutSmoothWords.weight_nonneg (Base (0,0)) k h)) hδ.le h ω
    (hC p δ hδ h) (hD p δ hδ h) (hB p δ hδ h)
  change ‖JointCutoffBoundary.strip (RecursiveHeatBounds.level (Base p) δ hδ 0 k) Λ δ h ω‖≤(1/2:ℝ)*(A₀+P.upper)*(B*UncutSmoothWords.weight (Base (0,0)) k h)*((n+k:ℕ):ℝ)*heatMass δ at hh
  convert hh using 1 <;> dsimp [K] <;> ring

variable (u : Ω→Inputs)
local notation "R₀" => ControlledReferenceLevel.referenceData P A hA Λ θ v b hvb (0,0)

def mass (ν : Measure Unit) (μ : Measure Ω) (k : ℕ) (δ : ℝ) : ℝ :=
  if hδ : 0<δ then ∫ q : History Unit k×Ω,
    correction (RecursiveHeatBounds.level (Base (u q.2)) δ hδ 0 k) Λ δ U V XU XV q.1 q.2
      ∂(historyMeasure R₀ ν k).prod μ else 0

include hU hV hXU hXV in
/-- Quantitative vanishing of actual moving random-reference cutoff
corrections in every finite history/sample measure. The bound uses the
integrated uncut weight and heatMass(δ), independent of the random past
states, rather than a derivative constant depending on δ. -/
theorem mass_tendsto_zero (ν : Measure Unit) [IsFiniteMeasure ν]
    (μ : Measure Ω) [IsFiniteMeasure μ] (k : ℕ) :
    Tendsto (mass P A hA Λ θ v b hvb Z htarget hstop F hF U V XU XV u ν μ k)
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
  obtain ⟨K,hKn,hK⟩ := weighted_bound P A hA Λ θ v b hvb Z htarget hstop F hF U V XU XV hU hV hXU hXV k
  let W := fun q : History Unit k×Ω => UncutSmoothWords.weight (Base (0,0)) k q.1
  let σ := (historyMeasure R₀ ν k).prod μ
  have hW : Integrable W σ := (UncutHistoryMass.weight_integrable (Base (0,0)) ν k).comp_fst μ
  have ht : Tendsto (fun δ : ℝ => (K*(∫ q,W q ∂σ))*heatMass δ) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have hh := ((continuous_const (y := K*(∫ q,W q ∂σ))).mul PhysicalBoundaryStrip.continuous_heatMass).tendsto (0:ℝ)
    have hr := hh.mono_left (nhdsWithin_le_nhds (s := Ioi (0:ℝ)))
    change Tendsto (fun δ : ℝ => (K*(∫ q,W q ∂σ))*heatMass δ) (𝓝[>] (0:ℝ)) (𝓝 ((K*(∫ q,W q ∂σ))*heatMass 0)) at hr
    simpa only [heatMass,Real.zero_rpow (by norm_num : (1/2:ℝ)≠0),mul_zero,add_zero] using hr
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) ?_ ht
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  change 0<δ at hδ
  rw [mass,dif_pos hδ]
  have hdom := hW.const_mul (K*heatMass δ)
  have hb := norm_integral_le_of_norm_le hdom (Eventually.of_forall (fun q : History Unit k×Ω => by
    have hh := hK (u q.2) δ hδ q.1 q.2
    convert hh using 1 <;> ring))
  apply hb.trans_eq
  rw [integral_const_mul]
  ring

end SHE.ControlledReferenceRandomCutoffCorrection
