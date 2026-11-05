module
public import SHE.ControlledActualTimeRemainder
public import SHE.ControlledReferenceFamilyEvaluation
public import SHE.OrdinaryUncutNoise
public import SHE.OrdinaryJointSelf

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
namespace SHE.ControlledOrdinaryNoise
open Set MeasureTheory StoppedFourier WordRecursion ControlledProfile ControlledReferenceLevel
  CutoffWordLevel CutoffWordHistories CutoffInsertionCore GaussianItoTest SmoothCylinders
  SmoothWords UniformSmooth IntegratedPhysicalStep Filter Topology
open scoped NNReal
local instance controlledOrdinaryNoise_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance controlledOrdinaryNoise_sigma : MeasurableSpace CircleL2 := borel _
local instance controlledOrdinaryNoise_borel : BorelSpace CircleL2 := ⟨rfl⟩
variable (P : CanonicalCovariance.ProfileParameters) (A : ℝ→ℝ) (hA : BoundedSmooth A)
variable (Λ θ : ℝ) (v b : ℝ≥0) (hvb : v≤b)
variable {Y : Type} [MeasurableSpace Y] {n : ℕ} (Z : VariableObservations.Family Y n)
variable (htarget : ∀ y i,(b:ℝ)≤(Z.observations y i).target)
variable (hstop : ∀ y i,(b:ℝ)≤(Z.observations y i).stop)
variable (F : Y→WordRecursion.State n→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun q : Y×WordRecursion.State n => F q.1 q.2))
local notation "Base" => ControlledReferenceFamilyLevel.level P A hA Λ θ v b hvb Z htarget hstop F hF hFm
local notation "NL" => (fun p k => UncutWordEvaluation.normalizedLevel (Base p) k)
variable {Ω : Type} [MeasurableSpace Ω]
variable {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {H : ℝ≥0} {κ : ℝ} {a : ℝ→ℝ} {ell M : ℝ}
variable (m : TwoChannelCutoffModel.Model 𝓕 μ H κ a ell M)

def value (p : Inputs) (k : ℕ) (h : History Y k) (ω : Ω) : ℝ :=
  OrdinaryUncutNoise.value m (Base p) k h ω

/-- The ordinary state is a genuine self-pair, rather than the θ=0
reference of a distinct joint process. All three original terms remain. -/
theorem value_eq (p : Inputs) (k : ℕ) (h : History Y k) (ω : Ω) :
    value P A hA Λ θ v b hvb Z htarget hstop F hF hFm m p k h ω =
      ControlledReferenceFamilyEvaluation.leaf P A hA Λ θ v b hvb Z htarget hstop F hF hFm
        m.physicalState m.physicalState m.physicalField m.physicalField p k h ω -
      ControlledReferenceFamilyEvaluation.reference P A hA Λ θ v b hvb Z htarget hstop F hF hFm
        m.physicalState m.physicalState m.physicalField m.physicalField p k h ω -
      ActualUncutRemainder.value (Base p) (fun z=>κ+a z) m.physicalState m.physicalField k h ω := by
  let D:=OrdinaryLevelOriginalNoise.data m (NL p k) (fun _ _ _=>0)
  have hl:UncutSmoothWords.weight (Base p) k h*D.leaf h ω=
      ControlledReferenceFamilyEvaluation.leaf P A hA Λ θ v b hvb Z htarget hstop F hF hFm
        m.physicalState m.physicalState m.physicalField m.physicalField p k h ω := by
    unfold ControlledReferenceFamilyEvaluation.leaf
    rw [OrdinaryJointSelf.uncutLeaf]
    unfold UncutWordEvaluation.leaf
    rw [UncutSmoothWords.test_eq_weight_normalized]
    rfl
  have hr:=JointUncutWordEvaluation.reference_eq_weight (Base p) Λ
    m.physicalState m.physicalState m.physicalField m.physicalField k h ω
  rw [OrdinaryJointSelf.reference] at hr
  change ControlledReferenceFamilyEvaluation.reference P A hA Λ θ v b hvb Z htarget hstop F hF hFm
    m.physicalState m.physicalState m.physicalField m.physicalField p k h ω=
      UncutSmoothWords.weight (Base p) k h*D.reference h ω at hr
  change UncutSmoothWords.weight (Base p) k h*(D.leaf h ω-D.reference h ω-D.remainder h ω)=
    _-_-UncutSmoothWords.weight (Base p) k h*D.remainder h ω
  rw [←hl,hr]
  ring

include m in
theorem total_bound : ∀z,|κ+a z|≤κ+M := by
  intro z
  rw [abs_of_nonneg (add_nonneg m.additive_pos.le (m.lower_pos.le.trans (m.variance_bounds z).1))]
  exact add_le_add le_rfl (m.variance_bounds z).2

include m in
theorem total_nonneg : 0≤κ+M :=
  add_nonneg m.additive_pos.le (m.lower_pos.le.trans ((m.variance_bounds 0).1.trans (m.variance_bounds 0).2))

theorem value_bound (k : ℕ) : ∃C:ℝ,0≤C∧∀p:Inputs,∀h ω,
    ‖value P A hA Λ θ v b hvb Z htarget hstop F hF hFm m p k h ω‖≤
      C*UncutSmoothWords.weight (Base (0,0)) k h := by
  obtain ⟨C,hC,hCb⟩:=ControlledReferenceFamilyEvaluation.evaluation_bound P A hA Λ θ v b hvb
    Z htarget hstop F hF hFm m.physicalState m.physicalState m.physicalField m.physicalField k
  obtain ⟨D,hD,hDb⟩:=ControlledActualTimeRemainder.remainder_bound P A hA Λ θ v b hvb
    Z htarget hstop F hF hFm (fun z=>κ+a z) (total_nonneg m) (total_bound m)
    m.physicalState m.physicalField k
  refine ⟨2*C+D,by positivity,fun p h ω=>?_⟩
  have hr:‖ActualUncutRemainder.value (Base p) (fun z=>κ+a z) m.physicalState m.physicalField k h ω‖≤
      D*UncutSmoothWords.weight (Base (0,0)) k h := by
    rw [ActualUncutRemainder.value,norm_mul,Real.norm_eq_abs,
      abs_of_nonneg (UncutSmoothWords.weight_nonneg (Base p) k h)]
    rw [ControlledReferenceFamilyBounds.weight_eq P A hA Λ θ v b hvb Z htarget hstop F hF hFm p (0,0) k h]
    exact (mul_le_mul_of_nonneg_left (hDb p h ω) (UncutSmoothWords.weight_nonneg (Base (0,0)) k h)).trans_eq (mul_comm _ _)
  rw [value_eq]
  exact (norm_sub_le _ _).trans ((add_le_add ((norm_sub_le _ _).trans
    (add_le_add (hCb p h ω).1 (hCb p h ω).2)) hr).trans_eq (by ring))

variable (hsmall : ProfileStability.memoryConstant P.lower P.holder P.exponent*
  ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
include hsmall in
theorem value_continuous (hΛ : 0≤Λ) (k : ℕ) (h : History Y k) (ω : Ω) :
    Continuous (fun p:Inputs=>value P A hA Λ θ v b hvb Z htarget hstop F hF hFm m p k h ω) := by
  have hl:=ControlledReferenceFamilyEvaluation.leaf_parameter_continuous P A hA Λ θ v b hvb
    Z htarget hstop F hF hFm hsmall m.physicalState m.physicalState m.physicalField m.physicalField hΛ k h ω
  have hr:=ControlledReferenceFamilyEvaluation.reference_parameter_continuous P A hA Λ θ v b hvb
    Z htarget hstop F hF hFm hsmall m.physicalState m.physicalState m.physicalField m.physicalField hΛ k h ω
  have hd:=ControlledActualTimeRemainder.value_continuous P A hA Λ θ v b hvb Z htarget hstop F hF hFm
    (fun z=>κ+a z) (measurable_const.add m.variance_measurable) (total_nonneg m) (total_bound m)
    m.physicalState m.physicalField hsmall hΛ m.physicalState_measurable m.physicalField_measurable k h ω
  convert! (hl.sub hr).sub hd using 1
  funext p
  exact value_eq P A hA Λ θ v b hvb Z htarget hstop F hF hFm m p k h ω

end SHE.ControlledOrdinaryNoise
