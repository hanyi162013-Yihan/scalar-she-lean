module
public import SHE.OrdinaryUncutNoise
public import SHE.OrdinaryJointSelf
public import SHE.JointUncutSuccessor

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
namespace SHE.OrdinaryUncutSampleExpansion
open Set MeasureTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
  CutoffCarriers UncutWordEvaluation IntegratedPhysicalStep GaussianItoTest
open scoped NNReal
local instance ordinaryUncutSampleExpansion_period:Fact (0<2*Real.pi):=⟨by positivity⟩
local instance ordinaryUncutSampleExpansion_sigma:MeasurableSpace CircleL2:=borel _
local instance ordinaryUncutSampleExpansion_borel:BorelSpace CircleL2:=⟨rfl⟩
variable {Y Ω:Type}[MeasurableSpace Y][MeasurableSpace Ω]
variable {𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›}{μ:Measure Ω}[IsProbabilityMeasure μ]
variable {H:ℝ≥0}{κ:ℝ}{a:ℝ→ℝ}{ell M:ℝ}(m:TwoChannelCutoffModel.Model 𝓕 μ H κ a ell M)
variable {R:ReferenceData}{n:ℕ}(L:Level R Y n)
local notation "U"=>m.physicalState
local notation "X"=>m.physicalField
local notation "leaf"=>JointUncutWordEvaluation.leaf L 0 U U X X
local notation "ref"=>JointUncutWordEvaluation.reference L 0 U U X X
local notation "actual"=>ActualUncutRemainder.value L (fun z=>κ+a z) U X
local notation "companion"=>ActualUncutRemainder.value L R.totalVariance U X

def leafMass (ν:Measure Y)(k:ℕ)(ω:Ω):ℝ:=∫h,leaf k h ω ∂historyMeasure R ν k
def referenceMass (ν:Measure Y)(k:ℕ)(ω:Ω):ℝ:=∫h,ref k h ω ∂historyMeasure R ν k
def noiseMass (ν:Measure Y)(k:ℕ)(ω:Ω):ℝ:=∫h,OrdinaryUncutNoise.value m L k h ω ∂historyMeasure R ν k
def errorMass (ν:Measure Y)(k:ℕ)(ω:Ω):ℝ:=∫h,actual k h ω-companion k h ω ∂historyMeasure R ν k

theorem noise_eq (k:ℕ)(h:History Y k)(ω:Ω):
    OrdinaryUncutNoise.value m L k h ω=leaf k h ω-ref k h ω-actual k h ω:=by
  let D:=OrdinaryLevelOriginalNoise.data m (normalizedLevel L k) (fun _ _ _=>0)
  have hl:UncutSmoothWords.weight L k h*D.leaf h ω=leaf k h ω:=by
    rw [OrdinaryJointSelf.uncutLeaf]
    unfold UncutWordEvaluation.leaf
    rw [UncutSmoothWords.test_eq_weight_normalized]
    rfl
  have hr:=JointUncutWordEvaluation.reference_eq_weight L 0 U U X X k h ω
  rw [OrdinaryJointSelf.reference] at hr
  change ref k h ω=UncutSmoothWords.weight L k h*D.reference h ω at hr
  change UncutSmoothWords.weight L k h*(D.leaf h ω-D.reference h ω-D.remainder h ω)=
    _-_-UncutSmoothWords.weight L k h*D.remainder h ω
  rw [←hl,hr]
  ring

/-- A literal samplewise ordinary-U recursion, with its actual rough
bracket. The mismatch is an additional positive first-hit insertion. -/
theorem sample_cycle (ν:Measure Y)[IsFiniteMeasure ν](k:ℕ)(ω:Ω):
    leafMass m L ν k ω=referenceMass m L ν k ω+noiseMass m L ν k ω+
      errorMass m L ν k ω+leafMass m L ν (k+1) ω:=by
  let σ:=historyMeasure R ν k
  let W:=UncutSmoothWords.weight L k
  have hW:Integrable W σ:=UncutHistoryMass.weight_integrable L ν k
  have hint(f:History Y k×Ω→ℝ)(hf:Measurable f)(C:ℝ)(hb:∀h ω,‖f (h,ω)‖≤C*W h):
      Integrable (fun h=>f (h,ω)) σ:=
    (hW.const_mul C).mono' (hf.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun h=>hb h ω))
  obtain ⟨C,_,hCl,hCr⟩:=JointUncutWordEvaluation.evaluation_norm_bounds L 0 U U X X k
  have hiL:=hint _ (JointUncutWordEvaluation.leaf_measurable L 0 m.physicalState_measurable m.physicalState_measurable
    m.physicalField_measurable m.physicalField_measurable k) C hCl
  have hiR:=hint _ (JointUncutWordEvaluation.reference_measurable L 0 m.physicalState_measurable m.physicalState_measurable
    m.physicalField_measurable m.physicalField_measurable k) C hCr
  have hM:0≤M:=m.lower_pos.le.trans ((m.variance_bounds 0).1.trans (m.variance_bounds 0).2)
  have hcap(z):|κ+a z|≤κ+M:=by
    rw [abs_of_nonneg (add_nonneg m.additive_pos.le (m.lower_pos.le.trans (m.variance_bounds z).1))]
    exact add_le_add le_rfl (m.variance_bounds z).2
  obtain ⟨D,_,hDb⟩:=ActualUncutRemainder.bound L (fun z=>κ+a z)
    (measurable_const.add m.variance_measurable) (add_nonneg m.additive_pos.le hM) hcap U X
    m.physicalState_measurable m.physicalField_measurable k
  have hiA:=hint _ (ActualUncutRemainder.value_measurable L (fun z=>κ+a z)
    (measurable_const.add m.variance_measurable) U X m.physicalState_measurable m.physicalField_measurable k) D hDb
  obtain ⟨B,hB⟩:=R.totalVariance_smooth.norm_bound
  have hBn:0≤B:=(norm_nonneg _).trans (hB 0)
  have hb(z):|R.totalVariance z|≤B:=by simpa only [Real.norm_eq_abs] using hB z
  obtain ⟨E,_,hEb⟩:=ActualUncutRemainder.bound L R.totalVariance
    R.totalVariance_smooth.smooth.continuous.measurable hBn hb U X
    m.physicalState_measurable m.physicalField_measurable k
  have hiC:=hint _ (ActualUncutRemainder.value_measurable L R.totalVariance
    R.totalVariance_smooth.smooth.continuous.measurable U X m.physicalState_measurable m.physicalField_measurable k) E hEb
  simp only [Prod.fst,Prod.snd] at hiL hiR hiA hiC
  have he:(∫h,OrdinaryUncutNoise.value m L k h ω ∂σ)=
      (∫h,leaf k h ω ∂σ)-(∫h,ref k h ω ∂σ)-(∫h,actual k h ω ∂σ):=by
    simp_rw [noise_eq m L]
    have he1:=integral_sub hiL hiR
    have he2:=integral_sub (hiL.sub hiR) hiA
    simp only [Pi.sub_apply] at he1 he2
    linarith only [he1,he2]
  have herr:=integral_sub hiA hiC
  try simp only [Pi.sub_apply] at herr
  have hs:=JointUncutSuccessor.averaged_eq L 0 U U X X m.physicalState_measurable m.physicalState_measurable
    m.physicalField_measurable m.physicalField_measurable ν k ω
  have hcomp:(∫h,companion k h ω ∂σ)=leafMass m L ν (k+1) ω:=by
    calc
      _=∫h,JointUncutLocalRemainder.value L 0 U U X X k h ω ∂σ:=by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun h=>(OrdinaryJointSelf.uncutLocalRemainder L 0 U X k h ω).symm)
      _=_:=hs
  change (∫h,leaf k h ω ∂σ)=(∫h,ref k h ω ∂σ)+_+_+_
  dsimp only [noiseMass,errorMass]
  linarith only [he,herr,hcomp]

/-- Finite depth is fixed before any approximation limit. This exact
identity keeps every original history normalization and error sign. -/
theorem finite_expansion (ν:Measure Y)[IsFiniteMeasure ν](depth:ℕ)(ω:Ω):
    leafMass m L ν 0 ω=(∑k∈Finset.range depth,referenceMass m L ν k ω)+
      (∑k∈Finset.range depth,noiseMass m L ν k ω)+
      (∑k∈Finset.range depth,errorMass m L ν k ω)+leafMass m L ν depth ω:=by
  induction depth with
  | zero=>simp
  | succ k ih=>
    have hs:=sample_cycle m L ν k ω
    simp only [Finset.sum_range_succ]
    linarith only [ih,hs]

end SHE.OrdinaryUncutSampleExpansion
