module

public import SHE.ControlledFamilyActualTransfer
public import SHE.ControlledThetaBackwardFields
public import SHE.UncutHistoryMass
public import SHE.CarrierStopBounds
public import SHE.ControlledJointMarkedWord
public import SHE.ControlledJointMeanIdentity
public import SHE.NativeHeatSpan

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section

namespace SHE.ControlledFamilyFrontFields
open Set MeasureTheory ProbabilityTheory AddCircle StoppedFourier WordRecursion ControlledProfile ControlledReferenceLevel
  CutoffWordLevel CutoffWordHistories SmoothCylinders UniformSmooth CutoffCarriers PhysicalChainArrays
  PhysicalScoreChain ControlledOldIntervals ControlledReferenceWindows ControlledFamilyProfileForest
  ProjectedUncutWord CoveredControlledLaw CoveredHistoryGeometry GaussianConvolution FiniteCenteredProduct
open scoped NNReal BigOperators
local instance controlledFamilyFrontFields_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance controlledFamilyFrontFields_circleSigma : MeasurableSpace CircleL2 := borel _
local instance controlledFamilyFrontFields_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable (P : CanonicalCovariance.ProfileParameters) (A : ℝ→ℝ) (hA : BoundedSmooth A)
variable (Λ : ℝ) (v b : ℝ≥0) (hvb : v≤b)
variable {X : Type} [MeasurableSpace X] {n : ℕ} (Z : VariableObservations.Family X n)
variable (htarget : ∀ x i,(b:ℝ)≤(Z.observations x i).target)
variable (hstop : ∀ x i,(b:ℝ)≤(Z.observations x i).stop)
variable (F : X→WordRecursion.State n→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun q : X×WordRecursion.State n=>F q.1 q.2))
local notation "Base" => ControlledReferenceThetaGeometry.level P A hA Λ v b hvb Z htarget hstop F hF hFm

local notation "Sig" => ControlledFamilyThreeLeg.sigma P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "Tar" => ControlledFamilyThreeLeg.target P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "Cen" => ControlledFamilyThreeLeg.center P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "Value" => ControlledFamilyThreeLeg.value P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "Mark" => ControlledFamilyThreeLeg.mark P A hA Λ v b hvb Z htarget hstop F hF hFm

local notation "Mean" => ControlledFamilyActualTransfer.mean P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "Val" => ControlledFamilyActualTransfer.actualValue P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "OME" => ControlledReferenceThetaGeometry.carrier_observations_eq P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "TME" => ControlledReferenceThetaGeometry.carrier_terminal_eq P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "WME" => ControlledReferenceThetaGeometry.weight_eq P A hA Λ v b hvb Z htarget hstop F hF hFm

/-- Joint Borel literal absolute-age current vector, permitting all
reference inputs/current states/original histories to be dependent. -/
theorem mean_measurable {W : Type} [MeasurableSpace W] (k : ℕ)
    (p : W→Inputs) (hp : Measurable p) (h : W→History X k) (hh : Measurable h)
    (q : W→ℝ) (hq : Measurable q) (U D : W→CircleL2) (hU : Measurable U) (hD : Measurable D)
    (θ : W→ℝ) (hθ : Measurable θ) :
    Measurable (fun w=>Mean (p w) k (h w) (q w) (U w) (D w) (θ w)) := by
  let Z₀ := (carrier (Base (0,(0,0))) k).observations
  let G : W→Fin (n+k)→ℝ := fun w i=>
    PhysicalProfile.physicalHeatMean (U w) ((Z₀.observations (h w) i).target-q w,(Z₀.observations (h w) i).center)+
      θ w*Real.exp (-Λ*((Z₀.observations (h w) i).stop-q w))*
        PhysicalProfile.physicalHeatMean (D w) ((Z₀.observations (h w) i).target-q w,(Z₀.observations (h w) i).center)
  have hG : Measurable G := by
    apply Measurable.of_eval
    intro i
    have hs := (Z₀.stop_measurable i).comp hh
    have ht := (Z₀.target_measurable i).comp hh
    have hc := (Z₀.center_measurable i).comp hh
    have hu := PhysicalProfile.physicalHeatMean_joint_measurable.comp (hU.prodMk ((ht.sub hq).prodMk hc))
    have hd := PhysicalProfile.physicalHeatMean_joint_measurable.comp (hD.prodMk ((ht.sub hq).prodMk hc))
    exact hu.add ((hθ.mul (((hs.sub hq).const_mul (-Λ)).exp)).mul hd)
  have he : (fun w=>Mean (p w) k (h w) (q w) (U w) (D w) (θ w))=
      fun w=>WithLp.toLp 2 (G w) := by
    funext w
    apply PiLp.ext
    intro i
    unfold ControlledFamilyActualTransfer.mean
    rw [ControlledJointWeightedWord.jointMeanVector_apply]
    unfold ControlledFamilyThreeLeg.center StoppedGaussianScore.nativeCenter
    rw [NativeHeatSpan.scale_inverse,OME (0,p w) (0,(0,0)) k]
  rw [he]
  exact (WithLp.measurable_toLp 2 (Fin (n+k)→ℝ)).comp hG

def activeValue (p : Inputs) (k : ℕ) (h : History X k) (q : ℝ) (U D : CircleL2) (θ : ℝ) : ℝ :=
  if (v:ℝ)≤q ∧ q<(carrier (Base (0,p)) k).terminal h then Val p k h q U D θ else 0

/-- Genuine joint Borel extension of the active actual family endpoint. -/
theorem active_value_measurable {W : Type} [MeasurableSpace W] (k : ℕ)
    (p : W→Inputs) (hp : Measurable p) (h : W→History X k) (hh : Measurable h)
    (q : W→ℝ) (hq : Measurable q) (U D : W→CircleL2) (hU : Measurable U) (hD : Measurable D)
    (θ : W→ℝ) (hθ : Measurable θ) :
    Measurable (fun w=>activeValue P A hA Λ v b hvb Z htarget hstop F hF hFm
      (p w) k (h w) (q w) (U w) (D w) (θ w)) := by
  classical
  have hm:=mean_measurable P A hA Λ v b hvb Z htarget hstop F hF hFm k p hp h hh q hq U D hU hD θ hθ
  have hmap : Measurable (fun w=>(((θ w,p w),(q w,h w)),Mean (p w) k (h w) (q w) (U w) (D w) (θ w))) :=
    ((hθ.prodMk hp).prodMk (hq.prodMk hh)).prodMk hm
  have hg:= (ControlledThetaBackwardFields.value_joint_measurable P A hA Λ v b hvb
    Z htarget hstop F hF hFm k).comp hmap
  have ht : Measurable (fun w=>(carrier (Base (0,p w)) k).terminal (h w)) := by
    convert ((carrier (Base (0,(0,0))) k).terminal_measurable).comp hh using 1
    funext w
    exact TME (0,p w) (0,(0,0)) k (h w)
  have hs : MeasurableSet {w : W | (v:ℝ)≤q w ∧ q w<(carrier (Base (0,p w)) k).terminal (h w)} :=
    (measurableSet_le measurable_const hq).inter (measurableSet_lt hq ht)
  have hg' : Measurable (fun w=>if (v:ℝ)≤q w ∧ q w<(carrier (Base (0,p w)) k).terminal (h w) then
      ActualMeanKernel.cappedAverage (Base (θ w,p w)) k (q w) (h w)
        (Mean (p w) k (h w) (q w) (U w) (D w) (θ w)) else 0) := hg.ite hs measurable_const
  convert hg' using 1
  funext w
  unfold activeValue
  split_ifs with ha
  · unfold ActualMeanKernel.cappedAverage ControlledFamilyActualTransfer.actualValue
    have hqt : q w≤(carrier (Base (θ w,p w)) k).terminal (h w) := by
      rw [TME (θ w,p w) (0,p w) k]
      exact ha.2.le
    rw [min_eq_left hqt]
  · rfl

/-- A finite-depth history mass bounds every actual endpoint uniformly
in theta, both past inputs and the current states. -/
theorem actual_value_bound (k : ℕ) : ∃ K : ℝ,0≤K ∧
    ∀ p θ h q U D,|Val p k h q U D θ|≤K*UncutSmoothWords.weight (Base (0,(0,0))) k h := by
  obtain ⟨K,hKn,hK⟩:=(ControlledThetaWordFields.normalized_uniform P A hA Λ v b hvb
    Z htarget hstop F hF hFm k).norm_bound
  refine ⟨K,hKn,fun p θ h q U D=>?_⟩
  apply GaussianFirstSplit.gaussianAverage_bound
  intro z
  rw [UncutSmoothWords.test_eq_weight_normalized,Pi.smul_apply,smul_eq_mul,abs_mul,
    abs_of_nonneg (UncutSmoothWords.weight_nonneg _ _ _),WME (θ,p) (0,(0,0)) k]
  have hz:=hK ((θ,p),h) z
  have hb : |UncutSmoothWords.normalized (Base (θ,p)) k h z|≤K := by
    simpa only [Real.norm_eq_abs] using hz
  exact (mul_le_mul_of_nonneg_left hb (UncutSmoothWords.weight_nonneg _ _ _)).trans_eq (mul_comm _ _)

end SHE.ControlledFamilyFrontFields
