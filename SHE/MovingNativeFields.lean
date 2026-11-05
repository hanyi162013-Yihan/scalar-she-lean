module

public import SHE.ControlledFamilyMeanFieldsBorel
public import SHE.MixedPastJointData
public import SHE.ControlledFamilyMeanFields
public import SHE.JointInterpolationFields
public import SHE.PastEventWeights
public import SHE.VaryingControlledGaussianFields
public import SHE.MixedNativePastWeightedMoments
public import SHE.MixedNativePastThetaMoments
public import SHE.NativePastHybridMoments
public import SHE.ControlledProfile
public import SHE.PastHybridIntegral
public import SHE.PastItoAlgebra
public import SHE.MixedNativePairObservation
public import SHE.NativePairScaledMartingale
public import SHE.NativePairLocalMartingale
public import SHE.NativePairExtendedMartingale

@[expose] public section
noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option quotPrecheck false

namespace SHE.MovingNativeFields
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance movingNativeFields_realSigma : MeasurableSpace RealL2 := borel _
local instance movingNativeFields_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance movingNativeFields_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance movingNativeFields_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance movingNativeFields_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance movingNativeFields_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)

local instance movingNativeFields_circleSigma : MeasurableSpace CircleL2 := borel _
local instance movingNativeFields_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance movingNativeFields_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance movingNativeFields_twoFinite : Fact ((2:ℝ≥0∞)≠∞) := ⟨by simp⟩
variable {W : Type} [MeasurableSpace W]

/-- The actual past profile inputs are jointly Borel in the moving
past time and sample, rather than only measurable separately at v. -/
theorem past_inputs_measurable :
    Measurable (fun z : ℝ≥0×Ω=>(embed (S.first z.1 z.2),embed (S.second z.1 z.2-S.first z.1 z.2))) := by
  have hu:=(S.first_predictable.mono (predictable_le_product 𝓕)).measurable
  have hv:=(S.second_predictable.mono (predictable_le_product 𝓕)).measurable
  exact (embed.continuous.measurable.comp hu).prodMk (embed.continuous.measurable.comp (hv.sub hu))

/-- Moving past and relative current times are genuine joint parameters
of the original constructed common-driver pair. -/
theorem shifted_states_measurable (v s : W→ℝ≥0) (hv : Measurable v) (hs : Measurable s)
    (ω : W→Ω) (hω : Measurable ω) :
    Measurable (fun w=>(S.first (v w+s w) (ω w),S.second (v w+s w) (ω w))) := by
  have hm:=(hv.add hs).prodMk hω
  exact (((S.first_predictable.mono (predictable_le_product 𝓕)).measurable).comp hm).prodMk
    (((S.second_predictable.mono (predictable_le_product 𝓕)).measurable).comp hm)

/-- Every variable past, relative current time, original history and
theta may be substituted together into the actual canonical mean leg
on a fixed relative local span. Its current input is the literal native
difference S.second(v+s)-S.first(v+s). -/
theorem relative_mean_leg_measurable
    (P : CanonicalCovariance.ProfileParameters) (A : ℝ→ℝ) (hA : SmoothCylinders.BoundedSmooth A)
    (h : ℝ≥0) {X : Type} [MeasurableSpace X] {n : ℕ} (Z : VariableObservations.Family X n)
    (htarget : ∀ x i,(h:ℝ)≤(Z.observations x i).target)
    (hstop : ∀ x i,(h:ℝ)≤(Z.observations x i).stop)
    (F : X→WordRecursion.State n→ℝ) (hF : UniformSmooth.UniformBoundedSmooth F)
    (hFm : Measurable (fun z : X×WordRecursion.State n=>F z.1 z.2))
    (k : ℕ) (past age : W→ℝ≥0) (hpast : Measurable past) (hage : Measurable age)
    (ω : W→Ω) (hω : Measurable ω)
    (hist : W→CutoffWordHistories.History X k) (hhist : Measurable hist)
    (θ : W→ℝ) (hθ : Measurable θ) :
    Measurable (fun w=>ControlledFamilyLegFubini.mean P A hA Λ 0 h (show (0:ℝ≥0)≤h from bot_le) Z htarget hstop F hF hFm
      (embed (S.first (past w) (ω w)),embed (S.second (past w) (ω w)-S.first (past w) (ω w)))
      k (hist w) (age w) (embed (S.first (past w+age w) (ω w)))
      (embed (S.second (past w+age w) (ω w)-S.first (past w+age w) (ω w))) (θ w)) := by
  have hp:=(past_inputs_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S).comp (hpast.prodMk hω)
  have hc:=shifted_states_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S past age hpast hage ω hω
  exact ControlledFamilyMeanFieldsBorel.mean_variable_measurable
    P A hA Λ 0 h (show (0:ℝ≥0)≤h from bot_le) Z htarget hstop F hF hFm k _ hp hist hhist
    (fun w=>(age w:ℝ)) (measurable_subtype_coe.comp hage)
    _ _ (embed.continuous.measurable.comp hc.fst) (embed.continuous.measurable.comp (hc.snd.sub hc.fst)) θ hθ

/-- The relative native joint current keeps exactly the original
absolute stops and targets after the moving-past change of clock. -/
theorem relative_current_eq (θ : ℝ) (v s : ℝ≥0) {n : ℕ}
    (σ target : Fin n→ℝ) (center : Fin n→HeatCircle) (ω : Ω) :
    JointInterpolationAlgebra.current Λ s θ (S.first (v+s) ω) (S.second (v+s) ω)
      (fun i=>⟨σ i,target i,center i⟩)=
    MixedPastJointData.mean 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S θ v (v+s) σ target center ω := by
  apply PiLp.ext
  intro i
  simp only [JointInterpolationAlgebra.current,MixedPastJointData.mean,
    MixedNativePastThetaCentering.current,WithLp.ofLp_toLp,NNReal.coe_add]
  congr 2 <;> ring

section HilbertInput
open CutoffWordLevel CutoffWordHistories ControlledProfile SmoothCylinders UniformSmooth
variable (P : CanonicalCovariance.ProfileParameters) (A : ℝ→ℝ) (hA : BoundedSmooth A)
variable (h : ℝ≥0) (Z : VariableObservations.Family HeatCircle 1)
variable (htarget : ∀ x i,(h:ℝ)≤(Z.observations x i).target)
variable (hstop : ∀ x i,(h:ℝ)≤(Z.observations x i).stop)
variable (F : HeatCircle→WordRecursion.State 1→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun z : HeatCircle×WordRecursion.State 1=>F z.1 z.2))
local notation "Ref"=>(fun a : ℝ×Inputs=>ControlledReferenceLevel.referenceData P A hA Λ a.1 0 h (show (0:ℝ≥0)≤h from bot_le) a.2)
local notation "Base"=>ControlledReferenceThetaGeometry.level P A hA Λ 0 h (show (0:ℝ≥0)≤h from bot_le) Z htarget hstop F hF hFm

/-- The literal negative-output mean input on a fixed relative span,
with the original moving physical past and current states substituted. -/
def relativeMeanInput (k : ℕ) (mass ρ : ℝ) (hmass : 1≤mass) (hρ : 0≤ρ)
    (past age : W→ℝ≥0) (θ : W→ℝ) (t : W→Fin k→ℝ) (ω : W→Ω) : W→CircleL2 :=
  ActualMeanKernel.familyMeanInput Ref Base
    (fun w=>(θ w,(embed (S.first (past w) (ω w)),embed (S.second (past w) (ω w)-S.first (past w) (ω w)))))
    k mass ρ hmass hρ (fun _=>Λ) (fun w=>(age w:ℝ))
    (fun w p=>ControlledFamilyActualTransfer.mean P A hA Λ 0 h (show (0:ℝ≥0)≤h from bot_le) Z htarget hstop F hF hFm
      (embed (S.first (past w) (ω w)),embed (S.second (past w) (ω w)-S.first (past w) (ω w)))
      k p (age w) (embed (S.first (past w+age w) (ω w)))
      (embed (S.second (past w+age w) (ω w)-S.first (past w+age w) (ω w))) (θ w))
    t (fun w=>S.second (past w+age w) (ω w)-S.first (past w+age w) (ω w))

/-- Joint moving-past/current/interpolation/history-time Borel
measurability in the ACTUAL Hilbert input space. Every kernel and
Gaussian-front applicability condition is derived internally. -/
theorem relativeMeanInput_measurable (hΛ : 0≤Λ) (k : ℕ) (mass ρ : ℝ) (hmass : 1≤mass) (hρ : 0≤ρ)
    (past age : W→ℝ≥0) (hpast : Measurable past) (hage : Measurable age)
    (θ : W→ℝ) (hθ : Measurable θ) (t : W→Fin k→ℝ) (ht : Measurable t)
    (ω : W→Ω) (hω : Measurable ω) :
    Measurable (relativeMeanInput 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P A hA h Z htarget hstop F hF hFm k mass ρ hmass hρ past age θ t ω) := by
  let p : W→Inputs:=fun w=>(embed (S.first (past w) (ω w)),embed (S.second (past w) (ω w)-S.first (past w) (ω w)))
  let U : W→CircleL2:=fun w=>embed (S.first (past w+age w) (ω w))
  let D : W→CircleL2:=fun w=>embed (S.second (past w+age w) (ω w)-S.first (past w+age w) (ω w))
  have hp : Measurable p:=(past_inputs_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S).comp (hpast.prodMk hω)
  have hc:=shifted_states_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S past age hpast hage ω hω
  have hU : Measurable U:=embed.continuous.measurable.comp hc.fst
  have hD : Measurable D:=embed.continuous.measurable.comp (hc.snd.sub hc.fst)
  have hq : Measurable (fun w : W=>(age w:ℝ)):=measurable_subtype_coe.comp hage
  have hm:=ControlledFamilyFrontFields.mean_measurable P A hA Λ 0 h (show (0:ℝ≥0)≤h from bot_le) Z htarget hstop F hF hFm k
    (fun z : W×History HeatCircle k=>p z.1) (hp.comp measurable_fst)
    Prod.snd measurable_snd (fun z=>(age z.1:ℝ)) (hq.comp measurable_fst)
    (fun z=>U z.1) (fun z=>D z.1) (hU.comp measurable_fst) (hD.comp measurable_fst)
    (fun z=>θ z.1) (hθ.comp measurable_fst)
  exact ControlledFamilyMeanFields.meanInput_measurable P A hA Λ 0 h (show (0:ℝ≥0)≤h from bot_le) Z htarget hstop F hF hFm hΛ
    (fun w=>(θ w,p w)) (hθ.prodMk hp) k mass ρ hmass hρ
    (fun w=>(age w:ℝ)) hq _ hm t ht _ (hc.snd.sub hc.fst)
end HilbertInput

end SHE.MovingNativeFields

