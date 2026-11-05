module

public import SHE.MixedPastSpatialMoments
public import SHE.ControlledFamilyMeanFields
public import SHE.MixedPastKernelSections
public import SHE.ControlledFamilyMeanEnergy
public import SHE.ControlledFamilyMeanFirstMoment
public import SHE.PastMeanAbsoluteBudget
public import SHE.MixedPastMeanFirstMoment
public import SHE.MixedPastBaselineFTCIdentity
public import SHE.MixedPastMeanLegIdentity
public import SHE.SectionFirstMoment
public import SHE.ControlledFamilyMeanFieldsBorel

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3600000
set_option quotPrecheck false

namespace SHE.MixedPastMeanAbsolute
open MeasureTheory PredictableL2 NativeHeatObservation NativeObservationNaturality
  FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation StoppedItoInputs
open scoped NNReal ENNReal
local instance mixedPastMeanAbsolute_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedPastMeanAbsolute_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedPastMeanAbsolute_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedPastMeanAbsolute_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedPastMeanAbsolute_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedPastMeanAbsolute_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)
variable (u₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀)
variable (J : StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))
open Real AddCircle Set Filter WordRecursion ControlledProfile ControlledReferenceLevel SmoothCylinders UniformSmooth
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalScoreChain PhysicalChainArrays
  PhysicalParentGeometry CoveredHistoryGeometry CoveredControlledLaw ControlledOldIntervals
  HistoryProductMeasure ActualMeanKernel
local instance mixedPastMeanAbsolute_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedPastMeanAbsolute_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance mixedPastMeanAbsolute_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
variable (P : CanonicalCovariance.ProfileParameters) (haP : BoundedSmooth P.coefficient)
variable (v b : ℝ≥0) (hvb : v≤b)
variable (Z : VariableObservations.Family HeatCircle 1)
variable (htarget : ∀ x i,(b:ℝ)≤(Z.observations x i).target)
variable (hstop : ∀ x i,(b:ℝ)≤(Z.observations x i).stop)
variable (F : HeatCircle→WordRecursion.State 1→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun z : HeatCircle×WordRecursion.State 1=>F z.1 z.2))
local notation "Base" => ControlledReferenceThetaGeometry.level P P.coefficient haP Λ v b hvb Z htarget hstop F hF hFm
local notation "Zero" => Base (0,(0,0))
local notation "U" => MixedPastJointData.pastU 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v
local notation "Dir" => MixedPastJointData.pastD 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v
local notation "Mean" => MixedPastLiteralPoint.meanField 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S P haP v b hvb Z htarget hstop F hF hFm

open NativeRandomKernel NormalizedKernelSplit QuarterSpatialEvent
local notation "Ref" => (fun a : ℝ×Inputs=>referenceData P P.coefficient haP Λ a.1 v b hvb a.2)

/-- The entire native negative-output mean mark, applied to the actual
dependent current difference of the original mixed common-driver pair. -/
def input (k : ℕ) (θ : ℝ) (q : ℝ≥0) (mass ρ : ℝ) (hmass : 1≤mass) (hρ : 0≤ρ)
    (t : Fin k→ℝ) (ω : Ω) : CircleL2 :=
  OneInputOperator.besselHalf mass ρ hmass hρ
    (integralOperator (MixedPastKernelFields.spatial 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S
      P haP v b hvb Z htarget hstop F hF hFm k θ q q t) ω
      (embed (S.second q ω-S.first q ω)))

attribute [local irreducible] MixedPastMeanLegIdentity.leg MixedPastMeanFirstMoment.value
local notation "Leg"=>MixedPastMeanLegIdentity.leg 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
  P haP v b hvb Z htarget hstop F hF hFm

/-- Joint Borel structure of the literal mean leg, including its active
current window, actual random past reference and correlated current states. -/
theorem leg_measurable (k : ℕ) (θ : ℝ) (q : ℝ≥0) :
    Measurable (fun z : Ω×History HeatCircle k=>Leg k θ q z.2 z.1) := by
  have hU := (MixedPastJointData.pastU_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v).mono (𝓕.le v) le_rfl
  have hDir := (MixedPastJointData.pastD_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S v).mono (𝓕.le v) le_rfl
  have hUq := (MixedPastJointData.pastU_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S q).mono (𝓕.le q) le_rfl
  have hDq := (MixedPastJointData.pastD_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ u₀ S q).mono (𝓕.le q) le_rfl
  have hh:=ControlledFamilyMeanFieldsBorel.mean_variable_measurable P P.coefficient haP Λ v b hvb
    Z htarget hstop F hF hFm k
    (fun z : Ω×History HeatCircle k=>(U z.1,Dir z.1)) ((hU.comp measurable_fst).prodMk (hDir.comp measurable_fst))
    Prod.snd measurable_snd (fun _=>(q:ℝ)) measurable_const
    (fun z=>embed (S.first q z.1)) (fun z=>embed (S.second q z.1-S.first q z.1))
    (hUq.comp measurable_fst) (hDq.comp measurable_fst) (fun _=>θ) measurable_const
  simpa only [MixedPastMeanLegIdentity.leg] using hh

include hIJ₀ hIJ₁ in
/-- Genuine absolute sample × ORIGINAL-history integrability of the
entire actual mean leg. No old-space cancellation is used. The finite
relative-age time budget is valid at every finite depth, including zero. -/
theorem actual_absolute_history (hlocal : StandardTerminalPastLocality J) (hΛ : 0≤Λ)
    (hages : ∀ x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (hrootStop : ∀ x i,(Z.observations x i).stop≤(b:ℝ))
    (hrootTarget : ∀ x i,(Z.observations x i).target=(b:ℝ))
    (hspan : (b:ℝ)-(v:ℝ)≤P.horizon) (root : Measure HeatCircle) [IsFiniteMeasure root] (k : ℕ)
    (hfresh : (b:ℝ)-(v:ℝ)≤UniformFutureProfileScores.horizon (1+k))
    (hold : ∀ j,j<k→(b:ℝ)-(v:ℝ)≤uniformHorizon 1 j)
    (θ : ℝ) (hθ : |θ|≤1) (A0 ν : ℝ) (hA0 : 0≤A0) (hν : 0≤ν)
    (hjet : ∀ x j,j≤k→∀ z,‖iteratedFDeriv ℝ j (F x) z‖≤A0*ν^j)
    (B0 : ℝ≥0) (hBDG : StandardTerminalBDGPower (k+2) J B0)
    (q : ℝ≥0) (hvq : v≤q) (hqb : q<b) (hqH : q≤H) (hq1 : (q:ℝ)≤1) :
    let C:=MixedPastWordMoments.momentConstant P k k 1
      ((k:ℝ)*(NativeHybridMoments.momentConstant (k+2) B0 κ M)^P.exponent)
    let K:=sqrt (∫ ω,‖S.second q ω-S.first q ω‖^2 ∂μ)*
      (sqrt C*((1+k:ℕ):ℝ)*sqrt (2*UniformFutureProfileScores.constant (1+k)/P.lower))
    Integrable (fun z : Ω×History HeatCircle k=>Leg k θ q z.2 z.1)
      (μ.prod (historyMeasure (referenceData P P.coefficient haP Λ 0 v b hvb (0,0)) root k)) ∧
    (∫ z : Ω×History HeatCircle k,|Leg k θ q z.2 z.1|
      ∂μ.prod (historyMeasure (referenceData P P.coefficient haP Λ 0 v b hvb (0,0)) root k))≤
      K*(root.real univ*(Fintype.card (OrderedHeatForests.Choices 1 k):ℝ)*
        QuarterRMSTimeFactors.oldTimeBudget P (fraction P*P.lower) (uniformConstant 1) k
          ((b:ℝ)-(v:ℝ)) ((q:ℝ)-(v:ℝ)) (1/2:ℝ) A0 ν) := by
  intro C K
  let D:=PastMeanTimeFactors.absoluteDensity Zero P (fraction P*P.lower) (uniformConstant 1) k q (1/2:ℝ) A0 ν
  have hK : 0≤K:=mul_nonneg (sqrt_nonneg _)
    (mul_nonneg (mul_nonneg (sqrt_nonneg _) (Nat.cast_nonneg _)) (sqrt_nonneg _))
  have hD (p) : 0≤D p:=PastMeanTimeFactors.absoluteDensity_nonneg Zero P
    (mul_pos (fraction_pos P) P.lower_pos) (uniformConstant 1) (fun j=>(uniformConstant_pos 1 j).le)
      k q (1/2:ℝ) A0 ν p
  have hDi:=PastMeanTimeFactors.absoluteDensity_history_budget Zero P (b:ℝ) (fun _=>rfl) hrootTarget hages
    (mul_pos (fraction_pos P) P.lower_pos) (uniformConstant 1) (fun j=>(uniformConstant_pos 1 j).le) k
    (q:=(q:ℝ)) (fresh:=(1/2:ℝ)) (A0:=A0) (ν:=ν)
    (by exact_mod_cast hvq) (by exact_mod_cast hqb) (by rfl) (by norm_num) (by norm_num) hA0 hν root
  have hp:=MixedPastMeanFirstMoment.first_moment_ae 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    J hIJ₀ hIJ₁ P haP v b hvb Z htarget hstop F hF hFm hlocal hΛ hages hrootStop
    (fun x i=>(hrootTarget x i).le) hspan root k hfresh hold θ hθ A0 ν hA0 hν hjet B0 hBDG q hvq hqH hq1
  have hs : ∀ᵐ p ∂historyMeasure (referenceData P P.coefficient haP Λ 0 v b hvb (0,0)) root k,
      Integrable (fun ω=>Leg k θ q p ω) μ ∧ (∫ ω,|Leg k θ q p ω| ∂μ)≤K*D p := by
    filter_upwards [hp] with p hp
    by_cases hqt : (q:ℝ)<(carrier Zero k).terminal p
    · by_cases hstrict : StrictHistory Zero k p
      · have he : (fun ω=>Leg k θ q p ω)=
            MixedPastMeanFirstMoment.value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm k θ q p:=
          funext (fun ω=>MixedPastMeanLegIdentity.leg_eq_value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
            P haP v b hvb Z htarget hstop F hF hFm hages hrootStop k θ q hvq p hqt ω)
        simpa only [he,C,K,D] using hp hstrict hqt
      · have hz (ω : Ω) : Leg k θ q p ω=0:=
          (MixedPastMeanLegIdentity.leg_eq_value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
            P haP v b hvb Z htarget hstop F hF hFm hages hrootStop k θ q hvq p hqt ω).trans
          (MixedPastMeanLegIdentity.value_zero_of_not_strict 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
            P haP v b hvb Z htarget hstop F hF hFm k θ q p hstrict ω)
        simp only [hz,abs_zero,integral_zero]
        exact ⟨integrable_const _,mul_nonneg hK (hD p)⟩
    · have hz (ω : Ω) : Leg k θ q p ω=0:=MixedPastMeanLegIdentity.leg_zero_of_not_current
        𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S P haP v b hvb Z htarget hstop F hF hFm k θ q p hqt ω
      simp only [hz,abs_zero,integral_zero]
      exact ⟨integrable_const _,mul_nonneg hK (hD p)⟩
  have hj:=SectionFirstMoment.joint_integrable μ _ _ (leg_measurable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ S
    P haP v b hvb Z htarget hstop F hF hFm k θ q) (fun p=>K*D p) (hDi.1.const_mul K) hs
  refine ⟨hj.1,?_⟩
  rw [integral_const_mul] at hj
  exact hj.2.trans (mul_le_mul_of_nonneg_left hDi.2 hK)
end SHE.MixedPastMeanAbsolute
