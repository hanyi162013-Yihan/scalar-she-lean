module

public import SHE.MixedCanonicalZeroHeatGradient
public import SHE.ControlledNormalizedNoiseBounds
public import SHE.ControlledReferenceCutoffBounds
public import SHE.NativeWeightedTerminalCap
public import SHE.CutoffUncutComparison
public import SHE.MixedNoiseTestScaling
public import SHE.MixedCanonicalGradientHeat
public import SHE.NativeVariableTerminalCap
public import SHE.MixedCanonicalGradientAverage
public import SHE.TerminalItoRawLimit
public import SHE.WeightedHistoryL2Limit
public import SHE.RecursiveHeatGradientContinuity
public import SHE.NativeRowTargetContinuity

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option quotPrecheck false
namespace SHE.MixedCanonicalUncutGradientKernel
open MeasureTheory Set PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation CutoffWordLevel
open GaussianTaylorAverage JointWordAnalytic GaussianItoTest ControlledProfile ControlledReferenceLevel
open Filter Topology Classical
open scoped ENNReal NNReal
local instance mixedCanonicalUncutGradientKernel_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance mixedCanonicalUncutGradientKernel_circleSigma : MeasurableSpace CircleL2 := borel _
local instance mixedCanonicalUncutGradientKernel_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance mixedCanonicalUncutGradientKernel_realSigma : MeasurableSpace RealL2 := borel _
local instance mixedCanonicalUncutGradientKernel_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedCanonicalUncutGradientKernel_inputSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedCanonicalUncutGradientKernel_inputBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedCanonicalUncutGradientKernel_bothSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedCanonicalUncutGradientKernel_bothBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)

open ControlledProfile ControlledReferenceLevel
variable (P : CanonicalCovariance.ProfileParameters) (hAs : SmoothCylinders.BoundedSmooth (fun z => κ+aV z))
variable (θ : ℝ) (v b : ℝ≥0) (hvb : v≤b)
variable {n : ℕ} (Z : Fin n→WordRecursion.Observation)
variable (htarget : ∀ i,(b:ℝ)≤(Z i).target) (hstop : ∀ i,(b:ℝ)≤(Z i).stop)
variable (F : WordRecursion.State n→ℝ) (hF : SmoothCylinders.BoundedSmooth F)
local notation "Base" => ControlledReferenceLevel.level P (fun z=>κ+aV z) hAs Λ θ v b hvb Z htarget hstop F hF
local notation "L" => (fun δ:ℝ=>fun hδ:0<δ=>ControlledReferenceRecursiveBounds.level P (fun z=>κ+aV z) hAs Λ θ v b hvb Z htarget hstop F hF δ hδ)

local notation "dU" => MixedNativeJointHistory.firstData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
local notation "dV" => MixedNativeJointHistory.secondData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
local notation "U" => (dU).physicalState
local notation "V" => (dV).physicalState
local notation "XU" => (dU).physicalField
local notation "XV" => (dV).physicalField

variable (hsmall : ProfileStability.memoryConstant P.lower P.holder P.exponent*
  ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)

local notation "pastParameter" => MixedNativeRandomReferenceStep.randomParameter 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v
variable (J : StandardTerminalIto (C := Both RealHaarInput) (E := ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))

variable (hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ) (hΛ:0≤Λ) (hbH:b≤H)

variable (k:ℕ)
local notation "Held"=>PredictablePastParameter.held v pastParameter (0,0)

local notation "Carrier" => (fun p:Inputs=>CutoffCarriers.carrier (Base p) k)
local notation "NL" => (fun p:Inputs=>UncutWordEvaluation.normalizedLevel (Base p) k)
local notation "Obs" => (Carrier (0,0)).observations.observations
local notation "Terminal" => (Carrier (0,0)).terminal
local notation "Mean"=>MixedCanonicalGradientKernel.mean
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
  P hAs θ v b hvb Z htarget hstop F hF 1 zero_lt_one 0 k
local notation "Cut" => (fun δ:ℝ=>fun hδ:0<δ=>MixedCanonicalGradientKernel.raw
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
  P hAs θ v b hvb Z htarget hstop F hF δ hδ 0 k)
local notation "W" => UncutSmoothWords.weight (Base (0,0)) k

/-- The exact uncut physical gradient input. The entire true uncut word
is differentiated, with the actual random past reference inside its
Gaussian reserve and original individual stopping ages retained. -/
def raw (z:CutoffWordHistories.History Unit k×(ℝ≥0×Ω)):Both RealHaarInput:=
  if (v:ℝ)<(z.2.1:ℝ) ∧ (z.2.1:ℝ)<Terminal z.1 then
    ∑i:Fin (n+k),
      (fderiv ℝ (GaussianItoTest.backward ((Carrier (Held z.2)).window z.1)
        (UncutSmoothWords.test (Base (Held z.2)) k z.1) (z.2.1:ℝ)) (Mean z)
          (EuclideanSpace.basisFun (Fin (n+k)) ℝ i)) •
        MixedNativeJointPhysicalRows.physicalRow
          𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (Obs z.1) z.2 i
  else 0
local notation "Raw"=>raw 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
  P hAs θ v b hvb Z htarget hstop F hF k

/-- The complete uncut scalar noise retains the newest actual factor
and FULL mixed first-defect correction. Its finite-depth heat weight is
kept outside the normalized physical residual. -/
def noise (z:CutoffWordHistories.History Unit k×Ω):ℝ:=W z.1*
  MixedJointPastExpectedLevel.noiseVersion
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (NL (pastParameter z.2)) z.1 z.2
local notation "Noise"=>noise 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
  P hAs θ v b hvb Z htarget hstop F hF k

/-- Every history/current section is eventually EXACTLY the uncut raw
kernel, not merely a fixed-test or fixed-reference approximation. -/
theorem raw_eventually_eq (z:CutoffWordHistories.History Unit k×(ℝ≥0×Ω)):
    ∃η:ℝ,0<η ∧ ∀(δ:ℝ)(hδ:0<δ),δ<η→Cut δ hδ z=Raw z:=by
  obtain ⟨η,hη,heq⟩:=CutoffUncutComparison.eventually_test_eq (Base (Held z.2)) k z.1
  refine ⟨η,hη,?_⟩
  intro δ hδ hd
  have hobs(p:Inputs):(L δ hδ p 0 k).observations.observations z.1=(Carrier p).observations.observations z.1:=
    CutoffCarriers.observations_eq (Base p) hδ zero_lt_one k z.1
  have htime(p:Inputs):(L δ hδ p 0 k).terminal z.1=(Carrier p).terminal z.1:=
    CutoffCarriers.terminal_eq (Base p) hδ zero_lt_one k z.1
  have hmean:MixedCanonicalGradientKernel.mean
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P hAs θ v b hvb Z htarget hstop F hF δ hδ 0 k z=Mean z:=by
    unfold MixedCanonicalGradientKernel.mean
    rw [hobs]
    rfl
  have hb:GaussianItoTest.backward ((L δ hδ (Held z.2) 0 k).window z.1)
      ((L δ hδ (Held z.2) 0 k).test z.1) (z.2.1:ℝ)=
        GaussianItoTest.backward ((Carrier (Held z.2)).window z.1)
          (UncutSmoothWords.test (Base (Held z.2)) k z.1) (z.2.1:ℝ):=by
    change GaussianSmooth.average (ProbabilityTheory.multivariateGaussian 0
      (WordRecursion.covariance _ ((L δ hδ (Held z.2) 0 k).observations.observations z.1)
        (ClippedCovariance.clip (v:ℝ) ((L δ hδ (Held z.2) 0 k).terminal z.1) (z.2.1:ℝ))
        ((L δ hδ (Held z.2) 0 k).terminal z.1))) ((L δ hδ (Held z.2) 0 k).test z.1)=_
    have ht:(L δ hδ (Held z.2) 0 k).test z.1=UncutSmoothWords.test (Base (Held z.2)) k z.1:=heq δ hδ hd
    rw [hobs,htime,ht]
    rfl
  dsimp only
  rw [MixedCanonicalGradientKernel.raw,raw,hobs,htime,hmean,hb]

/-- The scalar physical residual has the same pointwise eventual
identity; the original mixed bracket is preserved by exact test scaling. -/
theorem noise_eventually_eq (z:CutoffWordHistories.History Unit k×Ω):
    ∃η:ℝ,0<η ∧ ∀(δ:ℝ)(hδ:0<δ),δ<η→
      MixedJointPastExpectedLevel.noiseVersion
        𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
        (L δ hδ (pastParameter z.2) 0 k) z.1 z.2=Noise z:=by
  obtain ⟨η,hη,heq⟩:=CutoffUncutComparison.eventually_test_eq (Base (pastParameter z.2)) k z.1
  refine ⟨η,hη,?_⟩
  intro δ hδ hd
  have hn:=MixedNoiseTestScaling.noise_smul
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    (L δ hδ (pastParameter z.2) 0 k) (NL (pastParameter z.2))
    (UncutSmoothWords.weight (Base (pastParameter z.2)) k z.1) z.1 z.2
    (CutoffCarriers.observations_eq (Base (pastParameter z.2)) hδ zero_lt_one k z.1)
    (CutoffCarriers.terminal_eq (Base (pastParameter z.2)) hδ zero_lt_one k z.1)
    (by
      have ht:(L δ hδ (pastParameter z.2) 0 k).test z.1=UncutSmoothWords.test (Base (pastParameter z.2)) k z.1:=heq δ hδ hd
      rw [ht,UncutSmoothWords.test_eq_weight_normalized];rfl)
  change MixedJointPastExpectedLevel.noiseVersion
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      (L δ hδ (pastParameter z.2) 0 k) z.1 z.2=
      UncutSmoothWords.weight (Base (pastParameter z.2)) k z.1*
        MixedJointPastExpectedLevel.noiseVersion
          𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (NL (pastParameter z.2)) z.1 z.2 at hn
  dsimp only [noise]
  rw [←ControlledReferenceUncutBounds.weight_eq P (fun z=>κ+aV z) hAs Λ θ v b hvb
    Z htarget hstop F hF (pastParameter z.2) (0,0) k z.1]
  exact hn


/-- The cutoff only restricts the exact complete uncut physical noise.
Its whole mixed bracket correction scales with the same active test. -/
theorem noise_cutoff_eq (δ:ℝ)(hδ:0<δ)(z:CutoffWordHistories.History Unit k×Ω):
    MixedJointPastExpectedLevel.noiseVersion
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      (L δ hδ (pastParameter z.2) 0 k) z.1 z.2=
    if CutoffUncutComparison.Active (Base (pastParameter z.2)) δ k z.1 then Noise z else 0:=by
  classical
  let a:=CutoffUncutComparison.Active (Base (pastParameter z.2)) δ k z.1
  let w:ℝ:=if a then UncutSmoothWords.weight (Base (pastParameter z.2)) k z.1 else 0
  have ht:(L δ hδ (pastParameter z.2) 0 k).test z.1=
      w • (NL (pastParameter z.2)).test z.1:=by
    have hh:(L δ hδ (pastParameter z.2) 0 k).test z.1=
        if a then UncutSmoothWords.test (Base (pastParameter z.2)) k z.1 else 0:=
      CutoffUncutComparison.test_eq_active (Base (pastParameter z.2)) hδ k z.1
    rw [hh]
    by_cases ha:a
    · simp only [ha,ite_true,w]
      rw [UncutSmoothWords.test_eq_weight_normalized]
      rfl
    · simp only [ha,ite_false,w,zero_smul]
  have hn:=MixedNoiseTestScaling.noise_smul
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    (L δ hδ (pastParameter z.2) 0 k) (NL (pastParameter z.2)) w z.1 z.2
    (CutoffCarriers.observations_eq (Base (pastParameter z.2)) hδ zero_lt_one k z.1)
    (CutoffCarriers.terminal_eq (Base (pastParameter z.2)) hδ zero_lt_one k z.1) ht
  change MixedJointPastExpectedLevel.noiseVersion
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      (L δ hδ (pastParameter z.2) 0 k) z.1 z.2=
      w*MixedJointPastExpectedLevel.noiseVersion
        𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (NL (pastParameter z.2)) z.1 z.2 at hn
  rw [hn]
  by_cases ha:a
  · dsimp only [a] at ha
    simp only [w,a,ha,ite_true]
    dsimp only [noise]
    rw [ControlledReferenceUncutBounds.weight_eq P (fun z=>κ+aV z) hAs Λ θ v b hvb
      Z htarget hstop F hF (pastParameter z.2) (0,0) k z.1]
  · dsimp only [a] at ha
    simp only [w,a,ha,ite_false,zero_mul]

/-- An integrable uncut history weight, independent of the actual past,
controls every cutoff noise and its entire uncut limit. -/
theorem noise_bound (hΛ:0≤Λ):∃C:ℝ,0≤C ∧
    (∀z,‖Noise z‖≤C*W z.1) ∧ ∀(δ:ℝ)(hδ:0<δ)(z:CutoffWordHistories.History Unit k×Ω),
      ‖MixedJointPastExpectedLevel.noiseVersion
        𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
        (L δ hδ (pastParameter z.2) 0 k) z.1 z.2‖≤C*W z.1:=by
  obtain ⟨C,hC,hCb⟩:=ControlledNormalizedNoiseBounds.uniform_piece_bounds
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P hAs θ v b hvb Z htarget hstop F hF hΛ k
  have hb(z:CutoffWordHistories.History Unit k×Ω):‖Noise z‖≤C*W z.1:=by
    rw [noise,norm_mul,Real.norm_eq_abs,abs_of_nonneg (UncutSmoothWords.weight_nonneg _ _ _)]
    exact (mul_le_mul_of_nonneg_left (hCb (pastParameter z.2) z.1 z.2).2.2.2.2
      (UncutSmoothWords.weight_nonneg _ _ _)).trans_eq (mul_comm _ _)
  refine ⟨C,hC,hb,fun δ hδ z=>?_⟩
  rw [noise_cutoff_eq 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P hAs θ v b hvb Z htarget hstop F hF k δ hδ z]
  split_ifs
  · exact hb z
  · simpa only [norm_zero] using mul_nonneg hC (UncutSmoothWords.weight_nonneg _ _ _)

end SHE.MixedCanonicalUncutGradientKernel
