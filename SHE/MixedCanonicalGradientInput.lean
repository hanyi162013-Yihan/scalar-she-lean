module

public import SHE.MixedNamedLevelPostWitness
public import SHE.MixedNativeGradientColumns
public import SHE.PastParameterOriginalIto
public import SHE.TerminalItoAverageWitness

public import SHE.ControlledRecursiveGradientRows
public import SHE.PastParameterItoIdentity
public import SHE.FiniteItoGradientMajorant
public import SHE.MixedNamedLevelNoise
public import SHE.MixedNativeRandomReferenceStep
public import SHE.ControlledReferenceRecursiveResidualBounds
public import SHE.ControlledReferenceRecursiveResidualContinuity
public import SHE.PastParameterHistoryExpectation

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option quotPrecheck false

namespace SHE.MixedCanonicalGradientInput
open MeasureTheory Set PredictableL2 NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation CutoffWordLevel
open GaussianTaylorAverage JointWordAnalytic
open GaussianItoTest
open scoped ENNReal NNReal
local instance : Fact (0<(1:ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance : MeasurableSpace CircleHeat.CircleL2 := borel _
local instance : BorelSpace CircleHeat.CircleL2 := ⟨rfl⟩
local instance : MeasurableSpace CircleL2 := borel _
local instance : BorelSpace CircleL2 := ⟨rfl⟩
local instance mixedCanonicalGradientInput_circleSecondCountable : SecondCountableTopology StoppedFourier.CircleL2 :=
  (_root_.fourierBasis (T:=2*Real.pi)).repr.toHomeomorph.secondCountableTopology
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩
local instance : MeasurableSpace RealHaarInput := borel _
local instance : BorelSpace RealHaarInput := ⟨rfl⟩
local instance : MeasurableSpace (Both RealHaarInput) := borel _
local instance : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
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
variable (δ : ℝ) (hδ : 0<δ)
local notation "L" => ControlledReferenceRecursiveBounds.level P (fun z => κ+aV z) hAs Λ θ v b hvb Z htarget hstop F hF δ hδ

local notation "dU" => MixedNativeJointHistory.firstData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
local notation "dV" => MixedNativeJointHistory.secondData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
local notation "U" => (dU).physicalState
local notation "V" => (dV).physicalState
local notation "XU" => (dU).physicalField
local notation "XV" => (dV).physicalField

variable (hsmall : ProfileStability.memoryConstant P.lower P.holder P.exponent*
  ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)

local notation "pastParameter" => MixedNativeRandomReferenceStep.randomParameter 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v
local instance mixedCanonicalGradientInput_inputSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedCanonicalGradientInput_inputBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedCanonicalGradientInput_bothSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedCanonicalGradientInput_bothBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable (J : StandardTerminalIto (C := Both RealHaarInput) (E := ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))

variable (hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ) (hΛ:0≤Λ) (hbH:b≤H)
variable (ε:ℝ≥0)(hε:0<(ε:ℝ))(hgap:∀i,(ε:ℝ)≤(Z i).target-(b:ℝ))
variable (k:ℕ)(h:CutoffWordHistories.History Unit k)
local notation "Z₀" => (L (0,0) ε k).observations.observations h
local notation "c" => ((L (0,0) ε k).terminal h).toNNReal

local notation "cEq"=>(Real.coe_toNNReal ((L (0,0) ε k).terminal h)
  (v.2.trans ((L (0,0) ε k).terminal_base h)))
local notation "cH"=>(show c≤H from by
  exact_mod_cast (show (c:ℝ)≤H by rw [cEq];exact ((L (0,0) ε k).terminal_horizon h).trans (by exact_mod_cast hbH)))
local notation "Gap"=>(show ∀i,(c:ℝ)<(Z₀ i).target from by
  have hg:=HeatCutoffHistories.iterate_gap
    (ControlledReferenceLevel.level P (fun z=>κ+aV z) hAs Λ θ v b hvb Z htarget hstop F hF (0,0))
    hδ ε.2 (fun _=>hgap) k
  intro i
  rw [cEq]
  have hi:=hg h i
  change (ε:ℝ)≤(Z₀ i).target-(L (0,0) ε k).terminal h at hi
  linarith)

local notation "Y"=>MixedJointNamedIto.path
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z₀ c
local notation "Rows"=>MixedNativeJointObservations.rows
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z₀ c Gap hΛ
local notation "predY"=>MixedNativeJointObservations.predictable_value
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ Z₀ c Gap hnull hΛ cH
local notation "G"=>(fun p:Inputs=>GaussianItoTest.backward ((L p ε k).window h) ((L p ε k).test h))

/-- The literal stopped scalar gradient row with the actual joint
observations and their original two physical noise channels. -/
def raw (p:Inputs)(z:ℝ≥0×Ω):Both RealHaarInput:=
  (StoppedItoInputs.before (c:ℝ)).indicator
    (FiniteItoNoise.gradientRow 𝓕 μ H Y Rows (G p)) z
local notation "Raw"=>raw 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
  P hAs θ v b hvb Z htarget hstop F hF δ hδ hΛ ε hε hgap k h

include hsmall in
theorem raw_parameter_continuous (z:ℝ≥0×Ω):Continuous (fun p:Inputs=>Raw p z):=by
  by_cases hz:z∈StoppedItoInputs.before (Ω:=Ω) (c:ℝ)
  · simp only [raw,Set.indicator_of_mem hz]
    have hg:=ControlledRecursiveGradientRows.continuous_gradient P (fun z=>κ+aV z) hAs Λ θ v b hvb
      Z htarget hstop F hF δ hδ hsmall hΛ ε k h (z.1:ℝ)
    have hc:=hg.comp (continuous_id.prodMk (continuous_const (y:=Y z)))
    exact continuous_finsetSum _ (fun i _=>(hc.clm_apply (continuous_const
      (y:=EuclideanSpace.basisFun (Fin (n+k)) ℝ i))).smul continuous_const)
  · simp only [raw,Set.indicator_of_notMem hz]
    exact continuous_const

include hIJ₀ hIJ₁ hnull hbH in
theorem raw_predictable (p:Inputs):StronglyMeasurable[𝓕.predictable] (Raw p):=by
  have hp:=ControlledRecursiveGradientRows.admissible_gradient P (fun z=>κ+aV z) hAs Λ θ v b hvb
    Z htarget hstop F hF δ hδ ε k h p
  exact (FiniteItoNoise.gradientRow_predictable 𝓕 μ H Y predY Rows hp).indicator
    (StoppedItoInputs.before_measurable 𝓕 (c:ℝ))

include hIJ₀ hIJ₁ hnull hbH hsmall in
/-- Genuine past-parameter × predictable measurability, rather than
ambient product Borel measurability, of the full physical gradient row. -/
theorem raw_joint_predictable:
    @Measurable (Inputs×(ℝ≥0×Ω)) (Both RealHaarInput)
      ((inferInstance:MeasurableSpace Inputs).prod 𝓕.predictable) inferInstance
      (fun z=>Raw z.1 z.2):=by
  letI:MeasurableSpace (ℝ≥0×Ω):=𝓕.predictable
  exact measurable_uncurry_of_continuous_of_measurable
    (raw_parameter_continuous 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P hAs θ v b hvb Z htarget hstop F hF δ hδ hsmall hΛ ε hε hgap k h)
    (fun p=>(raw_predictable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      P hAs θ v b hvb Z htarget hstop F hF δ hδ J hIJ₀ hIJ₁ hnull hΛ hbH ε hε hgap k h p).measurable)


include hIJ₀ hIJ₁ hnull hΛ in
private theorem namedNoise_congr {m:ℕ} {Z₁ Z₂:Fin m→WordRecursion.Observation}
    {c₁ c₂:ℝ≥0} (hZ:Z₁=Z₂)(hc:c₁=c₂)
    (hgap₁:∀i,(c₁:ℝ)<(Z₁ i).target)(hgap₂:∀i,(c₂:ℝ)<(Z₂ i).target)
    (hc₁:c₁≤H)(hc₂:c₂≤H)(G₀:ℝ→WordRecursion.State m→ℝ):
    MixedJointNamedIto.scalarNoise
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ hnull hΛ Z₁ c₁ hgap₁ hc₁ v G₀=
    MixedJointNamedIto.scalarNoise
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ hnull hΛ Z₂ c₂ hgap₂ hc₂ v G₀:=by
  subst Z₂
  subst c₂
  rfl

include hIJ₀ hIJ₁ hnull hbH hsmall in
/-- At every actual finite recursive history the original scalar noise
has the literal random-reference physical gradient row as predictable
input. Past randomness is selected using ordinary locality and strong
predictable-L2 approximation, not a new reference-Ito premise. -/
theorem exists_explicit_input (hJ:StandardFiniteIto.Universal 𝓕 μ H J)
    (hlocal:StandardTerminalPastLocality J):
    ∃input:Process (E:=Both RealHaarInput) 𝓕 μ H,
      input=ᵐ[energyMeasure μ H] (fun z=>if v<z.1 then Raw (pastParameter z.2) z else 0) ∧
      J.integral input=ᵐ[μ] fun ω=>MixedJointPastExpectedLevel.noiseVersion
        𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (L (pastParameter ω) ε k) h ω:=by
  obtain ⟨C,hC,hCb⟩:=ControlledRecursiveGradientRows.gradient_bound P (fun z=>κ+aV z) hAs Λ θ v b hvb
    Z htarget hstop F hF δ hδ k
  let B:=FiniteItoGradientMajorant.process 𝓕 μ H Rows C
  have hB:∀ᵐz∂(energyMeasure μ H).trim (predictable_le_product 𝓕),∀p:Inputs,‖Raw p z‖≤‖B z‖:=by
    have hm:=FiniteItoGradientMajorant.family_bound 𝓕 μ H Rows C Y G hC (fun p t z=>hCb p ε h t z)
    filter_upwards [hm] with z hz p
    by_cases hzc:z∈StoppedItoInputs.before (Ω:=Ω) (c:ℝ)
    · simpa only [raw,Set.indicator_of_mem hzc] using hz p
    · simp only [raw,Set.indicator_of_notMem hzc,norm_zero]
      exact norm_nonneg _
  have hg:=raw_joint_predictable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P hAs θ v b hvb Z htarget hstop F hF δ hδ hsmall J hIJ₀ hIJ₁ hnull hΛ hbH ε hε hgap k h
  let inp:=fun {u:Ω→Inputs} (hu:Measurable[𝓕 v] u)=>
    PastParameterItoInput.input 𝓕 μ H v Raw hg B hB (0,0) hu
  let K:=fun (p:Inputs)(ω:Ω)=>MixedJointPastExpectedLevel.noiseVersion
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (L p ε k) h ω
  have hconst(p:Inputs):K p=ᵐ[μ] J.integral (inp (measurable_const (a:=p))):=by
    have hGp:=ControlledRecursiveGradientRows.admissible_gradient P (fun z=>κ+aV z) hAs Λ θ v b hvb
      Z htarget hstop F hF δ hδ ε k h p
    let GP:=FiniteItoNoise.gradientProcess 𝓕 μ H Y predY Rows (G p) hGp
    have heq:inp (measurable_const (a:=p))=
        PastItoInputs.post 𝓕 μ H v (StoppedItoInputs.stop 𝓕 μ H (c:ℝ) GP):=by
      apply PastItoAlgebra.eq_of_ambient_ae
      filter_upwards [PastParameterItoInput.input_ae 𝓕 μ H v Raw hg B hB (0,0) (measurable_const (a:=p)),
        PastItoInputs.post_ae 𝓕 μ H v (StoppedItoInputs.stop 𝓕 μ H (c:ℝ) GP),
        StoppedItoInputs.stop_ae 𝓕 μ H (c:ℝ) GP,
        FiniteItoNoise.gradientProcess_ae 𝓕 μ H Y predY Rows (G p) hGp] with z hi hp hs hgp
      rw [hi,hp]
      by_cases hvz:v<z.1
      · simp only [PastParameterItoInput.raw,hvz,↓reduceIte]
        rw [hs]
        by_cases hzc:z∈StoppedItoInputs.before (Ω:=Ω) (c:ℝ)
        · simpa only [raw,Set.indicator_of_mem hzc] using hgp.symm
        · simp only [raw,Set.indicator_of_notMem hzc]
      · simp only [PastParameterItoInput.raw,hvz,↓reduceIte]
    have hvT:v≤c:=by
      exact_mod_cast (show (v:ℝ)≤(c:ℝ) by rw [cEq];exact (L (0,0) ε k).terminal_base h)
    have hn:=MixedNamedLevelNoise.noise_eq_original
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (L p ε k) J hIJ₀ hIJ₁
      hnull hJ hΛ rfl (by exact_mod_cast hbH) hε
      (HeatCutoffHistories.iterate_gap
        (ControlledReferenceLevel.level P (fun z=>κ+aV z) hAs Λ θ v b hvb Z htarget hstop F hF p)
        hδ ε.2 (fun _=>hgap) k) h
    dsimp only at hn
    have ho:=ControlledReferenceRecursiveBounds.observations_eq P (fun z=>κ+aV z) hAs Λ θ v b hvb
      Z htarget hstop F hF δ hδ p (0,0) ε k h
    have ht:=ControlledReferenceRecursiveBounds.terminal_eq P (fun z=>κ+aV z) hAs Λ θ v b hvb
      Z htarget hstop F hF δ hδ p (0,0) ε ε k h
    have hpH:((L p ε k).terminal h).toNNReal≤H:=by
      rw [ht]
      exact cH
    have hpGap:∀i,(((L p ε k).terminal h).toNNReal:ℝ)<((L p ε k).observations.observations h i).target:=by
      intro i
      rw [ho,ht]
      exact Gap i
    have hbbase:(referenceData P (fun z=>κ+aV z) hAs Λ θ v b hvb p).base.toNNReal=v:=by
      simp only [ControlledReferenceLevel.referenceData,Real.toNNReal_coe]
    simp only [hbbase] at hn
    have he:=namedNoise_congr
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v J hIJ₀ hIJ₁ hnull hΛ
      ho (congrArg Real.toNNReal ht) hpGap Gap hpH cH (G p)
    have hn':K p=ᵐ[μ] MixedJointNamedIto.scalarNoise
        𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ hnull hΛ Z₀ c Gap cH v (G p):=by
      apply hn.trans
      exact ae_of_all _ (fun ω=>congrArg (fun f:Lp ℝ 2 μ=>f ω) he)
    change K p=ᵐ[μ] FiniteItoNoise.noise 𝓕 μ H Y predY Rows J v c (G p) at hn'
    rw [heq,←FiniteItoPastNoise.noise_eq_post 𝓕 μ H Y predY Rows J v c hvT (G p) hGp]
    exact hn'

  have hu:=MixedNativeRandomReferenceStep.randomParameter_stronglyMeasurable
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v
  refine ⟨inp hu.measurable,?_,?_⟩
  · exact PastParameterItoInput.input_ae 𝓕 μ H v Raw hg B hB (0,0) hu.measurable
  · exact (PastParameterItoIdentity.diagonal_identity 𝓕 μ H v Raw hg B hB (0,0) J hlocal
      (raw_parameter_continuous 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
        P hAs θ v b hvb Z htarget hstop F hF δ hδ hsmall hΛ ε hε hgap k h)
      K hconst (ae_of_all _ (fun ω=>ControlledReferenceRecursiveResidualContinuity.continuous_residual
        𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
        P hAs θ v b hvb Z htarget hstop F hF δ hδ hsmall hΛ ε k h ω)) hu).symm


include hIJ₀ hIJ₁ hnull hbH hsmall hΛ hε hgap in
/-- The actual random-reference kth noise has SAME-J predictable input
whose every Haar coordinate is the literal native Gaussian derivative
in the full original physical column direction. -/
theorem exists_physical_columns (hJ:StandardFiniteIto.Universal 𝓕 μ H J)
    (hlocal:StandardTerminalPastLocality J):
    ∃input:Process (E:=Both RealHaarInput) 𝓕 μ H,
      (J.integral input=ᵐ[μ] fun ω=>MixedJointPastExpectedLevel.noiseVersion
        𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (L (pastParameter ω) ε k) h ω) ∧
      ∀ᵐz∂energyMeasure μ H,
        (v:ℝ)<(z.1:ℝ)→(z.1:ℝ)<(L (0,0) ε k).terminal h→∀j:HaarNode,
        NativeJointColumnDirections.left j (input z)=
          fderiv ℝ (G (pastParameter z.2) (z.1:ℝ)) (Y z)
            (PhysicalMeanRange.currentDirection (fun i=>(Z₀ i).target)
              (fun i=>NativeHeatSpan.unitCenter (Z₀ i).center) (z.1:ℝ)
              (CircleNormalization.push (globalHaarColumn j (AdditiveHaarForcing.constantField κ hκ).1))) ∧
        NativeJointColumnDirections.right j (input z)=
          fderiv ℝ (G (pastParameter z.2) (z.1:ℝ)) (Y z)
            (PhysicalMeanRange.currentDirection (fun i=>(Z₀ i).target)
                (fun i=>NativeHeatSpan.unitCenter (Z₀ i).center) (z.1:ℝ)
                (CircleNormalization.push (globalHaarColumn j
                  (ContinuousHeatMild.coefficientFunction haU hell hbU S.first z).1))+
              PhysicalMeanRange.dampedDirection (fun i=>(Z₀ i).stop) (fun i=>(Z₀ i).target)
                (fun i=>NativeHeatSpan.unitCenter (Z₀ i).center) (z.1:ℝ) Λ
                (CircleNormalization.push (globalHaarColumn j
                    (ContinuousHeatMild.coefficientFunction haV hell hbV S.second z).1)-
                  CircleNormalization.push (globalHaarColumn j
                    (ContinuousHeatMild.coefficientFunction haU hell hbU S.first z).1))):=by
  obtain ⟨input,hi,hn⟩:=exists_explicit_input
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P hAs θ v b hvb Z htarget hstop F hF δ hδ hsmall J hIJ₀ hIJ₁ hnull hΛ hbH ε hε hgap k h hJ hlocal
  refine ⟨input,hn,?_⟩
  filter_upwards [hi,MixedNativeGradientColumns.gradient_columns_ae
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S Z₀ hΛ c Gap] with z hi hz hvz hzc j
  have hzv:v<z.1:=by exact_mod_cast hvz
  have hzc':(z.1:ℝ)<(c:ℝ):=by rw [cEq];exact hzc
  have hzcn:z.1<c:=by exact_mod_cast hzc'
  have he:input z=FiniteItoNoise.gradientRow 𝓕 μ H Y Rows (G (pastParameter z.2)) z:=by
    rw [hi,if_pos hzv]
    exact Set.indicator_of_mem (show z∈StoppedItoInputs.before (Ω:=Ω) (c:ℝ) from hzc') _
  rw [he]
  exact hz hzcn Y (G (pastParameter z.2)) j

end SHE.MixedCanonicalGradientInput
