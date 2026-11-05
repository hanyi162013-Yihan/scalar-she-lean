module

public import SHE.MixedLevelOriginalAverage
public import SHE.MixedLevelPhysicalGradient
public import SHE.FiniteItoPastNoise
public import SHE.TerminalItoRawAverage
public import SHE.RootHeatGradientContinuity
public import SHE.MixedHeatNoiseL2Limit
public import SHE.RootMixedNoiseL2Limit
public import SHE.TerminalItoClosedLimit
public import SHE.TerminalItoAverageWitness
public import SHE.MixedJointIntegratedLevel
public import SHE.MixedNativeJointHistory
public import SHE.JointInsertionIntegrability
public import SHE.JointWordDefect

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option quotPrecheck false
noncomputable section

namespace SHE.MixedLevelPhysicalInput
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
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩
local instance : MeasurableSpace RealHaarInput := borel _
local instance : BorelSpace RealHaarInput := ⟨rfl⟩
local instance : MeasurableSpace (Both RealHaarInput) := borel _
local instance : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω P : Type*} [MeasurableSpace Ω] [MeasurableSpace P]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {aU aV : ℝ→ℝ} (haU : Measurable aU) (haV : Measurable aV) {ell M : ℝ}
variable (hell : 0<ell) (hbU : ∀ z,ell≤aU z ∧ aU z≤M) (hbV : ∀ z,ell≤aV z ∧ aV z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)
variable {R : ReferenceData} {n : ℕ} (L : Level R P n)
local notation "dU" => MixedNativeJointHistory.firstData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
local notation "dV" => MixedNativeJointHistory.secondData 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
local notation "U" => (dU).physicalState
local notation "V" => (dV).physicalState
local notation "XU" => (dU).physicalField
local notation "XV" => (dV).physicalField

local notation "Mean"=>MixedLevelPhysicalGradient.mean
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L
local notation "Raw"=>MixedLevelPhysicalGradient.raw
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L

theorem admissible_gradient(p:P):FiniteItoNoise.AdmissibleGradient
    (GaussianItoTest.backward (L.window p) (L.test p)):=by
  obtain ⟨C₀,hC₀,hB₀⟩:=L.test_uniform.norm_bound
  obtain ⟨C,hC,hB⟩:=L.test_uniform.fderiv.norm_bound
  refine ⟨BackwardRegularity.gaussian_gradient_joint_continuous _ (L.window p).continuous_path
    ((L.test_uniform.smooth p).of_le (by simp)) (hB₀ p) (hB p),C,?_⟩
  intro t z
  exact BackwardRegularity.gaussian_state_gradient_bound _
    ((L.test_uniform.smooth p).of_le (by simp)) (hB₀ p) (hB p) z

variable (J:StandardTerminalIto (C:=Both RealHaarInput) (E:=ℝ) 𝓕 μ H)
variable (hIJ₀:StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁:StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))

include hIJ₀ hIJ₁ in
/-- The ordinary physical finite-Ito formula identifies its original
input with the literal native gradient row before any history average. -/
theorem original_section_input (hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (hJ:StandardFiniteIto.Universal 𝓕 μ H J)(hΛ:0≤Λ)
    (hA:R.totalVariance=(fun z=>κ+aV z))(hh:R.horizon≤(H:ℝ))
    {η:ℝ}(hη:0<η)(hgap:∀p i,η≤(L.observations.observations p i).target-L.terminal p)(p:P):
    ∃input:Process (E:=Both RealHaarInput) 𝓕 μ H,
      input=ᵐ[energyMeasure μ H] (fun z=>Raw (p,z)) ∧
      J.integral input=ᵐ[μ] MixedJointIntegratedLevel.noiseVersion
        𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L p:=by
  let c:ℝ≥0:=(L.terminal p).toNNReal
  let v:ℝ≥0:=R.base.toNNReal
  have hc:(c:ℝ)=L.terminal p:=Real.coe_toNNReal _ (R.base_nonneg.trans (L.terminal_base p))
  have hv:(v:ℝ)=R.base:=Real.coe_toNNReal _ R.base_nonneg
  have hcH:c≤H:=by exact_mod_cast (show (c:ℝ)≤H by rw [hc];exact (L.terminal_horizon p).trans hh)
  have hs:∀i,(c:ℝ)<(L.observations.observations p i).target:=by
    intro i;rw [hc];linarith [hgap p i]
  have hvc:v≤c:=by exact_mod_cast (show (v:ℝ)≤(c:ℝ) by rw [hv,hc];exact L.terminal_base p)
  let Y:=MixedJointNamedIto.path 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (L.observations.observations p) c
  let predY:=MixedNativeJointObservations.predictable_value
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁
    (L.observations.observations p) c hs hnull hΛ hcH
  let Rows:=MixedNativeJointObservations.rows
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (L.observations.observations p) c hs hΛ
  let G:=GaussianItoTest.backward (L.window p) (L.test p)
  have hG:=admissible_gradient L p
  let GP:=FiniteItoNoise.gradientProcess 𝓕 μ H Y predY Rows G hG
  let input:=PastItoInputs.post 𝓕 μ H v (StoppedItoInputs.stop 𝓕 μ H (c:ℝ) GP)
  refine ⟨input,?_,?_⟩
  · filter_upwards [PastItoInputs.post_ae 𝓕 μ H v (StoppedItoInputs.stop 𝓕 μ H (c:ℝ) GP),
      StoppedItoInputs.stop_ae 𝓕 μ H (c:ℝ) GP,
      FiniteItoNoise.gradientProcess_ae 𝓕 μ H Y predY Rows G hG,
      MixedNativeJointPhysicalRows.rows_ae 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
        (L.observations.observations p) hΛ c hs] with z hp hstop hgrad hrows
    change input z=_
    rw [hp]
    by_cases hvz:v<z.1
    · rw [if_pos hvz,hstop]
      have hvzR:R.base<(z.1:ℝ):=by rw [←hv];exact_mod_cast hvz
      by_cases hzc:z.1<c
      · have hzcR:(z.1:ℝ)<L.terminal p:=by rw [←hc];exact_mod_cast hzc
        rw [Set.indicator_of_mem (show z∈StoppedItoInputs.before (Ω:=Ω) (c:ℝ) from by exact_mod_cast hzc),hgrad]
        have hY:Y z=Mean (p,z):=by
          apply PiLp.ext
          intro i
          have ht:(z.1:ℝ)<(L.observations.observations p i).target:=
            (show (z.1:ℝ)<(c:ℝ) by exact_mod_cast hzc).trans (hs i)
          have he:=MixedNativeJointObservations.value_eq_physical
            𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
            (L.observations.observations p) c hs z.1 hzc.le z.2 i
          rw [functional_physical (sub_pos.mpr ht),functional_physical (sub_pos.mpr ht)] at he
          simpa only [Y,MixedJointNamedIto.path,Function.uncurry,MixedLevelPhysicalGradient.mean,WithLp.ofLp_toLp] using he
        simp only [MixedLevelPhysicalGradient.raw,ite_eq_left (show R.base<(z.1:ℝ) ∧ (z.1:ℝ)<L.terminal p from ⟨hvzR,hzcR⟩),
          FiniteItoNoise.gradientRow,FiniteItoNoise.gradientCoefficient,hY]
        exact Finset.sum_congr rfl (fun i _=>by rw [hrows hzc i])
      · have hn:¬(z.1:ℝ)<L.terminal p:=by rw [←hc];exact_mod_cast hzc
        rw [Set.indicator_of_notMem (show z∉StoppedItoInputs.before (Ω:=Ω) (c:ℝ) from by exact_mod_cast hzc)]
        simp only [MixedLevelPhysicalGradient.raw,if_neg (show ¬(R.base<(z.1:ℝ) ∧ (z.1:ℝ)<L.terminal p) from fun hz=>hn hz.2)]
    · have hn:¬R.base<(z.1:ℝ):=by rw [←hv];exact_mod_cast hvz
      rw [if_neg hvz]
      simp only [MixedLevelPhysicalGradient.raw,if_neg (show ¬(R.base<(z.1:ℝ) ∧ (z.1:ℝ)<L.terminal p) from fun hz=>hn hz.1)]
  · have hn:=MixedNamedLevelNoise.noise_eq_original
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L J hIJ₀ hIJ₁
      hnull hJ hΛ hA hh hη hgap p
    have he:MixedJointNamedIto.scalarNoise
        𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ hnull hΛ
        (L.observations.observations p) c hs hcH v G=J.integral input:=
      FiniteItoPastNoise.noise_eq_post 𝓕 μ H Y predY Rows J v c hvc G hG
    change MixedJointIntegratedLevel.noiseVersion
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L p=ᵐ[μ] _ at hn
    rw [he] at hn
    exact hn.symm

end SHE.MixedLevelPhysicalInput
