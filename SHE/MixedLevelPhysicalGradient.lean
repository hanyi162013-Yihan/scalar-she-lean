module

public import SHE.MixedLevelOriginalAverage
public import SHE.MixedCanonicalGradientKernel
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

namespace SHE.MixedLevelPhysicalGradient
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

/-- The actual positive-age physical joint current associated with a
history-dependent finite observation list. -/
def mean(z:P×(ℝ≥0×Ω)):WordRecursion.State n:=WithLp.toLp 2 (fun i=>
  PhysicalProfile.physicalHeatMean (embed (S.first z.2.1 z.2.2))
    ((L.observations.observations z.1 i).target-(z.2.1:ℝ),(L.observations.observations z.1 i).center)+
  Real.exp (-Λ*((L.observations.observations z.1 i).stop-(z.2.1:ℝ)))*
    PhysicalProfile.physicalHeatMean (embed (S.second z.2.1 z.2.2-S.first z.2.1 z.2.2))
      ((L.observations.observations z.1 i).target-(z.2.1:ℝ),(L.observations.observations z.1 i).center))
local notation "Mean"=>mean 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L

/-- Literal physical scalar gradient input, before its original J
integral. Original stop and target are retained separately. -/
def raw(z:P×(ℝ≥0×Ω)):Both RealHaarInput:=
  if R.base<(z.2.1:ℝ) ∧ (z.2.1:ℝ)<L.terminal z.1 then
    ∑i:Fin n,(fderiv ℝ (GaussianItoTest.backward (L.window z.1) (L.test z.1) (z.2.1:ℝ))
      (Mean z) (EuclideanSpace.basisFun (Fin n) ℝ i)) •
        MixedNativeJointPhysicalRows.physicalRow
          𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (L.observations.observations z.1) z.2 i
  else 0
local notation "Raw"=>raw 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L

theorem mean_predictable:
    @Measurable (P×(ℝ≥0×Ω)) (WordRecursion.State n)
      ((inferInstance:MeasurableSpace P).prod 𝓕.predictable) inferInstance Mean:=by
  letI:MeasurableSpace (ℝ≥0×Ω):=𝓕.predictable
  have hU:=embed.continuous.measurable.comp S.first_predictable.measurable
  have hD:=embed.continuous.measurable.comp (S.second_predictable.sub S.first_predictable).measurable
  have hq:Measurable (fun z:P×(ℝ≥0×Ω)=>(z.2.1:ℝ)):=
    (PredictableClock.real_time_measurable 𝓕).comp measurable_snd
  apply (WithLp.measurable_toLp 2 (Fin n→ℝ)).comp
  apply Measurable.of_eval
  intro i
  have hT:=(L.observations.target_measurable i).comp (measurable_fst : Measurable (Prod.fst:P×(ℝ≥0×Ω)→_))
  have hx:=(L.observations.center_measurable i).comp (measurable_fst : Measurable (Prod.fst:P×(ℝ≥0×Ω)→_))
  have hσ:=(L.observations.stop_measurable i).comp (measurable_fst : Measurable (Prod.fst:P×(ℝ≥0×Ω)→_))
  have hmU:=PhysicalProfile.physicalHeatMean_joint_measurable.comp
    ((hU.comp measurable_snd).prodMk ((hT.sub hq).prodMk hx))
  have hmD:=PhysicalProfile.physicalHeatMean_joint_measurable.comp
    ((hD.comp measurable_snd).prodMk ((hT.sub hq).prodMk hx))
  exact hmU.add (((hσ.sub hq).const_mul (-Λ)).exp.mul hmD)

/-- Joint original-history × predictable measurability, including the
literal moving finite Gaussian gradient and physical common-Haar rows. -/
theorem raw_predictable:
    @Measurable (P×(ℝ≥0×Ω)) (Both RealHaarInput)
      ((inferInstance:MeasurableSpace P).prod 𝓕.predictable) inferInstance Raw:=by
  letI:MeasurableSpace (ℝ≥0×Ω):=𝓕.predictable
  have hq:Measurable (fun z:P×(ℝ≥0×Ω)=>(z.2.1:ℝ)):=
    (PredictableClock.real_time_measurable 𝓕).comp measurable_snd
  have hd:=MeasurableDerivatives.fderiv_measurable (CutoffWordAnalytic.backward_measurable L)
    (fun q:P×ℝ=>((CutoffWordAnalytic.backward_uniform L).smooth q).differentiable (by simp))
  have hmap:Measurable (fun z:P×(ℝ≥0×Ω)=>((z.1,(z.2.1:ℝ)),Mean z)):=
    (measurable_fst.prodMk hq).prodMk
      (mean_predictable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L)
  have hgrad:=hd.comp hmap
  have hrow(i:Fin n):Measurable (fun z:P×(ℝ≥0×Ω)=>
      MixedNativeJointPhysicalRows.physicalRow
        𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (L.observations.observations z.1) z.2 i):=by
    have hT:=(L.observations.target_measurable i).comp (measurable_fst : Measurable (Prod.fst:P×(ℝ≥0×Ω)→_))
    have hx:=(L.observations.center_measurable i).comp (measurable_fst : Measurable (Prod.fst:P×(ℝ≥0×Ω)→_))
    have hσ:=(L.observations.stop_measurable i).comp (measurable_fst : Measurable (Prod.fst:P×(ℝ≥0×Ω)→_))
    have h0:=NativePhysicalRowFields.row_measurable_comp hκ
      (measurable_const (a:=AdditiveHaarForcing.constantField κ hκ)) hT hq hx
    have hu:=NativePhysicalRowFields.row_measurable_comp hell
      (S.first_coefficient.measurable.comp measurable_snd) hT hq hx
    have hv:=NativePhysicalRowFields.row_measurable_comp hell
      (S.second_coefficient.measurable.comp measurable_snd) hT hq hx
    exact (WithLp.prod_continuous_toLp 2 RealHaarInput RealHaarInput).measurable.comp
      (h0.prodMk (hv.add (((measurable_const (a:=(1:ℝ))).sub ((hσ.sub hq).const_mul (-Λ)).exp).smul (hu.sub hv))))
  have hs:Measurable (fun z:P×(ℝ≥0×Ω)=>∑i:Fin n,
      (fderiv ℝ (GaussianItoTest.backward (L.window z.1) (L.test z.1) (z.2.1:ℝ))
        (Mean z) (EuclideanSpace.basisFun (Fin n) ℝ i)) •
          MixedNativeJointPhysicalRows.physicalRow
            𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (L.observations.observations z.1) z.2 i):=
    Finset.measurable_fun_sum _ (fun i _=>
      ((ContinuousLinearMap.measurable_apply (EuclideanSpace.basisFun (Fin n) ℝ i)).comp hgrad).smul (hrow i))
  exact hs.ite ((measurableSet_lt measurable_const hq).inter
    (measurableSet_lt hq (L.terminal_measurable.comp measurable_fst))) measurable_const

end SHE.MixedLevelPhysicalGradient
