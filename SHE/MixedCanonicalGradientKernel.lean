module

public import SHE.MixedNativePhysicalRowBound
public import SHE.MixedCanonicalGradientInput
public import SHE.ControlledRecursiveGradientFields
public import SHE.MixedNativeGradientColumns
public import SHE.NativePhysicalRowFields
public import SHE.PredictablePastParameter
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
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1000000
set_option quotPrecheck false

namespace SHE.MixedCanonicalGradientKernel
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
local instance mixedCanonicalGradientKernel_circleSecondCountable : SecondCountableTopology StoppedFourier.CircleL2 :=
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
local instance mixedCanonicalGradientKernel_inputSigma : MeasurableSpace RealHaarInput := borel _
local instance mixedCanonicalGradientKernel_inputBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance mixedCanonicalGradientKernel_bothSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance mixedCanonicalGradientKernel_bothBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable (J : StandardTerminalIto (C := Both RealHaarInput) (E := ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))

variable (hnull:NullCompleteFiltration.ContainsNullSets 𝓕 μ) (hΛ:0≤Λ) (hbH:b≤H)
variable (ε:ℝ≥0)(hε:0<(ε:ℝ))(hgap:∀i,(ε:ℝ)≤(Z i).target-(b:ℝ))
variable (k:ℕ)
local notation "Obs"=>((L (0,0) ε k).observations.observations)
local notation "Terminal"=>((L (0,0) ε k).terminal)
local notation "Held"=>PredictablePastParameter.held v pastParameter (0,0)

/-- Literal positive-age current vector, retaining every original stop
and target, for the actual mixed pair. -/
def mean (z:CutoffWordHistories.History Unit k×(ℝ≥0×Ω)):WordRecursion.State (n+k):=
  WithLp.toLp 2 (fun i=>
    PhysicalProfile.physicalHeatMean (embed (S.first z.2.1 z.2.2))
      ((Obs z.1 i).target-(z.2.1:ℝ),(Obs z.1 i).center)+
    Real.exp (-Λ*((Obs z.1 i).stop-(z.2.1:ℝ)))*
      PhysicalProfile.physicalHeatMean (embed (S.second z.2.1 z.2.2-S.first z.2.1 z.2.2))
        ((Obs z.1 i).target-(z.2.1:ℝ),(Obs z.1 i).center))
local notation "Mean"=>mean 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
  P hAs θ v b hvb Z htarget hstop F hF δ hδ ε k

/-- Explicit physical gradient input BEFORE any stochastic integral,
jointly over the original finite history and predictable current time. -/
def raw (z:CutoffWordHistories.History Unit k×(ℝ≥0×Ω)):Both RealHaarInput:=
  if (v:ℝ)<(z.2.1:ℝ) ∧ (z.2.1:ℝ)<Terminal z.1 then
    ∑i:Fin (n+k),
      (fderiv ℝ (GaussianItoTest.backward ((L (Held z.2) ε k).window z.1)
        ((L (Held z.2) ε k).test z.1) (z.2.1:ℝ)) (Mean z)
          (EuclideanSpace.basisFun (Fin (n+k)) ℝ i)) •
        MixedNativeJointPhysicalRows.physicalRow
          𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (Obs z.1) z.2 i
  else 0
local notation "Raw"=>raw 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
  P hAs θ v b hvb Z htarget hstop F hF δ hδ ε k

/-- True original-history × predictable measurability of the actual
current vector; no zero-age L2 representative is evaluated here. -/
theorem mean_predictable:
    @Measurable (CutoffWordHistories.History Unit k×(ℝ≥0×Ω)) (WordRecursion.State (n+k))
      ((inferInstance:MeasurableSpace (CutoffWordHistories.History Unit k)).prod 𝓕.predictable) inferInstance Mean:=by
  letI:MeasurableSpace (ℝ≥0×Ω):=𝓕.predictable
  have hU:=embed.continuous.measurable.comp S.first_predictable.measurable
  have hD:=embed.continuous.measurable.comp (S.second_predictable.sub S.first_predictable).measurable
  have hq:Measurable (fun z:CutoffWordHistories.History Unit k×(ℝ≥0×Ω)=>(z.2.1:ℝ)):=
    (PredictableClock.real_time_measurable 𝓕).comp measurable_snd
  apply (WithLp.measurable_toLp 2 (Fin (n+k)→ℝ)).comp
  apply Measurable.of_eval
  intro i
  have hT:=((L (0,0) ε k).observations.target_measurable i).comp
    (measurable_fst : Measurable (Prod.fst:CutoffWordHistories.History Unit k×(ℝ≥0×Ω)→_))
  have hx:=((L (0,0) ε k).observations.center_measurable i).comp
    (measurable_fst : Measurable (Prod.fst:CutoffWordHistories.History Unit k×(ℝ≥0×Ω)→_))
  have hσ:=((L (0,0) ε k).observations.stop_measurable i).comp
    (measurable_fst : Measurable (Prod.fst:CutoffWordHistories.History Unit k×(ℝ≥0×Ω)→_))
  have hmU:=PhysicalProfile.physicalHeatMean_joint_measurable.comp
    ((hU.comp measurable_snd).prodMk ((hT.sub hq).prodMk hx))
  have hmD:=PhysicalProfile.physicalHeatMean_joint_measurable.comp
    ((hD.comp measurable_snd).prodMk ((hT.sub hq).prodMk hx))
  exact hmU.add (((hσ.sub hq).const_mul (-Λ)).exp.mul hmD)

section RawMeasurability
attribute [local irreducible] ControlledReferenceRecursiveBounds.level mean

include hsmall hΛ in
theorem raw_predictable:
    @Measurable (CutoffWordHistories.History Unit k×(ℝ≥0×Ω)) (Both RealHaarInput)
      ((inferInstance:MeasurableSpace (CutoffWordHistories.History Unit k)).prod 𝓕.predictable) inferInstance Raw:=by
  letI:MeasurableSpace (ℝ≥0×Ω):=𝓕.predictable
  have hq:Measurable (fun z:CutoffWordHistories.History Unit k×(ℝ≥0×Ω)=>(z.2.1:ℝ)):=
    (PredictableClock.real_time_measurable 𝓕).comp measurable_snd
  have hheld:=PredictablePastParameter.held_measurable 𝓕 v pastParameter
    (MixedNativeRandomReferenceStep.randomParameter_stronglyMeasurable
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S v).measurable (0,0)
  have hmap:Measurable (fun z:CutoffWordHistories.History Unit k×(ℝ≥0×Ω)=>
      (Held z.2,((z.1,(z.2.1:ℝ)),Mean z))):=
    (hheld.comp measurable_snd).prodMk ((measurable_fst.prodMk hq).prodMk
      (mean_predictable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
        P hAs θ v b hvb Z htarget hstop F hF δ hδ ε k))
  have hg0:=ControlledRecursiveGradientFields.gradient_joint_measurable P (fun z=>κ+aV z) hAs Λ θ v b hvb
    Z htarget hstop F hF δ hδ hsmall hΛ ε k
  have hgrad:=hg0.comp hmap
  have hrow(i:Fin (n+k)):Measurable (fun z:CutoffWordHistories.History Unit k×(ℝ≥0×Ω)=>
      MixedNativeJointPhysicalRows.physicalRow
        𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (Obs z.1) z.2 i):=by
    have hT:=((L (0,0) ε k).observations.target_measurable i).comp
      (measurable_fst : Measurable (Prod.fst:CutoffWordHistories.History Unit k×(ℝ≥0×Ω)→_))
    have hx:=((L (0,0) ε k).observations.center_measurable i).comp
      (measurable_fst : Measurable (Prod.fst:CutoffWordHistories.History Unit k×(ℝ≥0×Ω)→_))
    have hσ:=((L (0,0) ε k).observations.stop_measurable i).comp
      (measurable_fst : Measurable (Prod.fst:CutoffWordHistories.History Unit k×(ℝ≥0×Ω)→_))
    have h0:=NativePhysicalRowFields.row_measurable_comp hκ
      (measurable_const (a:=AdditiveHaarForcing.constantField κ hκ)) hT hq hx
    have hu:=NativePhysicalRowFields.row_measurable_comp hell
      (S.first_coefficient.measurable.comp measurable_snd) hT hq hx
    have hv:=NativePhysicalRowFields.row_measurable_comp hell
      (S.second_coefficient.measurable.comp measurable_snd) hT hq hx
    exact (WithLp.prod_continuous_toLp 2 RealHaarInput RealHaarInput).measurable.comp
      (h0.prodMk (hv.add (((measurable_const (a:=(1:ℝ))).sub ((hσ.sub hq).const_mul (-Λ)).exp).smul (hu.sub hv))))
  have hs:Measurable (fun z:CutoffWordHistories.History Unit k×(ℝ≥0×Ω)=>
      ∑i:Fin (n+k),
        (fderiv ℝ (GaussianItoTest.backward ((L (Held z.2) ε k).window z.1)
          ((L (Held z.2) ε k).test z.1) (z.2.1:ℝ)) (Mean z)
            (EuclideanSpace.basisFun (Fin (n+k)) ℝ i)) •
          MixedNativeJointPhysicalRows.physicalRow
            𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (Obs z.1) z.2 i):=
    Finset.measurable_fun_sum _ (fun i _=>((ContinuousLinearMap.measurable_apply (EuclideanSpace.basisFun (Fin (n+k)) ℝ i)).comp hgrad).smul (hrow i))
  exact hs.ite ((measurableSet_lt measurable_const hq).inter
    (measurableSet_lt hq (((L (0,0) ε k).terminal_measurable).comp measurable_fst))) measurable_const


end RawMeasurability

set_option backward.isDefEq.respectTransparency false

include hIJ₀ hIJ₁ hnull hbH hsmall hΛ hε hgap in
/-- Every original-history section of the jointly predictable physical
kernel is exactly the SAME-J input of the actual random-reference kth
finite noise. The Gaussian law and current are the actual ones. -/
theorem original_section_input (hJ:StandardFiniteIto.Universal 𝓕 μ H J)
    (hlocal:StandardTerminalPastLocality J)(h:CutoffWordHistories.History Unit k):
    ∃input:Process (E:=Both RealHaarInput) 𝓕 μ H,
      input=ᵐ[energyMeasure μ H] (fun q=>Raw (h,q)) ∧
      J.integral input=ᵐ[μ] fun ω=>MixedJointPastExpectedLevel.noiseVersion
        𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (L (pastParameter ω) ε k) h ω:=by
  obtain ⟨input,hi,hn⟩:=MixedCanonicalGradientInput.exists_explicit_input
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    P hAs θ v b hvb Z htarget hstop F hF δ hδ hsmall J hIJ₀ hIJ₁ hnull hΛ hbH ε hε hgap k h hJ hlocal
  let c:ℝ≥0:=(Terminal h).toNNReal
  have hcEq:(c:ℝ)=Terminal h:=Real.coe_toNNReal _ (v.2.trans ((L (0,0) ε k).terminal_base h))
  have hcGap:∀i,(c:ℝ)<(Obs h i).target:=by
    have hg:HeatCutoffHistories.Gap (L (0,0) ε k) (ε:ℝ):=HeatCutoffHistories.iterate_gap
      (ControlledReferenceLevel.level P (fun z=>κ+aV z) hAs Λ θ v b hvb Z htarget hstop F hF (0,0))
      hδ ε.2 (fun _=>hgap) k
    intro i
    rw [hcEq]
    have hi:=hg h i
    change (ε:ℝ)≤(Obs h i).target-Terminal h at hi
    linarith
  refine ⟨input,?_,hn⟩
  filter_upwards [hi,MixedNativeJointPhysicalRows.rows_ae
    𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (Obs h) hΛ c hcGap] with q hi hrows
  have hqc:(q.1:ℝ)<Terminal h↔q.1<c:=by
    rw [←hcEq]
    constructor <;> intro hh <;> exact_mod_cast hh
  by_cases hvq:v<q.1
  · have hvqR:(v:ℝ)<(q.1:ℝ):=by exact_mod_cast hvq
    by_cases hq:q.1<c
    · have hqR:(q.1:ℝ)<Terminal h:=hqc.mpr hq
      have hY:MixedJointNamedIto.path
          𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (Obs h) c q=Mean (h,q):=by
        apply PiLp.ext
        intro i
        have ht:(q.1:ℝ)<(Obs h i).target:=
          (show (q.1:ℝ)<(c:ℝ) from by exact_mod_cast hq).trans (hcGap i)
        have he:=MixedNativeJointObservations.value_eq_physical
          𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (Obs h) c hcGap q.1 hq.le q.2 i
        rw [functional_physical (sub_pos.mpr ht),functional_physical (sub_pos.mpr ht)] at he
        simpa only [MixedJointNamedIto.path,Function.uncurry,mean,WithLp.ofLp_toLp] using he
      rw [hi,ite_eq_left hvq]
      change (StoppedItoInputs.before (c:ℝ)).indicator
        (FiniteItoNoise.gradientRow 𝓕 μ H
          (MixedJointNamedIto.path 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (Obs h) c)
          (MixedNativeJointObservations.rows 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (Obs h) c hcGap hΛ)
          (GaussianItoTest.backward ((L (pastParameter q.2) ε k).window h)
            ((L (pastParameter q.2) ε k).test h))) q=Raw (h,q)
      rw [Set.indicator_of_mem (show q∈StoppedItoInputs.before (Ω:=Ω) (c:ℝ) from by exact_mod_cast hq)]
      simp only [raw,ite_eq_left (show (v:ℝ)<(q.1:ℝ) ∧ (q.1:ℝ)<Terminal h from ⟨hvqR,hqR⟩),

        FiniteItoNoise.gradientRow,FiniteItoNoise.gradientCoefficient,hY]
      apply Finset.sum_congr rfl
      intro i _
      rw [hrows hq i]
      rw [show Held q=pastParameter q.2 from PredictablePastParameter.held_eq pastParameter (0,0) hvq]
    · have hqR:¬(q.1:ℝ)<Terminal h:=fun hh=>hq (hqc.mp hh)
      rw [hi,ite_eq_left hvq]
      change (StoppedItoInputs.before (c:ℝ)).indicator _ q=Raw (h,q)
      rw [Set.indicator_of_notMem (show q∉StoppedItoInputs.before (Ω:=Ω) (c:ℝ) from by exact_mod_cast hq)]
      simp only [raw,ite_eq_right (show ¬((v:ℝ)<(q.1:ℝ) ∧ (q.1:ℝ)<Terminal h) from fun hh=>hqR hh.2)]
  · have hvqR:¬(v:ℝ)<(q.1:ℝ):=by exact_mod_cast hvq
    rw [hi,ite_eq_right hvq]
    simp only [raw,ite_eq_right (show ¬((v:ℝ)<(q.1:ℝ) ∧ (q.1:ℝ)<Terminal h) from fun hh=>hvqR hh.1)]

include hΛ hε hgap in
/-- Fixed smooth depth and positive cutoffs give one finite literal
input bound across all past states and original histories. -/
theorem raw_bound:∃B:ℝ,0≤B ∧ ∀z,‖Raw z‖≤B:=by
  obtain ⟨C,hC,hCb⟩:=ControlledRecursiveGradientRows.gradient_bound P (fun z=>κ+aV z) hAs Λ θ v b hvb
    Z htarget hstop F hF δ hδ k
  have hm:0≤M:=hell.le.trans ((hbU 0).1.trans (hbU 0).2)
  have hcap:=NativeObservationCaps.cap_nonneg (show 0≤κ+10*M by positivity) hε
  refine ⟨(n+k)*C*Real.sqrt (NativeObservationCaps.cap (κ+10*M) ε),by positivity,?_⟩
  intro z
  by_cases hz:(v:ℝ)<(z.2.1:ℝ) ∧ (z.2.1:ℝ)<Terminal z.1
  · simp only [raw,ite_eq_left hz]
    have hg:HeatCutoffHistories.Gap (L (0,0) ε k) (ε:ℝ):=HeatCutoffHistories.iterate_gap
      (ControlledReferenceLevel.level P (fun z=>κ+aV z) hAs Λ θ v b hvb Z htarget hstop F hF (0,0))
      hδ ε.2 (fun _=>hgap) k
    let c:ℝ≥0:=(Terminal z.1).toNNReal
    have hc:(c:ℝ)=Terminal z.1:=Real.coe_toNNReal _
      (v.2.trans ((L (0,0) ε k).terminal_base z.1))
    have hrow(i:Fin (n+k)):
        ‖MixedNativeJointPhysicalRows.physicalRow
          𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (Obs z.1) z.2 i‖≤
            Real.sqrt (NativeObservationCaps.cap (κ+10*M) ε):=by
      apply (Real.le_sqrt (norm_nonneg _) hcap).mpr
      apply MixedNativePhysicalRowBound.row_bound_uniform
        𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (Obs z.1) hΛ c hε
      · intro i;rw [hc];exact hg z.1 i
      · intro i;rw [hc];exact (L (0,0) ε k).stops_after z.1 i
      · rw [hc];exact hz.2.le
    calc
      _≤∑i:Fin (n+k),‖
        (fderiv ℝ (GaussianItoTest.backward ((L (Held z.2) ε k).window z.1)
          ((L (Held z.2) ε k).test z.1) (z.2.1:ℝ)) (Mean z)
            (EuclideanSpace.basisFun (Fin (n+k)) ℝ i)) •
          MixedNativeJointPhysicalRows.physicalRow
            𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (Obs z.1) z.2 i‖:=norm_sum_le _ _
      _≤∑_:Fin (n+k),C*Real.sqrt (NativeObservationCaps.cap (κ+10*M) ε):=by
        apply Finset.sum_le_sum
        intro i _
        rw [norm_smul]
        have hgrad:= (fderiv ℝ (GaussianItoTest.backward ((L (Held z.2) ε k).window z.1)
          ((L (Held z.2) ε k).test z.1) (z.2.1:ℝ)) (Mean z)).le_opNorm
            (EuclideanSpace.basisFun (Fin (n+k)) ℝ i)
        rw [(EuclideanSpace.basisFun (Fin (n+k)) ℝ).orthonormal.norm_eq_one,mul_one] at hgrad
        exact mul_le_mul (hgrad.trans (hCb _ _ _ _ _)) (hrow i) (norm_nonneg _) hC
      _=(n+k)*C*Real.sqrt (NativeObservationCaps.cap (κ+10*M) ε):=by
        simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
        push_cast
        ring
  · simp only [raw,ite_eq_right hz,norm_zero]
    positivity

end SHE.MixedCanonicalGradientKernel
