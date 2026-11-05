module

public import SHE.MixedLevelPhysicalGradient
public import SHE.MixedCanonicalGradientHeat
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

namespace SHE.MixedRootGradientContinuity
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

variable (δ:ℝ)(hδ:0<δ)(k:ℕ)
local notation "Q"=>RootHeatBounds.level L δ hδ
local notation "Obs"=>(fun ε:ℝ≥0=>(Q ε k).observations.observations)
local notation "Terminal"=>(fun ε:ℝ≥0=>(Q ε k).terminal)
local notation "Mean"=>(fun ε:ℝ≥0=>MixedLevelPhysicalGradient.mean
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (Q ε k))
local notation "Raw"=>(fun ε:ℝ≥0=>MixedLevelPhysicalGradient.raw
  𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (Q ε k))

include S in
private theorem target_continuous (h:CutoffWordHistories.History P k)(i:Fin (n+k)):
    Continuous (fun ε:ℝ≥0=>(Obs ε h i).target):=
  RootHeatTargets.target_continuous L δ hδ k h i
include S in
private theorem center_eq (ε:ℝ≥0)(h:CutoffWordHistories.History P k)(i:Fin (n+k)):
    ((Q ε k).observations.observations h i).center=((Q 0 k).observations.observations h i).center:=
  RootHeatTargets.center_eq L δ hδ ε 0 k h i
include S in
private theorem stop_eq (ε:ℝ≥0)(h:CutoffWordHistories.History P k)(i:Fin (n+k)):
    ((Q ε k).observations.observations h i).stop=((Q 0 k).observations.observations h i).stop:=
  RootHeatTargets.stop_eq L δ hδ ε 0 k h i
include S in
private theorem terminal_eq (ε:ℝ≥0)(h:CutoffWordHistories.History P k):
    (Q ε k).terminal h=(Q 0 k).terminal h:=
  RootHeatBounds.terminal_eq L δ hδ ε 0 k h

/-- The complete physical current vector converges with the moving
finite recursive history when the heat age vanishes. Every coordinate
has positive age strictly before its original terminal. -/
theorem mean_continuous (z:CutoffWordHistories.History P k×(ℝ≥0×Ω))
    (hz:(z.2.1:ℝ)<Terminal 0 z.1):
    Continuous (fun ε:ℝ≥0=>Mean ε z):=by
  apply (PiLp.continuous_toLp 2 (fun _:Fin (n+k)=>ℝ)).comp
  apply continuous_pi
  intro i
  have hg(ε:ℝ≥0):(z.2.1:ℝ)<(Obs ε z.1 i).target:=by
    have hh:=(Q ε k).targets_after z.1 i
    rw [terminal_eq 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      L δ hδ k ε z.1] at hh
    exact hz.trans_le hh
  have hu:Continuous (fun ε:ℝ≥0=>PhysicalProfile.physicalHeatMean
      (embed (S.first z.2.1 z.2.2)) ((Obs ε z.1 i).target-(z.2.1:ℝ),(Obs 0 z.1 i).center)):=by
    rw [continuous_iff_continuousAt]
    intro ε
    exact (ObservationTargetContinuity.continuousAt_heatMean_age (sub_pos.mpr (hg ε)) _ _).comp
      (f:=fun η:ℝ≥0=>(Obs η z.1 i).target-(z.2.1:ℝ)) (x:=ε)
      ((target_continuous 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
        L δ hδ k z.1 i).sub continuous_const).continuousAt
  have hd:Continuous (fun ε:ℝ≥0=>PhysicalProfile.physicalHeatMean
      (embed (S.second z.2.1 z.2.2-S.first z.2.1 z.2.2))
        ((Obs ε z.1 i).target-(z.2.1:ℝ),(Obs 0 z.1 i).center)):=by
    rw [continuous_iff_continuousAt]
    intro ε
    exact (ObservationTargetContinuity.continuousAt_heatMean_age (sub_pos.mpr (hg ε)) _ _).comp
      (f:=fun η:ℝ≥0=>(Obs η z.1 i).target-(z.2.1:ℝ)) (x:=ε)
      ((target_continuous 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
        L δ hδ k z.1 i).sub continuous_const).continuousAt
  convert hu.add (hd.const_mul (Real.exp (-Λ*((Obs 0 z.1 i).stop-(z.2.1:ℝ))))) using 1
  funext ε
  simp only [Function.comp_def,Pi.add_apply,Pi.mul_apply,Pi.sub_apply,Pi.smul_apply,MixedLevelPhysicalGradient.mean,WithLp.ofLp_toLp,
    center_eq 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L δ hδ k ε z.1 i,
    stop_eq 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L δ hδ k ε z.1 i]

private theorem row_continuous (z:CutoffWordHistories.History P k×(ℝ≥0×Ω))
    (hz:(z.2.1:ℝ)<Terminal 0 z.1)(i:Fin (n+k)):
    Continuous (fun ε:ℝ≥0=>MixedNativeJointPhysicalRows.physicalRow
      𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (Obs ε z.1) z.2 i):=by
  have hg(ε:ℝ≥0):(z.2.1:ℝ)<(Obs ε z.1 i).target:=by
    have hh:=(Q ε k).targets_after z.1 i
    rw [terminal_eq 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      L δ hδ k ε z.1] at hh
    exact hz.trans_le hh
  have hr {l W:ℝ}(hl:0<l)(f:EllipticField l W):Continuous (fun ε:ℝ≥0=>
      NativeObservationCovariance.row hl f (Obs ε z.1 i).target (z.2.1:ℝ) (Obs 0 z.1 i).center):=by
    rw [continuous_iff_continuousAt]
    intro ε
    exact (NativeRowTargetContinuity.row_continuousAt_target hl f (hg ε) _).comp
      (f:=fun η:ℝ≥0=>(Obs η z.1 i).target) (x:=ε)
      (target_continuous 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
        L δ hδ k z.1 i).continuousAt
  have h0:=hr hκ (AdditiveHaarForcing.constantField κ hκ)
  have hu:=hr hell (ContinuousHeatMild.coefficientFunction haU hell hbU S.first z.2)
  have hv:=hr hell (ContinuousHeatMild.coefficientFunction haV hell hbV S.second z.2)
  have hs:=WithLp.prod_continuous_toLp 2 RealHaarInput RealHaarInput |>.comp
    (h0.prodMk (hv.add ((hu.sub hv).const_smul (1-Real.exp (-Λ*((Obs 0 z.1 i).stop-(z.2.1:ℝ)))))))
  convert hs using 1
  funext ε
  simp only [Function.comp_def,Pi.add_apply,Pi.mul_apply,Pi.sub_apply,Pi.smul_apply,MixedNativeJointPhysicalRows.physicalRow,MixedNativeJointPhysicalRows.additiveRow,
    MixedNativeJointPhysicalRows.firstRow,MixedNativeJointPhysicalRows.secondRow,
    center_eq 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L δ hδ k ε z.1 i,
    stop_eq 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L δ hδ k ε z.1 i]

/-- Pointwise convergence of the literal predictable kth kernel, with
the whole recursive word, covariance and current varying with epsilon. -/
theorem raw_continuous (z:CutoffWordHistories.History P k×(ℝ≥0×Ω)):
    Continuous (fun ε:ℝ≥0=>Raw ε z):=by
  by_cases hvq:R.base<(z.2.1:ℝ)
  · by_cases hq:(z.2.1:ℝ)<Terminal 0 z.1
    · have hMean:=mean_continuous 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
        L δ hδ k z hq
      have hG:=RootHeatGradientContinuity.continuous_gradient L δ hδ k z.1 (z.2.1:ℝ)
      have hh:=hG.comp (continuous_id.prodMk hMean)
      have hs:=continuous_finsetSum Finset.univ (fun i _=>
        (hh.clm_apply (continuous_const (y:=EuclideanSpace.basisFun (Fin (n+k)) ℝ i))).smul
          (row_continuous 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
            L δ hδ k z hq i))
      convert hs using 1
      funext ε
      dsimp only
      rw [MixedLevelPhysicalGradient.raw,if_pos ⟨hvq,by
        rw [terminal_eq 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
          L δ hδ k ε z.1];exact hq⟩]
      rfl
    · have he:(fun ε:ℝ≥0=>Raw ε z)=fun _=>0:=by
        funext ε
        dsimp only
        rw [MixedLevelPhysicalGradient.raw]
        apply if_neg
        rintro ⟨_,hh⟩
        rw [terminal_eq 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
          L δ hδ k ε z.1] at hh
        exact hq hh
      rw [he];exact continuous_const
  · have he:(fun ε:ℝ≥0=>Raw ε z)=fun _=>0:=by
      funext ε
      dsimp only
      rw [MixedLevelPhysicalGradient.raw]
      exact if_neg (fun hh=>hvq hh.1)
    rw [he];exact continuous_const

end SHE.MixedRootGradientContinuity
