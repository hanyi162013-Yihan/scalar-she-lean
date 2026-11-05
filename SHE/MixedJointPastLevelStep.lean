module

public import SHE.MixedJointLevelData
public import SHE.MixedNativePastPhysicalStep
public import SHE.MixedNativeJointHistory
public import SHE.JointInsertionIntegrability
public import SHE.JointWordDefect

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option quotPrecheck false
noncomputable section

namespace SHE.MixedJointPastLevelStep
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

local notation "D" => MixedJointLevelData.state 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L

theorem state_eq_value (p : P) (b q : ℝ≥0)
    (hgap : ∀ i,(b:ℝ)<(L.observations.observations p i).target) (hqb : q≤b) (ω : Ω) :
    D p ω (q:ℝ)=MixedNativeJointObservations.value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
      (L.observations.observations p) b q ω :=
  MixedNativeJointHistory.evaluate_eq_value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    (L.observations.observations p) b q hgap hqb ω

variable (v : ℝ≥0) (hbase : R.base=(v:ℝ))

variable (J : StandardTerminalIto (C := Both RealHaarInput) (E := ℝ) 𝓕 μ H)
variable (hIJ₀ : StandardScalarNaturality I₀ (leftIntegral 𝓕 μ H J))
variable (hIJ₁ : StandardScalarNaturality I₁ (rightIntegral 𝓕 μ H J))
include hIJ₀ hIJ₁ hbase in
/-- Actual variable-history first-defect step for the mixed native pair.
The martingale term is an actual centered Itô term; no per-word
applicability or Gaussian PDE premise is introduced. -/
theorem one_step (hnull : NullCompleteFiltration.ContainsNullSets 𝓕 μ)
    (hJ : StandardFiniteIto.Universal 𝓕 μ H J) (hlocal : StandardTerminalPastLocality J) (hΛ : 0≤Λ)
    (hA : R.totalVariance=(fun z => κ+aV z)) (hh : R.horizon≤(H:ℝ))
    {η : ℝ} (hη : 0<η) (hgap : ∀ p i,η≤(L.observations.observations p i).target-L.terminal p)
    (p : P) : ∃ N : Ω→ℝ,Integrable N μ ∧ (∀ A,MeasurableSet[𝓕 v] A → (∫ ω in A,N ω ∂μ)=0) ∧ ∀ᵐ ω ∂μ,
      MixedJointLevelData.leaf 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L p ω=
        MixedJointLevelData.reference 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L p ω+N ω+
        MixedJointLevelData.localRemainder 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L p ω+
        MixedJointLevelData.mark 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L p ω := by
  let b : ℝ≥0 := (L.terminal p).toNNReal
  have hbcoe : (b:ℝ)=L.terminal p := Real.coe_toNNReal _ (R.base_nonneg.trans (L.terminal_base p))
  have hbH : b≤H := by exact_mod_cast (show (b:ℝ)≤H by rw [hbcoe];exact (L.terminal_horizon p).trans hh)
  have hstrict : ∀ i,(b:ℝ)<(L.observations.observations p i).target := by
    intro i
    rw [hbcoe]
    have := hgap p i
    linarith
  let Y := fun (ω : Ω) (t : ℝ) => MixedNativeJointObservations.value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
    I₀ I₁ u₀ v₀ S (L.observations.observations p) b t.toNNReal ω
  have hY (ω : Ω) (t : ℝ) (ht : t∈Icc R.base (L.terminal p)) : D p ω t=Y ω t := by
    have ht0 : 0≤t := R.base_nonneg.trans ht.1
    have htb : t.toNNReal≤b := by exact_mod_cast (show (t.toNNReal:ℝ)≤b by rw [Real.coe_toNNReal _ ht0,hbcoe];exact ht.2)
    have he := state_eq_value 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L p b t.toNNReal hstrict htb ω
    simpa only [Real.coe_toNNReal _ ht0] using he
  obtain ⟨N,hNi,hNc,hN⟩ := MixedNativePastPhysicalStep.one_step 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
    I₀ I₁ u₀ v₀ S J hIJ₀ hIJ₁ hnull hJ hlocal hΛ (L.window p) v hbase b hbcoe.symm hbH hη
    (by intro i;change η≤(L.observations.observations p i).target-(b:ℝ);rw [hbcoe];exact hgap p i)
    (by intro i;change (b:ℝ)≤(L.observations.observations p i).stop;rw [hbcoe];exact L.stops_after p i)
    (L.test_uniform.boundedSmooth p)
  have hlocal := JointInsertionIntegrability.time_integrable L Λ (dU).physicalState_measurable (dV).physicalState_measurable
    (dU).physicalField_measurable (dV).physicalField_measurable p
  obtain ⟨K,hKn,hmark⟩ := MixedJointLevelData.mark_uniform_bound 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
    I₀ I₁ u₀ v₀ S L hΛ
  refine ⟨N,hNi,hNc,?_⟩
  filter_upwards [hN] with ω hω
  have hsum := intervalIntegral.integral_add (hlocal ω) ((hmark p ω).2)
  let G : ℝ→ℝ := fun t =>
      (∫ x : HeatCircle,WordRecursion.insertion (fun v => κ+aV v) R.reference (L.observations.observations p) t x
        (backward (L.window p) (L.test p) t)
        (JointPhysicalInsertion.appendState (XV (ω,(t,x))) (Y ω t)) ∂AddCircle.haarAddCircle)+
      (1/2:ℝ)*covarianceAction
        (MixedNativeJointBracketDefect.defect 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
          (L.observations.observations p) (t.toNNReal,ω))
        (GaussianTaylor.hessian (backward (L.window p) (L.test p) t) (Y ω t))
  have he : (∫ t in R.base..L.terminal p,G t)=
      MixedJointLevelData.localRemainder 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L p ω+
      MixedJointLevelData.mark 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L p ω := by
    unfold MixedJointLevelData.localRemainder MixedJointLevelData.mark JointWordAnalytic.remainder JointWordDefect.mark
    rw [← hsum]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (L.terminal_base p)] at ht
    dsimp only [G]
    rw [← hY ω t ht,← hA]
    rfl
  change L.test p (Y ω (b:ℝ))= _ at hω
  rw [hbcoe] at hω
  have href := PhysicalIto.backward_eq_semigroup (L.window p) (L.test p)
    (show R.base∈Icc (L.window p).left (L.window p).right from ⟨le_rfl,L.terminal_base p⟩)
  have hrefpoint := congrArg (fun G : WordRecursion.State n→ℝ => G (Y ω R.base)) href
  change backward (L.window p) (L.test p) R.base (Y ω R.base)=
    WordRecursion.gaussianSemigroup R.reference (L.observations.observations p) R.base (L.terminal p) (L.test p) (Y ω R.base) at hrefpoint
  change L.test p (Y ω (L.terminal p))=
    WordRecursion.gaussianSemigroup R.reference (L.observations.observations p) R.base (L.terminal p) (L.test p) (Y ω R.base)+N ω+_ at hω
  rw [← hrefpoint] at hω
  change L.test p (Y ω (L.terminal p))=backward (L.window p) (L.test p) R.base (Y ω R.base)+N ω+
    (∫ t in R.base..L.terminal p,G t) at hω
  rw [he,← hY ω (L.terminal p) ⟨L.terminal_base p,le_rfl⟩,← hY ω R.base ⟨le_rfl,L.terminal_base p⟩] at hω
  change L.test p (D p ω (L.terminal p))=backward (L.window p) (L.test p) R.base (D p ω R.base)+N ω+
    MixedJointLevelData.localRemainder 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L p ω+
    MixedJointLevelData.mark 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L p ω
  exact hω.trans (by ring)

end SHE.MixedJointPastLevelStep
