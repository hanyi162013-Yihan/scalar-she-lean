module

public import SHE.NativeNoiseIto
public import SHE.MixedNativeJointHistory

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency true
noncomputable section

namespace SHE.MixedNativeJointNoise
open Set Filter MeasureTheory Real StoppedFourier NativeHeatObservation NativeObservationNaturality
  FiniteHaar DyadicApproximation PredictableL2 CutoffWordLevel CutoffWordHistories CutoffCarriers
  ActualMeanKernel NativeRandomKernel NativeRealNoise
open scoped ENNReal NNReal
local instance mixedNativeJointNoise_unitPositive : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩
local instance mixedNativeJointNoise_nativePositive : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local instance mixedNativeJointNoise_realMeasurable : MeasurableSpace RealL2 := borel RealL2
local instance mixedNativeJointNoise_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance mixedNativeJointNoise_unitMeasurable : MeasurableSpace CircleHeat.CircleL2 := borel CircleHeat.CircleL2
local instance mixedNativeJointNoise_unitBorel : BorelSpace CircleHeat.CircleL2 := ⟨rfl⟩
local instance mixedNativeJointNoise_nativeMeasurable : MeasurableSpace CircleL2 := borel CircleL2
local instance mixedNativeJointNoise_nativeBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance mixedNativeJointNoise_columnsMeasurable : MeasurableSpace SignedKernelColumns.Space := borel SignedKernelColumns.Space
local instance mixedNativeJointNoise_columnsBorel : BorelSpace SignedKernelColumns.Space := ⟨rfl⟩
local instance mixedNativeJointNoise_nativeSecondCountable : SecondCountableTopology CircleL2 :=
  (_root_.fourierBasis (T:=2*Real.pi)).repr.toHomeomorph.secondCountableTopology
variable {Ω A : Type} [MeasurableSpace Ω] [MeasurableSpace A]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0 < κ) {aU aV : ℝ → ℝ} (haU : Measurable aU) (haV : Measurable aV)
variable {ell M : ℝ} (hell : 0 < ell) (hbU : ∀ z,ell ≤ aU z ∧ aU z ≤ M)
variable (hbV : ∀ z,ell ≤ aV z ∧ aV z ≤ M)
variable (I₀ I₁ : StandardTerminalIto (C:=RealHaarIntegrand.Columns) (E:=RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : MixedNativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀)
variable {R : ReferenceData} {n : ℕ} (L : CutoffWordLevel.Level R HeatCircle n)

def firstCurrent (z : ℝ≥0 × Ω) : CircleL2 := embed (S.first z.1 z.2)
def secondCurrent (z : ℝ≥0 × Ω) : CircleL2 := embed (S.second z.1 z.2)
def firstField : ℝ≥0 × Ω → EllipticField ell M := ContinuousHeatMild.coefficientFunction haU hell hbU S.first
def secondField : ℝ≥0 × Ω → EllipticField ell M := ContinuousHeatMild.coefficientFunction haV hell hbV S.second

theorem firstCurrent_predictable : StronglyMeasurable[𝓕.predictable]
    (firstCurrent 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S) :=
  embed.continuous.comp_stronglyMeasurable S.first_predictable

theorem secondCurrent_predictable : StronglyMeasurable[𝓕.predictable]
    (secondCurrent 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S) :=
  embed.continuous.comp_stronglyMeasurable S.second_predictable

def kernel (k : ℕ) (t : A → Fin k → ℝ) :
    (A × (ℝ≥0 × Ω)) × (HeatCircle × HeatCircle) → ℂ :=
  jointVariableField L k Λ (fun z => (z.2.1:ℝ))
    (fun z => firstCurrent 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S z.2)
    (fun z => secondCurrent 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S z.2)
    (fun z => t z.1)

theorem kernel_predictable (k : ℕ) (t : A → Fin k → ℝ) (ht : Measurable t) :
    @Measurable _ _
      (((inferInstance : MeasurableSpace A).prod 𝓕.predictable).prod inferInstance)
      inferInstance (kernel 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L k t) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.predictable
  exact jointVariableField_measurable L k Λ _
    ((PredictableClock.real_time_measurable 𝓕).comp measurable_snd) _ _
    ((firstCurrent_predictable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S).measurable.comp measurable_snd)
    ((secondCurrent_predictable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S).measurable.comp measurable_snd)
    _ (ht.comp measurable_fst)

theorem kernel_bound (T : ℝ) (hT : ∀ p,L.terminal p=T) (k : ℕ) (t : A → Fin k → ℝ)
    (z : A × (ℝ≥0 × Ω)) :
    ∃ B : ℝ,0 ≤ B ∧ ∀ y x,‖kernel 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L k t (z,(y,x))‖ ≤ B := by
  obtain ⟨B,hB,hbound⟩ := spatial_uniform_bound L (Ω:=A × (ℝ≥0 × Ω)) T hT k (z.2.1:ℝ) (t z.1)
  exact ⟨B,hB,fun y x => hbound (currentJointMean L k Λ _ _ _) z y x⟩

/-- The unweighted first-derivative kernel at the actual mixed joint
state, followed by the actual signed-Haar difference. This is a supporting
term; the full joint diffusion also retains its stop-dependent diagonal
weights. Bessel mass and the drift-coupling parameter Λ are independent. -/
def raw (k : ℕ) (mass ρ : ℝ) (hmass : 1 ≤ mass) (hρ : 0 ≤ ρ) (t : A → Fin k → ℝ) :
    A × (ℝ≥0 × Ω) → SignedKernelColumns.Space :=
  SignedKernelColumns.rawColumns
    (kernel 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L k t)
    mass ρ hmass hρ ell M hell
    (fun z => firstField 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S z.2)
    (fun z => secondField 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S z.2)

theorem raw_predictable (T : ℝ) (hT : ∀ p,L.terminal p=T) (k : ℕ)
    (mass ρ : ℝ) (hmass : 1 ≤ mass) (hρ : 0 ≤ ρ) (t : A → Fin k → ℝ) (ht : Measurable t) :
    StronglyMeasurable[(inferInstance : MeasurableSpace A).prod 𝓕.predictable]
      (raw 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L k mass ρ hmass hρ t) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.predictable
  exact (SignedKernelColumns.rawColumns_measurable
    (kernel_predictable 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L k t ht)
    (kernel_bound 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L T hT k t)
    hmass hρ hell _ _ (S.first_coefficient.measurable.comp measurable_snd)
    (S.second_coefficient.measurable.comp measurable_snd)).stronglyMeasurable

def mean (k : ℕ) (q : ℝ≥0) (ω : Ω) (p : History HeatCircle k) : WordRecursion.State (n+k) :=
  MixedNativeJointHistory.evaluate 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S
    ((carrier L k).observations.observations p) ω q

theorem point_eq_actual (k : ℕ) (t : A → Fin k → ℝ) (a : A) (q : ℝ≥0) (ω : Ω)
    (p : History HeatCircle k) (y : HeatCircle) :
    point L k q (currentJointMean L k Λ (fun z : A × (ℝ≥0 × Ω) => (z.2.1:ℝ))
      (fun z => firstCurrent 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S z.2)
      (fun z => secondCurrent 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S z.2) (a,(q,ω))) p y=
      point L k q (mean 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L k q ω) p y := by
  by_cases hq : (q:ℝ) < (carrier L k).terminal p
  · have hm : currentJointMean L k Λ (fun z : A × (ℝ≥0 × Ω) => (z.2.1:ℝ))
        (fun z => firstCurrent 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S z.2)
        (fun z => secondCurrent 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S z.2) (a,(q,ω)) p=
        mean 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L k q ω p := by
      apply PiLp.ext
      intro i
      have ht := hq.trans_le ((carrier L k).targets_after p i)
      simp only [currentJointMean,MixedNativeJointNoise.mean,MixedNativeJointHistory.evaluate,
        JointWordObserve.evaluate,WithLp.ofLp_toLp,WordRecursion.observe,ite_eq_left ht,
        firstCurrent,secondCurrent,MixedNativeJointHistory.firstData,MixedNativeJointHistory.secondData,
        PredictableWordState.Data.physicalState,Real.toNNReal_coe,Function.uncurry]
    simp only [point,ite_eq_left hq,hm]
  · simp only [point,ite_eq_right hq]

/-- Every current-time section is exactly the actual mixed joint word
kernel used in the proved Gaussian trace estimate, including inactive
times. This is a pointwise identity, not a selected measurable version. -/
theorem kernel_eq_actual (k : ℕ) (t : A → Fin k → ℝ) (a : A) (q : ℝ≥0) (ω : Ω)
    (y x : HeatCircle) :
    kernel 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L k t ((a,(q,ω)),(y,x))=
      spatial L k q (mean 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L k q)
        (t a) ω y x := by
  unfold kernel jointVariableField spatial
  congr 1
  apply integral_congr_ae
  exact ae_of_all _ (fun z => point_eq_actual 𝓕 μ H Λ κ hκ haU haV hell hbU hbV
    I₀ I₁ u₀ v₀ S L k t a q ω (HistoryProductMeasure.separated k (x,t a,z)) y)

set_option backward.isDefEq.respectTransparency false in
theorem raw_eq_actual (k : ℕ) (mass ρ : ℝ) (hmass : 1 ≤ mass) (hρ : 0 ≤ ρ)
    (t : A → Fin k → ℝ) (a : A) (q : ℝ≥0) (ω : Ω) :
    raw 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L k mass ρ hmass hρ t (a,(q,ω))=
      SignedKernelColumns.rawColumns
        (field L k q (mean 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L k q) (t a))
        mass ρ hmass hρ ell M hell
        (fun ω => firstField 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (q,ω))
        (fun ω => secondField 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S (q,ω)) ω := by
  have hOp : integralOperator (kernel 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L k t) (a,(q,ω))=
      integralOperator
        (field L k q (mean 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L k q) (t a)) ω := by
    have hFG : (fun z : Unit × (HeatCircle × HeatCircle) =>
        kernel 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L k t ((a,(q,ω)),z.2))=
        fun z => field L k q (mean 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L k q) (t a) (ω,z.2) := by
      funext z
      exact kernel_eq_actual 𝓕 μ H Λ κ hκ haU haV hell hbU hbV I₀ I₁ u₀ v₀ S L k t a q ω z.2.1 z.2.2
    exact (integralOperator_section _ _).trans
      ((congrArg (fun G : Unit × (HeatCircle × HeatCircle) → ℂ => integralOperator G ()) hFG).trans
        (integralOperator_section _ _).symm)
  apply lp.ext
  funext i
  simp only [raw,SignedKernelColumns.rawColumns_apply,hOp]

end SHE.MixedNativeJointNoise
