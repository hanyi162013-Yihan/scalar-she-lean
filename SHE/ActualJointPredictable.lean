module

public import SHE.ActualJointKernel

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency true
noncomputable section

namespace SHE.ActualMeanKernel
open Set MeasureTheory Real StoppedFourier CutoffWordLevel CutoffWordHistories
  PredictableL2
open scoped ENNReal NNReal
local instance actualJointPredictable_nativePositive : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local instance actualJointPredictable_unitMeasurable : MeasurableSpace CircleHeat.CircleL2 := borel CircleHeat.CircleL2
local instance actualJointPredictable_unitBorel : BorelSpace CircleHeat.CircleL2 := ⟨rfl⟩
local instance actualJointPredictable_nativeMeasurable : MeasurableSpace CircleL2 := borel CircleL2
local instance actualJointPredictable_nativeBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance actualJointPredictable_nativeSecondCountable : SecondCountableTopology CircleL2 :=
  (_root_.fourierBasis (T:=2*Real.pi)).repr.toHomeomorph.secondCountableTopology
local instance actualJointPredictable_columnsMeasurable : MeasurableSpace SignedKernelColumns.Space := borel SignedKernelColumns.Space
local instance actualJointPredictable_columnsBorel : BorelSpace SignedKernelColumns.Space := ⟨rfl⟩
variable {Ω A : Type} [MeasurableSpace Ω] [MeasurableSpace A] {R : ReferenceData} {n : ℕ}
variable (L : CutoffWordLevel.Level R HeatCircle n)

/-- Actual raw columns, with old time parameters kept separate from the
current predictable time/sample. The right Haar difference is unchanged. -/
def oldTimeJointNoise (k : ℕ) (Λ ρ : ℝ) (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ)
    (t : A → Fin k → ℝ) (U V : ℝ≥0 × Ω → CircleL2)
    (ell M : ℝ) (hell : 0 < ell)
    (c d : ℝ≥0 × Ω → FiniteHaar.EllipticField ell M)
    (z : A × (ℝ≥0 × Ω)) : SignedKernelColumns.Space :=
  jointRawNoiseColumns L k Λ ρ hΛ hρ (fun z => (z.2.1:ℝ))
    (fun z => U z.2) (fun z => V z.2) (fun z => t z.1)
    ell M hell (fun z => c z.2) (fun z => d z.2) z

theorem oldTimeJointNoise_predictable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (T : ℝ) (hT : ∀ p,L.terminal p=T) (k : ℕ)
    (Λ ρ : ℝ) (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ) (t : A → Fin k → ℝ) (ht : Measurable t)
    (U V : ℝ≥0 × Ω → CircleL2)
    (hU : StronglyMeasurable[𝓕.predictable] U) (hV : StronglyMeasurable[𝓕.predictable] V)
    (ell M : ℝ) (hell : 0 < ell) (c d : ℝ≥0 × Ω → FiniteHaar.EllipticField ell M)
    (hc : StronglyMeasurable[𝓕.predictable] c) (hd : StronglyMeasurable[𝓕.predictable] d) :
    StronglyMeasurable[(inferInstance : MeasurableSpace A).prod 𝓕.predictable]
      (oldTimeJointNoise L k Λ ρ hΛ hρ t U V ell M hell c d) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.predictable
  have hq : Measurable (fun z : A × (ℝ≥0 × Ω) => (z.2.1:ℝ)) :=
    (PredictableClock.real_time_measurable 𝓕).comp measurable_snd
  exact (jointRawNoiseColumns_measurable L T hT k Λ ρ hΛ hρ _ hq
    _ _ (hU.measurable.comp measurable_snd) (hV.measurable.comp measurable_snd)
    _ (ht.comp measurable_fst) ell M hell _ _
    (hc.measurable.comp measurable_snd) (hd.measurable.comp measurable_snd)).stronglyMeasurable

def averagedJointNoise (ν : Measure A) (k : ℕ) (Λ ρ : ℝ) (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ)
    (t : A → Fin k → ℝ) (U V : ℝ≥0 × Ω → CircleL2)
    (ell M : ℝ) (hell : 0 < ell) (c d : ℝ≥0 × Ω → FiniteHaar.EllipticField ell M)
    (z : ℝ≥0 × Ω) : SignedKernelColumns.Space :=
  ∫ a,oldTimeJointNoise L k Λ ρ hΛ hρ t U V ell M hell c d (a,z) ∂ν

/-- The old-time average is genuinely predictable before its terminal
stochastic square is formed. Quantitative old-time L1 envelopes can be
used in HilbertParameterAverage.energy to prove its square integrability. -/
theorem averagedJointNoise_predictable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (ν : Measure A) [SFinite ν] (T : ℝ) (hT : ∀ p,L.terminal p=T) (k : ℕ)
    (Λ ρ : ℝ) (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ) (t : A → Fin k → ℝ) (ht : Measurable t)
    (U V : ℝ≥0 × Ω → CircleL2)
    (hU : StronglyMeasurable[𝓕.predictable] U) (hV : StronglyMeasurable[𝓕.predictable] V)
    (ell M : ℝ) (hell : 0 < ell) (c d : ℝ≥0 × Ω → FiniteHaar.EllipticField ell M)
    (hc : StronglyMeasurable[𝓕.predictable] c) (hd : StronglyMeasurable[𝓕.predictable] d) :
    StronglyMeasurable[𝓕.predictable]
      (averagedJointNoise L ν k Λ ρ hΛ hρ t U V ell M hell c d) :=
  HilbertParameterAverage.average_predictable 𝓕 ν _
    (oldTimeJointNoise_predictable L 𝓕 T hT k Λ ρ hΛ hρ t ht U V hU hV ell M hell c d hc hd).measurable

end SHE.ActualMeanKernel
