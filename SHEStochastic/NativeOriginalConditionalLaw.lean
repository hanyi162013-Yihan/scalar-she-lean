module

public import SHE.OriginalConditionalFamilyStep
public import SHEStochastic.NativeScalarModel

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section

namespace SHEStochastic.NativeOriginalConditionalLaw
open MeasureTheory ProbabilityTheory SHE SHE.PredictableL2 SHE.FiniteHaar SHE.DyadicApproximation
open SHE.OrthogonalItoChannels
open scoped NNReal ENNReal

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : SecondCountableTopology CircleHeat.CircleL2 :=
  (_root_.fourierBasis (T := (1 : ℝ))).repr.toHomeomorph.secondCountableTopology
local instance : SecondCountableTopology RealL2 := realCircleIdentification.toHomeomorph.secondCountableTopology
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩
local instance : MeasurableSpace RealHaarInput := borel _
local instance : BorelSpace RealHaarInput := ⟨rfl⟩
local instance : MeasurableSpace (Both RealL2) := borel _
local instance : BorelSpace (Both RealL2) := ⟨rfl⟩

/-- The old conditional model's actual canonical coordinates have the
native Brownian laws on one state-prefix event. -/
theorem law {Ω : Type} [MeasurableSpace Ω]
    (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (H : ℝ≥0) (hpos : 0<H) (D : SmoothApproximation.ScalarData)
    (B : StandardTerminalIto (C := Both RealL2) (E := ℝ) F μ H)
    (u₀ : RealL2) (S : OriginalNativeHeatEquation.Data F μ H D B u₀)
    (M : NativeScalarModel.Model B) (hn : NullCompleteFiltration.ContainsNullSets F μ)
    (v h : ℝ≥0) (hvh : v+h≤H) :
    ∀ᵐ p ∂μ.map (NativeContinuousPath.path v S.value S.continuous),
      ∀ n (a : Fin n → HaarNode), FiniteBrownianLawOn (ConditionalCanonicalModelFamily.filtration h)
        (OriginalShiftedSingleModels.kernel F μ H D B u₀ S v h hpos p) h
        (fun i ↦ CanonicalStateDriverFiltration.coordinate h (a i)) (fun i j ↦ if a i=a j then 1 else 0) := by
  let J := OriginalNativeWhiteDriver.integral F μ H B
  have ha (t : ℝ≥0) : Measurable[F t] (S.value t) :=
    ((show IsStronglyPredictable F S.value from S.predictable).stronglyAdapted t).measurable
  have hb := AllHorizonStatePrefixBrownian.law F μ H S.value S.continuous ha
    NativeSingleNoiseBasis.basis NativeSingleNoiseBasis.basis.orthonormal J (NativeScalarBDG.constant 3)
    (OriginalNativeWhiteDriver.bdg F μ H B _ (NativeScalarModel.bdg16 M)) hpos hn
    (OriginalNativeWhiteDriver.levy F μ H B (NativeScalarModel.levy M)) v h hvh
  rw [← OriginalConditionalWhiteNoise.bundle_eq F μ H S.value S.continuous J hpos v h] at hb
  exact hb

end SHEStochastic.NativeOriginalConditionalLaw
