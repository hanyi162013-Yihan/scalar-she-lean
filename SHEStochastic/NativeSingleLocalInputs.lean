module

public import SHEStochastic.NativeHaarChannels
public import SHE.GivenSingleNativeArbitraryLocalUniqueness
public import SHE.OriginalNativeFrozenRows
public import SHE.NativeSingleNoiseBasis

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section

namespace SHEStochastic.NativeSingleLocalInputs
open MeasureTheory SHE SHE.PredictableL2 SHE.FiniteHaar SHE.DyadicApproximation
open SHE.OrthogonalItoChannels SHE.NativeObservationNaturality
open NativeScalarModel
open scoped NNReal ENNReal

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : SecondCountableTopology CircleHeat.CircleL2 :=
  (_root_.fourierBasis (T := (1 : ℝ))).repr.toHomeomorph.secondCountableTopology
local instance : SecondCountableTopology RealL2 := realCircleIdentification.toHomeomorph.secondCountableTopology
local instance : MeasurableSpace RealL2 := borel _
local instance : BorelSpace RealL2 := ⟨rfl⟩
local instance : MeasurableSpace RealHaarInput := borel _
local instance : BorelSpace RealHaarInput := ⟨rfl⟩
local instance : Nontrivial RealHaarInput := ⟨⟨NativeSingleNoiseBasis.basis none, 0, by
  intro h
  have hh := NativeSingleNoiseBasis.basis.orthonormal.norm_eq_one none
  rw [h, norm_zero] at hh
  norm_num at hh⟩⟩
local instance : Nontrivial RealL2 := OriginalNativeFrozenRows.coordinates.symm.toEquiv.nontrivial

variable {ι : Type} [Fintype ι] (Ω : ι → Type) [∀ i, MeasurableSpace (Ω i)]
  (F : ∀ i, Filtration ℝ≥0 (inferInstance : MeasurableSpace (Ω i)))
  (μ : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (μ i)] (h : ℝ≥0)
  (D : SmoothApproximation.ScalarData)
  (J : ∀ i, StandardTerminalIto (C := RealL2) (E := ℝ)
    (PredictableTimeDilation.filtration (F i) (PredictableTimeDilation.clock NativeClock.rate NativeClock.rate_pos))
    (μ i) (NativeClock.rate*h))
  (u₀ : RealL2)
  (U : ∀ i, SingleNativeHeatEquation.Data
    (PredictableTimeDilation.filtration (F i) (PredictableTimeDilation.clock NativeClock.rate NativeClock.rate_pos))
    (μ i) (NativeClock.rate*h) D (J i) u₀)
  (M : ∀ i, NativeScalarModel.Model (J i))

def products : SingleNativeProductFamily.Products Ω F μ h J := fun i ↦ NativeScalarModel.products (M i)

def physicalModel (i : ι) : NativeScalarModel.Model
    (SingleNativeProductFamily.physical Ω F μ h J (products Ω F μ h J M) i) :=
  NativeScalarModel.selfProduct (M i) (SingleNativeProductFamily.selected Ω F μ h J (products Ω F μ h J M) i)

def driverModel (i : ι) : NativeScalarModel.Model
    (SingleNativeProductFamily.driver Ω F μ h J D u₀ U (products Ω F μ h J M) i) :=
  NativeScalarModel.rotated (physicalModel Ω F μ h J M i)
    (PredictableScalarHaarRotation.field D
      (Function.uncurry (SingleNativeProductFamily.augmented Ω F μ h J D u₀ U (products Ω F μ h J M) i).value))
    (PredictableScalarHaarRotation.field_measurable _ D _
      (SingleNativeProductFamily.augmented Ω F μ h J D u₀ U (products Ω F μ h J M) i).predictable)
    (SingleNativeProductFamily.contains_null Ω F μ i)

/-- All ordinary inputs for the legacy local comparison are proved
for the actual selected self-product and solution-dependent rotation. -/
def inputs : GivenSingleNativeLocalInputs.Inputs Ω F μ h D J u₀ U := by
  let A (i : ι) := NativeHaarChannels.channels _ (driverModel Ω F μ h D J u₀ U M i)
  refine {
    products := products Ω F μ h J M
    I₀ := fun i ↦ (A i).I₀
    I₁ := fun i ↦ (A i).I₁
    natural₀ := fun i ↦ (A i).natural₀
    natural₁ := fun i ↦ (A i).natural₁
    B₀ := fun _ ↦ NativeScalarBDG.constant 3
    B₁ := fun _ ↦ NativeScalarBDG.constant 3
    Bnext := fun _ ↦ 1
    B := fun _ ↦ NativeScalarBDGAll.constant
    bdg₀ := fun i ↦ (A i).bdg₀
    bdg₁ := fun i ↦ (A i).bdg₁
    bdgNext := fun i ↦ (A i).bdgNext
    girsanov := fun i ↦ NativeScalarModel.girsanov (driverModel Ω F μ h D J u₀ U M i)
    recognizedBDG := fun i ↦ NativeHaarChannels.changed _ (driverModel Ω F μ h D J u₀ U M i)
    finiteIto := fun i ↦ NativeScalarModel.finiteIto (physicalModel Ω F μ h J M i)
    locality := fun i ↦ NativeScalarModel.locality (physicalModel Ω F μ h J M i)
    fubini := fun i ↦ NativeScalarModel.fubini (physicalModel Ω F μ h J M i)
    novikov := fun i ↦ NativeScalarModel.novikov (physicalModel Ω F μ h J M i)
    bdg := fun i p hp ↦ NativeScalarModel.bdg (physicalModel Ω F μ h J M i) p hp }

end SHEStochastic.NativeSingleLocalInputs
