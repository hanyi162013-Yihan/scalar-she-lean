module

public import SHEStochastic.NativeConditionalPacketModel
public import SHEStochastic.NativeOriginalConditionalLaw
public import SHE.GivenSingleNativeGlobalUniqueness

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.NativeSingleGlobalInputs
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
local instance : Nontrivial RealHaarInput := ⟨⟨NativeSingleNoiseBasis.basis none, 0, by
  intro h
  have hh := NativeSingleNoiseBasis.basis.orthonormal.norm_eq_one none
  rw [h, norm_zero] at hh
  norm_num at hh⟩⟩
local instance : Nontrivial RealL2 := OriginalNativeFrozenRows.coordinates.symm.toEquiv.nontrivial

variable {ι : Type} [Fintype ι] [Nonempty ι] (Ω : ι → Type) [∀ i, MeasurableSpace (Ω i)]
  (F : ∀ i, Filtration ℝ≥0 (inferInstance : MeasurableSpace (Ω i)))
  (μ : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (μ i)] (H : ℝ≥0)
  (D : SmoothApproximation.ScalarData)
  (J : ∀ i, StandardTerminalIto (C := RealL2) (E := ℝ) (F i) (μ i) H)
  (u₀ : RealL2) (S : ∀ i, SingleNativeHeatEquation.Data (F i) (μ i) H D (J i) u₀)
  (M : ∀ i, NativeScalarModel.Model (J i))

def products : SingleNativeGlobalFamily.Products Ω F μ H J := fun i ↦ NativeScalarModel.products (M i)

def physicalModel (i : ι) : NativeScalarModel.Model
    (SingleNativeGlobalFamily.physical Ω F μ H J (products Ω F μ H J M) i) :=
  NativeScalarModel.selfProduct (M i)
    (SingleNativeGlobalFamily.selected Ω F μ H J (products Ω F μ H J M) i)

include M in
theorem conditionalLaws (hpos : 0<H) (v h : ℝ≥0) (hvh : v+h≤H) (i : ι) :
    ∀ᵐ p ∂OriginalConditionalFamilyStep.pastLaw (SingleNativeGlobalFamily.Space Ω μ)
      (SingleNativeGlobalFamily.filtration Ω F μ) (SingleNativeGlobalFamily.measure Ω μ) H D
      (SingleNativeGlobalFamily.physical Ω F μ H J (products Ω F μ H J M)) u₀
      (SingleNativeGlobalFamily.model Ω F μ H J D u₀ S (products Ω F μ H J M)) v i,
      ∀ n (a : Fin n → HaarNode), FiniteBrownianLawOn (ConditionalCanonicalModelFamily.filtration h)
        (OriginalConditionalFamilyStep.kernel (SingleNativeGlobalFamily.Space Ω μ)
          (SingleNativeGlobalFamily.filtration Ω F μ) (SingleNativeGlobalFamily.measure Ω μ) H D
          (SingleNativeGlobalFamily.physical Ω F μ H J (products Ω F μ H J M)) u₀
          (SingleNativeGlobalFamily.model Ω F μ H J D u₀ S (products Ω F μ H J M)) v h hpos i p) h
        (fun j ↦ CanonicalStateDriverFiltration.coordinate h (a j)) (fun j k ↦ if a j=a k then 1 else 0) :=
  NativeOriginalConditionalLaw.law _ _ H hpos D _ u₀
    (SingleNativeGlobalFamily.model Ω F μ H J D u₀ S (products Ω F μ H J M) i)
    (physicalModel Ω F μ H J M i) (SingleNativeGlobalFamily.contains_null Ω F μ i) v h hvh

/-- Native inputs for arbitrary-horizon bounded comparison. Conditional
packages are derived only on the genuine common-prefix Brownian event. -/
def inputs (hpos : 0<H) : GivenSingleNativeGlobalUniqueness.Inputs Ω F μ H D J u₀ S
    (products Ω F μ H J M) hpos := by
  refine {
    C := fun _ ↦ NativeScalarBDG.constant 3
    bdg := fun i ↦ NativeScalarModel.bdg16 (physicalModel Ω F μ H J M i)
    levy := fun i ↦ NativeScalarModel.levy (physicalModel Ω F μ H J M i)
    locality := fun i ↦ NativeScalarModel.locality (physicalModel Ω F μ H J M i)
    construction := ?_
    localPackages := ?_ }
  · intro v h hh hsmall hvh i p
    exact standardBrownianItoConstruction _ _ h NativeSingleNoiseBasis.basis (CanonicalStateDriverFiltration.coordinate h)
  · intro v h hh hsmall hvh hprefix i
    let κ := OriginalConditionalFamilyStep.kernel (SingleNativeGlobalFamily.Space Ω μ)
      (SingleNativeGlobalFamily.filtration Ω F μ) (SingleNativeGlobalFamily.measure Ω μ) H D
      (SingleNativeGlobalFamily.physical Ω F μ H J (products Ω F μ H J M)) u₀
      (SingleNativeGlobalFamily.model Ω F μ H J D u₀ S (products Ω F μ H J M)) v h hpos
    have hb (j : ι) := conditionalLaws Ω F μ H D J u₀ S M hpos v h hvh j
    have hc (j : ι) : ∀ᵐ p ∂OriginalConditionalFamilyStep.pastLaw (SingleNativeGlobalFamily.Space Ω μ)
        (SingleNativeGlobalFamily.filtration Ω F μ) (SingleNativeGlobalFamily.measure Ω μ) H D
        (SingleNativeGlobalFamily.physical Ω F μ H J (products Ω F μ H J M)) u₀
        (SingleNativeGlobalFamily.model Ω F μ H J D u₀ S (products Ω F μ H J M)) v i,
        ∀ n (a : Fin n → HaarNode), FiniteBrownianLawOn (ConditionalCanonicalModelFamily.filtration h)
          (κ j p) h (fun k ↦ CanonicalStateDriverFiltration.coordinate h (a k))
          (fun k l ↦ if a k=a l then 1 else 0) := by
      rw [hprefix i j]
      exact hb j
    filter_upwards [ae_all_iff.mpr hc] with p hp
    intro A
    refine ⟨?_⟩
    exact @NativeArbitraryLocalUniqueness.inputs ι inferInstance
      (fun _ : ι ↦ ConditionalCanonicalModelFamily.Space h) (fun _ ↦ inferInstance)
      (fun _ ↦ ConditionalCanonicalModelFamily.filtration h) (fun j ↦ κ j p) (fun j ↦ inferInstance)
      h hh (show (h : ℝ)≤1 from hsmall) D
      (fun j ↦ NativeWhiteToPhysicalEquation.physical (ConditionalCanonicalModelFamily.filtration h) (κ j p) h (A j).white)
      (OriginalShiftedSingleModels.known v p) (fun j ↦ (A j).model)
      (fun j ↦ NativeConditionalPacketModel.physicalModel h D (κ j p) _ (A j) (hp j))

end SHEStochastic.NativeSingleGlobalInputs
