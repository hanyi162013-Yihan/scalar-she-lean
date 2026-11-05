module

public import SHEStochastic.StandardNativeProductIto
public import SHEStochastic.NativeIntegralUniqueness
public import SHEStochastic.TerminalItoExt

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
noncomputable section

namespace SHEStochastic.NativeProductIdentification
open MeasureTheory SHE SHE.PredictableL2 SHE.OrthogonalItoChannels
open scoped NNReal ENNReal

variable {Ω Ξ ι C : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
  [Countable ι] [DecidableEq ι] [Inhabited ι]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {G : Filtration ℝ≥0 ‹MeasurableSpace Ξ›}
  {μ : Measure Ω} {ν : Measure Ξ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {H : ℝ≥0}
  (P : FiniteScalarIto.Family F μ H ι) (Q : FiniteScalarIto.Family G ν H ι)
  (e : HilbertBasis ι ℝ C)
  (A : IndependentProductItoData F G μ ν H
    (FiniteCylindricalIto.terminalIto P.toCoordinates e)
    (FiniteCylindricalIto.terminalIto Q.toCoordinates e))

theorem first_coordinate (i : ι) (t : ℝ≥0) (ht : t ≤ H) :
    RawCylindricalCoordinates.value (IndependentNoiseCompletion.filtration μ ν F G)
      (IndependentNoiseCompletion.measure μ ν) H
      (ProductHilbertBasis.basis e : Sum ι ι → Both C) A.integral (Sum.inl i) t =ᵐ[IndependentNoiseCompletion.measure μ ν]
        fun z ↦ P.W i t z.1 := by
  have hr := CylindricalPullback.stopped_basis_ae
    (F := F) (G := IndependentNoiseCompletion.filtration μ ν F G) (H := H) Prod.fst
    (IndependentNoiseCompletion.fst_preserving μ ν) (e : ι → C)
    (ProductHilbertBasis.basis e : Sum ι ι → Both C) (left (C := C)) Sum.inl
    (fun j ↦ (ProductHilbertBasis.basis_inl e j).symm) i t
  have hh := A.first _ _ hr
  exact hh.trans ((IndependentNoiseCompletion.fst_preserving μ ν).quasiMeasurePreserving.ae
    (FiniteCylindricalIto.coordinate_integral P e i t ht))

theorem second_coordinate (i : ι) (t : ℝ≥0) (ht : t ≤ H) :
    RawCylindricalCoordinates.value (IndependentNoiseCompletion.filtration μ ν F G)
      (IndependentNoiseCompletion.measure μ ν) H
      (ProductHilbertBasis.basis e : Sum ι ι → Both C) A.integral (Sum.inr i) t =ᵐ[IndependentNoiseCompletion.measure μ ν]
        fun z ↦ Q.W i t z.2 := by
  have hr := CylindricalPullback.stopped_basis_ae
    (F := G) (G := IndependentNoiseCompletion.filtration μ ν F G) (H := H) Prod.snd
    (IndependentNoiseCompletion.snd_preserving μ ν) (e : ι → C)
    (ProductHilbertBasis.basis e : Sum ι ι → Both C) (right (C := C)) Sum.inr
    (fun j ↦ (ProductHilbertBasis.basis_inr e j).symm) i t
  have hh := A.second _ _ hr
  exact hh.trans ((IndependentNoiseCompletion.snd_preserving μ ν).quasiMeasurePreserving.ae
    (FiniteCylindricalIto.coordinate_integral Q e i t ht))

/-- Every coherent product choice is the native product integral.
Coordinate compatibility and the retained ordinary locality determine
all predictable inputs by density. This removes dependence on choice. -/
theorem integral_eq : A.integral = NativeProductIto.terminalIto P Q e := by
  apply StandardTerminalIto.ext_integral
  apply DFunLike.ext
  intro u
  apply NativeIntegralUniqueness.integral (ProductBrownianFiniteLaw.family P Q)
    (ProductHilbertBasis.basis e) A.integral A.locality
  intro i t ht
  cases i with
  | inl i => exact first_coordinate P Q e A i t ht
  | inr i => exact second_coordinate P Q e A i t ht

end SHEStochastic.NativeProductIdentification
