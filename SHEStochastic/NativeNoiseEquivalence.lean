module

public import SHEStochastic.CylindricalProcessPullback
public import SHEStochastic.NoiseRestrictionBounds
public import SHEStochastic.TerminalItoExt

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section

namespace SHEStochastic.NativeNoiseEquivalence
open MeasureTheory SHE SHE.PredictableL2
open scoped NNReal ENNReal

variable {Ω A C ι : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι]
  [NormedAddCommGroup A] [InnerProductSpace ℝ A] [CompleteSpace A]
  [MeasurableSpace A] [BorelSpace A] [SecondCountableTopology A]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ] {H : ℝ≥0}

def basis (L : A ≃ₗᵢ[ℝ] C) (e : HilbertBasis ι ℝ C) : HilbertBasis ι ℝ A :=
  HilbertBasis.ofRepr (L.trans e.repr)

theorem basis_apply (L : A ≃ₗᵢ[ℝ] C) (e : HilbertBasis ι ℝ C) (i : ι) :
    basis L e i = L.symm (e i) := by
  classical
  rw [← (basis L e).repr_symm_single i]
  change (L.trans e.repr).symm (lp.single 2 i (1 : ℝ)) = _
  simp only [LinearIsometryEquiv.symm_trans, LinearIsometryEquiv.trans_apply, e.repr_symm_single]

/-- A fixed unitary change of the noise convention only changes its
Hilbert basis. It keeps every Brownian coordinate and every integral. -/
theorem integral_eq (P : FiniteScalarIto.Family F μ H ι)
    (L : A ≃ₗᵢ[ℝ] C) (e : HilbertBasis ι ℝ C) :
    restrictNoise (FiniteCylindricalIto.terminalIto P.toCoordinates e) L.toLinearIsometry =
      FiniteCylindricalIto.terminalIto P.toCoordinates (basis L e) := by
  apply StandardTerminalIto.ext_integral
  apply DFunLike.ext
  intro u
  have hr := ae_eq_of_ae_eq_trim (NoiseRestrictionBounds.input_ae_trim L.toLinearIsometry u)
  have hh := CylindricalPullback.process_naturality (F := F) (G := F) id
    (MeasurePreserving.id μ) (fun _ ↦ measurable_id) P P (basis L e) e L.toLinearIsometry id
    (fun i ↦ by
      change L (basis L e i) = e i
      rw [basis_apply, LinearIsometryEquiv.apply_symm_apply]) (fun _ _ _ ↦ rfl)
    u (NoiseRestrictionBounds.input L.toLinearIsometry u) (by
      simpa only [FilteredPullback.timeMap, id_eq, Prod.mk.eta] using hr)
  apply Lp.ext
  exact hh

end SHEStochastic.NativeNoiseEquivalence
