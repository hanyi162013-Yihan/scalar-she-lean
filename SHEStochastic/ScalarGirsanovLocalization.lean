module

public import SHEStochastic.ScalarGirsanovContinuousFamily
public import SHEStochastic.ScalarGirsanovIntegralTransport

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.ScalarGirsanovLocalization
open MeasureTheory SHE SHE.PredictableL2
open scoped NNReal ENNReal

variable {Ω C ι : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {H : ℝ≥0} (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)

local notation "νin" => FiniteScalarIto.inputMeasure F μ H
local notation "νt" => MathFin.ItoIntegralCLM.timeMeasure_T H
local notation "Q" => NativeGirsanovTilt.measure P e

/-- Once the actual stopped-law energy estimate is proved, the same
unstopped control changes to an equivalent probability law and a
continuous Brownian family. All compatible stochastic integrals are
transported with their original sign and time-fibre correction. -/
theorem change (hnull : NullCompleteFiltration.ContainsNullSets F μ)
    (u : Lp C 2 νin) (U : ℕ → Lp C 2 νin)
    (hCap : ∀ k : ℕ,∀ᵐ ω ∂μ,NativeEnergy.energy (U k) ω≤(k : ℝ))
    (hGood : ∀ k : ℕ,∀ᵐ ω ∂μ,NativeEnergy.energy u ω<(k : ℝ) →
      ∀ᵐ t ∂νt,U k (t,ω)=u (t,ω))
    (K : ℝ≥0) (hEnergy : ∀ k : ℕ,
      (∫⁻ ω,ENNReal.ofReal (NativeEnergy.energy u ω) ∂Q (U k))≤K) :
    ∃ (_ : IsProbabilityMeasure (Q u)) (R : FiniteScalarIto.Family F (Q u) H ι),
      Q u ≪ μ ∧ μ ≪ Q u ∧
      (∀ i,∀ᵐ ω ∂μ,∀ t,R.W i t ω=ScalarGirsanovCoordinateShift.shift P e
        (NativeInputEquiv.inverse F μ H u) i t ω) ∧
      ∀ (v : Lp C 2 νin) (w : Lp C 2 (FiniteScalarIto.inputMeasure F (Q u) H)),v =ᵐ[νin] w →
        FiniteCylindricalIto.rawIntegral R.toCoordinates e w =ᵐ[Q u]
          (fun ω => FiniteCylindricalIto.rawIntegral P.toCoordinates e v ω+
            NativeCrossEnergy.cross v u ω) := by
  have hMass := ScalarNativeStoppedTilt.mass_one P e (-1) u U hCap hGood K hEnergy
  let hQ : IsProbabilityMeasure (Q u) := ScalarGirsanovUncappedLaw.probability_of_mass_one P e u hMass
  have hAbs : Q u ≪ μ ∧ μ ≪ Q u := ScalarDriftDensityLocalization.equivalent μ
    (fun ω => ENNReal.ofReal (NativeExponential.density P e (-1) u ω))
    ((NativeExponential.stronglyMeasurable P e (-1) u).measurable.ennreal_ofReal.aemeasurable)
    (ae_of_all _ fun ω => ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos _))
  let u' := NativeInputEquiv.inverse F μ H u
  have hLaw := ScalarGirsanovUncappedLaw.finite_law P e u U hMass hCap hGood
  obtain ⟨R,hR⟩ := ScalarGirsanovContinuousFamily.exists_family (η := Q u) P e u' hAbs.1 hnull hLaw
  refine ⟨hQ,R,hAbs.1,hAbs.2,hR,?_⟩
  intro v w he
  have hSame : ScalarGirsanovIntegralTransport.Agrees (F := F) (μ := μ) (η := Q u) (H := H)
      P e u' R.toCoordinates := by
    intro i t _
    exact (hR i).mono (fun _ hω => hω t)
  have hTrans := ScalarGirsanovIntegralTransport.integral (μ := μ) (η := Q u)
    P e u' R.toCoordinates hAbs.1 hSame v w he
  rw [NativeInputEquiv.transport_inverse] at hTrans
  exact hTrans

end SHEStochastic.ScalarGirsanovLocalization
