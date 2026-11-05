module

public import SHEStochastic.ScalarGirsanovLocalization

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.ScalarGirsanovCappedTransport
open MeasureTheory SHE SHE.PredictableL2 ProbabilityTheory
open scoped NNReal ENNReal

variable {Ω C ι : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ] {H : ℝ≥0}
  (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)

local notation "νin" => FiniteScalarIto.inputMeasure F μ H
local notation "Q" => NativeGirsanovTilt.measure P e

/-- At a deterministic energy cap the true stopped law is equivalent,
with the same continuous coordinate shift and raw stochastic transport. -/
theorem change (hnull : NullCompleteFiltration.ContainsNullSets F μ)
    (u : Lp C 2 νin) (K : ℝ) (hK : 0≤K)
    (hCap : ∀ᵐ ω ∂μ,NativeEnergy.energy u ω≤K) :
    ∃ (_ : IsProbabilityMeasure (Q u)) (R : FiniteScalarIto.Family F (Q u) H ι),
      Q u ≪ μ ∧ μ ≪ Q u ∧
      ∀ (v : Lp C 2 νin) (w : Lp C 2 (FiniteScalarIto.inputMeasure F (Q u) H)),v =ᵐ[νin] w →
        FiniteCylindricalIto.rawIntegral R.toCoordinates e w =ᵐ[Q u]
          (fun ω => FiniteCylindricalIto.rawIntegral P.toCoordinates e v ω+
            NativeCrossEnergy.cross v u ω) := by
  let hQ : IsProbabilityMeasure (Q u) := NativeGirsanovTilt.probability P e u K hK hCap
  let u' := NativeInputEquiv.inverse F μ H u
  have ht : FiniteCylindricalIto.processTransport u'=u := NativeInputEquiv.transport_inverse F μ H u
  have he := NativeBoundedNovikov.energy_transport_ae u'
  rw [ht] at he
  have hCap' : ∀ᵐ ω ∂μ,StochasticExponential.bracket F μ H u' ω≤K := by
    filter_upwards [hCap,he] with ω hc he
    exact he ▸ hc
  have hAbs : Q u ≪ μ ∧ μ ≪ Q u := ScalarDriftDensityLocalization.equivalent μ
    (fun ω => ENNReal.ofReal (NativeExponential.density P e (-1) u ω))
    ((NativeExponential.stronglyMeasurable P e (-1) u).measurable.ennreal_ofReal.aemeasurable)
    (ae_of_all _ fun ω => ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos _))
  have hLaw (n : ℕ) (a : Fin n → ι) : FiniteBrownianLawOn F (Q u) H
      (fun i => ScalarGirsanovCoordinateShift.shift P e u' (a i))
      (fun i j => if a i=a j then 1 else 0) := by
    have h := ScalarGirsanovCoordinateShift.finite_cap P e u' K hK hCap' n a
    change FiniteBrownianLawOn F
      (ExponentialChangeMeasure.measure μ
        (fun ω => (FiniteCylindricalIto.terminalIto P.toCoordinates e).integral u' ω)
        (StochasticExponential.bracket F μ H u')) H _ _ at h
    rwa [←NativeGirsanovRows.measure_transport P e u',ht] at h
  obtain ⟨R,hR⟩ := ScalarGirsanovContinuousFamily.exists_family (η := Q u) P e u' hAbs.1 hnull hLaw
  refine ⟨hQ,R,hAbs.1,hAbs.2,?_⟩
  intro v w h
  have hSame : ScalarGirsanovIntegralTransport.Agrees (F := F) (μ := μ) (η := Q u) (H := H)
      P e u' R.toCoordinates := by
    intro i t _
    exact (hR i).mono (fun _ hω => hω t)
  have hTrans := ScalarGirsanovIntegralTransport.integral (μ := μ) (η := Q u)
    P e u' R.toCoordinates hAbs.1 hSame v w h
  rwa [ht] at hTrans

end SHEStochastic.ScalarGirsanovCappedTransport
