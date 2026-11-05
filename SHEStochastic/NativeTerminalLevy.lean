module

public import SHEStochastic.NativeStoppedGram
public import SHEStochastic.ConditionalBracket

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section

namespace SHEStochastic.NativeTerminalLevy
open MeasureTheory ProbabilityTheory SHE SHE.PredictableL2 SHE.StoppedItoInputs SHE.PastItoInputs
open NativeRowRepresentatives NativeStoppedGram
open scoped NNReal ENNReal

variable {Ω C ι : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {H : ℝ≥0}

local notation "ν" => FiniteScalarIto.inputMeasure F μ H

/-- Full finite-dimensional Brownian recognition for same-integral
versions, with every observation time retained and independence from the
entire original past. No Ito formula, BDG or Levy theorem is an input. -/
theorem finiteBrownianLaw (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    {n : ℕ} (R : Fin n → Process (E := C) F μ H) (X : Fin n → ℝ≥0 → Ω → ℝ)
    (G : Matrix (Fin n) (Fin n) ℝ)
    (hsame : ∀ t : ℝ≥0, t ≤ H → ∀ᵐ ω ∂μ, ∀ i,
      X i t ω = (FiniteCylindricalIto.terminalIto P.toCoordinates e).integral (stop F μ H t (R i)) ω)
    (hG : ∀ᵐ p ∂energyMeasure μ H, ∀ i j, inner ℝ (R i p) (R j p) = G i j) :
    FiniteBrownianLawOn F μ H X G := by
  classical
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  constructor
  · intro t htH
    let S (i : Fin n) := FiniteCylindricalIto.processTransport (stop F μ H (t i) (R i))
    have hSa (i : Fin n) : ∀ᵐ p ∂ν, p.1 ≤ 0 → S i p = 0 := by
      filter_upwards [FilteredItoCLM.ae_fst_mem_Ioc_trimMeasure_T (𝓖 := F) (μ := μ) H
        (B := fun _ _ ↦ (0 : ℝ)) (fun _ ↦ measurable_const)] with p hp hz
      exact False.elim ((not_le.mpr hp.1) hz)
    have hl := (HilbertGaussianVector.law_and_independent P e 0 zero_le S hSa
      (stopped_profiles R G hG t)).1
    have hcov := stopped_gram R G hG t htH
    change Matrix.gram ℝ S = _ at hcov
    rw [hcov] at hl
    apply hl.congr
    have he : ∀ᵐ ω ∂μ, ∀ i : Fin n,
        X i (t i) ω = FiniteCylindricalIto.rawIntegral P.toCoordinates e (S i) ω :=
      ae_all_iff.mpr (fun i ↦ (hsame (t i) (htH i)).mono fun ω hω ↦ hω i)
    filter_upwards [he] with ω hω
    apply congrArg (WithLp.toLp 2)
    funext i
    exact hω i
  · intro s t hst htH
    let B (i : Fin n) := FiniteCylindricalIto.processTransport (post F μ H s (stop F μ H t (R i)))
    have hBa (i : Fin n) : ∀ᵐ p ∂ν, p.1 ≤ s → B i p = 0 := by
      filter_upwards [band_transport_ae s t (R i)] with p hp hs
      rw [hp]
      exact Set.indicator_of_notMem (fun h ↦ (not_lt.mpr hs) h.1) _
    have hi := (HilbertGaussianVector.law_and_independent P e s (hst.trans htH) B hBa
      (band_profiles R G hG s t)).2
    have he : (fun ω ↦ WithLp.toLp 2 (fun i ↦ X i t ω - X i s ω)) =ᵐ[μ]
        HilbertGaussianVector.nativeVector P e B := by
      have hinc : ∀ᵐ ω ∂μ, ∀ i : Fin n,
          FiniteCylindricalIto.rawIntegral P.toCoordinates e (B i) ω =
            (FiniteCylindricalIto.terminalIto P.toCoordinates e).integral (stop F μ H t (R i)) ω -
            (FiniteCylindricalIto.terminalIto P.toCoordinates e).integral (stop F μ H s (R i)) ω :=
        ae_all_iff.mpr (fun i ↦ ConditionalBracket.integral_increment
          (FiniteCylindricalIto.terminalIto P.toCoordinates e) hst (R i))
      filter_upwards [hsame t htH, hsame s (hst.trans htH), hinc] with ω ht hs hω
      apply congrArg (WithLp.toLp 2)
      funext i
      exact ((congrArg₂ (· - ·) (ht i) (hs i)).trans (hω i).symm)
    have hii := ConditionalCharacteristic.indep_comap_congr (F s) he hi
    rw [← BorelSpace.measurable_eq (α := EuclideanSpace ℝ (Fin n))] at hii
    exact hii

/-- Discharge of the existing external package-5 interface for the
selected native cylindrical integral. -/
theorem standardTerminalLevy (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C) :
    StandardTerminalLevy (FiniteCylindricalIto.terminalIto P.toCoordinates e) := by
  intro n R X G _hX _hcontinuous hsame hG
  exact finiteBrownianLaw P e R X G hsame hG

end SHEStochastic.NativeTerminalLevy
