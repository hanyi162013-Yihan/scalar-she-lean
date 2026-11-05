module

public import SHEStochastic.FiniteStateDriverCoordinates
public import SHEStochastic.NativeBrownianCoordinates
public import SHE.ContinuousPredictable

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
noncomputable section

namespace SHEStochastic.NativeStateDriverCoordinates
open MeasureTheory SHE SHE.PredictableL2 GaussianItoTest FiniteStateDriverCoordinates
open scoped NNReal ENNReal

variable {Ω C ι : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {H : ℝ≥0} (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
  {s d : ℕ} (driver : Fin d → ι)

/-- Actual driver coordinates, centered pathwise at time zero. -/
def driverVector (t : ℝ≥0) (sample : Ω) : State d :=
  WithLp.toLp 2 (fun j ↦ P.W (driver j) t sample - P.W (driver j) 0 sample)

theorem continuous_driver (sample : Ω) : Continuous (fun t ↦ driverVector P driver t sample) :=
  (PiLp.continuous_toLp 2 (fun _ : Fin d ↦ ℝ)).comp
    (continuous_pi fun j ↦ (P.continuous (driver j) sample).sub continuous_const)

theorem predictable_driver : StronglyMeasurable[F.predictable] (Function.uncurry (driverVector P driver)) := by
  apply ContinuousPredictable.stronglyMeasurable F (driverVector P driver) ?_ (continuous_driver P driver)
  intro t
  apply (PiLp.continuous_toLp 2 (fun _ : Fin d ↦ ℝ)).comp_stronglyMeasurable
  have hm (j : Fin d) : Measurable[F t]
      (fun sample ↦ P.W (driver j) t sample - P.W (driver j) 0 sample) :=
    (P.adapted (driver j) t).sub ((P.adapted (driver j) 0).mono (F.mono zero_le) le_rfl)
  exact (@measurable_pi_lambda Ω (Fin d) (fun _ ↦ ℝ) (F t) _ _ hm).stronglyMeasurable

def rows (R : Fin s → Process (E := C) F μ H) : Fin (s + d) → Process (E := C) F μ H :=
  Fin.addCases R (fun j ↦ RawCylindricalCoordinates.row F μ H (e : ι → C) (driver j))

def augmented (Y : ℝ≥0 × Ω → State s) (p : ℝ≥0 × Ω) : State (s + d) :=
  append (Y p) (driverVector P driver p.1 p.2)

theorem continuous_augmented (Y : ℝ≥0 × Ω → State s)
    (hc : ∀ sample, Continuous (fun t ↦ Y (t, sample))) (sample : Ω) :
    Continuous (fun t ↦ augmented P driver Y (t, sample)) :=
  continuous_append.comp ((hc sample).prodMk (continuous_driver P driver sample))

theorem predictable_augmented (Y : ℝ≥0 × Ω → State s)
    (hp : StronglyMeasurable[F.predictable] Y) :
    StronglyMeasurable[F.predictable] (augmented P driver Y) :=
  continuous_append.comp_stronglyMeasurable (hp.prodMk (predictable_driver P driver))

/-- Appending the given Brownian coordinates appends their constant
basis inputs to the SAME native integral. No representation theorem or
replacement noise is required. -/
theorem represents_random (R : Fin s → Process (E := C) F μ H) (z : Ω → State s)
    (Y : ℝ≥0 × Ω → State s) (t : ℝ≥0) (ht : t ≤ H)
    (hRep : (fun sample ↦ Y (t, sample)) =ᵐ[μ]
      (fun sample ↦ StandardFiniteIto.vectorIntegral F μ H (FiniteCylindricalIto.terminalIto P.toCoordinates e) (z sample) R t sample)) :
    (fun sample ↦ augmented P driver Y (t, sample)) =ᵐ[μ]
      (fun sample ↦ StandardFiniteIto.vectorIntegral F μ H (FiniteCylindricalIto.terminalIto P.toCoordinates e)
        (append (z sample) (0 : State d)) (rows e driver R) t sample) := by
  have hr := ae_all_iff.mpr (fun j : Fin d ↦ FiniteCylindricalIto.coordinate_integral P e (driver j) t ht)
  have h0 := ae_all_iff.mpr (fun j : Fin d ↦ FiniteScalarIto.zero_ae P.toCoordinates (driver j))
  filter_upwards [hRep, hr, h0] with sample hy hr h0
  apply PiLp.ext
  refine Fin.addCases ?_ ?_
  · intro i
    simp only [augmented, append_left]
    have hi := congrArg (fun w : State s ↦ w i) hy
    change Y (t, sample) i = z sample i +
      (FiniteCylindricalIto.terminalIto P.toCoordinates e).integral
        (StoppedItoInputs.stop F μ H t (R i)) sample at hi
    simpa only [StandardFiniteIto.vectorIntegral, append_left, rows, Fin.addCases_left] using hi
  · intro j
    simp only [augmented, append_right]
    change P.W (driver j) t sample - P.W (driver j) 0 sample =
      append (z sample) (0 : State d) (Fin.natAdd s j) +
        (FiniteCylindricalIto.terminalIto P.toCoordinates e).integral
          (StoppedItoInputs.stop F μ H t (rows e driver R (Fin.natAdd s j))) sample
    simp only [append_right, PiLp.zero_apply, rows, Fin.addCases_right]
    rw [hr j, h0 j, sub_zero, zero_add]

/-- Deterministic-initial specialization. -/
theorem represents (R : Fin s → Process (E := C) F μ H) (z : State s)
    (Y : ℝ≥0 × Ω → State s) (t : ℝ≥0) (ht : t ≤ H)
    (hRep : (fun sample ↦ Y (t, sample)) =ᵐ[μ]
      StandardFiniteIto.vectorIntegral F μ H (FiniteCylindricalIto.terminalIto P.toCoordinates e) z R t) :
    (fun sample ↦ augmented P driver Y (t, sample)) =ᵐ[μ]
      StandardFiniteIto.vectorIntegral F μ H (FiniteCylindricalIto.terminalIto P.toCoordinates e)
        (append z (0 : State d)) (rows e driver R) t := by
  exact represents_random P e driver R (fun _ ↦ z) Y t ht hRep

end SHEStochastic.NativeStateDriverCoordinates
