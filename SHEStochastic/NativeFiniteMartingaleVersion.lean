module

public import SHEStochastic.NativeMartingaleVersion
public import SHEStochastic.NativeFiniteIto
public import SHE.ContinuousPredictable

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.NativeFiniteMartingaleVersion
open MeasureTheory SHE SHE.PredictableL2 SHE.GaussianItoTest Filter
open scoped ENNReal NNReal

variable {Ω C ι : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {H : ℝ≥0} {n : ℕ}

/-- A finite family of existing native scalar martingales gives the
continuous predictable vector required by the proved universal Ito formula. -/
theorem exists_version (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    (hnull : NullCompleteFiltration.ContainsNullSets F μ)
    (R : Fin n → Process (E := C) F μ H) (z : State n) :
    ∃ Y : ℝ≥0 × Ω → State n, StronglyMeasurable[F.predictable] Y ∧
      (∀ ω, Continuous (fun t ↦ Y (t, ω))) ∧
      ∀ t : ℝ≥0, (fun ω ↦ Y (t, ω)) =ᵐ[μ]
        StandardFiniteIto.vectorIntegral F μ H (FiniteCylindricalIto.terminalIto P.toCoordinates e) z R t := by
  choose M hc ha hp hm hr using fun i : Fin n ↦ NativeMartingaleVersion.exists_version P e hnull (R i)
  let Y (p : ℝ≥0 × Ω) : State n := WithLp.toLp 2 (fun i ↦ z i + M i p.1 p.2)
  have hY : StronglyMeasurable[F.predictable] Y := by
    letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
    exact (PiLp.continuous_toLp 2 (fun _ : Fin n ↦ ℝ)).comp_stronglyMeasurable
      (measurable_pi_lambda fun i ↦ measurable_const.add (hp i).measurable).stronglyMeasurable
  refine ⟨Y, hY, ?_, ?_⟩
  · intro ω
    exact (PiLp.continuous_toLp 2 (fun _ : Fin n ↦ ℝ)).comp (continuous_pi fun i ↦ continuous_const.add (hc i ω))
  · intro t
    filter_upwards [ae_all_iff.mpr (fun i ↦ hr i t)] with ω hω
    apply PiLp.ext
    intro i
    exact congrArg (fun r : ℝ ↦ z i + r) (hω i)

/-- A time-zero measurable initial vector can be added to the same
native continuous martingale version. No moment bound on that initial
vector is needed for this version or for compact-test Itô calculus. -/
theorem exists_random_version (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    (hnull : NullCompleteFiltration.ContainsNullSets F μ)
    (R : Fin n → Process (E := C) F μ H) (Z : Ω → State n) (hZ : StronglyMeasurable[F 0] Z) :
    ∃ Y : ℝ≥0 × Ω → State n, StronglyMeasurable[F.predictable] Y ∧
      (∀ sample, Continuous (fun t ↦ Y (t, sample))) ∧
      ∀ t : ℝ≥0, (fun sample ↦ Y (t, sample)) =ᵐ[μ]
        (fun sample ↦ StandardFiniteIto.vectorIntegral F μ H (FiniteCylindricalIto.terminalIto P.toCoordinates e)
          (Z sample) R t sample) := by
  obtain ⟨M, hp, hc, hr⟩ := exists_version P e hnull R (0 : State n)
  have hz : StronglyMeasurable[F.predictable] (fun p : ℝ≥0 × Ω ↦ Z p.2) :=
    ContinuousPredictable.stronglyMeasurable F (fun _ ↦ Z)
      (fun t ↦ hZ.mono (F.mono zero_le)) (fun _ ↦ continuous_const)
  refine ⟨fun p ↦ Z p.2 + M p, hz.add hp, ?_, ?_⟩
  · intro sample
    convert (continuous_const : Continuous (fun _ : ℝ≥0 ↦ Z sample)).add (hc sample) using 1 <;> rfl
  · intro t
    filter_upwards [hr t] with sample hh
    apply PiLp.ext
    intro i
    have hi := congrArg (fun v : State n ↦ v i) hh
    change M (t, sample) i = 0 + (FiniteCylindricalIto.terminalIto P.toCoordinates e).integral
      (StoppedItoInputs.stop F μ H t (R i)) sample at hi
    change Z sample i + M (t, sample) i = Z sample i + _
    rw [hi, zero_add]

/-- The finite native vector has exactly its prescribed initial state. -/
theorem initial_random (J : StandardTerminalIto (C := C) (E := ℝ) F μ H)
    (R : Fin n → Process (E := C) F μ H) (z : Ω → State n) (Y : ℝ≥0 × Ω → State n)
    (hRep : (fun ω ↦ Y (0, ω)) =ᵐ[μ] (fun sample ↦ StandardFiniteIto.vectorIntegral F μ H J (z sample) R 0 sample)) :
    (fun ω ↦ Y (0, ω)) =ᵐ[μ] z := by
  filter_upwards [hRep, Lp.coeFn_zero ℝ 2 μ] with ω hy hz
  apply PiLp.ext
  intro i
  have hi := congrArg (fun w : State n ↦ w i) hy
  change Y (0, ω) i = z ω i + J.integral (StoppedItoInputs.stop F μ H 0 (R i)) ω at hi
  rw [StoppedItoInputs.stop_zero, map_zero] at hi
  exact hi.trans (by
    change z ω i + (0 : Lp ℝ 2 μ) ω = z ω i
    rw [hz]
    exact add_zero (z ω i))

theorem initial (J : StandardTerminalIto (C := C) (E := ℝ) F μ H)
    (R : Fin n → Process (E := C) F μ H) (z : State n) (Y : ℝ≥0 × Ω → State n)
    (hRep : (fun ω ↦ Y (0, ω)) =ᵐ[μ] StandardFiniteIto.vectorIntegral F μ H J z R 0) :
    (fun ω ↦ Y (0, ω)) =ᵐ[μ] fun _ ↦ z := by
  exact initial_random J R (fun _ ↦ z) Y hRep

end SHEStochastic.NativeFiniteMartingaleVersion
