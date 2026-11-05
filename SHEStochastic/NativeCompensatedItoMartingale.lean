module

public import SHEStochastic.NativeFiniteIto
public import SHEStochastic.NativeMartingaleVersion
public import SHEStochastic.FiniteItoStoppedVersions

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section

namespace SHEStochastic.NativeCompensatedItoMartingale
open MeasureTheory SHE SHE.PredictableL2 SHE.GaussianItoTest SHE.StoppedItoInputs Filter Set
open scoped NNReal ENNReal

variable {d : ℕ} {G dG : ℝ → State d → ℝ}

theorem regular_prefix {H T : ℝ≥0} (hG : RegularTest 0 H G dG) (hT : T ≤ H) :
    RegularTest 0 T G dG := by
  have hs : uIcc (0 : ℝ) T ⊆ uIcc (0 : ℝ) H := by
    calc
      _ = Icc (0 : ℝ) T := by convert uIcc_of_le T.property using 1 <;> rfl
      _ ⊆ Icc (0 : ℝ) H := Icc_subset_Icc le_rfl hT
      _ = _ := by convert (uIcc_of_le H.property).symm using 1 <;> rfl
  refine ⟨hG.continuous, hG.state_smooth, hG.gradient_continuous, hG.hessian_continuous,
    fun z ↦ (hG.time_absolutelyContinuous z).mono hs, ?_, hG.derivative_measurable,
    hG.derivative_state_continuous, ?_, hG.bounds⟩
  · filter_upwards [hG.time_derivative] with t ht htm z
    exact ht ⟨htm.1, htm.2.trans_le hT⟩ z
  · obtain ⟨v, hv, hb⟩ := hG.derivative_envelope
    exact ⟨v, hv.mono_set hs, fun t ht ↦ hb t ⟨ht.1, ht.2.trans_le hT⟩⟩

variable {Ω C ι : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (R : Fin d → Process (E := C) F μ H) (Y : ℝ≥0 × Ω → State d)

def compensated (G dG : ℝ → State d → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  G (min t H) (Y (min t H, ω)) - G 0 (Y (0, ω)) -
    ∫ r in (0 : ℝ)..(min t H : ℝ≥0), dG r (Y (r.toNNReal, ω)) + (1 / 2 : ℝ) *
      GaussianTaylorAverage.covarianceAction (StandardFiniteIto.rowCovariance F μ H R ω r)
        (GaussianTaylor.hessian (G r) (Y (r.toNNReal, ω)))

/-- The compensated finite Ito expression is the SAME stopped native
integral of the original gradient row, including for random L2 rows. -/
theorem represents_random (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    (z : Ω → State d) (hY : StronglyMeasurable[F.predictable] Y)
    (hc : ∀ ω, Continuous (fun t ↦ Y (t, ω)))
    (hRep : ∀ t : ℝ≥0, t ≤ H → (fun ω ↦ Y (t, ω)) =ᵐ[μ]
      (fun ω ↦ StandardFiniteIto.vectorIntegral F μ H (FiniteCylindricalIto.terminalIto P.toCoordinates e) (z ω) R t ω))
    (G dG : ℝ → State d → ℝ) (hG : RegularTest 0 H G dG) (t : ℝ≥0) :
    compensated F μ H R Y G dG t =ᵐ[μ]
      (FiniteCylindricalIto.terminalIto P.toCoordinates e).integral (stop F μ H t
        (FiniteItoNoise.gradientProcess F μ H Y hY R G (FiniteItoNoise.regular_admissible hG))) := by
  let J := FiniteCylindricalIto.terminalIto P.toCoordinates e
  let u := FiniteItoNoise.gradientProcess F μ H Y hY R G (FiniteItoNoise.regular_admissible hG)
  let s := min t H
  have hh := NativeFiniteItoInterval.formula_random P e R z Y hY hc hRep
    0 s zero_le (min_le_right t H) G dG (regular_prefix hG (min_le_right t H))
  simp only [NNReal.coe_zero] at hh
  have hn : FiniteItoNoise.noise F μ H Y hY R J 0 s G = J.integral (stop F μ H s u) := by
    rw [FiniteItoNoise.noise_eq F μ H Y hY R J 0 s G (FiniteItoNoise.regular_admissible hG),
      stop_zero, sub_zero]
  have hcap : stop F μ H s u = stop F μ H t u := by
    calc
      _ = stop F μ H t (stop F μ H H u) := by
        simp only [StoppedInputAlgebra.stop_stop]
        convert congrArg (fun r : ℝ ↦ stop F μ H r u) (NNReal.coe_min t H) using 1 <;> rfl
      _ = _ := by rw [FiniteItoStoppedVersions.stop_horizon]
  change FiniteItoNoise.noise F μ H Y hY R (FiniteCylindricalIto.terminalIto P.toCoordinates e) 0 s G = _ at hn
  rw [hn, hcap] at hh
  filter_upwards [hh] with ω hω
  change G (s : ℝ) (Y (s, ω)) - G 0 (Y (0, ω)) - _ = _
  linarith

/-- Deterministic-initial specialization of the same proof. -/
theorem represents (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    (z : State d) (hY : StronglyMeasurable[F.predictable] Y)
    (hc : ∀ ω, Continuous (fun t ↦ Y (t, ω)))
    (hRep : ∀ t : ℝ≥0, t ≤ H → (fun ω ↦ Y (t, ω)) =ᵐ[μ]
      StandardFiniteIto.vectorIntegral F μ H (FiniteCylindricalIto.terminalIto P.toCoordinates e) z R t)
    (G dG : ℝ → State d → ℝ) (hG : RegularTest 0 H G dG) (t : ℝ≥0) :
    compensated F μ H R Y G dG t =ᵐ[μ]
      (FiniteCylindricalIto.terminalIto P.toCoordinates e).integral (stop F μ H t
        (FiniteItoNoise.gradientProcess F μ H Y hY R G (FiniteItoNoise.regular_admissible hG))) := by
  exact represents_random F μ H R Y P e (fun _ ↦ z) hY hc hRep G dG hG t

/-- A genuine martingale follows from the checked Ito formula and the
original integral's conditional centering. Integrability and adaptation
are inherited through the exact L2 representatives. -/
theorem martingale_random (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    (hnull : NullCompleteFiltration.ContainsNullSets F μ)
    (z : Ω → State d) (hY : StronglyMeasurable[F.predictable] Y)
    (hc : ∀ ω, Continuous (fun t ↦ Y (t, ω)))
    (hRep : ∀ t : ℝ≥0, t ≤ H → (fun ω ↦ Y (t, ω)) =ᵐ[μ]
      (fun ω ↦ StandardFiniteIto.vectorIntegral F μ H (FiniteCylindricalIto.terminalIto P.toCoordinates e) (z ω) R t ω))
    (G dG : ℝ → State d → ℝ) (hG : RegularTest 0 H G dG) :
    Martingale (compensated F μ H R Y G dG) F μ := by
  let J := FiniteCylindricalIto.terminalIto P.toCoordinates e
  let u := FiniteItoNoise.gradientProcess F μ H Y hY R G (FiniteItoNoise.regular_admissible hG)
  have hr (t : ℝ≥0) : compensated F μ H R Y G dG t =ᵐ[μ] (J.integral (stop F μ H t u) : Ω → ℝ) :=
    represents_random F μ H R Y P e z hY hc hRep G dG hG t
  have ha : StronglyAdapted F (compensated F μ H R Y G dG) := by
    apply NullCompleteFiltration.stronglyAdapted_of_versions F μ hnull
    intro t
    obtain ⟨Z, hZ, he⟩ := stopped_integral_adapted F μ H J t u
    exact ⟨Z, hZ, (hr t).trans he⟩
  exact ConditionalBracket.martingale J (FiniteCylindricalIto.pastLocality P e) u ha hr

/-- Deterministic-initial specialization of the same proof. -/
theorem martingale (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    (hnull : NullCompleteFiltration.ContainsNullSets F μ)
    (z : State d) (hY : StronglyMeasurable[F.predictable] Y)
    (hc : ∀ ω, Continuous (fun t ↦ Y (t, ω)))
    (hRep : ∀ t : ℝ≥0, t ≤ H → (fun ω ↦ Y (t, ω)) =ᵐ[μ]
      StandardFiniteIto.vectorIntegral F μ H (FiniteCylindricalIto.terminalIto P.toCoordinates e) z R t)
    (G dG : ℝ → State d → ℝ) (hG : RegularTest 0 H G dG) :
    Martingale (compensated F μ H R Y G dG) F μ := by
  exact martingale_random F μ H R Y P e hnull (fun _ ↦ z) hY hc hRep G dG hG

end SHEStochastic.NativeCompensatedItoMartingale
