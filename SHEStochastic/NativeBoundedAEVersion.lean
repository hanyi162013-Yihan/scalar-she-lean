module

public import SHEStochastic.NativeBoundedMartingaleVersion

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.NativeBoundedAEVersion
open MeasureTheory ProbabilityTheory SHE SHE.PredictableL2 SHE.StoppedItoInputs Filter
open scoped NNReal ENNReal Topology

variable {Ω C ι : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {H : ℝ≥0}

/-- The existing countable-left-grid construction gives a predictable
continuous version almost surely in the ORIGINAL filtration. No null
completeness or change of probability space is required. -/
theorem exists_version (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    (u : Process (E := C) F μ H) (M : ℝ≥0)
    (hu : ∀ᵐ p ∂(energyMeasure μ H).trim (predictable_le_product F), ‖u p‖ ≤ M) :
    ∃ Y : ℝ≥0 → Ω → ℝ,
      (∀ᵐ ω ∂μ, Continuous (Y · ω)) ∧ StronglyAdapted F Y ∧
      StronglyMeasurable[F.predictable] (Function.uncurry Y) ∧ Martingale Y F μ ∧
      (∀ t, Y t =ᵐ[μ] (FiniteCylindricalIto.terminalIto P.toCoordinates e).integral (stop F μ H t u)) ∧
      (∀ t (p : ℝ≥0), MemLp (Y t) p μ) ∧
      (∀ᵐ ω ∂μ, ∀ t, Y t ω = Y (min t H) ω) := by
  let J := FiniteCylindricalIto.terminalIto P.toCoordinates e
  obtain ⟨U, hUc, hUr⟩ := FiniteCylindricalIto.continuousStoppedVersions P e u
  choose Z hZa hZr using fun t ↦ stopped_integral_adapted F μ H J t u
  let V (t : ℝ≥0) (z : Unit × Ω) := Z (min t H) z.2
  have hV (t : ℝ≥0) : @Measurable (Unit × Ω) ℝ
      ((inferInstance : MeasurableSpace Unit).prod (F t)) _ (V t) :=
    ((hZa (min t H)).mono (F.mono (min_le_left t H))).measurable.comp measurable_snd
  obtain ⟨Y0, hYp, hYrep⟩ := JointContinuousVersion.exists_joint F μ V hV
    (fun (_ : Unit) t ω ↦ U (min t H) ω)
    (fun _ ω ↦ (hUc ω).comp (continuous_id.min continuous_const))
    (fun _ t ↦ by
      have hr : U (min t H) =ᵐ[μ] J.integral (stop F μ H (min t H) u) := hUr (min t H)
      exact (hZr (min t H)).symm.trans hr.symm)
  let Y (t : ℝ≥0) (ω : Ω) := Y0 ((), (t, ω))
  have hp : StronglyMeasurable[F.predictable] (Function.uncurry Y) :=
    hYp.comp_measurable (measurable_const.prodMk measurable_id)
  have ha : StronglyAdapted F Y := (show IsStronglyPredictable F Y from hp).stronglyAdapted
  have hrep (t : ℝ≥0) : Y t =ᵐ[μ] J.integral (stop F μ H t u) := by
    have hh : Y t =ᵐ[μ] (fun ω ↦ U (min t H) ω) := (hYrep ()).mono fun ω hω ↦ hω t
    have hr := hUr (min t H)
    simp only [NNReal.coe_min] at hr
    rw [NativeBoundedMartingaleVersion.stop_cap] at hr
    exact hh.trans hr
  refine ⟨Y, ?_, ha, hp, ConditionalBracket.martingale J
    (FiniteCylindricalIto.pastLocality P e) u ha hrep, hrep, ?_, ?_⟩
  · filter_upwards [hYrep ()] with ω hω
    change Continuous (fun t ↦ Y0 ((), (t, ω)))
    simpa only [hω, Function.comp_def, id_eq] using (hUc ω).comp (continuous_id.min continuous_const)
  · intro t p
    exact (memLp_congr_ae (hrep t)).mpr (NativeBoundedMoments.memLp_stopped P e u M hu t p)
  · filter_upwards [hYrep ()] with ω hω
    intro t
    change Y0 ((), (t, ω)) = Y0 ((), (min t H, ω))
    simp only [hω, min_assoc, min_self]

end SHEStochastic.NativeBoundedAEVersion
