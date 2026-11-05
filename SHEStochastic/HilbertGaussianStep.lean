module

public import SHEStochastic.HilbertSimpleIntegral
public import SHEStochastic.HilbertGaussianFinite
public import SHEStochastic.CharacteristicL2
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.HilbertGaussianStep
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

variable {Ω C ι : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ] {H : ℝ≥0}

/-- The actual native integral of a frozen Hilbert-valued row has the
conditional Gaussian characteristic function in the full original past.
The proof takes the Hilbert sum of the finite-coordinate identities. -/
theorem condExp_step (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    (s t : ℝ≥0) (hst : s ≤ t) (htH : t ≤ H)
    (R : Ω → C) (hR : StronglyMeasurable[F s] R) (K : ℝ) (hK : ∀ ω, ‖R ω‖ ≤ K) :
    letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
    μ[fun ω ↦ Complex.exp (((FiniteCylindricalIto.rawIntegral P.toCoordinates e
      (HilbertSimpleInputs.embedding F μ H (HilbertSimpleInputs.step s t hst htH R hR K hK))) ω : ℂ)
        * Complex.I) | F s] =ᵐ[μ]
      (fun ω ↦ (Real.exp (-(((t - s : ℝ≥0) : ℝ) * ‖R ω‖ ^ 2) / 2) : ℂ)) := by
  classical
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  let V := HilbertSimpleInputs.step s t hst htH R hR K hK
  let Z : Lp ℝ 2 μ := FiniteCylindricalIto.rawIntegral P.toCoordinates e (HilbertSimpleInputs.embedding F μ H V)
  let Zi (i : ι) : Lp ℝ 2 μ := FiniteScalarIto.simpleLp P.toCoordinates i
    (HilbertSimpleInputs.map (innerSL ℝ (e i)) V)
  let d : ℝ := (t - s : ℝ≥0)
  let damp : ℝ → ℂ := fun x ↦ Real.exp (-(d * x) / 2)
  let gS (S : Finset ι) (ω : Ω) := damp (∑ i ∈ S, (inner ℝ (e i) (R ω)) ^ 2)
  let g (ω : Ω) := damp (‖R ω‖ ^ 2)
  have hdamp : Continuous damp := by fun_prop
  have hdamp_le (x : ℝ) (hx : 0 ≤ x) : ‖damp x‖ ≤ 1 := by
    dsimp [damp]
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    apply Real.exp_le_one_iff.mpr
    have hd : 0 ≤ d := NNReal.coe_nonneg _
    linarith [mul_nonneg hd hx]
  have hci (i : ι) : StronglyMeasurable[F s] (fun ω ↦ inner ℝ (e i) (R ω)) :=
    (innerSL ℝ (e i)).continuous.comp_stronglyMeasurable hR
  have hgs (S : Finset ι) : StronglyMeasurable[F s] (gS S) :=
    hdamp.comp_stronglyMeasurable (Finset.stronglyMeasurable_fun_sum S
      (fun i _ ↦ (hci i).pow 2))
  have hg : StronglyMeasurable[F s] g := hdamp.comp_stronglyMeasurable (hR.norm.pow 2)
  have hgi : Integrable g μ := Integrable.of_bound (hg.mono (F.le s)).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun ω ↦ hdamp_le _ (sq_nonneg _))
  have hz : HasSum Zi Z := HilbertSimpleIntegral.hasSum P.toCoordinates e V
  have hZi : ∀ᵐ ω ∂μ, ∀ i : ι, Zi i ω =
      inner ℝ (e i) (R ω) * (P.W i t ω - P.W i s ω) := by
    apply ae_all_iff.mpr
    intro i
    exact HilbertSimpleIntegral.mapped_step_ae P.toCoordinates i (innerSL ℝ (e i)) s t hst htH R hR K hK
  have hpartial (S : Finset ι) : (∑ i ∈ S, Zi i : Lp ℝ 2 μ) =ᵐ[μ]
      (fun ω ↦ ∑ i ∈ S, inner ℝ (e i) (R ω) * (P.W i t ω - P.W i s ω)) := by
    filter_upwards [Lp.coeFn_finsetSum S Zi, hZi] with ω hs hω
    rw [hs]
    simp only [Finset.sum_apply]
    exact Finset.sum_congr rfl (fun i _ ↦ hω i)
  have hCE (S : Finset ι) :
      μ[fun ω ↦ Complex.exp ((((∑ i ∈ S, Zi i : Lp ℝ 2 μ) ω : ℝ) : ℂ) * Complex.I) | F s]
        =ᵐ[μ] gS S := by
    have hp := (hpartial S).mono fun ω hω ↦ congrArg
      (fun x : ℝ ↦ Complex.exp ((x : ℂ) * Complex.I)) hω
    exact (condExp_congr_ae hp).trans
      (HilbertGaussianFinite.finset_step P e S s t hst htH hR.measurable)
  have hvar (ω : Ω) : HasSum (fun i ↦ (inner ℝ (e i) (R ω)) ^ 2) (‖R ω‖ ^ 2) := by
    simpa only [real_inner_comm (R ω), ← pow_two, real_inner_self_eq_norm_sq] using
      e.hasSum_inner_mul_inner (R ω) (R ω)
  change μ[fun ω ↦ Complex.exp ((Z ω : ℂ) * Complex.I) | F s] =ᵐ[μ] g
  refine (ae_eq_condExp_of_forall_setIntegral_eq (F.le s) (CharacteristicL2.phase_integrable Z)
    (fun _ _ _ ↦ hgi.integrableOn) (fun A hA _ ↦ ?_) hg.aestronglyMeasurable).symm
  have hleft := ((CharacteristicL2.setExpectation_continuous (μ := μ) A).tendsto Z).comp hz
  have hEq (S : Finset ι) : CharacteristicL2.setExpectation A (∑ i ∈ S, Zi i) =
      ∫ ω in A, gS S ω ∂μ := by
    unfold CharacteristicL2.setExpectation
    rw [← setIntegral_condExp (F.le s) (CharacteristicL2.phase_integrable _) hA]
    exact integral_congr_ae ((hCE S).filter_mono ae_restrict_le)
  change Filter.Tendsto (fun S : Finset ι ↦ CharacteristicL2.setExpectation A (∑ i ∈ S, Zi i))
    Filter.atTop (𝓝 (CharacteristicL2.setExpectation A Z)) at hleft
  simp only [hEq] at hleft
  have hright : Filter.Tendsto (fun S : Finset ι ↦ ∫ ω in A, gS S ω ∂μ) Filter.atTop
      (𝓝 (∫ ω in A, g ω ∂μ)) := by
    apply tendsto_integral_filter_of_norm_le_const
    · exact Filter.Eventually.of_forall fun S ↦ ((hgs S).mono (F.le s)).aestronglyMeasurable.restrict
    · exact ⟨1, Filter.Eventually.of_forall fun S ↦ Filter.Eventually.of_forall fun ω ↦
        hdamp_le _ (Finset.sum_nonneg fun i _ ↦ sq_nonneg _)⟩
    · exact Filter.Eventually.of_forall fun ω ↦ (hdamp.tendsto _).comp (hvar ω)
  exact tendsto_nhds_unique hright hleft

end SHEStochastic.HilbertGaussianStep
