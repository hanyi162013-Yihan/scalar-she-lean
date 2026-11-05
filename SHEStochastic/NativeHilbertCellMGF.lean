module

public import SHEStochastic.NativeCellPullout
public import SHEStochastic.NativeUnitGaussianCell
public import SHEStochastic.HilbertUnitDirection
public import SHEStochastic.ConditionalGaussianMGF

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.NativeHilbertCellMGF
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

variable {Ω C ι : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {H : ℝ≥0}

local notation "ν" => FiniteScalarIto.inputMeasure F μ H

def value (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    (s t : ℝ≥0) (hst : s ≤ t) (htH : t ≤ H)
    (R : Ω → C) (hR : StronglyMeasurable[F s] R) (K : ℝ) (hK : ∀ ω, ‖R ω‖ ≤ K) : Lp ℝ 2 μ :=
  FiniteCylindricalIto.rawIntegral P.toCoordinates e (HilbertSimpleInputs.embedding F μ H
    (HilbertSimpleInputs.step s t hst htH R hR K hK))

/-- Exact exponential freezing for a bounded random Hilbert row. The
constant is its actual squared norm and has no dimension dependence.
Normalization and the old past-multiplier theorem reduce the proof to
the already recognized scalar Gaussian cell. -/
theorem freeze (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    (s t : ℝ≥0) (hst : s ≤ t) (htH : t ≤ H)
    (R : Ω → C) (hR : StronglyMeasurable[F s] R) (K : ℝ) (hK0 : 0 ≤ K) (hK : ∀ ω, ‖R ω‖ ≤ K)
    (v : C) (hv : ‖v‖ = 1) (a : ℝ) :
    Integrable (fun ω ↦ Real.exp (a * value P e s t hst htH R hR K hK ω)) μ ∧
      μ[fun ω ↦ Real.exp (a * value P e s t hst htH R hR K hK ω) | F s] =ᵐ[μ]
        (fun ω ↦ Real.exp (a ^ 2 * ((t - s : ℝ≥0) : ℝ) * ‖R ω‖ ^ 2 / 2)) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := F.predictable
  let Rhat (ω : Ω) := HilbertUnitDirection.direction v (R ω)
  have hRhat : StronglyMeasurable[F s] Rhat := HilbertUnitDirection.stronglyMeasurable_direction hR v
  have hn (ω : Ω) : ‖Rhat ω‖ = 1 := HilbertUnitDirection.norm_direction v hv (R ω)
  let Z := value P e s t hst htH R hR K hK
  let Y := value P e s t hst htH Rhat hRhat 1 (fun ω ↦ (hn ω).le)
  have hY := NativeUnitGaussianCell.law_and_independent P e s t hst htH Rhat hRhat hn
  change HasLaw (Y : Ω → ℝ) (gaussianReal 0 (t - s)) μ ∧
    Indep (MeasurableSpace.comap (Y : Ω → ℝ) (borel ℝ)) (F s) μ at hY
  have hb (ω : Ω) : |‖R ω‖| ≤ K := by simpa only [abs_norm] using hK ω
  have hprod (ω : Ω) : ‖‖R ω‖ • Rhat ω‖ ≤ K * 1 := by
    rw [HilbertUnitDirection.recover, mul_one]
    exact hK ω
  have hp := NativeCellPullout.pullout P e s t hst htH Rhat hRhat 1 (fun ω ↦ (hn ω).le)
    (fun ω ↦ ‖R ω‖) hR.norm K hK0 hb hprod
  have hInput : HilbertSimpleInputs.embedding F μ H
      (HilbertSimpleInputs.step s t hst htH (fun ω ↦ ‖R ω‖ • Rhat ω)
        (hR.norm.smul hRhat) (K * 1) hprod) =
      HilbertSimpleInputs.embedding F μ H (HilbertSimpleInputs.step s t hst htH R hR K hK) := by
    apply Lp.ext
    filter_upwards [HilbertSimpleInputs.embedding_ae F μ H
      (HilbertSimpleInputs.step s t hst htH (fun ω ↦ ‖R ω‖ • Rhat ω)
        (hR.norm.smul hRhat) (K * 1) hprod),
      HilbertSimpleInputs.embedding_ae F μ H (HilbertSimpleInputs.step s t hst htH R hR K hK)]
      with p hleft hright
    rw [hleft, hright]
    change (HilbertSimpleInputs.step s t hst htH (fun ω ↦ ‖R ω‖ • Rhat ω)
      (hR.norm.smul hRhat) (K * 1) hprod).val p.1 p.2 =
      (HilbertSimpleInputs.step s t hst htH R hR K hK).val p.1 p.2
    simp only [HilbertSimpleInputs.step_apply]
    by_cases hm : p.1 ∈ Set.Ioc s t <;> simp [hm, Rhat, HilbertUnitDirection.recover]
  rw [hInput] at hp
  change Z =ᵐ[μ] (fun ω ↦ ‖R ω‖ * Y ω) at hp
  have hX : Measurable[F s] (fun ω ↦ a * ‖R ω‖) := measurable_const.mul hR.norm.measurable
  have hXb (ω : Ω) : |a * ‖R ω‖| ≤ |a| * K := by
    rw [abs_mul, abs_norm]
    exact mul_le_mul_of_nonneg_left (hK ω) (abs_nonneg _)
  obtain ⟨hi, hCE⟩ := ConditionalGaussianMGF.freeze (F s) (F.le s) hX
    (Lp.stronglyMeasurable Y).measurable hY.1 hY.2 (|a| * K) hXb
  have he : (fun ω ↦ Real.exp (a * Z ω)) =ᵐ[μ]
      (fun ω ↦ Real.exp ((a * ‖R ω‖) * Y ω)) := hp.mono fun ω hω ↦ by
    change Real.exp (a * Z ω) = Real.exp ((a * ‖R ω‖) * Y ω)
    rw [hω, mul_assoc]
  refine ⟨hi.congr he.symm, ?_⟩
  apply (condExp_congr_ae he).trans
  filter_upwards [hCE] with ω hω
  exact hω.trans (congrArg Real.exp (by ring))

/-- The exact normalized Hilbert Gaussian exponential has conditional
mean one, with the variance correction supplied by the original row. -/
theorem density (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    (s t : ℝ≥0) (hst : s ≤ t) (htH : t ≤ H)
    (R : Ω → C) (hR : StronglyMeasurable[F s] R) (K : ℝ) (hK0 : 0 ≤ K) (hK : ∀ ω, ‖R ω‖ ≤ K)
    (v : C) (hv : ‖v‖ = 1) (a : ℝ) :
    Integrable (fun ω ↦ Real.exp (a * value P e s t hst htH R hR K hK ω -
      a ^ 2 * ((t - s : ℝ≥0) : ℝ) * ‖R ω‖ ^ 2 / 2)) μ ∧
      μ[fun ω ↦ Real.exp (a * value P e s t hst htH R hR K hK ω -
        a ^ 2 * ((t - s : ℝ≥0) : ℝ) * ‖R ω‖ ^ 2 / 2) | F s] =ᵐ[μ] fun _ ↦ 1 := by
  obtain ⟨hi, hCE⟩ := freeze P e s t hst htH R hR K hK0 hK v hv a
  have hA : StronglyMeasurable[F s]
      (fun ω ↦ a ^ 2 * ((t - s : ℝ≥0) : ℝ) * ‖R ω‖ ^ 2 / 2) := by
    letI : MeasurableSpace Ω := F s
    have hRn : StronglyMeasurable (fun ω ↦ ‖R ω‖) := hR.norm
    fun_prop
  exact ConditionalGaussianMGF.compensate (F s) (F.le s) hi hA
    (fun ω ↦ div_nonneg (mul_nonneg
      (mul_nonneg (sq_nonneg _) (NNReal.coe_nonneg _)) (sq_nonneg _)) (by norm_num)) hCE

end SHEStochastic.NativeHilbertCellMGF
