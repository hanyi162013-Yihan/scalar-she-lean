module

public import SHEStochastic.JointStateDriverPath
public import SHEStochastic.GaussianCharacteristicMartingale
public import SHEStochastic.PastedCharacteristicMartingale

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 900000
noncomputable section

namespace SHEStochastic.JointDriverCharacteristic
open MeasureTheory ProbabilityTheory SHE Matrix
open StoppedPathPasting PastedPastTests AdaptedCanonicalPathTests
open GaussianCharacteristicMartingale PastedCharacteristicFunctional
open scoped NNReal InnerProductSpace

variable {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [Countable ι] [DecidableEq ι]

/-- A finite continuous linear functional of the countable driver,
without imposing any norm or summability on the full driver sequence. -/
def row {n : ℕ} (a : Fin n → ι) (r : WordRecursion.State n) :
    JointStateDriverPath.State V ι →L[ℝ] ℝ :=
  { toFun z := ∑ i : Fin n, r i * z.2 (a i)
    map_add' z w := by simp [Finset.mul_sum, mul_add, Finset.sum_add_distrib]
    map_smul' c z := by simp [Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]
    cont := by fun_prop }

theorem row_apply {n : ℕ} (a : Fin n → ι) (r : WordRecursion.State n)
    (z : JointStateDriverPath.State V ι) :
    row (V := V) a r z = inner ℝ (WithLp.toLp 2 (fun i ↦ z.2 (a i))) r := by
  simp only [row, ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk,
    PiLp.inner_apply, WithLp.ofLp_toLp, RCLike.inner_apply, conj_trivial]

variable {Ω : Type*} [MeasurableSpace Ω]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
  (H : ℝ≥0) (P : FiniteScalarIto.Family F μ H ι)
  (X : Ω → Path H (JointStateDriverPath.State V ι))

theorem value_eq {n : ℕ} (a : Fin n → ι) (r : WordRecursion.State n)
    (hcoord : ∀ ω t i, (X ω t).2 i-(X ω (origin H)).2 i =
      P.W i (toNN H t) ω-P.W i 0 ω) (q : ℝ≥0) (ω : Ω) :
    value H (row (V := V) a r) (variance a r) (X ω) (clock H q) =
      Complex.exp (((phase μ P a r (min q H) ω-phase μ P a r 0 ω : ℝ) : ℂ) * Complex.I +
        (variance a r * (min q H : ℝ≥0) : ℝ)) := by
  unfold value
  congr 1
  have he : row (V := V) a r (X ω (clock H q)-X ω (origin H)) =
      phase μ P a r (min q H) ω-phase μ P a r 0 ω := by
    rw [row_apply, phase, phase, ← inner_sub_left]
    congr 1
    apply PiLp.ext
    intro i
    change (X ω (clock H q)).2 (a i)-(X ω (origin H)).2 (a i) =
      P.W (a i) (min q H) ω-P.W (a i) 0 ω
    simpa only [toNN_clock] using hcoord ω (clock H q) (a i)
  rw [he]
  rfl

theorem source_martingale {n : ℕ} (a : Fin n → ι) (r : WordRecursion.State n)
    (hcoord : ∀ ω t i, (X ω t).2 i-(X ω (origin H)).2 i =
      P.W i (toNN H t) ω-P.W i 0 ω) :
    Martingale (fun q ω ↦ value H (row (V := V) a r) (variance a r) (X ω) (clock H q)) F μ := by
  have he : (fun q ω ↦ value H (row (V := V) a r) (variance a r) (X ω) (clock H q)) =
      fun q ω ↦ Complex.exp
        (((phase μ P a r (min q H) ω-phase μ P a r 0 ω : ℝ) : ℂ) * Complex.I +
          (variance a r * (min q H : ℝ≥0) : ℝ)) := by
    funext q ω
    exact value_eq F μ H P X a r hcoord q ω
  rw [he]
  exact family_centered μ P a r

/-- Original stopped characteristic identities use the same source
Brownian family and the entire state-driver past test. -/
theorem stopped_identity
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
    (hadapt : ∀ t : Time H, Measurable[F (toNN H t)]
      (fun ω ↦ X ω t))
    (hcoord : ∀ ω t i, (X ω t).2 i-(X ω (origin H)).2 i =
      P.W i (toNN H t) ω-P.W i 0 ω)
    (exit : Ω → Time H)
    (hstop : IsStoppingTime F (fun ω ↦ (toNN H (exit ω) : WithTop ℝ≥0)))
    {n : ℕ} (a : Fin n → ι) (r : WordRecursion.State n)
    (s t : Time H) (hst : s.val ≤ t.val)
    (test : BoundedContinuousFunction (Path H (JointStateDriverPath.State V ι)) ℝ)
    (htest : UsesPast H s test) :
    (∫ ω, test (X ω) •
      (value H (row (V := V) a r) (variance a r) (X ω) (pastTime H (exit ω) t) -
        value H (row (V := V) a r) (variance a r) (X ω) (pastTime H (exit ω) s)) ∂μ) = 0 := by
  let M := fun q ω ↦ value H (row (V := V) a r) (variance a r) (X ω) (clock H q)
  have hM : Martingale M F μ := source_martingale F μ H P X a r hcoord
  have hc (ω : Ω) : Continuous (fun q ↦ M q ω) :=
    (continuous_value H (row (V := V) a r) (variance a r)).comp
      (continuous_const.prodMk (continuous_clock H))
  have hh := ContinuousStoppedMartingaleTests.stopped_weighted_increment_smul μ F M hM hc
    (fun ω ↦ (toNN H (exit ω) : WithTop ℝ≥0)) hstop (toNN H s) (toNN H t) hst
    (fun ω ↦ test (X ω)) (past_test_measurable H F X hadapt s test htest) ‖test‖
    (fun ω ↦ test.norm_coe_le_norm _)
  have he (q : Time H) (ω : Ω) : stoppedProcess M
      (fun ω ↦ (toNN H (exit ω) : WithTop ℝ≥0)) (toNN H q) ω =
        value H (row (V := V) a r) (variance a r) (X ω) (pastTime H (exit ω) q) := by
    simp only [stoppedProcess, ← WithTop.coe_min, WithTop.untopA_eq_untop WithTop.coe_ne_top,
      WithTop.untop_coe, M, clock_min]
  simpa only [he] using hh

theorem law_identity
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
    (hX : Measurable X)
    (hadapt : ∀ t : Time H, Measurable[F (toNN H t)] (fun ω ↦ X ω t))
    (hcoord : ∀ ω t i, (X ω t).2 i-(X ω (origin H)).2 i =
      P.W i (toNN H t) ω-P.W i 0 ω)
    {n : ℕ} (a : Fin n → ι) (r : WordRecursion.State n) :
    PastedCharacteristicMartingale.Identity H (row (V := V) a r) (variance a r) (μ.map X) := by
  intro s t hst test htest
  have hh := ContinuousStoppedMartingaleTests.weighted_increment_smul μ F _
    (source_martingale F μ H P X a r hcoord) (toNN H s) (toNN H t) hst
    (fun ω ↦ test (X ω)) (past_test_measurable H F X hadapt s test htest) ‖test‖
    (fun ω ↦ test.norm_coe_le_norm _)
  simp only [clock_toNN] at hh
  have hv (q : Time H) : Continuous (fun x : Path H (JointStateDriverPath.State V ι) ↦
      value H (row (V := V) a r) (variance a r) x q) :=
    (continuous_value H (row (V := V) a r) (variance a r)).comp (continuous_id.prodMk continuous_const)
  calc
    _ = ∫ ω, test (X ω) • (value H (row (V := V) a r) (variance a r) (X ω) t -
        value H (row (V := V) a r) (variance a r) (X ω) s) ∂μ :=
      integral_map_of_stronglyMeasurable hX (test.continuous.smul ((hv t).sub (hv s))).stronglyMeasurable
    _ = 0 := hh

end SHEStochastic.JointDriverCharacteristic
