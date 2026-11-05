module

public import SHE.CanonicalWordMeasurable
public import SHE.PhysicalWordExpectation
public import SHE.SmoothWords
public import Mathlib.Probability.Kernel.Basic

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-! Conditional physical one-step assembly for the canonical reference.
The initial L² input is frozen on each conditional fiber. No uncountable
family of separately almost-sure identities is evaluated on a diagonal. -/
noncomputable section
namespace SHE.CanonicalConditional
open Set MeasureTheory ProbabilityTheory StoppedFourier Filter
open WordRecursion GaussianItoTest PhysicalIto PhysicalWordExpectation CovarianceEndpoint
open CanonicalCovariance SmoothCylinders ObservationMeasurable

abbrev State (n : ℕ) := WordRecursion.State n
variable [MeasurableSpace CircleL2] [BorelSpace CircleL2]

def initialMean {n : ℕ} (Z : Fin n → Observation) (q : ℝ) (u : CircleL2) : State n :=
  WithLp.toLp 2 (fun i => PhysicalProfile.physicalHeatMean u ((Z i).target - q, (Z i).center))

theorem initialMean_measurable {n : ℕ} (Z : Fin n → Observation) (q : ℝ) :
    Measurable (initialMean Z q) := by
  apply (WithLp.measurable_toLp 2 (Fin n → ℝ)).comp
  apply Measurable.of_eval
  intro i
  exact PhysicalProfile.physicalHeatMean_joint_measurable.comp
    (measurable_id.prodMk (measurable_const (a := ((Z i).target - q, (Z i).center))))

theorem observe_initial_eq {n : ℕ} (Z : Fin n → Observation) (q : ℝ)
    (U : ℝ → CircleL2) (X : ℝ × HeatCircle → ℝ) (u : CircleL2)
    (hU : U q = u) (hZ : ∀ i, q < (Z i).target) :
    observe U X Z q = initialMean Z q u := by
  ext i
  change (if q < (Z i).target then PhysicalProfile.physicalHeatMean (U q) ((Z i).target - q, (Z i).center)
    else X (q, (Z i).center)) = _
  rw [if_pos (hZ i), hU]
  rfl

def referenceAverage (A : ProfileParameters) {n : ℕ} (q s : ℝ) (Z : Fin n → Observation)
    (hqs : q ≤ s) (hZ : ∀ i, s ≤ (Z i).target) (F : State n → ℝ) (u : CircleL2) : ℝ :=
  backward (A.window u q s Z hqs hZ) F q (initialMean Z q u)

theorem referenceAverage_measurable (A : ProfileParameters) {n : ℕ} (q s : ℝ)
    (Z : Fin n → Observation) (hqs : q ≤ s) (hZ : ∀ i, s ≤ (Z i).target)
    {F : State n → ℝ} (hF : Continuous F) {M : ℝ} (hbound : ∀ z, ‖F z‖ ≤ M) :
    Measurable (referenceAverage A q s Z hqs hZ F) := by
  have hmap : Measurable (fun u : CircleL2 => ((u, q), initialMean Z q u)) :=
    (measurable_id.prodMk measurable_const).prodMk (initialMean_measurable Z q)
  have hm := (A.backward_measurable q s Z hqs hZ hF hbound).comp hmap
  exact hm

/-- Actual canonical reference recursion on conditional fibers. The
remaining hypotheses are precisely the standard conditional Itô input,
its centered martingale, and the conditional initial-state identity.
The actual physical insertion remainder is proved integrable on each
good fiber. -/
theorem conditional_one_step (A : ProfileParameters) {n : ℕ} (q s : ℝ)
    (Z : Fin n → Observation) (hqs : q < s) (hZ : ∀ i, s ≤ (Z i).target)
    {Ω : Type*} [MeasurableSpace Ω] (ν : Measure CircleL2) (κ : Kernel CircleL2 Ω) [IsMarkovKernel κ]
    (U : (CircleL2 × Ω) × ℝ → CircleL2) (hU : Measurable U)
    (X : (CircleL2 × Ω) × (ℝ × HeatCircle) → ℝ) (hX : Measurable X)
    (N : CircleL2 → (ℝ → State n → ℝ) → Ω → ℝ)
    (hIto : ∀ᵐ u ∂ν, FiniteItoInput (κ u)
      (fun ω => observe (fun t => U ((u, ω), t)) (fun p => X ((u, ω), p)) Z)
      (fun ω t => CovarianceMatrix.densityMatrix (fun p => A.coefficient (X ((u, ω), p))) Z t)
      q s (N u))
    {F : State n → ℝ} (hF : BoundedSmooth F)
    (hN : ∀ᵐ u ∂ν, Integrable (N u (backward (A.window u q s Z hqs.le hZ) F)) (κ u) ∧
      (∫ ω, N u (backward (A.window u q s Z hqs.le hZ) F) ω ∂κ u) = 0)
    (hinitial : ∀ᵐ u ∂ν, ∀ᵐ ω ∂κ u, U ((u, ω), q) = u) :
    ∀ᵐ u ∂ν,
      Integrable (fun ω => wordRemainder (A.window u q s Z hqs.le hZ) A.coefficient
        (fun t => U ((u, ω), t)) (fun p => X ((u, ω), p)) F) (κ u) ∧
      (∫ ω, F (observe (fun t => U ((u, ω), t)) (fun p => X ((u, ω), p)) Z s) ∂κ u) =
        referenceAverage A q s Z hqs.le hZ F u +
          ∫ ω, wordRemainder (A.window u q s Z hqs.le hZ) A.coefficient
            (fun t => U ((u, ω), t)) (fun p => X ((u, ω), p)) F ∂κ u := by
  let : NormedAddCommGroup (State n →L[ℝ] State n →L[ℝ] ℝ) := inferInstance
  obtain ⟨M, hM⟩ := hF.norm_bound
  obtain ⟨L, hL⟩ := hF.fderiv.norm_bound
  obtain ⟨B, hB⟩ := hF.hessian_norm_bound
  obtain ⟨K, hKn, hK⟩ := hF.hessian_lipschitz
  have hBn : 0 ≤ B := (norm_nonneg (GaussianTaylor.hessian F 0)).trans (hB 0)
  have haB (z : ℝ) : |A.coefficient z| ≤ A.upper := by
    rw [abs_of_nonneg (A.lower_pos.le.trans (A.lower_bound z))]
    exact A.upper_bound z
  filter_upwards [hIto, hN, hinitial] with u hItou hNu hinitu
  have hUu : Measurable (fun p : Ω × ℝ => U ((u, p.1), p.2)) :=
    hU.comp ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
  have hXu : Measurable (fun p : Ω × (ℝ × HeatCircle) => X ((u, p.1), p.2)) :=
    hX.comp ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
  have hXfiber : ∀ᵐ ω ∂κ u, Measurable (fun p : ℝ × HeatCircle => X ((u, ω), p)) :=
    Eventually.of_forall (fun ω => hXu.comp (measurable_const.prodMk measurable_id))
  have hY := observe_joint_measurable Z hUu hXu
  have hYq : Measurable (fun ω => observe (fun t => U ((u, ω), t)) (fun p => X ((u, ω), p)) Z q) :=
    hY.comp (measurable_id.prodMk measurable_const)
  have hYs : Measurable (fun ω => observe (fun t => U ((u, ω), t)) (fun p => X ((u, ω), p)) Z s) :=
    hY.comp (measurable_id.prodMk measurable_const)
  have hh := weighted_one_step_expectation (κ u) (A.window u q s Z hqs.le hZ) A.coefficient A.measurable
    (fun ω t => U ((u, ω), t)) (fun ω p => X ((u, ω), p)) hXfiber A.upper_nonneg haB (N u) hItou
    (hF.smooth.of_le (by simp)) hM hL hB hBn hKn hK hYq hYs (fun _ => 1) measurable_const
    (by norm_num : (0 : ℝ) ≤ 1) (fun _ => by norm_num)
    (by simpa only [one_mul] using hNu.1) (by simpa only [one_mul] using hNu.2)
  simp only [one_mul] at hh
  refine ⟨hh.1, ?_⟩
  have hinitmean : (fun ω => gaussianSemigroup (A.window u q s Z hqs.le hZ).coefficient Z q s F
      (observe (fun t => U ((u, ω), t)) (fun p => X ((u, ω), p)) Z q)) =ᵐ[κ u]
      fun _ => referenceAverage A q s Z hqs.le hZ F u := by
    filter_upwards [hinitu] with ω hω
    rw [observe_initial_eq Z q _ _ u hω (fun i => hqs.trans_le (hZ i))]
    exact congrFun (PhysicalIto.backward_eq_semigroup (A.window u q s Z hqs.le hZ) F ⟨le_rfl, hqs.le⟩).symm _
  have he := integral_congr_ae hinitmean
  simp only [integral_const, probReal_univ, one_smul] at he
  have hhEq := hh.2
  change (∫ ω, F (observe (fun t => U ((u, ω), t)) (fun p => X ((u, ω), p)) Z s) ∂κ u) =
    (∫ ω, gaussianSemigroup (A.window u q s Z hqs.le hZ).coefficient Z q s F
      (observe (fun t => U ((u, ω), t)) (fun p => X ((u, ω), p)) Z q) ∂κ u) +
        ∫ ω, wordRemainder (A.window u q s Z hqs.le hZ) A.coefficient
          (fun t => U ((u, ω), t)) (fun p => X ((u, ω), p)) F ∂κ u at hhEq
  rw [he] at hhEq
  exact hhEq

end SHE.CanonicalConditional
