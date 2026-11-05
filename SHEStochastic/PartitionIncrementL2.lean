module

public import SHEStochastic.ConditionalOrthogonalSums
public import SHEStochastic.L2EnergyContinuity
public import SHE.StoppedDampingClock
public import MathFin.Foundations.ItoIntegralBrownian
public import Mathlib.MeasureTheory.SpecificCodomains.WithLp

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
noncomputable section

namespace SHEStochastic.PartitionIncrementL2
open MeasureTheory ProbabilityTheory SHE SHE.PredictableL2 SHE.StoppedItoInputs
open MathFin.QuadraticVariationL2
open scoped NNReal ENNReal Topology

variable {Ω C : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {H : ℝ≥0}

def increment (J : StandardTerminalIto (C := C) (E := ℝ) F μ H)
    (u : Process (E := C) F μ H) (n : ℕ) (i : ℕ) : Lp ℝ 2 μ :=
  J.integral (stop F μ H (unifPart H n (i + 1)) u) -
    J.integral (stop F μ H (unifPart H n i) u)

theorem adapted (J : StandardTerminalIto (C := C) (E := ℝ) F μ H)
    (u : Process (E := C) F μ H) (n i : ℕ) :
    AEStronglyMeasurable[F (unifPart H n (i + 1))] (increment J u n i) μ := by
  obtain ⟨Z, hZ, heZ⟩ := stopped_integral_adapted F μ H J (unifPart H n (i + 1)) u
  obtain ⟨W, hW, heW⟩ := stopped_integral_adapted F μ H J (unifPart H n i) u
  exact ((hZ.aestronglyMeasurable.congr heZ.symm).sub
    ((hW.mono (F.mono (MathFin.ItoIntegralBrownian.unifPart_mono H n (Nat.le_succ i)))).aestronglyMeasurable.congr heW.symm)).congr (Lp.coeFn_sub _ _).symm

theorem centered (J : StandardTerminalIto (C := C) (E := ℝ) F μ H)
    (hlocal : StandardTerminalPastLocality J) (u : Process (E := C) F μ H) (n i : ℕ) :
    μ[(increment J u n i : Ω → ℝ) | F (unifPart H n i)] =ᵐ[μ] (fun _ ↦ 0) := by
  have hi : increment J u n i = J.integral
      (PastItoInputs.post F μ H (unifPart H n i)
        (stop F μ H (unifPart H n (i + 1)) u)) := by
    rw [PastItoAlgebra.post_stop_eq_sub F μ H _ _
      (MathFin.ItoIntegralBrownian.unifPart_mono H n (Nat.le_succ i)), map_sub]
    rfl
  rw [hi]
  exact ConditionalBracket.condExp_post_zero J hlocal _ _

/-- The sum of squared L² norms of partition increments is bounded by the
original row energy, uniformly in partition size. -/
theorem sum_norm_sq_le (J : StandardTerminalIto (C := C) (E := ℝ) F μ H)
    (hlocal : StandardTerminalPastLocality J) (u : Process (E := C) F μ H) (n : ℕ) :
    (∑ i : Fin n, ‖increment J u n i‖ ^ 2) ≤ ‖u‖ ^ 2 := by
  have hτ := MathFin.ItoIntegralBrownian.unifPart_mono H n
  have hpy := ConditionalOrthogonalSums.norm_sum_sq_intervals F
    (fun i : Fin n ↦ unifPart H n i) (fun i ↦ unifPart H n (i + 1))
    (fun i ↦ increment J u n i) Finset.univ
    (fun i _ j _ hij ↦ hτ (Nat.succ_le_of_lt (show (i : ℕ) < j from hij)))
    (fun i _ ↦ adapted J u n i) (fun i _ ↦ centered J hlocal u n i)
  have hs : (∑ i : Fin n, increment J u n i) =
      J.integral (stop F μ H (unifPart H n n) u) - J.integral (stop F μ H 0 u) := by
    rw [Fin.sum_univ_eq_sum_range (increment J u n)]
    simp only [increment]
    rw [Finset.sum_range_sub (fun i ↦ J.integral (stop F μ H (unifPart H n i) u))]
    simp [unifPart]
  rw [← hpy, hs, stop_zero, map_zero, sub_zero, J.integral.norm_map]
  exact pow_le_pow_left₀ (norm_nonneg _) (Lp.norm_le_norm_of_ae_le
    (StoppedInputParameter.norm_le_ae F μ H u _)) 2

/-- The increment array uses the Euclidean norm over cells. -/
def array (J : StandardTerminalIto (C := C) (E := ℝ) F μ H)
    (u : Process (E := C) F μ H) (n : ℕ) (ω : Ω) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun i ↦ increment J u n i ω)

theorem memLp_array (J : StandardTerminalIto (C := C) (E := ℝ) F μ H)
    (u : Process (E := C) F μ H) (n : ℕ) : MemLp (array J u n) 2 μ :=
  MemLp.of_eval_piLp (fun i ↦ Lp.memLp (increment J u n i))

def embedding (J : StandardTerminalIto (C := C) (E := ℝ) F μ H)
    (u : Process (E := C) F μ H) (n : ℕ) : Lp (EuclideanSpace ℝ (Fin n)) 2 μ :=
  (memLp_array J u n).toLp (array J u n)

theorem embedding_ae (J : StandardTerminalIto (C := C) (E := ℝ) F μ H)
    (u : Process (E := C) F μ H) (n : ℕ) : embedding J u n =ᵐ[μ] array J u n :=
  (memLp_array J u n).coeFn_toLp

theorem norm_embedding_sq (J : StandardTerminalIto (C := C) (E := ℝ) F μ H)
    (u : Process (E := C) F μ H) (n : ℕ) :
    ‖embedding J u n‖ ^ 2 = ∑ i : Fin n, ‖increment J u n i‖ ^ 2 := by
  rw [← L2EnergyContinuity.norm_sq]
  have he : (∫ ω, ‖embedding J u n ω‖ ^ 2 ∂μ) = ∫ ω, ‖array J u n ω‖ ^ 2 ∂μ :=
    integral_congr_ae ((embedding_ae J u n).mono fun ω hω ↦ congrArg (fun x ↦ ‖x‖ ^ 2) hω)
  rw [he]
  simp only [array, EuclideanSpace.real_norm_sq_eq]
  rw [integral_finsetSum _ (fun (i : Fin n) _ ↦ (Lp.memLp (increment J u n i)).integrable_sq)]
  exact Finset.sum_congr rfl (fun i _ ↦ (MathFin.ItoIntegralL2.lp_two_norm_sq _).symm)

theorem norm_embedding_le (J : StandardTerminalIto (C := C) (E := ℝ) F μ H)
    (hlocal : StandardTerminalPastLocality J) (u : Process (E := C) F μ H) (n : ℕ) :
    ‖embedding J u n‖ ≤ ‖u‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_embedding_sq]
  exact sum_norm_sq_le J hlocal u n

theorem increment_sub (J : StandardTerminalIto (C := C) (E := ℝ) F μ H)
    (u v : Process (E := C) F μ H) (n i : ℕ) :
    increment J (u - v) n i = increment J u n i - increment J v n i := by
  simp only [increment, StoppedDampingClock.stop_sub, map_sub]
  abel

theorem embedding_sub (J : StandardTerminalIto (C := C) (E := ℝ) F μ H)
    (u v : Process (E := C) F μ H) (n : ℕ) :
    embedding J (u - v) n = embedding J u n - embedding J v n := by
  apply Lp.ext
  have hi : ∀ᵐ ω ∂μ, ∀ i : Fin n,
      increment J (u - v) n i ω = increment J u n i ω - increment J v n i ω := by
    apply ae_all_iff.mpr
    intro i
    rw [increment_sub]
    exact Lp.coeFn_sub _ _
  filter_upwards [embedding_ae J (u - v) n, embedding_ae J u n, embedding_ae J v n,
    Lp.coeFn_sub (embedding J u n) (embedding J v n), hi] with ω hd hu hv hs hiω
  rw [hd, hs]
  change array J (u - v) n ω = embedding J u n ω - embedding J v n ω
  rw [hu, hv]
  ext i
  exact hiω i

end SHEStochastic.PartitionIncrementL2
