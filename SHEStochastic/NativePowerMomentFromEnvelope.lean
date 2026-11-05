module

public import SHEStochastic.DiscretePowerMoment
public import SHEStochastic.NativeUnweightedQuadraticVariation
public import SHEStochastic.NativeBoundedAEVersion
public import SHEStochastic.WeightedBracketBound

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHEStochastic.NativePowerMomentFromEnvelope
open MeasureTheory ProbabilityTheory SHE SHE.PredictableL2 SHE.StoppedItoInputs Filter
open MathFin.QuadraticVariationL2
open scoped NNReal ENNReal Topology

variable {Ω C ι : Type*} [MeasurableSpace Ω] [Countable ι] [DecidableEq ι]
  [NormedAddCommGroup C] [InnerProductSpace ℝ C] [CompleteSpace C]
  [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {H : ℝ≥0}

/-- The Taylor estimate passes to expectations using only the existing
mean-square quadratic-variation limit. -/
theorem estimate (P : FiniteScalarIto.Family F μ H ι) (e : HilbertBasis ι ℝ C)
    (u : Process (E := C) F μ H) (M : ℝ≥0)
    (hu : ∀ᵐ x ∂(energyMeasure μ H).trim (predictable_le_product F), ‖u x‖ ≤ M)
    (Y : ℝ≥0 → Ω → ℝ) (hm : Martingale Y F μ)
    (hRep : ∀ t : ℝ≥0, Y t =ᵐ[μ]
      (FiniteCylindricalIto.terminalIto P.toCoordinates e).integral (stop F μ H t u))
    (hL : ∀ t k, MemLp (fun ω ↦ Y t ω^k) 2 μ)
    (k : ℕ) (hk : 2 ≤ k) (D : Ω → ℝ) (hD0 : ∀ ω, 0 ≤ D ω)
    (hDb : ∀ᵐ ω ∂μ, ∀ t, t ≤ H → |Y t ω| ≤ D ω)
    (hDq : MemLp (fun ω ↦ D ω^(k-2)) 2 μ) :
    (∫ ω, Y H ω^k ∂μ) ≤ (k : ℝ)*(k-1 : ℕ) *
      ∫ ω, D ω^(k-2)*StochasticExponential.bracket F μ H u ω ∂μ := by
  let J := FiniteCylindricalIto.terminalIto P.toCoordinates e
  let A := StochasticExponential.bracket F μ H u
  let f (ω : Ω) := D ω^(k-2)
  let c : ℝ := (k : ℝ)*(k-1 : ℕ)
  let Z (n : ℕ) := NativeQuadraticFluctuation.fluctuation P e u (fun _ _ ↦ 1) n
  let L (n : ℕ) (ω : Ω) := ∑ i : Fin n,
    Y (unifPart H n i) ω^(k-1)*(Y (unifPart H n (i+1)) ω-Y (unifPart H n i) ω)
  have huN : ∀ᵐ x ∂FiniteScalarIto.inputMeasure F μ H, ‖u x‖ ≤ M := by
    rwa [NativeRowRepresentatives.inputMeasure_eq]
  have hZ (n : ℕ) : MemLp (Z n) 2 μ :=
    NativeQuadraticFluctuation.memLp_fluctuation P e u M huN (fun _ _ ↦ 1)
      (fun _ ↦ stronglyMeasurable_const) 1 (by norm_num) (fun _ _ ↦ by norm_num) n
  have hA : MemLp A 2 μ := by
    apply MemLp.of_bound (StochasticExponential.bracket_measurable F μ H u).stronglyMeasurable.aestronglyMeasurable
      ((timeMeasure H).real Set.univ*(M : ℝ)^2)
    filter_upwards [WeightedBracketBound.bounded u M M.coe_nonneg hu] with ω hω
    rw [Real.norm_of_nonneg (WeightedBracketBound.bracket_nonneg u ω)]
    exact hω
  have hY2 (t : ℝ≥0) : MemLp (Y t) 2 μ := by
    simpa only [pow_one] using hL t 1
  have hLI (n : ℕ) : Integrable (L n) μ := by
    apply integrable_finset_sum
    intro i hi
    exact (hL _ (k-1)).integrable_mul ((hY2 _).sub (hY2 _))
  have hLzero (n : ℕ) : (∫ ω, L n ω ∂μ) = 0 := by
    rw [show (∫ ω, L n ω ∂μ) = ∑ i : Fin n, ∫ ω,
        Y (unifPart H n i) ω^(k-1)*(Y (unifPart H n (i+1)) ω-Y (unifPart H n i) ω) ∂μ from
      integral_finset_sum Finset.univ (fun i hi ↦
        (hL _ (k-1)).integrable_mul ((hY2 _).sub (hY2 _)))]
    apply Finset.sum_eq_zero
    intro i hi
    exact DiscretePowerMoment.centered Y hm _ _
      (MathFin.ItoIntegralBrownian.unifPart_mono H n (Nat.le_succ _)) (k-1) (hL _ _) (hY2 _) (hY2 _)
  have hY0 : Y 0 =ᵐ[μ] (fun _ ↦ (0 : ℝ)) := by
    have hh := hRep 0
    rw [NNReal.coe_zero, stop_zero, map_zero] at hh
    exact hh.trans (Lp.coeFn_zero _ _ _)
  have hBound (n : ℕ) (hn : 0 < n) :
      (∫ ω, Y H ω^k ∂μ) ≤ c*((∫ ω, f ω*A ω ∂μ)+(∫ ω, f ω*Z n ω ∂μ)) := by
    have hgrid : ∀ᵐ ω ∂μ, ∀ j : ℕ, Y (unifPart H n j) ω =
        J.integral (stop F μ H (unifPart H n j) u) ω :=
      ae_all_iff.mpr (fun j ↦ hRep _)
    have hb : ∀ᵐ ω ∂μ, Y H ω^k ≤ (k : ℝ)*L n ω+c*(f ω*(A ω+Z n ω)) := by
      filter_upwards [hDb, hY0, hgrid, NativeUnweightedQuadraticVariation.energy_sum u n hn]
        with ω hd hz hg he
      have hTaylor := DiscretePowerMoment.discrete H (fun t ↦ Y t ω) k hk (D ω) (hD0 ω) hd n hn
      have hQ : (∑ i : Fin n, (Y (unifPart H n (i+1)) ω-Y (unifPart H n i) ω)^2) = A ω+Z n ω := by
        calc
          _ = NativeWeightedQuadraticVariation.sum J u (fun _ _ ↦ 1) n ω := by
            simp only [NativeWeightedQuadraticVariation.sum, one_mul]
            exact Finset.sum_congr rfl (fun i hi ↦ by rw [hg (i+1), hg i])
          _ = _ := by rw [NativeWeightedQuadraticVariation.sum_eq, he]; exact add_comm _ _
      rw [hz, zero_pow (by omega : k ≠ 0), sub_zero, hQ] at hTaylor
      change Y H ω^k ≤ (k : ℝ)*L n ω+(c*f ω)*(A ω+Z n ω) at hTaylor
      simpa only [mul_assoc] using hTaylor
    have hR : Integrable (fun ω ↦ f ω*(A ω+Z n ω)) μ := hDq.integrable_mul (hA.add (hZ n))
    have hi := integral_mono_ae ((hL H k).integrable one_le_two)
      (((hLI n).const_mul (k : ℝ)).add (hR.const_mul c)) hb
    have he : (∫ ω, f ω*(A ω+Z n ω) ∂μ) =
        (∫ ω, f ω*A ω ∂μ)+(∫ ω, f ω*Z n ω ∂μ) := by
      simp_rw [mul_add]
      exact integral_add (hDq.integrable_mul hA) (hDq.integrable_mul (hZ n))
    have hInt : (∫ ω, (k : ℝ)*L n ω+c*(f ω*(A ω+Z n ω)) ∂μ) =
        (k : ℝ)*(∫ ω, L n ω ∂μ)+c*(∫ ω, f ω*(A ω+Z n ω) ∂μ) :=
      (integral_add ((hLI n).const_mul (k : ℝ)) (hR.const_mul c)).trans
        (congrArg₂ (· + ·) (integral_const_mul _ _) (integral_const_mul _ _))
    change (∫ ω, Y H ω^k ∂μ) ≤ ∫ ω, (k : ℝ)*L n ω+c*(f ω*(A ω+Z n ω)) ∂μ at hi
    rwa [hInt, hLzero, mul_zero, zero_add, he] at hi
  have hlim := NativeUnweightedQuadraticVariation.pairing_limit P e u M huN f hDq
  have ht : Tendsto (fun n ↦ c*((∫ ω, f ω*A ω ∂μ)+(∫ ω, f ω*Z n ω ∂μ)))
      atTop (𝓝 (c*(∫ ω, f ω*A ω ∂μ))) := by
    simpa only [add_zero] using ((tendsto_const_nhds (x := ∫ ω, f ω*A ω ∂μ)).add hlim).const_mul c
  exact ge_of_tendsto ht (by
    filter_upwards [eventually_gt_atTop 0] with n hn
    exact hBound n hn)

end SHEStochastic.NativePowerMomentFromEnvelope
