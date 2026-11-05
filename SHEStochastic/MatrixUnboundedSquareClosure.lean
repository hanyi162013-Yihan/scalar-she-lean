module

public import SHEStochastic.MatrixUnboundedCompensatorGrowth
public import SHEStochastic.CompensatedEnergyMartingale

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
noncomputable section

namespace SHEStochastic.MatrixUnboundedSquareClosure
open MeasureTheory ProbabilityTheory Filter SHE MatrixInfiniteHaar Matrix MatrixFourierCoordinates
open scoped NNReal ENNReal Topology MatrixOrder Matrix.Norms.L2Operator
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ENNReal)≠⊤) := ⟨by simp⟩
variable {n : ℕ} (G : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ)
    {C β : ℝ≥0} (hG : HolderWith C β G) (hβ : 0<β) (hβ1 : β≤1)
    (ell : ℝ) (hell : 0<ell)
    (hLower : ∀ z,ell • (1 : Matrix (Fin n) (Fin n) ℝ) ≤ G z*(G z)ᴴ)
local instance : SecondCountableTopology (Physical (d := Fin n)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (Physical (d := Fin n)) := borel _
local instance : BorelSpace (Physical (d := Fin n)) := ⟨rfl⟩
variable (H : ℝ≥0) (i : Fin n) (a : ℂ →L[ℝ] ℝ) (freq : ℤ)
local notation "X" => CanonicalContinuousStateDriver.Space (E := Physical (d := Fin n))
  (ι := Fin n×SHE.FiniteHaar.HaarNode) H
local notation "M" => CanonicalLinearFluctuation.value (ι := Fin n×SHE.FiniteHaar.HaarNode)
  H (coordinate i a freq) ((freq : ℝ)^2)

theorem fluctuation_bound (t : ℝ≥0) (x : X) : (M t x)^2≤
    (((Real.exp ((H : ℝ)*(freq : ℝ)^2)+1)*‖coordinate i a freq‖)^2)*(1+‖x.1‖^2) := by
  have hh := CanonicalEnergyGrowth.square_fluctuation H (coordinate i a freq) ((freq : ℝ)^2)
    (sq_nonneg _) t x
  simp only [Real.norm_eq_abs,sq_abs] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left (by linarith : ‖x.1‖^2≤1+‖x.1‖^2) (sq_nonneg _))

theorem compensator_bound (t : ℝ≥0) (x : X) :
    |MatrixUnboundedFourierCompensator.square G hG hβ hβ1 H i a freq t x|≤
      MatrixUnboundedCompensatorGrowth.squareConstant G (C := C) H i a freq*(1+‖x.1‖^2) := by
  simpa only [Real.norm_eq_abs] using MatrixUnboundedCompensatorGrowth.square_bound G hG hβ hβ1 H i a freq t x

theorem cutoff_compensator_bound (R : ℝ≥0) (t : ℝ≥0) (x : X) :
    |MatrixFourierSquareTests.compensator H
      (MatrixUnboundedCutoff.coefficient G hG hβ ell hell hLower R)
      (MatrixUnboundedCutoff.holder G hG hβ ell hell hLower R) hβ hβ1 i a freq t x|≤
      MatrixUnboundedCompensatorGrowth.squareConstant G (C := C) H i a freq*(1+‖x.1‖^2) := by
  simpa only [Real.norm_eq_abs] using
    MatrixUnboundedCompensatorGrowth.cutoff_square_bound G hG hβ hβ1 ell hell hLower H i a freq R t x

theorem compensator_convergence (φ : ℕ → ℕ) (hφ : StrictMono φ) (t : ℝ≥0)
    (K : Set X) (hK : IsCompact K) :
    TendstoUniformlyOn (fun m x => MatrixFourierSquareTests.compensator H
      (MatrixUnboundedCutoff.coefficient G hG hβ ell hell hLower (φ m : ℝ≥0))
      (MatrixUnboundedCutoff.holder G hG hβ ell hell hLower (φ m : ℝ≥0)) hβ hβ1 i a freq t x)
      (MatrixUnboundedFourierCompensator.square G hG hβ hβ1 H i a freq t) atTop K := by
  exact CompactUniformComposition.reindex (φ := φ)
    (F := fun (m : ℕ) (x : X) => MatrixFourierSquareTests.compensator H
      (MatrixUnboundedCutoff.coefficient G hG hβ ell hell hLower (m : ℝ≥0))
      (MatrixUnboundedCutoff.holder G hG hβ ell hell hLower (m : ℝ≥0)) hβ hβ1 i a freq t x)
    (MatrixUnboundedFourierCompensator.cutoff_square G hG hβ hβ1 H i a freq ell hell hLower hK t)
    hφ.tendsto_atTop

/-- Quadratic closure specialized to the literal matrix coefficients,
separated from the actual-solution construction for efficient checking. -/
theorem martingale (P : ℕ → ProbabilityMeasure X) (Q : ProbabilityMeasure X)
    (hlim : Tendsto P atTop (𝓝 Q)) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hTight : IsTightMeasureSet (Set.range (fun m => (P m).toMeasure)))
    (hUI : Tendsto (fun N : ℕ => ⨆ m,∫⁻ x in {x | (N : ℝ)≤‖x.1‖^2},
      ENNReal.ofReal (‖x.1‖^2) ∂(P m).toMeasure) atTop (𝓝 0))
    (htest : ∀ m s t,s≤t → ∀ ψ : BoundedContinuousFunction X ℝ,
      (∫ x,ψ (CanonicalStateDriverFiltration.history H s x)*
        (CompensatedEnergyMartingale.value M (fun q x => MatrixFourierSquareTests.compensator H
          (MatrixUnboundedCutoff.coefficient G hG hβ ell hell hLower (φ m : ℝ≥0))
          (MatrixUnboundedCutoff.holder G hG hβ ell hell hLower (φ m : ℝ≥0)) hβ hβ1 i a freq q x) t x-
        CompensatedEnergyMartingale.value M (fun q x => MatrixFourierSquareTests.compensator H
          (MatrixUnboundedCutoff.coefficient G hG hβ ell hell hLower (φ m : ℝ≥0))
          (MatrixUnboundedCutoff.holder G hG hβ ell hell hLower (φ m : ℝ≥0)) hβ hβ1 i a freq q x) s x)
        ∂(P m).toMeasure)=0) :
    Martingale (fun t x => (M t x)^2-
      MatrixUnboundedFourierCompensator.square G hG hβ hβ1 H i a freq t x)
      (CanonicalStateDriverFiltration.filtration H) Q.toMeasure := by
  let A := MatrixUnboundedFourierCompensator.square G hG hβ hβ1 H i a freq
  let An := fun m => MatrixFourierSquareTests.compensator H
    (MatrixUnboundedCutoff.coefficient G hG hβ ell hell hLower (φ m : ℝ≥0))
    (MatrixUnboundedCutoff.holder G hG hβ ell hell hLower (φ m : ℝ≥0)) hβ hβ1 i a freq
  let K : ℝ := ((Real.exp ((H : ℝ)*(freq : ℝ)^2)+1)*‖coordinate i a freq‖)^2
  let D : ℝ := MatrixUnboundedCompensatorGrowth.squareConstant G (C := C) H i a freq
  change Martingale (CompensatedEnergyMartingale.value (M) A) _ _
  apply CompensatedEnergyMartingale.martingale P Q hlim
    hTight
    (fun x : X => ‖x.1‖^2) (continuous_fst.norm.pow 2) (fun _ => sq_nonneg _)
    hUI
    (CanonicalStateDriverFiltration.filtration H) (CanonicalStateDriverFiltration.history H)
    (WeakLimitCanonicalBrownian.continuous_history H) (fun _ => le_rfl) (M) A
    (fun m t x => An m t x)
    (CanonicalLinearFluctuation.continuous H (coordinate i a freq) ((freq : ℝ)^2))
    (fun t => ContinuousCanonicalCompensator.continuous H _ _ _ t)
    (fun m t => (An m t).continuous)
    (CanonicalLinearFluctuation.adapted H (coordinate i a freq) ((freq : ℝ)^2))
    (MatrixUnboundedFourierCompensator.square_adapted G hG hβ hβ1 H i a freq)
    (compensator_convergence G hG hβ hβ1 ell hell hLower H i a freq φ hφ)
    K D (sq_nonneg _) (MatrixUnboundedCompensatorGrowth.squareConstant_nonneg G H i a freq)
    (fluctuation_bound H i a freq)
    (compensator_bound G hG hβ hβ1 H i a freq)
    (fun m => cutoff_compensator_bound G hG hβ hβ1 ell hell hLower H i a freq (φ m))
  exact htest

end SHEStochastic.MatrixUnboundedSquareClosure
