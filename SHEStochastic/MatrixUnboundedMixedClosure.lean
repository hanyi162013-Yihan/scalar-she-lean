module

public import SHEStochastic.MatrixUnboundedCompensatorGrowth
public import SHEStochastic.CompensatedEnergyMartingale
public import SHEStochastic.EnergyTailAddition

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
noncomputable section

namespace SHEStochastic.MatrixUnboundedMixedClosure
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
variable (H : ℝ≥0) (i : Fin n) (a : ℂ →L[ℝ] ℝ) (freq : ℤ) (k : Fin n×SHE.FiniteHaar.HaarNode)
local notation "X" => CanonicalContinuousStateDriver.Space (E := Physical (d := Fin n))
  (ι := Fin n×SHE.FiniteHaar.HaarNode) H
local notation "M" => CanonicalLinearFluctuation.value (ι := Fin n×SHE.FiniteHaar.HaarNode)
  H (coordinate i a freq) ((freq : ℝ)^2)
local notation "N" => CanonicalStateDriverFiltration.coordinate (E := Physical (d := Fin n)) H k
local notation "A" => MatrixUnboundedFourierCompensator.mixed G hG hβ hβ1 H i a freq k

def energy (x : X) : ℝ := ‖x.1‖^2+‖x.2 k‖^2

theorem energy_continuous : Continuous (energy (n := n) H k) :=
  (continuous_fst.norm.pow 2).add (((continuous_apply k).comp continuous_snd).norm.pow 2)

theorem product_bound (t : ℝ≥0) (x : X) :
    |M t x*N t x| ≤ ((Real.exp ((H : ℝ)*(freq : ℝ)^2)+1)*‖coordinate i a freq‖)*
      (1+energy H k x) := by
  let B : ℝ := (Real.exp ((H : ℝ)*(freq : ℝ)^2)+1)*‖coordinate i a freq‖
  have hB : 0≤B := by dsimp only [B];positivity
  have hd : ‖N t x‖≤‖x.2 k‖ := (x.2 k).norm_coe_le_norm _
  rw [←Real.norm_eq_abs,norm_mul]
  calc
    _ ≤ (B*‖x.1‖)*‖x.2 k‖ := mul_le_mul
      (CanonicalEnergyGrowth.fluctuation H (coordinate i a freq) ((freq : ℝ)^2) (sq_nonneg _) t x)
      hd (norm_nonneg _) (by positivity)
    _ = B*(‖x.1‖*‖x.2 k‖) := by ring
    _ ≤ B*(1+energy H k x) := mul_le_mul_of_nonneg_left
      (by dsimp only [energy];nlinarith [sq_nonneg (‖x.1‖-‖x.2 k‖)]) hB

def cutoff (m : ℕ) : ℝ≥0 → BoundedContinuousFunction X ℝ :=
  MatrixFourierMixedTests.compensator H
    (MatrixUnboundedCutoff.coefficient G hG hβ ell hell hLower (m : ℝ≥0))
    (MatrixUnboundedCutoff.holder G hG hβ ell hell hLower (m : ℝ≥0)) hβ hβ1 i a freq k
local notation "An" => cutoff G hG hβ hβ1 ell hell hLower H i a freq k

theorem compensator_bound (t : ℝ≥0) (x : X) : |A t x| ≤
    MatrixUnboundedCompensatorGrowth.mixedConstant G (C := C) H i a freq k*(1+energy H k x) := by
  rw [←Real.norm_eq_abs]
  apply (MatrixUnboundedCompensatorGrowth.mixed_bound G hG hβ hβ1 H i a freq k t x).trans
  apply mul_le_mul_of_nonneg_left _ (MatrixUnboundedCompensatorGrowth.mixedConstant_nonneg G H i a freq k)
  dsimp only [energy]
  linarith [sq_nonneg ‖x.2 k‖]

theorem cutoff_bound (m : ℕ) (t : ℝ≥0) (x : X) : |An m t x| ≤
    MatrixUnboundedCompensatorGrowth.mixedConstant G (C := C) H i a freq k*(1+energy H k x) := by
  rw [←Real.norm_eq_abs]
  apply (MatrixUnboundedCompensatorGrowth.cutoff_mixed_bound G hG hβ hβ1 ell hell hLower H i a freq m k t x).trans
  apply mul_le_mul_of_nonneg_left _ (MatrixUnboundedCompensatorGrowth.mixedConstant_nonneg G H i a freq k)
  dsimp only [energy]
  linarith [sq_nonneg ‖x.2 k‖]

theorem compensator_convergence (φ : ℕ → ℕ) (hφ : StrictMono φ) (t : ℝ≥0)
    (K : Set X) (hK : IsCompact K) :
    TendstoUniformlyOn (fun m x => An (φ m) t x) (A t) atTop K := by
  exact CompactUniformComposition.reindex (φ := φ) (F := fun (m : ℕ) (x : X) => An m t x)
    (MatrixUnboundedFourierCompensator.cutoff_mixed G hG hβ hβ1 H i a freq ell hell hLower hK k t)
    hφ.tendsto_atTop

/-- Mixed state/original-driver characteristics pass to the same weak
limit using whole state and single-driver path energy UI. -/
theorem martingale (P : ℕ → ProbabilityMeasure X) (Q : ProbabilityMeasure X)
    (hlim : Tendsto P atTop (𝓝 Q)) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hTight : IsTightMeasureSet (Set.range (fun m => (P m).toMeasure)))
    (hUI : Tendsto (fun R : ℕ => ⨆ m,∫⁻ x in {x | (R : ℝ)≤energy H k x},
      ENNReal.ofReal (energy H k x) ∂(P m).toMeasure) atTop (𝓝 0))
    (htest : ∀ m s t,s≤t → ∀ ψ : BoundedContinuousFunction X ℝ,
      (∫ x,ψ (CanonicalStateDriverFiltration.history H s x)*
        (CompensatedEnergyMartingale.productValue M N (fun q x => An (φ m) q x) t x-
          CompensatedEnergyMartingale.productValue M N (fun q x => An (φ m) q x) s x) ∂(P m).toMeasure)=0) :
    Martingale (fun t x => M t x*N t x-A t x) (CanonicalStateDriverFiltration.filtration H) Q.toMeasure := by
  exact CompensatedEnergyMartingale.product P Q hlim hTight (energy H k) (energy_continuous H k)
    (fun x => add_nonneg (sq_nonneg _) (sq_nonneg _)) hUI
    (CanonicalStateDriverFiltration.filtration H) (CanonicalStateDriverFiltration.history H)
    (WeakLimitCanonicalBrownian.continuous_history H) (fun _ => le_rfl) M N A
    (fun m q x => An (φ m) q x)
    (CanonicalLinearFluctuation.continuous H (coordinate i a freq) ((freq : ℝ)^2))
    (WeakLimitCanonicalBrownian.continuous_coordinate H k)
    (fun t => ContinuousCanonicalCompensator.continuous H _ _ _ t) (fun m t => (An (φ m) t).continuous)
    (CanonicalLinearFluctuation.adapted H (coordinate i a freq) ((freq : ℝ)^2))
    (fun t => (CanonicalStateDriverFiltration.coordinate_adapted H k t).stronglyMeasurable)
    (MatrixUnboundedFourierCompensator.mixed_adapted G hG hβ hβ1 H i a freq k)
    (compensator_convergence G hG hβ hβ1 ell hell hLower H i a freq k φ hφ)
    ((Real.exp ((H : ℝ)*(freq : ℝ)^2)+1)*‖coordinate i a freq‖)
    (MatrixUnboundedCompensatorGrowth.mixedConstant G (C := C) H i a freq k)
    (by positivity) (MatrixUnboundedCompensatorGrowth.mixedConstant_nonneg G H i a freq k)
    (product_bound H i a freq k) (compensator_bound G hG hβ hβ1 H i a freq k)
    (fun m => cutoff_bound G hG hβ hβ1 ell hell hLower H i a freq k (φ m)) htest

end SHEStochastic.MatrixUnboundedMixedClosure
