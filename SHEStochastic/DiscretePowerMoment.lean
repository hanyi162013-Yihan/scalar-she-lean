module

public import SHEStochastic.PowerTaylorBound
public import SHEStochastic.MartingaleCrossPairing
public import MathFin.Foundations.ItoIntegralBrownian

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
noncomputable section

namespace SHEStochastic.DiscretePowerMoment
open MeasureTheory ProbabilityTheory Filter
open MathFin.QuadraticVariationL2
open scoped NNReal ENNReal Topology

/-- A finite-partition power estimate with unweighted squared increments. -/
theorem discrete (H : ℝ≥0) (x : ℝ≥0 → ℝ) (k : ℕ) (hk : 2 ≤ k)
    (D : ℝ) (hD : 0 ≤ D) (hb : ∀ t, t ≤ H → |x t| ≤ D)
    (n : ℕ) (hn : 0 < n) :
    x H^k-x 0^k ≤ (k : ℝ)*(∑ i : Fin n,
      x (unifPart H n i)^(k-1)*(x (unifPart H n (i+1))-x (unifPart H n i))) +
      ((k : ℝ)*(k-1 : ℕ)*D^(k-2)) *
        ∑ i : Fin n, (x (unifPart H n (i+1))-x (unifPart H n i))^2 := by
  have ht : (∑ i : Fin n, (x (unifPart H n (i+1))^k-x (unifPart H n i)^k)) =
      x H^k-x 0^k := by
    rw [Fin.sum_univ_eq_sum_range (fun j : ℕ ↦ x (unifPart H n (j+1))^k-x (unifPart H n j)^k),
      Finset.sum_range_sub (fun j ↦ x (unifPart H n j)^k)]
    have hn0 : (n : ℝ≥0) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    simp [unifPart, hn0]
  rw [← ht, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i hi
  have hs := MathFin.ItoIntegralBrownian.unifPart_le_T (T := H) (n := n) (Nat.le_of_lt i.isLt)
  have ht := MathFin.ItoIntegralBrownian.unifPart_le_T (T := H) (n := n) (Nat.succ_le_of_lt i.isLt)
  have hr := le_trans (le_abs_self _) (PowerTaylorBound.remainder k hk
    (x (unifPart H n i)) (x (unifPart H n (i+1))) D hD (hb _ hs) (hb _ ht))
  linarith

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

/-- An integrable past power has zero pairing with a martingale increment. -/
theorem centered (Y : ℝ≥0 → Ω → ℝ) (hm : Martingale Y F μ)
    (s t : ℝ≥0) (hst : s ≤ t) (k : ℕ)
    (hp : MemLp (fun ω ↦ Y s ω^k) 2 μ)
    (hs : MemLp (Y s) 2 μ) (ht : MemLp (Y t) 2 μ) :
    (∫ ω, Y s ω^k*(Y t ω-Y s ω) ∂μ) = 0 := by
  have h1 := hp.integrable_mul ht
  have h2 := hp.integrable_mul hs
  have he : (fun ω ↦ Y s ω^k*(Y t ω-Y s ω)) =
      (fun ω ↦ Y s ω^k*Y t ω)-(fun ω ↦ Y s ω^k*Y s ω) := by
    funext ω
    simp only [Pi.sub_apply]
    ring
  calc
    _ = (∫ ω, Y s ω^k*Y t ω ∂μ)-(∫ ω, Y s ω^k*Y s ω ∂μ) := by
      rw [he]
      exact integral_sub h1 h2
    _ = 0 := by
      rw [MartingaleCrossPairing.past_mul μ F Y hm s t hst (fun ω ↦ Y s ω^k) ((hm.stronglyAdapted s).pow k) h1, sub_self]

end SHEStochastic.DiscretePowerMoment
