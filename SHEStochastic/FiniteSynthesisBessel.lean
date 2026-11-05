module

public import SHE.BesselSynthesis
public import Mathlib.Topology.Algebra.InfiniteSum.Real

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
noncomputable section

namespace SHEStochastic.FiniteSynthesisBessel
open Finset

variable {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Uniform finite synthesis estimates imply Bessel estimates for
every actual physical Hilbert-space test vector. -/
theorem finite (a : ι → E) (U : ℝ) (hU : 0≤U)
    (hFinite : ∀ (s : Finset ι) (z : ι → ℝ),
      ‖∑ i∈s, z i • a i‖^2 ≤ U*(∑ i∈s, ‖z i‖^2))
    (s : Finset ι) (x : E) : (∑ i∈s, ‖inner ℝ (a i) x‖^2) ≤ U*‖x‖^2 := by
  let V := ∑ i∈s, inner ℝ (a i) x • a i
  let e := ∑ i∈s, ‖inner ℝ (a i) x‖^2
  have hinner : inner ℝ V x=e := by
    simp only [V, e, sum_inner, real_inner_smul_left, Real.norm_eq_abs, sq_abs]
    simp only [pow_two]
  have he : 0≤e := sum_nonneg (fun _ _ => sq_nonneg _)
  have hc : e≤‖V‖*‖x‖ := by rw [← hinner]; exact real_inner_le_norm _ _
  have hs : e^2 ≤ ‖V‖^2*‖x‖^2 := by
    have hh := mul_self_le_mul_self he hc
    nlinarith only [hh]
  have hu : ‖V‖^2 ≤ U*e := hFinite s (fun i => inner ℝ (a i) x)
  have htot := hs.trans (mul_le_mul_of_nonneg_right hu (sq_nonneg ‖x‖))
  by_cases hz : e=0
  · change e ≤ _
    rw [hz]
    exact mul_nonneg hU (sq_nonneg _)
  · have hp : 0<e := lt_of_le_of_ne he (Ne.symm hz)
    change e ≤ _
    nlinarith only [htot, hp]


theorem summable (a : ι → E) (U : ℝ) (hU : 0≤U)
    (hFinite : ∀ (s : Finset ι) (z : ι → ℝ),
      ‖∑ i∈s, z i • a i‖^2 ≤ U*(∑ i∈s, ‖z i‖^2)) (x : E) :
    Summable (fun i => ‖inner ℝ (a i) x‖^2) :=
  summable_of_sum_le (fun _ => sq_nonneg _) (fun s => finite a U hU hFinite s x)

theorem tsum_bound (a : ι → E) (U : ℝ) (hU : 0≤U)
    (hFinite : ∀ (s : Finset ι) (z : ι → ℝ),
      ‖∑ i∈s, z i • a i‖^2 ≤ U*(∑ i∈s, ‖z i‖^2)) (x : E) :
    (∑' i, ‖inner ℝ (a i) x‖^2) ≤ U*‖x‖^2 :=
  Real.tsum_le_of_sum_le (fun _ => sq_nonneg _) (fun s => finite a U hU hFinite s x)

/-- The actual infinite synthesis is constructed from the uniform
finite bound by reusing the common real/complex synthesis machinery. -/
def synthesis [CompleteSpace E] (a : ι → E) (U : ℝ) (hU : 0≤U)
    (hFinite : ∀ (s : Finset ι) (z : ι → ℝ),
      ‖∑ i∈s, z i • a i‖^2 ≤ U*(∑ i∈s, ‖z i‖^2)) :
    lp (fun _ : ι => ℝ) 2 →L[ℝ] E :=
  SHE.BesselSynthesis.synthesis a (summable a U hU hFinite) U hU (tsum_bound a U hU hFinite)

theorem synthesis_single [CompleteSpace E] [DecidableEq ι]
    (a : ι → E) (U : ℝ) (hU : 0≤U)
    (hFinite : ∀ (s : Finset ι) (z : ι → ℝ),
      ‖∑ i∈s, z i • a i‖^2 ≤ U*(∑ i∈s, ‖z i‖^2)) (i : ι) :
    synthesis a U hU hFinite (lp.single 2 i 1)=a i :=
  SHE.BesselSynthesis.synthesis_single a _ U hU _ i

end SHEStochastic.FiniteSynthesisBessel
