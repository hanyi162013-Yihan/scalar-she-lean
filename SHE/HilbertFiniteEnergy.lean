module
public import SHE.NativeBesselFiniteSumEnergy
public import Mathlib.Algebra.Order.Chebyshev
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace SHE.HilbertFiniteEnergy
open MeasureTheory
open scoped ENNReal
variable {X I E:Type*}[MeasurableSpace X][NormedAddCommGroup E]
variable [MeasurableSpace E][BorelSpace E][SecondCountableTopology E]

/-- A finite set of actual Hilbert fields has the ordinary Cauchy square
bound. No orthogonality or independence is assumed between its terms. -/
theorem sum_bound(η:Measure X)(s:Finset I)(F:I→X→E)(hF:∀i,Measurable (F i))
    (hi:∀i∈s,Integrable (fun x=>‖F i x‖^2) η):
    Integrable (fun x=>‖∑i∈s,F i x‖^2) η ∧
      (∫x,‖∑i∈s,F i x‖^2 ∂η)≤(s.card:ℝ)*∑i∈s,(∫x,‖F i x‖^2 ∂η):=by
  have hp(i:I)(his:i∈s):MemLp (F i) 2 η:=
    (memLp_two_iff_integrable_sq_norm (hF i).aestronglyMeasurable).mpr (hi i his)
  have hs:MemLp (fun x=>∑i∈s,F i x) 2 η:=memLp_finsetSum s hp
  have hsi:Integrable (fun x=>‖∑i∈s,F i x‖^2) η:=
    (memLp_two_iff_integrable_sq_norm hs.aestronglyMeasurable).mp hs
  have hsum:Integrable (fun x=>∑i∈s,‖F i x‖^2) η:=integrable_finsetSum s hi
  have hb(x:X):‖∑i∈s,F i x‖^2≤(s.card:ℝ)*(∑i∈s,‖F i x‖^2):=
    (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le s _) 2).trans
      (sq_sum_le_card_mul_sum_sq (s:=s) (f:=fun i=>‖F i x‖))
  refine ⟨hsi,?_⟩
  have hh:=integral_mono hsi (hsum.const_mul (s.card:ℝ)) hb
  simpa only [integral_const_mul,integral_finsetSum s hi] using hh

/-- Uniform approximation budgets for finitely many actual fields may
be combined before the approximation index is selected. -/
theorem approximation(η:Measure X)(s:Finset I)(F:I→X→E)(hF:∀i,Measurable (F i))
    (hi:∀i∈s,Integrable (fun x=>‖F i x‖^2) η)(ε:ℝ)(C:I→ℝ)
    (hb:∀i∈s,(∫x,‖F i x‖^2 ∂η)≤ε^2*C i):
    Integrable (fun x=>‖∑i∈s,F i x‖^2) η ∧
      (∫x,‖∑i∈s,F i x‖^2 ∂η)≤ε^2*((s.card:ℝ)*∑i∈s,C i):=by
  obtain ⟨hsi,hs⟩:=sum_bound η s F hF hi
  refine ⟨hsi,hs.trans ?_⟩
  have hh:=mul_le_mul_of_nonneg_left (Finset.sum_le_sum hb) (Nat.cast_nonneg s.card : (0:ℝ)≤s.card)
  rw [←Finset.mul_sum] at hh
  exact hh.trans_eq (by ring)
end SHE.HilbertFiniteEnergy
