module

public import SHE.HaarRowPacket
public import SHE.NodeKernelLocal
public import SHE.HeatKernelLocal

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section

namespace SHE.FiniteHaar
open Finset Set MeasureTheory AddCircle CircleHeat HeatMarkov HaarWeightedHeat CellNegative
open scoped InnerProductSpace
local instance haarFinePacket_periodPos : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩

theorem centeredRow_toLp (p : List Bool) {t : ℝ} (ht : 0 < t) (x : AddCircle (1:ℝ)) :
    ContinuousMap.toLp 2 haarAddCircle ℂ (NodeKernelLocal.centeredRow p t ht x) =
      HeatTorusKernel.unitHeatKernel t x-kernel t ht (x-nodeCenter p) • circleOne := by
  have he : (ContinuousMap.toLp 2 haarAddCircle ℂ (NodeKernelLocal.centeredRow p t ht x)) =ᵐ[haarAddCircle]
      NodeKernelLocal.centeredRow p t ht x := ContinuousMap.coeFn_toLp haarAddCircle _
  apply Lp.ext
  filter_upwards [he,unitHeatKernel_ae ht x,circleOne_ae,
    Lp.coeFn_smul (kernel t ht (x-nodeCenter p)) circleOne,
    Lp.coeFn_sub (HeatTorusKernel.unitHeatKernel t x) (kernel t ht (x-nodeCenter p) • circleOne)] with y hy hk ho hsm hsub
  rw [hy,hsub]
  change kernel t ht (x-y)-kernel t ht (x-nodeCenter p) = _
  change _ = HeatTorusKernel.unitHeatKernel t x y-(kernel t ht (x-nodeCenter p) • circleOne) y
  rw [hk,hsm]
  simp only [Pi.smul_apply,ho,smul_eq_mul,mul_one]
  rw [show x-y = -(y-x) by abel,kernel_neg ht]

theorem centeredRow_pair (p : List Bool) {t : ℝ} (ht : 0 < t) (x : AddCircle (1:ℝ))
    (v : CircleL2) (hv : inner ℂ circleOne v = 0) :
    CellRow.row (NodeKernelLocal.centeredRow p t ht x) v = inner ℂ (HeatTorusKernel.unitHeatKernel t x) v := by
  change inner ℂ (ContinuousMap.toLp 2 haarAddCircle ℂ (NodeKernelLocal.centeredRow p t ht x)) v = _
  rw [centeredRow_toLp p ht x,inner_sub_left,inner_smul_left,hv,mul_zero,sub_zero]

/-- The actual all-order fine negative-input Gaussian packet on the
unit torus. The kernel is the normalized positive periodized heat kernel,
and the column is the genuine iterated Fréchet derivative. -/
theorem globalHaarColumn_jet_fine_pointwise {Λ ρ t : ℝ} (hΛ : 1 ≤ Λ)
    (hρ : 0 < ρ) (hρhalf : ρ < 1/2) (ht : 0 < t) (p : List Bool)
    (hsmall : nodeLength p ≤ Real.sqrt t) (f : DyadicApproximation.RealL2)
    (m U : ℝ) (hm : 0 < m)
    (hf : ∀ᵐ y ∂haarAddCircle, m ≤ (DyadicApproximation.realEmbed f y).re ∧
      (DyadicApproximation.realEmbed f y).re ≤ U)
    (j : ℕ) (v : Fin (j+1) → DyadicApproximation.RealL2) (M : Fin (j+1) → ℝ)
    (hM : ∀ i, 0 ≤ M i)
    (hv : ∀ i, i ≠ 0 → ∀ᵐ y ∂haarAddCircle, ‖DyadicApproximation.realEmbed (v i) y‖ ≤ M i) :
    ∀ᵐ x ∂haarAddCircle,
      ‖heat t (iteratedFDeriv ℝ (j+1) (globalHaarColumn (some p)) (DyadicApproximation.realEmbed f)
        (fun i => DyadicApproximation.realEmbed (v i))) x‖ ≤
      rowPacketConstant m U hm j ρ *
        (NodeKernelLocal.constant p t ht x/(((2^(p.length+1):ℕ):ℝ)))*scale Λ ρ (p.length+1)*
        localNegativeNorm p Λ ρ hΛ hρ.le (DyadicApproximation.realEmbed (v 0))*
          (∏ i ∈ univ.erase (0 : Fin (j+1)), M i) := by
  let w := iteratedFDeriv ℝ (j+1) (globalHaarColumn (some p)) (DyadicApproximation.realEmbed f)
    (fun i => DyadicApproximation.realEmbed (v i))
  have hp (x : Grid (p.length+1)) : 0 < localAverage (p.length+1) (DyadicApproximation.realEmbed f) x :=
    hm.trans_le (localAverage_bounds_ae _ _ m U hf x).1
  have hz : inner ℂ circleOne w = 0 := globalHaarColumn_jet_mean_zero p f hp (j+1) v
  filter_upwards [kernel_inner_ae ht w] with x hx
  rw [← hx]
  rw [← centeredRow_pair p ht x w hz]
  exact globalHaarColumn_jet_row_packet hΛ hρ hρhalf p (NodeKernelLocal.centeredRow p t ht x)
    (NodeKernelLocal.constant_pos p ht x)
    (fun b y hy => NodeKernelLocal.row_amplitude p ht hsmall x b y hy)
    (fun b y hy z hz => NodeKernelLocal.row_lipschitz p ht hsmall x b y z hy hz)
    (DyadicApproximation.realEmbed f) m U hm (realEmbed_real f) hf j
    (fun i => DyadicApproximation.realEmbed (v i)) M hM hv

end SHE.FiniteHaar
