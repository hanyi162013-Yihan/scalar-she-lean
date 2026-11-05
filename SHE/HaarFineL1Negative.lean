module

public import SHE.HaarNegativeFine

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.FiniteHaar
open Finset Set MeasureTheory AddCircle CircleHeat HeatMarkov HaarWeightedHeat CellNegative
local instance haarFineL1Negative_periodPos : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩

/-- The actual fine heat packet in spatial L¹, retaining the local
negative input norm. This permits a later, distinct adapted kernel
operator without moving any cancellation through that operator. -/
theorem globalHaarColumn_jet_fine_normOne_negative {Λ ρ δ : ℝ} (hΛ : 1 ≤ Λ)
    (hρ : 0 < ρ) (hρhalf : ρ < 1/2) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (p : List Bool) (hsmall : nodeLength p ≤ Real.sqrt δ) (f : DyadicApproximation.RealL2)
    (m U : ℝ) (hm : 0 < m)
    (hf : ∀ᵐ y ∂haarAddCircle, m ≤ (DyadicApproximation.realEmbed f y).re ∧
      (DyadicApproximation.realEmbed f y).re ≤ U)
    (j : ℕ) (v : Fin (j+1) → DyadicApproximation.RealL2) (M : Fin (j+1) → ℝ)
    (hM : ∀ i, 0 ≤ M i)
    (hv : ∀ i, i ≠ 0 → ∀ᵐ y ∂haarAddCircle, ‖DyadicApproximation.realEmbed (v i) y‖ ≤ M i) :
    normOne (heat δ (iteratedFDeriv ℝ (j+1) (globalHaarColumn (some p)) (DyadicApproximation.realEmbed f)
      (fun i => DyadicApproximation.realEmbed (v i))))^2 ≤
      (rowPacketConstant m U hm j ρ)^2*localConstant^2*
        ((((2^(p.length+1):ℕ):ℝ))⁻¹)^2*δ⁻¹*(Λ+(((2^(p.length+1):ℕ):ℝ))^2)^ρ*
        localNegativeNorm p Λ ρ hΛ hρ.le (DyadicApproximation.realEmbed (v 0))^2*
        (∏ i ∈ univ.erase (0 : Fin (j+1)), M i)^2 := by
  let N : ℝ := ((2^(p.length+1):ℕ):ℝ)
  let D := scale Λ ρ (p.length+1)
  let H := localNegativeNorm p Λ ρ hΛ hρ.le (DyadicApproximation.realEmbed (v 0))
  let P := ∏ i ∈ univ.erase (0 : Fin (j+1)), M i
  let A := rowPacketConstant m U hm j ρ
  let R := A*localConstant/(Real.sqrt δ*N)*D*H*P
  let z := heat δ (iteratedFDeriv ℝ (j+1) (globalHaarColumn (some p)) (DyadicApproximation.realEmbed f)
    (fun i => DyadicApproximation.realEmbed (v i)))
  have hA : 0 ≤ A := rowPacketConstant_nonneg m U hm j ρ
  have hP : 0 ≤ P := prod_nonneg (fun i _ => hM i)
  have hH : 0 ≤ H := add_nonneg (norm_nonneg _) (norm_nonneg _)
  have hN : 0 < N := by dsimp [N]; positivity
  have hD : 0 ≤ D := by dsimp [D,scale]; positivity
  have hR : 0 ≤ R := by dsimp [R]; positivity [localConstant_pos]
  have hdom : ∀ᵐ x ∂haarAddCircle, ‖z x‖ ≤ R*‖kernel (8*δ) (by positivity) (x-nodeCenter p)‖ := by
    filter_upwards [globalHaarColumn_jet_fine_pointwise hΛ hρ hρhalf hδ p hsmall f m U hm hf j v M hM hv] with x hx
    apply hx.trans_eq
    dsimp only [NodeKernelLocal.constant,R,A,N,D,H,P,localConstant]
    field_simp
  have hn := (GaussianNegativePacket.dominated_norms hδ hδ1 hR (nodeCenter p) z hdom).2
  apply hn.trans_eq
  have hDs : D^2 = (Λ+N^2)^ρ := by
    dsimp only [D,scale,N]
    rw [← Real.rpow_mul_natCast (by positivity : 0 ≤ Λ+(((2^(p.length+1):ℕ):ℝ))^2)]
    congr 1
    norm_num
  dsimp only [R]
  rw [mul_pow,mul_pow,mul_pow,div_pow,mul_pow,mul_pow,Real.sq_sqrt hδ.le,hDs]
  dsimp only [A,N,H,P]
  field_simp

end SHE.FiniteHaar
