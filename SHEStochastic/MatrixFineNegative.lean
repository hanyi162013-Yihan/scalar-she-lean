module

public import SHEStochastic.MatrixFinePacket
public import SHE.GaussianPacketOutput

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.MatrixFineNegative
open MeasureTheory SHE SHE.FiniteHaar SHE.DyadicApproximation SHE.HaarWeightedHeat SHE.CellNegative
open MatrixInfiniteHaar MatrixPhysicalColumnSmooth MatrixActualColumnCalculus MatrixProfileEntries MatrixNegativeEntries
open scoped NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local notation "μ" => AddCircle.haarAddCircle (T := (1 : ℝ))
variable {d : Type*} [Fintype d] [DecidableEq d]

def constant (P : Profile d) (ρ : ℝ) (k : ℕ) : ℝ :=
  GaussianPacketOutput.constant ρ * MatrixRowJets.packetConstant P ρ k ^ 2

theorem constant_nonneg {ρ : ℝ} (hρhalf : ρ < 1/2) (P : Profile d) (k : ℕ) :
    0 ≤ constant P ρ k := mul_nonneg (GaussianPacketOutput.constant_nonneg hρhalf) (sq_nonneg _)

/-- Fine matrix derivative packets retain both massive and fractional
negative-output gains after an arbitrary bounded rough multiplier. -/
theorem bound {Λ ρ t : ℝ} (hΛ : 1 ≤ Λ) (hρ : 0 < ρ) (hρhalf : ρ < 1/2)
    (ht : 0 < t) (ht1 : t ≤ 1) (P : Profile d) (p : List Bool) (hsmall : nodeLength p ≤ Real.sqrt t)
    (i r : d) (v : Domain (d := d)) (w : List (Domain (d := d)))
    (M : Domain (d := d) → ℝ) (hM : ∀ q, 0 ≤ M q) (hRest : ∀ q ∈ w, ∀ᵐ x ∂μ, ‖q.val x‖ ≤ M q)
    (b : CircleHeat.CircleL2) (B : ℝ) (hB : 0 ≤ B) (hb : ∀ᵐ x ∂μ, ‖b x‖ ≤ B) :
    ‖weightedHeat Λ ρ t hΛ hρ.le b B hb (MatrixFinePacket.scalarColumn P p i r (v :: w))‖ ^ 2 ≤
      constant P ρ w.length * B ^ 2 * ((((2^(p.length+1):ℕ):ℝ))⁻¹) ^ 2 * t⁻¹ *
        (Λ+(((2^(p.length+1):ℕ):ℝ))^2)^ρ * min (Λ^(-ρ)*t^(-(1/2 : ℝ))) (t^(ρ-1/2)) *
        localNorm p Λ ρ hΛ hρ.le v ^ 2 * MatrixJetClosure.weight M w ^ 2 := by
  let A := MatrixRowJets.packetConstant P ρ w.length * scale Λ ρ (p.length+1) *
    localNorm p Λ ρ hΛ hρ.le v * MatrixJetClosure.weight M w
  have hA : 0 ≤ A := mul_nonneg (mul_nonneg (mul_nonneg (MatrixRowJets.packetConstant_nonneg P ρ _)
    (scale_positive Λ ρ hΛ _).le) (localNorm_nonneg p Λ ρ hΛ hρ.le v)) (MatrixJetClosure.weight_nonneg M hM w)
  have hpoint : ∀ᵐ x ∂μ, ‖CircleHeat.heat t (MatrixFinePacket.scalarColumn P p i r (v :: w)) x‖ ≤
      A * (NodeKernelLocal.constant p t ht x/(((2^(p.length+1):ℕ):ℝ))) := by
    filter_upwards [MatrixFinePacket.pointwise hΛ hρ hρhalf ht P p hsmall i r v w M hM hRest] with x hx
    exact hx.trans_eq (by dsimp [A]; ring)
  have hh := GaussianPacketOutput.negative hΛ hρ hρhalf ht ht1 hA p _ hpoint b B hB hb
  have hs : scale Λ ρ (p.length+1)^2 = (Λ+(((2^(p.length+1):ℕ):ℝ))^2)^ρ := by
    rw [scale, ← Real.rpow_mul_natCast (by positivity : 0 ≤ Λ+(((2^(p.length+1):ℕ):ℝ))^2)]
    congr 1
    norm_num
  exact hh.trans_eq (by dsimp only [A, constant]; simp only [mul_pow, hs]; ring)

end SHEStochastic.MatrixFineNegative
