module
public import SHE.NativeHigherMasterCoefficient
public import SHE.FullMaster
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SHE.NativeHigherMasterFiniteCoefficient
open Real Filter Topology
open scoped NNReal ENNReal BigOperators

def constant(N:ℕ)(aC aP aG aB:Fin N→ℝ≥0∞)(Cc Ci Cp Cg Cb:Fin N→ℝ)(q:Fin 4→ℝ):ℝ:=
  ∑k:Fin N,NativeHigherMasterCoefficient.constant (aC k) (aP k) (aG k) (aB k)
    (Cc k) (Ci k) (Cp k) (Cg k) (Cb k) q

def signedLinear(q:Fin 4→ℝ)(Λ:ℝ):ℝ:=Λ^(-(q 2/8))
def pastLinear(q:Fin 4→ℝ)(Λ:ℝ):ℝ:=Λ^(-(q 1/8))

theorem constant_nonneg(N:ℕ)(aC aP aG aB:Fin N→ℝ≥0∞)(Cc Ci Cp Cg Cb:Fin N→ℝ)
    (q:Fin 4→ℝ)(hq:∀i,0<q i):0≤constant N aC aP aG aB Cc Ci Cp Cg Cb q:=
  Finset.sum_nonneg (fun k _=>NativeHigherMasterCoefficient.constant_nonneg
    (aC k) (aP k) (aG k) (aB k) (Cc k) (Ci k) (Cp k) (Cg k) (Cb k) q hq)

/-- Summing the actual finite-depth four-rate caps gives the native
master row, a decaying true-negative linear coefficient, a global
linear coefficient, and the arbitrarily small bad tail. All finite
depths use the same frequency cutoff and the same true energies. -/
theorem cap(N:ℕ)(aC aP aG aB:Fin N→ℝ≥0∞)(Cc Ci Cp Cg Cb:Fin N→ℝ)
    (q:Fin 4→ℝ)(hq:∀i,0<q i){Λ R m H χ:ℝ}(Neg:ℝ≥0∞)
    (hΛ:1≤Λ)(hR:Λ^(1/4:ℝ)≤R)(hm:0≤m)(hH0:0≤H)(hH1:H≤1)(hχ:χ≤1):
    let K:=fun k:Fin N=>NativeFullRateCap.coefficient (aC k) (aP k) (aG k) (aB k)
      (Cc k) (Ci k) (Cp k) (Cg k) (Cb k) (m^2) H χ Neg
    (∑k:Fin N,∑i:Fin 4,sqrt (K k i).toReal*StateBands.geometricConstant (q i/2)*R^(-(q i/2)))≤
      constant N aC aP aG aB Cc Ci Cp Cg Cb q*
        (signedLinear q Λ*sqrt Neg.toReal+pastLinear q Λ*m+m^χ+Λ^(-(q 3/8))) :=by
  intro K
  let row:=signedLinear q Λ*sqrt Neg.toReal+pastLinear q Λ*m+m^χ+Λ^(-(q 3/8))
  have hCurrent:Λ^(-(q 0/8))≤1:=rpow_le_one_of_one_le_of_nonpos hΛ (by linarith only [hq 0])
  have hrow:(∑i:Fin 4,Λ^(-(q i/8))*(![m^χ,m,sqrt Neg.toReal,1]:Fin 4→ℝ) i)≤row:=by
    simp only [Fin.sum_univ_four]
    change Λ^(-(q 0/8))*m^χ+Λ^(-(q 1/8))*m+
      Λ^(-(q 2/8))*sqrt Neg.toReal+Λ^(-(q 3/8))*1≤row
    have hh:=mul_le_mul_of_nonneg_right hCurrent (rpow_nonneg hm χ)
    dsimp only [row,signedLinear,pastLinear]
    nlinarith only [hh]
  calc
    _≤∑k:Fin N,NativeHigherMasterCoefficient.constant (aC k) (aP k) (aG k) (aB k)
        (Cc k) (Ci k) (Cp k) (Cg k) (Cb k) q*row:=by
      apply Finset.sum_le_sum
      intro k _
      exact (NativeHigherMasterCoefficient.cap (aC k) (aP k) (aG k) (aB k)
        (Cc k) (Ci k) (Cp k) (Cg k) (Cb k) q hq Neg hΛ hR hm hH0 hH1 hχ).trans
          (mul_le_mul_of_nonneg_left hrow (NativeHigherMasterCoefficient.constant_nonneg
            (aC k) (aP k) (aG k) (aB k) (Cc k) (Ci k) (Cp k) (Cg k) (Cb k) q hq))
    _=_:=by rw [←Finset.sum_mul];rfl

theorem signed_limit(q:Fin 4→ℝ)(hq:0<q 2):
    Tendsto (signedLinear q) atTop (𝓝 0):=
  tendsto_rpow_neg_atTop (div_pos hq (by norm_num))

theorem scaled_past{β:ℝ}(q:Fin 4→ℝ){Λ:ℝ}(hΛ:0<Λ):
    energyScale β Λ*pastLinear q Λ=Λ^(-(3*β/10+q 1/8)):=by
  unfold energyScale pastLinear
  rw [←rpow_add hΛ]
  congr 1
  dsimp [SHE.rho]
  ring

theorem past_limit{β:ℝ}(hβ:0<β)(q:Fin 4→ℝ)(hq:0<q 1):
    Tendsto (fun Λ=>energyScale β Λ*pastLinear q Λ) atTop (𝓝 0):=by
  apply (tendsto_rpow_neg_atTop (by linarith only [hβ,hq]:0<3*β/10+q 1/8)).congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with Λ hΛ
  exact (scaled_past q hΛ).symm

/-- The strict bad degree is retained until the error budget is chosen.
Thus any fixed structural multiplier can be absorbed into an arbitrary
fraction of the Lambda^-2 error slot for all sufficiently large damping. -/
theorem bad_eventually(q:Fin 4→ℝ)(hq:16<q 3)(C:ℝ){δ:ℝ}(hδ:0<δ):
    ∀ᶠΛ:ℝ in atTop,C*Λ^(-(q 3/8))≤δ*Λ^(-2:ℝ):=by
  have ht:Tendsto (fun Λ:ℝ=>C*Λ^(-(q 3/8-2))) atTop (𝓝 0):=by
    simpa only [mul_zero] using
      (tendsto_rpow_neg_atTop (by linarith only [hq]:0<q 3/8-2)).const_mul C
  filter_upwards [ht.eventually (gt_mem_nhds hδ),eventually_gt_atTop (0:ℝ)] with Λ hs hΛ
  have hh:=mul_le_mul_of_nonneg_right hs.le (rpow_nonneg hΛ.le (-2:ℝ))
  have he:(C*Λ^(-(q 3/8-2)))*Λ^(-2:ℝ)=C*Λ^(-(q 3/8)):=by
    rw [mul_assoc,←rpow_add hΛ]
    congr 2
    ring
  simpa only [he] using hh

end SHE.NativeHigherMasterFiniteCoefficient
