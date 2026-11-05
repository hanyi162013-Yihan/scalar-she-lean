module
public import SHE.HighFiniteRemainderWeight
@[expose] public section
noncomputable section
set_option autoImplicit false
namespace SHE.BareGaussianRemainderDegree
open Real

def degree(β χ η:ℝ)(N:ℕ):ℝ:=
  2*β-2*(χ+η)+(3*β/2)*((N:ℝ)*β-χ-η)

/-- The exact finite-depth energy degree after substituting the actual
Gaussian band amplitude and the individual h=frequency^(-3 beta). -/
theorem weight{lam β χ η:ℝ}(hlam:1≤lam)(ha:0≤χ+η)(N:ℕ):
    (lam^(-β))^2*(1+lam)^(2*(χ+η))*
      (lam^(-3*β))^(((N:ℝ)*β-χ-η)/2)≤
        (2:ℝ)^(2*(χ+η))*lam^(-degree β χ η N):=by
  have hl:0<lam:=zero_lt_one.trans_le hlam
  have hp:(1+lam)^(2*(χ+η))≤(2*lam)^(2*(χ+η)):=
    rpow_le_rpow (by linarith) (by linarith) (mul_nonneg (by norm_num) ha)
  rw [mul_rpow (by norm_num:(0:ℝ)≤2) hl.le] at hp
  have hh:=mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hp (sq_nonneg (lam^(-β))))
    (rpow_nonneg (rpow_nonneg hl.le (-3*β)) (((N:ℝ)*β-χ-η)/2))
  have he:lam^(-2*β)*lam^(2*(χ+η))*(lam^(-3*β))^(((N:ℝ)*β-χ-η)/2)=
      lam^(-degree β χ η N):=by
    rw [←rpow_mul hl.le,←rpow_add hl,←rpow_add hl]
    congr 1
    unfold degree
    ring
  have hs:(lam^(-β))^2=lam^(-2*β):=by
    rw [←rpow_mul_natCast hl.le]
    congr 1
    norm_num
    ring
  rw [hs]
  rw [hs] at hh
  calc
    _≤_:=hh
    _=(2:ℝ)^(2*(χ+η))*(lam^(-2*β)*lam^(2*(χ+η))*(lam^(-3*β))^(((N:ℝ)*β-χ-η)/2)):=by ring
    _=_:=by rw [he]

/-- Any larger fixed finite depth retains the conservative degree8. -/
theorem eight_le{β η:ℝ}(hβ:0<β)(hb:β≤4/25)(hη:0≤η)(hηb:η≤β/4)
    (N:ℕ)(hN:SHE.depth β≤N):8≤degree β (β/2) η N:=by
  have hd:=(HighFiniteRemainderDegree.degree_margin hβ hb hη hηb).2
  have hNr:(SHE.depth β:ℝ)≤(N:ℝ):=by exact_mod_cast hN
  have hm:=mul_le_mul_of_nonneg_left hNr (sq_nonneg β)
  unfold degree
  nlinarith
end SHE.BareGaussianRemainderDegree
