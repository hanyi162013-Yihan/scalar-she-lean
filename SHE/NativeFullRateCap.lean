module
public import SHE.NativeFourTermScale

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace SHE.NativeFullRateCap
open Real
open scoped ENNReal BigOperators

/-- The four mechanisms retain their original decay degrees. -/
def degree(qc qp qg qb:ℝ):Fin 4→ℝ:=![qc,qp,qg,qb]

/-- Initial and completed current terms combine; the past term occurs
only in completed windows. Relative and arbitrary bad terms occur on
both genuine pieces of the original output clock. -/
def coefficient(aC aP aG aB:ℝ≥0∞)(Cc Ci Cp Cg Cb G H χ:ℝ)(Neg:ℝ≥0∞):Fin 4→ℝ≥0∞:=
  ![aC*(ENNReal.ofReal Ci+ENNReal.ofReal Cc)*(ENNReal.ofReal G^χ*ENNReal.ofReal H^(1-χ)),
    aP*ENNReal.ofReal Cp*ENNReal.ofReal G,
    2*aG*ENNReal.ofReal Cg*Neg,2*aB*ENNReal.ofReal Cb*ENNReal.ofReal H]

/-- Exact four-rate form of the actual initial-plus-completed cap. No
inequality merges the arbitrary bad tail with the current exponent. -/
theorem combine(aC aP aG aB:ℝ≥0∞)(Cc Ci Cp Cg Cb G H χ ν qc qp qg qb:ℝ)(Neg:ℝ≥0∞)
    (hν:0<ν):
    (aC*ENNReal.ofReal (Ci*ν^(-qc))*(ENNReal.ofReal G^χ*ENNReal.ofReal H^(1-χ))+
      aG*ENNReal.ofReal (Cg*ν^(-qg))*Neg+aB*ENNReal.ofReal (Cb*ν^(-qb))*ENNReal.ofReal H)+
    (aC*ENNReal.ofReal (Cc*ν^(-qc))*(ENNReal.ofReal G^χ*ENNReal.ofReal H^(1-χ))+
      aP*ENNReal.ofReal (Cp*ν^(-qp))*ENNReal.ofReal G+
      aG*ENNReal.ofReal (Cg*ν^(-qg))*Neg+aB*ENNReal.ofReal (Cb*ν^(-qb))*ENNReal.ofReal H)=
    ∑i,coefficient aC aP aG aB Cc Ci Cp Cg Cb G H χ Neg i*
      ENNReal.ofReal (ν^(-degree qc qp qg qb i)):=by
  simp only [ENNReal.ofReal_mul' (Real.rpow_nonneg hν.le _)]
  simp [Fin.sum_univ_succ,coefficient,degree]
  ring

end SHE.NativeFullRateCap
