module
public import SHE.AgePartition
public import SHE.StoppedAgeBlocks
public import SHE.DefectCombinedTime
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace SHE.NativeAgePartitionFrame
open Real StoppedAgeBlocks

variable {n:ℕ}{d:Fin n→ℝ}{A:ℝ}(P:AgeClustering.Partition d A)

def time(i:Fin n):ℝ:=d i/(4*Real.pi^2)
def width(j:Fin P.count):ℝ:=P.lower j/(4*Real.pi^2)

 theorem clock_pos:0<(4*Real.pi^2:ℝ):=by positivity
 theorem width_pos(j:Fin P.count):0<width P j:=div_pos (P.lower_pos j) clock_pos
 theorem ratio_one(hA:1≤A):1≤A^n:=one_le_pow₀ hA

/-- Every actual native age block retains its original representative,
with the exact physical-to-unit clock and dimension-only block ratio. -/
 theorem group_bounds(j:Fin P.count)(i:Fin n):
    width P j≤groupData P.label P.rep (time (d:=d)) j i ∧
      groupData P.label P.rep (time (d:=d)) j i≤A^n*width P j:=by
  apply groupData_bounds P.label P.rep P.label_rep (time (d:=d)) (width P) (fun j=>A^n*width P j)
  · intro i
    exact div_le_div_of_nonneg_right (P.lower_bound i) clock_pos.le
  · intro i
    have hi:=div_le_div_of_nonneg_right ((P.upper_bound i).trans (P.ratio (P.label i))) clock_pos.le
    simpa only [time,width,mul_div_assoc] using hi

/-- The small physical-age condition supplies the exact unit-clock
scale needed by the native stopped-block covariance estimate. -/
 theorem scaled_width {θ H:ℝ}(hθ:0≤θ)(hages:∀i,d i≤H)(hθH:θ*H≤4*Real.pi^2)
    (j:Fin P.count):θ*width P j≤1:=by
  have hlo:P.lower j≤H:=by rw [P.lower_eq_rep];exact hages (P.rep j)
  have hmul:θ*P.lower j≤4*Real.pi^2:=(mul_le_mul_of_nonneg_left hlo hθ).trans hθH
  rw [width,←mul_div_assoc]
  exact (div_le_one clock_pos).mpr hmul

/-- The true all-age signed cost factors at original endpoint ages;
there is no replacement of the two individual ages by one minimum. -/
 theorem kernel_factorization(Λ ρ bi bj τ:ℝ)(hi:0<τ+bi):
    DefectCombinedTime.kernel Λ ρ bi bj τ=
      min 1 (Λ*(τ+bi))*(τ+bi)^(-(1/2:ℝ))*(τ+bj)^(-(1/2:ℝ))*
        (1+Λ^(-ρ/2)*(τ+bi)^(-ρ/2)):=by
  unfold DefectCombinedTime.kernel SHE.newTimeKernel
  rw [show -(1/2:ℝ)-ρ/2=-(1/2:ℝ)+(-ρ/2) by ring,Real.rpow_add hi]
  ring

end SHE.NativeAgePartitionFrame
