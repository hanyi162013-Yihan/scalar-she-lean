module

public import SHE.NormalizedScalarMoment
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1200000
noncomputable section

namespace SHE.NormalizedProductTelescope
open Set MeasureTheory
open scoped BigOperators
variable {Ω:Type*} [MeasurableSpace Ω] {m:ℕ}

def term (new old source:Fin m→ℝ) (i:Fin m) : ℝ :=
  NormalizedScalarMoment.value (new i-old i) (source i)*
    (∏ j ∈ (Finset.univ.filter (fun j : Fin m => j < i)),old j)*
      ∏ j ∈ (Finset.univ.filter (fun j : Fin m => i < j)),new j

/-- Exact own-endpoint finite product difference after each distinguished
current source has been removed. A different endpoint choice in every
other factor is retained, rather than replaced by an interpolated cap. -/
theorem sum_difference (new old source:Fin m→ℝ)
    (hz:∀i,source i=0→new i=old i) :
    (∏i,new i)-(∏i,old i)=∑i,source i*term new old source i := by
  have hh:=Finset.prod_sub_ordered (Finset.univ:Finset (Fin m)) new (fun i=>new i-old i)
  simp only [sub_sub_cancel] at hh
  have he:(∏i,new i)-(∏i,old i)=
      ∑i,(new i-old i)*(∏ j ∈ (Finset.univ.filter (fun j : Fin m => j < i)),old j)*
        ∏ j ∈ (Finset.univ.filter (fun j : Fin m => i < j)),new j := by linarith
  rw [he]
  apply Finset.sum_congr rfl
  intro i _
  have hf:=NormalizedScalarMoment.factorization (new i-old i) (source i)
    (fun h=>sub_eq_zero.mpr (hz i h))
  unfold term
  conv_lhs => rw [←hf]
  ring

/-- Genuine finite integral telescoping. The current source is OUTSIDE
all auxiliary Gaussian expectations, preserving its later correlation
with the actual current process. -/
theorem integral_difference (μ:Measure Ω) (new old:Ω→Fin m→ℝ) (S:Ω→ℝ)
    (source:Fin m→ℝ) (hz:∀x i,source i=0→new x i=old x i)
    (hnew:Integrable (fun x=>S x*∏i,new x i) μ)
    (hold:Integrable (fun x=>S x*∏i,old x i) μ)
    (hi:∀i,Integrable (fun x=>S x*term (new x) (old x) source i) μ) :
    (∫x,S x*∏i,new x i ∂μ)-(∫x,S x*∏i,old x i ∂μ)=
      ∑i,source i*(∫x,S x*term (new x) (old x) source i ∂μ) := by
  rw [←integral_sub hnew hold]
  have he:(fun x=>S x*(∏i,new x i)-S x*(∏i,old x i))=
      (fun x=>∑i,source i*(S x*term (new x) (old x) source i)) := by
    funext x
    rw [←mul_sub,sum_difference (new x) (old x) source (hz x),Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he,integral_finsetSum _ (fun i _=>(hi i).const_mul _)]
  apply Finset.sum_congr rfl
  intro i _
  exact integral_const_mul _ _

end SHE.NormalizedProductTelescope
