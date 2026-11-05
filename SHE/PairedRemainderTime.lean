module

public import SHE.HeterogeneousSimplexIntegral

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1900000
noncomputable section

namespace SHE.PairedRemainderTime
open Set MeasureTheory Real GaussianAssignmentBlocks HeterogeneousAssignmentKernel
open scoped BigOperators
variable {k : ℕ}

/-- All original rough ages, including empty blocks, are counted once.
Only the distinguished paired slot has the reduced (beta-chi)/4 degree;
all original root clips survive in their exact rootMass factor. -/
theorem paired_density_integral_bound (cs : List (Fin k×Fin (k+1)))
    (hc : cs∈assignments (m:=k+1) (List.finRange k))
    {ν β χ w : ℝ} (hν : 0≤ν) (hβ : 0<β) (hβ1 : β≤1)
    (hχ : 0≤χ) (hχβ : χ<β) (hw : 0<w) (j0 : Fin k) :
    let a:=pairedDegree β χ j0
    let G:=fun d : Fin k→ℝ=>w^(emptyDegree cs a)*assignedDensity cs ν a 1 w d
    Integrable G ∧ (∫ d,G d)≤
      (((k+1:ℕ):ℝ)^2*inverseDegreeProduct cs hc a)*
        w^((k:ℝ)*β/4-χ/4)*rootMass ν w^(AllocatedAssignmentKernel.rootCount cs) := by
  intro a G
  have ha (l : Fin (k+1)) (_ : l≠0) : 0<a l :=
    (pairedDegree_pos_le_one hβ hβ1 hχ hχβ j0 l).1
  have ha1 (l : Fin (k+1)) (_ : l≠0) : a l≤1 :=
    (pairedDegree_pos_le_one hβ hβ1 hχ hχβ j0 l).2
  have hh:=assignedDensity_integral_bound cs hc hν ha ha1 (by norm_num : 0<(1:ℝ)) le_rfl hw
  refine ⟨hh.1.const_mul _,?_⟩
  change (∫ d,w^(emptyDegree cs a)*assignedDensity cs ν a 1 w d)≤_
  rw [integral_const_mul]
  have he : emptyDegree cs a+(1+assignedDegree cs a-1)=(k:ℝ)*β/4-χ/4 := by
    have ht:=paired_total_degree cs β χ j0
    change assignedDegree cs a+emptyDegree cs a=_ at ht
    linarith
  have hz:=mul_le_mul_of_nonneg_left hh.2 (rpow_nonneg hw.le (emptyDegree cs a))
  refine hz.trans_eq ?_
  simp only [div_one]
  calc
    _=(((k+1:ℕ):ℝ)^2*inverseDegreeProduct cs hc a)*
        (w^(emptyDegree cs a)*w^(1+assignedDegree cs a-1))*
          rootMass ν w^(AllocatedAssignmentKernel.rootCount cs) := by ring
    _=_ := by rw [←rpow_add hw,he]

/-- The native band-time condition restores the one paired quarter-age
loss, costing exactly lambda^chi and preserving the full N*beta/4 gain. -/
theorem band_age_recovery {lam w χ β : ℝ} (hlam : 0<lam) (hw : 0<w)
    (hχ : 0≤χ) (hscale : lam^(-4:ℝ)≤w) (k : ℕ) :
    lam^(-β)*w^((k:ℝ)*β/4-χ/4)≤lam^(-β+χ)*w^((k:ℝ)*β/4) := by
  have ht : w^(-χ/4)≤lam^χ := by
    have hh:=rpow_le_rpow_of_nonpos (rpow_pos_of_pos hlam (-4)) hscale
      (show -χ/4≤0 by linarith)
    have he : (-4:ℝ)*(-χ/4)=χ:=by ring
    rw [←rpow_mul hlam.le,he] at hh
    exact hh
  have he : w^((k:ℝ)*β/4-χ/4)=w^((k:ℝ)*β/4)*w^(-χ/4) := by
    rw [←rpow_add hw]
    congr 1
    ring
  rw [he]
  have hh:=mul_le_mul_of_nonneg_left ht (rpow_nonneg hw.le ((k:ℝ)*β/4))
  have hh':=mul_le_mul_of_nonneg_left hh (rpow_nonneg hlam.le (-β))
  refine hh'.trans_eq ?_
  rw [rpow_add hlam]
  ring

end SHE.PairedRemainderTime
