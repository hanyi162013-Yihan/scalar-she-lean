module

public import SHE.PhysicalAssignedTimeTotal

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1900000
noncomputable section

namespace SHE.AllocatedAssignmentKernel
open Set MeasureTheory Real GaussianAssignmentBlocks AssignmentGapPartition
open scoped BigOperators
open Classical
variable {k : ℕ}

theorem all_root_count (cs : List (Fin k×Fin (k+1)))
    (hc : cs∈assignments (m:=k+1) (List.finRange k)) (hb : roughCount cs=0) : rootCount cs=k := by
  have hf : Finset.univ.filter (fun l : Fin (k+1)=>l≠0 ∧ block cs l≠[])=∅ :=
    Finset.card_eq_zero.mp hb
  have hl (i : Fin k) : label cs hc i=0 := by
    by_contra h
    have hm : i∈block cs (label cs hc i) := (mem_block_iff_label cs hc i _).mpr rfl
    have hn : block cs (label cs hc i)≠[] := by
      intro he
      simpa only [he,List.not_mem_nil] using hm
    have hh : label cs hc i∈Finset.univ.filter (fun l : Fin (k+1)=>l≠0 ∧ block cs l≠[]) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,h,hn⟩
    rw [hf] at hh
    exact Finset.notMem_empty _ hh
  rw [←root_count_eq cs hc]
  have he : Finset.univ.filter (fun i=>rootFlag cs hc i=true)=(Finset.univ : Finset (Fin k)) := by
    ext i
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,rootFlag,hl,decide_true,true_iff]
  rw [he,Finset.card_univ,Fintype.card_fin]

def squareAmplitude (cs : List (Fin k×Fin (k+1))) (a ν w : ℝ) : ℝ :=
  w^(a*(roughCount cs:ℝ)-(1/2:ℝ))*rootMass ν w^(rootCount cs)

theorem squareAmplitude_sq (cs : List (Fin k×Fin (k+1))) (a ν : ℝ) {w : ℝ} (hw : 0≤w) :
    (squareAmplitude cs a ν w)^2=
      w^(2*a*(roughCount cs:ℝ)-1)*rootMass ν w^(2*rootCount cs) := by
  unfold squareAmplitude
  rw [mul_pow,←Real.rpow_mul_natCast hw]
  have he : (a*(roughCount cs:ℝ)-(1/2:ℝ))*(2:ℕ)=2*a*(roughCount cs:ℝ)-1 := by norm_num;ring
  rw [he,←pow_mul]
  congr 1
  ring

theorem square_degree_pos (cs : List (Fin k×Fin (k+1)))
    (hc : cs∈assignments (m:=k+1) (List.finRange k)) (hk : 0<k) {a : ℝ} (ha : 0<a) :
    0<2*a*(roughCount cs:ℝ)+((2*rootCount cs:ℕ):ℝ)/4 := by
  by_cases hb : roughCount cs=0
  · rw [all_root_count cs hc hb,hb]
    have hkp : (0:ℝ)<k := by exact_mod_cast hk
    push_cast
    nlinarith
  · have hbp : (0:ℝ)<roughCount cs := by exact_mod_cast Nat.pos_of_ne_zero hb
    have hr : (0:ℝ)≤rootCount cs := Nat.cast_nonneg _
    push_cast
    nlinarith

/-- The actual finite-assignment square corner is convergent. The
all-root case follows from its actual root count and the exact vanishing
root mass, rather than an undefined integral of `1/w`. -/
theorem squareAmplitude_intervalIntegrable (cs : List (Fin k×Fin (k+1)))
    (hc : cs∈assignments (m:=k+1) (List.finRange k)) (hk : 0<k)
    {a ν T : ℝ} (ha : 0<a) (hν : 0<ν) (hT : 0≤T) :
    IntervalIntegrable (fun w=>(squareAmplitude cs a ν w)^2) volume 0 T := by
  have hh := weighted_root_integrable hν hT (square_degree_pos cs hc hk ha)
  apply (intervalIntegrable_congr_uIoo (μ:=volume) (a:=0) (b:=T) ?_).mpr hh
  intro w hw
  rw [uIoo_of_le hT] at hw
  exact squareAmplitude_sq cs a ν hw.1.le

theorem squareAmplitude_integral_bound (cs : List (Fin k×Fin (k+1)))
    (hc : cs∈assignments (m:=k+1) (List.finRange k)) (hk : 0<k)
    {a ν T : ℝ} (ha : 0<a) (hν : 0<ν) (hT : 0≤T) :
    (∫ w in (0:ℝ)..T,(squareAmplitude cs a ν w)^2)≤
      if roughCount cs=0 then
        (4/((2*rootCount cs:ℕ):ℝ)+rootMass ν T)*rootMass ν T^(2*rootCount cs)
      else T^(2*a*(roughCount cs:ℝ))/(2*a*(roughCount cs:ℝ))*rootMass ν T^(2*rootCount cs) := by
  rw [intervalIntegral.integral_congr_Ioo_of_le hT (fun w hw=>squareAmplitude_sq cs a ν hw.1.le)]
  split_ifs with hb
  · have hr : 0<rootCount cs := by rw [all_root_count cs hc hb];exact hk
    have hh := root_mass_density_integral_le (m:=2*rootCount cs) hν hT (by omega)
    simpa only [hb,Nat.cast_zero,mul_zero,zero_sub,Real.rpow_neg_one] using hh
  · have hd : 0<2*a*(roughCount cs:ℝ) := mul_pos (mul_pos (by norm_num) ha)
      (by exact_mod_cast Nat.pos_of_ne_zero hb)
    exact weighted_root_mass_pos_le hν.le hd hT (2*rootCount cs)

end SHE.AllocatedAssignmentKernel
