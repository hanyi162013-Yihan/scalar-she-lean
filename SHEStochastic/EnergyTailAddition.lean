module

public import SHEStochastic.UniformEnergyBound

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHEStochastic.EnergyTailAddition
open MeasureTheory Filter Set
open scoped ENNReal Topology

theorem pointwise (e d R : ℝ) (he : 0≤e) (hd : 0≤d) :
    (if 2*R≤e+d then ENNReal.ofReal (e+d) else 0)≤
      2*((if R≤e then ENNReal.ofReal e else 0)+(if R≤d then ENNReal.ofReal d else 0)) := by
  by_cases hlarge : 2*R≤e+d
  · rw [if_pos hlarge]
    have hp : e+d≤2*((if R≤e then e else 0)+(if R≤d then d else 0)) := by
      split_ifs <;> linarith
    have hE : 0≤(if R≤e then e else 0) := by split_ifs <;> positivity
    have hD : 0≤(if R≤d then d else 0) := by split_ifs <;> positivity
    apply (ENNReal.ofReal_le_ofReal hp).trans_eq
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ)≤2),ENNReal.ofReal_ofNat,
      ENNReal.ofReal_add hE hD]
    by_cases he' : R≤e <;> by_cases hd' : R≤d <;> simp [he',hd']
  · rw [if_neg hlarge]
    exact bot_le

theorem bound {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (e d : Ω → ℝ) (he : Measurable e) (hd : Measurable d)
    (hE : ∀ x,0≤e x) (hD : ∀ x,0≤d x) (R : ℝ) :
    (∫⁻ x in {x | 2*R≤e x+d x},ENNReal.ofReal (e x+d x) ∂μ)≤
      2*((∫⁻ x in {x | R≤e x},ENNReal.ofReal (e x) ∂μ)+
        (∫⁻ x in {x | R≤d x},ENNReal.ofReal (d x) ∂μ)) := by
  let E := {x | R≤e x}.indicator (fun x => ENNReal.ofReal (e x))
  let D := {x | R≤d x}.indicator (fun x => ENNReal.ofReal (d x))
  have hmE : Measurable E := he.ennreal_ofReal.indicator (measurableSet_le measurable_const he)
  have hmD : Measurable D := hd.ennreal_ofReal.indicator (measurableSet_le measurable_const hd)
  have hmSum : Measurable (fun x => e x+d x) := he.add hd
  rw [←lintegral_indicator (measurableSet_le measurable_const hmSum)]
  calc
    _ ≤ ∫⁻ x,2*(E x+D x) ∂μ := by
      apply lintegral_mono
      intro x
      simpa only [Set.indicator_apply,Set.mem_setOf_eq,E,D] using pointwise (e x) (d x) R (hE x) (hD x)
    _ = 2*((∫⁻ x,E x ∂μ)+(∫⁻ x,D x ∂μ)) := by
      have hmED : Measurable (fun x => E x+D x) := hmE.add hmD
      rw [lintegral_const_mul'' _ hmED.aemeasurable,lintegral_add_left hmE]
    _ = _ := by
      rw [show (∫⁻ x,E x ∂μ)=∫⁻ x in {x | R≤e x},ENNReal.ofReal (e x) ∂μ from
          lintegral_indicator (measurableSet_le measurable_const he) _,
        show (∫⁻ x,D x ∂μ)=∫⁻ x in {x | R≤d x},ENNReal.ofReal (d x) ∂μ from
          lintegral_indicator (measurableSet_le measurable_const hd) _]

/-- Energy UI is stable under addition, retaining different source
probability spaces and possible dependence between the energies. -/
theorem uniform_tails {Ω : ℕ → Type*} [∀ m,MeasurableSpace (Ω m)]
    (P : ∀ m,Measure (Ω m)) (e d : ∀ m,Ω m → ℝ)
    (he : ∀ m,Measurable (e m)) (hd : ∀ m,Measurable (d m))
    (hE : ∀ m x,0≤e m x) (hD : ∀ m x,0≤d m x)
    (hUIe : Tendsto (fun R : ℕ => ⨆ m,∫⁻ x in {x | (R : ℝ)≤e m x},ENNReal.ofReal (e m x) ∂P m) atTop (𝓝 0))
    (hUId : Tendsto (fun R : ℕ => ⨆ m,∫⁻ x in {x | (R : ℝ)≤d m x},ENNReal.ofReal (d m x) ∂P m) atTop (𝓝 0)) :
    Tendsto (fun R : ℕ => ⨆ m,∫⁻ x in {x | (R : ℝ)≤e m x+d m x},
      ENNReal.ofReal (e m x+d m x) ∂P m) atTop (𝓝 0) := by
  have hhalf : Tendsto (fun N : ℕ => N/2) atTop atTop := by
    apply tendsto_atTop.mpr
    intro N
    exact eventually_atTop.mpr ⟨2*N,fun m hm => by omega⟩
  have ht : Tendsto (fun N : ℕ => 2*((⨆ m,∫⁻ x in {x | ((N/2 : ℕ) : ℝ)≤e m x},ENNReal.ofReal (e m x) ∂P m)+
      (⨆ m,∫⁻ x in {x | ((N/2 : ℕ) : ℝ)≤d m x},ENNReal.ofReal (d m x) ∂P m))) atTop (𝓝 0) := by
    simpa only [add_zero,mul_zero,Function.comp_def,Pi.add_apply] using ENNReal.Tendsto.const_mul (a := (2 : ℝ≥0∞))
      ((hUIe.add hUId).comp hhalf) (Or.inr (by norm_num))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht (fun _ => bot_le)
  intro N
  apply iSup_le
  intro m
  apply (lintegral_mono_set (show {x | (N : ℝ)≤e m x+d m x}⊆
      {x | 2*((N/2 : ℕ) : ℝ)≤e m x+d m x} from fun x hx => by
        have hh : 2*((N/2 : ℕ) : ℝ)≤(N : ℝ) := by exact_mod_cast (show 2*(N/2)≤N by omega)
        exact hh.trans hx)).trans
    ((bound (P m) (e m) (d m) (he m) (hd m) (hE m) (hD m) ((N/2 : ℕ) : ℝ)).trans ?_)
  apply mul_le_mul_right _ 2
  exact add_le_add
    (le_iSup (fun j => ∫⁻ x in {x | ((N/2 : ℕ) : ℝ)≤e j x},ENNReal.ofReal (e j x) ∂P j) m)
    (le_iSup (fun j => ∫⁻ x in {x | ((N/2 : ℕ) : ℝ)≤d j x},ENNReal.ofReal (d j x) ∂P j) m)

end SHEStochastic.EnergyTailAddition
