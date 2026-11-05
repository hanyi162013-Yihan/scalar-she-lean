module
public import SHE.TwoPointHeatLine
public import SHE.CircleCut

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
namespace SHE.TwoPointHeatTorus
open Real Set MeasureTheory HeatLine HeatTorus HeatTorusKernel FourierHeatLine
open scoped BigOperators
local instance : Fact (0<(1:ℝ)):=⟨zero_lt_one⟩

theorem separated_lower:
    ∃h:ℝ,0<h ∧ h≤1 ∧ ∀t:ℝ,0<t→t≤h→∀x y:UnitAddCircle,
      4*sqrt t≤dist x y→∀u v:ℝ,
        (u^2+v^2)/(32*Real.pi*sqrt t)≤
          ‖(u:ℂ)•unitHeatKernel t x+(v:ℂ)•unitHeatKernel t y‖^2:=by
  obtain ⟨h,hh,hh1,henergy⟩:=HeatTorus.exists_heat_span_periodization_energy_bound 2
    (CircleCut.margin_pos 2) (circle_margin_le_one 2)
  refine ⟨h,hh,hh1,?_⟩
  intro t ht hth x y hsep u v
  let a:Fin 2→UnitAddCircle:=![x,y]
  obtain ⟨c,b,hb,hbm⟩:=CircleCut.exists_interior_lifts 2 a
  have hb0:(b 0:UnitAddCircle)+c=x:=hb 0
  have hb1:(b 1:UnitAddCircle)+c=y:=hb 1
  have hd:dist x y≤|b 0-b 1|:=by
    calc
      _=dist (b 0:UnitAddCircle) (b 1:UnitAddCircle):=by rw [←hb0,←hb1,dist_add_right]
      _=‖((b 0-b 1:ℝ):UnitAddCircle)‖:=by rw [dist_eq_norm,QuotientAddGroup.mk_sub]
      _≤‖b 0-b 1‖:=QuotientAddGroup.norm_mk_le_norm
      _=|b 0-b 1|:=Real.norm_eq_abs _
  let ts:Fin 2→ℝ:=fun _=>t
  let z:Fin 2→ℂ:=![(u:ℂ),(v:ℂ)]
  let f:ℂ→ℂ:=∑i:Fin 2,z i•heatEntire (ts i) (b i)
  have hf:f∈Submodule.span ℂ (Set.range (fun i=>heatEntire (ts i) (b i))):=by
    apply Submodule.sum_mem
    intro i _
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i,rfl⟩)
  have hf_pair:f=TwoPointHeatLine.pair t (b 0) (b 1) u v:=by
    funext w
    simp only [f,Fin.sum_univ_two,Pi.add_apply,Pi.smul_apply,z,Matrix.cons_val_zero,Matrix.cons_val_one,
      smul_eq_mul,ts,TwoPointHeatLine.pair]
  have hl:=TwoPointHeatLine.separated_lower ht (b 0) (b 1) u v (hsep.trans hd)
  rw [←hf_pair] at hl
  let per:=HeatTorus.periodizationL2 ts b (fun _=>ht) f hf
  have he:(∫w:ℝ,‖f (w:ℂ)‖^2)≤4*‖per‖^2:=henergy ts b (fun _=>ht) (fun _=>hth) hbm f hf
  have hp:HeatTorusKernel.translate c per=(heatMass t:ℂ)•
      ((u:ℂ)•unitHeatKernel t x+(v:ℂ)•unitHeatKernel t y):=by
    rw [show per=∑i:Fin 2,(z i*(heatMass (ts i):ℂ))•unitHeatKernel (ts i) (b i:UnitAddCircle) from
      HeatTorusKernel.periodizationL2_eq_heat_sum ts b (fun _=>ht) f hf z rfl]
    rw [map_sum]
    simp only [Fin.sum_univ_two,map_smul,translate_unitHeatKernel ht,z,Matrix.cons_val_zero,
      Matrix.cons_val_one,ts,hb0,hb1,smul_add,smul_smul]
    congr 1 <;> ring
  have hn:‖per‖^2=(4*Real.pi*t)*
      ‖(u:ℂ)•unitHeatKernel t x+(v:ℂ)•unitHeatKernel t y‖^2:=by
    rw [←HeatTorusKernel.translate_norm c per,hp,norm_smul,mul_pow,Complex.norm_real,
      Real.norm_eq_abs,sq_abs,heatMass,sq_sqrt (by positivity)]
  rw [hn] at he
  have hbound:(sqrt t/2)*(u^2+v^2)≤16*Real.pi*t*
      ‖(u:ℂ)•unitHeatKernel t x+(v:ℂ)•unitHeatKernel t y‖^2:=by linarith
  have hsq:sqrt t^2=t:=sq_sqrt ht.le
  have halg:(sqrt t/2)*(32*Real.pi*sqrt t*
      ‖(u:ℂ)•unitHeatKernel t x+(v:ℂ)•unitHeatKernel t y‖^2)=
        16*Real.pi*t*‖(u:ℂ)•unitHeatKernel t x+(v:ℂ)•unitHeatKernel t y‖^2:=by
    calc
      _=16*Real.pi*(sqrt t)^2*‖(u:ℂ)•unitHeatKernel t x+(v:ℂ)•unitHeatKernel t y‖^2:=by ring
      _=_:=by rw [hsq]
  have hfinal:u^2+v^2≤32*Real.pi*sqrt t*
      ‖(u:ℂ)•unitHeatKernel t x+(v:ℂ)•unitHeatKernel t y‖^2:=by
    apply (mul_le_mul_iff_right₀ (by positivity:0<sqrt t/2)).mp
    simpa only [mul_comm _ (sqrt t/2),halg] using hbound
  apply (div_le_iff₀ (by positivity:0<32*Real.pi*sqrt t)).mpr
  simpa only [mul_comm _ (32*Real.pi*sqrt t)] using hfinal

end SHE.TwoPointHeatTorus
