module
public import SHE.DeterministicItoShiftLocality
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
namespace SHE.DeterministicItoShift
open MeasureTheory Set PredictableL2
open scoped NNReal ENNReal
variable{Ω C:Type*}[MeasurableSpace Ω]
variable(𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(v:ℝ≥0)

theorem initial_rectangle(A:Set Ω)(hA:MeasurableSet[𝓕 0] A):
    MeasurableSet[𝓕.predictable] ((univ:Set ℝ≥0)×ˢA):=by
  have he:({0}:Set ℝ≥0)×ˢA∪Ioi (0:ℝ≥0)×ˢA=univ×ˢA:=by
    ext p
    simp only [mem_union,mem_prod,mem_singleton_iff,mem_Ioi,mem_univ,true_and]
    constructor
    · intro hp;exact hp.elim And.right And.right
    · intro hp
      by_cases h0:p.1=0
      · exact Or.inl ⟨h0,hp⟩
      · exact Or.inr ⟨lt_of_le_of_ne bot_le (Ne.symm h0),hp⟩
  rw [←he]
  exact (measurableSet_predictable_singleton_bot_prod hA).union
    (measurableSet_predictable_Ioi_prod hA)

/-- The actual original future path is predictable in the shifted
filtration, including its F_v-measurable initial state. -/
theorem forward_predictable:
    @Measurable (ℝ≥0×Ω) (ℝ≥0×Ω) (filtration 𝓕 v).predictable 𝓕.predictable
      (fun p=>(v+p.1,p.2)):=by
  letI:MeasurableSpace (ℝ≥0×Ω):=(filtration 𝓕 v).predictable
  rw [measurable_iff_comap_le,MeasurableSpace.comap_le_iff_le_map]
  apply measurableSpace_le_predictable_of_measurableSet
  · intro A hA
    change MeasurableSet[(filtration 𝓕 v).predictable]
      ((fun p:ℝ≥0×Ω=>(v+p.1,p.2)) ⁻¹' ({0}×ˢA))
    by_cases hv:v=0
    · subst v
      change MeasurableSet[𝓕 (0:ℝ≥0)] A at hA
      have hA':MeasurableSet[(filtration 𝓕 0) 0] A:=by
        change MeasurableSet[𝓕 ((0:ℝ≥0)+0)] A
        rw [_root_.zero_add]
        exact hA
      have he:(fun p:ℝ≥0×Ω=>((0:ℝ≥0)+p.1,p.2)) ⁻¹' ({0}×ˢA)=({0}:Set ℝ≥0)×ˢA:=by
        ext p
        simp only [mem_preimage,_root_.zero_add,Prod.mk.eta]
      rw [he]
      exact measurableSet_predictable_singleton_bot_prod (𝓕:=filtration 𝓕 0) hA' 
    · have he:(fun p:ℝ≥0×Ω=>(v+p.1,p.2)) ⁻¹' ({0}×ˢA)=∅:=by
        ext p
        simp only [mem_preimage,mem_prod,mem_singleton_iff,mem_empty_iff_false,iff_false,not_and]
        intro hp
        have h0:v=0:=(add_eq_zero.mp hp).1
        exact False.elim (hv h0)
      rw [he]
      exact MeasurableSet.empty
  · intro t A hA
    change MeasurableSet[(filtration 𝓕 v).predictable]
      ((fun p:ℝ≥0×Ω=>(v+p.1,p.2)) ⁻¹' (Ioi t×ˢA))
    by_cases ht:t<v
    · have he:(fun p:ℝ≥0×Ω=>(v+p.1,p.2)) ⁻¹' (Ioi t×ˢA)=univ×ˢA:=by
        ext p
        simp only [mem_preimage,mem_prod,mem_Ioi,mem_univ,true_and]
        exact and_iff_right (ht.trans_le (le_add_of_nonneg_right p.1.2))
      rw [he]
      exact initial_rectangle (filtration 𝓕 v) A (by
        change MeasurableSet[𝓕 (v+0)] A
        rw [_root_.add_zero]
        exact 𝓕.mono ht.le A hA)
    · have hvt:v≤t:=le_of_not_gt ht
      have hsum:v+(t-v)=t:=by simpa only [add_comm] using tsub_add_cancel_of_le hvt
      have hA':MeasurableSet[(filtration 𝓕 v) (t-v)] A:=by
        change MeasurableSet[𝓕 (v+(t-v))] A
        rw [hsum]
        exact hA
      have he:(fun p:ℝ≥0×Ω=>(v+p.1,p.2)) ⁻¹' (Ioi t×ˢA)=Ioi (t-v)×ˢA:=by
        ext p
        change (t<v+p.1∧p.2∈A)↔(t-v<p.1∧p.2∈A)
        have hvreal:((t-v:ℝ≥0):ℝ)=(t:ℝ)-(v:ℝ):=NNReal.coe_sub hvt
        have hh:t<v+p.1↔t-v<p.1:=by
          constructor
          · intro hh
            have hh':(t:ℝ)<(v:ℝ)+(p.1:ℝ):=by exact_mod_cast hh
            have:(t:ℝ)-(v:ℝ)<(p.1:ℝ):=by linarith
            rw [←hvreal] at this
            exact_mod_cast this
          · intro hh
            have hh':((t-v:ℝ≥0):ℝ)<(p.1:ℝ):=by exact_mod_cast hh
            rw [hvreal] at hh'
            have:(t:ℝ)<(v:ℝ)+(p.1:ℝ):=by linarith
            exact_mod_cast this
        exact and_congr_left (fun _=>hh)
      rw [he]
      exact measurableSet_predictable_Ioi_prod hA'

theorem pull_predictable{E:Type*}[TopologicalSpace E]
    (U:ℝ≥0×Ω→E)(hU:StronglyMeasurable[𝓕.predictable] U):
    StronglyMeasurable[(filtration 𝓕 v).predictable] (fun p=>U (v+p.1,p.2)):=
  hU.comp_measurable (forward_predictable 𝓕 v)


variable[NormedAddCommGroup C][InnerProductSpace ℝ C]
variable[MeasurableSpace C][BorelSpace C][SecondCountableTopology C]
variable(μ:Measure Ω)[SFinite μ](H h:ℝ≥0)(hvh:v+h≤H)
include hvh

/-- Pull the actual original input onto its local deterministic clock. -/
theorem pull_memLp(f:Process (E:=C) 𝓕 μ H):
    @MemLp _ _ (filtration 𝓕 v).predictable _ _ (fun p:ℝ≥0×Ω=>f (v+p.1,p.2)) 2
      ((energyMeasure μ h).trim (predictable_le_product (filtration 𝓕 v))):=by
  have hp:StronglyMeasurable[(filtration 𝓕 v).predictable] (fun p:ℝ≥0×Ω=>f (v+p.1,p.2)):=
    pull_predictable 𝓕 v f (Lp.stronglyMeasurable f)
  have ha:MemLp f 2 (energyMeasure μ H):=memLp_of_memLp_trim (predictable_le_product 𝓕) (Lp.memLp f)
  have hs:=((ha.restrict (Ioc v (v+h)×ˢuniv))).comp_measurePreserving (product_translation μ H v h hvh)
  exact (le_of_eq (eLpNorm_trim (predictable_le_product (filtration 𝓕 v)) hp)).trans_lt hs

def pull(f:Process (E:=C) 𝓕 μ H):Process (E:=C) (filtration 𝓕 v) μ h:=
  (pull_memLp 𝓕 v μ H h hvh f).toLp (fun p:ℝ≥0×Ω=>f (v+p.1,p.2))

theorem pull_ae(f:Process (E:=C) 𝓕 μ H):
    pull 𝓕 v μ H h hvh f=ᵐ[energyMeasure μ h] (fun p:ℝ≥0×Ω=>f (v+p.1,p.2)):=
  ae_eq_of_ae_eq_trim (pull_memLp 𝓕 v μ H h hvh f).coeFn_toLp

def windowInput(f:Process (E:=C) 𝓕 μ H):Process (E:=C) 𝓕 μ H:=
  ((Lp.memLp f).indicator (measurableSet_predictable_Ioc_prod v (v+h)
    (MeasurableSet.univ (m:=𝓕 v))).nullMeasurableSet).toLp
      ((Ioc v (v+h)×ˢuniv).indicator f)

theorem windowInput_ae(f:Process (E:=C) 𝓕 μ H):
    windowInput 𝓕 v μ H h f=ᵐ[energyMeasure μ H] (Ioc v (v+h)×ˢuniv).indicator f:=
  ae_eq_of_ae_eq_trim ((Lp.memLp f).indicator (measurableSet_predictable_Ioc_prod v (v+h)
    (MeasurableSet.univ (m:=𝓕 v))).nullMeasurableSet).coeFn_toLp

omit hvh in
theorem extend_pull_field(f:ℝ≥0×Ω→C):
    extend v h (fun p=>f (v+p.1,p.2))=(Ioc v (v+h)×ˢuniv).indicator f:=by
  classical
  funext p
  by_cases hv:v<p.1
  · by_cases hu:p.1≤v+h
    · have hp:p∈Ioc v (v+h)×ˢuniv:=⟨⟨hv,hu⟩,mem_univ _⟩
      have he:v+(p.1-v)=p.1:=by simpa only [add_comm] using tsub_add_cancel_of_le hv.le
      simp only [extend,ite_eq_left hv,ite_eq_left hu,relative,he,Set.indicator_of_mem hp]
    · have hp:p∉Ioc v (v+h)×ˢuniv:=fun hp=>hu hp.1.2
      simp only [extend,ite_eq_left hv,ite_eq_right hu,Set.indicator_of_notMem hp]
  · have hp:p∉Ioc v (v+h)×ˢuniv:=fun hp=>hv hp.1.1
    simp only [extend,ite_eq_right hv,Set.indicator_of_notMem hp]

theorem input_pull(f:Process (E:=C) 𝓕 μ H):
    input 𝓕 μ H v h hvh (pull 𝓕 v μ H h hvh f)=windowInput 𝓕 v μ H h f:=by
  apply PastItoAlgebra.eq_of_ambient_ae
  have he:=extend_ae 𝓕 μ H v h hvh (Lp.stronglyMeasurable (pull 𝓕 v μ H h hvh f)).measurable
    (pull_predictable 𝓕 v f (Lp.stronglyMeasurable f)).measurable (pull_ae 𝓕 v μ H h hvh f)
  filter_upwards [input_ae 𝓕 μ H v h hvh (pull 𝓕 v μ H h hvh f),he,windowInput_ae 𝓕 v μ H h hvh f] with p hi he hw
  rw [hi,he,hw,congrFun (extend_pull_field (v:=v) (h:=h) f) p]

theorem window_eq_post(f:Process (E:=C) 𝓕 μ H)
    (hs:∀ᵐp∂energyMeasure μ H,v+h<p.1→f p=0):
    windowInput 𝓕 v μ H h f=PastItoInputs.post 𝓕 μ H v f:=by
  apply PastItoAlgebra.eq_of_ambient_ae
  filter_upwards [windowInput_ae 𝓕 v μ H h hvh f,PastItoInputs.post_ae 𝓕 μ H v f,hs] with p hw hp hs
  rw [hw,hp]
  by_cases hv:v<p.1
  · by_cases hu:p.1≤v+h
    · have hm:p∈Ioc v (v+h)×ˢ(univ:Set Ω):=⟨⟨hv,hu⟩,mem_univ _⟩
      rw [Set.indicator_of_mem hm,ite_eq_left hv]
    · have hm:p∉Ioc v (v+h)×ˢ(univ:Set Ω):=fun hp=>hu hp.1.2
      rw [Set.indicator_of_notMem hm,ite_eq_left hv,hs (lt_of_not_ge hu)]
  · have hm:p∉Ioc v (v+h)×ˢ(univ:Set Ω):=fun hp=>hv hp.1.1
    rw [Set.indicator_of_notMem hm,ite_eq_right hv]

variable{E:Type*}[NormedAddCommGroup E][InnerProductSpace ℝ E]
theorem integral_pull(J:StandardTerminalIto (C:=C) (E:=E) 𝓕 μ H)(f:Process (E:=C) 𝓕 μ H):
    (integral 𝓕 μ H v h hvh J).integral (pull 𝓕 v μ H h hvh f)=
      J.integral (windowInput 𝓕 v μ H h f):=by
  rw [integral_eq,input_pull]

end SHE.DeterministicItoShift
