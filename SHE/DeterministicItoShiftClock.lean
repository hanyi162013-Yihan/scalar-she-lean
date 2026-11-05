module
public import SHE.PredictableTime
public import SHE.PredictableTimeDilation
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
set_option linter.style.haveILetI false
namespace SHE.DeterministicItoShift
open MeasureTheory Set PredictableL2
open scoped NNReal ENNReal
variable {Ω C:Type*}[MeasurableSpace Ω]

/-- A deterministic restart clock, with the original sigma algebras. -/
def filtration(𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(v:ℝ≥0):
    Filtration ℝ≥0 ‹MeasurableSpace Ω› where
  seq t:=𝓕 (v+t)
  mono':=by intro s t h;exact 𝓕.mono (by simpa only [add_comm] using add_le_add_left h v)
  le' t:=𝓕.le (v+t)

def after(v:ℝ≥0):Set (ℝ≥0×Ω):=Ioi v×ˢuniv

theorem after_measurable(𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(v:ℝ≥0):
    MeasurableSet[𝓕.predictable] (after (Ω:=Ω) v):=
  measurableSet_predictable_Ioi_prod (𝓕:=𝓕) (MeasurableSet.univ (m:=𝓕 v))

def relative(v:ℝ≥0)(p:ℝ≥0×Ω):ℝ≥0×Ω:=(p.1-v,p.2)

theorem relative_order(v t q:ℝ≥0)(hv:v<q):t<q-v↔v+t<q:=by
  have he:((q-v:ℝ≥0):ℝ)=(q:ℝ)-(v:ℝ):=NNReal.coe_sub hv.le
  constructor
  · intro h
    have hh:(t:ℝ)<((q-v:ℝ≥0):ℝ):=by exact_mod_cast h
    rw [he] at hh
    have:(v:ℝ)+(t:ℝ)<(q:ℝ):=by linarith
    exact_mod_cast this
  · intro h
    have hh:(v:ℝ)+(t:ℝ)<(q:ℝ):=by exact_mod_cast h
    have:(t:ℝ)<((q-v:ℝ≥0):ℝ):=by rw [he];linarith
    exact_mod_cast this

/-- The inverse clock is predictable on the strict post-v region.
Discarding the single initial time avoids assuming F_v is F_{v-}. -/
theorem relative_predictable(𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(v:ℝ≥0):
    @Measurable (after (Ω:=Ω) v) (ℝ≥0×Ω)
      (MeasurableSpace.comap Subtype.val 𝓕.predictable) (filtration 𝓕 v).predictable
      (fun p=>relative v p.val):=by
  letI:MeasurableSpace (ℝ≥0×Ω):=𝓕.predictable
  rw [measurable_iff_comap_le,MeasurableSpace.comap_le_iff_le_map]
  apply measurableSpace_le_predictable_of_measurableSet
  · intro A hA
    change MeasurableSet[MeasurableSpace.comap Subtype.val 𝓕.predictable]
      ((fun p:after (Ω:=Ω) v=>relative v p.val) ⁻¹' ({0}×ˢA))
    have he:(fun p:after (Ω:=Ω) v=>relative v p.val) ⁻¹' ({0}×ˢA)=∅:=by
      ext p
      simp only [mem_preimage,relative,mem_prod,mem_singleton_iff,mem_empty_iff_false,iff_false,not_and]
      intro hh
      have hp:v<p.val.1:=p.property.1
      have hz:0<p.val.1-v:=tsub_pos_iff_lt.mpr hp
      exact False.elim ((ne_of_gt hz) hh)
    rw [he]
    exact MeasurableSet.empty
  · intro t A hA
    change MeasurableSet[MeasurableSpace.comap Subtype.val 𝓕.predictable]
      ((fun p:after (Ω:=Ω) v=>relative v p.val) ⁻¹' (Ioi t×ˢA))
    have he:(fun p:after (Ω:=Ω) v=>relative v p.val) ⁻¹' (Ioi t×ˢA)=
        Subtype.val ⁻¹' (Ioi (v+t)×ˢA):=by
      ext p
      change (t<p.val.1-v∧p.val.2∈A)↔(v+t<p.val.1∧p.val.2∈A)
      exact and_congr_left (fun _=>relative_order v t p.val.1 p.property.1)
    rw [he]
    exact measurable_subtype_coe (measurableSet_predictable_Ioi_prod (𝓕:=𝓕) hA)

/-- Extend a local input by zero outside the actual physical window. -/
def extend[Zero C](v h:ℝ≥0)(f:ℝ≥0×Ω→C)(p:ℝ≥0×Ω):C:=
  if v<p.1 then (if p.1≤v+h then f (relative v p) else 0) else 0

theorem extend_predictable[Zero C][MeasurableSpace C]
    (𝓕:Filtration ℝ≥0 ‹MeasurableSpace Ω›)(v h:ℝ≥0)
    {f:ℝ≥0×Ω→C}(hf:@Measurable _ _ (filtration 𝓕 v).predictable _ f):
    @Measurable _ _ 𝓕.predictable _ (extend v h f):=by
  classical
  letI:MeasurableSpace (ℝ≥0×Ω):=𝓕.predictable
  have hs:MeasurableSet (after (Ω:=Ω) v):=after_measurable 𝓕 v
  apply measurable_of_restrict_of_restrict_compl hs
  · have hu:MeasurableSet {p:after (Ω:=Ω) v|p.val.1≤v+h}:=by
      have hm:MeasurableSet (after (Ω:=Ω) (v+h)):=after_measurable 𝓕 (v+h)
      convert! (measurable_subtype_coe hm).compl using 1
      ext p
      simp only [mem_compl_iff,mem_preimage,after,mem_prod,mem_Ioi,mem_univ,and_true,not_lt,Set.mem_ofPred_eq]
    have hm:Measurable (fun p:after (Ω:=Ω) v=>
        if p.val.1≤v+h then f (relative v p.val) else (0:C)):=
      (hf.comp (relative_predictable 𝓕 v)).ite hu (measurable_const (a:=(0:C)))
    convert! hm using 1
    funext p
    have hp:v<p.val.1:=p.property.1
    simp only [Set.domRestrict_apply,extend,ite_eq_left hp]
  · convert! (measurable_const (a:=(0:C))) using 1
    funext p
    have hp:¬v<p.val.1:=by simpa only [after,mem_prod,mem_Ioi,mem_univ,and_true,mem_compl_iff] using p.property
    simp only [Set.domRestrict_apply,extend,ite_eq_right hp]

end SHE.DeterministicItoShift
