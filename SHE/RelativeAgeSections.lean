module

public import SHE.BaselineSharpSections
public import SHE.ObservationTimeShift

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1400000
noncomputable section

namespace SHE.BaselineSharpHistory
open Set Filter MeasureTheory ProbabilityTheory Real AddCircle StoppedFourier ProfileL2
  CutoffWordLevel CutoffWordHistories CutoffCarriers PhysicalChainArrays CoveredControlledLaw
  CoveredHistoryGeometry PhysicalParentGeometry HistoryProductMeasure
local instance relativeAgeSections_period : Fact (0<2*π) := ⟨by positivity⟩

/-- Relative-age AE statements pull back to the actual ORIGINAL old
times. The input is translated before restricting the history box;
clipped endpoints are never substituted into an AE time assertion. -/
theorem relative_history_of_time_ae {X : Type} [MeasurableSpace X] {R : ReferenceData} {n : ℕ}
    (L : Level R X n) (ρ : Measure X) [IsFiniteMeasure ρ] (k : ℕ) (v : ℝ) (hv : v≤R.base)
    (Q : ℝ→Prop) (hQ : ∀ᵐ r ∂volume.restrict (Ici (0:ℝ)),Q r) :
    ∀ᵐ p ∂historyMeasure R ρ k,StrictHistory L k p→∀ j:Fin k,Q (lower L k p j-v) := by
  rw [ae_restrict_iff' measurableSet_Ici] at hQ
  have ht:=(measurePreserving_add_right (volume:Measure ℝ) (-v)).quasiMeasurePreserving.ae hQ
  have ht' : ∀ᵐ r ∂volume,0≤r-v→Q (r-v) := by
    simpa only [Function.comp_apply,sub_eq_add_neg,mem_Ici] using ht
  have hh:=history_of_time_ae L ρ k (fun r=>0≤r-v→Q (r-v)) (ae_restrict_of_ae ht')
  filter_upwards [hh] with p hp
  intro hstrict j
  exact hp hstrict j (sub_nonneg.mpr (hv.trans (((carrier L k).terminal_base p).trans (terminal_le_lower L k p j))))

/-- The relative-age property descends to one original old-time
section, justified by literal invariance of the actual time arrays. -/
theorem relative_time_sections_of_ae {R : ReferenceData} {n : ℕ} (L : Level R HeatCircle n)
    (T : ℝ) (hT : ∀ x,L.terminal x=T) (k : ℕ) (v : ℝ) (hv : v≤R.base)
    (Q : ℝ→Prop) (hQ : ∀ᵐ r ∂volume.restrict (Ici (0:ℝ)),Q r) :
    ∀ᵐ t:Fin k→ℝ ∂Measure.pi (fun _=>volume.restrict (Ioc R.base R.horizon)),
      let a:=separated k ((0:HeatCircle),t,fun _=>(0:HeatCircle))
      StrictHistory L k a→∀ j:Fin k,Q (targets L k a (leafIndex k (fun i=>i) j)-v) := by
  have hh:=ae_relative_spatial_sections R k (relative_history_of_time_ae L haarAddCircle k v hv Q hQ)
  filter_upwards [hh] with t ht
  intro a hp
  obtain ⟨x,hx⟩:=ht.exists
  obtain ⟨w,hw⟩:=hx.exists
  let p:=separated k (x,t,fun i=>w i+x)
  have hpp : StrictHistory L k p:=
    (FixedHistoryTimeFactors.strict_sections L T hT k t x 0 (fun i=>w i+x) (fun _=>0)).mpr hp
  intro j
  have hj:=hw hpp j
  have htarget : targets L k a (leafIndex k (fun i=>i) j)=lower L k a j:=by
    rw [targets,leaf_observation L k a j]
  rw [htarget]
  rw [FixedHistoryTimeFactors.lower_sections L T hT k t x 0 (fun i=>w i+x) (fun _=>0)] at hj
  exact hj

end SHE.BaselineSharpHistory
