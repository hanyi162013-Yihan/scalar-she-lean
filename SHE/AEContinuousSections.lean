module

public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000

namespace SHE.AEContinuousSections
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology

/-- An AE Caratheodory theorem. Time continuity and genuinely AE
measurable fixed-time sections give product AE measurability, without
selecting an exceptional set simultaneously at uncountably many times. -/
theorem aemeasurable {X T E : Type*} [MeasurableSpace X]
    [TopologicalSpace T] [MetrizableSpace T] [MeasurableSpace T]
    [SecondCountableTopology T] [OpensMeasurableSpace T]
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (ν : Measure T) (μ : Measure X) (u : T→X→E)
    (hcont : ∀x,Continuous (fun t=>u t x))
    (hsection : ∀t,AEMeasurable (u t) μ) :
    AEMeasurable (Function.uncurry u) (ν.prod μ) := by
  classical
  have hid : StronglyMeasurable (id : T→T):=stronglyMeasurable_id
  let s:ℕ→SimpleFunc T T:=hid.approx
  let U:ℕ→T×X→E:=fun n p=>u (s n p.1) p.2
  have hm(n:ℕ):AEMeasurable (U n) (ν.prod μ):=by
    have hi(t:T):AEMeasurable (fun p:T×X=>u t p.2) (ν.prod μ):=
      (hsection t).comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
    have he(t:T):MeasurableSet {p:T×X|s n p.1=t}:=
      measurableSet_eq_fun ((s n).measurable.comp measurable_fst) measurable_const
    have hs:AEMeasurable (fun p:T×X=>∑t∈(s n).range,
        ({p:T×X|s n p.1=t}).indicator (fun p=>u t p.2) p) (ν.prod μ):=
      by
        convert Finset.aemeasurable_sum (s n).range (fun t _=>(hi t).indicator (he t)) using 1
        funext p
        simp only [Finset.sum_apply]
    convert hs using 1
    funext p
    dsimp only [U]
    symm
    rw [Finset.sum_eq_single (s n p.1)]
    · exact Set.indicator_of_mem (show p∈{r:T×X|s n r.1=s n p.1} from rfl) _
    · intro t ht hne
      apply Set.indicator_of_notMem
      exact fun h=>hne h.symm
    · intro hnot
      exact (hnot (SimpleFunc.mem_range_self (s n) p.1)).elim
  apply aemeasurable_of_tendsto_metrizable_ae' hm
  apply ae_of_all
  intro p
  exact ((hcont p.2).tendsto p.1).comp (hid.tendsto_approx p.1)

end SHE.AEContinuousSections
