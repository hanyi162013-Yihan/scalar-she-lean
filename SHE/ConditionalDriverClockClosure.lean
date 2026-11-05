module
public import SHE.RationalIntervalSequence
public import SHE.CanonicalPastPathContinuity
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2600000
namespace SHE.ConditionalDriverClockClosure
open MeasureTheory ProbabilityTheory Set Filter CanonicalPastPathContinuity
open scoped Topology NNReal
variable{E ι:Type*}[Countable ι][DecidableEq ι]
variable[NormedAddCommGroup E][InnerProductSpace ℝ E][CompleteSpace E]
variable[MeasurableSpace E][BorelSpace E][SecondCountableTopology E]
variable(h:ℝ≥0) (m:Measure (CanonicalFutureStateDriver.Space (E:=E) (ι:=ι) h))
variable[IsProbabilityMeasure m]
local notation "R"=>CanonicalFutureStateDriver.Space (E:=E) (ι:=ι) h
local notation "T"=>Icc (0:ℝ) (h:ℝ)

/-- Rational conditional Brownian independence extends to ALL real
clocks using actual continuous STATE and DRIVER paths and countably
packed finite projections. No uncountable AE intersection is used. -/
theorem independent
    (hi:∀n (a:Fin n→ι) (s t:CanonicalConditionalRationalDriver.Times h),s≤t→
      IndepFun (CanonicalFutureStateDriver.past (E:=E) (ι:=ι)
        (CanonicalConditionalRationalDriver.time s))
        (CanonicalFutureStateDriver.increment (E:=E) a
          (CanonicalConditionalRationalDriver.time s) (CanonicalConditionalRationalDriver.time t)) m)
    {n:ℕ}(a:Fin n→ι) (s t:T) (hst:s≤t):
    IndepFun (CanonicalFutureStateDriver.past (E:=E) (ι:=ι) s)
      (CanonicalFutureStateDriver.increment (E:=E) a s t) m:=by
  classical
  by_cases he:s=t
  · subst t
    have hz:CanonicalFutureStateDriver.increment (E:=E) a s s=(fun _:R=>0):=by
      funext r;apply PiLp.ext;intro i;simp[CanonicalFutureStateDriver.increment]
    rw[hz]
    exact indepFun_const_right _ _
  have hst':s<t:=lt_of_le_of_ne hst he
  obtain ⟨q,hq⟩:=RationalIntervalSequence.exists_sequence h s
  obtain ⟨r,hr⟩:=RationalIntervalSequence.exists_sequence h t
  obtain ⟨N,hN⟩:=eventually_atTop.mp (hq.eventually_lt hr hst')
  let Q:ℕ→T:=fun j=>CanonicalConditionalRationalDriver.time (q (j+N))
  let S:ℕ→T:=fun j=>CanonicalConditionalRationalDriver.time (r (j+N))
  have hQ:Tendsto Q atTop (𝓝 s):=hq.comp (tendsto_add_atTop_nat N)
  have hS:Tendsto S atTop (𝓝 t):=hr.comp (tendsto_add_atTop_nat N)
  have hI(j:ℕ):IndepFun (CanonicalFutureStateDriver.past (E:=E) (ι:=ι) (Q j))
      (CanonicalFutureStateDriver.increment (E:=E) a (Q j) (S j)) m:=by
    apply hi n a (q (j+N)) (r (j+N))
    have hh:Q j≤S j:=(hN (j+N) (Nat.le_add_left N j)).le
    change (q (j+N)).val≤(r (j+N)).val
    have hh':(Q j).val≤(S j).val:=hh
    dsimp only[Q,S,CanonicalConditionalRationalDriver.time] at hh'
    exact_mod_cast hh'
  have hfull:IndepFun (CanonicalFutureStateDriver.increment (E:=E) a s t)
      (fun z:R=>fun k=>pack h (CanonicalFutureStateDriver.past s z) k) m:=by
    apply FiniteCylinderIndependence.full m _ _
      (CanonicalFutureStateDriver.measurable_increment a s t) (fun k=>
        (pack_measurable h k).comp (CanonicalFutureStateDriver.measurable_past s))
    intro K
    let X:ℕ→R→(K→C(Icc (0:ℝ) (h:ℝ),E)×C(Icc (0:ℝ) (h:ℝ),ℝ)):=
      fun j z k=>pack h (CanonicalFutureStateDriver.past (Q j) z) k.val
    let Y:ℕ→R→WordRecursion.State n:=fun j=>CanonicalFutureStateDriver.increment a (Q j) (S j)
    have hl:=IndependenceContinuousLimit.independent m X Y
      (fun z (k:K)=>pack h (CanonicalFutureStateDriver.past s z) k.val)
      (CanonicalFutureStateDriver.increment a s t)
      (fun j=>(measurable_pi_iff.mpr (fun (k:K)=>
        (pack_measurable h k.val).comp (CanonicalFutureStateDriver.measurable_past (Q j)))).aemeasurable)
      (fun j=>(CanonicalFutureStateDriver.measurable_increment a (Q j) (S j)).aemeasurable)
      (measurable_pi_iff.mpr (fun (k:K)=>(pack_measurable h k.val).comp
        (CanonicalFutureStateDriver.measurable_past s))).aemeasurable
      (CanonicalFutureStateDriver.measurable_increment a s t).aemeasurable
      (ae_of_all _ (fun z=>tendsto_pi_nhds.mpr (fun (k:K)=>
        (past_continuous h z k.val).tendsto s |>.comp hQ)))
      (ae_of_all _ (fun z=>(increment_continuous h z a).tendsto (s,t) |>.comp (hQ.prodMk_nhds hS)))
      (fun j=>by
        simpa only[Function.comp_def,X,Y,id_eq] using
          (hI j).comp (measurable_pi_iff.mpr (fun (k:K)=>pack_measurable h k.val)) measurable_id)
    exact hl.symm
  have hp:MeasurableSpace.comap (CanonicalFutureStateDriver.past (E:=E) (ι:=ι) s)
      inferInstance≤MeasurableSpace.comap
        (fun z:R=>fun k=>pack h (CanonicalFutureStateDriver.past s z) k) inferInstance:=by
    rw[←generates (E:=E) (ι:=ι) h]
    rw[MeasurableSpace.comap_comp]
    exact le_rfl
  exact (indep_of_indep_of_le_right hfull hp).symm
end SHE.ConditionalDriverClockClosure
