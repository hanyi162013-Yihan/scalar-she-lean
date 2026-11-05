module
public import SHE.CanonicalFutureStateDriver
public import SHE.IndependenceContinuousLimit
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1800000
namespace SHE.CanonicalPastPathContinuity
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal
variable{E ι:Type*}[Countable ι]
variable[NormedAddCommGroup E][InnerProductSpace ℝ E][CompleteSpace E]
variable[MeasurableSpace E][BorelSpace E][SecondCountableTopology E]
variable(h:ℝ≥0)

abbrev Space:=CanonicalFutureStateDriver.Space (E:=E) (ι:=ι) h

def pack(r:Space (E:=E) (ι:=ι) h) (k:Option ι):C(Icc (0:ℝ) (h:ℝ),E)×C(Icc (0:ℝ) (h:ℝ),ℝ):=
  match k with
  | none=>(r.1,0)
  | some i=>(0,r.2 i)

theorem pack_measurable(k:Option ι):Measurable (fun r:Space (E:=E) (ι:=ι) h=>pack h r k):=by
  cases k with
  | none =>exact measurable_fst.prodMk measurable_const
  | some i =>exact measurable_const.prodMk ((measurable_pi_apply i).comp measurable_snd)

/-- Finite projections of the entire stopped STATE+DRIVER past vary
continuously with the actual clock in the uniform path topology. -/
theorem past_continuous(r:Space (E:=E) (ι:=ι) h) (k:Option ι):
    Continuous (fun u:Icc (0:ℝ) (h:ℝ)=>pack h (CanonicalFutureStateDriver.past u r) k):=by
  have hc(f:C(Icc (0:ℝ) (h:ℝ),E)):
      Continuous (fun u:Icc (0:ℝ) (h:ℝ)=>
        (CanonicalFutureStateDriver.past (ι:=ι) u (f,fun _=>0)).1):=by
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact f.continuous.comp
      ((continuous_snd.subtype_val.min continuous_fst.subtype_val).subtype_mk _)
  have hd(f:C(Icc (0:ℝ) (h:ℝ),ℝ)):
      Continuous (fun u:Icc (0:ℝ) (h:ℝ)=>
        (⟨fun t=>f (CanonicalFutureStateDriver.stopTime u t),f.continuous.comp
          ((continuous_subtype_val.min continuous_const).subtype_mk _)⟩:
            C(Icc (0:ℝ) (h:ℝ),ℝ))):=by
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact f.continuous.comp
      ((continuous_snd.subtype_val.min continuous_fst.subtype_val).subtype_mk _)
  cases k with
  | none =>exact (hc r.1).prodMk continuous_const
  | some i =>exact continuous_const.prodMk (hd (r.2 i))

theorem increment_continuous(r:Space (E:=E) (ι:=ι) h){n:ℕ}(a:Fin n→ι):
    Continuous (fun p:Icc (0:ℝ) (h:ℝ)×Icc (0:ℝ) (h:ℝ)=>
      CanonicalFutureStateDriver.increment (E:=E) a p.1 p.2 r):=by
  apply (PiLp.continuous_toLp 2 (fun _:Fin n=>ℝ)).comp
  apply continuous_pi
  intro i
  exact ((r.2 (a i)).continuous.comp continuous_snd).sub
    ((r.2 (a i)).continuous.comp continuous_fst)

/-- The packed countable path coordinates generate the entire canonical
state-and-driver path sigma algebra. -/
theorem generates:
    MeasurableSpace.comap (fun r:Space (E:=E) (ι:=ι) h=>fun k=>pack h r k)
      inferInstance=(inferInstance:MeasurableSpace (Space (E:=E) (ι:=ι) h)):=by
  apply le_antisymm
  · exact (measurable_pi_iff.mpr (pack_measurable h)).comap_le
  · let V:=fun r:Space (E:=E) (ι:=ι) h=>fun k=>pack h r k
    let mR:MeasurableSpace (Space (E:=E) (ι:=ι) h):=inferInstance
    letI:MeasurableSpace (Space (E:=E) (ι:=ι) h):=MeasurableSpace.comap V inferInstance
    have hv:Measurable V:=Measurable.of_comap_le le_rfl
    have hs:Measurable (fun r:Space (E:=E) (ι:=ι) h=>r.1):=
      (show Measurable (fun z:C(Icc (0:ℝ) (h:ℝ),E)×C(Icc (0:ℝ) (h:ℝ),ℝ)=>z.1) from measurable_fst).comp
        ((measurable_pi_apply none).comp hv)
    have hd:Measurable (fun r:Space (E:=E) (ι:=ι) h=>r.2):=by
      apply measurable_pi_iff.mpr
      intro i
      exact (show Measurable (fun z:C(Icc (0:ℝ) (h:ℝ),E)×C(Icc (0:ℝ) (h:ℝ),ℝ)=>z.2) from measurable_snd).comp
        ((measurable_pi_apply (some i)).comp hv)
    have hh:@Measurable (Space (E:=E) (ι:=ι) h) (Space (E:=E) (ι:=ι) h)
        (MeasurableSpace.comap V inferInstance) mR id:=hs.prodMk hd

    simpa only[MeasurableSpace.comap_id] using hh.comap_le
end SHE.CanonicalPastPathContinuity
