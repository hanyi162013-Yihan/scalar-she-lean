module
public import SHE.PredictableTime
public import Mathlib.MeasureTheory.Measure.OpenPos
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace SHE.CountableStoppedPathAgreement
open MeasureTheory Set PredictableL2
open scoped NNReal
variable {Ω E:Type*}[MeasurableSpace Ω][NormedAddCommGroup E]

/-- Equality at almost every native time determines the whole continuous
path on a nondegenerate compact interval, including both endpoints. -/
theorem continuous_eq(H:ℝ≥0)(hH:0<H)(f g:ℝ≥0→E)
    (hf:Continuous f)(hg:Continuous g)(he:f=ᵐ[timeMeasure H] g):
    ∀t:ℝ≥0,t≤H→f t=g t:=by
  have hr:(fun t:ℝ=>f t.toNNReal)=ᵐ[volume.restrict (Ioc (0:ℝ) (H:ℝ))]
      (fun t:ℝ=>g t.toNNReal):=by
    rw [←timeMeasure_map H]
    apply nonnegative_coe_measurableEmbedding.ae_map_iff.mpr
    filter_upwards [he] with t ht
    simpa only [Real.toNNReal_coe] using ht
  rw [Measure.restrict_congr_set Ioc_ae_eq_Icc] at hr
  have hne:(0:ℝ)≠(H:ℝ):=ne_of_lt (by exact_mod_cast hH)
  have hall:=Measure.eqOn_Icc_of_ae_eq volume hne hr
    (hf.comp continuous_real_toNNReal).continuousOn (hg.comp continuous_real_toNNReal).continuousOn
  intro t ht
  have hh:=hall (show (t:ℝ)∈Icc (0:ℝ) (H:ℝ) from ⟨t.2,by exact_mod_cast ht⟩)
  simpa only [Real.toNNReal_coe] using hh

/-- Countably many zero stopped differences imply genuine path agreement
on the raw nonexit event. Only product-null sets are sectioned; the final
exceptional event is common to every time and every stopping index. -/
theorem off_exit_ae(Q:Measure Ω)[SFinite Q](H:ℝ≥0)(hH:0<H)
    (V W:ℝ≥0→Ω→E)(hcV:∀ω,Continuous (fun t=>V t ω))(hcW:∀ω,Continuous (fun t=>W t ω))
    (A:ℕ→ℝ≥0→Ω→ℝ)(hA:∀N ω,Monotone (fun t=>A N t ω))(Raw:Ω→ℝ)
    (hcover:∀ᵐω∂Q,Raw ω<1→∃N:ℕ,A N H ω<1)
    (hzero:∀N:ℕ,∀ᵐz∂energyMeasure Q H,
      (if A N z.1 z.2<1 then V z.1 z.2-W z.1 z.2 else 0)=0):
    ∀ᵐω∂Q,Raw ω<1→∀t:ℝ≥0,t≤H→V t ω=W t ω:=by
  have hs(N:ℕ):∀ᵐω∂Q,∀ᵐt∂timeMeasure H,
      (if A N t ω<1 then V t ω-W t ω else 0)=0:=by
    have he:=(Measure.measurePreserving_swap (μ:=Q) (ν:=timeMeasure H)).quasiMeasurePreserving.ae (hzero N)
    exact Measure.ae_ae_of_ae_prod he
  have hall:∀ᵐω∂Q,∀N:ℕ,∀ᵐt∂timeMeasure H,
      (if A N t ω<1 then V t ω-W t ω else 0)=0:=ae_all_iff.mpr hs
  filter_upwards [hall,hcover] with ω hω hcov hRaw
  obtain ⟨N,hN⟩:=hcov hRaw
  apply continuous_eq H hH (fun t=>V t ω) (fun t=>W t ω) (hcV ω) (hcW ω)
  filter_upwards [hω N,timeMeasure_ae_mem H] with t ht hmem
  have hAt:A N t ω<1:=(hA N ω hmem.2).trans_lt hN
  simpa only [ite_eq_left hAt,sub_eq_zero] using ht
end SHE.CountableStoppedPathAgreement
