module

public import SHEStochastic.KolmogorovFieldTightness
public import SHEStochastic.FiniteMarginalTightness
public import Mathlib.Topology.ContinuousMap.SecondCountableSpace

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1100000
noncomputable section

namespace SHEStochastic.FieldLawTightness
open MeasureTheory ProbabilityTheory Set Metric
open scoped NNReal ENNReal
variable {Ω : ℕ → Type*} [∀ m,MeasurableSpace (Ω m)]
    {T V : Type*} [MetricSpace T] [CompactSpace T] [SecondCountableTopology T]
    [NormedAddCommGroup V] [ProperSpace V] [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]

/-- The existing quantitative Chentsov tightness theorem applies to
field laws even when every approximation has its own probability space. -/
theorem tight (μ : ∀ m,Measure (Ω m)) (Y : ∀ m,Ω m → C(T,V)) (hY : ∀ m,Measurable (Y m))
    (t₀ : T) (hzero : ∀ m,∀ᵐ ω ∂μ m,Y m ω t₀=0)
    {c : ℝ≥0∞} {d p q : ℝ} {M α : ℝ≥0}
    (hT : HasCoveringExponent (Set.univ : Set T) c d)
    (hc : c≠⊤) (hd : 0<d) (hp : 0<p) (hdq : d<q) (hα : 0<α) (hαpq : (α : ℝ)<(q-d)/p)
    (hX : ∀ m,IsKolmogorovProcess (fun t ω => Y m ω t) (μ m) p q M) :
    IsTightMeasureSet (Set.range (fun m => (μ m).map (Y m))) := by
  have hz (m : ℕ) : ∀ᵐ f ∂(μ m).map (Y m),f t₀=0 := by
    apply ae_iff.mpr
    change ((μ m).map (Y m)) {f : C(T,V) | f t₀=0}ᶜ=0
    rw [Measure.map_apply (hY m) (measurableSet_eq_fun (ContinuousMap.measurable_eval t₀) measurable_const).compl]
    exact ae_iff.mp (hzero m)
  have hx (m : ℕ) : IsKolmogorovProcess (fun t (f : C(T,V)) => f t) ((μ m).map (Y m)) p q M := by
    refine ⟨?_,?_,(hX m).p_pos,(hX m).q_pos⟩
    · intro s t
      borelize (V×V)
      exact ((continuous_eval_const s).prodMk (continuous_eval_const t)).measurable
    · intro s t
      rw [lintegral_map (((ContinuousMap.measurable_eval s).edist (ContinuousMap.measurable_eval t)).pow_const p) (hY m)]
      exact (hX m).kolmogorovCondition s t
  have ht := KolmogorovFieldTightness.tight (fun m => (μ m).map (Y m))
    (fun _ f => f) (fun _ => measurable_id) t₀ hz hT hc hd hp hdq hα hαpq hx
  have hid (ν : Measure C(T,V)) : ν.map (fun f => f)=ν := by
    change ν.map id=ν
    exact Measure.map_id
  simpa only [hid] using ht

/-- Finite marginal tightness also retains joint field laws on varying
probability spaces. No independence or change of coupling is needed. -/
theorem joint {ι : Type*} [Fintype ι] (μ : ∀ m,Measure (Ω m))
    (Y : ∀ m,Ω m → (ι → C(T,V))) (hY : ∀ m,Measurable (Y m))
    (hTight : ∀ i,IsTightMeasureSet (Set.range (fun m => (μ m).map (fun ω => Y m ω i)))) :
    IsTightMeasureSet (Set.range (fun m => (μ m).map (Y m))) := by
  have ht (i : ι) : IsTightMeasureSet (Set.range (fun m => ((μ m).map (Y m)).map (fun f => f i))) := by
    have he (m : ℕ) : ((μ m).map (Y m)).map (fun f => f i)=(μ m).map (fun ω => Y m ω i) :=
      Measure.map_map (measurable_pi_apply i) (hY m)
    simpa only [he] using hTight i
  have hh := FiniteMarginalTightness.tight_varying (fun m => (μ m).map (Y m))
    (fun _ f => f) (fun _ => measurable_id) ht
  have hid (ν : Measure (ι → C(T,V))) : ν.map (fun f => f)=ν := by
    change ν.map id=ν
    exact Measure.map_id
  simpa only [hid] using hh

end SHEStochastic.FieldLawTightness
