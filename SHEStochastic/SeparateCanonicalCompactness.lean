module

public import SHEStochastic.CanonicalApproximationCompactness
public import SHEStochastic.CoupledLawTightness
public import SHEStochastic.WeakLimitProbabilityTools

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1200000
noncomputable section

namespace SHEStochastic.SeparateCanonicalCompactness
open MeasureTheory ProbabilityTheory Filter SHE
open CanonicalStateDriverFiltration
open scoped NNReal Topology
variable {Ω : ℕ → Type*} [∀ m,MeasurableSpace (Ω m)]
    {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [Countable ι] [DecidableEq ι]
    (F : ∀ m,Filtration ℝ≥0 (inferInstance : MeasurableSpace (Ω m)))
    (μ : ∀ m,Measure (Ω m)) [∀ m,IsProbabilityMeasure (μ m)] (H : ℝ≥0)
    (P : ∀ m,FiniteScalarIto.Family (F m) (μ m) H ι)
    (U : ∀ m,ℝ≥0 → Ω m → E) (hc : ∀ m ω,Continuous (fun t => U m t ω))
    (hU : ∀ m t,Measurable[F m t] (U m t))

/-- Actual joint path laws, even when every approximation lives on a
separately completed probability space. -/
def laws (m : ℕ) : ProbabilityMeasure (CanonicalContinuousStateDriver.Space (E := E) (ι := ι) H) :=
  (μ m).toProbabilityMeasure.map (CanonicalNativeBrownian.bundle (F m) (μ m) H (P m) (U m) (hc m))

include hU in
/-- All actual joint laws have the same full original-driver marginal,
even though their state/noise dependence and source spaces may differ. -/
theorem driver_law (m : ℕ) :
    (laws F μ H P U hc m).toMeasure.map Prod.snd=(laws F μ H P U hc 0).toMeasure.map Prod.snd := by
  change ((μ m).map (CanonicalNativeBrownian.bundle (F m) (μ m) H (P m) (U m) (hc m))).map Prod.snd=
    ((μ 0).map (CanonicalNativeBrownian.bundle (F 0) (μ 0) H (P 0) (U 0) (hc 0))).map Prod.snd
  rw [Measure.map_map measurable_snd
      (CanonicalNativeBrownian.measurable_bundle (F m) (μ m) H (P m) (U m) (hc m) (hU m)),
    Measure.map_map measurable_snd
      (CanonicalNativeBrownian.measurable_bundle (F 0) (μ 0) H (P 0) (U 0) (hc 0) (hU 0))]
  exact NativeBrownianPathLaw.map_eq (P m) (P 0)

include hU in
/-- Tight actual state paths give tight actual joint state/driver laws,
even on separately completed probability spaces. -/
theorem tight
    (htight : IsTightMeasureSet (Set.range (fun m =>
      (μ m).map (NativeContinuousPath.path H (U m) (hc m))))) :
    IsTightMeasureSet (Set.range (fun m => (laws F μ H P U hc m).toMeasure)) := by
  let A := fun m => CanonicalNativeBrownian.bundle (F m) (μ m) H (P m) (U m) (hc m)
  have hm (m : ℕ) : Measurable (A m) :=
    CanonicalNativeBrownian.measurable_bundle (F m) (μ m) H (P m) (U m) (hc m) (hU m)
  have hs (m : ℕ) : (fun ω => (A m ω).1)=NativeContinuousPath.path H (U m) (hc m) := by
    funext ω
    apply ContinuousMap.ext
    intro t
    change U m (0+t.val.toNNReal) ω=U m t.val.toNNReal ω
    rw [zero_add]
  let driver := BrownianFuturePath.value (P 0).W (P 0).continuous 0 H
  have hd (m : ℕ) : (μ m).map (fun ω => (A m ω).2)=(μ 0).map driver :=
    NativeBrownianPathLaw.map_eq (P m) (P 0)
  have hts : IsTightMeasureSet (Set.range (fun m => (μ m).map (fun ω => (A m ω).1))) := by
    simpa only [hs] using htight
  have htd : IsTightMeasureSet (Set.range (fun m => (μ m).map (fun ω => (A m ω).2))) := by
    simp only [hd,Set.range_const]
    exact isTightMeasureSet_singleton
  have ht := CoupledLawTightness.paired μ (fun m ω => (A m ω).1) (fun m ω => (A m ω).2)
    (fun m => measurable_fst.comp (hm m)) (fun m => measurable_snd.comp (hm m)) hts htd
  have he (m : ℕ) : (laws F μ H P U hc m).toMeasure=(μ m).map (A m) := rfl
  have ht' : IsTightMeasureSet (Set.range (fun m => (laws F μ H P U hc m).toMeasure)) := by
    simpa only [he] using ht
  exact ht'

include hU in
/-- Tight state paths retain their actual Brownian drivers in a joint
weak limit. The limiting driver is Brownian in the full state-and-driver
filtration. No common underlying probability space is required. -/
theorem exists_limit
    (htight : IsTightMeasureSet (Set.range (fun m =>
      (μ m).map (NativeContinuousPath.path H (U m) (hc m))))) :
    ∃ Q : ProbabilityMeasure (CanonicalContinuousStateDriver.Space (E := E) (ι := ι) H),
      ∃ φ : ℕ → ℕ,StrictMono φ ∧ Tendsto (laws F μ H P U hc ∘ φ) atTop (𝓝 Q) ∧
        ∀ n (a : Fin n → ι),FiniteBrownianLawOn (filtration (E := E) (ι := ι) H)
          Q.toMeasure H (fun i => coordinate H (a i)) (fun i j => if a i=a j then 1 else 0) := by
  have ht' := tight F μ H P U hc hU htight
  obtain ⟨Q,φ,hφ,hlim⟩ := TightLawSubsequence.exists_limit (laws F μ H P U hc) ht'
  refine ⟨Q,φ,hφ,hlim,?_⟩
  exact (WeakLimitCanonicalBrownian.family H (laws F μ H P U hc ∘ φ) Q hlim
    (fun k n a => CanonicalNativeBrownian.law (F (φ k)) (μ (φ k)) H (P (φ k))
      (U (φ k)) (hc (φ k)) (hU (φ k)) n a)).law

include hU in
/-- The joint compactness construction preserves a common arbitrary
initial law, allowing different completed spaces for each approximation. -/
theorem initial_law (ρ : Measure E) [IsProbabilityMeasure ρ]
    (hInitial : ∀ m,(μ m).map (U m 0)=ρ)
    (Q : ProbabilityMeasure (CanonicalContinuousStateDriver.Space (E := E) (ι := ι) H))
    (φ : ℕ → ℕ) (hlim : Tendsto (laws F μ H P U hc ∘ φ) atTop (𝓝 Q)) :
    Q.toMeasure.map (fun x => x.1 (StoppedPathPasting.origin H))=ρ := by
  let f := fun x : CanonicalContinuousStateDriver.Space (E := E) (ι := ι) H =>
    x.1 (StoppedPathPasting.origin H)
  have hf : Continuous f := (continuous_eval_const _).comp continuous_fst
  apply (WeakLimitProbabilityTools.hasLaw (laws F μ H P U hc ∘ φ) Q hlim f hf ρ ?_).map_eq
  intro k
  have hm := CanonicalNativeBrownian.measurable_bundle (F (φ k)) (μ (φ k)) H (P (φ k))
    (U (φ k)) (hc (φ k)) (hU (φ k))
  refine ⟨hf.measurable.aemeasurable,?_⟩
  change ((μ (φ k)).map (CanonicalNativeBrownian.bundle (F (φ k)) (μ (φ k)) H
    (P (φ k)) (U (φ k)) (hc (φ k)))).map f=ρ
  rw [Measure.map_map hf.measurable hm]
  have he : f ∘ CanonicalNativeBrownian.bundle (F (φ k)) (μ (φ k)) H
      (P (φ k)) (U (φ k)) (hc (φ k))=U (φ k) 0 := by
    funext ω
    change U (φ k) (0+(StoppedPathPasting.origin H).val.toNNReal) ω=U (φ k) 0 ω
    simp only [StoppedPathPasting.origin,Real.toNNReal_zero,zero_add]
  rw [he]
  exact hInitial (φ k)

end SHEStochastic.SeparateCanonicalCompactness
