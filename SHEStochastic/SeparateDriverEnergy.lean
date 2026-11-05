module

public import SHEStochastic.SeparateCanonicalCompactness
public import SHEStochastic.CanonicalBrownianSubGaussian
public import SHEStochastic.FixedLawEnergy
public import SHEStochastic.DoobL2Envelope
public import SHEStochastic.NativeClippedBrownian

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
noncomputable section

namespace SHEStochastic.SeparateDriverEnergy
open MeasureTheory ProbabilityTheory Filter SHE
open scoped NNReal ENNReal Topology
variable {Ω : ℕ → Type*} [∀ m,MeasurableSpace (Ω m)]
    {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [Countable ι] [DecidableEq ι]
    (F : ∀ m,Filtration ℝ≥0 (inferInstance : MeasurableSpace (Ω m)))
    (μ : ∀ m,Measure (Ω m)) [∀ m,IsProbabilityMeasure (μ m)] (H : ℝ≥0)
    (P : ∀ m,FiniteScalarIto.Family (F m) (μ m) H ι)
    (U : ∀ m,ℝ≥0 → Ω m → E) (hc : ∀ m ω,Continuous (fun t => U m t ω))
    (hU : ∀ m t,Measurable[F m t] (U m t))

include hU in
/-- Any two observations of a retained original Brownian coordinate
have uniformly integrable squared energy across actual joint laws.
The common full driver law supplies the tails; its state dependence
is unrestricted, and no fourth-moment estimate is needed. -/
theorem uniform_tails (i : ι) (s t : ℝ≥0) :
    Tendsto (fun R : ℕ => ⨆ m,∫⁻ x in {x | (R : ℝ)≤
      (CanonicalStateDriverFiltration.coordinate H i s x)^2+
        (CanonicalStateDriverFiltration.coordinate H i t x)^2},
      ENNReal.ofReal ((CanonicalStateDriverFiltration.coordinate H i s x)^2+
        (CanonicalStateDriverFiltration.coordinate H i t x)^2)
      ∂(SeparateCanonicalCompactness.laws F μ H P U hc m).toMeasure) atTop (𝓝 0) := by
  let D := fun w : ι → StoppedPathPasting.Path H ℝ =>
    (w i (CanonicalStateDriverFiltration.clock H s))^2+(w i (CanonicalStateDriverFiltration.clock H t))^2
  have hmD : Measurable D := by
    exact ((((continuous_eval_const _).comp (continuous_apply i)).pow 2).add
      (((continuous_eval_const _).comp (continuous_apply i)).pow 2)).measurable
  have hsg (q : ℝ≥0) := CanonicalBrownianSubGaussian.coordinate (F 0) (μ 0) H (P 0) (U 0) (hc 0) (hU 0) i q
  have hM (q : ℝ≥0) : MemLp (CanonicalStateDriverFiltration.coordinate (E := E) H i q) 2
      (SeparateCanonicalCompactness.laws F μ H P U hc 0).toMeasure := by
    change MemLp (CanonicalStateDriverFiltration.coordinate (E := E) H i q) 2
      ((μ 0).map (CanonicalNativeBrownian.bundle (F 0) (μ 0) H (P 0) (U 0) (hc 0)))
    simpa using (hsg q).memLp (2 : ℝ≥0)
  exact FixedLawEnergy.of_common_map
    (fun m => (SeparateCanonicalCompactness.laws F μ H P U hc m).toMeasure)
    (fun _ => Prod.snd) (fun _ => measurable_snd)
    (SeparateCanonicalCompactness.driver_law F μ H P U hc hU) D hmD
    ((hM s).integrable_sq.add (hM t).integrable_sq)

include hU in
/-- The existing continuous Doob L2 envelope supplies full scalar
driver-path energy UI. One fixed driver law controls every observation
time, while all state/driver dependence is retained. -/
theorem path_uniform_tails {C : Type*} [NormedAddCommGroup C] [InnerProductSpace ℝ C]
    [CompleteSpace C] [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
    (e : HilbertBasis ι ℝ C) (i : ι) :
    Tendsto (fun R : ℕ => ⨆ m,∫⁻ x in {x | (R : ℝ)≤‖x.2 i‖^2},
      ENNReal.ofReal (‖x.2 i‖^2) ∂(SeparateCanonicalCompactness.laws F μ H P U hc m).toMeasure)
      atTop (𝓝 0) := by
  let B := CanonicalNativeBrownian.bundle (F 0) (μ 0) H (P 0) (U 0) (hc 0)
  have hmB := CanonicalNativeBrownian.measurable_bundle (F 0) (μ 0) H (P 0) (U 0) (hc 0) (hU 0)
  have hclip (ω : Ω 0) : Continuous (fun t => NativeClippedBrownian.value (P 0) H i t ω) :=
    (((P 0).continuous i ω).comp (continuous_id.min continuous_const)).sub continuous_const
  have hT : MemLp (NativeClippedBrownian.value (P 0) H i H) 2 (μ 0) := by
    simpa using (NativeClippedBrownian.subgaussian (P 0) H le_rfl i H).memLp (2 : ℝ≥0)
  obtain ⟨D,hD,hD0,hDb,_⟩ := DoobL2Envelope.exists_envelope
    (NativeClippedBrownian.martingale (P 0) e H le_rfl i) hclip H hT
  have hb (ω : Ω 0) : ‖(B ω).2 i‖≤D ω := by
    apply (ContinuousMap.norm_le _ (hD0 ω)).mpr
    intro t
    have ht : t.val.toNNReal≤H := by
      simpa only [Real.toNNReal_coe] using Real.toNNReal_le_toNNReal t.property.2
    have heq : (B ω).2 i t=NativeClippedBrownian.value (P 0) H i t.val.toNNReal ω := by
      change (P 0).W i (0+t.val.toNNReal) ω-(P 0).W i 0 ω=
        (P 0).W i (min t.val.toNNReal H) ω-(P 0).W i 0 ω
      rw [zero_add,min_eq_left ht]
    rw [heq]
    exact hDb t.val.toNNReal ht ω
  let energy := fun w : ι → StoppedPathPasting.Path H ℝ => ‖w i‖^2
  have he : Measurable energy := ((continuous_apply i).norm.pow 2).measurable
  have hi : Integrable (fun ω => energy (B ω).2) (μ 0) := hD.integrable_sq.mono'
    ((he.comp measurable_snd).comp hmB).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun ω => by
      change ‖‖(B ω).2 i‖^2‖≤D ω^2
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hb ω) 2))
  apply FixedLawEnergy.of_common_map
    (fun m => (SeparateCanonicalCompactness.laws F μ H P U hc m).toMeasure)
    (fun _ => Prod.snd) (fun _ => measurable_snd)
    (SeparateCanonicalCompactness.driver_law F μ H P U hc hU) energy he
  exact (integrable_map_measure (he.comp measurable_snd).aestronglyMeasurable hmB.aemeasurable).mpr hi

end SHEStochastic.SeparateDriverEnergy
