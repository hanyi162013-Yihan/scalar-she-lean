module

public import SHEStochastic.CanonicalNativeBrownian
public import SHEStochastic.TightnessFromCompactControl
public import SHEStochastic.TightLawSubsequence
public import SHEStochastic.NativeBrownianPathLaw

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 900000
noncomputable section

namespace SHEStochastic.CanonicalApproximationCompactness
open MeasureTheory ProbabilityTheory Filter SHE
open SHE.CanonicalStateDriverFiltration
open scoped NNReal Topology

variable {Ω E ι : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [Countable ι] [DecidableEq ι]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  (P : FiniteScalarIto.Family F μ H ι)
  (U : ℕ → ℝ≥0 → Ω → E) (hc : ∀ k sample, Continuous (fun t ↦ U k t sample))
  (hU : ∀ k t, Measurable[F t] (U k t))

def laws (k : ℕ) : ProbabilityMeasure (CanonicalContinuousStateDriver.Space (E := E) (ι := ι) H) :=
  μ.toProbabilityMeasure.map (CanonicalNativeBrownian.bundle F μ H P (U k) (hc k))

def varyingLaws (Ps : ℕ → FiniteScalarIto.Family F μ H ι) (k : ℕ) :
    ProbabilityMeasure (CanonicalContinuousStateDriver.Space (E := E) (ι := ι) H) :=
  laws F μ H (Ps k) U hc k

include hU in
/-- Uniform tightness of the state paths gives an actual weak joint
state/driver subsequential limit. The driver law is fixed; dependence
between state and driver is retained. The limit is Brownian in its FULL
canonical filtration, so it supports the native stochastic construction. -/
theorem exists_limit_varying (Ps : ℕ → FiniteScalarIto.Family F μ H ι)
    (htight : IsTightMeasureSet (Set.range (fun k ↦ μ.map (NativeContinuousPath.path H (U k) (hc k))))) :
    ∃ Q : ProbabilityMeasure (CanonicalContinuousStateDriver.Space (E := E) (ι := ι) H),
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto ((varyingLaws F μ H U hc Ps) ∘ φ) atTop (𝓝 Q) ∧
        ∀ n (a : Fin n → ι), FiniteBrownianLawOn (filtration (E := E) (ι := ι) H)
          (Q : Measure _) H (fun i ↦ coordinate H (a i))
          (fun i j ↦ if a i = a j then 1 else 0) := by
  let A (k : ℕ) := CanonicalNativeBrownian.bundle F μ H (Ps k) (U k) (hc k)
  have hm (k : ℕ) : Measurable (A k) :=
    CanonicalNativeBrownian.measurable_bundle F μ H (Ps k) (U k) (hc k) (hU k)
  have hstate (k : ℕ) : (fun sample ↦ (A k sample).1) = NativeContinuousPath.path H (U k) (hc k) := by
    funext sample
    apply ContinuousMap.ext
    intro t
    change U k (0 + t.val.toNNReal) sample = U k t.val.toNNReal sample
    rw [zero_add]
  let driver := BrownianFuturePath.value (Ps 0).W (Ps 0).continuous 0 H
  have hdriver (k : ℕ) : μ.map (fun sample ↦ (A k sample).2) = μ.map driver :=
    NativeBrownianPathLaw.map_eq (Ps k) (Ps 0)
  have htf : IsTightMeasureSet (Set.range (fun k ↦ μ.map (fun sample ↦ (A k sample).1))) := by
    simpa only [hstate] using htight
  have htg : IsTightMeasureSet (Set.range (fun k ↦ μ.map (fun sample ↦ (A k sample).2))) := by
    simp only [hdriver, Set.range_const]
    exact isTightMeasureSet_singleton
  have ht := TightnessFromCompactControl.paired μ (fun k sample ↦ (A k sample).1)
    (fun k sample ↦ (A k sample).2) (fun k ↦ measurable_fst.comp (hm k))
    (fun k ↦ measurable_snd.comp (hm k)) htf htg
  have he (k : ℕ) : (varyingLaws F μ H U hc Ps k).toMeasure = μ.map (A k) := rfl
  have ht' : IsTightMeasureSet (Set.range (fun k ↦ (varyingLaws F μ H U hc Ps k).toMeasure)) := by
    simpa only [he] using ht
  obtain ⟨Q, φ, hφ, hlim⟩ := TightLawSubsequence.exists_limit (varyingLaws F μ H U hc Ps) ht'
  refine ⟨Q, φ, hφ, hlim, ?_⟩
  let B := WeakLimitCanonicalBrownian.family H ((varyingLaws F μ H U hc Ps) ∘ φ) Q hlim
    (fun k n a ↦ CanonicalNativeBrownian.law F μ H (Ps (φ k)) (U (φ k)) (hc (φ k)) (hU (φ k)) n a)
  exact B.law

include hU in
/-- The original common-driver interface follows from the varying-driver
compactness theorem without changing any canonical path laws. -/
theorem exists_limit
    (htight : IsTightMeasureSet (Set.range (fun k ↦ μ.map (NativeContinuousPath.path H (U k) (hc k))))) :
    ∃ Q : ProbabilityMeasure (CanonicalContinuousStateDriver.Space (E := E) (ι := ι) H),
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto ((laws F μ H P U hc) ∘ φ) atTop (𝓝 Q) ∧
        ∀ n (a : Fin n → ι), FiniteBrownianLawOn (filtration (E := E) (ι := ι) H)
          (Q : Measure _) H (fun i ↦ coordinate H (a i))
          (fun i j ↦ if a i = a j then 1 else 0) :=
  exists_limit_varying F μ H U hc hU (fun _ ↦ P) htight

end SHEStochastic.CanonicalApproximationCompactness
