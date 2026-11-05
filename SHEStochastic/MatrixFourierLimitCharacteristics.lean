module

public import SHEStochastic.MatrixFourierSquareTests
public import SHEStochastic.MatrixFourierMixedTests
public import SHEStochastic.CanonicalBrownianSubGaussian
public import SHEStochastic.CanonicalApproximationCompactness
public import SHEStochastic.CanonicalLinearWeakLimit
public import SHEStochastic.MatrixCanonicalFourierRecognition

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section

namespace SHEStochastic.MatrixFourierLimitCharacteristics
open MeasureTheory ProbabilityTheory Filter SHE SHE.PredictableL2 MatrixInfiniteHaar MatrixFourierCoordinates
open scoped NNReal ENNReal Topology Matrix.Norms.L2Operator
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
variable {d Ω : Type*} [Fintype d] [DecidableEq d] [mΩ : MeasurableSpace Ω]
local instance : SecondCountableTopology (Physical (d := d)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (Physical (d := d)) := borel _
local instance : BorelSpace (Physical (d := d)) := ⟨rfl⟩
variable (F : Filtration ℝ≥0 mΩ) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
    (Gn : ℕ → MatrixNonlinearCoefficient.Coefficient d) {Cn : ℕ → ℝ≥0} {β : ℝ≥0}
    (hGn : ∀ m,HolderWith (Cn m) β (Gn m).value) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (N : ℕ → FiniteScalarIto.Family F μ H (d×FiniteHaar.HaarNode))
    (U : ℕ → ℝ≥0×Ω → Physical (d := d)) (hU : ∀ m,StronglyMeasurable[F.predictable] (U m))
    (hcU : ∀ m ω,Continuous (fun t => U m (t,ω))) (ξ : Ω → Physical (d := d))
    (hEquation : ∀ m,MatrixFourierMildRealization.RandomEquation F μ H (Gn m) (hGn m) hβ hβ1 (U m) (hU m) (N m) ξ)
    (G : MatrixNonlinearCoefficient.Coefficient d) {C : ℝ≥0} (hG : HolderWith C β G.value)
    (B : ℝ≥0) (hBound : ∀ m,(Gn m).bound ≤ B)
    (error : ℕ → ℝ) (he : ∀ m,0 ≤ error m) (helim : Tendsto error atTop (𝓝 0))
    (happrox : ∀ m z,‖G.value z-(Gn m).value z‖ ≤ error m)
    (Q : ProbabilityMeasure (CanonicalContinuousStateDriver.Space (E := Physical (d := d)) (ι := d×FiniteHaar.HaarNode) H))
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hlim : Tendsto ((CanonicalApproximationCompactness.varyingLaws F μ H
      (fun m t ω => U m (t,ω)) hcU N) ∘ φ) atTop (𝓝 Q))
    (i : d) (a : ℂ →L[ℝ] ℝ) (n : ℤ)
local notation "X" => CanonicalContinuousStateDriver.Space (E := Physical (d := d)) (ι := d×FiniteHaar.HaarNode) H
local notation "laws" => (CanonicalApproximationCompactness.varyingLaws F μ H (fun m t ω => U m (t,ω)) hcU N) ∘ φ
local notation "M" => CanonicalLinearFluctuation.value (ι := d×FiniteHaar.HaarNode) H (coordinate i a n) ((n : ℝ)^2)
local notation "c" => (fun t : ℝ≥0 => min t H*MatrixFourierInput.commonCap H a n B^2)

include hEquation hBound in
theorem source_subgaussian (k : ℕ) (t : ℝ≥0) : HasSubgaussianMGF (M t) (c t) (laws k : Measure X) := by
  change HasSubgaussianMGF _ _ (μ.map _)
  exact MatrixFourierPathMoments.random_subgaussian F μ H (Gn (φ k)) (hGn (φ k)) hβ hβ1
    (U (φ k)) (hU (φ k)) (N (φ k)) ξ (hEquation (φ k)) (hcU (φ k)) B (hBound (φ k)) i a n t

include hEquation hBound hlim in
/-- The same actual weak limit retains every linear Fourier martingale and moment bound. -/
theorem linear (hnull : NullCompleteFiltration.ContainsNullSets F μ) :
    Martingale M (CanonicalStateDriverFiltration.filtration H) (Q : Measure X) ∧
      ∀ t,HasSubgaussianMGF (M t) (c t) (Q : Measure X) := by
  apply CanonicalLinearWeakLimit.martingale H (coordinate i a n) ((n : ℝ)^2) laws Q hlim c
    (source_subgaussian F μ H Gn hGn hβ hβ1 N U hU hcU ξ hEquation B hBound φ i a n)
  intro k s t hst ψ
  change (∫ x,ψ (CanonicalStateDriverFiltration.history H s x)*(M t x-M s x) ∂μ.map _)=0
  exact MatrixFourierPathMoments.random_identity F μ H (Gn (φ k)) (hGn (φ k)) hβ hβ1
    (U (φ k)) (hU (φ k)) (N (φ k)) ξ (hEquation (φ k)) (hcU (φ k)) hnull i a n s t hst ψ

include hEquation hBound he helim happrox hφ hlim in
/-- The actual weak vector limit has the correct quadratic Fourier
compensator, obtained from the original approximations and fourth moments. -/
theorem square (hnull : NullCompleteFiltration.ContainsNullSets F μ) :
    Martingale (fun t x => M t x^2-MatrixFourierSquareTests.compensator H G hG hβ hβ1 i a n t x)
      (CanonicalStateDriverFiltration.filtration H) (Q : Measure X) := by
  letI : MetricSpace X := TopologicalSpace.metrizableSpaceMetric X
  let A := MatrixFourierSquareTests.compensator H G hG hβ hβ1 i a n
  let An (k : ℕ) := MatrixFourierSquareTests.compensator H (Gn (φ k)) (hGn (φ k)) hβ hβ1 i a n
  have hSG := source_subgaussian F μ H Gn hGn hβ hβ1 N U hU hcU ξ hEquation B hBound φ i a n
  have hA : StronglyAdapted (CanonicalStateDriverFiltration.filtration H) (fun t x => A t x) :=
    CanonicalFourierCompensator.adapted H (2*(n : ℝ)^2) (by positivity)
      (MatrixFourierCompensator.diagonal G hG hβ hβ1 i a n)
  have hAc (t : ℝ≥0) : Tendsto (fun k => ‖A t-An k t‖) atTop (𝓝 0) :=
    MatrixFourierSquareTests.compensator_limit H G hG hβ hβ1 i a n (fun k => Gn (φ k))
      (fun k => hGn (φ k)) B (fun k => by exact_mod_cast hBound (φ k))
      (error ∘ φ) (fun k => he (φ k)) (helim.comp hφ.tendsto_atTop) (fun k => happrox (φ k)) t
  have hm := WeakLimitCompensatedProducts.martingale laws Q hlim
    (CanonicalStateDriverFiltration.filtration H) (CanonicalStateDriverFiltration.history H)
    (WeakLimitCanonicalBrownian.continuous_history H) (fun _ => le_rfl) M M
    (CanonicalLinearFluctuation.continuous H (coordinate i a n) ((n : ℝ)^2))
    (CanonicalLinearFluctuation.continuous H (coordinate i a n) ((n : ℝ)^2))
    (CanonicalLinearFluctuation.adapted H (coordinate i a n) ((n : ℝ)^2))
    (CanonicalLinearFluctuation.adapted H (coordinate i a n) ((n : ℝ)^2)) c c hSG hSG A An hA hAc
    (fun k s t hst ψ => by
      change (∫ x,ψ (CanonicalStateDriverFiltration.history H s x)*
        (WeakLimitCompensatedProducts.value M M (An k) t x-WeakLimitCompensatedProducts.value M M (An k) s x)
        ∂μ.map _)=0
      exact MatrixFourierSquareTests.random_identity F μ H (Gn (φ k)) (hGn (φ k)) hβ hβ1
        (U (φ k)) (hU (φ k)) (N (φ k)) i a n ξ (hEquation (φ k)) (hcU (φ k)) hnull s t hst ψ)
  have hfun : (fun t x => M t x^2-A t x)=WeakLimitCompensatedProducts.value M M A := by
    funext t x
    change M t x^2-A t x=M t x*M t x-A t x
    rw [pow_two]
  change Martingale (fun t x => M t x^2-A t x) _ _
  rw [hfun]
  exact hm

include hEquation hBound he helim happrox hφ hlim in
/-- All mixed Fourier/driver brackets pass to the same actual joint
weak limit, retaining the noise needed for native integral recognition. -/
theorem mixed (hnull : NullCompleteFiltration.ContainsNullSets F μ) (k : d×FiniteHaar.HaarNode) :
    Martingale (fun t x => M t x*CanonicalStateDriverFiltration.coordinate H k t x-
      MatrixFourierMixedTests.compensator H G hG hβ hβ1 i a n k t x)
      (CanonicalStateDriverFiltration.filtration H) (Q : Measure X) := by
  letI : MetricSpace X := TopologicalSpace.metrizableSpaceMetric X
  let D := CanonicalStateDriverFiltration.coordinate (E := Physical (d := d)) H k
  let A := MatrixFourierMixedTests.compensator H G hG hβ hβ1 i a n k
  let An (m : ℕ) := MatrixFourierMixedTests.compensator H (Gn (φ m)) (hGn (φ m)) hβ hβ1 i a n k
  have hSG := source_subgaussian F μ H Gn hGn hβ hβ1 N U hU hcU ξ hEquation B hBound φ i a n
  have hDG (m : ℕ) (t : ℝ≥0) : HasSubgaussianMGF (D t) (min t H) (laws m : Measure X) := by
    change HasSubgaussianMGF _ _ (μ.map _)
    exact CanonicalBrownianSubGaussian.coordinate F μ H (N (φ m)) (fun t ω => U (φ m) (t,ω)) (hcU (φ m))
      (fun t => ((show IsStronglyPredictable F (fun t ω => U (φ m) (t,ω)) from hU (φ m)).stronglyAdapted t).measurable) k t
  have hA : StronglyAdapted (CanonicalStateDriverFiltration.filtration H) (fun t x => A t x) :=
    CanonicalFourierCompensator.adapted H ((n : ℝ)^2) (sq_nonneg _)
      (MatrixFourierCompensator.mixed G hG hβ hβ1 i a n (MatrixPredictableHaarRotation.basis k))
  have hAc (t : ℝ≥0) : Tendsto (fun m => ‖A t-An m t‖) atTop (𝓝 0) :=
    MatrixFourierMixedTests.compensator_limit H G hG hβ hβ1 i a n (fun m => Gn (φ m))
      (fun m => hGn (φ m)) (error ∘ φ) (fun m => he (φ m)) (helim.comp hφ.tendsto_atTop)
      (fun m => happrox (φ m)) k t
  change Martingale (WeakLimitCompensatedProducts.value M D A) _ _
  apply WeakLimitCompensatedProducts.martingale laws Q hlim
    (CanonicalStateDriverFiltration.filtration H) (CanonicalStateDriverFiltration.history H)
    (WeakLimitCanonicalBrownian.continuous_history H) (fun _ => le_rfl) M D
    (CanonicalLinearFluctuation.continuous H (coordinate i a n) ((n : ℝ)^2))
    (WeakLimitCanonicalBrownian.continuous_coordinate H k)
    (CanonicalLinearFluctuation.adapted H (coordinate i a n) ((n : ℝ)^2))
    (fun t => (CanonicalStateDriverFiltration.coordinate_adapted H k t).stronglyMeasurable)
    c (fun t => min t H) hSG hDG A An hA hAc
  intro m s t hst ψ
  change (∫ x,ψ (CanonicalStateDriverFiltration.history H s x)*
    (WeakLimitCompensatedProducts.value M D (An m) t x-WeakLimitCompensatedProducts.value M D (An m) s x)
    ∂μ.map _)=0
  exact MatrixFourierMixedTests.random_identity F μ H (Gn (φ m)) (hGn (φ m)) hβ hβ1
    (U (φ m)) (hU (φ m)) (N (φ m)) i a n ξ (hEquation (φ m)) (hcU (φ m)) hnull k s t hst ψ

include hEquation hBound he helim happrox hφ hlim in
/-- All actual matrix Fourier equations hold for the joint weak limit,
with the original retained Brownian drivers and limiting coefficient. -/
theorem equation (hnull : NullCompleteFiltration.ContainsNullSets F μ)
    (hBrown : ∀ m (j : Fin m → d×FiniteHaar.HaarNode),FiniteBrownianLawOn
      (CanonicalStateDriverFiltration.filtration H) (Q : Measure X) H
      (fun i => CanonicalStateDriverFiltration.coordinate H (j i)) (fun i k => if j i=j k then 1 else 0)) :
    MatrixCanonicalFourierRecognition.Solves H (Q : Measure X) G hG hβ hβ1 hBrown i a n := by
  obtain ⟨hm,hsg⟩ := linear F μ H Gn hGn hβ hβ1 N U hU hcU ξ hEquation B hBound Q φ hlim i a n hnull
  apply MatrixCanonicalFourierRecognition.equation H (Q : Measure X) G hG hβ hβ1 hBrown i a n hm
    (fun t _ => (hsg t).memLp (2 : ℝ≥0))
  · exact square F μ H Gn hGn hβ hβ1 N U hU hcU ξ hEquation G hG B hBound error he helim happrox Q φ hφ hlim i a n hnull
  · exact mixed F μ H Gn hGn hβ hβ1 N U hU hcU ξ hEquation G hG B hBound error he helim happrox Q φ hφ hlim i a n hnull

end SHEStochastic.MatrixFourierLimitCharacteristics
