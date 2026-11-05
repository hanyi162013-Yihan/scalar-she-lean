module

public import SHEStochastic.MatrixApproximationCompactness
public import SHEStochastic.MatrixFourierPathMoments
public import SHEStochastic.CanonicalLinearWeakLimit

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section

namespace SHEStochastic.MatrixFourierApproximationLimit
open MeasureTheory ProbabilityTheory Filter SHE SHE.PredictableL2 SHE.FiniteHaar MatrixInfiniteHaar
open CanonicalStateDriverFiltration
open scoped NNReal ENNReal Topology Matrix.Norms.L2Operator
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {n : ℕ}
local instance : SecondCountableTopology (Physical (d := Fin n)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (Physical (d := Fin n)) := borel _
local instance : BorelSpace (Physical (d := Fin n)) := ⟨rfl⟩
local instance : MeasurableSpace (Input (d := Fin n)) := borel _
local instance : BorelSpace (Input (d := Fin n)) := ⟨rfl⟩
variable (F : Filtration ℝ≥0 mΩ) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
    (hH : (H : ℝ) ≤ 1) (hH0 : 0 < H)
    (G : ℕ → MatrixNonlinearCoefficient.Coefficient (Fin n))
    (N : ℕ → FiniteScalarIto.Family F μ H ((Fin n) × HaarNode))
    (U : ℕ → ℝ≥0 × Ω → Physical (d := Fin n))
    (hU : ∀ m, StronglyMeasurable[F.predictable] (U m))
    (hc : ∀ m ω, Continuous (fun t => U m (t,ω)))
    (u₀ : Physical (d := Fin n))

variable {C : ℕ → ℝ≥0} {β : ℝ≥0} (hG : ∀ m,HolderWith (C m) β (G m).value)
    (hβ : 0 < β) (hβ1 : β ≤ 1) (B : ℝ≥0) (hBound : ∀ m,(G m).bound ≤ B)
local notation "X" => CanonicalContinuousStateDriver.Space (E := Physical (d := Fin n)) (ι := Fin n×HaarNode) H

include hH0 hG hβ hβ1 hBound in
/-- The actual matrix approximations have a joint weak limit whose
Fourier fluctuations are genuine martingales with uniform sub-Gaussian
moments. Initial data and full Brownian histories are retained. -/
theorem exists_random_limit (ξ : Ω → Physical (d := Fin n)) (hξ : Measurable ξ) (hnull : NullCompleteFiltration.ContainsNullSets F μ)
    (cap : ℝ) (hcap : 0 ≤ cap) (hCaps : ∀ m,NativeMatrixEquation.cap (G m) ≤ cap)
    (hEq : ∀ m,MatrixRandomMildExistence.Equation (G m) hH (N m) (U m) (hU m) ξ) :
    ∃ noise : ℕ → FiniteScalarIto.Family F μ H (Fin n×HaarNode),
      (∀ m,MatrixFourierMildRealization.RandomEquation F μ H (G m) (hG m) hβ hβ1
        (U m) (hU m) (noise m) ξ) ∧ ∃ Q : ProbabilityMeasure X,∃ φ : ℕ → ℕ,StrictMono φ ∧
        Tendsto ((CanonicalApproximationCompactness.varyingLaws F μ H
          (fun m t ω => U m (t,ω)) hc noise) ∘ φ) atTop (𝓝 Q) ∧
        (∀ k (a : Fin k → Fin n×HaarNode),FiniteBrownianLawOn
          (filtration (E := Physical (d := Fin n)) (ι := Fin n×HaarNode) H)
          (Q : Measure X) H (fun i => coordinate H (a i)) (fun i j => if a i=a j then 1 else 0)) ∧
        (Q : Measure X).map (CanonicalInitialLaw.initial H)=
          μ.map (fun ω : Ω => (ξ ω,fun _ : Fin n×HaarNode => (0 : ℝ))) ∧
        ∀ (i : Fin n) (a : ℂ →L[ℝ] ℝ) (freq : ℤ),
          Martingale (CanonicalLinearFluctuation.value H (MatrixFourierCoordinates.coordinate i a freq) ((freq : ℝ)^2))
            (filtration H) (Q : Measure X) ∧
          ∀ t,HasSubgaussianMGF
            (CanonicalLinearFluctuation.value H (MatrixFourierCoordinates.coordinate i a freq) ((freq : ℝ)^2) t)
            (min t H*MatrixFourierInput.commonCap H a freq B^2) (Q : Measure X) := by
  choose noise hnoise using fun m => MatrixFourierMildRealization.exists_random_family F μ H
    (G m) (hG m) hβ hβ1 (U m) (hU m) hH (N m) ξ hnull (hEq m)
  have ha (m : ℕ) (t : ℝ≥0) : Measurable[F t] (fun ω => U m (t,ω)) :=
    ((show IsStronglyPredictable F (fun t ω => U m (t,ω)) from hU m).stronglyAdapted t).measurable
  obtain ⟨Q,φ,hφ,hlim,hBrown⟩ := CanonicalApproximationCompactness.exists_limit_varying
    F μ H (fun m t ω => U m (t,ω)) hc ha noise
    (MatrixSolutionPathTightness.tight_random F μ H hH hH0 G N U hU hc ξ hξ cap hcap hCaps hEq)
  refine ⟨noise,hnoise,Q,φ,hφ,hlim,hBrown,?_,?_⟩
  · apply CanonicalInitialLaw.preserved F μ H (fun m t ω => U m (t,ω)) hc hU noise
      ξ hξ _ Q φ hlim
    intro m
    exact MatrixRandomInitialLaw.initial (G m) hH (N m) (U m) (hU m) ξ (hEq m)
  · intro i a freq
    apply CanonicalLinearWeakLimit.martingale H (MatrixFourierCoordinates.coordinate i a freq) ((freq : ℝ)^2)
      ((CanonicalApproximationCompactness.varyingLaws F μ H (fun m t ω => U m (t,ω)) hc noise) ∘ φ)
      Q hlim (fun t => min t H*MatrixFourierInput.commonCap H a freq B^2)
    · intro k t
      change HasSubgaussianMGF _ _ (μ.map _)
      exact MatrixFourierPathMoments.random_subgaussian F μ H (G (φ k)) (hG (φ k)) hβ hβ1
        (U (φ k)) (hU (φ k)) (noise (φ k)) ξ (hnoise (φ k)) (hc (φ k)) B (hBound (φ k)) i a freq t
    · intro k s t hst ψ
      change (∫ x,ψ (history H s x)*
        (CanonicalLinearFluctuation.value H (MatrixFourierCoordinates.coordinate i a freq) ((freq : ℝ)^2) t x-
          CanonicalLinearFluctuation.value H (MatrixFourierCoordinates.coordinate i a freq) ((freq : ℝ)^2) s x)
        ∂μ.map _)=0
      exact MatrixFourierPathMoments.random_identity F μ H (G (φ k)) (hG (φ k)) hβ hβ1
        (U (φ k)) (hU (φ k)) (noise (φ k)) ξ (hnoise (φ k)) (hc (φ k)) hnull i a freq s t hst ψ


include hH0 hG hβ hβ1 hBound in
theorem exists_limit (hnull : NullCompleteFiltration.ContainsNullSets F μ)
    (cap : ℝ) (hcap : 0 ≤ cap) (hCaps : ∀ m,NativeMatrixEquation.cap (G m) ≤ cap)
    (hEq : ∀ m,MatrixContinuousMild.Equation (G m) hH (N m) (U m) (hU m) u₀) :
    ∃ noise : ℕ → FiniteScalarIto.Family F μ H (Fin n×HaarNode),
      (∀ m,MatrixFourierMildRealization.Equation F μ H (G m) (hG m) hβ hβ1
        (U m) (hU m) (noise m) u₀) ∧ ∃ Q : ProbabilityMeasure X,∃ φ : ℕ → ℕ,StrictMono φ ∧
        Tendsto ((CanonicalApproximationCompactness.varyingLaws F μ H
          (fun m t ω => U m (t,ω)) hc noise) ∘ φ) atTop (𝓝 Q) ∧
        (∀ k (a : Fin k → Fin n×HaarNode),FiniteBrownianLawOn
          (filtration (E := Physical (d := Fin n)) (ι := Fin n×HaarNode) H)
          (Q : Measure X) H (fun i => coordinate H (a i)) (fun i j => if a i=a j then 1 else 0)) ∧
        (Q : Measure X).map (CanonicalInitialLaw.initial H)=
          μ.map (fun _ : Ω => (u₀,fun _ : Fin n×HaarNode => (0 : ℝ))) ∧
        ∀ (i : Fin n) (a : ℂ →L[ℝ] ℝ) (freq : ℤ),
          Martingale (CanonicalLinearFluctuation.value H (MatrixFourierCoordinates.coordinate i a freq) ((freq : ℝ)^2))
            (filtration H) (Q : Measure X) ∧
          ∀ t,HasSubgaussianMGF
            (CanonicalLinearFluctuation.value H (MatrixFourierCoordinates.coordinate i a freq) ((freq : ℝ)^2) t)
            (min t H*MatrixFourierInput.commonCap H a freq B^2) (Q : Measure X) := by
  exact exists_random_limit F μ H hH hH0 G N U hU hc hG hβ hβ1 B hBound
    (fun _ => u₀) measurable_const hnull cap hcap hCaps hEq

end SHEStochastic.MatrixFourierApproximationLimit
