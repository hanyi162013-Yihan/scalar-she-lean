module

public import SHEStochastic.MatrixLocalizedMildPath
public import SHEStochastic.LocalizedExitBound

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1300000
noncomputable section

namespace SHEStochastic.MatrixLocalizedExitProbability
open MeasureTheory SHE SHE.PredictableL2 SHE.StoppedFourier MatrixInfiniteHaar
open StoppedPathPasting AdaptedCanonicalPathTests HeatParameterCover HeatParameterPullback
open scoped NNReal ENNReal
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ENNReal)≠⊤) := ⟨by simp⟩
variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
local instance : SecondCountableTopology (Physical (d := Fin n)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (Physical (d := Fin n)) := borel _
local instance : BorelSpace (Physical (d := Fin n)) := ⟨rfl⟩
local instance : MeasurableSpace (Input (d := Fin n)) := borel _
local instance : BorelSpace (Input (d := Fin n)) := ⟨rfl⟩
variable (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (G : MatrixNonlinearCoefficient.Coefficient (Fin n))
    (U : ℝ≥0×Ω → Physical (d := Fin n)) (hU : StronglyMeasurable[F.predictable] U)

variable (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0) (hH : (H : ℝ)≤1) (hH0 : 0<H)

include hH0 in
/-- The genuine matrix mild solution's L2 exit is controlled by its
initial L2 tail and the finitely many localized stochastic field tails.
The pre-exit reconstruction and its random-stop identification are
proved above, rather than assumed as an extra solution property. -/
theorem bound (hc : ∀ ω,Continuous (fun t => U (t,ω))) (N : ℕ) (hN : 0<N)
    (B : FiniteScalarIto.Family F μ H (Fin n×SHE.FiniteHaar.HaarNode))
    (hnull : NullCompleteFiltration.ContainsNullSets F μ)
    (ξ : Ω → Physical (d := Fin n)) (hξ : Measurable ξ)
    (hEq : MatrixRandomMildExistence.Equation G hH B U hU ξ)
    (Y : Ω → (Fin n → C(Parameter,ℝ)))
    (hY : ∀ p i,(fun ω => Y ω i p)=ᵐ[μ]
      MatrixLocalizedPointField.value F G (MatrixL2LocalizedPointRows.state U (N : ℝ≥0))
        (MatrixL2LocalizedPointRows.predictable F U hU (N : ℝ≥0)) μ H hH B p i)
    (hzY : ∀ᵐ ω ∂μ,∀ i p,Y ω i (HeatParameterCoordinates.zeroTime p)=0) :
    μ {ω | ContinuousNormExit.exit (fun t ω => U (t,ω)) N ω≤(H : WithTop ℝ≥0)} ≤
      μ {ω | (N : ℝ)/2≤‖ξ ω‖}+
        ∑ i,μ {ω | (N : ℝ)/(4*((n : ℝ)+1))<‖Y ω i‖} := by
  have hs := MatrixLocalizedMildPath.state_before F G U hU μ H hH hH0 hc N B hnull ξ hξ hEq Y hY hzY
  apply LocalizedExitBound.finite_fields μ (fun t ω => U (t,ω)) hc N hN H
    (fun ω => ‖ξ ω‖) (fun i ω => ‖Y ω i‖)
  filter_upwards [hs] with ω hω s hsH hsτ
  let t : Time H := ⟨(s : ℝ),s.coe_nonneg,hsH⟩
  have ht : toNN H t=s := by apply NNReal.eq;rfl
  have he := hω t (by rw [ht];exact hsτ)
  rw [ht] at he
  rw [he]
  exact VectorMildPathEnvelope.norm_bound H hH0 (ξ ω) (Y ω) t

end SHEStochastic.MatrixLocalizedExitProbability
