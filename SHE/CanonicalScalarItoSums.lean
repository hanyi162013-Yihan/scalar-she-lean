module
public import SHE.CanonicalScalarItoCells
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false
namespace SHE.CanonicalScalarItoSums
open MeasureTheory PredictableL2 FiniteHaar CanonicalContinuousStateDriver
open scoped NNReal ENNReal Topology
local instance canonicalSums_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance canonicalSums_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable (H : ℝ≥0) (t : ℕ→ℝ≥0) (ht : ∀k,t k≤H) (Φ : ℕ→E→RealHaarInput)
variable (S : Finset (ℕ×HaarNode))

def value (p : Space (E:=E) (ι:=HaarNode) H) : ℝ :=
  ∑j∈S,CanonicalScalarItoCells.value H (t j.1) (t (j.1+1))
    (ht j.1) (ht (j.1+1)) (Φ j.1) j.2 p

theorem value_measurable (hΦ : ∀k,Measurable (Φ k)) : Measurable (value H t ht Φ S) :=
  Finset.measurable_sum S (fun j _=>CanonicalScalarItoCells.value_measurable
    H (t j.1) (t (j.1+1)) (ht j.1) (ht (j.1+1)) (Φ j.1) j.2 (hΦ j.1))

variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ]
variable (J : StandardTerminalIto (C:=RealHaarInput) (E:=ℝ) 𝓕 μ H)

/-- A full finite path-functional sum is an actual SAME-J integral,
with its exact elementary predictable row recorded simultaneously. -/
theorem exists_input (hmono : ∀k,t k≤t (k+1)) (hΦ : ∀k,Measurable (Φ k))
    (M : ℝ) (hM : 0≤M) (hbound : ∀k u,‖Φ k u‖≤M)
    (hlocal : StandardTerminalPastLocality J)
    (U : ℝ≥0→Ω→E) (hc : ∀ω,Continuous (fun t=>U t ω)) (hUa : StronglyAdapted 𝓕 U)
    (W : HaarNode→ℝ≥0→Ω→ℝ) (hWc : ∀i ω,Continuous (fun t=>W i t ω))
    (hW : ∀i k,W i (t k)=ᵐ[μ] CanonicalScalarItoCells.coordinate H i 𝓕 μ J (t k)) :
    ∃f:Process (E:=RealHaarInput) 𝓕 μ H,
      f=ᵐ[energyMeasure μ H] (fun p=>∑j∈S,if t j.1<p.1 ∧ p.1<t (j.1+1) then
        (Φ j.1 (U (t j.1) p.2) j.2) • lp.single 2 j.2 (1:ℝ) else 0) ∧
      J.integral f=ᵐ[μ] (fun ω=>value H t ht Φ S (bundle H U hc W hWc ω)) := by
  classical
  choose f hf hi using fun k i=>CanonicalScalarItoCells.exists_canonical_input
    H (t k) (t (k+1)) (ht k) (ht (k+1)) (Φ k) i 𝓕 μ J
    (hmono k) (hΦ k) M hM (hbound k) hlocal U hc hUa W hWc (hW i k) (hW i (k+1))
  refine ⟨∑j∈S,f j.1 j.2,?_,?_⟩
  · have hall := ae_all_iff.mpr (fun j:ℕ×HaarNode=>hf j.1 j.2)
    have hs := ae_eq_of_ae_eq_trim (Lp.coeFn_fun_finsetSum S (fun j=>f j.1 j.2))
    filter_upwards [hall,hs] with p hp hs
    rw [hs]
    exact Finset.sum_congr rfl (fun j _=>hp j)
  · rw [map_sum]
    have hall := ae_all_iff.mpr (fun j:ℕ×HaarNode=>hi j.1 j.2)
    filter_upwards [hall,Lp.coeFn_fun_finsetSum S (fun j=>J.integral (f j.1 j.2))] with ω hω hs
    rw [hs]
    simp only [value]
    exact Finset.sum_congr rfl (fun j _=>hω j)
end SHE.CanonicalScalarItoSums
