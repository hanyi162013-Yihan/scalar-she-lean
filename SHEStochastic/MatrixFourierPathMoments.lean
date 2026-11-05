module

public import SHEStochastic.MatrixFourierMildRealization
public import SHEStochastic.CanonicalNativeLinearTests

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
noncomputable section

namespace SHEStochastic.MatrixFourierPathMoments
open MeasureTheory SHE SHE.PredictableL2 MatrixInfiniteHaar MatrixFourierCoordinates
open scoped NNReal ENNReal Matrix.Norms.L2Operator
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
variable {d Ω : Type*} [Fintype d] [DecidableEq d] [mΩ : MeasurableSpace Ω]
local instance : SecondCountableTopology (Physical (d := d)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (Physical (d := d)) := borel _
local instance : BorelSpace (Physical (d := d)) := ⟨rfl⟩
local instance : MeasurableSpace (Input (d := d)) := borel _
local instance : BorelSpace (Input (d := d)) := ⟨rfl⟩
variable (F : Filtration ℝ≥0 mΩ) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
    (G : MatrixNonlinearCoefficient.Coefficient d) {C β : ℝ≥0}
    (hG : HolderWith C β G.value) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (U : ℝ≥0×Ω → Physical (d := d)) (hU : StronglyMeasurable[F.predictable] U)
variable (N : FiniteScalarIto.Family F μ H (d×FiniteHaar.HaarNode)) (u₀ : Physical (d := d))
    (hEquation : MatrixFourierMildRealization.Equation F μ H G hG hβ hβ1 U hU N u₀)

theorem random_representation
    (Z : Ω → Physical (d := d))
    (hRandom : MatrixFourierMildRealization.RandomEquation F μ H G hG hβ hβ1 U hU N Z) (i : d) (a : ℂ →L[ℝ] ℝ) (n : ℤ) (t : ℝ≥0) (ht : t ≤ H) :
    (fun ω => Real.exp ((t : ℝ)*(n : ℝ)^2)*coordinate i a n (U (t,ω))-coordinate i a n (U (0,ω))) =ᵐ[μ]
      (FiniteCylindricalIto.terminalIto N.toCoordinates MatrixPredictableHaarRotation.basis).integral
        (StoppedItoInputs.stop F μ H t (MatrixFourierInput.input F μ H G hG hβ hβ1 U hU i a n)) := by
  filter_upwards [hRandom i a n t ht,hRandom i a n 0 zero_le,Lp.coeFn_zero ℝ 2 μ] with ω ht h0 hz
  have h0' : coordinate i a n (U (0,ω))=coordinate i a n (Z ω) := by
    simpa only [NNReal.coe_zero,zero_mul,Real.exp_zero,one_mul,StoppedItoInputs.stop_zero,map_zero,
      hz,Pi.zero_apply,add_zero] using h0
  rw [ht,h0']
  ring


/-- The actual approximation law has one uniform sub-Gaussian bound
for every matrix Fourier fluctuation. -/
theorem random_subgaussian
    (Z : Ω → Physical (d := d))
    (hRandom : MatrixFourierMildRealization.RandomEquation F μ H G hG hβ hβ1 U hU N Z) (hcU : ∀ ω,Continuous (fun t => U (t,ω)))
    (B : ℝ≥0) (hB : G.bound ≤ B) (i : d) (a : ℂ →L[ℝ] ℝ) (n : ℤ) (t : ℝ≥0) :
    ProbabilityTheory.HasSubgaussianMGF
      (CanonicalLinearFluctuation.value (ι := d×FiniteHaar.HaarNode) H (coordinate i a n) ((n : ℝ)^2) t)
      (min t H*MatrixFourierInput.commonCap H a n B^2)
      (μ.map (CanonicalNativeBrownian.bundle F μ H N (fun t ω => U (t,ω)) hcU)) :=
  CanonicalNativeLinearTests.subgaussian F μ H N MatrixPredictableHaarRotation.basis
    (fun t ω => U (t,ω)) hU hcU (coordinate i a n) ((n : ℝ)^2)
    (MatrixFourierInput.input F μ H G hG hβ hβ1 U hU i a n)
    (random_representation F μ H G hG hβ hβ1 U hU N Z hRandom i a n) _
    (MatrixFourierInput.input_bound_of_le F μ H G hG hβ hβ1 U hU i a n B hB) t


/-- Full-past martingale identities for the same actual approximation law. -/
theorem random_identity
    (Z : Ω → Physical (d := d))
    (hRandom : MatrixFourierMildRealization.RandomEquation F μ H G hG hβ hβ1 U hU N Z) (hcU : ∀ ω,Continuous (fun t => U (t,ω)))
    (hnull : NullCompleteFiltration.ContainsNullSets F μ) (i : d) (a : ℂ →L[ℝ] ℝ) (n : ℤ)
    (s t : ℝ≥0) (hst : s ≤ t)
    (ψ : BoundedContinuousFunction (CanonicalContinuousStateDriver.Space
      (E := Physical (d := d)) (ι := d×FiniteHaar.HaarNode) H) ℝ) :
    (∫ x,ψ (CanonicalStateDriverFiltration.history H s x)*
      (CanonicalLinearFluctuation.value H (coordinate i a n) ((n : ℝ)^2) t x-
        CanonicalLinearFluctuation.value H (coordinate i a n) ((n : ℝ)^2) s x)
      ∂μ.map (CanonicalNativeBrownian.bundle F μ H N (fun t ω => U (t,ω)) hcU))=0 :=
  CanonicalNativeLinearTests.identity F μ H N MatrixPredictableHaarRotation.basis
    (fun t ω => U (t,ω)) hU hcU (coordinate i a n) ((n : ℝ)^2)
    (MatrixFourierInput.input F μ H G hG hβ hβ1 U hU i a n)
    (random_representation F μ H G hG hβ hβ1 U hU N Z hRandom i a n) hnull s t hst ψ

include hEquation in
theorem representation (i : d) (a : ℂ →L[ℝ] ℝ) (n : ℤ) (t : ℝ≥0) (ht : t ≤ H) :
    (fun ω => Real.exp ((t : ℝ)*(n : ℝ)^2)*coordinate i a n (U (t,ω))-coordinate i a n (U (0,ω))) =ᵐ[μ]
      (FiniteCylindricalIto.terminalIto N.toCoordinates MatrixPredictableHaarRotation.basis).integral
        (StoppedItoInputs.stop F μ H t (MatrixFourierInput.input F μ H G hG hβ hβ1 U hU i a n)) :=
  random_representation F μ H G hG hβ hβ1 U hU N (fun _ => u₀) hEquation i a n t ht

include hEquation in
theorem subgaussian (hcU : ∀ ω,Continuous (fun t => U (t,ω)))
    (B : ℝ≥0) (hB : G.bound ≤ B) (i : d) (a : ℂ →L[ℝ] ℝ) (n : ℤ) (t : ℝ≥0) :
    ProbabilityTheory.HasSubgaussianMGF
      (CanonicalLinearFluctuation.value (ι := d×FiniteHaar.HaarNode) H (coordinate i a n) ((n : ℝ)^2) t)
      (min t H*MatrixFourierInput.commonCap H a n B^2)
      (μ.map (CanonicalNativeBrownian.bundle F μ H N (fun t ω => U (t,ω)) hcU)) :=
  random_subgaussian F μ H G hG hβ hβ1 U hU N (fun _ => u₀) hEquation hcU B hB i a n t

include hEquation in
theorem identity (hcU : ∀ ω,Continuous (fun t => U (t,ω)))
    (hnull : NullCompleteFiltration.ContainsNullSets F μ) (i : d) (a : ℂ →L[ℝ] ℝ) (n : ℤ)
    (s t : ℝ≥0) (hst : s ≤ t)
    (ψ : BoundedContinuousFunction (CanonicalContinuousStateDriver.Space
      (E := Physical (d := d)) (ι := d×FiniteHaar.HaarNode) H) ℝ) :
    (∫ x,ψ (CanonicalStateDriverFiltration.history H s x)*
      (CanonicalLinearFluctuation.value H (coordinate i a n) ((n : ℝ)^2) t x-
        CanonicalLinearFluctuation.value H (coordinate i a n) ((n : ℝ)^2) s x)
      ∂μ.map (CanonicalNativeBrownian.bundle F μ H N (fun t ω => U (t,ω)) hcU))=0 :=
  random_identity F μ H G hG hβ hβ1 U hU N (fun _ => u₀) hEquation hcU hnull i a n s t hst ψ

end SHEStochastic.MatrixFourierPathMoments
