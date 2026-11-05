module

public import SHEStochastic.MatrixFourierPullback
public import SHEStochastic.RandomInitialBrownianFamily

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHEStochastic.CompletedMatrixFourierSolution
open MeasureTheory SHE SHE.PredictableL2 MatrixInfiniteHaar
open scoped NNReal ENNReal Matrix.Norms.L2Operator
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
variable {d Ω : Type*} [Fintype d] [DecidableEq d] [mΩ : MeasurableSpace Ω]
local instance : SecondCountableTopology (Physical (d := d)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (Physical (d := d)) := borel _
local instance : BorelSpace (Physical (d := d)) := ⟨rfl⟩
variable (F : Filtration ℝ≥0 mΩ) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
    (G : MatrixNonlinearCoefficient.Coefficient d) {C β : ℝ≥0}
    (hG : HolderWith C β G.value) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (U : ℝ≥0×Ω → Physical (d := d)) (hU : StronglyMeasurable[F.predictable] U)
    (P : FiniteScalarIto.Family F μ H (d×FiniteHaar.HaarNode))
local notation "ρ" => (Measure.dirac () : Measure Unit)
local notation "Fc" => RandomInitialBrownianFamily.filtration ρ μ F
local notation "μc" => IndependentNoiseCompletion.measure ρ μ

def state (p : ℝ≥0×RandomInitialBrownianFamily.Space ρ μ) : Physical (d := d) := U (p.1,p.2.2)

theorem filtered (t : ℝ≥0) :
    @Measurable (RandomInitialBrownianFamily.Space ρ μ) Ω (Fc t) (F t) Prod.snd :=
  (@measurable_snd Unit Ω inferInstance (F t)).mono le_sup_left le_rfl

include hU in
theorem predictable : StronglyMeasurable[(Fc).predictable] (state μ U) :=
  MatrixFourierPullback.predictable (Ξ := RandomInitialBrownianFamily.Space ρ μ)
    (D := Fc) Prod.snd (filtered F μ) U hU

/-- Completion changes neither the path nor its continuity. -/
theorem continuous (hcU : ∀ ω,Continuous (fun t => U (t,ω)))
    (ω : RandomInitialBrownianFamily.Space ρ μ) : Continuous (fun t => state μ U (t,ω)) := hcU ω.2

/-- The genuine Fourier solution has a completed native Haar mild
realization with precisely the same state and initial random variable. -/
theorem exists_haar_equation (Z : Ω → Physical (d := d)) (hH : (H : ℝ) ≤ 1)
    (hFourier : MatrixFourierMildRealization.RandomEquation F μ H G hG hβ hβ1 U hU P Z) :
    ∃ B : FiniteScalarIto.Family Fc μc H (d×FiniteHaar.HaarNode),
      MatrixRandomMildExistence.Equation G hH B (state μ U) (predictable F μ U hU) (Z ∘ Prod.snd) := by
  let B := RandomInitialBrownianFamily.family ρ μ F H P
  have he := MatrixFourierPullback.equation (Ξ := RandomInitialBrownianFamily.Space ρ μ)
    (D := Fc) Prod.snd (IndependentNoiseCompletion.snd_preserving ρ μ) (filtered F μ)
    G hG hβ hβ1 U hU P B (fun _ _ _ => rfl) Z hFourier
  exact MatrixFourierMildRecognition.exists_haar_equation Fc μc H G hG hβ hβ1
    (state μ U) (predictable F μ U hU) hH B (Z ∘ Prod.snd) he
    (RandomInitialBrownianFamily.contains_null ρ μ F)

end SHEStochastic.CompletedMatrixFourierSolution
