module

public import SHEStochastic.MatrixFourierPathMoments
public import SHEStochastic.MatrixFourierCompensator
public import SHEStochastic.CanonicalFourierCompensator
public import SHEStochastic.CanonicalLawMartingaleTests
public import SHEStochastic.WeakLimitCompensatedProducts

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
noncomputable section

namespace SHEStochastic.MatrixFourierSquareTests
open MeasureTheory SHE SHE.PredictableL2 MatrixInfiniteHaar MatrixFourierCoordinates
open scoped NNReal ENNReal Topology Matrix.Norms.L2Operator
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

variable (i : d) (a : ℂ →L[ℝ] ℝ) (n : ℤ)
local notation "X" => CanonicalContinuousStateDriver.Space (E := Physical (d := d)) (ι := d×FiniteHaar.HaarNode) H
local notation "M" => CanonicalLinearFluctuation.value (ι := d×FiniteHaar.HaarNode) H (coordinate i a n) ((n : ℝ)^2)

def compensator (t : ℝ≥0) : BoundedContinuousFunction X ℝ :=
  CanonicalFourierCompensator.functional H (2*(n : ℝ)^2) (by positivity)
    (MatrixFourierCompensator.diagonal G hG hβ hβ1 i a n) t

/-- Uniform square-diffusion approximation gives uniform path-compensator convergence. -/
theorem compensator_limit (Gn : ℕ → MatrixNonlinearCoefficient.Coefficient d) {Cn : ℕ → ℝ≥0}
    (hGn : ∀ k,HolderWith (Cn k) β (Gn k).value) (B : ℝ) (hB : ∀ k,((Gn k).bound : ℝ) ≤ B)
    (error : ℕ → ℝ) (he : ∀ k,0 ≤ error k) (helim : Filter.Tendsto error Filter.atTop (𝓝 0))
    (happrox : ∀ k z,‖G.value z-(Gn k).value z‖ ≤ error k) (t : ℝ≥0) :
    Filter.Tendsto (fun k => ‖compensator H G hG hβ hβ1 i a n t-
      compensator H (Gn k) (hGn k) hβ hβ1 i a n t‖) Filter.atTop (𝓝 0) := by
  apply CanonicalFourierCompensator.uniform_limit H (2*(n : ℝ)^2) (by positivity)
    (MatrixFourierCompensator.diagonal G hG hβ hβ1 i a n)
    (fun k => MatrixFourierCompensator.diagonal (Gn k) (hGn k) hβ hβ1 i a n) _ t
  have hh := MatrixStateNoise.uniform_covariance_limit G hG hβ hβ1 Gn hGn B hB error he helim happrox
    i i (weight a n) (weight a n)
  simpa only [MatrixFourierCompensator.diagonal,norm_sub_rev] using tendsto_iff_norm_sub_tendsto_zero.mp hh

/-- Actual matrix solutions satisfy the full-past square-compensator
identities used to recognize the weak limit. -/
theorem random_identity
    (ξ : Ω → Physical (d := d))
    (hRandom : MatrixFourierMildRealization.RandomEquation F μ H G hG hβ hβ1 U hU N ξ) (hcU : ∀ ω,Continuous (fun t => U (t,ω)))
    (hnull : NullCompleteFiltration.ContainsNullSets F μ) (s t : ℝ≥0) (hst : s ≤ t)
    (ψ : BoundedContinuousFunction X ℝ) :
    (∫ x,ψ (CanonicalStateDriverFiltration.history H s x)*
      (WeakLimitCompensatedProducts.value M M (compensator H G hG hβ hβ1 i a n) t x-
        WeakLimitCompensatedProducts.value M M (compensator H G hG hβ hβ1 i a n) s x)
      ∂μ.map (CanonicalNativeBrownian.bundle F μ H N (fun t ω => U (t,ω)) hcU))=0 := by
  let r := MatrixFourierInput.input F μ H G hG hβ hβ1 U hU i a n
  let bundle := CanonicalNativeBrownian.bundle F μ H N (fun t ω => U (t,ω)) hcU
  have hUa (t : ℝ≥0) : Measurable[F t] (fun ω => U (t,ω)) :=
    ((show IsStronglyPredictable F (fun t ω => U (t,ω)) from hU).stronglyAdapted t).measurable
  obtain ⟨Y,_,haY,_,_,hrY⟩ := NativeMartingaleVersion.exists_version N MatrixPredictableHaarRotation.basis hnull r
  have hSq := PredictableBracket.square_compensator_martingale
    (FiniteCylindricalIto.terminalIto N.toCoordinates MatrixPredictableHaarRotation.basis)
    (FiniteCylindricalIto.pastLocality N MatrixPredictableHaarRotation.basis) r haY hrY
  apply CanonicalLawMartingaleTests.identity μ F H bundle
    (CanonicalNativeBrownian.measurable_bundle F μ H N (fun t ω => U (t,ω)) hcU hUa)
    (CanonicalStateDriverFiltration.history H) (WeakLimitCanonicalBrownian.continuous_history H)
    (CanonicalNativeBrownian.past_adapted_capped F μ H N (fun t ω => U (t,ω)) hcU hUa)
    (WeakLimitCompensatedProducts.value M M (compensator H G hG hβ hβ1 i a n))
    (fun q => ((CanonicalLinearFluctuation.continuous H (coordinate i a n) ((n : ℝ)^2) q).mul
      (CanonicalLinearFluctuation.continuous H (coordinate i a n) ((n : ℝ)^2) q)).sub
        (compensator H G hG hβ hβ1 i a n q).continuous)
    (fun q ω => Y q ω^2-PredictableBracket.energy r q ω) hSq
  · intro q
    have hm := CanonicalNativeLinearTests.representation F μ H N MatrixPredictableHaarRotation.basis
      (fun t ω => U (t,ω)) hcU (coordinate i a n) ((n : ℝ)^2) r
      (MatrixFourierPathMoments.random_representation F μ H G hG hβ hβ1 U hU N ξ hRandom i a n) q
    filter_upwards [hm,hrY (min q H),MatrixFourierCompensator.energy_ae F μ H G hG hβ hβ1 U hU i a n]
      with ω hm hy he
    change M q (bundle ω)*M q (bundle ω)-
      CanonicalFourierCompensator.value H (2*(n : ℝ)^2) _ _ q (bundle ω)=_
    rw [CanonicalFourierCompensator.comp_bundle,← he (min q H) (min_le_right _ _)]
    change M q (bundle ω)=_ at hm
    rw [hm.trans hy.symm,pow_two]
  · exact hst


include hEquation in
theorem identity (hcU : ∀ ω,Continuous (fun t => U (t,ω)))
    (hnull : NullCompleteFiltration.ContainsNullSets F μ) (s t : ℝ≥0) (hst : s ≤ t)
    (ψ : BoundedContinuousFunction X ℝ) :
    (∫ x,ψ (CanonicalStateDriverFiltration.history H s x)*
      (WeakLimitCompensatedProducts.value M M (compensator H G hG hβ hβ1 i a n) t x-
        WeakLimitCompensatedProducts.value M M (compensator H G hG hβ hβ1 i a n) s x)
      ∂μ.map (CanonicalNativeBrownian.bundle F μ H N (fun t ω => U (t,ω)) hcU))=0 := by
  exact random_identity F μ H G hG hβ hβ1 U hU N i a n (fun _ => u₀) hEquation hcU hnull s t hst ψ

end SHEStochastic.MatrixFourierSquareTests
