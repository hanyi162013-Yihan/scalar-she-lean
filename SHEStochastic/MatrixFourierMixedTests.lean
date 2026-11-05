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

namespace SHEStochastic.MatrixFourierMixedTests
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

def compensator (k : d×FiniteHaar.HaarNode) (t : ℝ≥0) : BoundedContinuousFunction X ℝ :=
  CanonicalFourierCompensator.functional H ((n : ℝ)^2) (sq_nonneg _)
    (MatrixFourierCompensator.mixed G hG hβ hβ1 i a n (MatrixPredictableHaarRotation.basis k)) t

theorem compensator_limit (Gn : ℕ → MatrixNonlinearCoefficient.Coefficient d) {Cn : ℕ → ℝ≥0}
    (hGn : ∀ k,HolderWith (Cn k) β (Gn k).value)
    (error : ℕ → ℝ) (he : ∀ k,0 ≤ error k) (helim : Filter.Tendsto error Filter.atTop (𝓝 0))
    (happrox : ∀ k z,‖G.value z-(Gn k).value z‖ ≤ error k) (k : d×FiniteHaar.HaarNode) (t : ℝ≥0) :
    Filter.Tendsto (fun r => ‖compensator H G hG hβ hβ1 i a n k t-
      compensator H (Gn r) (hGn r) hβ hβ1 i a n k t‖) Filter.atTop (𝓝 0) := by
  let b : Input (d := d) := MatrixPredictableHaarRotation.basis k
  have hh : Filter.Tendsto
      (fun r => MatrixFourierCompensator.mixed (Gn r) (hGn r) hβ hβ1 i a n b)
      Filter.atTop (𝓝 (MatrixFourierCompensator.mixed G hG hβ hβ1 i a n b)) :=
    MatrixStateNoise.uniform_cross_limit G hG hβ hβ1 Gn hGn error he helim happrox
      i (weight a n) ((VectorWhiteCoordinates.analysis (d := d)).symm b)
  have hn : Filter.Tendsto (fun r => ‖MatrixFourierCompensator.mixed G hG hβ hβ1 i a n b-
      MatrixFourierCompensator.mixed (Gn r) (hGn r) hβ hβ1 i a n b‖) Filter.atTop (𝓝 0) :=
    (tendsto_iff_norm_sub_tendsto_zero.mp hh).congr' (Filter.Eventually.of_forall fun r => norm_sub_rev _ _)
  exact CanonicalFourierCompensator.uniform_limit
    (E := Physical (d := d)) (ι := d×FiniteHaar.HaarNode) H ((n : ℝ)^2) (sq_nonneg _)
    (MatrixFourierCompensator.mixed G hG hβ hβ1 i a n b)
    (fun r => MatrixFourierCompensator.mixed (Gn r) (hGn r) hβ hβ1 i a n b) hn t

/-- Every original driver has the correct mixed compensator with each
matrix Fourier fluctuation, on the actual joint approximation law. -/
theorem random_identity
    (ξ : Ω → Physical (d := d))
    (hRandom : MatrixFourierMildRealization.RandomEquation F μ H G hG hβ hβ1 U hU N ξ) (hcU : ∀ ω,Continuous (fun t => U (t,ω)))
    (hnull : NullCompleteFiltration.ContainsNullSets F μ) (k : d×FiniteHaar.HaarNode)
    (s t : ℝ≥0) (hst : s ≤ t) (ψ : BoundedContinuousFunction X ℝ) :
    (∫ x,ψ (CanonicalStateDriverFiltration.history H s x)*
      (WeakLimitCompensatedProducts.value M (CanonicalStateDriverFiltration.coordinate H k)
        (compensator H G hG hβ hβ1 i a n k) t x-
       WeakLimitCompensatedProducts.value M (CanonicalStateDriverFiltration.coordinate H k)
        (compensator H G hG hβ hβ1 i a n k) s x)
      ∂μ.map (CanonicalNativeBrownian.bundle F μ H N (fun t ω => U (t,ω)) hcU))=0 := by
  let r := MatrixFourierInput.input F μ H G hG hβ hβ1 U hU i a n
  let v := RotatedCylindricalCoordinates.constant F μ H (MatrixPredictableHaarRotation.basis k)
  let bundle := CanonicalNativeBrownian.bundle F μ H N (fun t ω => U (t,ω)) hcU
  let D := CanonicalStateDriverFiltration.coordinate (E := Physical (d := d)) H k
  have hUa (t : ℝ≥0) : Measurable[F t] (fun ω => U (t,ω)) :=
    ((show IsStronglyPredictable F (fun t ω => U (t,ω)) from hU).stronglyAdapted t).measurable
  obtain ⟨Y,_,haY,_,_,hrY⟩ := NativeMartingaleVersion.exists_version N MatrixPredictableHaarRotation.basis hnull r
  obtain ⟨Z,_,haZ,_,_,hrZ⟩ := NativeMartingaleVersion.exists_version N MatrixPredictableHaarRotation.basis hnull v
  have hCross := NativeCrossCompensator.martingale
    (FiniteCylindricalIto.terminalIto N.toCoordinates MatrixPredictableHaarRotation.basis)
    (FiniteCylindricalIto.pastLocality N MatrixPredictableHaarRotation.basis) r v Y Z haY haZ hrY hrZ
  have hDriver (q : ℝ≥0) : (D q ∘ bundle) =ᵐ[μ] Z (min q H) := by
    filter_upwards [hrZ (min q H),FiniteCylindricalIto.coordinate_integral N MatrixPredictableHaarRotation.basis
      k (min q H) (min_le_right _ _),FiniteScalarIto.zero_ae N.toCoordinates k] with ω hz hcoord h0
    change N.W k (0+(CanonicalStateDriverFiltration.clock H q).val.toNNReal) ω-N.W k 0 ω=Z (min q H) ω
    rw [CanonicalFourierFluctuation.clock_time H q,zero_add,h0,sub_zero]
    exact hcoord.symm.trans hz.symm
  apply CanonicalLawMartingaleTests.identity μ F H bundle
    (CanonicalNativeBrownian.measurable_bundle F μ H N (fun t ω => U (t,ω)) hcU hUa)
    (CanonicalStateDriverFiltration.history H) (WeakLimitCanonicalBrownian.continuous_history H)
    (CanonicalNativeBrownian.past_adapted_capped F μ H N (fun t ω => U (t,ω)) hcU hUa)
    (WeakLimitCompensatedProducts.value M D (compensator H G hG hβ hβ1 i a n k))
    (fun q => ((CanonicalLinearFluctuation.continuous H (coordinate i a n) ((n : ℝ)^2) q).mul
      (WeakLimitCanonicalBrownian.continuous_coordinate H k q)).sub
        (compensator H G hG hβ hβ1 i a n k q).continuous)
    (fun q ω => Y q ω*Z q ω-NativeCrossCompensator.value r v q ω) hCross
  · intro q
    have hm := CanonicalNativeLinearTests.representation F μ H N MatrixPredictableHaarRotation.basis
      (fun t ω => U (t,ω)) hcU (coordinate i a n) ((n : ℝ)^2) r
      (MatrixFourierPathMoments.random_representation F μ H G hG hβ hβ1 U hU N ξ hRandom i a n) q
    filter_upwards [hm,hrY (min q H),hDriver q,
      MatrixFourierCompensator.mixed_ae F μ H G hG hβ hβ1 U hU i a n (MatrixPredictableHaarRotation.basis k)]
      with ω hm hy hd he
    change M q (bundle ω)*D q (bundle ω)-
      CanonicalFourierCompensator.value H ((n : ℝ)^2) _ _ q (bundle ω)=_
    rw [CanonicalFourierCompensator.comp_bundle,← he (min q H) (min_le_right _ _)]
    change M q (bundle ω)=_ at hm
    change D q (bundle ω)=_ at hd
    rw [hm.trans hy.symm,hd]
  · exact hst


include hEquation in
theorem identity (hcU : ∀ ω,Continuous (fun t => U (t,ω)))
    (hnull : NullCompleteFiltration.ContainsNullSets F μ) (k : d×FiniteHaar.HaarNode)
    (s t : ℝ≥0) (hst : s ≤ t) (ψ : BoundedContinuousFunction X ℝ) :
    (∫ x,ψ (CanonicalStateDriverFiltration.history H s x)*
      (WeakLimitCompensatedProducts.value M (CanonicalStateDriverFiltration.coordinate H k)
        (compensator H G hG hβ hβ1 i a n k) t x-
       WeakLimitCompensatedProducts.value M (CanonicalStateDriverFiltration.coordinate H k)
        (compensator H G hG hβ hβ1 i a n k) s x)
      ∂μ.map (CanonicalNativeBrownian.bundle F μ H N (fun t ω => U (t,ω)) hcU))=0 := by
  exact random_identity F μ H G hG hβ hβ1 U hU N i a n (fun _ => u₀) hEquation hcU hnull k s t hst ψ

end SHEStochastic.MatrixFourierMixedTests
