module

public import SHE.NativeJointPhysicalRows
public import SHE.NonlinearTwoChannelStep

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section

namespace SHE.NativeJointBracketDefect
open MeasureTheory GaussianIncrement NativeHeatObservation NativeObservationNaturality
open FiniteHaar StoppedFourier OrthogonalItoChannels DyadicApproximation PredictableL2
open NativeJointPhysicalRows
open scoped NNReal ENNReal
local instance nativeJointBracketDefect_realSigma : MeasurableSpace RealL2 := borel _
local instance nativeJointBracketDefect_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance nativeJointBracketDefect_rowSigma : MeasurableSpace RealHaarInput := borel _
local instance nativeJointBracketDefect_rowBorel : BorelSpace RealHaarInput := ⟨rfl⟩
local instance nativeJointBracketDefect_blockSigma : MeasurableSpace (Both RealHaarInput) := borel _
local instance nativeJointBracketDefect_blockBorel : BorelSpace (Both RealHaarInput) := ⟨rfl⟩
variable {Ω : Type*} [MeasurableSpace Ω]
variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
variable (Λ κ : ℝ) (hκ : 0<κ) {a : ℝ→ℝ} (ha : Measurable a) {ell M : ℝ}
variable (hell : 0<ell) (hb : ∀ z,ell≤a z ∧ a z≤M)
variable (I₀ I₁ : StandardTerminalIto (C := RealHaarIntegrand.Columns) (E := RealL2) 𝓕 μ H)
variable (u₀ v₀ : RealL2)
variable (S : NativeAdditiveResidualPair.Solution 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀)
variable {n : ℕ} (Z : Fin n→WordRecursion.Observation)

def physicalGram (p : ℝ≥0×Ω) : Matrix (Fin n) (Fin n) ℝ := fun i j => inner ℝ
  (physicalRow 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S Z p i)
  (physicalRow 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S Z p j)

def baseGram (p : ℝ≥0×Ω) : Matrix (Fin n) (Fin n) ℝ := fun i j =>
  inner ℝ (additiveRow κ hκ Z p i) (additiveRow κ hκ Z p j)+
    inner ℝ (secondRow 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S Z p i)
      (secondRow 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S Z p j)

def defect (p : ℝ≥0×Ω) : Matrix (Fin n) (Fin n) ℝ :=
  let u := firstRow 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S Z p
  let v := secondRow 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S Z p
  let r := fun i => 1-Real.exp (-Λ*((Z i).stop-(p.1:ℝ)))
  fun i j => r i*inner ℝ (u i-v i) (v j)+r j*inner ℝ (v i) (u j-v j)+
    r i*r j*inner ℝ (u i-v i) (u j-v j)

/-- Exact direct bracket defect of the constructed pair, with its two
cross terms and its quadratic common-Haar difference term. -/
theorem physicalGram_eq_base_add_defect (p : ℝ≥0×Ω) :
    physicalGram 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S Z p=
      baseGram 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S Z p+
        defect 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S Z p := by
  ext i j
  have he := SHE.direct_bracket_defect
    (secondRow 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S Z p i)
    (secondRow 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S Z p j)
    (firstRow 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S Z p i-
      secondRow 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S Z p i)
    (firstRow 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S Z p j-
      secondRow 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S Z p j)
    (1-Real.exp (-Λ*((Z i).stop-(p.1:ℝ)))) (1-Real.exp (-Λ*((Z j).stop-(p.1:ℝ))))
  simp only [physicalGram,physicalRow,WithLp.prod_inner_apply,Matrix.add_apply,baseGram,defect]
  linarith

/-- The local part of the same physical Gram is precisely TOTAL
variance kappa+a(V), with an actual jointly predictable scalar spatial
representative. No residual-only covariance is substituted. -/
theorem baseGram_eq_total_density {δ r : ℝ} (hδ : 0<δ)
    (hgap : ∀ i,δ≤(Z i).target-r) (p : ℝ≥0×Ω) (hpr : (p.1:ℝ)≤r) :
    baseGram 𝓕 μ H Λ κ hκ ha hell hb I₀ I₁ u₀ v₀ S Z p=
      CovarianceMatrix.densityMatrix
        (fun tx => κ+a (PredictableScalarField.wordField (Function.uncurry S.second) p.2 tx)) Z (p.1:ℝ) := by
  have hT (i : Fin n) : (p.1:ℝ)<(Z i).target := by have := hgap i;linarith
  have he := NonlinearTwoChannelStep.density_sum_eq 𝓕 κ hκ hell
    (ContinuousHeatMild.coefficientFunction ha hell hb S.second)
    (Function.uncurry S.second) S.second_predictable a ha hb (fun _ => rfl) Z hδ hgap hpr p.2
  rw [← he]
  ext i j
  have h₀ := NativeObservationCovariance.row_cross_covariance hκ (AdditiveHaarForcing.constantField κ hκ)
    Z (p.1:ℝ) i j (hT i) (hT j)
  have hV := NativeObservationCovariance.row_cross_covariance hell
    (ContinuousHeatMild.coefficientFunction ha hell hb S.second p) Z (p.1:ℝ) i j (hT i) (hT j)
  simp only [baseGram,Matrix.add_apply,additiveRow,secondRow]
  rw [h₀,hV]
  simp only [Matrix.add_apply,CovarianceMatrix.densityMatrix,WordRecursion.covarianceDensity,
    NativeItoBracket.coefficient,Real.toNNReal_coe]

end SHE.NativeJointBracketDefect
