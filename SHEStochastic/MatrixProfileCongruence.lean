module

public import SHEStochastic.MatrixHaarHigherFamily
public import SHEStochastic.MatrixKernelVersion

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section

namespace SHEStochastic.MatrixProfileCongruence
open MeasureTheory SHE SHE.PredictableL2 SHE.FiniteHaar MatrixInfiniteHaar MatrixHeatKernelModel
open scoped NNReal ENNReal Matrix.Norms.L2Operator
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
variable {d : Type*} [Fintype d] [DecidableEq d]

theorem realize_eq (P Q : Profile d)
    (h : P.value =ᵐ[AddCircle.haarAddCircle (T := (1 : ℝ))] Q.value) :
    MatrixProfileSymmetry.realize d P=MatrixProfileSymmetry.realize d Q := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [MatrixProfileHilbert.realize_ae d P,MatrixProfileHilbert.realize_ae d Q,h] with x hp hq hx
  change MatrixProfileHilbert.realize d P x=MatrixProfileHilbert.realize d Q x
  rw [hp,hq,hx]

/-- The literal matrix Haar kernel depends only on the almost-everywhere
spatial covariance. Its arbitrary bounds and measurable representatives
do not affect the actual columns. -/
theorem kernel_eq (P Q : Profile d)
    (h : P.value =ᵐ[AddCircle.haarAddCircle (T := (1 : ℝ))] Q.value) (τ : ℝ) :
    MatrixAnalyticKernel.kernel τ P=MatrixAnalyticKernel.kernel τ Q := by
  have he := realize_eq P Q h
  have hk (k : d × HaarNode) : factor P (lp.single 2 k 1)=factor Q (lp.single 2 k 1) := by
    rw [← MatrixHaarHigherFamily.column_realize P k.1 k.2,
      ← MatrixHaarHigherFamily.column_realize Q k.1 k.2,he]
  apply lp.ext
  funext k
  simp only [MatrixAnalyticKernel.column,hk]

variable {X : Type*} [MeasurableSpace X]
local instance : SecondCountableTopology (Physical (d := d)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (Physical (d := d)) := borel _
local instance : BorelSpace (Physical (d := d)) := ⟨rfl⟩

theorem nonlinear_value_ae (G : MatrixNonlinearCoefficient.Coefficient d)
    (u v : X → Physical (d := d)) (hu : StronglyMeasurable u) (hv : StronglyMeasurable v)
    (p : X) (hp : u p=v p) :
    (MatrixNemytskii.profile G u hu p).value =ᵐ[AddCircle.haarAddCircle (T := (1 : ℝ))]
      (MatrixNemytskii.profile G v hv p).value := by
  filter_upwards [MatrixNemytskii.state_ae u hu p,MatrixNemytskii.state_ae v hv p] with x hx hy
  change G.covariance (MatrixNemytskii.state u hu (p,x))=G.covariance (MatrixNemytskii.state v hv (p,x))
  rw [hx,hy,hp]

variable {Ω : Type*} [MeasurableSpace Ω] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {H : ℝ≥0} {U : ℝ}
local instance : MeasurableSpace (MatrixHaarKernel.Columns (d := d)) := borel _
local instance : BorelSpace (MatrixHaarKernel.Columns (d := d)) := ⟨rfl⟩

/-- Native heat inputs are invariant under an actual product-a.e.
change of the spatial covariance profile. -/
theorem input_eq (hH : (H : ℝ) ≤ 1) (hU : 0 ≤ U) (a b : Fields (d := d) F U)
    (hab : ∀ᵐ p ∂energyMeasure μ H, (a.value p).value =ᵐ[AddCircle.haarAddCircle (T := (1 : ℝ))] (b.value p).value)
    (t : ℝ≥0) (ht : t ≤ H) :
    MatrixAnalyticConvolution.input F μ H hH U hU a.value a.upper a.measurable t ht=
      MatrixAnalyticConvolution.input F μ H hH U hU b.value b.upper b.measurable t ht := by
  apply Lp.ext
  apply ae_eq_trim_of_measurable (predictable_le_product F)
    (Lp.stronglyMeasurable _).measurable (Lp.stronglyMeasurable _).measurable
  filter_upwards [MatrixAnalyticConvolution.input_ae F μ H hH U hU a.value a.upper a.measurable t ht,
    MatrixAnalyticConvolution.input_ae F μ H hH U hU b.value b.upper b.measurable t ht,hab] with p ha hb hp
  rw [ha,hb]
  exact kernel_eq _ _ hp _

end SHEStochastic.MatrixProfileCongruence
