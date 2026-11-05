module

public import SHEStochastic.MatrixGlobalHaarComplete
public import SHEStochastic.MatrixFieldAdjoint
public import SHEStochastic.WeightedBasisFactor

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section

namespace SHEStochastic.MatrixInfiniteHaar
open MeasureTheory SHE SHE.FiniteHaar
open scoped NNReal MatrixOrder Matrix.Norms.L2Operator

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
variable {d : Type*} [Fintype d] [DecidableEq d]
local notation "μ" => AddCircle.haarAddCircle (T := (1 : ℝ))

/-- A bounded uniformly elliptic matrix covariance profile on the
actual spatial circle. No basis/completeness/covariance assumption is
part of these data. -/
structure Profile (d : Type*) [Fintype d] [DecidableEq d] where
  value : AddCircle (1 : ℝ) → Matrix d d ℝ
  measurable : Measurable value
  bound : ℝ≥0
  norm_bound : ∀ᵐ x ∂μ, ‖value x‖ ≤ bound
  lower : ℝ
  lower_pos : 0 < lower
  lower_bound : ∀ᵐ x ∂μ, lower • (1 : Matrix d d ℝ) ≤ value x
  upper : ℝ
  upper_pos : 0 < upper
  upper_bound : ∀ᵐ x ∂μ, value x ≤ upper • (1 : Matrix d d ℝ)

abbrev Physical := Lp (EuclideanSpace ℝ d) 2 μ
abbrev Input := lp (fun _ : d × HaarNode => ℝ) 2

theorem Profile.integrable (P : Profile d) : Integrable P.value μ :=
  Integrable.of_bound P.measurable.aestronglyMeasurable P.bound P.norm_bound

def multiplier (P : Profile d) : Physical (d := d) →L[ℝ] Physical (d := d) :=
  MatrixFieldOperator.operator P.value P.measurable P.bound P.norm_bound

def column (P : Profile d) (k : d × HaarNode) : Physical (d := d) :=
  MatrixGlobalHaar.column P.value k.2 k.1

theorem gram (P : Profile d) (k l : d × HaarNode) :
    inner ℝ (column P k) (multiplier P (column P l))=if k=l then 1 else 0 :=
  MatrixGlobalHaarGram.weighted_gram P.value P.measurable P.integrable P.bound P.norm_bound
    P.lower P.lower_pos P.lower_bound k.2 l.2 k.1 l.1

theorem coercive (P : Profile d) (u : Physical (d := d)) :
    P.lower*‖u‖^2 ≤ inner ℝ u (multiplier P u) :=
  MatrixFieldQuadratic.operator_lower P.value P.measurable P.bound P.norm_bound
    P.lower P.lower_bound u

theorem bounded (P : Profile d) (u : Physical (d := d)) :
    inner ℝ u (multiplier P u) ≤ P.upper*‖u‖^2 :=
  MatrixFieldQuadratic.operator_upper P.value P.measurable P.bound P.norm_bound
    P.upper P.upper_bound u

/-- The actual bounded infinite synthesis of the covariance-adapted
weighted Haar columns, constructed from their finite energy estimates. -/
def synthesis (P : Profile d) : Input (d := d) →L[ℝ] Physical (d := d) :=
  WeightedRieszSynthesis.synthesis (column P) (multiplier P) (gram P)
    P.lower P.lower_pos (coercive P)

theorem synthesis_single (P : Profile d) (k : d × HaarNode) :
    synthesis P (lp.single 2 k 1)=column P k :=
  WeightedRieszSynthesis.synthesis_single (column P) (multiplier P) (gram P)
    P.lower P.lower_pos (coercive P) k

theorem synthesis_bijective (P : Profile d) : Function.Bijective (synthesis P) :=
  WeightedRieszSynthesis.bijective (column P) (multiplier P) (gram P)
    P.lower P.lower_pos (coercive P) P.upper P.upper_pos (bounded P)
    (MatrixGlobalHaarComplete.dense P.value P.integrable P.lower P.lower_pos P.lower_bound)

theorem weighted_identity (P : Profile d) :
    (synthesis P).adjoint.comp ((multiplier P).comp (synthesis P))=
      ContinuousLinearMap.id ℝ (Input (d := d)) :=
  WeightedRieszSynthesis.weighted_identity (column P) (multiplier P) (gram P)
    P.lower P.lower_pos (coercive P)

theorem multiplier_selfadjoint (P : Profile d) : (multiplier P).adjoint=multiplier P :=
  MatrixFieldAdjoint.selfadjoint_of_elliptic P.value P.measurable P.bound P.norm_bound
    P.lower P.lower_pos P.lower_bound

/-- The physical factor has precisely the manuscript's actual ordered
columns `κH`, indexed by all dyadic nodes and vector components. -/
def factor (P : Profile d) : Input (d := d) →L[ℝ] Physical (d := d) :=
  (multiplier P).comp (synthesis P)

theorem factor_single (P : Profile d) (k : d × HaarNode) :
    factor P (lp.single 2 k 1)=MatrixGlobalHaar.physicalColumn P.value
      P.measurable P.bound P.norm_bound k.2 k.1 := by
  change multiplier P (synthesis P (lp.single 2 k 1))=_
  rw [synthesis_single]
  rfl

/-- Genuine invertibility of the countable physical matrix Haar
factor, with the actual weighted Haar analysis as its inverse. -/
def equivalence (P : Profile d) : Input (d := d) ≃L[ℝ] Physical (d := d) :=
  WeightedBasisFactor.equivalence (synthesis P) (multiplier P) (weighted_identity P)
    (synthesis_bijective P).2 (multiplier_selfadjoint P)

theorem equivalence_apply (P : Profile d) (z : Input (d := d)) : equivalence P z=factor P z := rfl

/-- Full infinite matrix Haar covariance in the actual vector `L²`
space, obtained from the proved completeness and weighted Gram identity. -/
theorem covariance (P : Profile d) : (factor P).comp (factor P).adjoint=multiplier P :=
  WeightedBasisFactor.covariance (synthesis P) (multiplier P) (weighted_identity P)
    (synthesis_bijective P).2 (multiplier_selfadjoint P)

end SHEStochastic.MatrixInfiniteHaar
