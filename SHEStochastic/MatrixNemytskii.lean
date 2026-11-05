module

public import SHEStochastic.MatrixNonlinearCoefficient
public import SHEStochastic.FamilyLpRepresentative

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section

namespace SHEStochastic.MatrixNemytskii
open MeasureTheory MatrixNonlinearCoefficient MatrixInfiniteHaar
open scoped NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
variable {d X : Type*} [Fintype d] [DecidableEq d] [MeasurableSpace X]
local instance : SecondCountableTopology (Physical (d := d)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (Physical (d := d)) := borel _
local instance : BorelSpace (Physical (d := d)) := ⟨rfl⟩
variable (G : Coefficient d) (U : X → Physical (d := d)) (hU : StronglyMeasurable U)

def state : X × AddCircle (1 : ℝ) → EuclideanSpace ℝ d :=
  FamilyLpRepresentative.representative (AddCircle.haarAddCircle (T := (1 : ℝ))) U hU

theorem state_measurable : Measurable (state U hU) :=
  FamilyLpRepresentative.representative_measurable _ U hU

theorem state_ae (p : X) :
    (fun x => state U hU (p,x)) =ᵐ[AddCircle.haarAddCircle (T := (1 : ℝ))] U p :=
  FamilyLpRepresentative.representative_ae _ U hU p

/-- A predictable L2 vector state gives the literal matrix coefficient
G(U) and its covariance using a proved joint measurable representative. -/
def profile (p : X) : Profile d := G.family (state U hU) (state_measurable U hU) p

def data (p : X) : MatrixSquareCoefficient.Data (profile G U hU p) :=
  G.dataFamily (state U hU) (state_measurable U hU) p

theorem covariance_measurable : Measurable (fun p : X × AddCircle (1 : ℝ) => (profile G U hU p.1).value p.2) :=
  G.family_measurable _ (state_measurable U hU)

theorem coefficient_measurable : Measurable (fun p : X × AddCircle (1 : ℝ) => (data G U hU p.1).value p.2) :=
  G.dataFamily_measurable _ (state_measurable U hU)

theorem coefficient_ae (p : X) :
    (data G U hU p).value =ᵐ[AddCircle.haarAddCircle (T := (1 : ℝ))] fun x => G.value (U p x) :=
  (state_ae U hU p).mono fun x hx => congrArg G.value hx

end SHEStochastic.MatrixNemytskii
