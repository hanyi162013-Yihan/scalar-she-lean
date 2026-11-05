module

public import SHEStochastic.VectorScalarTransform

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHEStochastic.MatrixWeightedOutput
open MeasureTheory SHE SHE.FiniteHaar SHE.DyadicApproximation SHE.CircleHeat SHE.HaarWeightedHeat
open MatrixInfiniteHaar MatrixPhysicalColumnSmooth MatrixProfileEntries
open scoped NNReal ENNReal
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local notation "μ" => AddCircle.haarAddCircle (T := (1 : ℝ))
variable {d : Type*} [Fintype d] [DecidableEq d]

abbrev Output (d : Type*) [Fintype d] := VectorScalarTransform.Output d CircleL2

def map (Λ ρ t : ℝ) (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ) (b : CircleL2) (B : ℝ)
    (hb : ∀ᵐ x ∂μ, ‖b x‖ ≤ B) : Physical (d := d) →L[ℝ] Output d :=
  VectorScalarTransform.map (((weightedHeat Λ ρ t hΛ hρ b B hb).restrictScalars ℝ).comp realEmbed)

theorem norm_sq (Λ ρ t : ℝ) (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ) (b : CircleL2) (B : ℝ)
    (hb : ∀ᵐ x ∂μ, ‖b x‖ ≤ B) (u : Physical (d := d)) :
    ‖map Λ ρ t hΛ hρ b B hb u‖^2 =
      ∑ r : d, ‖weightedHeat Λ ρ t hΛ hρ b B hb (realEmbed (component r u))‖^2 :=
  VectorScalarTransform.norm_sq _ _

theorem jet_norm_sq (Λ ρ t : ℝ) (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ) (b : CircleL2) (B : ℝ)
    (hb : ∀ᵐ x ∂μ, ‖b x‖ ≤ B) (P : Profile d) (w : List (Domain (d := d))) (k : d × HaarNode) :
    ‖map Λ ρ t hΛ hρ b B hb (MatrixHaarHigherFamily.jet P w k)‖^2 =
      MatrixHaarNegativeFamily.packetEnergy Λ ρ t hΛ hρ b B hb P w k := norm_sq _ _ _ _ _ _ _ _ _

end SHEStochastic.MatrixWeightedOutput
