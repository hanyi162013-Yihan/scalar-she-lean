module
public import SHE.RealRootMultiplier
public import SHE.AdditivePhysicalFactor
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace SHE.ScalarHaarSplitting
open MeasureTheory CircleHeat FiniteHaar DyadicApproximation AddCircle
open NoiseSplitting OrthogonalItoChannels AdditivePhysicalFactor
open scoped ENNReal
local instance : Fact (0 < (1:ℝ)) := ⟨zero_lt_one⟩
variable {ell M : ℝ} (hell : 0 < ell) (f : EllipticField ell M)
variable (g : UnitAddCircle → ℝ) (hg : AEStronglyMeasurable g haarAddCircle)
variable (m C : ℝ) (hm : 0 < m)
variable (hgap : ∀ᵐy∂haarAddCircle, m ≤ |g y|)
variable (hbound : ∀ᵐy∂haarAddCircle, |g y| ≤ C)

def rotation : Both RealHaarInput ≃ₗᵢ[ℝ] Both RealL2 :=
  (PairedHilbertIsometry.equivalence
    (whiteCoordinates (m^2) (sq_pos_of_pos hm))
    (fieldRealInnovation ell M hell f).symm).trans
    (physicalRotation haarAddCircle g hg m hm hgap)

/-- The SAME actual two-channel Hilbert isometry converts the original
constant/residual Haar analysis rows to the one-noise physical g-row,
with exactly zero auxiliary row. No covariance-only surrogate is used. -/
theorem analysis
    (hf : ∀ᵐy∂haarAddCircle, (f.1 y).re = (g y)^2-m^2)
    (v : RealL2) :
    rotation hell f g hg m hm hgap
      (WithLp.toLp 2
        (realInputPart (factorAnalysis (AdditiveHaarForcing.constantField (m^2) (sq_pos_of_pos hm)).1
          (m^2) (m^2) (sq_pos_of_pos hm)
          (AdditiveHaarForcing.constantField (m^2) (sq_pos_of_pos hm)).2.1
          (AdditiveHaarForcing.constantField (m^2) (sq_pos_of_pos hm)).2.2 (realEmbed v)),
        realInputPart (factorAnalysis f.1 ell M hell f.2.1 f.2.2 (realEmbed v)))) =
    WithLp.toLp 2 (ScalarSplittingInputs.originalInput haarAddCircle g hg C hbound v,0) := by
  have hA : whiteCoordinates (m^2) (sq_pos_of_pos hm)
      (realInputPart (factorAnalysis (AdditiveHaarForcing.constantField (m^2) (sq_pos_of_pos hm)).1
        (m^2) (m^2) (sq_pos_of_pos hm)
        (AdditiveHaarForcing.constantField (m^2) (sq_pos_of_pos hm)).2.1
        (AdditiveHaarForcing.constantField (m^2) (sq_pos_of_pos hm)).2.2 (realEmbed v))) = m • v := by
    rw [analysis_constant,map_smul,LinearIsometryEquiv.apply_symm_apply,Real.sqrt_sq hm.le]
  have hF := (RealRootMultiplier.decode_analysis hell f v).trans
    (RealRootMultiplier.residual_input hell f g hg m C hbound hf v)
  change physicalRotation haarAddCircle g hg m hm hgap
    (WithLp.toLp 2 (_, _)) = _
  change physicalRotation haarAddCircle g hg m hm hgap
    (WithLp.toLp 2
      (whiteCoordinates (m^2) (sq_pos_of_pos hm)
        (realInputPart (factorAnalysis (AdditiveHaarForcing.constantField (m^2) (sq_pos_of_pos hm)).1
          (m^2) (m^2) (sq_pos_of_pos hm)
          (AdditiveHaarForcing.constantField (m^2) (sq_pos_of_pos hm)).2.1
          (AdditiveHaarForcing.constantField (m^2) (sq_pos_of_pos hm)).2.2 (realEmbed v))),
      (fieldRealInnovation ell M hell f).symm
        (realInputPart (factorAnalysis f.1 ell M hell f.2.1 f.2.2 (realEmbed v))))) = _
  rw [hA,hF]
  exact ScalarSplittingInputs.reconstruct haarAddCircle g hg m C hm hgap hbound v
end SHE.ScalarHaarSplitting
