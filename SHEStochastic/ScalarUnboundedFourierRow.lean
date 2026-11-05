module

public import SHEStochastic.ScalarUnboundedOneDimensional
public import SHEStochastic.NativeNoiseEquivalence

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.ScalarUnboundedFourierRow
open MeasureTheory SHE SHE.DyadicApproximation MatrixInfiniteHaar AddCircle
open scoped NNReal ENNReal Matrix.Norms.L2Operator

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩

local notation "ν" => haarAddCircle (T := (1 : ℝ))
local notation "ν₂" => haarAddCircle (T := 2*Real.pi)
local notation "Vec" => Physical (d := Fin 1)
local notation "comp₀" => VectorHeatObservation.component (0 : Fin 1)

/-- A one-component L² vector and its scalar component have the same norm. -/
def componentEquiv : Vec ≃ₗᵢ[ℝ] RealL2 :=
  LinearIsometryEquiv.ofSurjective
    { toLinearMap := (comp₀).toLinearMap
      norm_map' := fun u => by
        change ‖VectorHeat.coordinates u 0‖ = ‖u‖
        have h : ‖u‖^2 = ‖VectorHeat.coordinates u 0‖^2 := by
          rw [←(VectorHeat.coordinates (d := Fin 1)).norm_map u,
            PiLp.norm_sq_eq_of_L2,Fin.sum_univ_one]
        nlinarith [norm_nonneg u,norm_nonneg (VectorHeat.coordinates u 0)] }
    (fun u => ⟨ScalarUnboundedOneDimensional.initial u,ScalarUnboundedOneDimensional.initial_component u⟩)

theorem componentEquiv_apply (u : Vec) : componentEquiv u = comp₀ u := rfl

/-- This change of basis keeps the original Brownian coordinates. -/
def noiseEquiv : Lp ℝ 2 ν₂ ≃ₗᵢ[ℝ] Input (d := Fin 1) :=
  NativePhysicalState.equivalence.symm.trans (componentEquiv.symm.trans VectorWhiteCoordinates.analysis)

private theorem scalar_row (g : ℝ → ℝ) (z : EuclideanSpace ℝ (Fin 1)) :
    MatrixDiffusionRows.row 0 (ScalarUnboundedOneDimensional.coefficient g z) 0 = g (z 0) := by
  let e := EuclideanSpace.single (0 : Fin 1) (1 : ℝ)
  let A := ScalarUnboundedOneDimensional.coefficient g z
  have h (v : EuclideanSpace ℝ (Fin 1)) : inner ℝ e v = v 0 := by
    simp [e,PiLp.inner_apply]
  have hA : (Matrix.toEuclideanCLM (n := Fin 1) (𝕜 := ℝ) A e) 0 = g (z 0) := by
    change (A.mulVec (WithLp.ofLp e)) 0 = g (z 0)
    simp [A,e,ScalarUnboundedOneDimensional.coefficient,Matrix.mulVec,dotProduct]
  calc
    _ = inner ℝ e ((Matrix.toEuclideanCLM (n := Fin 1) (𝕜 := ℝ) A).adjoint e) := (h _).symm
    _ = inner ℝ (Matrix.toEuclideanCLM (n := Fin 1) (𝕜 := ℝ) A e) e := ContinuousLinearMap.adjoint_inner_right _ _ _
    _ = g (z 0) := by rw [real_inner_comm,h,hA]

private theorem weight_scale (a : ℂ →L[ℝ] ℝ) (n : ℤ) (x : AddCircle (2*Real.pi)) :
    MatrixFourierCoordinates.weight a n (CircleNormalization.scale (2*Real.pi) 1 x) =
      NativeFourierHeatCoordinate.weight a n x := by
  change a (fourier (-n) (CircleNormalization.scale (2*Real.pi) 1 x)) =
    1 * a (fourier (-n) x)
  rw [CircleNormalization.fourier_scale,one_mul]

/-- The exact scalar noise row is the one-component matrix row, with
the same spatial Haar normalization and signed amplitude. -/
theorem row {g : ℝ → ℝ} {C β : ℝ≥0} (hg : HolderWith C β g) (hβ : 0<β) (hβ₁ : β≤1)
    (u : Vec) (a : ℂ →L[ℝ] ℝ) (n : ℤ) :
    noiseEquiv (StateNoiseCovariance.row ν₂ hβ hβ₁ hg
      (NativeFourierHeatCoordinate.weight a n) (NativePhysicalState.push (comp₀ u))) =
    VectorWhiteCoordinates.analysis (StateNoiseCovariance.row ν hβ hβ₁
      (MatrixDiffusionRows.holder (ScalarUnboundedOneDimensional.holder hg) (0 : Fin 1))
      (MatrixFourierCoordinates.weight a n) u) := by
  let v := StateNoiseCovariance.row ν hβ hβ₁
    (MatrixDiffusionRows.holder (ScalarUnboundedOneDimensional.holder hg) (0 : Fin 1))
    (MatrixFourierCoordinates.weight a n) u
  change VectorWhiteCoordinates.analysis (componentEquiv.symm
    (NativePhysicalState.equivalence.symm _)) = VectorWhiteCoordinates.analysis v
  apply congrArg (VectorWhiteCoordinates.analysis (d := Fin 1))
  apply componentEquiv.injective
  rw [LinearIsometryEquiv.apply_symm_apply]
  apply NativePhysicalState.equivalence.injective
  rw [LinearIsometryEquiv.apply_symm_apply]
  change _ = NativePhysicalState.push (comp₀ v)
  apply Lp.ext
  let s := CircleNormalization.scale (2*Real.pi) 1
  have hs := (CircleNormalization.scale_measurePreserving (2*Real.pi) 1).quasiMeasurePreserving
  have hv : ∀ᵐ x ∂ν, comp₀ v x = v x 0 := (L2EuclideanCoordinates.coordinates_ae ν v).mono fun x h => h 0
  have hu : ∀ᵐ x ∂ν, comp₀ u x = u x 0 := (L2EuclideanCoordinates.coordinates_ae ν u).mono fun x h => h 0
  have hrow := StateNoiseCovariance.row_ae ν hβ hβ₁
    (MatrixDiffusionRows.holder (ScalarUnboundedOneDimensional.holder hg) (0 : Fin 1))
    (MatrixFourierCoordinates.weight a n) u
  filter_upwards [StateNoiseCovariance.row_ae ν₂ hβ hβ₁ hg
    (NativeFourierHeatCoordinate.weight a n) (NativePhysicalState.push (comp₀ u)),
    NativePhysicalState.push_ae (comp₀ v),NativePhysicalState.push_ae (comp₀ u),
    hs.ae hv,hs.ae hu,hs.ae hrow] with x hl hr hstate hv hu hrow
  rw [hl,hr,hstate,hu,hv]
  change _ = v (s x) 0
  change v (s x) = _ at hrow
  rw [hrow]
  change NativeFourierHeatCoordinate.weight a n x * g (u (s x) 0) =
    MatrixFourierCoordinates.weight a n (s x) *
      MatrixDiffusionRows.row 0 (ScalarUnboundedOneDimensional.coefficient g (u (s x))) 0
  rw [weight_scale,scalar_row]

end SHEStochastic.ScalarUnboundedFourierRow
