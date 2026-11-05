module

public import SHE.StoppedGaussianSegment
public import SHE.ConvexResidualCovariance

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.ControlledResidualGaussianSegment
open Set MeasureTheory ProbabilityTheory AddCircle StoppedFourier StoppedGaussianFeatures
  GaussianIncrement GaussianConvolution ControlledOldIntervals ControlledProfile
local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
variable {n r : ℕ}

/-- Exact finite comparison of the two actual future Gaussian laws at a
fixed endpoint mean and fixed own-baseline word. Every old profile fraction
stays fixed. The intermediate law is the TRUE convex endpoint law, without
requiring another fixed point or excluding the singular terminal frame. -/
theorem covariance_ftc (P : CanonicalCovariance.ProfileParameters) (Λ : ℝ) (u d : CircleL2)
    (lo hi : Fin r→ℝ) (hdisjoint : ∀ j l,j≠l→hi j≤lo l ∨ hi l≤lo j)
    (σ target : Fin n→ℝ) (center : Fin n→HeatCircle) (hages : ∀ i,σ i≤target i)
    (q θ₀ θ₁ : ℝ) (F : State n→ℝ) (hF : Measurable F) (B : ℝ)
    (hB : ∀ y,|F y|≤B) (mean : State n) :
    let mark:=fun ζ=>FiniteWordScores.covarianceMark (historyMeasure q)
      (stoppedCovariance σ target center (BoundedWindowDecomposition.residual P Λ u d lo hi
        (BoundedWindowDecomposition.convexProfile P Λ u d θ₀ θ₁ ζ)) q)
      (fun p=>profile P Λ u d (θ₁,p)-profile P Λ u d (θ₀,p))
      (stoppedRow σ target center) F mean
    IntervalIntegrable mark volume 0 1 ∧ (∫ ζ in (0:ℝ)..1,mark ζ)=
      gaussianAverage (ControlledFixedReserve.covariance P Λ u d
        (fixedProfile P Λ u d lo hi) σ target center q θ₁) F mean-
      gaussianAverage (ControlledFixedReserve.covariance P Λ u d
        (fixedProfile P Λ u d lo hi) σ target center q θ₀) F mean := by
  intro mark
  let c:=ControlledFixedReserve.coefficient P Λ u d (fixedProfile P Λ u d lo hi)
  have hcm (a) : Measurable (c a) :=
    ((ControlledProfile.profile_measurable P Λ u d).comp
      (measurable_const.prodMk measurable_id)).sub (fixedProfile_measurable P Λ u d lo hi)
  have hcb (a p) : P.lower/2≤c a p ∧ c a p≤P.upper :=
    BoundedWindowDecomposition.residual_bounds P Λ u d lo hi hdisjoint
      (fun p=>profile P Λ u d (a,p)) (fun p=>profile_bounds P Λ u d (a,p)) p
  have he (ζ) : EllipticGaussianSegment.segment (c θ₀) (c θ₁) ζ=
      BoundedWindowDecomposition.residual P Λ u d lo hi
        (BoundedWindowDecomposition.convexProfile P Λ u d θ₀ θ₁ ζ) :=
    (ConvexResidualCovariance.coefficient P Λ u d lo hi θ₀ θ₁ ζ).symm
  have hd : (fun p=>c θ₁ p-c θ₀ p)=
      fun p=>profile P Λ u d (θ₁,p)-profile P Λ u d (θ₀,p) := by
    funext p
    dsimp [c,ControlledFixedReserve.coefficient]
    ring
  have hh:=StoppedGaussianSegment.covariance_ftc σ target center hages q
    (c θ₀) (c θ₁) (hcm θ₀) (hcm θ₁) (half_pos P.lower_pos) (hcb θ₀) (hcb θ₁)
    F hF B hB mean
  simpa only [he,hd,mark,ControlledFixedReserve.covariance,c] using hh

end SHE.ControlledResidualGaussianSegment
