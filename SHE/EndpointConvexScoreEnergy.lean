module

public import SHE.EndpointHolderScoreEnergy
public import SHE.BoundedResidualFields

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
noncomputable section
namespace SHE.EndpointConvexScoreEnergy
open Set Filter MeasureTheory ProbabilityTheory Real AddCircle StoppedFourier StoppedGaussianFeatures
  ProfileL2 ProfileStability ControlledProfile ControlledResidualScoreInput ControlledOldIntervals
local instance : Fact (0<2*π):=⟨by positivity⟩
variable {W : Type*} [MeasurableSpace W] [MeasurableSpace CircleL2] [BorelSpace CircleL2]

/-- True newest-endpoint finite profile-difference score mass against the convex
endpoint future law, after subtracting the ORIGINAL fixed old fractions.
Both profile fixed points are original endpoints; the intermediate law
is not assumed to solve a fixed point. Original sample/output energy
is retained to beta with no negative quarter-age loss. -/
theorem future_energy (P : CanonicalCovariance.ProfileParameters)
    {Λ : ℝ} (hΛ : 0≤Λ) (u d : W→CircleL2) (hu : Measurable u) (hd : Measurable d)
    (hsmallL2 : memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-1)/4)*P.horizon^(P.exponent/4)≤1/2)
    (μ : Measure W) [IsProbabilityMeasure μ] (hdi : Integrable (fun ω=>‖d ω‖^2) μ)
    (q : ℝ) (hq : 0≤q) (θ η : ℝ) (newCenter : HeatCircle) {ζ : ℝ} (hζ : 0≤ζ) (hζ1 : ζ≤1)
    {r : ℕ} (lo hi : Fin r→ℝ) (hdisjoint : ∀ j k,j≠k→hi j≤lo k ∨ hi k≤lo j)
    (n : ℕ) (σ target : Fin n→ℝ) (center : Fin n→HeatCircle)
    (hσ1 : ∀ i,σ i-q≤1) (hages : ∀ i,σ i≤target i)
    (stop : ℝ) (hstop : q<stop) (hstops : ∀ i,stop≤σ i) :
    let c:=fun z : W×ControlledProfile.Domain=>BoundedWindowDecomposition.residual P Λ (u z.1) (d z.1) lo hi
      (BoundedWindowDecomposition.convexProfile P Λ (u z.1) (d z.1) θ η ζ) z.2
    let e:=fun z : W×ControlledProfile.Domain=>profile P Λ (u z.1) (d z.1) (θ,z.2)-profile P Λ (u z.1) (d z.1) (η,z.2)
    let F:=fun z : W×HeatCircle=>futureInput (Fin.cons q σ) (Fin.cons q target) (Fin.cons newCenter center) (fun p=>c (z.1,p)) (fun p=>e (z.1,p)) q z.2
    let C:=2*P.holder*|θ-η|^P.exponent*(3*((n:ℝ)/(P.lower/2)))
    Integrable (fun z=>|F z|^2) (μ.prod haarAddCircle) ∧
      (∫ z,|F z|^2 ∂μ.prod haarAddCircle)≤C^2*(∫ ω,‖d ω‖^2 ∂μ)^P.exponent := by
  intro c e F C
  have hcf:=BoundedResidualFields.convexProfile_measurable P Λ θ η ζ u d hu hd
  have ho:=VaryingControlledGaussianFields.fixed_profile_measurable P Λ u d hu hd lo hi
  have hc : Measurable c:=by convert! hcf.sub ho using 1
  have hb (z : W×ControlledProfile.Domain) : P.lower/2≤c z ∧ c z≤P.upper:=
    BoundedWindowDecomposition.residual_bounds P Λ (u z.1) (d z.1) lo hi hdisjoint _
      (BoundedWindowDecomposition.convexProfile_bounds P Λ (u z.1) (d z.1) θ η hζ hζ1) z.2
  have hh:=EndpointHolderScoreEnergy.future_energy P hΛ u d hu hd hsmallL2 μ hdi q hq θ η newCenter n
    σ target center hσ1 hages stop hstop hstops (P.lower/2) (half_pos P.lower_pos) c hc P.upper
    (fun z=>⟨(half_pos P.lower_pos).le.trans (hb z).1,(hb z).2⟩) (fun z=>(hb z).1)
  exact hh

end SHE.EndpointConvexScoreEnergy
