module

public import SHE.BoundedResidualVarying
public import SHE.VaryingControlledGaussianFields

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2300000
noncomputable section
namespace SHE.BoundedResidualFields
open Set MeasureTheory ProbabilityTheory StoppedFourier StoppedGaussianFeatures ControlledOldIntervals
  OldIntervalCovariance GaussianIncrement BoundedResidualAssignedMoments VaryingControlledGaussianFields
open scoped BigOperators
local instance : Fact (0<2*Real.pi):=⟨by positivity⟩
variable {Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace CircleL2] [BorelSpace CircleL2]
variable {n r m : ℕ}

theorem residual_covariance_measurable (P : CanonicalCovariance.ProfileParameters) (Λ q : ℝ)
    (u d0 : Ω→CircleL2) (hu : Measurable u) (hd : Measurable d0)
    (c : Ω×Domain→ℝ) (hc : Measurable c)
    (σ target : Fin n→ℝ) (center : Fin n→HeatCircle) (lo hi : Fin r→ℝ) :
    Measurable (fun ω=>stoppedCovariance σ target center
      (BoundedWindowDecomposition.residual P Λ (u ω) (d0 ω) lo hi (fun p=>c (ω,p))) q) := by
  convert! StoppedGaussianFields.covariance_measurable (family (Ω:=Ω) σ target center)
    (hc.sub (fixed_profile_measurable P Λ u d0 hu hd lo hi)) (measurable_const (a:=q)) using 1

theorem fibreAverage_measurable (P : CanonicalCovariance.ProfileParameters) (Λ η q : ℝ)
    (u d0 : Ω→CircleL2) (hu : Measurable u) (hd : Measurable d0)
    (c : Ω×Domain→ℝ) (hc : Measurable c)
    (σ target : Fin n→ℝ) (center : Fin n→HeatCircle) (lo hi : Fin r→ℝ)
    (mean : Ω→State n) (hm : Measurable mean) (second : Bool)
    (D : Ω→Fin r→State n) (hD : ∀ j,Measurable (fun ω=>D ω j))
    (E : Ω→State n) (hE : Measurable E)
    (g : Fin 1→Fin n) (leaf : Fin m→Fin n) (choices : List (Fin r×Fin (m+1)))
    (F : State 1→ℝ) (hF : Measurable F) :
    Measurable (fun ω=>fibreAverage P Λ (u ω) (d0 ω) (fun p=>c (ω,p)) η q
      σ target center lo hi (mean ω) second (D ω) (E ω) g leaf choices F) := by
  have hbase (j : Fin m) : Measurable (fun ω=>ControlledProfile.profile P Λ (u ω) (d0 ω)
      (η,(target (leaf j),center (leaf j)))) := by
    convert! (profile_measurable P Λ η u d0 hu hd).comp
      (measurable_id.prodMk (measurable_const (a:=(target (leaf j),center (leaf j))))) using 1
  have hh:=VaryingAssignedFields.average_measurable _
    (fun j=>old_covariance_measurable P Λ u d0 hu hd σ target center lo hi j) D hD _
    (residual_covariance_measurable P Λ q u d0 hu hd c hc σ target center lo hi) E hE second choices
    P.coefficient P.measurable F hF mean hm g leaf _ hbase
  simpa only [fibreAverage,BoundedResidualAssignedMoments.word,FullResidualAssignedMoments.word] using hh

theorem convexProfile_measurable (P : CanonicalCovariance.ProfileParameters) (Λ θ η ζ : ℝ)
    (u d0 : Ω→CircleL2) (hu : Measurable u) (hd : Measurable d0) :
    Measurable (fun z : Ω×Domain=>BoundedWindowDecomposition.convexProfile P Λ (u z.1) (d0 z.1) θ η ζ z.2) :=
  ((profile_measurable P Λ θ u d0 hu hd).const_mul (1-ζ)).add
    ((profile_measurable P Λ η u d0 hu hd).const_mul ζ)

end SHE.BoundedResidualFields
