module

public import SHE.VaryingAssignedFields
public import SHE.VaryingFullResidualMoments
public import SHE.ControlledProfileFamilies
public import SHE.StoppedGaussianFields

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2200000
noncomputable section

namespace SHE.VaryingControlledGaussianFields
open Set MeasureTheory ProbabilityTheory StoppedFourier StoppedGaussianFeatures ControlledOldIntervals
  OldIntervalCovariance GaussianIncrement FullResidualAssignedMoments
open scoped BigOperators
local instance varyingControlledGaussianFields_periodPositive : Fact (0<2*Real.pi) := ⟨by positivity⟩
variable {Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace CircleL2] [BorelSpace CircleL2]
variable {n d r m : ℕ}

/-- The actual controlled profile is jointly measurable after arbitrary
measurable initial-data substitution, in relative native time. -/
theorem profile_measurable (P : CanonicalCovariance.ProfileParameters) (Λ θ : ℝ)
    (u d0 : Ω→CircleL2) (hu : Measurable u) (hd : Measurable d0) :
    Measurable (fun z : Ω×Domain=>ControlledProfile.profile P Λ (u z.1) (d0 z.1) (θ,z.2)) := by
  convert! (ControlledProfile.random_profile_measurable P hu hd Λ).comp
    ((measurable_fst.prodMk measurable_const).prodMk measurable_snd) using 1

def family (σ target : Fin n→ℝ) (center : Fin n→HeatCircle) : VariableObservations.Family Ω n where
  observations := fun _ i=>⟨σ i,target i,center i⟩
  stop_measurable := fun _=>measurable_const
  target_measurable := fun _=>measurable_const
  center_measurable := fun _=>measurable_const

theorem reference_measurable (P : CanonicalCovariance.ProfileParameters) (Λ : ℝ)
    (u d0 : Ω→CircleL2) (hu : Measurable u) (hd : Measurable d0) :
    Measurable (fun z : Ω×Domain=>referenceProfile P Λ (u z.1) (d0 z.1) z.2) := by
  exact (profile_measurable P Λ 0 u d0 hu hd).const_mul (fraction P)

theorem interval_measurable (P : CanonicalCovariance.ProfileParameters) (Λ : ℝ)
    (u d0 : Ω→CircleL2) (hu : Measurable u) (hd : Measurable d0) (lo hi : ℝ) :
    Measurable (fun z : Ω×Domain=>intervalProfile (referenceProfile P Λ (u z.1) (d0 z.1)) lo hi z.2) := by
  have hset : MeasurableSet {z : Ω×Domain | z.2∈timeSet lo hi} :=
    (measurableSet_Ioc.prod MeasurableSet.univ).preimage measurable_snd
  convert! ((reference_measurable P Λ u d0 hu hd).ite hset (measurable_const (a:=(0:ℝ)))) using 1

theorem old_covariance_measurable (P : CanonicalCovariance.ProfileParameters) (Λ : ℝ)
    (u d0 : Ω→CircleL2) (hu : Measurable u) (hd : Measurable d0)
    (σ target : Fin n→ℝ) (center : Fin n→HeatCircle) (lo hi : Fin r→ℝ) (j : Fin r) :
    Measurable (fun ω=>familyCovariance σ target center (referenceProfile P Λ (u ω) (d0 ω)) lo hi j) := by
  convert! StoppedGaussianFields.covariance_measurable (family (Ω:=Ω) σ target center)
    (interval_measurable P Λ u d0 hu hd (lo j) (hi j)) (measurable_const (a:=(0:ℝ))) using 1

theorem fixed_profile_measurable (P : CanonicalCovariance.ProfileParameters) (Λ : ℝ)
    (u d0 : Ω→CircleL2) (hu : Measurable u) (hd : Measurable d0) (lo hi : Fin r→ℝ) :
    Measurable (fun z : Ω×Domain=>fixedProfile P Λ (u z.1) (d0 z.1) lo hi z.2) :=
  Finset.measurable_sum Finset.univ (fun j _=>interval_measurable P Λ u d0 hu hd (lo j) (hi j))

theorem residual_covariance_measurable (P : CanonicalCovariance.ProfileParameters) (Λ θ q : ℝ)
    (u d0 : Ω→CircleL2) (hu : Measurable u) (hd : Measurable d0)
    (σ target : Fin n→ℝ) (center : Fin n→HeatCircle) (lo hi : Fin r→ℝ) :
    Measurable (fun ω=>ControlledFixedReserve.covariance P Λ (u ω) (d0 ω)
      (fixedProfile P Λ (u ω) (d0 ω) lo hi) σ target center q θ) := by
  convert! StoppedGaussianFields.covariance_measurable (family (Ω:=Ω) σ target center)
    ((profile_measurable P Λ θ u d0 hu hd).sub (fixed_profile_measurable P Λ u d0 hu hd lo hi))
    (measurable_const (a:=q)) using 1

/-- Borel dependence of the ACTUAL variable-data Gaussian assigned
average. All covariance fields and full-profile baselines are derived
from the canonical profile, rather than supplied as unexplained inputs. -/
theorem fibreAverage_measurable (P : CanonicalCovariance.ProfileParameters) (Λ θ q : ℝ)
    (u d0 : Ω→CircleL2) (hu : Measurable u) (hd : Measurable d0)
    (σ target : Fin n→ℝ) (center : Fin n→HeatCircle) (lo hi : Fin r→ℝ)
    (mean : Ω→State n) (hm : Measurable mean) (second : Bool)
    (D : Ω→Fin r→State n) (hD : ∀ j,Measurable (fun ω=>D ω j))
    (E : Ω→State n) (hE : Measurable E)
    (g : Fin d→Fin n) (leaf : Fin m→Fin n) (choices : List (Fin r×Fin (m+1)))
    (F : State d→ℝ) (hF : Measurable F) :
    Measurable (fun ω=>fibreAverage P Λ (u ω) (d0 ω) θ q σ target center lo hi (mean ω)
      second (D ω) (E ω) g leaf choices F) := by
  have hbase (j : Fin m) : Measurable (fun ω=>ControlledProfile.profile P Λ (u ω) (d0 ω)
      (θ,(target (leaf j),center (leaf j)))) := by
    convert! (profile_measurable P Λ θ u d0 hu hd).comp
      (measurable_id.prodMk (measurable_const (a:=(target (leaf j),center (leaf j))))) using 1
  exact VaryingAssignedFields.average_measurable _
    (fun j=>old_covariance_measurable P Λ u d0 hu hd σ target center lo hi j) D hD _
    (residual_covariance_measurable P Λ θ q u d0 hu hd σ target center lo hi) E hE second choices
    P.coefficient P.measurable F hF mean hm g leaf _ hbase

end SHE.VaryingControlledGaussianFields
