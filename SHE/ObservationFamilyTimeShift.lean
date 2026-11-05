module

public import SHE.ControlledProfileTimeShift
public import SHE.StoppedGaussianFields
public import SHE.VariableObservations

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHE.ObservationFamilyTimeShift
open Set MeasureTheory ProbabilityTheory AddCircle WordRecursion StoppedFourier
  StoppedGaussianFeatures OldIntervalCovariance ObservationTimeShift
open scoped Topology BigOperators
local instance observationFamilyTimeShift_period : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
variable {P : Type*} [MeasurableSpace P] {n : ℕ}

/-- A jointly Borel observation family translated to absolute time. -/
def family (v : ℝ) (Z : VariableObservations.Family P n) : VariableObservations.Family P n where
  observations p:=ObservationTimeShift.observations v (Z.observations p)
  stop_measurable i:=(Z.stop_measurable i).add_const v
  target_measurable i:=(Z.target_measurable i).add_const v
  center_measurable i:=Z.center_measurable i

/-- A genuinely varying profile, translated without changing its
parameter dependence. -/
def coefficient (v : ℝ) (c : P×Domain→ℝ) : P×Domain→ℝ :=
  fun p=>ObservationTimeShift.profile v (fun z=>c (p.1,z)) p.2

theorem coefficient_measurable (v : ℝ) {c : P×Domain→ℝ} (hc : Measurable c) :
    Measurable (coefficient v c) := hc.comp (measurable_fst.prodMk
      ((measurable_snd.fst.sub_const v).prodMk measurable_snd.snd))

theorem row_translation (v : ℝ) (Z : VariableObservations.Family P n) (p : P) (r : Domain) :
    StoppedGaussianFields.row (family v Z) p (translation v r)=StoppedGaussianFields.row Z p r :=
  stoppedRow_translation v _ _ _ r

/-- Exact full individually stopped covariance identity for arbitrary
jointly varying observations, profiles and lower cutoffs. -/
theorem covariance_translation (v : ℝ) (Z : VariableObservations.Family P n)
    (c : P×Domain→ℝ) (q : P→ℝ) (p : P) :
    StoppedGaussianFields.covariance (family v Z) (coefficient v c) (fun p=>q p+v) p=
      StoppedGaussianFields.covariance Z c q p := by
  exact ObservationTimeShift.stoppedCovariance_translation v (q p)
    (fun i=>(Z.observations p i).stop) (fun i=>(Z.observations p i).target)
    (fun i=>(Z.observations p i).center) (fun r=>c (p,r))

theorem dampedDirection_translation (v : ℝ) (Z : VariableObservations.Family P n)
    (u Λ : P→ℝ) (p : P) (x : HeatCircle) :
    StoppedGaussianFields.dampedDirection (family v Z) (fun p=>u p+v) Λ p x=
      StoppedGaussianFields.dampedDirection Z u Λ p x := by
  unfold StoppedGaussianFields.dampedDirection
  congr 1
  funext i
  change Real.exp (-Λ p*(((Z.observations p i).stop+v)-(u p+v)))*
      StoppedGaussianFields.row (family v Z) p (translation v (u p,x)) i=_
  rw [add_sub_add_right_eq_sub,row_translation]

theorem defectDirection_translation (v : ℝ) (Z : VariableObservations.Family P n)
    (u Λ : P→ℝ) (p : P) (x : HeatCircle) :
    StoppedGaussianFields.defectDirection (family v Z) (fun p=>u p+v) Λ p x=
      StoppedGaussianFields.defectDirection Z u Λ p x := by
  unfold StoppedGaussianFields.defectDirection
  congr 1
  funext i
  change (1-Real.exp (-Λ p*(((Z.observations p i).stop+v)-(u p+v))))*
      StoppedGaussianFields.row (family v Z) p (translation v (u p,x)) i=_
  rw [add_sub_add_right_eq_sub,row_translation]

/-- Relative observations of an already absolute family. -/
def relative (v : ℝ) (Z : VariableObservations.Family P n) : VariableObservations.Family P n :=
  family (-v) Z

theorem family_relative_observations (v : ℝ) (Z : VariableObservations.Family P n) (p : P) :
    (family v (relative v Z)).observations p=Z.observations p := by
  funext i
  cases h : Z.observations p i
  simp only [family,relative,ObservationTimeShift.observations,neg_add_cancel_right]
  congr 1

/-- The relative coefficient recovered from an arbitrary absolute field. -/
def relativeCoefficient (v : ℝ) (c : P×Domain→ℝ) : P×Domain→ℝ :=
  fun p=>c (p.1,translation v p.2)

theorem relativeCoefficient_measurable (v : ℝ) {c : P×Domain→ℝ} (hc : Measurable c) :
    Measurable (relativeCoefficient v c) :=
  hc.comp (measurable_fst.prodMk ((translation v).measurable.comp measurable_snd))

theorem coefficient_relative (v : ℝ) (c : P×Domain→ℝ) :
    coefficient v (relativeCoefficient v c)=c := by
  funext p
  simp only [coefficient,relativeCoefficient,ObservationTimeShift.profile,translation_apply,
    sub_add_cancel,Prod.eta]

/-- Literal arbitrary absolute-family covariance in relative ages. This
form can be applied directly to a canonical carrier history at random
past inputs, without an uncountable AE substitution. -/
theorem absolute_covariance_eq_relative (v : ℝ) (Z : VariableObservations.Family P n)
    (c : P×Domain→ℝ) (q : P→ℝ) (p : P) :
    StoppedGaussianFields.covariance Z c (fun p=>q p+v) p=
      StoppedGaussianFields.covariance (relative v Z) (relativeCoefficient v c) q p := by
  have hh:=covariance_translation v (relative v Z) (relativeCoefficient v c) q p
  rw [coefficient_relative] at hh
  change StoppedGaussianFeatures.stoppedCovariance _ _ _ _ _=_ at hh
  simp only [family_relative_observations] at hh
  exact hh

end SHE.ObservationFamilyTimeShift
