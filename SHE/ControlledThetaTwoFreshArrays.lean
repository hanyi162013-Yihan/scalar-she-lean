module

public import SHE.PhysicalTwoFreshAssignments
public import SHE.ControlledThetaRelativeArrays
public import SHE.RelativeHistoryGeometry
public import SHE.NativeFirstScoreReserve

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
namespace SHE.ControlledThetaTwoFreshArrays
open Set MeasureTheory ProbabilityTheory StoppedFourier WordRecursion ControlledProfile ControlledReferenceLevel
  CutoffWordLevel CutoffWordHistories SmoothCylinders UniformSmooth CutoffCarriers PhysicalChainArrays
  PhysicalScoreChain ControlledOldIntervals ControlledReferenceWindows ControlledFamilyProfileForest
  ProjectedUncutWord CoveredControlledLaw CoveredHistoryGeometry StoppedGaussianFeatures
open scoped NNReal
local instance controlledThetaTwoFreshArrays_period : Fact (0<2*Real.pi):=⟨by positivity⟩
local instance controlledThetaTwoFreshArrays_circleSigma : MeasurableSpace CircleL2:=borel _
local instance controlledThetaTwoFreshArrays_circleBorel : BorelSpace CircleL2:=⟨rfl⟩

/-- Exact native reserve subtraction without auxiliary positivity or
time-box hypotheses; it is a covariance identity, not a range estimate. -/
theorem covariance_sub_native {N:ℕ} (P:CanonicalCovariance.ProfileParameters) (Λ:ℝ)
    (u d:CircleL2) (old:ControlledProfile.Domain→ℝ) (hm:Measurable old)
    (hb:∀z,0≤old z ∧ old z≤P.lower/2)
    (σ target:Fin N→ℝ) (center:Fin N→HeatCircle) (hage:∀i,σ i≤target i) (q θ:ℝ):
    ControlledFixedReserve.covariance P Λ u d old σ target center q θ-
      NativeFirstScoreReserve.covariance P σ target center q=
    ControlledFixedReserve.covariance P Λ u d (NativeFirstScoreReserve.oldProfile P old)
      σ target center q θ:=by
  have hcm:Measurable (ControlledFixedReserve.coefficient P Λ u d (NativeFirstScoreReserve.oldProfile P old) θ):=
    ((ControlledProfile.profile_measurable P Λ u d).comp (measurable_const.prodMk measurable_id)).sub
      (NativeFirstScoreReserve.oldProfile_measurable P hm)
  have hcb:∀z,|ControlledFixedReserve.coefficient P Λ u d (NativeFirstScoreReserve.oldProfile P old) θ z|≤P.upper:=by
    intro z
    rw [abs_of_nonneg ((by have :=P.lower_pos;positivity:0≤3*P.lower/8).trans
      (NativeFirstScoreReserve.residual_bounds P Λ u d hb θ z).1)]
    exact (NativeFirstScoreReserve.residual_bounds P Λ u d hb θ z).2
  have hi:=StoppedCovarianceSplit.covariance_add σ target center hage q
    (c:=fun _=>NativeFirstScoreReserve.floor P)
    (d:=ControlledFixedReserve.coefficient P Λ u d (NativeFirstScoreReserve.oldProfile P old) θ)
    measurable_const hcm (M:=NativeFirstScoreReserve.floor P) (N:=P.upper)
    (fun _=>by rw [abs_of_pos (by have :=P.lower_pos;unfold NativeFirstScoreReserve.floor;positivity)]) hcb
  have he:(fun z:ControlledProfile.Domain=>NativeFirstScoreReserve.floor P+
      ControlledFixedReserve.coefficient P Λ u d (NativeFirstScoreReserve.oldProfile P old) θ z)=
      ControlledFixedReserve.coefficient P Λ u d old θ:=by
    funext z
    dsimp only [ControlledFixedReserve.coefficient,NativeFirstScoreReserve.oldProfile]
    ring
  rw [he] at hi
  change ControlledFixedReserve.covariance P Λ u d old σ target center q θ=
    NativeFirstScoreReserve.covariance P σ target center q+
      ControlledFixedReserve.covariance P Λ u d (NativeFirstScoreReserve.oldProfile P old) σ target center q θ at hi
  rw [hi]
  abel

theorem native_relative {N:ℕ} (P:CanonicalCovariance.ProfileParameters) (v q:ℝ)
    (σ target:Fin N→ℝ) (center:Fin N→HeatCircle):
    NativeFirstScoreReserve.covariance P σ target center q=
      NativeFirstScoreReserve.covariance P (fun i=>σ i-v) (fun i=>target i-v) center (q-v):=by
  have he:=ObservationTimeShift.stoppedCovariance_translation v (q-v)
    (fun i=>σ i-v) (fun i=>target i-v) center (fun _=>NativeFirstScoreReserve.floor P)
  have hp:ObservationTimeShift.profile v (fun _:ControlledProfile.Domain=>NativeFirstScoreReserve.floor P)=
      (fun _=>NativeFirstScoreReserve.floor P):=rfl
  rw [hp] at he
  simpa only [NativeFirstScoreReserve.covariance,sub_add_cancel] using he

variable (P:CanonicalCovariance.ProfileParameters) (hA:BoundedSmooth P.coefficient)
variable (Λ:ℝ) (v b:ℝ≥0) (hvb:v≤b)
variable {X:Type} [MeasurableSpace X] {n:ℕ} (Z:VariableObservations.Family X n)
variable (htarget:∀x i,(b:ℝ)≤(Z.observations x i).target)
variable (hstop:∀x i,(b:ℝ)≤(Z.observations x i).stop)
variable (F:X→WordRecursion.State n→ℝ) (hF:UniformBoundedSmooth F)
variable (hFm:Measurable (fun z:X×WordRecursion.State n=>F z.1 z.2))
local notation "Base"=>ControlledReferenceThetaGeometry.level P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm
local notation "Zero"=>Base (0,(0,0))

/-- ONE history event identifies the actual smaller fresh covariance
after the independent native reserve with the literal relative-age
three-eighths controlled residual, for ALL theta and past inputs. -/
theorem residual_all_parameters_ae
    (hages:∀x i,(Z.observations x i).stop≤(Z.observations x i).target)
    (ρ:Measure X) [IsFiniteMeasure ρ] (k:ℕ):
    ∀ᵐh∂historyMeasure (referenceData P P.coefficient hA Λ 0 v b hvb (0,0)) ρ k,
      ∀p:ℝ×Inputs,∀q:ℝ,(v:ℝ)≤q→q≤(carrier Zero k).terminal h→
      fullResidualCovariance (Base p) (oldProfile P Λ v p.2) k h q-
        NativeFirstScoreReserve.covariance P (stops (Base p) k h) (targets (Base p) k h)
          (centers (Base p) k h) q=
      ControlledFixedReserve.covariance P Λ p.2.1 p.2.2
        (NativeFirstScoreReserve.oldProfile P (fixedProfile P Λ p.2.1 p.2.2
          (fun j=>lower Zero k h j-(v:ℝ)) (fun j=>upper Zero k h j-(v:ℝ))))
        (fun i=>stops Zero k h i-(v:ℝ)) (fun i=>targets Zero k h i-(v:ℝ))
        (centers Zero k h) (q-(v:ℝ)) p.1:=by
  filter_upwards [ControlledThetaRelativeArrays.full_covariance_relative_fixed_ae
    P hA Λ v b hvb Z htarget hstop F hF hFm hages ρ k] with h hh
  intro p q hvq hqt
  rw [hh p q (v.2.trans hvq) hqt,
    ControlledThetaRelativeDerivative.stops_eq P hA Λ v b hvb Z htarget hstop F hF hFm p (0,(0,0)) k h,
    ControlledThetaRelativeDerivative.targets_eq P hA Λ v b hvb Z htarget hstop F hF hFm p (0,(0,0)) k h,
    ControlledThetaRelativeDerivative.centers_eq P hA Λ v b hvb Z htarget hstop F hF hFm p (0,(0,0)) k h,
    native_relative P (v:ℝ) q]
  apply covariance_sub_native P Λ p.2.1 p.2.2 _ (fixedProfile_measurable P Λ _ _ _ _)
    (fixedProfile_bounds P Λ _ _ _ _ (RelativeHistoryGeometry.relative_disjoint Zero k h))
  intro i
  exact sub_le_sub_right ((min_le_left _ _).trans (RecursiveScoreSupport.carrier_ages Zero hages k h i)) _

end SHE.ControlledThetaTwoFreshArrays
