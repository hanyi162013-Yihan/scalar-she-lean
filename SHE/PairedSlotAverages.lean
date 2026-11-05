module

public import SHE.PairedGaussianComparison

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
namespace SHE.PairedAssignedTelescope
open Set MeasureTheory ProbabilityTheory Real GaussianIncrement GaussianAssignmentBlocks GaussianCoordinates
  ControlledOldIntervals OldIntervalCovariance StoppedFourier
open scoped BigOperators
open Classical
variable {n r m:ℕ}

def averageSlot (P:CanonicalCovariance.ProfileParameters) (Λ:ℝ) (u d:CircleL2)
    (θ ηNew ηOld q:ℝ) (σ target:Fin n→ℝ) (center:Fin n→HeatCircle) (lo hi:Fin r→ℝ)
    (D:Fin r→State n) (choices:List (Fin r×Fin (m+1))) (F:State 1→ℝ)
    (g:Fin 1→Fin n) (leaf:Fin m→Fin n) (newMean oldMean:State n) (ν χ:ℝ) (i:Fin (m+1)):ℝ:=
  let A:=familyCovariance σ target center (referenceProfile P Λ u d) lo hi
  let B:=ControlledFixedReserve.covariance P Λ u d (fixedProfile P Λ u d lo hi) σ target center q θ
  let bas:=fun η j=>ControlledProfile.profile P Λ u d (η,(target (leaf j),center (leaf j)))
  ∫x,slot P A D choices F g leaf newMean oldMean (bas ηNew) (bas ηOld) ν χ i x
    ∂(Measure.pi (fun j=>multivariateGaussian (0:State n) (A j))).prod
      (multivariateGaussian (0:State n) B)

def endpointAverage (P:CanonicalCovariance.ProfileParameters) (Λ:ℝ) (u d:CircleL2)
    (θ η q:ℝ) (σ target:Fin n→ℝ) (center:Fin n→HeatCircle) (lo hi:Fin r→ℝ)
    (D:Fin r→State n) (choices:List (Fin r×Fin (m+1))) (F:State 1→ℝ)
    (g:Fin 1→Fin n) (leaf:Fin m→Fin n) (mean:State n):ℝ:=
  let A:=familyCovariance σ target center (referenceProfile P Λ u d) lo hi
  let B:=ControlledFixedReserve.covariance P Λ u d (fixedProfile P Λ u d lo hi) σ target center q θ
  ∫x,NoFreshGaussianIdentity.value A D choices P.coefficient F g leaf
    (fun j=>ControlledProfile.profile P Λ u d (η,(target (leaf j),center (leaf j)))) mean x
    ∂(Measure.pi (fun j=>multivariateGaussian (0:State n) (A j))).prod
      (multivariateGaussian (0:State n) B)

theorem averageSlot_root (P:CanonicalCovariance.ProfileParameters) (Λ:ℝ) (u d:CircleL2)
    (θ ηNew ηOld q:ℝ) (σ target:Fin n→ℝ) (center:Fin n→HeatCircle) (lo hi:Fin r→ℝ)
    (D:Fin r→State n) (choices:List (Fin r×Fin (m+1))) (F:State 1→ℝ)
    (g:Fin 1→Fin n) (leaf:Fin m→Fin n) (newMean oldMean:State n) (ν χ:ℝ):
    averageSlot P Λ u d θ ηNew ηOld q σ target center lo hi D choices F g leaf newMean oldMean ν χ 0=
      PairedRootVaryingMoments.fibreAverage P Λ u d θ q σ target center lo hi newMean oldMean
        (fun _=>newMean) (fun _=>ηNew) D g leaf choices F ν χ :=
  root_average P Λ u d θ ηNew ηOld q σ target center lo hi D choices F g leaf newMean oldMean ν χ

theorem averageSlot_rough (P:CanonicalCovariance.ProfileParameters) (Λ:ℝ) (u d:CircleL2)
    (θ ηNew ηOld q:ℝ) (σ target:Fin n→ℝ) (center:Fin n→HeatCircle) (lo hi:Fin r→ℝ)
    (D:Fin r→State n) (choices:List (Fin r×Fin (m+1))) (F:State 1→ℝ)
    (g:Fin 1→Fin n) (leaf:Fin m→Fin n) (newMean oldMean:State n) (ν χ:ℝ) (j0:Fin m):
    averageSlot P Λ u d θ ηNew ηOld q σ target center lo hi D choices F g leaf newMean oldMean ν χ j0.succ=
      PairedRoughVaryingMoments.fibreAverage P Λ u d θ ηOld ηNew q σ target center lo hi
        newMean oldMean oldMean (fun j=>decide (j0<j)) D g leaf choices j0 F χ :=
  rough_average P Λ u d θ ηNew ηOld q σ target center lo hi D choices F g leaf newMean oldMean ν χ j0

/-- Exact no-fresh Gaussian endpoint comparison at a COMMON future law:
one root source and each original rough source are OUTSIDE the checked
normalized averages. Each endpoint retains its OWN profile baseline. -/
theorem endpoint_difference (P:CanonicalCovariance.ProfileParameters) (Λ:ℝ) (u d:CircleL2)
    (θ ηNew ηOld q:ℝ) (σ target:Fin n→ℝ) (center:Fin n→HeatCircle) (lo hi:Fin r→ℝ)
    (D:Fin r→State n) (choices:List (Fin r×Fin (m+1))) (hnd:(choices.map Prod.fst).Nodup)
    (F:State 1→ℝ) (g:Fin 1→Fin n) (leaf:Fin m→Fin n) (newMean oldMean:State n)
    {A0 ν χ:ℝ} (hA0:0≤A0) (hν:0≤ν) (hχ:0≤χ) (hχβ:χ≤P.exponent)
    (hF:ContDiff ℝ ((block choices 0).length+1) F)
    (hb:∀j,j≤(block choices 0).length+1→∀z,‖iteratedFDeriv ℝ j F z‖≤A0*ν^j):
    endpointAverage P Λ u d θ ηNew q σ target center lo hi D choices F g leaf newMean-
      endpointAverage P Λ u d θ ηOld q σ target center lo hi D choices F g leaf oldMean=
      (min 1 (ν*‖projection g (newMean-oldMean)‖))^χ*
        averageSlot P Λ u d θ ηNew ηOld q σ target center lo hi D choices F g leaf newMean oldMean ν χ 0+
      ∑j,PairedRoughWordMoments.source P choices j.succ χ newMean oldMean (leaf j)
        (ControlledProfile.profile P Λ u d (ηNew,(target (leaf j),center (leaf j))))
        (ControlledProfile.profile P Λ u d (ηOld,(target (leaf j),center (leaf j))))*
        averageSlot P Λ u d θ ηNew ηOld q σ target center lo hi D choices F g leaf newMean oldMean ν χ j.succ := by
  let bas:=fun η (j:Fin m)=>ControlledProfile.profile P Λ u d (η,(target (leaf j),center (leaf j)))
  have hh:=(gaussian_difference P
    (familyCovariance σ target center (referenceProfile P Λ u d) lo hi) D
    (ControlledFixedReserve.covariance P Λ u d (fixedProfile P Λ u d lo hi) σ target center q θ)
    choices hnd F g leaf newMean oldMean (bas ηNew) (bas ηOld)
    hA0 hν hχ hχβ hF hb).2
  simpa only [Fin.sum_univ_succ,sources,Fin.cases_zero,Fin.cases_succ,endpointAverage,averageSlot,bas] using hh

end SHE.PairedAssignedTelescope
