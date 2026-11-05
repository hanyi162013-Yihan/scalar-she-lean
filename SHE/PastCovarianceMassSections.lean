module

public import SHE.ScalarRootRelativeGeometry

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.ScalarRootRelativeGeometry
open Set MeasureTheory Real AddCircle StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
  CutoffCarriers PhysicalParentGeometry PhysicalChainArrays PhysicalScoreChain HistoryProductMeasure
  CoveredHistoryGeometry CoveredControlledLaw OrderedHeatForests ActualMeanKernel ControlledOldIntervals
  ControlledResidualScoreInput
local instance : Fact (0<2*π) := ⟨by positivity⟩
variable {R : ReferenceData} (L : Level R HeatCircle 1)
variable (T : ℝ) (hT : ∀ x,L.terminal x=T)
include T hT in
/-- Exact root-relative score mass while EVERY original time array is
shifted by the actual past time. The spatially inhomogeneous random
profile may be substituted only after this identity is proved for all data. -/
theorem future_input_relative_shifted (P : CanonicalCovariance.ProfileParameters) (Λ : ℝ)
    (u d : CircleL2) (θ shift : ℝ) (σ A : ℝ)
    (hσ : ∀ x i,(L.observations.observations x i).stop=σ)
    (hA : ∀ x i,(L.observations.observations x i).target=A)
    (hcenter : ∀ x i,(L.observations.observations x i).center=x)
    (k : ℕ) (t : Fin k→ℝ) (x : HeatCircle) (w : Fin k→HeatCircle)
    (e : StoppedGaussianFeatures.Domain→ℝ) (q : ℝ) :
    let p := separated k (x,t,fun i=>w i+x)
    let a := separated k ((0:HeatCircle),t,fun _=>(0:HeatCircle))
    futureInput (fun i=>stops L k p i-shift) (fun i=>targets L k p i-shift) (centers L k p)
      (fun r=>ControlledProfile.profile P Λ u d (θ,r)-fixedProfile P Λ u d (fun j=>lower L k p j-shift) (fun j=>upper L k p j-shift) r) e q 0=
    futureInput (fun i=>stops L k a i-shift) (fun i=>targets L k a i-shift) (values (fun _ : Fin 1=>(0:HeatCircle)) k w)
      (fun r=>ControlledProfile.profile P Λ u d (θ,r)-fixedProfile P Λ u d (fun j=>lower L k a j-shift) (fun j=>upper L k a j-shift) r) e q x := by
  dsimp only
  rw [covered_stops_sections L T hT σ hσ k t x 0 _ (fun _=>0),
    FixedHistoryTimeFactors.targets_sections L T hT (fun _=>A) hA k t x 0 _ (fun _=>0),
    FixedHistoryTimeFactors.lower_sections L T hT k t x 0 _ (fun _=>0),
    FixedHistoryTimeFactors.upper_sections L T hT k t x 0 _ (fun _=>0),
    centers_relative L hcenter]
  simp only [futureInput,add_zero]


end SHE.ScalarRootRelativeGeometry
