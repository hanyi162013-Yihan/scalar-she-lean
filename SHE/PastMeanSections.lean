module

public import SHE.PastMeanAmplitude
public import SHE.FixedHistoryTimeFactors

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SHE.PastWordTimeFields
open Set MeasureTheory Real StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
  CutoffCarriers PhysicalParentGeometry PhysicalChainArrays CoveredControlledLaw HistoryProductMeasure
variable {X : Type} [MeasurableSpace X] {R : ReferenceData} {n : ℕ}
variable (L : Level R X n)

/-- Relative full-age gains, old gaps and minimum selections are all
independent of the output root and every old insertion location. -/
theorem total_sections (P : CanonicalCovariance.ProfileParameters)
    (T : ℝ) (hT : ∀ x,L.terminal x=T) (target : Fin n→ℝ)
    (htarget : ∀ x i,(L.observations.observations x i).target=target i)
    (k : ℕ) (t : Fin k→ℝ) (x x' : X) (z z' : Fin k→HeatCircle) (A0 ν : ℝ) :
    total L P k (separated k (x,t,z)) A0 ν=total L P k (separated k (x',t,z')) A0 ν := by
  have hl:=FixedHistoryTimeFactors.lower_sections L T hT k t x x' z z'
  have hu:=FixedHistoryTimeFactors.upper_sections L T hT k t x x' z z'
  have ht:=FixedHistoryTimeFactors.targets_sections L T hT target htarget k t x x' z z'
  simp only [total,hl,hu,ht]

end SHE.PastWordTimeFields

namespace SHE.PastMeanAmplitude
open Set MeasureTheory Real StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
  CutoffCarriers PhysicalParentGeometry PhysicalScoreChain PhysicalChainArrays CoveredControlledLaw
  HistoryProductMeasure ActualMeanKernel HistoryQuarterFields
variable {X : Type} [MeasurableSpace X] {R : ReferenceData} {n : ℕ}
variable (L : Level R X n)

theorem value_sections (P : CanonicalCovariance.ProfileParameters)
    (T : ℝ) (hT : ∀ x,L.terminal x=T) (target : Fin n→ℝ)
    (htarget : ∀ x i,(L.observations.observations x i).target=target i)
    (k : ℕ) (t : Fin k→ℝ) (x x' : X) (z z' : Fin k→HeatCircle) (q A0 ν : ℝ) :
    value L P k q A0 ν (separated k (x,t,z))=value L P k q A0 ν (separated k (x',t,z')) := by
  simp only [value,terminal_separated L T hT,rowTime_separated L T hT,
    FixedHistoryTimeFactors.timeWeight_sections L T hT _ _ k t x x' z z',
    PastWordTimeFields.total_sections L P T hT target htarget k t x x' z z']

theorem damped_sections (P : CanonicalCovariance.ProfileParameters)
    (T : ℝ) (hT : ∀ x,L.terminal x=T) (target : Fin n→ℝ)
    (htarget : ∀ x i,(L.observations.observations x i).target=target i)
    (k : ℕ) (t : Fin k→ℝ) (x x' : X) (z z' : Fin k→HeatCircle) (Λ q A0 ν : ℝ) :
    damped L P k Λ q A0 ν (separated k (x,t,z))=damped L P k Λ q A0 ν (separated k (x',t,z')) := by
  simp only [damped,rowTime_separated L T hT,value_sections L P T hT target htarget k t x x' z z']

end SHE.PastMeanAmplitude
