module

public import SHE.SharpWordTimeScale
public import SHE.FixedHistoryTimeFactors

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2100000
noncomputable section

namespace SHE.SharpWordTimeScale
open Set MeasureTheory StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
  CutoffCarriers PhysicalParentGeometry PhysicalChainArrays HistoryProductMeasure
  CoveredHistoryGeometry CoveredControlledLaw GaussianAssignmentBlocks GaussianFreshAssignments ActualMeanKernel
variable {X : Type} [MeasurableSpace X] {R : ReferenceData} {n : ℕ}
variable (L : CutoffWordLevel.Level R X n)
variable (T : ℝ) (hT : ∀ p,L.terminal p=T)
include T hT

/-- The actual minimizing index is invariant under changing the output
root and old insertion sites when their true time arrays agree. -/
theorem chosen_sections (k : ℕ) (t : Fin k→ℝ) (p p' : X)
    (x x' : Fin k→HeatCircle) (q : ℝ) (cs : List (Fin k×Fin (k+1))) :
    chosen L k (separated k (p,t,x)) q cs=chosen L k (separated k (p',t,x')) q cs := by
  have hl := FixedHistoryTimeFactors.lower_sections L T hT k t p p' x x'
  have hu := FixedHistoryTimeFactors.upper_sections L T hT k t p p' x x'
  have he : (carrier L k).terminal (separated k (p,t,x))=
      (carrier L k).terminal (separated k (p',t,x')) := by
    rw [terminal_separated L T hT,terminal_separated L T hT]
  funext j h
  simp only [chosen,lowerWith,upperWith,hl,hu,he]

theorem factor_sections (Q : CanonicalCovariance.ProfileParameters) (target : Fin n→ℝ)
    (htarget : ∀ p i,(L.observations.observations p i).target=target i)
    (k : ℕ) (t : Fin k→ℝ) (p p' : X) (x x' : Fin k→HeatCircle)
    (q A0 ν : ℝ) (cs : List (Fin k×Fin (k+1))) :
    factor L Q k (separated k (p,t,x)) q cs A0 ν=
      factor L Q k (separated k (p',t,x')) q cs A0 ν := by
  have hl := FixedHistoryTimeFactors.lower_sections L T hT k t p p' x x'
  have hu := FixedHistoryTimeFactors.upper_sections L T hT k t p p' x x'
  have ht := FixedHistoryTimeFactors.targets_sections L T hT target htarget k t p p' x x'
  have he : (carrier L k).terminal (separated k (p,t,x))=
      (carrier L k).terminal (separated k (p',t,x')) := by
    rw [terminal_separated L T hT,terminal_separated L T hT]
  have hchoice := chosen_sections L T hT k t p p' x x' q cs
  simp only [factor,PhysicalWordTimeScale.factor,hchoice,lowerWith,upperWith,hl,hu,ht,he]

/-- The SHARP minimum-block time sum is a deterministic old-time
amplitude, independent of root/output and all insertion positions. -/
theorem total_sections (Q : CanonicalCovariance.ProfileParameters) (target : Fin n→ℝ)
    (htarget : ∀ p i,(L.observations.observations p i).target=target i)
    (k : ℕ) (t : Fin k→ℝ) (p p' : X) (x x' : Fin k→HeatCircle) (q A0 ν : ℝ) :
    total L Q k (separated k (p,t,x)) q A0 ν=
      total L Q k (separated k (p',t,x')) q A0 ν := by
  simp only [total,factor_sections L T hT Q target htarget k t p p' x x' q A0 ν]

end SHE.SharpWordTimeScale
