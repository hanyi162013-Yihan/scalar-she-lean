module

public import SHE.ScalarDefectRelativeGeometry
public import SHE.ScalarRootSharpSections

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1800000

namespace SHE.DefectRelativeFactor
open Set MeasureTheory Real AddCircle StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories
  CutoffCarriers PhysicalParentGeometry PhysicalChainArrays PhysicalScoreChain HistoryProductMeasure
  CoveredControlledLaw OrderedHeatForests
local instance defectRelativeFactor_period:Fact (0<2*π):=⟨by positivity⟩
variable {R:ReferenceData}(L:Level R HeatCircle 1)(T:ℝ)(hT:∀x,L.terminal x=T)

/-- Bounded untouched leaves eliminate current-age dependence, while
every genuine old block minimum and root clip is kept. -/
def total (P:CanonicalCovariance.ProfileParameters)(v:ℝ)(k:ℕ)(h:History HeatCircle k)(A0 ν:ℝ):ℝ:=
  TwoFreshBoundedEmptyWord.total (d:=1) P
    (fun j=>lower L k h j-v) (fun j=>upper L k h j-v) (fun _:Fin k=>0) A0 ν

theorem total_actual (P:CanonicalCovariance.ProfileParameters)(v:ℝ)(k:ℕ)(h:History HeatCircle k)
    (age:Fin k→ℝ)(A0 ν:ℝ):
    TwoFreshBoundedEmptyWord.total (d:=1) P
      (fun j=>lower L k h j-v) (fun j=>upper L k h j-v) age A0 ν=
      total L P v k h A0 ν:=
  ScalarDefectRelativeGeometry.total_age P _ _ age (fun _:Fin k=>0) A0 ν

include T hT in
theorem total_sections (P:CanonicalCovariance.ProfileParameters)(v:ℝ)(k:ℕ)(t:Fin k→ℝ)
    (x x':HeatCircle)(w w':Fin k→HeatCircle)(A0 ν:ℝ):
    total L P v k (separated k (x,t,w)) A0 ν=
      total L P v k (separated k (x',t,w')) A0 ν:=by
  unfold total
  rw [FixedHistoryTimeFactors.lower_sections L T hT k t x x' w w',
    FixedHistoryTimeFactors.upper_sections L T hT k t x x' w w']

include T hT in
/-- Exact factorization in original relative old coordinates. The
entire root dependence is in the actual Hessian; the positive parent
density and every old gain remain available for Minkowski averaging. -/
theorem factor_relative (P:CanonicalCovariance.ProfileParameters)(v ell A:ℝ)(C:ℕ→ℝ)
    (hA:∀x i,(L.observations.observations x i).target=A)
    (hcenter:∀x i,(L.observations.observations x i).center=x)
    (k:ℕ)(t:Fin k→ℝ)(x:HeatCircle)(w:Fin k→HeatCircle)
    (ht:OrderedTimes k (targets L k (separated k (x,t,fun i=>w i+x))))
    (A0 ν:ℝ):
    let h:=separated k (x,t,fun i=>w i+x)
    let z:=separated k ((0:HeatCircle),t,fun _=>0)
    timeWeight L ell C k h*
      parentDensity 2 (by norm_num) k (targets L k h) ht (centers L k h)*
      total L P v k h A0 ν=
      (timeWeight L ell C k z*total L P v k z A0 ν)*
        parentDensity 2 (by norm_num) k (targets L k z)
          (by
            have he:=FixedHistoryTimeFactors.targets_sections L T hT (fun _=>A) hA
              k t x 0 (fun i=>w i+x) (fun _=>0)
            simpa only [he] using ht)
          (values (fun _:Fin 1=>(0:HeatCircle)) k w):=by
  intro h z
  rw [ScalarRootRelativeGeometry.parent_density_relative L T hT 2 (by norm_num) A hA hcenter k t x w ht,
    FixedHistoryTimeFactors.timeWeight_sections L T hT ell C k t x 0 (fun i=>w i+x) (fun _=>0),
    total_sections L T hT P v k t x 0 (fun i=>w i+x) (fun _=>0)]
  ring

end SHE.DefectRelativeFactor
