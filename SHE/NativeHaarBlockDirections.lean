module

public import SHE.NativeDefectHaarAction
public import SHE.StoppedCurrentBlockHaarTrace
public import SHE.StoppedDefectBlockProjection

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

namespace SHE.NativeHaarBlockDirections
open Set MeasureTheory Real AddCircle FiniteHaar CircleHeat StoppedFourier StoppedGaussianFeatures
  StoppedGaussianScore StoppedCanonicalScore HeatTorus HeatTorusKernel HeatProjection
  GaussianGramScore GaussianIncrement StoppedMeanEnergy StoppedAgeBlocks StoppedBlockMean
  RealHeatCovarianceMean MeasurableGaussianScores BlockDefectScores CommonHaarDefectTrace
local instance nativeHaarBlockDirections_period:Fact (0<2*π):=⟨by positivity⟩
local instance nativeHaarBlockDirections_unit:Fact (0<(1:ℝ)):=⟨zero_lt_one⟩

/-- The selected clipped block is exactly the selected original
common-Haar analysis direction, including its own stopping weight. -/
theorem clipped {n g:ℕ}{m W:ℝ}(hm:0<m)(c d:EllipticField m W)
    (label:Fin n→Fin g)(rep:Fin g→Fin n)(σ target:Fin n→ℝ)(a:Fin n→UnitAddCircle)(u Λ:ℝ)
    (t:Fin n→ℝ)(ht:∀i,0<t i)(hage:∀i,target i-u=4*π^2*t i)
    (act:∀i,u<σ i)(actg:∀j i,u<groupData label rep σ j i)(j:Fin g)(l:HaarNode):
    restrictCoefficients label j (NativeClippedHaarDirection.column hm c d σ target a u Λ l)=
      meanDirection (StoppedDefectBlockProjection.synthesis label rep σ target a u Λ t hage actg j)
        (globalSignedColumn l c.1 d.1):=by
  apply PiLp.ext
  intro i
  rw [restrictCoefficients_apply,meanDirection_apply]
  by_cases hi:label i=j
  · rw [if_pos hi]
    have he:=congrArg (fun z:State n=>z i)
      (NativeClippedHaarDirection.column_eq_meanDirection hm c d σ target a u Λ t ht hage act l)
    rw [meanDirection_apply,StoppedDefectMeanEnergy.clippedSynthesis_basis] at he
    simpa only [StoppedDefectBlockProjection.synthesis,LinearMap.comp_apply,
      LinearMap.restrictScalars_apply,Submodule.subtype_apply,defectBlockRow_basis,if_pos hi] using he
  · simp only [if_neg hi,StoppedDefectBlockProjection.synthesis,LinearMap.comp_apply,
      LinearMap.restrictScalars_apply,Submodule.subtype_apply,defectBlockRow_basis,if_neg hi,
      inner_zero_left,Complex.zero_re]

/-- The selected undamped companion block is the actual original
Haar row of that same coefficient field, with no modified clock. -/
theorem current {n g:ℕ}{m W:ℝ}(hm:0<m)(c:EllipticField m W)
    (label:Fin n→Fin g)(rep:Fin g→Fin n)(σ target:Fin n→ℝ)(a:Fin n→UnitAddCircle)(u:ℝ)
    (t:Fin n→ℝ)(ht:∀i,0<t i)(hage:∀i,target i-u=4*π^2*t i)
    (actg:∀j i,u<groupData label rep σ j i)(j:Fin g)(l:HaarNode):
    restrictCoefficients label j (direction (fun i=>NativeObservationCovariance.row hm c
      (target i) u (nativeCenter a i)) l)=
      meanDirection (StoppedCurrentBlockHaarTrace.synthesis label rep σ target a u t hage actg j)
        (globalHaarColumn l c.1):=by
  apply PiLp.ext
  intro i
  rw [restrictCoefficients_apply,meanDirection_apply,StoppedCurrentBlockHaarTrace.basis]
  by_cases hi:label i=j
  · simp only [if_pos hi]
    change NativeObservationCovariance.row hm c (target i) u (nativeCenter a i) l=_
    have hiage:u<target i:=by
      have hp:0<target i-u:=by rw [hage i];exact mul_pos (by positivity) (ht i)
      linarith
    rw [NativeObservationColumnMean.row hm c hiage,PhysicalProfile.physicalHeatMean_eq (sub_pos.mpr hiage)]
    have he:=CircleNormalization.push.inner_map_map (unitHeatKernel (t i) (a i)) (globalHaarColumn l c.1)
    rw [HeatMarkov.push_unitHeatKernel,←hage i] at he
    exact congrArg Complex.re he
  · simp only [if_neg hi,inner_zero_left,Complex.zero_re]

/-- The block operation is a decomposition of all original coordinates,
not a projection to a smaller observation law. -/
theorem sum_blocks {n g:ℕ}(label:Fin n→Fin g)(z:State n):
    (∑j:Fin g,restrictCoefficients label j z)=z:=by
  apply PiLp.ext
  intro i
  change ((∑j:Fin g,restrictCoefficients label j z).ofLp i)=z i
  simp only [WithLp.ofLp_sum,Finset.sum_apply,restrictCoefficients_apply]
  simp

end SHE.NativeHaarBlockDirections
