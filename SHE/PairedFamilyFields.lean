module

public import SHE.ControlledFiniteEndpointComparison
public import SHE.FiniteAssignmentMoments
public import SHE.ControlledThetaPhysicalGeometry

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
namespace SHE.PairedFamilyFields
open Set MeasureTheory Real StoppedFourier WordRecursion CutoffWordLevel CutoffWordHistories CutoffCarriers
  ControlledProfile PhysicalChainArrays PhysicalScoreChain SmoothCylinders UniformSmooth GaussianCoordinates
open scoped NNReal BigOperators
local instance pairedFamilyFields_period:Fact (0<2*Real.pi):=⟨by positivity⟩
local instance pairedFamilyFields_circleSigma:MeasurableSpace CircleL2:=borel _
local instance pairedFamilyFields_circleBorel:BorelSpace CircleL2:=⟨rfl⟩
variable (P:CanonicalCovariance.ProfileParameters) (hA:BoundedSmooth P.coefficient) (Λ:ℝ)
variable (v b:ℝ≥0) (hvb:v≤b) {X:Type} [MeasurableSpace X]
variable (Z:VariableObservations.Family X 1)
variable (htarget:∀x i,(b:ℝ)≤(Z.observations x i).target)
variable (hstop:∀x i,(b:ℝ)≤(Z.observations x i).stop)
variable (F:X→WordRecursion.State 1→ℝ) (hF:UniformBoundedSmooth F)
variable (hFm:Measurable (fun z:X×WordRecursion.State 1=>F z.1 z.2))
local notation "Base"=>ControlledReferenceThetaGeometry.level P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm

/-- Full paired comparison with BOTH own baselines, evaluated at
arbitrary jointly dependent past inputs and endpoint current vectors. -/
theorem paired_variable_measurable {W:Type} [MeasurableSpace W] (k:ℕ)
    (p:W→Inputs) (hp:Measurable p) (hist:W→History X k) (hh:Measurable hist)
    (newMean oldMean:W→WordRecursion.State (1+k)) (hn:Measurable newMean) (ho:Measurable oldMean)
    (ν χ:ℝ):
    Measurable (fun w=>ControlledFiniteEndpointComparison.paired P hA Λ v b hvb Z htarget hstop F hF hFm
      (p w) k (hist w) (newMean w) (oldMean w) ν χ):=by
  have hbas(a:ℝ)(j:Fin k):Measurable (fun w=>baseline (Base (a,p w)) k (hist w) j):=by
    have hl:Measurable (fun w=>lower (Base (0,(0,0))) k (hist w) j):=(lower_measurable _ k j).comp hh
    have hs:Measurable (fun w=>space k (hist w) j):=(space_measurable k j).comp hh
    have hg:=(ControlledThetaWordFields.coefficient_joint_measurable P Λ v).comp
      (((measurable_const (a:=a)).prodMk hp).prodMk (hl.prodMk hs))
    convert! hg using 1
    funext w
    unfold baseline
    rw [ControlledThetaPhysicalGeometry.lower_eq P P.coefficient hA Λ v b hvb Z htarget hstop F hF hFm
      (a,p w) (0,(0,0)) k (hist w)]
    rfl
  have hcoord(j:Fin (1+k)):Measurable (fun w=>newMean w j-oldMean w j):=
    ((EuclideanSpace.proj (𝕜:=ℝ) j).continuous.measurable.comp hn).sub
      ((EuclideanSpace.proj (𝕜:=ℝ) j).continuous.measurable.comp ho)
  have hsrc(cs:List (Fin k×Fin (k+1)))(i:Fin (k+1)):
      Measurable (fun w=>PairedAssignedTelescope.sources P cs (rootSelector k (fun j=>j))
        (leafIndex k (fun j=>j)) (newMean w) (oldMean w)
        (baseline (Base (1,p w)) k (hist w)) (baseline (Base (0,p w)) k (hist w)) ν χ i):=by
    refine Fin.cases ?_ (fun j=>?_) i
    · simp only [PairedAssignedTelescope.sources,Fin.cases_zero]
      exact (measurable_const.min (((GaussianCoordinates.projection (rootSelector k (fun j=>j))).continuous.measurable.comp
        (hn.sub ho)).norm.const_mul ν)).pow_const χ
    · simp only [PairedAssignedTelescope.sources,Fin.cases_succ,PairedRoughWordMoments.source]
      split_ifs with hb
      · unfold NormalizedPairedLeaf.source
        exact (measurable_const.mul ((continuous_abs.measurable.comp (hcoord _)).pow_const χ)).add
          ((continuous_abs.measurable.comp ((hbas 1 j).sub (hbas 0 j))).pow_const (χ/P.exponent))
      · exact (continuous_abs.measurable.comp (hcoord _)).pow_const χ
  unfold ControlledFiniteEndpointComparison.paired
  simp_rw [FiniteAssignmentMoments.map_sum_eq_fin]
  apply measurable_const.mul
  apply Finset.measurable_sum
  intro cs _
  apply Finset.measurable_sum
  intro i _
  exact (hsrc _ i).mul (ControlledTerminalPairedFields.average_variable_measurable
    P hA Λ v b hvb Z htarget hstop F hF hFm k p hp hist hh newMean oldMean hn ho _ ν χ i)

end SHE.PairedFamilyFields
