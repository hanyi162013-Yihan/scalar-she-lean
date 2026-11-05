module
public import SHE.ControlledFamilyThreeLeg
public import SHE.ControlledFamilyNativeLegs
public import SHE.NativeDirectionKernelFTC

public import SHE.ControlledThetaStoppedCovariance
public import SHE.CarrierStopBounds
public import SHE.ControlledJointMarkedWord
public import SHE.ControlledJointMeanIdentity
public import SHE.NativeHeatSpan

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section

namespace SHE.ControlledFamilyNativeKernelValue
open Set MeasureTheory ProbabilityTheory AddCircle StoppedFourier WordRecursion ControlledProfile ControlledReferenceLevel
  CutoffWordLevel CutoffWordHistories SmoothCylinders UniformSmooth CutoffCarriers PhysicalChainArrays
  PhysicalScoreChain ControlledOldIntervals ControlledReferenceWindows ControlledFamilyProfileForest
  ProjectedUncutWord CoveredControlledLaw CoveredHistoryGeometry GaussianConvolution FiniteCenteredProduct
open scoped NNReal BigOperators
local instance controlledFamilyThreeLeg_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance controlledFamilyThreeLeg_circleSigma : MeasurableSpace CircleL2 := borel _
local instance controlledFamilyThreeLeg_circleBorel : BorelSpace CircleL2 := ⟨rfl⟩
variable (P : CanonicalCovariance.ProfileParameters) (A : ℝ→ℝ) (hA : BoundedSmooth A)
variable (Λ : ℝ) (v b : ℝ≥0) (hvb : v≤b)
variable {X : Type} [MeasurableSpace X] {n : ℕ} (Z : VariableObservations.Family X n)
variable (htarget : ∀ x i,(b:ℝ)≤(Z.observations x i).target)
variable (hstop : ∀ x i,(b:ℝ)≤(Z.observations x i).stop)
variable (F : X→WordRecursion.State n→ℝ) (hF : UniformBoundedSmooth F)
variable (hFm : Measurable (fun q : X×WordRecursion.State n=>F q.1 q.2))
local notation "Base" => ControlledReferenceThetaGeometry.level P A hA Λ v b hvb Z htarget hstop F hF hFm

local notation "Sig" => ControlledFamilyThreeLeg.sigma P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "Tar" => ControlledFamilyThreeLeg.target P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "Cen" => ControlledFamilyThreeLeg.center P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "Lo" => ControlledFamilyThreeLeg.lo P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "Hi" => ControlledFamilyThreeLeg.hi P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "LP" => ControlledFamilyThreeLeg.leafPoint P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "Law" => ControlledFamilyThreeLeg.oldLaw P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "Wgt" => ControlledFamilyThreeLeg.oldWeight P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "Root" => ControlledFamilyThreeLeg.scaledRoot P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "Leaf" => ControlledFamilyThreeLeg.coefficientLeaf A (n:=n)
open ControlledFamilyThreeLeg

/-- Literal original finite-history kernel differentiated in an arbitrary
fixed native range direction. In particular, the physical row may be
at a later r while the conditional Gaussian law remains at q. -/
local notation "Kernel"=>ControlledFamilyNativeDirection.kernel P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "C"=>ControlledFamilyNativeLegs.remaining P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "Avg"=>ControlledFamilyNativeLegs.average P A hA Λ v b hvb Z htarget hstop F hF hFm

theorem kernel_eq_average
    (hroot:∀x i,(Z.observations x i).stop=(b:ℝ))
    (hspan:(b:ℝ)-(v:ℝ)≤P.horizon)(p:Inputs)(k:ℕ)(h:History X k)
    (q:ℝ)(hq:(v:ℝ)≤q)(hqt:q<(carrier (Base (0,p)) k).terminal h)
    (U D:CircleL2)(E:WordRecursion.State (n+k))
    (hE:E∈(Matrix.toEuclideanCLM (𝕜:=ℝ) (NativeFirstScoreReserve.covariance P
      (Sig p k h) (Tar p k h) (StoppedGaussianScore.nativeCenter (Cen p k h)) (q-(v:ℝ)))).range)
    (θ:ℝ):
    Kernel p k h q U D E θ=
      gaussianAverage (C p k h q θ)
        (Avg p k h q E (test Finset.univ (Root p k h) (Leaf k)
          (fun j=>ControlledFiniteWord.baselines P Λ p.1 p.2 (LP p k h) j θ)))
        (ControlledJointWeightedWord.jointMeanVector (Sig p k h) (Tar p k h) (Cen p k h) (q-(v:ℝ)) Λ U D θ):=by
  have hages : ∀ x i,(Z.observations x i).stop≤(Z.observations x i).target := by
    intro x i
    rw [hroot x i]
    exact htarget x i
  have hgeom:=RecursiveScoreSupport.carrier_ages (Base (0,p)) hages k h
  have hs : ∀ i,Sig p k h i≤Tar p k h i:=fun i=>sub_le_sub_right (hgeom i) _
  have hgap : ∀ i,q-(v:ℝ)<Sig p k h i := by
    intro i
    exact sub_lt_sub_right (hqt.trans_le ((carrier (Base (0,p)) k).stops_after h i)) _
  have hTh : ∀ i,Sig p k h i≤P.horizon := by
    intro i
    have he:=CarrierStopBounds.stop_le_initial (Base (0,p))
      (fun x i=>by change (Z.observations x i).stop≤(b:ℝ);rw [hroot x i]) k h i
    change ((carrier (Base (0,p)) k).observations.observations h i).stop≤(b:ℝ) at he
    exact (sub_le_sub_right he (v:ℝ)).trans hspan
  have hd : ∀ j l : Fin k,j≠l → Hi p k h j≤Lo p k h l ∨ Hi p k h l≤Lo p k h j := by
    intro j l hjl
    rcases disjoint (Base (0,p)) k h j l hjl with hj|hl
    · exact Or.inl (sub_le_sub_right hj _)
    · exact Or.inr (sub_le_sub_right hl _)
  have hold:=fixedProfile_measurable P Λ p.1 p.2 (Lo p k h) (Hi p k h)
  have holdb:=fixedProfile_bounds P Λ p.1 p.2 (Lo p k h) (Hi p k h) hd
  letI : IsProbabilityMeasure (Law p k h) := by
    unfold oldLaw
    infer_instance
  have hw : Integrable (Wgt p k h) (Law p k h):=Integrable.fintype_prod
    (fun j=>GaussianVectorFractions.gaussian_secondScore_integrable
      (oldMatrices P A hA Λ v b hvb Z htarget hstop F hF hFm p k h j)
      (oldDirections P A hA Λ v b hvb Z htarget hstop F hF hFm p k h j))
  have hwm : Measurable (Wgt p k h) := by
    apply Finset.measurable_prod Finset.univ
    intro j _
    have hm:=MeasurableGaussianScores.secondScore_measurable (n:=n+k)
    have hmap : Measurable (fun y : Fin k→WordRecursion.State (n+k)=>
        ((oldMatrices P A hA Λ v b hvb Z htarget hstop F hF hFm p k h j,
          oldDirections P A hA Λ v b hvb Z htarget hstop F hF hFm p k h j),y j)) :=
      (measurable_const.prodMk measurable_const).prodMk (measurable_pi_apply j)
    have hh:=hm.comp hmap
    exact hh
  have hshift : Measurable (fun y : Fin k→WordRecursion.State (n+k)=>∑ j,y j):=
    Finset.measurable_sum Finset.univ (fun j _=>measurable_pi_apply j)
  obtain ⟨K,hKn,hKb⟩:=hF.norm_bound
  obtain ⟨M,hMb⟩:=hA.norm_bound
  have hMn : 0≤M:=(norm_nonneg (A 0)).trans (hMb 0)
  have hRm : Measurable (Root p k h) :=
    ((PhysicalChainArrays.initial_measurable (Base (0,p)) k (fun i=>i)).comp
      (measurable_const.prodMk measurable_id)).const_mul _
  have hRb (z : WordRecursion.State (n+k)) : |Root p k h z|≤(1/2:ℝ)^k*K := by
    rw [scaledRoot,abs_mul,abs_of_nonneg (by positivity : 0≤(1/2:ℝ)^k)]
    have hh:=hKb (PhysicalScoreChain.rootParameter k h) (GaussianCoordinates.projection
      (rootSelector k (fun i=>i)) z)
    have hb : |PhysicalChainArrays.initial (Base (0,p)) k h (fun i=>i) z|≤K := by
      simpa only [PhysicalChainArrays.initial,ControlledReferenceThetaGeometry.level,
        ControlledReferenceFamilyLevel.level,Real.norm_eq_abs] using hh
    exact mul_le_mul_of_nonneg_left hb (by positivity)
  have ham (j : Fin k) : Measurable (Leaf k j) := hA.smooth.continuous.measurable.comp
    ((measurable_pi_apply (leafIndex k (fun i=>i) j)).comp (WithLp.measurable_ofLp 2 (Fin (n+k)→ℝ)))
  have hab (j : Fin k) (z : WordRecursion.State (n+k)) : |Leaf k j z|≤M:=by
    simpa only [coefficientLeaf,Real.norm_eq_abs] using hMb (z (leafIndex k (fun i=>i) j))
  exact NativeDirectionKernelFTC.kernel_eq
    (P:=P) (Λ:=Λ) (σ:=Sig p k h) (target:=Tar p k h) (center:=Cen p k h)
    (q:=q-(v:ℝ)) (hq:=sub_nonneg.mpr hq) (hgap:=hgap) (hTh:=hTh) (hages:=hs)
    (u:=p.1) (d:=p.2) (Z:=U) (D:=D)
    (old:=fixedProfile P Λ p.1 p.2 (Lo p k h) (Hi p k h)) (hold:=hold) (holdb:=holdb)
    (μ:=Law p k h) (w:=Wgt p k h) (hw:=hw) (hwm:=hwm) (shift:=fun y=>∑j,y j) (hs:=hshift)
    (e:=E) (he:=hE) (s:=Finset.univ) (leaf:=LP p k h) (Rtest:=Root p k h) (a:=Leaf k)
    (hRoot:=hRm) (ha:=fun j _=>ham j) (B:=(1/2:ℝ)^k*K) (M:=fun _=>M)
    (hB:=by positivity) (hM:=fun _ _=>hMn) (hRb:=hRb) (hab:=fun j _=>hab j) θ

end SHE.ControlledFamilyNativeKernelValue
