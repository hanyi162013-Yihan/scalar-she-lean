module

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

namespace SHE.ControlledFamilyThreeLeg
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

/-- The original carrier data in relative physical ages. Old scores
will be selected once at theta zero and retained throughout the FTC. -/
def sigma (p : Inputs) (k : ℕ) (h : History X k) (i : Fin (n+k)) : ℝ :=
  ((carrier (Base (0,p)) k).observations.observations h i).stop-(v:ℝ)
def target (p : Inputs) (k : ℕ) (h : History X k) (i : Fin (n+k)) : ℝ :=
  ((carrier (Base (0,p)) k).observations.observations h i).target-(v:ℝ)
def center (p : Inputs) (k : ℕ) (h : History X k) (i : Fin (n+k)) : UnitAddCircle :=
  NativeHeatSpan.unitCenter ((carrier (Base (0,p)) k).observations.observations h i).center

def lo (p : Inputs) (k : ℕ) (h : History X k) (j : Fin k) : ℝ :=lower (Base (0,p)) k h j-(v:ℝ)
def hi (p : Inputs) (k : ℕ) (h : History X k) (j : Fin k) : ℝ :=upper (Base (0,p)) k h j-(v:ℝ)
def leafPoint (p : Inputs) (k : ℕ) (h : History X k) (j : Fin k) : ControlledProfile.Domain :=
  (lo P A hA Λ v b hvb Z htarget hstop F hF hFm p k h j,space k h j)

def oldMatrices (p : Inputs) (k : ℕ) (h : History X k) :=
  PhysicalChainArrays.covariances (Base (0,p))
    ((carrier (Base (0,p)) k).observations.observations h)
    (ControlledFamilyProfileForest.oldProfile P Λ v p) k h

def oldDirections (p : Inputs) (k : ℕ) (h : History X k) :=
  PhysicalChainArrays.directions (Base (0,p))
    ((carrier (Base (0,p)) k).observations.observations h) k h

def oldLaw (p : Inputs) (k : ℕ) (h : History X k) :=
  Measure.pi (fun j=>multivariateGaussian (0 : WordRecursion.State (n+k))
    (oldMatrices P A hA Λ v b hvb Z htarget hstop F hF hFm p k h j))

def oldWeight (p : Inputs) (k : ℕ) (h : History X k) (y : Fin k→WordRecursion.State (n+k)) : ℝ :=
  ∏ j,MeasurableGaussianScores.secondScore
    (oldMatrices P A hA Λ v b hvb Z htarget hstop F hF hFm p k h j)
    (oldDirections P A hA Λ v b hvb Z htarget hstop F hF hFm p k h j) (y j)

def scaledRoot (p : Inputs) (k : ℕ) (h : History X k) (z : WordRecursion.State (n+k)) : ℝ :=
  (1/2:ℝ)^k*PhysicalChainArrays.initial (Base (0,p)) k h (fun i=>i) z

def coefficientLeaf (k : ℕ) (j : Fin k) (z : WordRecursion.State (n+k)) : ℝ :=
  A (z (leafIndex k (fun i=>i) j))

local notation "Sig" => sigma P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "Tar" => target P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "Cen" => center P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "Lo" => lo P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "Hi" => hi P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "LP" => leafPoint P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "Law" => oldLaw P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "Wgt" => oldWeight P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "Root" => scaledRoot P A hA Λ v b hvb Z htarget hstop F hF hFm
local notation "Leaf" => coefficientLeaf A (n:=n)

/-- The entire literal centered root/leaf word after the SAME old score
average, with its full positive residual at relative age q-v. -/
def value (p : Inputs) (k : ℕ) (h : History X k) (q : ℝ) (U D : CircleL2) (θ : ℝ) : ℝ :=
  gaussianAverage
    (ControlledFixedReserve.covariance P Λ p.1 p.2 (fixedProfile P Λ p.1 p.2 (Lo p k h) (Hi p k h))
      (Sig p k h) (Tar p k h) (StoppedGaussianScore.nativeCenter (Cen p k h)) (q-(v:ℝ)) θ)
    (WeightedBorelAverage.average (Law p k h) (Wgt p k h) (fun y=>∑ j,y j)
      (test Finset.univ (Root p k h) (Leaf k)
        (fun j=>ControlledFiniteWord.baselines P Λ p.1 p.2 (LP p k h) j θ)))
    (ControlledJointWeightedWord.jointMeanVector (Sig p k h) (Tar p k h) (Cen p k h) (q-(v:ℝ)) Λ U D θ)

/-- The covariance leg, the original-stop damped current-mean leg, and
EVERY omitted-leaf full-profile baseline derivative. -/
def mark (p : Inputs) (k : ℕ) (h : History X k) (q : ℝ) (U D : CircleL2) : ℝ→ℝ :=
  WeightedWordMarking.mark Finset.univ (Law p k h) (Wgt p k h) (fun y=>∑ j,y j)
    (ControlledFixedReserve.covariance P Λ p.1 p.2 (fixedProfile P Λ p.1 p.2 (Lo p k h) (Hi p k h))
      (Sig p k h) (Tar p k h) (StoppedGaussianScore.nativeCenter (Cen p k h)) (q-(v:ℝ)))
    (Root p k h) (Leaf k) (ControlledFiniteWord.baselines P Λ p.1 p.2 (LP p k h))
    (ControlledFiniteWord.baselineDerivatives P Λ p.1 p.2 (LP p k h))
    (ControlledFixedReserve.mark P Λ p.1 p.2 (fixedProfile P Λ p.1 p.2 (Lo p k h) (Hi p k h))
      (Sig p k h) (Tar p k h) (StoppedGaussianScore.nativeCenter (Cen p k h)) (q-(v:ℝ)))
    (PhysicalMeanRange.currentDirection (Tar p k h) (Cen p k h) (q-(v:ℝ)) U)
    (PhysicalMeanRange.dampedDirection (Sig p k h) (Tar p k h) (Cen p k h) (q-(v:ℝ)) Λ D)

/-- The exact canonical carrier-history three-leg FTC. The scalar
native root stop=terminal is a direct instance. Constants, original
stops, full baselines and fixed-old scores are retained explicitly. -/
theorem transfer (hΛ : 0≤Λ)
    (hsmall : ProfileStability.memoryConstant P.lower P.holder P.exponent*
      ProfileVolterra.powerConstant ((P.exponent-2)/4)*P.horizon^(P.exponent/4)≤1/2)
    (hroot : ∀ x i,(Z.observations x i).stop=(b:ℝ))
    (hspan : (b:ℝ)-(v:ℝ)≤P.horizon) (p : Inputs) (k : ℕ) (h : History X k)
    (q : ℝ) (hq : (v:ℝ)≤q) (hqt : q<(carrier (Base (0,p)) k).terminal h)
    (U D : CircleL2) :
    (∀ᵐ θ ∂volume,HasDerivAt (value P A hA Λ v b hvb Z htarget hstop F hF hFm p k h q U D)
      (mark P A hA Λ v b hvb Z htarget hstop F hF hFm p k h q U D θ) θ) ∧
    ∀ r t,IntervalIntegrable (mark P A hA Λ v b hvb Z htarget hstop F hF hFm p k h q U D) volume r t ∧
      (∫ θ in r..t,mark P A hA Λ v b hvb Z htarget hstop F hF hFm p k h q U D θ)=
      value P A hA Λ v b hvb Z htarget hstop F hF hFm p k h q U D t-
        value P A hA Λ v b hvb Z htarget hstop F hF hFm p k h q U D r := by
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
  exact ControlledJointWeightedWord.actual_joint_marked_transfer P hΛ (Sig p k h) (Tar p k h)
    (Cen p k h) (q-(v:ℝ)) (sub_nonneg.mpr hq) hgap hTh hs p.1 p.2 U D
    (fixedProfile P Λ p.1 p.2 (Lo p k h) (Hi p k h)) hold (half_lt_self P.lower_pos) holdb hsmall
    (Law p k h) (Wgt p k h) hw hwm (fun y=>∑ j,y j) hshift Finset.univ (LP p k h)
    (Root p k h) (Leaf k) hRm (fun j _=>ham j) ((1/2:ℝ)^k*K) (fun _=>M)
    (by positivity) (fun _ _=>hMn) hRb (fun j _=>hab j)

end SHE.ControlledFamilyThreeLeg
