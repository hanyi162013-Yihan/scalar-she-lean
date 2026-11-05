module

public import SHE.FullResidualAssignedMoments
public import SHE.NativeFirstScoreReserve
public import SHE.TwoFreshGaussianFractions

public import SHE.OffsetAssignedLeafMoments
public import SHE.GaussianJointScoreMoments
public import SHE.DependentWordMoments

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
noncomputable section

namespace SHE.TwoFreshFullResidualMoments
open Set MeasureTheory ProbabilityTheory Real StoppedGaussianFeatures StoppedGaussianScore
  StoppedFourier GaussianIncrement GaussianAssignmentBlocks ControlledOldIntervals OldIntervalCovariance
  GaussianDependentScores GaussianJointScoreMoments MeasurableGaussianScores
open scoped BigOperators
local instance fullResidualAssignedMoments_periodPos : Fact (0 < 2 * π) := ⟨by positivity⟩
variable {Ω : Type*} [MeasurableSpace Ω] {n d r m : ℕ}

def constant (P : CanonicalCovariance.ProfileParameters) (r m : ℕ)
    (choices : List (Fin r × Fin (m+1))) (b : ℕ) (C0 : ℝ) : ℝ :=
  GaussianAudit.secondScoreMoment (b*(m+2))^r*(productMomentConstant (b*(m+2)))^2+
    ControlledAssignedRoot.constant (b*(m+2)) choices 0+
      ∑ j : Fin m,OffsetAssignedLeafMoments.leafConstant P (b*(m+2)) C0 choices j.succ

/-- Both new Gaussian fractions remain independent score carriers;
every test factor sees their SUM, hence the original full residual law. -/
def collapse (z:Ω×((Fin r→State n)×(State n×State n))):Ω×((Fin r→State n)×State n):=
  (z.1,(z.2.1,z.2.2.1+z.2.2.2))

def word (second:Bool) (A:Fin r→Matrix (Fin n) (Fin n) ℝ) (D:Fin r→State n)
    (R C:Matrix (Fin n) (Fin n) ℝ) (E V:State n) (choices:List (Fin r×Fin (m+1)))
    (a:ℝ→ℝ) (F:State d→ℝ) (mean:Ω→State n) (g:Fin d→Fin n)
    (leaf:Fin m→Fin n) (baseline:Fin m→ℝ) (z:Ω×((Fin r→State n)×(State n×State n))):ℝ:=
  TwoFreshGaussianFractions.scores second A D R C E V z.2*
    VectorControlledRoot.value choices 0 F (mean z.1) g (collapse z).2*
      ∏j,ControlledAssignedLeaf.leaf choices j.succ a (mean z.1) (leaf j) (baseline j) (collapse z).2

theorem joint_even_moment (μ : Measure Ω) [IsProbabilityMeasure μ]
    (P : CanonicalCovariance.ProfileParameters) (Λ : ℝ) (u d0 : CircleL2) (θ : ℝ)
    (q : ℝ) (hq : 0 ≤ q) (σ target : Fin n → ℝ) (center : Fin n → HeatCircle)
    (hσ : ∀ i,0 < σ i) (hσ1 : ∀ i,σ i ≤ 1) (hages : ∀ i,σ i ≤ target i)
    (lo hi : Fin r → ℝ) (hlo : ∀ j,q ≤ lo j) (hlohi : ∀ j,lo j < hi j)
    (hstop : ∀ j i,σ i ≤ lo j ∨ hi j ≤ σ i)
    (hdisjoint : ∀ j l,j ≠ l → hi j ≤ lo l ∨ hi l ≤ lo j)
    (mean : Ω → State n) (hm : Measurable mean) (second : Bool) (D : Fin r → State n)
    (hD : ∀ j,D j ∈ (Matrix.toEuclideanCLM (𝕜:=ℝ)
      (familyCovariance σ target center (referenceProfile P Λ u d0) lo hi j)).range)
    (E V : State n) (hE : E ∈ (Matrix.toEuclideanCLM (𝕜:=ℝ)
      (NativeFirstScoreReserve.covariance P σ target center q)).range)
    (hV : V ∈ (Matrix.toEuclideanCLM (𝕜:=ℝ)
      (ControlledFixedReserve.covariance P Λ u d0
        (NativeFirstScoreReserve.oldProfile P (fixedProfile P Λ u d0 lo hi)) σ target center q θ)).range)
    (g : Fin d → Fin n) (leaf : Fin m → Fin n)
    (hnative : ∀ j,σ (leaf j)=target (leaf j)) (ht : ∀ j,target (leaf j) ∈ Ioc 0 P.horizon)
    (choices : List (Fin r × Fin (m+1))) (hnd : (choices.map Prod.fst).Nodup)
    (chosen : ∀ j : Fin m,block choices j.succ ≠ [] → Fin r)
    (hchosen : ∀ j h,chosen j h ∈ block choices j.succ)
    (F : State d → ℝ) (hFm : Measurable F) {A0 ν : ℝ} (hA0 : 0 ≤ A0) (hν : 0 ≤ ν)
    (hf : ContDiff ℝ (block choices 0).length F)
    (hfb : ∀ j,j ≤ (block choices 0).length → ∀ z,‖iteratedFDeriv ℝ j F z‖ ≤ A0*ν^j)
    (b : ℕ) (hb0 : 0 < b) (C0 : ℝ) (hC0 : 0 ≤ C0)
    (hoffset : ∀ j,Integrable (fun ω => |mean ω (leaf j)-ControlledProfile.mean Λ u d0
        (θ,(target (leaf j),center (leaf j)))|^(((2*(b*(m+2)):ℕ):ℝ)*P.exponent)) μ ∧
      (∫ ω,|mean ω (leaf j)-ControlledProfile.mean Λ u d0 (θ,(target (leaf j),center (leaf j)))|^
        (((2*(b*(m+2)):ℕ):ℝ)*P.exponent) ∂μ) ≤ C0*(target (leaf j))^((b*(m+2):ℕ)*P.exponent/2)) :
    let A := familyCovariance σ target center (referenceProfile P Λ u d0) lo hi
    let R := NativeFirstScoreReserve.covariance P σ target center q
    let C := ControlledFixedReserve.covariance P Λ u d0
      (NativeFirstScoreReserve.oldProfile P (fixedProfile P Λ u d0 lo hi)) σ target center q θ
    let νG := (Measure.pi (fun j => multivariateGaussian (0 : State n) (A j))).prod
      ((multivariateGaussian (0 : State n) R).prod (multivariateGaussian (0 : State n) C))
    let W := word second A D R C E V choices P.coefficient F mean g leaf
      (fun j => ControlledProfile.profile P Λ u d0 (θ,(target (leaf j),center (leaf j))))
    Integrable (fun z => |W z|^(2*b)) (μ.prod νG) ∧
      (∫ z,|W z|^(2*b) ∂μ.prod νG) ≤ constant P r m choices b C0*
        (((∏ j,scoreVariance (A j) (D j))*Real.sqrt (scoreVariance R E)*scale second C V)*
          VectorPhysicalRoot.scale choices 0 lo hi A0 ν (P.lower/2) d*
            ∏ j,NativeAssignedLeafMoments.leafScale P choices j.succ lo hi (target (leaf j)) (chosen j))^(2*b) := by
  intro A R C νG W
  let B:=ControlledFixedReserve.covariance P Λ u d0 (fixedProfile P Λ u d0 lo hi) σ target center q θ
  let νB:=(Measure.pi (fun j=>multivariateGaussian (0:State n) (A j))).prod
    (multivariateGaussian (0:State n) B)
  let Score:=fun z:Ω×((Fin r→State n)×(State n×State n))=>TwoFreshGaussianFractions.scores second A D R C E V z.2
  let Root0:=fun z:Ω×((Fin r→State n)×State n)=>VectorControlledRoot.value choices 0 F (mean z.1) g z.2
  let Leaf0:=fun j:Fin m=>fun z:Ω×((Fin r→State n)×State n)=>
    ControlledAssignedLeaf.leaf choices j.succ P.coefficient (mean z.1) (leaf j)
      (ControlledProfile.profile P Λ u d0 (θ,(target (leaf j),center (leaf j)))) z.2
  let Root:=fun z:Ω×((Fin r→State n)×(State n×State n))=>Root0 (collapse z)
  let Leaf:=fun j:Fin m=>fun z:Ω×((Fin r→State n)×(State n×State n))=>Leaf0 j (collapse z)
  have hA(j:Fin r):(A j).PosSemidef:=covariance_posSemidef σ target center hages _
    (referenceProfile_measurable P Λ u d0)
    (fun p=>⟨(mul_nonneg (fraction_pos P).le P.lower_pos.le).trans (referenceProfile_bounds P Λ u d0 p).1,
      (referenceProfile_bounds P Λ u d0 p).2⟩) (lo j) (hi j)
  have hR:R.PosSemidef:=NativeFirstScoreReserve.covariance_posSemidef P σ target center hages q
  have hCold:=fixedProfile_bounds P Λ u d0 lo hi hdisjoint
  have hCm:Measurable (ControlledFixedReserve.coefficient P Λ u d0
      (NativeFirstScoreReserve.oldProfile P (fixedProfile P Λ u d0 lo hi)) θ):=
    ((ControlledProfile.profile_measurable P Λ u d0).comp (measurable_const.prodMk measurable_id)).sub
      (NativeFirstScoreReserve.oldProfile_measurable P (fixedProfile_measurable P Λ u d0 lo hi))
  have hC:C.PosSemidef:=StoppedCovarianceSplit.covariance_posSemidef σ target center hages q hCm
    (fun p=>⟨(by have :=P.lower_pos;positivity:0≤3*P.lower/8).trans
      (NativeFirstScoreReserve.residual_bounds P Λ u d0 hCold θ p).1,
      (NativeFirstScoreReserve.residual_bounds P Λ u d0 hCold θ p).2⟩)
  have heq:R+C=B:=NativeFirstScoreReserve.covariance_split P Λ u d0
    (fixedProfile_measurable P Λ u d0 lo hi) hCold σ target center hσ hσ1 hages q hq θ
  have hmerge:MeasurePreserving (collapse (Ω:=Ω) (r:=r) (n:=n)) (μ.prod νG) (μ.prod νB):=by
    have hp:=(MeasurePreserving.id μ).prod
      (TwoFreshGaussianFractions.merge_preserving (Measure.pi (fun j=>multivariateGaussian (0:State n) (A j))) hR hC)
    rw [heq] at hp
    exact hp
  have hSm:Measurable Score:=by
    unfold Score TwoFreshGaussianFractions.scores
    apply Measurable.mul
    · apply Measurable.mul
      · exact Finset.measurable_prod Finset.univ (fun j _=>
          (factor_measurable true (A j) (D j)).comp ((measurable_pi_apply j).comp measurable_snd.fst))
      · exact (factor_measurable false R E).comp measurable_snd.snd.fst
    · exact (factor_measurable second C V).comp measurable_snd.snd.snd
  have hR0m:Measurable Root0:=ParametricAssignedMoments.root_measurable choices 0 F hFm mean hm g
  have hL0m(j:Fin m):Measurable (Leaf0 j):=ParametricAssignedMoments.leaf_measurable choices j.succ
    P.coefficient P.measurable mean hm (leaf j) _
  have hRm:Measurable Root:=hR0m.comp hmerge.measurable
  have hLm(j:Fin m):Measurable (Leaf j):=(hL0m j).comp hmerge.measurable
  have pull(f:Ω×((Fin r→State n)×State n)→ℝ)(hf:Measurable f)(p:ℕ)
      (hi:Integrable (fun z=>|f z|^(2*p)) (μ.prod νB)):
      Integrable (fun z=>|f (collapse z)|^(2*p)) (μ.prod νG) ∧
        (∫z,|f (collapse z)|^(2*p) ∂μ.prod νG)=(∫z,|f z|^(2*p) ∂μ.prod νB):=by
    refine ⟨(hmerge.integrable_comp (hf.norm.pow_const _).aestronglyMeasurable).mpr hi,?_⟩
    have hp:=integral_map (μ:=μ.prod νG) hmerge.measurable.aemeasurable
      (hf.norm.pow_const (2*p)).aestronglyMeasurable
    rw [hmerge.map_eq] at hp
    simpa only [Real.norm_eq_abs] using hp.symm
  have hs0:=TwoFreshGaussianFractions.scores_even_moment second A hA D hD R C hR hC E V hE hV (b*(m+2))
  have hs:=UniformFiberMoments.even_moment μ νG Score hSm (b*(m+2))
    (((GaussianAudit.secondScoreMoment (b*(m+2)))^r*(productMomentConstant (b*(m+2)))^2)*
      ((∏j,scoreVariance (A j) (D j))*Real.sqrt (scoreVariance R E)*scale second C V)^(2*(b*(m+2))))
    (fun _=>hs0.1) (fun _=>hs0.2)
  have hr0:=ParametricAssignedMoments.root_even_moment μ P Λ u d0 lo hi σ target center hσ hσ1 hages
    (fun j=>hq.trans (hlo j)) hlohi hstop B mean hm g choices hnd 0 F hFm hA0 hν hf hfb
    (b*(m+2)) (Nat.mul_pos hb0 (by omega))
  have hrp:=pull Root0 hR0m (b*(m+2)) hr0.1
  have hr:Integrable (fun z=>|Root z|^(2*(b*(m+2)))) (μ.prod νG) ∧
      (∫z,|Root z|^(2*(b*(m+2))) ∂μ.prod νG)≤ControlledAssignedRoot.constant (b*(m+2)) choices 0*
        (VectorPhysicalRoot.scale choices 0 lo hi A0 ν (P.lower/2) d)^(2*(b*(m+2))):=
    ⟨hrp.1,hrp.2.trans_le hr0.2⟩
  have hl(j:Fin m):Integrable (fun z=>|Leaf j z|^(2*(b*(m+2)))) (μ.prod νG) ∧
      (∫z,|Leaf j z|^(2*(b*(m+2))) ∂μ.prod νG)≤OffsetAssignedLeafMoments.leafConstant P (b*(m+2)) C0 choices j.succ*
        (NativeAssignedLeafMoments.leafScale P choices j.succ lo hi (target (leaf j)) (chosen j))^(2*(b*(m+2))):=by
    have hl0:=OffsetAssignedLeafMoments.even_moment μ P Λ u d0 θ σ target center hσ hσ1 hages
      hq lo hi hlo hlohi hstop hdisjoint mean hm (leaf j) (hnative j) (ht j) choices hnd j.succ
      (chosen j) (hchosen j) (b*(m+2)) C0 (hoffset j)
    have hlp:=pull (Leaf0 j) (hL0m j) (b*(m+2)) hl0.1
    exact ⟨hlp.1,hlp.2.trans_le hl0.2⟩
  have hLS(j:Fin m):0≤NativeAssignedLeafMoments.leafScale P choices j.succ lo hi (target (leaf j)) (chosen j):=by
    unfold NativeAssignedLeafMoments.leafScale
    split_ifs
    · exact mul_nonneg P.holder_nonneg (rpow_nonneg (ht j).1.le _)
    · exact mul_nonneg (mul_nonneg (mul_nonneg (by positivity) P.holder_nonneg)
        (rpow_nonneg (mul_nonneg ProfileVariance.upperConstant_pos.le (half_pos P.lower_pos).le) _))
        (rpow_nonneg (sub_pos.mpr (hlohi _)).le _)
  simp only [←Nat.mul_assoc] at hs hr hl
  exact DependentWordMoments.word_even_moment (μ.prod νG) Score Root Leaf hSm hRm hLm
    ((∏j,scoreVariance (A j) (D j))*Real.sqrt (scoreVariance R E)*scale second C V)
    (VectorPhysicalRoot.scale choices 0 lo hi A0 ν (P.lower/2) d)
    (fun j=>NativeAssignedLeafMoments.leafScale P choices j.succ lo hi (target (leaf j)) (chosen j))
    (mul_nonneg (mul_nonneg (Finset.prod_nonneg (fun j _=>scoreVariance_nonneg (hA j) (hD j))) (Real.sqrt_nonneg _))
      (scale_nonneg hC hV second))
    (VectorControlledRoot.scale_nonneg P choices 0 lo hi (fun j=>(hlohi j).le) hA0 hν d) hLS
    _ _ _ (mul_nonneg (pow_nonneg (GaussianAudit.secondScoreMoment_nonneg _) _)
      (sq_nonneg (productMomentConstant _)))
    (ControlledAssignedRoot.constant_nonneg _ _ _)
    (fun j=>OffsetAssignedLeafMoments.leafConstant_nonneg P _ hC0 choices j.succ)
    b hs.1 hr.1 (fun j=>(hl j).1) hs.2 hr.2 (fun j=>(hl j).2)

end SHE.TwoFreshFullResidualMoments
