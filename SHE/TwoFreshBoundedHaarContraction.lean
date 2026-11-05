module

public import SHE.TwoFreshBoundedEmptyWord
public import SHE.NativeCurrentCapInterpolation
public import SHE.HilbertColumns

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000

namespace SHE.TwoFreshBoundedHaarContraction
open MeasureTheory Set Real FiniteHaar
open scoped ENNReal

private theorem sqrt_cauchy {I:Type*}(a b:I→ℝ)(ha:∀i,0≤a i)(hb:∀i,0≤b i)
    (hsa:Summable a)(hsb:Summable b):
    Summable (fun i=>sqrt (a i)*sqrt (b i)) ∧
      (∑'i,sqrt (a i)*sqrt (b i))≤sqrt (∑'i,a i)*sqrt (∑'i,b i):=by
  have hma:Memℓp (fun i=>sqrt (a i)) 2:=by
    apply memℓp_gen
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two,Real.norm_eq_abs,
      abs_of_nonneg (sqrt_nonneg _),sq_sqrt (ha _)] using hsa
  have hmb:Memℓp (fun i=>sqrt (b i)) 2:=by
    apply memℓp_gen
    simpa only [ENNReal.toReal_ofNat,Real.rpow_two,Real.norm_eq_abs,
      abs_of_nonneg (sqrt_nonneg _),sq_sqrt (hb _)] using hsb
  let x:HilbertColumns.Space I ℝ:=⟨fun i=>sqrt (a i),hma⟩
  let y:HilbertColumns.Space I ℝ:=⟨fun i=>sqrt (b i),hmb⟩
  have hx:‖x‖=sqrt (∑'i,a i):=by
    rw [←Real.sqrt_sq (norm_nonneg x),HilbertColumns.norm_sq]
    congr 1
    apply tsum_congr
    intro i
    exact (sq_abs (sqrt (a i))).trans (sq_sqrt (ha i))
  have hy:‖y‖=sqrt (∑'i,b i):=by
    rw [←Real.sqrt_sq (norm_nonneg y),HilbertColumns.norm_sq]
    congr 1
    apply tsum_congr
    intro i
    exact (sq_abs (sqrt (b i))).trans (sq_sqrt (hb i))
  have hh:=lp.tsum_mul_le_mul_norm
    (show (2:ENNReal).toReal.HolderConjugate (2:ENNReal).toReal from Real.HolderConjugate.two_two) x y
  rw [hx,hy] at hh
  simpa only [x,y,Real.norm_eq_abs,abs_of_nonneg (sqrt_nonneg _)] using hh

private theorem sum_bound {I:Type*}(f a b:I→ℝ)(ha:∀i,0≤a i)(hb:∀i,0≤b i)
    (hsa:Summable a)(hsb:Summable b){C:ℝ}(hC:0≤C)
    (hpoint:∀i,|f i|≤C*(sqrt (a i)*sqrt (b i))):
    Summable f ∧ |∑'i,f i|≤C*(sqrt (∑'i,a i)*sqrt (∑'i,b i)):=by
  obtain ⟨hs,hbnd⟩:=sqrt_cauchy a b ha hb hsa hsb
  have hsmajor:Summable (fun i=>C*(sqrt (a i)*sqrt (b i))):=hs.mul_left C
  have hf:Summable f:=hsmajor.of_norm_bounded (fun i=>by simpa only [Real.norm_eq_abs] using hpoint i)
  refine ⟨hf,?_⟩
  calc
    _≤∑'i,|f i|:=by simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hf.norm
    _≤∑'i,C*(sqrt (a i)*sqrt (b i)):=hf.abs.tsum_le_tsum hpoint hsmajor
    _=C*(∑'i,sqrt (a i)*sqrt (b i)):=tsum_mul_left
    _≤_:=mul_le_mul_of_nonneg_left hbnd hC

open ProbabilityTheory StoppedGaussianFeatures StoppedGaussianScore StoppedFourier
  GaussianIncrement GaussianAssignmentBlocks ControlledOldIntervals OldIntervalCovariance
  GaussianDependentScores GaussianJointScoreMoments MeasurableGaussianScores
open scoped BigOperators
local instance twoFreshBoundedHaarContraction_period:Fact (0<2*π):=⟨by positivity⟩
local instance twoFreshBoundedHaarContraction_nativeSigma:MeasurableSpace CircleL2:=borel _
local instance twoFreshBoundedHaarContraction_nativeBorel:BorelSpace CircleL2:=⟨rfl⟩
variable {n d r m:ℕ}

/-- Complete original old-score assignment sum contracted over the SAME
countable Haar coordinates. Every untouched mean is allowed uniformly;
no stochastic offset cap is inserted or decorrelated. -/
theorem complete_word (P : CanonicalCovariance.ProfileParameters) (Λ : ℝ) (u d0 : CircleL2) (θ : ℝ)
    (q : ℝ) (hq : 0≤q) (σ target : Fin n→ℝ) (center : Fin n→HeatCircle)
    (hσ : ∀ i,0<σ i) (hσ1 : ∀ i,σ i≤1) (hages : ∀ i,σ i≤target i)
    (lo hi : Fin r→ℝ) (hlo : ∀ j,q≤lo j) (hlohi : ∀ j,lo j<hi j)
    (hstop : ∀ j i,σ i≤lo j ∨ hi j≤σ i)
    (hdisjoint : ∀ j l,j≠l→hi j≤lo l ∨ hi l≤lo j)
    (mean : State n) (D : Fin r→State n)
    (hD : ∀ j,D j∈(Matrix.toEuclideanCLM (𝕜:=ℝ)
      (familyCovariance σ target center (referenceProfile P Λ u d0) lo hi j)).range)
    (E V : HaarNode→State n) (hE : ∀j,E j∈(Matrix.toEuclideanCLM (𝕜:=ℝ)
      (NativeFirstScoreReserve.covariance P σ target center q)).range)
    (hV : ∀j,V j∈(Matrix.toEuclideanCLM (𝕜:=ℝ)
      (ControlledFixedReserve.covariance P Λ u d0
        (NativeFirstScoreReserve.oldProfile P (fixedProfile P Λ u d0 lo hi)) σ target center q θ)).range)
    (g : Fin d→Fin n) (leaf : Fin m→Fin n)
    (hnative : ∀ j,σ (leaf j)=target (leaf j)) (ht : ∀ j,target (leaf j)∈Ioc 0 P.horizon)
    (F : State d→ℝ) (hFm : Measurable F) {A0 ν : ℝ} (hA0 : 0≤A0) (hν : 0≤ν)
    (hf : ContDiff ℝ r F) (hfb : ∀ j,j≤r→∀ z,‖iteratedFDeriv ℝ j F z‖≤A0*ν^j)
    (hsE:Summable (fun j:HaarNode=>scoreVariance
      (NativeFirstScoreReserve.covariance P σ target center q) (E j)))
    (hsV:Summable (fun j:HaarNode=>scoreVariance
      (ControlledFixedReserve.covariance P Λ u d0
        (NativeFirstScoreReserve.oldProfile P (fixedProfile P Λ u d0 lo hi)) σ target center q θ) (V j))):
    let A:=familyCovariance σ target center (referenceProfile P Λ u d0) lo hi
    let R:=NativeFirstScoreReserve.covariance P σ target center q
    let C:=ControlledFixedReserve.covariance P Λ u d0
      (NativeFirstScoreReserve.oldProfile P (fixedProfile P Λ u d0 lo hi)) σ target center q θ
    let W:=fun j:HaarNode=>TwoFreshBoundedEmptyWord.value P Λ u d0 θ q
      σ target center lo hi mean false D (E j) (V j) g leaf F
    Summable W ∧ |∑'j,W j|≤sqrt (TwoFreshBoundedEmptyWord.momentConstant P r m 1)*
      ((∏j,scoreVariance (A j) (D j))*TwoFreshBoundedEmptyWord.total (d:=d) P lo hi (fun j=>target (leaf j)) A0 ν)*
      (sqrt (∑'j:HaarNode,scoreVariance R (E j))*sqrt (∑'j:HaarNode,scoreVariance C (V j))):=by
  intro A R C W
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
  let old:=∏j,scoreVariance (A j) (D j)
  let T:=TwoFreshBoundedEmptyWord.total (d:=d) P lo hi (fun j=>target (leaf j)) A0 ν
  let Cpacket:=sqrt (TwoFreshBoundedEmptyWord.momentConstant P r m 1)*(old*T)
  have hold:0≤old:=Finset.prod_nonneg (fun j _=>scoreVariance_nonneg (hA j) (hD j))
  have hT:0≤T:=TwoFreshBoundedEmptyWord.total_nonneg _ _ _ _ _ _
  have hE0(j:HaarNode):0≤scoreVariance R (E j):=scoreVariance_nonneg hR (hE j)
  have hV0(j:HaarNode):0≤scoreVariance C (V j):=scoreVariance_nonneg hC (hV j)
  have hpoint(j:HaarNode):|W j|≤Cpacket*(sqrt (scoreVariance R (E j))*sqrt (scoreVariance C (V j))):=by
    let K:=old*sqrt (scoreVariance R (E j))*sqrt (scoreVariance C (V j))
    have hK:0≤K:=mul_nonneg (mul_nonneg hold (sqrt_nonneg _)) (sqrt_nonneg _)
    have hgeom:|(∏i,scoreVariance (A i) (D i))*sqrt (scoreVariance R (E j))*
        GaussianDependentScores.scale false C (V j)|≤K:=by
      change |K|≤K
      rw [abs_of_nonneg hK]
    have hh:=TwoFreshBoundedEmptyWord.bound P Λ u d0 θ q hq σ target center hσ hσ1 hages
      lo hi hlo hlohi hstop hdisjoint mean false D hD (E j) (V j) (hE j) (hV j) g leaf hnative ht
      F hFm hA0 hν hf hfb 1 (by norm_num) K hK hgeom
    have hp:=NativeCurrentCapInterpolation.root_cap
      (TwoFreshBoundedEmptyWord.momentConstant_nonneg P r m 1) (mul_nonneg hK hT) 1 (by norm_num) hh
    norm_num only [Nat.mul_one,Nat.cast_ofNat] at hp
    apply hp.trans_eq
    dsimp only [Cpacket,K]
    simp only [sqrt_eq_rpow]
    ring
  exact sum_bound W (fun j=>scoreVariance R (E j)) (fun j=>scoreVariance C (V j))
    hE0 hV0 hsE hsV (mul_nonneg (sqrt_nonneg _) (mul_nonneg hold hT)) hpoint

end SHE.TwoFreshBoundedHaarContraction
