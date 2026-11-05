module

public import SHE.NativeFirstOmittedPointwise
public import SHE.NativeOmittedTimeTotal
public import SHE.MixedPastWordMoments

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section

namespace SHE.NativeOmittedCompleteWord
open Set MeasureTheory ProbabilityTheory Real StoppedGaussianFeatures StoppedGaussianScore
  StoppedFourier GaussianIncrement GaussianAssignmentBlocks ControlledOldIntervals OldIntervalCovariance
  GaussianDependentScores GaussianJointScoreMoments MeasurableGaussianScores
open scoped BigOperators
local instance nativeOmittedCompleteWord_periodPositive : Fact (0<2*π) := ⟨by positivity⟩
variable {X : Type*} [MeasurableSpace X] [MeasurableSpace CircleL2] [BorelSpace CircleL2]
variable {n d r m : ℕ}
open NativeFirstOmittedMoments

def momentConstant (P : CanonicalCovariance.ProfileParameters) (r m : ℕ) (j0 : Fin m) (b : ℕ) (C0 : ℝ) : ℝ :=
  ((1/2:ℝ)^r)^(2*b)*((assignments (m:=m+1) (List.finRange r)).length:ℝ)^(2*b-1)*
    ((assignments (m:=m+1) (List.finRange r)).map (fun choices=>
      max (NativeFirstOmittedMoments.constant P r m choices j0 b C0) 0)).sum

theorem momentConstant_nonneg (P : CanonicalCovariance.ProfileParameters) (r m : ℕ) (j0 : Fin m) (b : ℕ) (C0 : ℝ) :
    0 ≤ momentConstant P r m j0 b C0 := by
  unfold momentConstant
  apply mul_nonneg (by positivity)
  apply List.sum_nonneg
  intro x hx
  obtain ⟨cs,_,rfl⟩:=List.mem_map.mp hx
  exact le_max_right _ _

def value (P : CanonicalCovariance.ProfileParameters) (Λ : ℝ) (u d0 : CircleL2) (θ q : ℝ)
    (σ target : Fin n→ℝ) (center : Fin n→HeatCircle) (lo hi : Fin r→ℝ) (mean : State n)
    (D : Fin r→State n) (E : State n) (j0 : Fin m) (g : Fin d→Fin n)
    (leaf : Fin m→Fin n) (F : State d→ℝ) : ℝ :=
  (1/2:ℝ)^r*((assignments (m:=m+1) (List.finRange r)).map (fun choices=>
    if block choices j0.succ=[] then
      fibreAverage P Λ u d0 θ q σ target center lo hi mean D E g leaf choices j0 F else 0)).sum

/-- Deterministic pointwise all-order bound for the COMPLETE assignment
omitted-baseline sum. The native reserve retains its FIRST score;
the smaller remaining law stays UNSCORED. The Gaussian laws can vary with the past because this is
proved before any outer native probability average. Every block minimum,
original empty-leaf age and root clip is retained in the true time total. -/
theorem bound (P : CanonicalCovariance.ProfileParameters) (Λ : ℝ) (u d0 : CircleL2) (θ : ℝ)
    (q : ℝ) (hq : 0≤q) (σ target : Fin n→ℝ) (center : Fin n→HeatCircle)
    (hσ : ∀ i,0<σ i) (hσ1 : ∀ i,σ i≤1) (hages : ∀ i,σ i≤target i)
    (lo hi : Fin r→ℝ) (hlo : ∀ j,q≤lo j) (hlohi : ∀ j,lo j<hi j)
    (hstop : ∀ j i,σ i≤lo j ∨ hi j≤σ i)
    (hdisjoint : ∀ j l,j≠l→hi j≤lo l ∨ hi l≤lo j)
    (mean : State n) (D : Fin r→State n) (j0 : Fin m)
    (hD : ∀ j,D j∈(Matrix.toEuclideanCLM (𝕜:=ℝ)
      (familyCovariance σ target center (referenceProfile P Λ u d0) lo hi j)).range)
    (E : State n) (hE : E∈(Matrix.toEuclideanCLM (𝕜:=ℝ)
      (NativeFirstScoreReserve.covariance P σ target center q)).range)
    (g : Fin d→Fin n) (leaf : Fin m→Fin n)
    (hnative : ∀ j,σ (leaf j)=target (leaf j)) (ht : ∀ j,target (leaf j)∈Ioc 0 P.horizon)
    (F : State d→ℝ) (hFm : Measurable F) {A0 ν : ℝ} (hA0 : 0≤A0) (hν : 0≤ν)
    (hf : ContDiff ℝ r F) (hfb : ∀ j,j≤r→∀ z,‖iteratedFDeriv ℝ j F z‖≤A0*ν^j)
    (b : ℕ) (hb : 0<b) (K : ℝ) (hK : 0≤K)
    (hgeom : |(∏ j,scoreVariance
      (familyCovariance σ target center (referenceProfile P Λ u d0) lo hi j) (D j))*
        Real.sqrt (scoreVariance (NativeFirstScoreReserve.covariance P σ target center q) E)|≤K) :
    |value P Λ u d0 θ q σ target center lo hi mean D E j0 g leaf F|^(2*b)≤
      momentConstant P r m j0 b (FullResidualAssignedMoments.currentBudget P Λ u d0 θ target center leaf mean b)*
        (K*NativeOmittedTimeTotal.total (d:=d) P lo hi (fun j=>target (leaf j)) j0 A0 ν)^(2*b) := by
  let cs:=assignments (m:=m+1) (List.finRange r)
  let f:=fun choices=>if block choices j0.succ=[] then
    fibreAverage P Λ u d0 θ q σ target center lo hi mean D E g leaf choices j0 F else 0
  let budget:=FullResidualAssignedMoments.currentBudget P Λ u d0 θ target center leaf mean b
  let T:=NativeOmittedTimeTotal.total (d:=d) P lo hi (fun j=>target (leaf j)) j0 A0 ν
  have hT : 0≤T:=NativeOmittedTimeTotal.total_nonneg P lo hi _ j0 A0 ν
  have hpoint (choices) (hc : choices∈cs) :
      |f choices|^(2*b)≤max (constant P r m choices j0 b budget) 0*(K*T)^(2*b) := by
    by_cases hblock:block choices j0.succ=[]
    · have hnd : (choices.map Prod.fst).Nodup := by
        rw [assignment_coordinates _ _ hc]
        exact List.nodup_finRange r
      have hlen : (block choices 0).length≤r := by
        simpa only [Fintype.card_fin] using
          (List.Nodup.length_le_card (GaussianAssignmentBlocks.block_nodup choices hnd 0))
      have hh:=pointwise_even_moment P Λ u d0 θ q hq σ target center hσ hσ1 hages lo hi hlo hlohi
        hstop hdisjoint mean D hD E hE g leaf hnative ht choices hnd j0
        (fun j=>MinimumGapChoice.blockChoice lo hi choices j.succ)
        (fun j h=>MinimumGapChoice.blockChoice_mem lo hi choices j.succ h)
        F hFm hA0 hν (hf.of_le (by exact_mod_cast hlen)) (fun j hj=>hfb j (hj.trans hlen)) b hb
      let s:=(∏ j,scoreVariance
        (familyCovariance σ target center (referenceProfile P Λ u d0) lo hi j) (D j))*
        Real.sqrt (scoreVariance (NativeFirstScoreReserve.covariance P σ target center q) E)
      have hscale : |s*NativeOmittedTimeTotal.factor (d:=d) P lo hi
          (fun j=>target (leaf j)) choices j0 A0 ν|≤K*T := by
        rw [abs_mul]
        exact mul_le_mul hgeom (NativeOmittedTimeTotal.factor_le_total P lo hi _ choices j0 A0 ν hc)
          (abs_nonneg _) hK
      have hC : 0≤constant P r m choices j0 b budget := constant_nonneg P b choices j0
        (NormalizedLeafOffsets.budget_nonneg _ _ _ _ (fun j=>(ht j).1))
      simp only [f,hblock,ite_true,max_eq_left hC]
      refine hh.trans (mul_le_mul_of_nonneg_left ?_ hC)
      rw [←pow_abs_two_mul]
      convert! pow_le_pow_left₀ (abs_nonneg _) hscale (2*b) using 1
      simp only [s,NativeOmittedTimeTotal.factor,hblock,ite_true,mul_assoc]
    · simp only [f,hblock,ite_false,abs_zero,zero_pow (by omega:2*b≠0)]
      exact mul_nonneg (le_max_right _ _) ((even_two_mul b).pow_nonneg _)
  have hsum:=FiniteAssignmentMoments.abs_sum_pow_le cs f b hb
  have hterm : (cs.map (fun choices=>|f choices|^(2*b))).sum≤
      (cs.map (fun choices=>max (constant P r m choices j0 b budget) 0)).sum*(K*T)^(2*b) := by
    rw [←List.sum_map_mul_right]
    exact List.sum_le_sum (fun choices hc=>hpoint choices hc)
  have hfinal:=mul_le_mul_of_nonneg_left
    (hsum.trans (mul_le_mul_of_nonneg_left hterm (by positivity)))
    (show 0≤((1/2:ℝ)^r)^(2*b) by positivity)
  simpa only [value,abs_mul,abs_pow,abs_of_pos (by norm_num : (0:ℝ)<1/2),mul_pow,
    momentConstant,cs,f,budget,T,mul_assoc] using hfinal

end SHE.NativeOmittedCompleteWord

