module

public import SHE.BoundedResidualFields
public import SHE.MixedPastWordMoments

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section

namespace SHE.BoundedCompleteGaussianWord
open Set MeasureTheory ProbabilityTheory Real StoppedGaussianFeatures StoppedGaussianScore
  StoppedFourier GaussianIncrement GaussianAssignmentBlocks ControlledOldIntervals OldIntervalCovariance
  GaussianDependentScores GaussianJointScoreMoments MeasurableGaussianScores
open scoped BigOperators
local instance pointwiseCompleteGaussianWord_periodPositive : Fact (0<2*π) := ⟨by positivity⟩
variable {X : Type*} [MeasurableSpace X] [MeasurableSpace CircleL2] [BorelSpace CircleL2]
variable {n r m : ℕ}
open BoundedResidualAssignedMoments
open FullResidualAssignedMoments (currentBudget)

def value (P : CanonicalCovariance.ProfileParameters) (Λ : ℝ) (u d0 : CircleL2) (c : Domain→ℝ) (η q : ℝ)
    (σ target : Fin n→ℝ) (center : Fin n→HeatCircle) (lo hi : Fin r→ℝ) (mean : State n)
    (second : Bool) (D : Fin r→State n) (E : State n) (g : Fin 1→Fin n)
    (leaf : Fin m→Fin n) (F : State 1→ℝ) : ℝ :=
  (1/2:ℝ)^r*((assignments (m:=m+1) (List.finRange r)).map (fun choices=>
    fibreAverage P Λ u d0 c η q σ target center lo hi mean second D E g leaf choices F)).sum

/-- Deterministic pointwise all-order bound for the COMPLETE assignment
sum. The Gaussian laws can later vary with the past because this is
proved before any outer native probability average. Every block minimum,
original empty-leaf age and root clip is retained in the true time total. -/
theorem bound (P : CanonicalCovariance.ProfileParameters) (Λ : ℝ) (u d0 : CircleL2) (c : Domain→ℝ) (hc : Measurable c)
    (hcb : ∀ p,P.lower≤c p ∧ c p≤P.upper) (η : ℝ)
    (q : ℝ) (hq : 0≤q) (σ target : Fin n→ℝ) (center : Fin n→HeatCircle)
    (hσ : ∀ i,0<σ i) (hσ1 : ∀ i,σ i≤1) (hages : ∀ i,σ i≤target i)
    (lo hi : Fin r→ℝ) (hlo : ∀ j,q≤lo j) (hlohi : ∀ j,lo j<hi j)
    (hstop : ∀ j i,σ i≤lo j ∨ hi j≤σ i)
    (hdisjoint : ∀ j l,j≠l→hi j≤lo l ∨ hi l≤lo j)
    (mean : State n) (second : Bool) (D : Fin r→State n)
    (hD : ∀ j,D j∈(Matrix.toEuclideanCLM (𝕜:=ℝ)
      (familyCovariance σ target center (referenceProfile P Λ u d0) lo hi j)).range)
    (E : State n) (hE : E∈(Matrix.toEuclideanCLM (𝕜:=ℝ)
      (stoppedCovariance σ target center (BoundedWindowDecomposition.residual P Λ u d0 lo hi c) q)).range)
    (g : Fin 1→Fin n) (leaf : Fin m→Fin n)
    (hnative : ∀ j,σ (leaf j)=target (leaf j)) (ht : ∀ j,target (leaf j)∈Ioc 0 P.horizon)
    (F : State 1→ℝ) (hFm : Measurable F) {A0 ν : ℝ} (hA0 : 0≤A0) (hν : 0≤ν)
    (hf : ContDiff ℝ r F) (hfb : ∀ j,j≤r→∀ z,‖iteratedFDeriv ℝ j F z‖≤A0*ν^j)
    (b : ℕ) (hb : 0<b) (K : ℝ) (hK : 0≤K)
    (hgeom : |(∏ j,scoreVariance
      (familyCovariance σ target center (referenceProfile P Λ u d0) lo hi j) (D j))*
        scale second (stoppedCovariance σ target center (BoundedWindowDecomposition.residual P Λ u d0 lo hi c) q) E|≤K) :
    |value P Λ u d0 c η q σ target center lo hi mean second D E g leaf F|^(2*b)≤
      MixedPastWordMoments.momentConstant P r m b (currentBudget P Λ u d0 η target center leaf mean b)*
        (K*MixedPastWordMoments.total (d:=1) P lo hi (fun j=>target (leaf j)) A0 ν)^(2*b) := by
  have hcm:=hc
  let cs:=assignments (m:=m+1) (List.finRange r)
  let f:=fun choices=>fibreAverage P Λ u d0 c η q σ target center lo hi mean second D E g leaf choices F
  let budget:=currentBudget P Λ u d0 η target center leaf mean b
  let T:=MixedPastWordMoments.total (d:=1) P lo hi (fun j=>target (leaf j)) A0 ν
  have hT : 0≤T:=MixedPastWordMoments.total_nonneg P lo hi _ A0 ν
  have hpoint (choices) (hc : choices∈cs) :
      |f choices|^(2*b)≤max (constant P r m choices b budget) 0*(K*T)^(2*b) := by
    have hnd : (choices.map Prod.fst).Nodup := by
      rw [assignment_coordinates _ _ hc]
      exact List.nodup_finRange r
    have hlen : (block choices 0).length≤r := by
      simpa only [Fintype.card_fin] using
        (List.Nodup.length_le_card (GaussianAssignmentBlocks.block_nodup choices hnd 0))
    have hh:=pointwise_even_moment P Λ u d0 c hcm hcb η q hq σ target center hσ hσ1 hages lo hi hlo hlohi
      hstop hdisjoint mean second D hD E hE g leaf hnative ht choices hnd
      (fun j=>MinimumGapChoice.blockChoice lo hi choices j.succ)
      (fun j h=>MinimumGapChoice.blockChoice_mem lo hi choices j.succ h)
      F hFm hA0 hν (hf.of_le (by exact_mod_cast hlen)) (fun j hj=>hfb j (hj.trans hlen)) b hb
    let s:=(∏ j,scoreVariance
      (familyCovariance σ target center (referenceProfile P Λ u d0) lo hi j) (D j))*
      scale second (stoppedCovariance σ target center (BoundedWindowDecomposition.residual P Λ u d0 lo hi c) q) E
    have hscale : |s*MixedPastWordMoments.factor (d:=1) P lo hi (fun j=>target (leaf j)) choices A0 ν|≤K*T := by
      rw [abs_mul]
      exact mul_le_mul hgeom (MixedPastWordMoments.factor_le_total P lo hi _ A0 ν choices hc)
        (abs_nonneg _) hK
    have hC : 0≤constant P r m choices b budget := constant_nonneg P b choices
      (NormalizedLeafOffsets.budget_nonneg _ _ _ _ (fun j=>(ht j).1))
    rw [max_eq_left hC]
    refine hh.trans (mul_le_mul_of_nonneg_left ?_ hC)
    rw [←pow_abs_two_mul]
    convert! pow_le_pow_left₀ (abs_nonneg _) hscale (2*b) using 1
    simp only [s,MixedPastWordMoments.factor,mul_assoc]
  have hsum:=FiniteAssignmentMoments.abs_sum_pow_le cs f b hb
  have hterm : (cs.map (fun choices=>|f choices|^(2*b))).sum≤
      (cs.map (fun choices=>max (constant P r m choices b budget) 0)).sum*(K*T)^(2*b) := by
    rw [←List.sum_map_mul_right]
    exact List.sum_le_sum (fun choices hc=>hpoint choices hc)
  have hfinal:=mul_le_mul_of_nonneg_left
    (hsum.trans (mul_le_mul_of_nonneg_left hterm (by positivity)))
    (show 0≤((1/2:ℝ)^r)^(2*b) by positivity)
  simpa only [value,abs_mul,abs_pow,abs_of_pos (by norm_num : (0:ℝ)<1/2),mul_pow,
    MixedPastWordMoments.momentConstant,constant,FullResidualAssignedMoments.constant,cs,f,budget,T,mul_assoc] using hfinal

end SHE.BoundedCompleteGaussianWord

