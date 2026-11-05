module

public import SHE.TwoFreshControlledFields
public import SHE.SignedInputMoments
public import SHE.TwoFreshCompleteWord

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section

namespace SHE.TwoFreshCovarianceInput
open Set MeasureTheory ProbabilityTheory Real StoppedGaussianFeatures StoppedGaussianScore
  StoppedFourier GaussianIncrement GaussianAssignmentBlocks ControlledOldIntervals OldIntervalCovariance
  GaussianDependentScores GaussianJointScoreMoments MeasurableGaussianScores
open scoped BigOperators
local instance twoFreshCovarianceInput_periodPositive : Fact (0<2*π) := ⟨by positivity⟩
variable {X : Type*} [MeasurableSpace X] [MeasurableSpace CircleL2] [BorelSpace CircleL2]
variable {n d r m : ℕ}
open TwoFreshFullResidualMoments

/-- Genuine pathwise signed-input density Jensen for the COMPLETE
all-order Gaussian word. The positive input mass is kept separate from
the sharp assignment time total; the actual offset budget is kept
separate from both. -/
theorem bound (νX : Measure X) [SFinite νX]
    (P : CanonicalCovariance.ProfileParameters) (Λ : ℝ) (u d0 : CircleL2) (θ : ℝ)
    (q : ℝ) (hq : 0≤q) (σ target : Fin n→ℝ) (center : Fin n→HeatCircle)
    (hσ : ∀ i,0<σ i) (hσ1 : ∀ i,σ i≤1) (hages : ∀ i,σ i≤target i)
    (lo hi : Fin r→ℝ) (hlo : ∀ j,q≤lo j) (hlohi : ∀ j,lo j<hi j)
    (hstop : ∀ j i,σ i≤lo j ∨ hi j≤σ i)
    (hdisjoint : ∀ j l,j≠l→hi j≤lo l ∨ hi l≤lo j)
    (mean : State n) (D : Fin r→State n)
    (hD : ∀ j,D j∈(Matrix.toEuclideanCLM (𝕜:=ℝ)
      (familyCovariance σ target center (referenceProfile P Λ u d0) lo hi j)).range)
    (E : State n) (hE : E∈(Matrix.toEuclideanCLM (𝕜:=ℝ)
      (NativeFirstScoreReserve.covariance P σ target center q)).range)
    (row : X→State n) (hrow : Measurable row)
    (hB : (ControlledFixedReserve.covariance P Λ u d0 (NativeFirstScoreReserve.oldProfile P (fixedProfile P Λ u d0 lo hi))
      σ target center q θ).PosSemidef)
    (hrowRange : ∀ᵐ x ∂νX,row x∈(Matrix.toEuclideanCLM (𝕜:=ℝ)
      (ControlledFixedReserve.covariance P Λ u d0 (NativeFirstScoreReserve.oldProfile P (fixedProfile P Λ u d0 lo hi))
        σ target center q θ)).range)
    (g : Fin d→Fin n) (leaf : Fin m→Fin n)
    (hnative : ∀ j,σ (leaf j)=target (leaf j)) (ht : ∀ j,target (leaf j)∈Ioc 0 P.horizon)
    (F : State d→ℝ) (hFm : Measurable F) {A0 ν : ℝ} (hA0 : 0≤A0) (hν : 0≤ν)
    (hf : ContDiff ℝ r F) (hfb : ∀ j,j≤r→∀ z,‖iteratedFDeriv ℝ j F z‖≤A0*ν^j)
    (b : ℕ) (hb : 0<b) (e : X→ℝ) (he : Measurable e)
    (hEnergy : Integrable (fun x=>|e x| *scoreVariance
      (ControlledFixedReserve.covariance P Λ u d0 (NativeFirstScoreReserve.oldProfile P (fixedProfile P Λ u d0 lo hi))
        σ target center q θ) (row x)) νX)
    (K : ℝ) (hK : 0≤K)
    (hgeom : |∏ j,scoreVariance
      (familyCovariance σ target center (referenceProfile P Λ u d0) lo hi j) (D j)|≤K) :
    let B := ControlledFixedReserve.covariance P Λ u d0 (NativeFirstScoreReserve.oldProfile P (fixedProfile P Λ u d0 lo hi))
      σ target center q θ
    |(1/2:ℝ)*∫ x,e x*TwoFreshCompleteWord.value P Λ u d0 θ q
        σ target center lo hi mean true D E (row x) g leaf F ∂νX|^(2*b)≤
      TwoFreshCompleteWord.momentConstant P r m b (currentBudget P Λ u d0 θ target center leaf mean b)*
        (((1/2:ℝ)*K*Real.sqrt (scoreVariance
          (NativeFirstScoreReserve.covariance P σ target center q) E)*MixedPastWordMoments.total (d:=d) P lo hi (fun j=>target (leaf j)) A0 ν)*
          ∫ x,|e x| *scoreVariance B (row x) ∂νX)^(2*b) := by
  intro B
  let G : Unit×X→ℝ := fun z=>TwoFreshCompleteWord.value P Λ u d0 θ q
    σ target center lo hi mean true D E (row z.2) g leaf F
  let V : X→ℝ := fun x=>scoreVariance B (row x)
  let C:=TwoFreshCompleteWord.momentConstant P r m b (currentBudget P Λ u d0 θ target center leaf mean b)
  let N:=Real.sqrt (scoreVariance (NativeFirstScoreReserve.covariance P σ target center q) E)
  let T:=MixedPastWordMoments.total (d:=d) P lo hi (fun j=>target (leaf j)) A0 ν
  have hN : 0≤N:=Real.sqrt_nonneg _
  have hKN : 0≤K*N:=mul_nonneg hK hN
  have hC : 0≤C:=TwoFreshCompleteWord.momentConstant_nonneg _ _ _ _ _
  have hT : 0≤T:=MixedPastWordMoments.total_nonneg P lo hi _ A0 ν
  have hG : Measurable G := by
    let cs:=assignments (m:=m+1) (List.finRange r)
    have heq : G=(fun z : Unit×X=>(1/2:ℝ)^r*∑ j : Fin cs.length,
      fibreAverage P Λ u d0 θ q σ target center lo hi mean true D E (row z.2) g leaf (cs.get j) F) :=
      funext (fun _=>congrArg (fun a:ℝ=>(1/2:ℝ)^r*a) (FiniteAssignmentMoments.map_sum_eq_fin cs _))
    rw [heq]
    apply Measurable.const_mul
    apply Finset.measurable_sum
    intro j _
    have hh:=TwoFreshControlledFields.fibreAverage_measurable P Λ θ q
      (fun _ : X=>u) (fun _ : X=>d0) measurable_const measurable_const σ target center lo hi
      (fun _ : X=>mean) measurable_const true (fun _=>D) (fun _=>measurable_const) (fun _=>E) row measurable_const hrow
      g leaf (cs.get j) F hFm
    exact hh.comp measurable_snd
  have hV : Measurable V := by
    convert! scoreVariance_measurable.comp (measurable_const.prodMk hrow) using 1
  have hV0 : ∀ᵐ x ∂νX,0≤V x:=hrowRange.mono (fun _ hx=>scoreVariance_nonneg hB hx)
  have hpoint : ∀ᵐ x ∂νX,|G ((),x)|^(2*b)≤C*(V x*(K*N*T))^(2*b) := by
    filter_upwards [hrowRange,hV0] with x hx hv
    have hgeom' : |(∏ j,scoreVariance
        (familyCovariance σ target center (referenceProfile P Λ u d0) lo hi j) (D j))*
        N*scale true B (row x)|≤V x*(K*N) := by
      change |((∏ j,scoreVariance _ (D j))*N)*V x|≤_
      rw [abs_mul,abs_mul,abs_of_nonneg hN,abs_of_nonneg hv]
      exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hgeom hN) hv).trans_eq (by ring)
    have hh:=TwoFreshCompleteWord.bound P Λ u d0 θ q hq σ target center hσ hσ1 hages
      lo hi hlo hlohi hstop hdisjoint mean true D hD E (row x) hE hx g leaf hnative ht F hFm hA0 hν hf hfb
      b hb (V x*(K*N)) (mul_nonneg hv hKN) hgeom'
    simpa only [G,C,T,N,mul_assoc] using hh
  have hi : ∀ᵐ x ∂νX,Integrable (fun w : Unit=>|G (w,x)|^(2*b)) (Measure.dirac ()) :=
    ae_of_all _ (fun x=>by simpa only [G] using (integrable_const
      (|TwoFreshCompleteWord.value P Λ u d0 θ q σ target center lo hi mean true D E (row x)
        g leaf F|^(2*b)) : Integrable (fun _ : Unit=>_) (Measure.dirac ())))
  have hbnd : ∀ᵐ x ∂νX,(∫ w : Unit,|G (w,x)|^(2*b) ∂Measure.dirac ())≤C*(V x*(K*N*T))^(2*b) := by
    simpa only [integral_dirac] using hpoint
  have hh:=SignedInputMoments.weighted_even_moment (Measure.dirac ()) νX G hG V e hV he
    hV0 hEnergy (mul_nonneg hKN hT) hC b hb hi hbnd
  have hp : |(1/2:ℝ)*∫ x,e x*G ((),x) ∂νX|^(2*b)=
      (1/2:ℝ)^(2*b)*|∫ x,e x*G ((),x) ∂νX|^(2*b) := by
    rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<1/2),mul_pow]
  rw [hp]
  have hf0:=mul_le_mul_of_nonneg_left (by simpa only [integral_dirac] using hh.2)
    (show 0≤(1/2:ℝ)^(2*b) by positivity)
  convert! hf0 using 1 <;> simp only [mul_pow] <;> ring

end SHE.TwoFreshCovarianceInput

