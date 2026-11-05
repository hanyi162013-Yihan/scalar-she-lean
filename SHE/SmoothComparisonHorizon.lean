module

public import SHE.SmoothComparisonParameters
public import SHE.UniformFutureProfileScores
public import SHE.UniformPhysicalScoreForest

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace SHE.SmoothComparisonHorizon
open SmoothApproximation ScalarData GaussianProfile

theorem small_power_shrink {C θ t h : ℝ} (hC : 0≤C) (hθ : 0≤θ)
    (hh : 0≤h) (hht : h≤t) (ht : C*t^θ≤1/2) : C*h^θ≤1/2 :=
  (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hh hht hθ) hC).trans ht

/-- One actual positive profile horizon works for every coefficient
mollifier and both pointwise and spatial-L2 stability estimates. -/
theorem common_horizon (D : ScalarData) :
    ∃ T : ℝ,0<T ∧ T≤1 ∧
      contractionConstant D.ell D.holderConstant D.beta*T^(D.beta/4)≤1/2 ∧
      ProfileStability.memoryConstant ((TotalSmoothLimit.amplitude D)^2+D.ell) D.holderConstant D.beta*
        ProfileVolterra.powerConstant ((D.beta-2)/4)*T^(D.beta/4)≤1/2 ∧
      ProfileStability.memoryConstant ((TotalSmoothLimit.amplitude D)^2+D.ell) D.holderConstant D.beta*
        ProfileVolterra.powerConstant ((D.beta-1)/4)*T^(D.beta/4)≤1/2 := by
  let lo:=(TotalSmoothLimit.amplitude D)^2+D.ell
  have hlo : 0≤lo:=add_nonneg (sq_nonneg _) D.ell_pos.le
  have hθ : 0<D.beta/4:=by linarith [D.beta_pos]
  have hpoint : -1<(D.beta-2)/4:=by linarith [D.beta_pos]
  obtain ⟨a,ha,ha1,has⟩:=D.common_profile_horizon
  obtain ⟨b,hb,hb1,hbs⟩:=ProfileVolterra.exists_absorption_horizon hpoint
    (ProfileStability.memoryConstant_nonneg hlo D.holderConstant_nonneg) hθ
  obtain ⟨c,hc,hc1,hcs⟩:=ProfileStability.exists_l2_stability_horizon hlo D.holderConstant_nonneg D.beta_pos
  let T:=min a (min b c)
  have hT : 0<T:=lt_min ha (lt_min hb hc)
  have hTa : T≤a:=min_le_left _ _
  have hTb : T≤b:=(min_le_right _ _).trans (min_le_left _ _)
  have hTc : T≤c:=(min_le_right _ _).trans (min_le_right _ _)
  refine ⟨T,hT,hTa.trans ha1,?_,?_,?_⟩
  · exact small_power_shrink (contractionConstant_nonneg D.ell_pos.le D.holderConstant_nonneg)
      hθ.le hT.le hTa has
  · exact small_power_shrink
      (mul_nonneg (ProfileStability.memoryConstant_nonneg hlo D.holderConstant_nonneg)
        (ProfileVolterra.powerConstant_pos hpoint).le) hθ.le hT.le hTb hbs
  · exact small_power_shrink
      (mul_nonneg (ProfileStability.memoryConstant_nonneg hlo D.holderConstant_nonneg)
        (ProfileVolterra.powerConstant_pos (by linarith [D.beta_pos] : -1<(D.beta-1)/4)).le)
      hθ.le hT.le hTc hcs

/-- The finite word depth is chosen first. A single positive physical
window then satisfies every fresh and old collision-uniform span bound
up to that depth, independently of all coefficient/root cutoffs. -/
theorem common_word_horizon {T : ℝ} (hT : 0<T) (N : ℕ) :
    ∃ h : ℝ,0<h ∧ h≤T ∧
      (∀ j,j≤N→h≤UniformFutureProfileScores.horizon (1+j)) ∧
      (∀ j,j<N→h≤PhysicalScoreChain.uniformHorizon 1 j) := by
  induction N with
  | zero=>
    refine ⟨min T (UniformFutureProfileScores.horizon 1),
      lt_min hT (UniformFutureProfileScores.horizon_pos 1),min_le_left _ _,?_,?_⟩
    · intro j hj
      have : j=0:=by omega
      subst j
      exact min_le_right _ _
    · intro j hj
      omega
  | succ N ih=>
    obtain ⟨a,ha,haT,haf,hao⟩:=ih
    let h:=min a (min (UniformFutureProfileScores.horizon (1+(N+1))) (PhysicalScoreChain.uniformHorizon 1 N))
    have hha : h≤a:=min_le_left _ _
    have hhf : h≤UniformFutureProfileScores.horizon (1+(N+1)):=
      (min_le_right _ _).trans (min_le_left _ _)
    have hho : h≤PhysicalScoreChain.uniformHorizon 1 N:=
      (min_le_right _ _).trans (min_le_right _ _)
    refine ⟨h,lt_min ha (lt_min (UniformFutureProfileScores.horizon_pos _)
      (PhysicalScoreChain.uniformHorizon_pos _ _)),hha.trans haT,?_,?_⟩
    · intro j hj
      by_cases hjN : j≤N
      · exact hha.trans (haf j hjN)
      · have : j=N+1:=by omega
        subst j
        exact hhf
    · intro j hj
      by_cases hjN : j<N
      · exact hha.trans (hao j hjN)
      · have : j=N:=by omega
        subst j
        exact hho

end SHE.SmoothComparisonHorizon
