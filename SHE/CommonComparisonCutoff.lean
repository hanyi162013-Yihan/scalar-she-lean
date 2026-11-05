module
public import SHE.DefectDyadicComparableCutoff
public import SHE.FiniteNativeGaussianCutoff
public import SHE.NativeUniversalConstants
public import SHE.UniformFutureProfileScores
public import SHE.NativeTwoPointCovariance
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace SHE.CommonComparisonCutoff
open Real Filter Topology
open scoped NNReal
variable (m W:ℝ)(hm:0<m)(hW:0≤W)(ρ:ℝ)(hρ:0<ρ)(hρhalf:ρ<1/2)
variable (D:SmoothApproximation.ScalarData){T:ℝ}(hT:0<T)(hT1:T≤1)
  (hsmall:GaussianProfile.contractionConstant D.ell D.holderConstant D.beta*T^(D.beta/4)≤1/2)
local notation "Smooth"=>ControlledSmoothLimit.smoothTotalParameters D hT hT1 hsmall

/-- One lower-frequency index satisfies every finite-depth comparison
window before any actual smoothing index is selected. -/
def Ready(H:ℝ≥0)(hH:0<H)(N J:ℕ):Prop:=
  FiniteNativeGaussianCutoff.index D hT hT1 hsmall H hH N≤J ∧
  ∀n j:ℕ,J≤j→
    (RemainderBandSpans.span (Smooth n).exponent j:ℝ)≤H ∧
    (RemainderBandSpans.span (Smooth n).exponent j:ℝ)≤(Smooth n).horizon ∧
    (∀l,l<N→(RemainderBandSpans.span (Smooth n).exponent j:ℝ)≤PhysicalScoreChain.uniformHorizon 1 l) ∧
    (∀k,k≤N→(RemainderBandSpans.span (Smooth n).exponent j:ℝ)≤
      ControlledDefectConstants.horizon (Smooth n).lower (Smooth n).lower_pos m W hm hW ρ hρ hρhalf k) ∧
    (RemainderBandSpans.span (Smooth n).exponent j:ℝ)≤NativeUniversalConstants.rowHorizon 1 ∧
    (RemainderBandSpans.span (Smooth n).exponent j:ℝ)≤4*Real.pi^2*NativeUniversalConstants.currentHorizon.{0} 1 (by omega) ∧
    (RemainderBandSpans.span (Smooth n).exponent j:ℝ)≤UniformFutureProfileScores.horizon 1 ∧
    (RemainderBandSpans.span (Smooth n).exponent j:ℝ)≤NativeTwoPointCovariance.horizon

/-- The same genuine comparable split serves low reconstruction
(2^J), all seven high components (2^(J+1)), Gaussian windows, first
defect ages, initial/full Gamma windows, and the frozen covariance.
The threshold and the split precede the companion index. -/
theorem exists_threshold(H:ℝ≥0)(hH:0<H)(N:ℕ):
    ∃B:ℝ,1≤B ∧ ∀Λ:ℝ,B≤Λ→∃J:ℕ,
      Λ^(1/4:ℝ)<(2:ℝ)^J ∧ (2:ℝ)^J≤2*Λ^(1/4:ℝ) ∧
      Λ^(1/4:ℝ)<(2:ℝ)^(J+1) ∧ (2:ℝ)^(J+1)≤4*Λ^(1/4:ℝ) ∧
      Ready m W hm hW ρ hρ hρhalf D hT hT1 hsmall H hH N J:=by
  have hHr:0<(H:ℝ):=by exact_mod_cast hH
  obtain ⟨B0,hB0,hcut⟩:=DefectDyadicComparableCutoff.uniform_smooth_threshold
    m W hm hW ρ hρ hρhalf D hT hT1 hsmall H hHr N
  obtain ⟨Jr,hJr⟩:=RemainderBandSpans.eventually_small D.beta_pos (NativeUniversalConstants.rowHorizon_pos 1)
  have hcur:0<4*Real.pi^2*NativeUniversalConstants.currentHorizon.{0} 1 (by omega):=
    mul_pos (by positivity) (NativeUniversalConstants.currentHorizon_pos.{0} 1 (by omega))
  obtain ⟨Jc,hJc⟩:=RemainderBandSpans.eventually_small D.beta_pos hcur
  obtain ⟨Js,hJs⟩:=RemainderBandSpans.eventually_small D.beta_pos (UniformFutureProfileScores.horizon_pos 1)
  obtain ⟨Jf,hJf⟩:=RemainderBandSpans.eventually_small D.beta_pos NativeTwoPointCovariance.horizon_pos
  let Jg:=FiniteNativeGaussianCutoff.index D hT hT1 hsmall H hH N
  let Jmin:=max Jg (max Jr (max Jc (max Js Jf)))
  have he:∀ᶠΛ:ℝ in atTop,B0≤Λ ∧ (2:ℝ)^Jmin≤Λ^(1/4:ℝ):=
    (eventually_ge_atTop B0).and
      ((tendsto_rpow_atTop (by norm_num:(0:ℝ)<1/4)).eventually (eventually_ge_atTop _))
  have hall:∀ᶠΛ:ℝ in atTop,∃J:ℕ,
      Λ^(1/4:ℝ)<(2:ℝ)^J ∧ (2:ℝ)^J≤2*Λ^(1/4:ℝ) ∧
      Λ^(1/4:ℝ)<(2:ℝ)^(J+1) ∧ (2:ℝ)^(J+1)≤4*Λ^(1/4:ℝ) ∧
      Ready m W hm hW ρ hρ hρhalf D hT hT1 hsmall H hH N J:=by
    filter_upwards [he] with Λ hΛ
    obtain ⟨J,hJ0,hJ1,hReady⟩:=hcut Λ hΛ.1
    have hj:Jmin≤J:=by
      by_contra hn
      have hp:(2:ℝ)^J≤(2:ℝ)^Jmin:=pow_le_pow_right₀ (by norm_num:(1:ℝ)≤2)
        (Nat.le_of_lt (lt_of_not_ge hn))
      exact (not_lt_of_ge (hp.trans hΛ.2)) hJ0
    have hNext:(2:ℝ)^(J+1)=2*(2:ℝ)^J:=by rw [pow_succ];ring
    refine ⟨J,hJ0,hJ1,?_,?_,?_,?_⟩
    · rw [hNext]
      have hp:0<(2:ℝ)^J:=by positivity
      linarith only [hJ0,hp]
    · rw [hNext]
      linarith only [hJ1]
    · change Jg≤J
      dsimp only [Jmin] at hj
      omega
    · intro n j hjj
      have hh:=hReady n j hjj
      refine ⟨hh.1,hh.2.1,hh.2.2.1,hh.2.2.2,?_,?_,?_,?_⟩
      all_goals change (RemainderBandSpans.span D.beta j:ℝ)≤_
      · exact hJr j (by dsimp only [Jmin] at hj;omega)
      · exact hJc j (by dsimp only [Jmin] at hj;omega)
      · exact hJs j (by dsimp only [Jmin] at hj;omega)
      · exact hJf j (by dsimp only [Jmin] at hj;omega)
  obtain ⟨B,hB⟩:=eventually_atTop.mp hall
  exact ⟨max 1 B,le_max_left _ _,fun Λ hΛ=>hB Λ ((le_max_right _ _).trans hΛ)⟩

end SHE.CommonComparisonCutoff
