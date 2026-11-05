module
public import SHE.DyadicComparableCutoff
public import SHE.ControlledDefectConstants
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace SHE.DefectDyadicComparableCutoff
open Real Filter Topology
variable (m W:ℝ)(hm:0<m)(hW:0≤W)(ρ:ℝ)(hρ:0<ρ)(hρhalf:ρ<1/2)

/-- A single comparable dyadic cutoff includes every new fresh-age
horizon at the fixed finite depth, before the damping or band choices. -/
theorem exists_threshold (P:CanonicalCovariance.ProfileParameters)(H:ℝ)(hH:0<H)(N:ℕ):
    ∃B:ℝ,1≤B ∧ ∀Λ:ℝ,B≤Λ→∃J:ℕ,
      Λ^(1/4:ℝ)<(2:ℝ)^J ∧ (2:ℝ)^J≤2*Λ^(1/4:ℝ) ∧
      ∀j,J≤j→
        (RemainderBandSpans.span P.exponent j:ℝ)≤H ∧
        (RemainderBandSpans.span P.exponent j:ℝ)≤P.horizon ∧
        (∀l,l<N→(RemainderBandSpans.span P.exponent j:ℝ)≤PhysicalScoreChain.uniformHorizon 1 l) ∧
        ∀k,k≤N→(RemainderBandSpans.span P.exponent j:ℝ)≤
          ControlledDefectConstants.horizon P.lower P.lower_pos m W hm hW ρ hρ hρhalf k:=by
  have hsmall(c:ℝ)(hc:0<c):∀ᶠj:ℕ in atTop,(RemainderBandSpans.span P.exponent j:ℝ)≤c:=by
    obtain ⟨J,hJ⟩:=RemainderBandSpans.eventually_small P.exponent_pos hc
    exact eventually_atTop.2 ⟨J,hJ⟩
  have hfin:∀ᶠj:ℕ in atTop,∀k:Fin (N+1),
      (RemainderBandSpans.span P.exponent j:ℝ)≤
        ControlledDefectConstants.horizon P.lower P.lower_pos m W hm hW ρ hρ hρhalf k:=by
    rw [eventually_all]
    intro k
    exact hsmall _ (ControlledDefectConstants.horizon_pos P.lower P.lower_pos m W hm hW ρ hρ hρhalf k)
  obtain ⟨Jage,hJage⟩:=eventually_atTop.1 hfin
  obtain ⟨B0,hB0,hcut⟩:=DyadicComparableCutoff.exists_threshold P H hH N
  have he:∀ᶠΛ:ℝ in atTop,B0≤Λ ∧ (2:ℝ)^Jage≤Λ^(1/4:ℝ):=
    (eventually_ge_atTop B0).and ((tendsto_rpow_atTop (by norm_num:(0:ℝ)<1/4)).eventually (eventually_ge_atTop _))
  have hall:∀ᶠΛ:ℝ in atTop,∃J:ℕ,
      Λ^(1/4:ℝ)<(2:ℝ)^J ∧ (2:ℝ)^J≤2*Λ^(1/4:ℝ) ∧
      ∀j,J≤j→
        (RemainderBandSpans.span P.exponent j:ℝ)≤H ∧
        (RemainderBandSpans.span P.exponent j:ℝ)≤P.horizon ∧
        (∀l,l<N→(RemainderBandSpans.span P.exponent j:ℝ)≤PhysicalScoreChain.uniformHorizon 1 l) ∧
        ∀k,k≤N→(RemainderBandSpans.span P.exponent j:ℝ)≤
          ControlledDefectConstants.horizon P.lower P.lower_pos m W hm hW ρ hρ hρhalf k:=by
    filter_upwards [he] with Λ hΛ
    obtain ⟨J,hJ0,hJ1,hJ⟩:=hcut Λ hΛ.1
    have hage:Jage≤J:=by
      by_contra hn
      have hp:(2:ℝ)^J≤(2:ℝ)^Jage:=pow_le_pow_right₀ (by norm_num:(1:ℝ)≤2) (Nat.le_of_lt (lt_of_not_ge hn))
      exact (not_lt_of_ge (hp.trans hΛ.2)) hJ0
    refine ⟨J,hJ0,hJ1,fun j hj=>⟨(hJ j hj).1,(hJ j hj).2.1,(hJ j hj).2.2,?_⟩⟩
    intro k hk
    exact hJage j (hage.trans hj) ⟨k,Nat.lt_succ_of_le hk⟩
  obtain ⟨B,hB⟩:=eventually_atTop.1 hall
  exact ⟨max 1 B,le_max_left _ _,fun Λ hΛ=>hB Λ ((le_max_right _ _).trans hΛ)⟩

open SmoothApproximation
variable (D:ScalarData){T0:ℝ}(hT0:0<T0)(hT1:T0≤1)
variable (hsmall:GaussianProfile.contractionConstant D.ell D.holderConstant D.beta*T0^(D.beta/4)≤1/2)
local notation "Smooth"=>ControlledSmoothLimit.smoothTotalParameters D hT0 hT1 hsmall
local notation "Rough"=>ControlledSmoothLimit.roughTotalParameters D hT0 hT1 hsmall

/-- The cutoff is chosen before the smoothing index; all newly required
fresh-age horizons and all original physical horizons hold together. -/
theorem uniform_smooth_threshold (H:ℝ)(hH:0<H)(N:ℕ):
    ∃B:ℝ,1≤B ∧ ∀Λ:ℝ,B≤Λ→∃J:ℕ,
      Λ^(1/4:ℝ)<(2:ℝ)^J ∧ (2:ℝ)^J≤2*Λ^(1/4:ℝ) ∧
      ∀n j:ℕ,J≤j→
        (RemainderBandSpans.span (Smooth n).exponent j:ℝ)≤H ∧
        (RemainderBandSpans.span (Smooth n).exponent j:ℝ)≤(Smooth n).horizon ∧
        (∀l,l<N→(RemainderBandSpans.span (Smooth n).exponent j:ℝ)≤PhysicalScoreChain.uniformHorizon 1 l) ∧
        ∀k,k≤N→(RemainderBandSpans.span (Smooth n).exponent j:ℝ)≤
          ControlledDefectConstants.horizon (Smooth n).lower (Smooth n).lower_pos m W hm hW ρ hρ hρhalf k:=by
  obtain ⟨B,hB,hcut⟩:=exists_threshold m W hm hW ρ hρ hρhalf Rough H hH N
  refine ⟨B,hB,fun Λ hΛ=>?_⟩
  obtain ⟨J,hJ0,hJ1,hJ⟩:=hcut Λ hΛ
  exact ⟨J,hJ0,hJ1,fun n j hj=>hJ j hj⟩
end SHE.DefectDyadicComparableCutoff
