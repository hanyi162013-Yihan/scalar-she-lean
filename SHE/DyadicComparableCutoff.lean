module

public import SHE.DyadicMasterRemainder
public import SHE.FullRemainderConstants

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace SHE.DyadicComparableCutoff
open Real Filter Topology

/-- A genuine dyadic split stays within factor2 of the manuscript's
frequency Lambda^(1/4). For sufficiently large Lambda the SAME split
also satisfies all fixed finite-depth physical window conditions. -/
theorem eventually_cutoff (P:CanonicalCovariance.ProfileParameters) (H:ℝ) (hH:0<H) (N:ℕ):
    ∀ᶠΛ:ℝ in atTop,∃J:ℕ,
      Λ^(1/4:ℝ)<(2:ℝ)^J ∧ (2:ℝ)^J≤2*Λ^(1/4:ℝ) ∧
      ∀j,J≤j→
        (RemainderBandSpans.span P.exponent j:ℝ)≤H ∧
        (RemainderBandSpans.span P.exponent j:ℝ)≤P.horizon ∧
        ∀l,l<N→(RemainderBandSpans.span P.exponent j:ℝ)≤PhysicalScoreChain.uniformHorizon 1 l:=by
  obtain ⟨J0,hJ0⟩:=RemainderBandCutoff.exists_cutoff P H hH N
  have he:∀ᶠΛ:ℝ in atTop,max 1 ((2:ℝ)^J0)≤Λ^(1/4:ℝ):=
    (tendsto_rpow_atTop (by norm_num:(0:ℝ)<1/4)).eventually (eventually_ge_atTop _)
  filter_upwards [he] with Λ hΛ
  have hR:1≤Λ^(1/4:ℝ):=(le_max_left _ _).trans hΛ
  have hR0:(2:ℝ)^J0≤Λ^(1/4:ℝ):=(le_max_right _ _).trans hΛ
  obtain ⟨i,hi,hnext⟩:=exists_nat_pow_near hR (by norm_num:(1:ℝ)<2)
  have hindex:J0 ≤ i+1:=by
    by_contra hn
    have hp:(2:ℝ)^(i+1)≤(2:ℝ)^J0:=
      pow_le_pow_right₀ (by norm_num:(1:ℝ)≤2) (Nat.le_of_lt (lt_of_not_ge hn))
    exact (not_lt_of_ge (hp.trans hR0)) hnext
  refine ⟨i+1,hnext,?_,fun j hj=>hJ0 j (hindex.trans hj)⟩
  rw [pow_succ]
  nlinarith

/-- The admissible lower damping threshold is fixed before the actual
solution, smoothing index, band cutoff or sample is chosen. -/
theorem exists_threshold (P:CanonicalCovariance.ProfileParameters) (H:ℝ) (hH:0<H) (N:ℕ):
    ∃B:ℝ,1≤B ∧ ∀Λ:ℝ,B≤Λ→∃J:ℕ,
      Λ^(1/4:ℝ)<(2:ℝ)^J ∧ (2:ℝ)^J≤2*Λ^(1/4:ℝ) ∧
      ∀j,J≤j→
        (RemainderBandSpans.span P.exponent j:ℝ)≤H ∧
        (RemainderBandSpans.span P.exponent j:ℝ)≤P.horizon ∧
        ∀l,l<N→(RemainderBandSpans.span P.exponent j:ℝ)≤PhysicalScoreChain.uniformHorizon 1 l:=by
  obtain ⟨B,hB⟩:=eventually_atTop.1 (eventually_cutoff P H hH N)
  exact ⟨max 1 B,le_max_left _ _,fun Λ hΛ=>hB Λ ((le_max_right _ _).trans hΛ)⟩

open SmoothApproximation
variable (D:ScalarData) {T0:ℝ} (hT0:0<T0) (hT1:T0≤1)
variable (hsmall:GaussianProfile.contractionConstant D.ell D.holderConstant D.beta*T0^(D.beta/4)≤1/2)
local notation "Smooth"=>ControlledSmoothLimit.smoothTotalParameters D hT0 hT1 hsmall
local notation "Rough"=>ControlledSmoothLimit.roughTotalParameters D hT0 hT1 hsmall

/-- ONE eventual dyadic cutoff works simultaneously for ALL actual
smooth companions. The smoothing index is quantified after the cutoff. -/
theorem uniform_smooth_threshold (H:ℝ) (hH:0<H) (N:ℕ):
    ∃B:ℝ,1≤B ∧ ∀Λ:ℝ,B≤Λ→∃J:ℕ,
      Λ^(1/4:ℝ)<(2:ℝ)^J ∧ (2:ℝ)^J≤2*Λ^(1/4:ℝ) ∧
      ∀n j:ℕ,J≤j→
        (RemainderBandSpans.span (Smooth n).exponent j:ℝ)≤H ∧
        (RemainderBandSpans.span (Smooth n).exponent j:ℝ)≤(Smooth n).horizon ∧
        ∀l,l<N→(RemainderBandSpans.span (Smooth n).exponent j:ℝ)≤PhysicalScoreChain.uniformHorizon 1 l:=by
  obtain ⟨B,hB,hcut⟩:=exists_threshold Rough H hH N
  refine ⟨B,hB,fun Λ hΛ=>?_⟩
  obtain ⟨J,hJ0,hJ1,hJ⟩:=hcut Λ hΛ
  refine ⟨J,hJ0,hJ1,fun n j hj=>?_⟩
  exact hJ j hj

end SHE.DyadicComparableCutoff
