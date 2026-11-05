module

public import SHE.RemainderBandSpans
public import SHE.UniformPhysicalScoreForest

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace SHE.RemainderBandCutoff
open Filter Topology Real

/-- A fixed finite depth needs only finitely many positive physical
horizons. Every sufficiently high band satisfies ALL of them, on the
same original output interval and fixed-point horizon. -/
theorem exists_cutoff (P:CanonicalCovariance.ProfileParameters) (H:ℝ) (hH:0<H) (N:ℕ):
    ∃J:ℕ,∀j,J≤j→
      (RemainderBandSpans.span P.exponent j:ℝ)≤H ∧
      (RemainderBandSpans.span P.exponent j:ℝ)≤P.horizon ∧
      ∀l,l<N→(RemainderBandSpans.span P.exponent j:ℝ)≤PhysicalScoreChain.uniformHorizon 1 l:=by
  have hsmall(c:ℝ)(hc:0<c):∀ᶠj:ℕ in atTop,(RemainderBandSpans.span P.exponent j:ℝ)≤c:=by
    obtain ⟨J,hJ⟩:=RemainderBandSpans.eventually_small P.exponent_pos hc
    exact eventually_atTop.2 ⟨J,hJ⟩
  have hfin:∀ᶠj:ℕ in atTop,∀l:Fin N,
      (RemainderBandSpans.span P.exponent j:ℝ)≤PhysicalScoreChain.uniformHorizon 1 l:=by
    rw [eventually_all]
    intro l
    exact hsmall _ (PhysicalScoreChain.uniformHorizon_pos 1 l)
  have hall:∀ᶠj:ℕ in atTop,
      (RemainderBandSpans.span P.exponent j:ℝ)≤H ∧
      (RemainderBandSpans.span P.exponent j:ℝ)≤P.horizon ∧
      ∀l:Fin N,(RemainderBandSpans.span P.exponent j:ℝ)≤PhysicalScoreChain.uniformHorizon 1 l:=
    (hsmall H hH).and ((hsmall P.horizon P.horizon_pos).and hfin)
  obtain ⟨J,hJ⟩:=eventually_atTop.1 hall
  refine ⟨J,fun j hj=>⟨(hJ j hj).1,(hJ j hj).2.1,?_⟩⟩
  intro l hl
  exact (hJ j hj).2.2 ⟨l,hl⟩

end SHE.RemainderBandCutoff
