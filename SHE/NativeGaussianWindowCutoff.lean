module
public import SHE.CanonicalGaussianRootBands
public import SHE.NativeUniversalConstants
public import SHE.UniformFutureProfileScores
public import SHE.UniformPhysicalScoreForest

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace SHE.NativeGaussianWindowCutoff
open Filter
open scoped NNReal Topology
variable (D:SmoothApproximation.ScalarData){T:ℝ}(hT:0<T)(hT1:T≤1)
  (hsmall:GaussianProfile.contractionConstant D.ell D.holderConstant D.beta*T^(D.beta/4)≤1/2)
variable (H:ℝ≥0)(hH:0<H)(k:ℕ)
local notation "Pzero"=>ControlledSmoothLimit.smoothTotalParameters D hT hT1 hsmall 0

def Ready(j:ℕ):Prop:=
  (RemainderBandSpans.span D.beta j:ℝ)≤(H:ℝ) ∧
  (RemainderBandSpans.span D.beta j:ℝ)≤(Pzero).horizon ∧
  (RemainderBandSpans.span D.beta j:ℝ)≤NativeUniversalConstants.rowHorizon (1+k) ∧
  (RemainderBandSpans.span D.beta j:ℝ)≤4*Real.pi^2*NativeUniversalConstants.currentHorizon.{0} (1+k) (by omega) ∧
  (RemainderBandSpans.span D.beta j:ℝ)≤UniformFutureProfileScores.horizon (1+k) ∧
  ∀l,l<k→(RemainderBandSpans.span D.beta j:ℝ)≤PhysicalScoreChain.uniformHorizon 1 l

include hH in
/-- One actual cutoff meets every finite-depth window condition before
any companion index, frequency, sample, or original reference input. -/
theorem exists_cutoff:∃J:ℕ,∀j,J≤j→Ready D hT hT1 hsmall H k j:=by
  have eventually_le(c:ℝ)(hc:0<c):∀ᶠj:ℕ in atTop,(RemainderBandSpans.span D.beta j:ℝ)≤c:=by
    obtain ⟨J,hJ⟩:=RemainderBandSpans.eventually_small D.beta_pos hc
    exact eventually_atTop.mpr ⟨J,hJ⟩
  have hold:∀ᶠj:ℕ in atTop,∀l:Fin k,
      (RemainderBandSpans.span D.beta j:ℝ)≤PhysicalScoreChain.uniformHorizon 1 l:=by
    rw [Filter.eventually_all]
    intro l
    exact eventually_le _ (PhysicalScoreChain.uniformHorizon_pos 1 l)
  have hcur:0<4*Real.pi^2*NativeUniversalConstants.currentHorizon.{0} (1+k) (by omega):=
    mul_pos (by positivity) (NativeUniversalConstants.currentHorizon_pos _ _)
  have hh:∀ᶠj:ℕ in atTop,Ready D hT hT1 hsmall H k j:=by
    filter_upwards [eventually_le _ (show 0<(H:ℝ) from hH),
      eventually_le _ (Pzero).horizon_pos,
      eventually_le _ (NativeUniversalConstants.rowHorizon_pos (1+k)),
      eventually_le _ hcur,eventually_le _ (UniformFutureProfileScores.horizon_pos (1+k)),hold]
      with j h₀ h₁ h₂ h₃ h₄ h₅
    exact ⟨h₀,h₁,h₂,h₃,h₄,fun l hl=>h₅ ⟨l,hl⟩⟩
  exact eventually_atTop.mp hh

def index:ℕ:=Classical.choose (exists_cutoff D hT hT1 hsmall H hH k)

theorem ready(j:ℕ)(hj:index D hT hT1 hsmall H hH k≤j):
    Ready D hT hT1 hsmall H k j:=
  Classical.choose_spec (exists_cutoff D hT hT1 hsmall H hH k) j hj

end SHE.NativeGaussianWindowCutoff
