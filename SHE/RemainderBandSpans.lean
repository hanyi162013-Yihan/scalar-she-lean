module

public import SHE.DyadicRemainderTail

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace SHE.RemainderBandSpans
open Real Filter Topology
open scoped NNReal

def span (β:ℝ) (j:ℕ):ℝ≥0:=⟨((2:ℝ)^j)^(-3*β),rpow_nonneg (by positivity) _⟩

theorem span_pos (β:ℝ) (j:ℕ):0<span β j:=rpow_pos_of_pos (by positivity) _

theorem span_antitone {β:ℝ} (hβ:0≤β):Antitone (span β):=by
  intro j k hjk
  change ((2:ℝ)^k)^(-3*β)≤((2:ℝ)^j)^(-3*β)
  apply rpow_le_rpow_of_nonpos (by positivity) (pow_le_pow_right₀ (by norm_num:(1:ℝ)≤2) hjk)
  linarith

theorem span_tendsto {β:ℝ} (hβ:0<β):
    Tendsto (fun j:ℕ=>(span β j:ℝ)) atTop (𝓝 0):=by
  have hr:0<(2:ℝ)^(-3*β):=rpow_pos_of_pos (by norm_num) _
  have hr1:(2:ℝ)^(-3*β)<1:=rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have ht:=tendsto_pow_atTop_nhds_zero_of_lt_one hr.le hr1
  convert! ht using 1
  funext j
  exact (rpow_pow_comm (by norm_num:(0:ℝ)≤2) (-3*β) j).symm

theorem eventually_small {β c:ℝ} (hβ:0<β) (hc:0<c):
    ∃J:ℕ,∀j,J≤j→(span β j:ℝ)≤c:=by
  have hh:∀ᶠj:ℕ in atTop,(span β j:ℝ)<c:=(span_tendsto hβ).eventually (gt_mem_nhds hc)
  obtain ⟨J,hJ⟩:=eventually_atTop.1 hh
  exact ⟨J,fun j hj=>(hJ j hj).le⟩

end SHE.RemainderBandSpans
