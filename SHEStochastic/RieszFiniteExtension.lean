module

public import SHE.BesselSynthesis
public import SHE.SynthesisEquivalence

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
noncomputable section

namespace SHEStochastic.RieszFiniteExtension
open Filter
open scoped ENNReal Topology

variable {𝕜 ι E : Type*} [RCLike 𝕜] [DecidableEq ι]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- A uniform finite-column lower bound extends to the actual infinite
bounded synthesis, using the standard `ℓ²` finite-support approximation.
This applies unchanged to scalar and vector Haar families. -/
theorem lower (S : lp (fun _ : ι => 𝕜) 2 →L[𝕜] E) (a : ι → E)
    (hSingle : ∀ i, S (lp.single 2 i 1)=a i) (m : ℝ)
    (hFinite : ∀ (s : Finset ι) (z : ι → 𝕜),
      m*(∑ i∈s, ‖z i‖^2) ≤ ‖∑ i∈s, z i • a i‖^2)
    (x : lp (fun _ : ι => 𝕜) 2) : m*‖x‖^2 ≤ ‖S x‖^2 := by
  let P := fun s : Finset ι => ∑ i∈s, lp.single 2 i (x i)
  have hp : Tendsto P atTop (𝓝 x) := lp.hasSum_single (by norm_num : (2 : ENNReal)≠⊤) x
  have he : Tendsto (fun s : Finset ι => ∑ i∈s, ‖x i‖^2) atTop (𝓝 (‖x‖^2)) := by
    have hh := lp.hasSum_norm (by norm_num : 0 < (2 : ENNReal).toReal) x
    change Tendsto _ _ _ at hh
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, SummationFilter.unconditional_filter] using hh
  have hScalar (i : ι) (r : 𝕜) : S (lp.single 2 i r)=r • a i := by
    have hh := lp.single_smul (E := fun _ : ι => 𝕜) 2 i r (1 : 𝕜)
    simp only [smul_eq_mul, mul_one] at hh
    rw [hh, map_smul, hSingle]
  have hb (s : Finset ι) : m*(∑ i∈s, ‖x i‖^2) ≤ ‖S (P s)‖^2 := by
    simp only [P, map_sum, hScalar]
    exact hFinite s x
  exact le_of_tendsto_of_tendsto (he.const_mul m)
    ((S.continuous.tendsto x |>.comp hp).norm.pow 2) (Filter.Eventually.of_forall hb)

end SHEStochastic.RieszFiniteExtension
