module

public import SHEStochastic.UnboundedCutoffLpConvergence
public import SHEStochastic.HolderCoefficientContinuity
public import Mathlib.Topology.MetricSpace.Equicontinuity
public import Mathlib.Topology.UniformSpace.Ascoli

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHEStochastic.HolderLpComposition
open MeasureTheory Filter HolderCoefficientIntegrability
open scoped NNReal ENNReal Topology
variable {X E V : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
    (ν : Measure X) [IsProbabilityMeasure ν] {G : E → V} {C β : ℝ≥0}

/-- The old coefficient classes have their literal spatial L2 error.
Only representatives are identified; no new composition map is defined. -/
theorem norm_sq_difference {K : E → V} {D γ : ℝ≥0}
    (hG : HolderWith C β G) (hβ : 0<β) (hβ1 : β≤1)
    (hK : HolderWith D γ K) (hγ : 0<γ) (hγ1 : γ≤1) (u v : Lp E 2 ν) :
    ‖coefficient hβ hβ1 hG u-coefficient hγ hγ1 hK v‖^2=
      ∫ x,‖G (u x)-K (v x)‖^2 ∂ν := by
  rw [SHE.PredictableL2.realLp_norm_sq]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (coefficient hβ hβ1 hG u) (coefficient hγ hγ1 hK v),
    coefficient_ae hβ hβ1 hG u,coefficient_ae hγ hγ1 hK v] with x hx hg hk
  simp only [hx,Pi.sub_apply,hg,hk]

/-- Radial truncations converge in the existing L2 coefficient classes,
including states with unbounded pointwise representatives. -/
theorem cutoff_tendsto (hG : HolderWith C β G) (hβ : 0<β) (hβ1 : β≤1) (u : Lp E 2 ν) :
    Tendsto (fun m : ℕ => coefficient hβ hβ1 (UnboundedCoefficientCutoff.holder hG (m : ℝ≥0)) u)
      atTop (𝓝 (coefficient hβ hβ1 hG u)) := by
  have hh := UnboundedCutoffLpConvergence.energy_tendsto ν hG hβ hβ1 u
  have he : (fun m : ℕ => ‖coefficient hβ hβ1 (UnboundedCoefficientCutoff.holder hG (m : ℝ≥0)) u-
      coefficient hβ hβ1 hG u‖^2)=
      (fun m : ℕ => ∫ x,‖UnboundedCoefficientCutoff.coefficient G (m : ℝ≥0) (u x)-G (u x)‖^2 ∂ν) := by
    funext m
    exact norm_sq_difference ν (UnboundedCoefficientCutoff.holder hG (m : ℝ≥0)) hβ hβ1 hG hβ hβ1 u u
  rw [←he] at hh
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp hh
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  change Tendsto (fun m : ℕ => Real.sqrt
    (‖coefficient hβ hβ1 (UnboundedCoefficientCutoff.holder hG (m : ℝ≥0)) u-coefficient hβ hβ1 hG u‖^2))
      atTop (𝓝 (Real.sqrt 0)) at hs
  simpa only [Real.sqrt_sq_eq_abs,abs_norm,Real.sqrt_zero] using hs

/-- Convergence is uniform on compact L2 state sets. Existing Holder
continuity and the public Ascoli theorem do all equicontinuity work;
no shared pointwise bound on spatial representatives is needed. -/
theorem cutoff_uniformly_on_compact (hG : HolderWith C β G) (hβ : 0<β) (hβ1 : β≤1)
    {s : Set (Lp E 2 ν)} (hs : IsCompact s) :
    TendstoUniformlyOn
      (fun m : ℕ => coefficient hβ hβ1 (UnboundedCoefficientCutoff.holder hG (m : ℝ≥0)) (ν := ν))
      (coefficient hβ hβ1 hG) atTop s := by
  letI : CompactSpace s := isCompact_iff_compactSpace.mp hs
  let F := fun (m : ℕ) (x : s) => coefficient hβ hβ1 (UnboundedCoefficientCutoff.holder hG (m : ℝ≥0)) x.val
  have hE : Equicontinuous F := by
    intro x
    apply Metric.equicontinuousAt_of_continuity_modulus
      (fun y : s => (C : ℝ)*dist x.val y.val^(β : ℝ))
    · have hc : Continuous (fun y : s => (C : ℝ)*dist x.val y.val^(β : ℝ)) :=
        continuous_const.mul ((continuous_const.dist continuous_subtype_val).rpow_const (fun _ => Or.inr β.property))
      simpa only [dist_self,Real.zero_rpow (show (β : ℝ)≠0 from by exact_mod_cast hβ.ne'),mul_zero] using hc.tendsto x
    · exact Filter.Eventually.of_forall fun y m => by
        simpa only [F,dist_eq_norm] using
          HolderCoefficientContinuity.difference_norm ν hβ hβ1
            (UnboundedCoefficientCutoff.holder hG (m : ℝ≥0)) x.val y.val
  have hp : Tendsto F atTop (𝓝 (fun x : s => coefficient hβ hβ1 hG x.val)) :=
    tendsto_pi_nhds.mpr fun x => cutoff_tendsto ν hG hβ hβ1 x.val
  have hu := (hE.tendsto_uniformFun_iff_pi atTop (fun x : s => coefficient hβ hβ1 hG x.val)).mpr hp
  exact tendstoUniformlyOn_iff_tendstoUniformly_comp_coe.mpr
    (UniformFun.tendsto_iff_tendstoUniformly.mp hu)

end SHEStochastic.HolderLpComposition
