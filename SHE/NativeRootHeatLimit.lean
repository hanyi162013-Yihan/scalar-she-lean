module

public import SHE.NativeApproximationInput
public import SHE.RealHeat
public import SHE.NativeHeatObservation

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1600000
noncomputable section

namespace SHE.NativeRootHeatLimit
open Set Filter MeasureTheory AddCircle StoppedFourier DyadicApproximation
open scoped ENNReal Topology
local instance nativeRootHeatLimit_unit : Fact (0<(1:ℝ)) := ⟨by positivity⟩
local instance nativeRootHeatLimit_period : Fact (0<2*Real.pi) := ⟨by positivity⟩
local instance nativeRootHeatLimit_realSigma : MeasurableSpace RealL2 := borel _
local instance nativeRootHeatLimit_realBorel : BorelSpace RealL2 := ⟨rfl⟩
local instance nativeRootHeatLimit_unitSigma : MeasurableSpace CircleHeat.CircleL2 := borel _
local instance nativeRootHeatLimit_unitBorel : BorelSpace CircleHeat.CircleL2 := ⟨rfl⟩
local instance nativeRootHeatLimit_nativeSigma : MeasurableSpace CircleL2 := borel _
local instance nativeRootHeatLimit_nativeBorel : BorelSpace CircleL2 := ⟨rfl⟩
local instance nativeRootHeatLimit_nativeCountable : SecondCountableTopology CircleL2 :=
  (_root_.fourierBasis (T:=2*Real.pi)).repr.toHomeomorph.secondCountableTopology

variable (a : ℝ→ℝ) (ha : Measurable a) (M : ℝ) (hM : ∀z,|a z|≤M)

/-- Literal scalar root evaluated after native-clock heat smoothing of
the actual state, represented in the native circle Hilbert space. -/
def root (t : ℝ) (U : RealL2) : CircleL2 :=
  CircleNormalization.push (CoefficientFields.coefficient a ha M hM (NativeHeatObservation.heat t U))

theorem root_zero (U : RealL2) :
    root a ha M hM 0 U=CircleNormalization.push (CoefficientFields.coefficient a ha M hM U) := by
  simp only [root,NativeHeatObservation.heat,zero_div,RealHeat.realHeat_zero,ContinuousLinearMap.id_apply]

theorem root_norm_le (t : ℝ) (U : RealL2) : ‖root a ha M hM t U‖≤M := by
  have hM0:0≤M:=(abs_nonneg _).trans (hM 0)
  rw [root,CircleNormalization.push.norm_map]
  have hb:∀ᵐ y∂haarAddCircle (T:=(1:ℝ)),
      ‖CoefficientFields.coefficient a ha M hM (NativeHeatObservation.heat t U) y‖≤M:=by
    filter_upwards [CoefficientFields.coefficient_ae a ha M hM (NativeHeatObservation.heat t U)] with y hy
    rw [hy,Complex.norm_real,Real.norm_eq_abs]
    exact hM _
  simpa [measureUnivNNReal] using Lp.norm_le_of_ae_bound hM0 hb

attribute [local irreducible] root NativeHeatObservation.heat RealHeat.realHeat
  CoefficientFields.coefficient CircleNormalization.push

theorem root_continuous {β K : ℝ} (hβ : 0<β) (hK : 0≤K)
    (hholder : ∀z w,|a z-a w|≤K*|z-w|^β) :
    Continuous (fun p:ℝ×RealL2=>root a ha M hM p.1 p.2) := by
  have hh:Continuous (fun p:ℝ×RealL2=>NativeHeatObservation.heat p.1 p.2):=by
    unfold NativeHeatObservation.heat
    exact RealHeat.continuous_realHeat_action.comp ((continuous_fst.div_const _).prodMk continuous_snd)
  unfold root
  exact CircleNormalization.push.continuous.comp
    ((CoefficientFields.coefficient_continuous hβ hK a ha hM hholder).comp hh)

theorem root_tendsto {β K : ℝ} (hβ : 0<β) (hK : 0≤K)
    (hholder : ∀z w,|a z-a w|≤K*|z-w|^β) (U : RealL2)
    (ε : ℕ→ℝ) (hε : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun j=>root a ha M hM (ε j) U) atTop
      (𝓝 (CircleNormalization.push (CoefficientFields.coefficient a ha M hM U))) := by
  simpa only [Function.comp_def,root_zero] using
    (((root_continuous a ha M hM hβ hK hholder).continuousAt (x:=(0,U))).tendsto.comp
      (hε.prodMk_nhds (tendsto_const_nhds (x:=U))))

/-- Whole endpoint root fields converge in true sample/time L2. The
state process may be arbitrarily dependent and needs no pointwise
representative convergence hypothesis or moment bound. -/
theorem root_error_energy_tendsto {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsFiniteMeasure ν] {β K : ℝ} (hβ : 0<β) (hK : 0≤K)
    (hholder : ∀z w,|a z-a w|≤K*|z-w|^β)
    (U : X→RealL2) (hU : Measurable U) (ε : ℕ→ℝ) (hε : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun j=>∫x,‖root a ha M hM (ε j) (U x)-root a ha M hM 0 (U x)‖^2 ∂ν)
      atTop (𝓝 (0:ℝ)) := by
  have hc:=root_continuous a ha M hM hβ hK hholder
  have hm(j:ℕ):AEStronglyMeasurable
      (fun x=>‖root a ha M hM (ε j) (U x)-root a ha M hM 0 (U x)‖^2) ν:=
    (((hc.measurable.comp (measurable_const.prodMk hU)).sub
      (hc.measurable.comp (measurable_const.prodMk hU))).norm.pow_const 2).aestronglyMeasurable
  have hb(j:ℕ):∀ᵐ x∂ν,
      ‖‖root a ha M hM (ε j) (U x)-root a ha M hM 0 (U x)‖^2‖≤(2*M)^2:=by
    apply ae_of_all
    intro x
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    apply pow_le_pow_left₀ (norm_nonneg _)
    exact (norm_sub_le _ _).trans (by linarith [root_norm_le a ha M hM (ε j) (U x),root_norm_le a ha M hM 0 (U x)])
  have ht:=tendsto_integral_of_dominated_convergence (fun _x:X=>(2*M)^2) hm
    (integrable_const _) hb (ae_of_all _ (fun x=>by
      have hh:=((root_tendsto a ha M hM hβ hK hholder (U x) ε hε).sub
        (tendsto_const_nhds (x:=root a ha M hM 0 (U x)))).norm.pow 2
      simpa only [root_zero,sub_self,norm_zero,zero_pow (by norm_num : (2:ℕ)≠0)] using hh))
  simpa only [integral_zero] using ht

end SHE.NativeRootHeatLimit
