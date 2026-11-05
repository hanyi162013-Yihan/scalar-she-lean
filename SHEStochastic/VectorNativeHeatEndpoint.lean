module

public import SHEStochastic.VectorObservedBandLimit
public import SHEStochastic.HolderCoefficientContinuity
public import SHE.NativeBesselGivenSection
public import SHE.NativeRootHeatIdentification

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1000000
noncomputable section

namespace SHEStochastic.VectorNativeHeatEndpoint
open MeasureTheory Filter SHE SHE.StoppedFourier SHE.DyadicApproximation SHE.GaussianIncrement MatrixInfiniteHaar
open HolderCoefficientIntegrability
open scoped ENNReal NNReal Topology
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
local notation "ν" => AddCircle.haarAddCircle (T := 2*Real.pi)
variable {n : ℕ}
local instance : SecondCountableTopology (Physical (d := Fin n)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (Physical (d := Fin n)) := borel _
local instance : BorelSpace (Physical (d := Fin n)) := ⟨rfl⟩
local instance : MeasurableSpace (Lp (State n) 2 ν) := borel _
local instance : BorelSpace (Lp (State n) 2 ν) := ⟨rfl⟩
local instance : MeasurableSpace CircleL2 := borel _
local instance : BorelSpace CircleL2 := ⟨rfl⟩
local instance : SecondCountableTopology CircleL2 :=
  (_root_.fourierBasis (T := 2*Real.pi)).repr.toHomeomorph.secondCountableTopology

/-- Exact real vector rescaling between normalized spatial circles. -/
def push : Physical (d := Fin n) →ₗᵢ[ℝ] Lp (State n) 2 ν :=
  Lp.compMeasurePreservingₗᵢ ℝ (CircleNormalization.scale (2*Real.pi) 1)
    (CircleNormalization.scale_measurePreserving (2*Real.pi) 1)

theorem push_ae (u : Physical (d := Fin n)) :
    push u=ᵐ[ν] fun x => u (CircleNormalization.scale (2*Real.pi) 1 x) :=
  Lp.coeFn_compMeasurePreserving u (CircleNormalization.scale_measurePreserving (2*Real.pi) 1)

/-- The scalar native heat observation is the rescaled original
positive-time heat field, almost everywhere in its spatial center. -/
theorem scalar_heat_ae {t : ℝ} (ht : 0 < t) (u : RealL2) :
    ∀ᵐ x ∂ν,NativeHeatObservation.heat t u (CircleNormalization.scale (2*Real.pi) 1 x)=
      NativeHeatObservation.functional t x u := by
  let v := NativeHeatObservation.heat t u
  have hpres := (CircleNormalization.scale_measurePreserving (2*Real.pi) 1).quasiMeasurePreserving
  have hk := StoppedFourier.heat_kernel_inner_ae ht (NativeHeatObservation.embed u)
  rw [←NativeHeatObservation.embed_heat ht.le u] at hk
  filter_upwards [CircleNormalization.push_ae (realEmbed v),hpres.ae (realEmbed_ae v),hk] with x hp hr hk
  rw [NativeHeatObservation.functional_apply,hk]
  change _=(CircleNormalization.push (realEmbed v) x).re
  rw [hp,hr]
  rfl

/-- Every positive-age vector observation is the literal spatial
representative of the original vector heat semigroup, in the native clock. -/
theorem heat_ae {t : ℝ} (ht : 0 < t) (u : Physical (d := Fin n)) :
    push (VectorHeat.heat (t/NativeHeatObservation.timeScale) u)=ᵐ[ν]
      fun x => VectorHeatObservation.observation t x u := by
  have hpres := (CircleNormalization.scale_measurePreserving (2*Real.pi) 1).quasiMeasurePreserving
  have hcoord := hpres.ae (L2EuclideanCoordinates.coordinates_ae
    (AddCircle.haarAddCircle (T := (1 : ℝ))) (VectorHeat.heat (t/NativeHeatObservation.timeScale) u))
  have hscalar : ∀ᵐ x ∂ν,∀ i : Fin n,
      NativeHeatObservation.heat t (VectorHeat.coordinates u i) (CircleNormalization.scale (2*Real.pi) 1 x)=
        NativeHeatObservation.functional t x (VectorHeat.coordinates u i) :=
    ae_all_iff.mpr (fun i => scalar_heat_ae ht (VectorHeat.coordinates u i))
  filter_upwards [push_ae (VectorHeat.heat (t/NativeHeatObservation.timeScale) u),hcoord,hscalar] with x hp hc hs
  rw [hp]
  apply PiLp.ext
  intro i
  change _=NativeHeatObservation.functional t x (VectorHeat.coordinates u i)
  rw [←hc i]
  change VectorHeat.coordinates (VectorHeat.heat (t/NativeHeatObservation.timeScale) u) i
    (CircleNormalization.scale (2*Real.pi) 1 x)=_
  rw [VectorHeat.coordinate_heat]
  exact hs i

variable {φ : State n → ℝ} {C β : ℝ≥0} (hβ : 0 < β) (hβ1 : β ≤ 1) (hφ : HolderWith C β φ)

/-- The nonlinear coefficient applied to the true heat-smoothed L2
state, including the original unsmoothed state at age zero. -/
def root (t : ℝ) (u : Physical (d := Fin n)) : CircleL2 :=
  Complex.ofRealCLM.compLpL 2 ν (coefficient hβ hβ1 hφ (push (VectorHeat.heat (t/NativeHeatObservation.timeScale) u)))

theorem root_continuous : Continuous (fun p : ℝ×Physical (d := Fin n) => root hβ hβ1 hφ p.1 p.2) := by
  have hmap : Continuous (fun p : ℝ×Physical (d := Fin n) => (p.1/NativeHeatObservation.timeScale,p.2)) :=
    (continuous_fst.div_const NativeHeatObservation.timeScale).prodMk continuous_snd
  have hh : Continuous (fun p : ℝ×Physical (d := Fin n) =>
      VectorHeat.heat (p.1/NativeHeatObservation.timeScale) p.2) :=
    Continuous.comp (f := fun p : ℝ×Physical (d := Fin n) => (p.1/NativeHeatObservation.timeScale,p.2))
      (g := fun p : ℝ×Physical (d := Fin n) => VectorHeat.heat p.1 p.2)
      (VectorHeat.continuous_action (d := Fin n)) hmap
  exact (Complex.ofRealCLM.compLpL 2 ν).continuous.comp
    ((HolderCoefficientContinuity.continuous ν hβ hβ1 hφ).comp ((push (n := n)).continuous.comp hh))

theorem root_ae {t : ℝ} (ht : 0 < t) (u : Physical (d := Fin n)) :
    root hβ hβ1 hφ t u=ᵐ[ν] fun x => (φ (VectorHeatObservation.observation t x u) : ℂ) := by
  filter_upwards [Complex.ofRealCLM.coeFn_compLpL
      (coefficient hβ hβ1 hφ (push (VectorHeat.heat (t/NativeHeatObservation.timeScale) u))),
    coefficient_ae hβ hβ1 hφ (push (VectorHeat.heat (t/NativeHeatObservation.timeScale) u)),heat_ae ht u] with x hr hc hh
  exact hr.trans (by rw [hc,hh];rfl)

theorem root_bound {M : ℝ} (hM : 0 ≤ M) (hφb : ∀ z,|φ z| ≤ M)
    (t : ℝ) (u : Physical (d := Fin n)) : ‖root hβ hβ1 hφ t u‖ ≤ M := by
  have hb : ∀ᵐ x ∂ν,‖root hβ hβ1 hφ t u x‖ ≤ M := by
    filter_upwards [Complex.ofRealCLM.coeFn_compLpL
        (coefficient hβ hβ1 hφ (push (VectorHeat.heat (t/NativeHeatObservation.timeScale) u))),
      coefficient_ae hβ hβ1 hφ (push (VectorHeat.heat (t/NativeHeatObservation.timeScale) u))] with x hr hc
    dsimp only [root]
    rw [hr]
    change ‖(coefficient hβ hβ1 hφ (push (VectorHeat.heat (t/NativeHeatObservation.timeScale) u)) x : ℂ)‖ ≤ M
    rw [hc,Complex.norm_real,Real.norm_eq_abs]
    exact hφb _
  simpa [measureUnivNNReal] using Lp.norm_le_of_ae_bound hM hb

def difference (Λ ρ : ℝ) (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ)
    (t : ℝ) (u v : Physical (d := Fin n)) : CircleL2 :=
  OneInputOperator.besselHalf Λ ρ hΛ hρ (root hβ hβ1 hφ t v-root hβ hβ1 hφ t u)

/-- The unsmoothed endpoint is explicitly the original coefficient
applied to the original L2 states, rather than a new limit object. -/
theorem root_zero (u : Physical (d := Fin n)) :
    root hβ hβ1 hφ 0 u=Complex.ofRealCLM.compLpL 2 ν (coefficient hβ hβ1 hφ (push u)) := by
  simp only [root,zero_div,VectorHeat.zero,ContinuousLinearMap.id_apply]

/-- Nonlinear coefficient evaluation commutes with the exact spatial
rescaling, so the zero-age endpoint is the original unit-circle input. -/
theorem root_zero_unit (u : Physical (d := Fin n)) :
    root hβ hβ1 hφ 0 u=NativeHeatObservation.embed
      (coefficient hβ hβ1 hφ u) := by
  rw [root_zero]
  let f : RealL2 := coefficient hβ hβ1 hφ u
  let g : Lp ℝ 2 ν := coefficient hβ hβ1 hφ (push u)
  change Complex.ofRealCLM.compLpL 2 ν g=CircleNormalization.push (realEmbed f)
  have hpres := (CircleNormalization.scale_measurePreserving (2*Real.pi) 1).quasiMeasurePreserving
  apply Lp.ext
  filter_upwards [Complex.ofRealCLM.coeFn_compLpL g,coefficient_ae hβ hβ1 hφ (push u),push_ae u,
    CircleNormalization.push_ae (realEmbed f),hpres.ae (realEmbed_ae f),
    hpres.ae (coefficient_ae hβ hβ1 hφ u)] with x hg hc hu hp hr hf
  rw [hg,hp,hr]
  change (g x : ℂ)=(f (CircleNormalization.scale (2*Real.pi) 1 x) : ℂ)
  rw [hc,hu,hf]

/-- The native negative endpoint energy is exactly the original
unit-circle massive Fourier energy, with no period factor omitted. -/
theorem energy_zero_unit {Λ ρ : ℝ} (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ) (u v : Physical (d := Fin n)) :
    ‖difference hβ hβ1 hφ Λ ρ hΛ hρ 0 u v‖^2=
      StepInput.negativeEnergy 1 Λ ρ (realEmbed
        (coefficient hβ hβ1 hφ v-
          coefficient hβ hβ1 hφ u)) := by
  rw [difference,root_zero_unit,root_zero_unit,←map_sub]
  exact CircleNormalization.push_bessel_energy hΛ hρ _

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Identifies the positive-gap canonical field with the actual
coefficient of the vector heat observations used in the native comparison. -/
theorem observed_eq {t Λ ρ : ℝ} (ht : 0 < t) (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ)
    (U V : Ω → Physical (d := Fin n)) (hU : Measurable U) (hV : Measurable V) (ω : Ω) :
    VectorObservedBandLimit.value φ t Λ ρ hΛ hρ U V ω=
      difference hβ hβ1 hφ Λ ρ hΛ hρ t (U ω) (V ω) := by
  apply NativeBesselGivenSection.value_eq Λ ρ hΛ hρ _
    (Complex.continuous_ofReal.measurable.comp
      (VectorObservedProfile.measurable φ (hφ.uniformContinuous hβ).continuous.measurable ht U V hU hV))
    (fun p => root hβ hβ1 hφ t (V p)-root hβ hβ1 hφ t (U p)) ω
  filter_upwards [root_ae hβ hβ1 hφ ht (V ω),root_ae hβ hβ1 hφ ht (U ω),
    Lp.coeFn_sub (root hβ hβ1 hφ t (V ω)) (root hβ hβ1 hφ t (U ω))] with x hv hu hs
  rw [hs,Pi.sub_apply]
  change (VectorObservedProfile.difference φ t U V (ω,x) : ℂ)=_
  rw [hv,hu]
  simp only [VectorObservedProfile.difference,Complex.ofReal_sub]

/-- Removing the artificial heat-observation age in the whole true
negative energy requires only strong heat continuity and boundedness. -/
theorem energy_tendsto (μ : Measure Ω) [IsFiniteMeasure μ]
    {M : ℝ} (hM : 0 ≤ M) (hφb : ∀ z,|φ z| ≤ M)
    (Λ ρ : ℝ) (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ)
    (U V : Ω → Physical (d := Fin n)) (hU : Measurable U) (hV : Measurable V)
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun j => ∫ ω,‖difference hβ hβ1 hφ Λ ρ hΛ hρ (ε j) (U ω) (V ω)‖^2 ∂μ)
      atTop (𝓝 (∫ ω,‖difference hβ hβ1 hφ Λ ρ hΛ hρ 0 (U ω) (V ω)‖^2 ∂μ)) := by
  let Q := OneInputOperator.besselHalf Λ ρ hΛ hρ
  have hr (W : Ω → Physical (d := Fin n)) (hW : Measurable W) (t : ℝ) :
      Measurable (fun ω => root hβ hβ1 hφ t (W ω)) :=
    Measurable.comp (g := fun p : ℝ×Physical (d := Fin n) => root hβ hβ1 hφ p.1 p.2)
      (f := fun ω : Ω => (t,W ω)) (root_continuous hβ hβ1 hφ).measurable (measurable_const.prodMk hW)
  have hm (t : ℝ) : Measurable (fun ω => difference hβ hβ1 hφ Λ ρ hΛ hρ t (U ω) (V ω)) :=
    Q.continuous.measurable.comp ((hr V hV t).sub (hr U hU t))
  apply tendsto_integral_of_dominated_convergence (fun _ : Ω => (2*M)^2)
  · intro j
    exact ((hm (ε j)).norm.pow_const 2).aestronglyMeasurable
  · exact integrable_const _
  · intro j
    apply ae_of_all
    intro ω
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    apply pow_le_pow_left₀ (norm_nonneg _)
    exact (OneInputOperator.besselHalf_norm_le Λ ρ hΛ hρ _).trans
      ((norm_sub_le _ _).trans ((add_le_add
        (root_bound hβ hβ1 hφ hM hφb (ε j) (V ω))
        (root_bound hβ hβ1 hφ hM hφb (ε j) (U ω))).trans_eq (by ring)))
  · apply ae_of_all
    intro ω
    have ht (u : Physical (d := Fin n)) :
        Tendsto (fun j => root hβ hβ1 hφ (ε j) u) atTop (𝓝 (root hβ hβ1 hφ 0 u)) :=
      by
        have hp : Tendsto (fun j => (ε j,u)) atTop (𝓝 ((0 : ℝ),u)) := hε.prodMk_nhds tendsto_const_nhds
        exact Filter.Tendsto.comp (f := fun j => (ε j,u))
          (g := fun p : ℝ×Physical (d := Fin n) => root hβ hβ1 hφ p.1 p.2)
          ((root_continuous hβ hβ1 hφ).tendsto ((0 : ℝ),u)) hp
    exact ((Q.continuous.tendsto _).comp ((ht (V ω)).sub (ht (U ω)))).norm.pow 2

/-- A uniform estimate on genuine positive-age comparison fields
therefore holds for the original coefficient of the original states. -/
theorem energy_le_of_observed (μ : Measure Ω) [IsFiniteMeasure μ]
    {M cap : ℝ} (hM : 0 ≤ M) (hφb : ∀ z,|φ z| ≤ M)
    (Λ ρ : ℝ) (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ)
    (U V : Ω → Physical (d := Fin n)) (hU : Measurable U) (hV : Measurable V)
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0)) (hεpos : ∀ j,0 < ε j)
    (hBound : ∀ j,(∫ ω,‖VectorObservedBandLimit.value φ (ε j) Λ ρ hΛ hρ U V ω‖^2 ∂μ) ≤ cap) :
    (∫ ω,‖difference hβ hβ1 hφ Λ ρ hΛ hρ 0 (U ω) (V ω)‖^2 ∂μ) ≤ cap := by
  apply le_of_tendsto (energy_tendsto hβ hβ1 hφ μ hM hφb Λ ρ hΛ hρ U V hU hV ε hε)
  exact Eventually.of_forall (fun j => by simpa only [observed_eq hβ hβ1 hφ (hεpos j) hΛ hρ U V hU hV] using hBound j)

end SHEStochastic.VectorNativeHeatEndpoint

