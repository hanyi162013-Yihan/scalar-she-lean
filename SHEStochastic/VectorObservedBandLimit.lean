module

public import SHEStochastic.VectorObservedProfile
public import SHEStochastic.IsotropicGaussianBandSeries
public import SHE.NativeBesselDifferenceIdentity

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section

namespace SHEStochastic.VectorObservedBandLimit
open MeasureTheory Filter SHE SHE.StoppedFourier SHE.GaussianIncrement SHE.GaussianConvolution MatrixInfiniteHaar
open scoped ENNReal NNReal Topology
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
local instance : MeasurableSpace CircleL2 := borel _
local instance : BorelSpace CircleL2 := ⟨rfl⟩
local instance : SecondCountableTopology CircleL2 :=
  (_root_.fourierBasis (T := 2*Real.pi)).repr.toHomeomorph.secondCountableTopology
variable {Ω : Type*} [MeasurableSpace Ω]
local notation "ν" => AddCircle.haarAddCircle (T := 2*Real.pi)

/-- Bounded joint fields have their literal spatial L2 section at every parameter. -/
theorem bounded_section (F : Ω×HeatCircle → ℂ) (hF : Measurable F)
    {M : ℝ} (hFbound : ∀ p,‖F p‖ ≤ M) (ω : Ω) :
    MemLp (fun x => F (ω,x)) 2 ν :=
  MemLp.of_bound (hF.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable M
    (ae_of_all _ (fun x => hFbound (ω,x)))

/-- Uniform coefficient errors control the actual canonical Bessel
versions, with constant one and no stochastic or spatial truncation. -/
theorem norm_sub (F G : Ω×HeatCircle → ℂ) (hF : Measurable F) (hG : Measurable G)
    {M N δ Λ ρ : ℝ} (hFbound : ∀ p,‖F p‖ ≤ M) (hGbound : ∀ p,‖G p‖ ≤ N)
    (hδ : 0 ≤ δ) (hclose : ∀ p,‖F p-G p‖ ≤ δ) (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ) (ω : Ω) :
    ‖NativeBesselFieldAE.value Λ ρ hΛ hρ F ω-NativeBesselFieldAE.value Λ ρ hΛ hρ G ω‖ ≤ δ := by
  let A := MeasurableL2FieldAE.realization ν F ω
  let B := MeasurableL2FieldAE.realization ν G ω
  have ha := MeasurableL2FieldAE.realization_ae ν F hF ω
    ((MeasurableL2FieldAE.section_memLp_iff ν F hF ω).mp (bounded_section F hF hFbound ω))
  have hb := MeasurableL2FieldAE.realization_ae ν G hG ω
    ((MeasurableL2FieldAE.section_memLp_iff ν G hG ω).mp (bounded_section G hG hGbound ω))
  have hd : ∀ᵐ x ∂ν,‖(A-B : CircleL2) x‖ ≤ δ := by
    filter_upwards [ha,hb,Lp.coeFn_sub A B] with x ha hb hx
    rw [hx]
    change ‖A x-B x‖ ≤ δ
    rw [ha,hb]
    exact hclose (ω,x)
  have hn : ‖A-B‖ ≤ δ := by simpa [measureUnivNNReal] using Lp.norm_le_of_ae_bound hδ hd
  change ‖OneInputOperator.besselHalf Λ ρ hΛ hρ A-OneInputOperator.besselHalf Λ ρ hΛ hρ B‖ ≤ δ
  rw [←map_sub]
  exact (OneInputOperator.besselHalf_norm_le Λ ρ hΛ hρ _).trans hn

/-- The Bessel multiplier is contractive on each bounded literal field. -/
theorem norm_le (F : Ω×HeatCircle → ℂ) (hF : Measurable F)
    {M Λ ρ : ℝ} (hM : 0 ≤ M) (hFbound : ∀ p,‖F p‖ ≤ M)
    (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ) (ω : Ω) :
    ‖NativeBesselFieldAE.value Λ ρ hΛ hρ F ω‖ ≤ M := by
  have ha := MeasurableL2FieldAE.realization_ae ν F hF ω
    ((MeasurableL2FieldAE.section_memLp_iff ν F hF ω).mp (bounded_section F hF hFbound ω))
  have hb : ∀ᵐ x ∂ν,‖MeasurableL2FieldAE.realization ν F ω x‖ ≤ M :=
    ha.mono (fun x hx => by rw [hx];exact hFbound (ω,x))
  exact (OneInputOperator.besselHalf_norm_le Λ ρ hΛ hρ _).trans
    (by simpa [measureUnivNNReal] using Lp.norm_le_of_ae_bound hM hb)

variable {n : ℕ}
local instance : SecondCountableTopology (Physical (d := Fin n)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (Physical (d := Fin n)) := borel _
local instance : BorelSpace (Physical (d := Fin n)) := ⟨rfl⟩

/-- The actual signed heat-observed field, after the massive Bessel multiplier. -/
def value (φ : State n → ℝ) (ε Λ ρ : ℝ) (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ)
    (U V : Ω → Physical (d := Fin n)) (ω : Ω) : CircleL2 :=
  NativeBesselFieldAE.value Λ ρ hΛ hρ
    (fun p => (VectorObservedProfile.difference φ ε U V p : ℂ)) ω

theorem measurable (φ : State n → ℝ) (hφ : Measurable φ) {ε Λ ρ : ℝ}
    (hε : 0 < ε) (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ)
    (U V : Ω → Physical (d := Fin n)) (hU : Measurable U) (hV : Measurable V) :
    Measurable (value φ ε Λ ρ hΛ hρ U V) :=
  NativeBesselFieldAE.measurable Λ ρ hΛ hρ _
    (Complex.continuous_ofReal.measurable.comp (VectorObservedProfile.measurable φ hφ hε U V hU hV))

/-- Uniform approximation of vector-state coefficients gives uniform
approximation of their genuine signed negative spatial profiles. -/
theorem approximation (φ ψ : State n → ℝ) (hφ : Measurable φ) (hψ : Measurable ψ)
    {M N δ ε Λ ρ : ℝ} (hφb : ∀ z,|φ z| ≤ M) (hψb : ∀ z,|ψ z| ≤ N)
    (hδ : 0 ≤ δ) (hclose : ∀ z,|φ z-ψ z| ≤ δ) (hε : 0 < ε) (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ)
    (U V : Ω → Physical (d := Fin n)) (hU : Measurable U) (hV : Measurable V) (ω : Ω) :
    ‖value φ ε Λ ρ hΛ hρ U V ω-value ψ ε Λ ρ hΛ hρ U V ω‖ ≤ 2*δ := by
  refine norm_sub _ _
    (Complex.continuous_ofReal.measurable.comp (VectorObservedProfile.measurable φ hφ hε U V hU hV))
    (Complex.continuous_ofReal.measurable.comp (VectorObservedProfile.measurable ψ hψ hε U V hU hV))
    (M := 2*M) (N := 2*N) ?_ ?_ (by positivity) ?_ hΛ hρ ω
  · intro p
    simpa only [Function.comp_def,Complex.norm_real,Real.norm_eq_abs] using VectorObservedProfile.bound φ hφb ε U V p
  · intro p
    simpa only [Function.comp_def,Complex.norm_real,Real.norm_eq_abs] using VectorObservedProfile.bound ψ hψb ε U V p
  · intro p
    dsimp only [Function.comp_def]
    rw [←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
    dsimp only [VectorObservedProfile.difference]
    have he (v u : State n) : φ v-φ u-(ψ v-ψ u)=(φ v-ψ v)-(φ u-ψ u) := by ring
    rw [he]
    exact ((abs_sub _ _).trans (add_le_add (hclose _) (hclose _))).trans_eq (by ring)

theorem value_bound (φ : State n → ℝ) (hφ : Measurable φ)
    {M ε Λ ρ : ℝ} (hM : 0 ≤ M) (hφb : ∀ z,|φ z| ≤ M)
    (hε : 0 < ε) (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ)
    (U V : Ω → Physical (d := Fin n)) (hU : Measurable U) (hV : Measurable V) (ω : Ω) :
    ‖value φ ε Λ ρ hΛ hρ U V ω‖ ≤ 2*M := by
  apply norm_le _
    (Complex.continuous_ofReal.measurable.comp (VectorObservedProfile.measurable φ hφ hε U V hU hV))
    (by positivity : 0 ≤ 2*M) _ hΛ hρ ω
  intro p
  simpa only [Function.comp_def,Complex.norm_real,Real.norm_eq_abs] using
    VectorObservedProfile.bound φ hφb ε U V p

def smooth (φ : State n → ℝ) (j : ℕ) : State n → ℝ :=
  gaussianAverage (IsotropicGaussianHolder.matrix (IsotropicGaussianDyadicBands.variance j)) φ

/-- Positive-variance Gaussian smoothing gives the bounded smooth test
needed for the low mode as well as for every later partial sum. -/
theorem smooth_boundedSmooth (φ : State n → ℝ) (hφ : Measurable φ)
    (M : ℝ) (hφb : ∀ z, |φ z| ≤ M) (j : ℕ) :
    SmoothCylinders.BoundedSmooth (smooth φ j) := by
  refine ⟨contDiff_infty.mpr (fun k => ?_), fun k =>
    ⟨M * IsotropicGaussianJets.constant n k *
      ((Real.sqrt (IsotropicGaussianDyadicBands.variance j))⁻¹)^k, fun z => ?_⟩⟩
  · exact IsotropicGaussianJets.smooth (IsotropicGaussianDyadicBands.variance_pos j)
      φ hφ M hφb k
  · exact IsotropicGaussianJets.bound (IsotropicGaussianDyadicBands.variance_pos j)
      φ hφ M hφb k z

/-- Signed coefficient subtraction is preserved by the actual Borel
Hilbert realization and the massive Bessel multiplier. -/
theorem value_sub (φ ψ : State n → ℝ) (hφ : Measurable φ) (hψ : Measurable ψ)
    {M N ε Λ ρ : ℝ} (hφb : ∀ z,|φ z| ≤ M) (hψb : ∀ z,|ψ z| ≤ N)
    (hε : 0 < ε) (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ)
    (U V : Ω → Physical (d := Fin n)) (hU : Measurable U) (hV : Measurable V) (ω : Ω) :
    value (fun z => φ z-ψ z) ε Λ ρ hΛ hρ U V ω=
      value φ ε Λ ρ hΛ hρ U V ω-value ψ ε Λ ρ hΛ hρ U V ω := by
  let A := fun p => (VectorObservedProfile.difference (fun z => φ z-ψ z) ε U V p : ℂ)
  let B := fun p => (VectorObservedProfile.difference φ ε U V p : ℂ)
  let C := fun p => (VectorObservedProfile.difference ψ ε U V p : ℂ)
  have hm (f : State n → ℝ) (hf : Measurable f) : Measurable
      (fun p => (VectorObservedProfile.difference f ε U V p : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp (VectorObservedProfile.measurable f hf hε U V hU hV)
  have hb (f : State n → ℝ) {R : ℝ} (hf : ∀ z,|f z| ≤ R) (p : Ω×HeatCircle) :
      ‖(VectorObservedProfile.difference f ε U V p : ℂ)‖ ≤ 2*R := by
    simpa only [Complex.norm_real,Real.norm_eq_abs] using VectorObservedProfile.bound f hf ε U V p
  have hsub (z : State n) : |φ z-ψ z| ≤ M+N := (abs_sub _ _).trans (add_le_add (hφb z) (hψb z))
  exact NativeBesselDifferenceIdentity.sub Λ ρ hΛ hρ A B C (hm _ (hφ.sub hψ)) (hm φ hφ) (hm ψ hψ) ω
    (bounded_section A (hm _ (hφ.sub hψ)) (hb _ hsub) ω)
    (bounded_section B (hm φ hφ) (hb φ hφb) ω)
    (bounded_section C (hm ψ hψ) (hb ψ hψb) ω)
    (ae_of_all _ (fun x => by dsimp only [A,B,C,VectorObservedProfile.difference];push_cast;ring))

theorem smooth_measurable (φ : State n → ℝ) (hφ : Measurable φ)
    {M : ℝ} (hφb : ∀ z,|φ z| ≤ M) (j : ℕ) : Measurable (smooth φ j) :=
  (IsotropicGaussianJets.smooth (IsotropicGaussianDyadicBands.variance_pos j) φ hφ M hφb 0).continuous.measurable

theorem smooth_bound (φ : State n → ℝ) {M : ℝ} (hφb : ∀ z,|φ z| ≤ M) (j : ℕ) (z : State n) :
    |smooth φ j z| ≤ M := IsotropicGaussianBands.average_bound _ φ M hφb z

/-- Each actual coefficient band is the difference of its two
adjacent positive-scale smoothings, including after spatial realization. -/
theorem band_succ (φ : State n → ℝ) (hφ : Measurable φ)
    {M ε Λ ρ : ℝ} (hφb : ∀ z,|φ z| ≤ M)
    (hε : 0 < ε) (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ)
    (U V : Ω → Physical (d := Fin n)) (hU : Measurable U) (hV : Measurable V) (j : ℕ) (ω : Ω) :
    value (IsotropicGaussianBands.band (IsotropicGaussianDyadicBands.variance (j+1)) φ) ε Λ ρ hΛ hρ U V ω=
      value (smooth φ (j+1)) ε Λ ρ hΛ hρ U V ω-value (smooth φ j) ε Λ ρ hΛ hρ U V ω := by
  have he : IsotropicGaussianBands.band (IsotropicGaussianDyadicBands.variance (j+1)) φ=
      fun z => smooth φ (j+1) z-smooth φ j z := by
    funext z
    simp only [IsotropicGaussianBands.band,IsotropicGaussianDyadicBands.four_next,smooth]
  rw [he]
  exact value_sub _ _ (smooth_measurable φ hφ hφb (j+1)) (smooth_measurable φ hφ hφb j)
    (smooth_bound φ hφb (j+1)) (smooth_bound φ hφb j) hε hΛ hρ U V hU hV ω

/-- The finite low-plus-band expansion is exactly the actual smoothed
physical coefficient field, not a separately postulated Hilbert series. -/
theorem finite_prefix (φ : State n → ℝ) (hφ : Measurable φ)
    {M ε Λ ρ : ℝ} (hφb : ∀ z,|φ z| ≤ M)
    (hε : 0 < ε) (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ)
    (U V : Ω → Physical (d := Fin n)) (hU : Measurable U) (hV : Measurable V) (J : ℕ) (ω : Ω) :
    value (smooth φ 0) ε Λ ρ hΛ hρ U V ω+
      ∑ j ∈ Finset.range J,
        value (IsotropicGaussianBands.band (IsotropicGaussianDyadicBands.variance (j+1)) φ) ε Λ ρ hΛ hρ U V ω=
      value (smooth φ J) ε Λ ρ hΛ hρ U V ω := by
  induction J with
  | zero => simp only [Finset.range_zero,Finset.sum_empty,add_zero]
  | succ J ih =>
    rw [Finset.sum_range_succ,←add_assoc,ih,band_succ φ hφ hφb hε hΛ hρ U V hU hV J ω]
    abel

/-- Uniform quantitative removal of the actual vector coefficient-band
cutoff, including arbitrary dependent physical source/companion states. -/
theorem cutoff_error (φ : State n → ℝ) (hφ : Measurable φ)
    {M K β ε Λ ρ : ℝ} (hφb : ∀ z,|φ z| ≤ M) (hK : 0 ≤ K) (hβ : 0 ≤ β)
    (hHolder : ∀ z w,|φ z-φ w| ≤ K*‖z-w‖^β)
    (hε : 0 < ε) (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ)
    (U V : Ω → Physical (d := Fin n)) (hU : Measurable U) (hV : Measurable V) (j : ℕ) (ω : Ω) :
    ‖value φ ε Λ ρ hΛ hρ U V ω-value (smooth φ j) ε Λ ρ hΛ hρ U V ω‖ ≤
      2*(K*((2 : ℝ)^j)^(-β)*GaussianNormMoment.moment (Fin n) β) := by
  apply approximation φ (smooth φ j) hφ (smooth_measurable φ hφ hφb j)
    hφb (smooth_bound φ hφb j) _ _ hε hΛ hρ U V hU hV ω
  · exact mul_nonneg (mul_nonneg hK (Real.rpow_nonneg (by positivity) _)) (GaussianNormMoment.nonneg _)
  · intro z
    have hh := IsotropicGaussianDyadicBands.remainder hK hβ φ hφ M hφb hHolder j z
    rwa [IsotropicGaussianDyadicBands.telescope] at hh

/-- Finite vector Gaussian band prefixes converge to the original
coefficient in the actual massive negative spatial Hilbert space. -/
theorem cutoff_tendsto (φ : State n → ℝ) (hφ : Measurable φ)
    {M K β ε Λ ρ : ℝ} (hφb : ∀ z,|φ z| ≤ M) (hK : 0 ≤ K) (hβ : 0 < β)
    (hHolder : ∀ z w,|φ z-φ w| ≤ K*‖z-w‖^β)
    (hε : 0 < ε) (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ)
    (U V : Ω → Physical (d := Fin n)) (hU : Measurable U) (hV : Measurable V) (ω : Ω) :
    Tendsto (fun j => value (smooth φ j) ε Λ ρ hΛ hρ U V ω) atTop
      (𝓝 (value φ ε Λ ρ hΛ hρ U V ω)) := by
  apply Metric.tendsto_atTop.mpr
  intro δ hδ
  have hd := IsotropicGaussianBandSeries.decay hβ (2*K*GaussianNormMoment.moment (Fin n) β)
  obtain ⟨J,hJ⟩ := eventually_atTop.mp ((tendsto_order.mp hd).2 δ hδ)
  refine ⟨J,fun j hj => ?_⟩
  rw [dist_eq_norm,norm_sub_rev]
  exact (cutoff_error φ hφ hφb hK hβ.le hHolder hε hΛ hρ U V hU hV j ω).trans_lt
    (by convert hJ j hj using 1;ring)

/-- The full expected negative coefficient energy is the limit of the
true finite Gaussian-band energies. No new stochastic limit is assumed. -/
theorem energy_tendsto (μ : Measure Ω) [IsFiniteMeasure μ]
    (φ : State n → ℝ) (hφ : Measurable φ)
    {M K β ε Λ ρ : ℝ} (hM : 0 ≤ M) (hφb : ∀ z,|φ z| ≤ M) (hK : 0 ≤ K) (hβ : 0 < β)
    (hHolder : ∀ z w,|φ z-φ w| ≤ K*‖z-w‖^β)
    (hε : 0 < ε) (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ)
    (U V : Ω → Physical (d := Fin n)) (hU : Measurable U) (hV : Measurable V) :
    Tendsto (fun j => ∫ ω,‖value (smooth φ j) ε Λ ρ hΛ hρ U V ω‖^2 ∂μ) atTop
      (𝓝 (∫ ω,‖value φ ε Λ ρ hΛ hρ U V ω‖^2 ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun _ : Ω => (2*M)^2)
  · intro j
    exact ((measurable (smooth φ j) (smooth_measurable φ hφ hφb j) hε hΛ hρ U V hU hV).norm.pow_const 2).aestronglyMeasurable
  · exact integrable_const _
  · intro j
    apply ae_of_all
    intro ω
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _)
      (value_bound (smooth φ j) (smooth_measurable φ hφ hφb j) hM (smooth_bound φ hφb j)
        hε hΛ hρ U V hU hV ω) 2
  · exact ae_of_all _ (fun ω => (cutoff_tendsto φ hφ hφb hK hβ hHolder hε hΛ hρ U V hU hV ω).norm.pow 2)

/-- Bounds for the genuine finite low-plus-band energies pass to the
full rough vector coefficient, on the original probability/time measure. -/
theorem energy_le_of_prefix (μ : Measure Ω) [IsFiniteMeasure μ]
    (φ : State n → ℝ) (hφ : Measurable φ)
    {M K β ε Λ ρ C : ℝ} (hM : 0 ≤ M) (hφb : ∀ z,|φ z| ≤ M) (hK : 0 ≤ K) (hβ : 0 < β)
    (hHolder : ∀ z w,|φ z-φ w| ≤ K*‖z-w‖^β)
    (hε : 0 < ε) (hΛ : 1 ≤ Λ) (hρ : 0 ≤ ρ)
    (U V : Ω → Physical (d := Fin n)) (hU : Measurable U) (hV : Measurable V)
    (hPrefix : ∀ J,(∫ ω,‖value (smooth φ 0) ε Λ ρ hΛ hρ U V ω+
      ∑ j ∈ Finset.range J,
        value (IsotropicGaussianBands.band (IsotropicGaussianDyadicBands.variance (j+1)) φ) ε Λ ρ hΛ hρ U V ω‖^2 ∂μ) ≤ C) :
    (∫ ω,‖value φ ε Λ ρ hΛ hρ U V ω‖^2 ∂μ) ≤ C := by
  apply le_of_tendsto (energy_tendsto μ φ hφ hM hφb hK hβ hHolder hε hΛ hρ U V hU hV)
  exact Eventually.of_forall (fun J => by simpa only [finite_prefix φ hφ hφb hε hΛ hρ U V hU hV] using hPrefix J)

/-- Every bounded smooth vector test supplies its own global
Lipschitz/Holder input for the checked heat-endpoint removal. -/
theorem boundedSmooth_holder (φ : State n → ℝ) (hφ : SmoothCylinders.BoundedSmooth φ) :
    ∃ C : ℝ≥0,HolderWith C 1 φ := by
  obtain ⟨L,hL⟩ := hφ.fderiv.norm_bound
  let C : ℝ≥0 := ⟨max L 0,le_max_right _ _⟩
  refine ⟨C,?_⟩
  apply LipschitzWith.holderWith
  apply lipschitzWith_of_nnnorm_fderiv_le (hφ.smooth.differentiable (by simp))
  intro z
  exact_mod_cast (hL z).trans (le_max_left L 0)

end SHEStochastic.VectorObservedBandLimit



