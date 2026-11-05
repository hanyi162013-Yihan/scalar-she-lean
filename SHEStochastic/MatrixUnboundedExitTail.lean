module

public import SHEStochastic.MatrixUnboundedPointMaximum
public import SHEStochastic.MatrixLocalizedExitProbability
public import SHEStochastic.HeatFieldThreshold
public import SHEStochastic.UnboundedMomentBounds

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.MatrixUnboundedExitTail
open MeasureTheory ProbabilityTheory Filter SHE SHE.PredictableL2 SHE.StoppedFourier MatrixInfiniteHaar Matrix
open HeatParameterCover HeatParameterCoordinates
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local instance : Fact ((2 : ENNReal)≠⊤) := ⟨by simp⟩
variable {n : ℕ} (G : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ)
    {C β : ℝ≥0} (hG : HolderWith C β G) (hβ : 0<β) (hβ1 : β<1)
    (ell : ℝ) (hell : 0<ell)
    (hLower : ∀ z,ell • (1 : Matrix (Fin n) (Fin n) ℝ) ≤ G z*(G z)ᴴ)
local notation "G_R" R => MatrixUnboundedCutoff.coefficient G hG hβ ell hell hLower R
variable {Ω : Type*} [MeasurableSpace Ω]
local instance : SecondCountableTopology (Physical (d := Fin n)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (Physical (d := Fin n)) := borel _
local instance : BorelSpace (Physical (d := Fin n)) := ⟨rfl⟩
local instance : MeasurableSpace (Input (d := Fin n)) := borel _
local instance : BorelSpace (Input (d := Fin n)) := ⟨rfl⟩
variable (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (H : ℝ≥0) (hH : (H : ℝ)≤1) (hH0 : 0<H)

/-- A single scalar-field error, uniform over all coefficient cutoffs
and all solutions after the stated L2 history localization. -/
def error (k : ℕ) (α : ℝ≥0) (N : ℕ) : ℝ≥0∞ :=
  (MatrixUnboundedPointMaximum.momentConstant G (C := C) (β := β) H (N : ℝ) k*
    constL 64 2 (2*2^k : ℕ) (UnboundedHeatIncrementCaps.exponent β*(2^k : ℕ)) α)/
      (HeatFieldThreshold.level n α (2*2^k) N : ℝ≥0∞)

include hβ hβ1 in
/-- The actual localized stochastic field error tends to zero under
sublinear growth, retaining the original finite-dimensional geometry. -/
theorem error_tendsto (k : ℕ) (hq : 2<UnboundedHeatIncrementCaps.exponent β*(2^k : ℕ))
    (α : ℝ≥0) (hα : (α : ℝ)<(UnboundedHeatIncrementCaps.exponent β*(2^k : ℕ)-2)/(2*2^k : ℕ)) :
    Tendsto (error G (C := C) (β := β) H k α) atTop (𝓝 0) := by
  have hc := constL_lt_top (by norm_num : (64 : ℝ≥0∞)≠⊤) (by norm_num : (0 : ℝ)<2)
    (by positivity : (0 : ℝ)<(2*2^k : ℕ)) hq hα
  have hl := HeatFieldThreshold.scaled_tendsto n α (2*2^k)
    (fun N => MatrixUnboundedPointMaximum.momentConstant G (C := C) (β := β) H (N : ℝ) k)
    (fun N => MatrixUnboundedPointMaximum.moment_finite G H (N : ℝ) k)
    (MatrixUnboundedPointMaximum.normalized_moment_tendsto G hβ hβ1 H k)
  have ht := ENNReal.Tendsto.mul_const (b := constL 64 2 (2*2^k : ℕ)
    (UnboundedHeatIncrementCaps.exponent β*(2^k : ℕ)) α) hl (Or.inr hc.ne)
  simp only [zero_mul] at ht
  apply ht.congr
  intro N
  dsimp only [error]
  simp only [div_eq_mul_inv]
  ring

include hβ1 in
/-- The geometric level is exactly the scalar-field threshold in the
proved vector exit bound. No coefficient cutoff enters its error. -/
theorem scalar_bound (μ : Measure Ω) [IsProbabilityMeasure μ]
    (U : ℝ≥0×Ω → Physical (d := Fin n)) (hU : StronglyMeasurable[F.predictable] U)
    (R : ℝ≥0) (B : FiniteScalarIto.Family F μ H (Fin n×SHE.FiniteHaar.HaarNode)) (i : Fin n)
    (N : ℕ) (hN : 0<N) (hbound : ∀ᵐ z ∂energyMeasure μ H,‖U z‖≤(N : ℝ))
    (Y : Ω → C(Parameter,ℝ)) (hY : Measurable Y)
    (hrep : ∀ p,(fun ω => Y ω p)=ᵐ[μ]
      MatrixUnboundedPointTightness.value G hG hβ ell hell hLower F H hH μ U hU R B p i)
    (hzero : ∀ᵐ ω ∂μ,∀ p,Y ω (zeroTime p)=0)
    (k : ℕ) (hq : 2<UnboundedHeatIncrementCaps.exponent β*(2^k : ℕ))
    (α : ℝ≥0) (hα : 0<α) :
    μ {ω | (N : ℝ)/(4*((n : ℝ)+1))<‖Y ω‖}≤error G (C := C) (β := β) H k α N := by
  have ht := MatrixUnboundedPointMaximum.tail G hG hβ hβ1 ell hell hLower F H hH μ U hU R B i
    hbound Y hY hrep hzero k hq α (HeatFieldThreshold.level n α (2*2^k) N) hα
    (HeatFieldThreshold.level_pos n α (2*2^k) N hN)
  simpa only [error,HeatFieldThreshold.amplitude_level n α (2*2^k) N (by positivity)] using ht

include hβ1 hH0 in
/-- Uniform exit bound for an ACTUAL cutoff-equation solution, using
only its native mild equation and prescribed L2 initial state. All
localized field versions are constructed by the existing bounded theory. -/
theorem exit_bound (μ : Measure Ω) [IsProbabilityMeasure μ]
    (U : ℝ≥0×Ω → Physical (d := Fin n)) (hU : StronglyMeasurable[F.predictable] U)
    (hcU : ∀ ω,Continuous (fun t => U (t,ω))) (R : ℝ≥0)
    (B : FiniteScalarIto.Family F μ H (Fin n×SHE.FiniteHaar.HaarNode))
    (hnull : NullCompleteFiltration.ContainsNullSets F μ)
    (ξ : Ω → Physical (d := Fin n)) (hξ : Measurable ξ)
    (hEq : MatrixRandomMildExistence.Equation (G_R R) hH B U hU ξ)
    (N : ℕ) (hN : 0<N)
    (k : ℕ) (hq : 2<UnboundedHeatIncrementCaps.exponent β*(2^k : ℕ))
    (α : ℝ≥0) (hα : 0<α) :
    μ {ω | ContinuousNormExit.exit (fun t ω => U (t,ω)) N ω≤(H : WithTop ℝ≥0)} ≤
      μ {ω | (N : ℝ)/2≤‖ξ ω‖}+(n : ℝ≥0∞)*error G (C := C) (β := β) H k α N := by
  let W := MatrixL2LocalizedPointRows.state U (N : ℝ≥0)
  have hW := MatrixL2LocalizedPointRows.predictable F U hU (N : ℝ≥0)
  choose Y hm he hz using fun i : Fin n => MatrixPointFieldTightness.exists_version F μ H
    (NativeMatrixEquation.cap (G_R R)) (NativeMatrixEquation.cap_nonneg (G_R R))
    (NativeMatrixEquation.profile F (G_R R) W hW) (fun _ => le_rfl) hH
    (NativeMatrixEquation.profile_measurable F (G_R R) W hW) B i
  have hb := MatrixLocalizedExitProbability.bound F (G_R R) U hU μ H hH hH0 hcU N hN B hnull
    ξ hξ hEq (fun ω i => Y i ω) (fun p i => he i p) (ae_all_iff.mpr hz)
  apply hb.trans
  apply add_le_add le_rfl
  have htail (i : Fin n) : μ {ω | (N : ℝ)/(4*((n : ℝ)+1))<‖Y i ω‖}≤error G (C := C) (β := β) H k α N :=
    scalar_bound G hG hβ hβ1 ell hell hLower F H hH μ W hW R B i N hN
      (Filter.Eventually.of_forall (MatrixL2LocalizedPointRows.norm_bound U (N : ℝ≥0)))
      (Y i) (hm i) (he i) (hz i) k hq α hα
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using
    Finset.sum_le_sum (s := Finset.univ) (fun i _ => htail i)

def initialTail (ρ : Measure (Physical (d := Fin n))) (N : ℕ) : ℝ≥0∞ :=
  ρ {u | (N : ℝ)/2≤‖u‖}

theorem initial_tendsto (ρ : Measure (Physical (d := Fin n))) [IsFiniteMeasure ρ] :
    Tendsto (initialTail ρ) atTop (𝓝 0) := by
  have ht := UnboundedMomentBounds.tails_vanish ρ (fun u => 2*‖u‖) (measurable_const.mul measurable_norm)
  convert ht using 1
  funext N
  apply congrArg ρ
  ext u
  change ((N : ℝ)/2≤‖u‖)↔((N : ℝ)≤2*‖u‖)
  constructor <;> intro h <;> linarith

def envelope (ρ : Measure (Physical (d := Fin n))) (k : ℕ) (α : ℝ≥0) (N : ℕ) : ℝ≥0∞ :=
  initialTail ρ N+(n : ℝ≥0∞)*error G (C := C) (β := β) H k α N

include hβ hβ1 in
/-- The radius-uniform nonexplosion envelope vanishes for every finite
initial L2 law, without requiring an initial supremum norm. -/
theorem envelope_tendsto (ρ : Measure (Physical (d := Fin n))) [IsFiniteMeasure ρ]
    (k : ℕ) (hq : 2<UnboundedHeatIncrementCaps.exponent β*(2^k : ℕ))
    (α : ℝ≥0) (hα : (α : ℝ)<(UnboundedHeatIncrementCaps.exponent β*(2^k : ℕ)-2)/(2*2^k : ℕ)) :
    Tendsto (envelope G (C := C) (β := β) H ρ k α) atTop (𝓝 0) := by
  have he := ENNReal.Tendsto.const_mul (a := (n : ℝ≥0∞)) (error_tendsto G (C := C) hβ hβ1 H k hq α hα)
    (Or.inr (by simp))
  change Tendsto (fun N => initialTail ρ N+(n : ℝ≥0∞)*error G (C := C) (β := β) H k α N) atTop (𝓝 0)
  simpa only [mul_zero,add_zero] using (initial_tendsto ρ).add he

include hβ1 hH0 in
/-- The preceding bound depends on the actual solution's initial law
only. Its other constants are uniform over every coefficient cutoff. -/
theorem law_bound (μ : Measure Ω) [IsProbabilityMeasure μ]
    (U : ℝ≥0×Ω → Physical (d := Fin n)) (hU : StronglyMeasurable[F.predictable] U)
    (hcU : ∀ ω,Continuous (fun t => U (t,ω))) (R : ℝ≥0)
    (B : FiniteScalarIto.Family F μ H (Fin n×SHE.FiniteHaar.HaarNode))
    (hnull : NullCompleteFiltration.ContainsNullSets F μ)
    (ξ : Ω → Physical (d := Fin n)) (hξ : Measurable ξ)
    (hEq : MatrixRandomMildExistence.Equation (G_R R) hH B U hU ξ)
    (ρ : Measure (Physical (d := Fin n))) (hInitial : μ.map ξ=ρ)
    (N : ℕ) (hN : 0<N)
    (k : ℕ) (hq : 2<UnboundedHeatIncrementCaps.exponent β*(2^k : ℕ))
    (α : ℝ≥0) (hα : 0<α) :
    μ {ω | ContinuousNormExit.exit (fun t ω => U (t,ω)) N ω≤(H : WithTop ℝ≥0)} ≤
      envelope G (C := C) (β := β) H ρ k α N := by
  have hb := exit_bound G hG hβ hβ1 ell hell hLower F H hH hH0 μ U hU hcU R B hnull ξ hξ hEq N hN k hq α hα
  have he : μ {ω | (N : ℝ)/2≤‖ξ ω‖}=initialTail ρ N := by
    calc
      _ = (μ.map ξ) {u | (N : ℝ)/2≤‖u‖} :=
        (Measure.map_apply hξ (measurableSet_le measurable_const measurable_norm)).symm
      _ = _ := by rw [hInitial];rfl
  rw [he] at hb
  exact hb

include hβ hβ1 hH0 in
/-- Uniform nonexplosion for arbitrary actual cutoff-solution families.
The probability spaces, filtrations and Brownian realizations may all
vary with the coefficient cutoff. No solution compatibility or
uniqueness assumption is needed. -/
theorem uniform_nonexplosion {Ξ : ℕ → Type*} [∀ m,MeasurableSpace (Ξ m)]
    (D : ∀ m,Filtration ℝ≥0 (inferInstance : MeasurableSpace (Ξ m)))
    (μ : ∀ m,Measure (Ξ m)) [∀ m,IsProbabilityMeasure (μ m)]
    (U : ∀ m,ℝ≥0×Ξ m → Physical (d := Fin n))
    (hU : ∀ m,StronglyMeasurable[(D m).predictable] (U m))
    (hcU : ∀ m ω,Continuous (fun t => U m (t,ω))) (radii : ℕ → ℝ≥0)
    (B : ∀ m,FiniteScalarIto.Family (D m) (μ m) H (Fin n×SHE.FiniteHaar.HaarNode))
    (hnull : ∀ m,NullCompleteFiltration.ContainsNullSets (D m) (μ m))
    (ξ : ∀ m,Ξ m → Physical (d := Fin n)) (hξ : ∀ m,Measurable (ξ m))
    (hEq : ∀ m,MatrixRandomMildExistence.Equation (G_R (radii m)) hH (B m) (U m) (hU m) (ξ m))
    (ρ : ProbabilityMeasure (Physical (d := Fin n))) (hInitial : ∀ m,(μ m).map (ξ m)=ρ.toMeasure) :
    Tendsto (fun N : ℕ => ⨆ m,(μ m) {ω | ContinuousNormExit.exit (fun t ω => U m (t,ω)) N ω≤(H : WithTop ℝ≥0)})
      atTop (𝓝 0) := by
  have hbase := UnboundedHeatIncrementCaps.exponent_pos hβ1
  obtain ⟨k,hk⟩ := pow_unbounded_of_one_lt (2/UnboundedHeatIncrementCaps.exponent β) (by norm_num : (1 : ℝ)<2)
  have hq : 2<UnboundedHeatIncrementCaps.exponent β*(2^k : ℕ) := by
    have hh := (div_lt_iff₀ hbase).mp hk
    push_cast
    nlinarith
  obtain ⟨a,ha,haq⟩ := exists_between (div_pos (sub_pos.mpr hq) (by positivity : (0 : ℝ)<(2*2^k : ℕ)))
  let α : ℝ≥0 := ⟨a,ha.le⟩
  have hlim := envelope_tendsto G (C := C) hβ hβ1 H ρ.toMeasure k hq α haq
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Filter.Eventually.of_forall (fun _ => zero_le))
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  apply iSup_le
  intro m
  exact law_bound G hG hβ hβ1 ell hell hLower (D m) H hH hH0 (μ m) (U m) (hU m) (hcU m) (radii m)
    (B m) (hnull m) (ξ m) (hξ m) (hEq m) ρ.toMeasure (hInitial m) N (lt_of_lt_of_le Nat.zero_lt_one hN) k hq α ha

end SHEStochastic.MatrixUnboundedExitTail
