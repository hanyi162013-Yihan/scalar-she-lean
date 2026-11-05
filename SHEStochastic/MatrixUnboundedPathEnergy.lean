module

public import SHEStochastic.MatrixExitPolynomialTail
public import SHEStochastic.ContinuousPathExitNorm
public import SHEStochastic.NatTailEnergyUniformity

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.MatrixUnboundedPathEnergy
open MeasureTheory ProbabilityTheory Filter SHE SHE.PredictableL2 MatrixInfiniteHaar Matrix
open scoped Topology NNReal ENNReal MatrixOrder Matrix.Norms.L2Operator
local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact ((2 : ENNReal)≠⊤) := ⟨by simp⟩
variable {n : ℕ} (G : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ)
    {C β : ℝ≥0} (hG : HolderWith C β G) (hβ : 0<β) (hβ1 : β<1)
    (ell : ℝ) (hell : 0<ell)
    (hLower : ∀ z,ell • (1 : Matrix (Fin n) (Fin n) ℝ) ≤ G z*(G z)ᴴ)
local notation "G_R" R => MatrixUnboundedCutoff.coefficient G hG hβ ell hell hLower R
local instance : SecondCountableTopology (Physical (d := Fin n)) := Lp.SecondCountableTopology
local instance : MeasurableSpace (Physical (d := Fin n)) := borel _
local instance : BorelSpace (Physical (d := Fin n)) := ⟨rfl⟩

include hβ1 in
/-- Choose an actual dyadic moment order with an integrable energy
tail exponent, together with a positive admissible field regularity. -/
theorem exists_order : ∃ k : ℕ,
    2<UnboundedHeatIncrementCaps.exponent β*(2^k : ℕ) ∧
    (2*(β : ℝ)-2)*(2^k : ℕ)< -2 ∧
    ∃ α : ℝ≥0,0<α ∧ (α : ℝ)<
      (UnboundedHeatIncrementCaps.exponent β*(2^k : ℕ)-2)/(2*2^k : ℕ) := by
  have hb := UnboundedHeatIncrementCaps.exponent_pos hβ1
  have hβr : (β : ℝ)<1 := by exact_mod_cast hβ1
  have hd : 0<2-2*(β : ℝ) := by nlinarith
  obtain ⟨k,hk⟩ := pow_unbounded_of_one_lt
    (max (2/UnboundedHeatIncrementCaps.exponent β) (2/(2-2*(β : ℝ))))
    (by norm_num : (1 : ℝ)<2)
  have h1 := (div_lt_iff₀ hb).mp (lt_of_le_of_lt (le_max_left _ _) hk)
  have h2 := (div_lt_iff₀ hd).mp (lt_of_le_of_lt (le_max_right _ _) hk)
  have hq : 2<UnboundedHeatIncrementCaps.exponent β*(2^k : ℕ) := by
    push_cast
    nlinarith
  have he : (2*(β : ℝ)-2)*(2^k : ℕ)< -2 := by
    push_cast
    nlinarith
  obtain ⟨a,ha,haq⟩ := exists_between
    (div_pos (sub_pos.mpr hq) (by positivity : (0 : ℝ)<(2*2^k : ℕ)))
  exact ⟨k,hq,he,⟨a,ha.le⟩,ha,haq⟩

include hβ1 in
/-- Squared full L2 path norms of actual bounded-cutoff solutions are
uniformly integrable, even on varying probability spaces. Only the
prescribed initial L2 law is required; no fourth initial moment is used. -/
theorem uniform_tails (H : ℝ≥0) (hH : (H : ℝ)≤1) (hH0 : 0<H)
    {Ξ : ℕ → Type*} [∀ m,MeasurableSpace (Ξ m)]
    (D : ∀ m,Filtration ℝ≥0 (inferInstance : MeasurableSpace (Ξ m)))
    (μ : ∀ m,Measure (Ξ m)) [∀ m,IsProbabilityMeasure (μ m)]
    (U : ∀ m,ℝ≥0×Ξ m → Physical (d := Fin n))
    (hU : ∀ m,StronglyMeasurable[(D m).predictable] (U m))
    (hcU : ∀ m ω,Continuous (fun t => U m (t,ω))) (radii : ℕ → ℝ≥0)
    (B : ∀ m,FiniteScalarIto.Family (D m) (μ m) H (Fin n×SHE.FiniteHaar.HaarNode))
    (hnull : ∀ m,NullCompleteFiltration.ContainsNullSets (D m) (μ m))
    (ξ : ∀ m,Ξ m → Physical (d := Fin n)) (hξ : ∀ m,Measurable (ξ m))
    (hEq : ∀ m,MatrixRandomMildExistence.Equation (G_R (radii m)) hH (B m) (U m) (hU m) (ξ m))
    (ρ : ProbabilityMeasure (Physical (d := Fin n)))
    (hL2 : MemLp (id : Physical (d := Fin n) → Physical (d := Fin n)) 2 ρ.toMeasure)
    (hInitial : ∀ m,(μ m).map (ξ m)=ρ.toMeasure) :
    Tendsto (fun R : ℕ => ⨆ m,∫⁻ ω in {ω | (R : ℝ)≤
      ‖NativeContinuousPath.path H (fun t ω => U m (t,ω)) (hcU m) ω‖^2},
      ENNReal.ofReal (‖NativeContinuousPath.path H (fun t ω => U m (t,ω)) (hcU m) ω‖^2) ∂μ m)
      atTop (𝓝 0) := by
  obtain ⟨k,hq,ha,α,hα,hαq⟩ := exists_order (β := β) hβ1
  let a : ℝ := (2*(β : ℝ)-2)*(2^k : ℕ)
  let A : ℝ≥0∞ := (n : ℝ≥0∞)*MatrixExitPolynomialTail.constant G (C := C) (β := β) H k α
  have hA : A≠⊤ := by
    dsimp only [A]
    exact ENNReal.mul_ne_top (by simp) (MatrixExitPolynomialTail.constant_finite G H k hq α hαq)
  let X := fun m => NativeContinuousPath.path H (fun t ω => U m (t,ω)) (hcU m)
  have hX (m : ℕ) : Measurable (X m) :=
    NativeContinuousPath.measurable_path H (fun t ω => U m (t,ω)) (hcU m)
      ((hU m).mono (predictable_le_product (D m))).measurable
  apply NatTailEnergyUniformity.uniform_tails μ X hX ρ.toMeasure (fun u => ‖u‖)
    measurable_norm hL2.norm A hA a ha
  intro m N hN
  have he : {ω | (N : ℝ)≤‖X m ω‖}=
      {ω | ContinuousNormExit.exit (fun t ω => U m (t,ω)) N ω≤(H : WithTop ℝ≥0)} := by
    ext ω
    exact ContinuousPathExitNorm.le_iff H (fun t ω => U m (t,ω)) (hcU m) N ω
  rw [he]
  have hb := MatrixUnboundedExitTail.law_bound G hG hβ hβ1 ell hell hLower (D m) H hH hH0
    (μ m) (U m) (hU m) (hcU m) (radii m) (B m) (hnull m) (ξ m) (hξ m) (hEq m)
    ρ.toMeasure (hInitial m) N (by omega) k hq α hα
  have hp := MatrixExitPolynomialTail.bound G (C := C) H hβ k hq α hαq N hN
  apply hb.trans
  simpa only [MatrixUnboundedExitTail.envelope,MatrixUnboundedExitTail.initialTail,A,a,mul_assoc] using
    add_le_add (le_rfl : ρ.toMeasure {u | (N : ℝ)/2≤‖u‖}≤_)
      (mul_le_mul_right hp (n : ℝ≥0∞))

end SHEStochastic.MatrixUnboundedPathEnergy
