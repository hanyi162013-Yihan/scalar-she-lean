module

public import SHEStochastic.PolynomialTailEnvelope

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section

namespace SHEStochastic.NatTailEnergyUniformity
open MeasureTheory Filter Set
open scoped ENNReal Topology
variable {Ω Ξ E : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ] [NormedAddCommGroup E]

/-- A natural-level norm tail bound yields an integrable real-level
squared-norm envelope. The fixed initial L2 tail is retained exactly;
only harmless numerical constants are enlarged. -/
theorem bound (μ : Measure Ω) [IsProbabilityMeasure μ] (ρ : Measure Ξ) (g : Ξ → ℝ)
    (X : Ω → E) (A : ℝ≥0∞) (a : ℝ) (ha : a<0)
    (htail : ∀ N : ℕ,1≤N → μ {ω | (N : ℝ)≤‖X ω‖}≤
      ρ {z | (N : ℝ)/2≤g z}+A*(N : ℝ≥0∞)^a)
    (r : ℝ) (hr : 0<r) :
    μ {ω | r≤‖X ω‖^2}≤PolynomialTailEnvelope.value ρ g A a r := by
  by_cases hsmall : r≤16
  · apply (measure_mono (Set.subset_univ _) : μ {ω | r≤‖X ω‖^2}≤μ Set.univ).trans
    rw [measure_univ]
    simp only [PolynomialTailEnvelope.value,Set.indicator_apply,Set.mem_Ioc,hr,hsmall,
      and_self,ite_true]
    exact (le_add_of_nonneg_right (bot_le : (0 : ℝ≥0∞)≤_)).trans
      (le_add_of_nonneg_right (bot_le : (0 : ℝ≥0∞)≤_))
  · have hr16 : (16 : ℝ)<r := lt_of_not_ge hsmall
    have hs : 4<Real.sqrt r := by nlinarith [Real.sq_sqrt hr.le,Real.sqrt_nonneg r]
    let N : ℕ := ⌊Real.sqrt r⌋₊
    have hNF : (N : ℝ)≤Real.sqrt r := Nat.floor_le (Real.sqrt_nonneg r)
    have hFN : Real.sqrt r<(N : ℝ)+1 := Nat.lt_floor_add_one _
    have hNhalf : Real.sqrt r/2≤N := by linarith
    have hNpos : 0<N := Nat.floor_pos.mpr (by linarith)
    have hN1 : 1≤N := hNpos
    have hp : μ {ω | r≤‖X ω‖^2}≤μ {ω | (N : ℝ)≤‖X ω‖} := by
      apply measure_mono
      intro ω hω
      change r≤‖X ω‖^2 at hω
      have hroot : Real.sqrt r≤‖X ω‖ := by nlinarith [Real.sq_sqrt hr.le,Real.sqrt_nonneg r,norm_nonneg (X ω)]
      exact hNF.trans hroot
    have hinit : ρ {z | (N : ℝ)/2≤g z}≤ρ {z | r≤16*(g z)^2} := by
      apply measure_mono
      intro z hz
      change (N : ℝ)/2≤g z at hz
      change r≤16*(g z)^2
      have hh : Real.sqrt r≤4*g z := by linarith
      have hsq := pow_le_pow_left₀ (Real.sqrt_nonneg r) hh 2
      nlinarith [Real.sq_sqrt hr.le]
    have hpow : (N : ℝ≥0∞)^a≤ENNReal.ofReal ((2 : ℝ)^(-a))*ENNReal.ofReal (r^(a/2)) := by
      have hhalf : 0<Real.sqrt r/2 := by positivity
      have hh := Real.rpow_le_rpow_of_nonpos hhalf hNhalf ha.le
      have he : (Real.sqrt r/2)^a=(2 : ℝ)^(-a)*r^(a/2) := by
        rw [Real.div_rpow (Real.sqrt_nonneg r) (by norm_num : (0 : ℝ)≤2),Real.sqrt_eq_rpow,
          ←Real.rpow_mul hr.le,show (1/2 : ℝ)*a=a/2 by ring,
          Real.rpow_neg (by norm_num : (0 : ℝ)≤2),div_eq_mul_inv,mul_comm]
      calc
        _ = ENNReal.ofReal ((N : ℝ)^a) := by
          simpa only [ENNReal.ofReal_natCast] using
            (ENNReal.ofReal_rpow_of_pos (show (0 : ℝ)<N by exact_mod_cast hNpos) :
              ENNReal.ofReal (N : ℝ)^a=ENNReal.ofReal ((N : ℝ)^a))
        _ ≤ ENNReal.ofReal ((Real.sqrt r/2)^a) := ENNReal.ofReal_le_ofReal hh
        _ = _ := by rw [he,ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num : (0 : ℝ)≤2) _)]
    apply (hp.trans (htail N hN1)).trans
    have he := add_le_add hinit (mul_le_mul_right hpow A)
    simpa only [PolynomialTailEnvelope.value,PolynomialTailEnvelope.initial,PolynomialTailEnvelope.power,
      Set.indicator_apply,Set.mem_Ioc,Set.mem_Ioi,hr,hsmall,hr16,true_and,and_false,
      ite_true,ite_false,zero_add,mul_assoc] using he

/-- The preceding bounds give uniformly vanishing squared-norm tail
energies with only the prescribed initial L2 law, on varying spaces. -/
theorem uniform_tails [MeasurableSpace E] [BorelSpace E]
    {Ξm : ℕ → Type*} [∀ m,MeasurableSpace (Ξm m)]
    (P : ∀ m,Measure (Ξm m)) [∀ m,IsProbabilityMeasure (P m)]
    (X : ∀ m,Ξm m → E) (hX : ∀ m,Measurable (X m))
    (ρ : Measure Ξ) (g : Ξ → ℝ) (hg : Measurable g) (hL2 : MemLp g 2 ρ)
    (A : ℝ≥0∞) (hA : A≠⊤) (a : ℝ) (ha : a < -2)
    (htail : ∀ m (N : ℕ),1≤N → (P m) {ω | (N : ℝ)≤‖X m ω‖}≤
      ρ {z | (N : ℝ)/2≤g z}+A*(N : ℝ≥0∞)^a) :
    Tendsto (fun R : ℕ => ⨆ m,∫⁻ ω in {ω | (R : ℝ)≤‖X m ω‖^2},
      ENNReal.ofReal (‖X m ω‖^2) ∂P m) atTop (𝓝 0) :=
  TailIntegralUniformity.uniform_tails P (fun m ω => ‖X m ω‖^2) (fun m => (hX m).norm.pow_const 2)
    (PolynomialTailEnvelope.value ρ g A a) (PolynomialTailEnvelope.measurable ρ g A a)
    (PolynomialTailEnvelope.finite ρ g hg hL2 A hA a ha)
    (fun m r hr => bound (P m) ρ g (X m) A a (by linarith) (htail m) r hr)

end SHEStochastic.NatTailEnergyUniformity
