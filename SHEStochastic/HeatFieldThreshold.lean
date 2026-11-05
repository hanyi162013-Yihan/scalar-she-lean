module

public import SHEStochastic.KolmogorovFieldMaximum
public import SHEStochastic.HeatParameterCover

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
noncomputable section

namespace SHEStochastic.HeatFieldThreshold
open MeasureTheory Filter SHEStochastic.HeatParameterCover
open scoped Topology NNReal ENNReal

def diameterFactor (α : ℝ≥0) : ℝ≥0 :=
  ⟨(max 1 (Metric.diam (Set.univ : Set Parameter)))^(α : ℝ),Real.rpow_nonneg (by positivity) _⟩

theorem diameter_pos (α : ℝ≥0) : 0<diameterFactor α :=
  Real.rpow_pos_of_pos (zero_lt_one.trans_le (le_max_left _ _)) _

def denominator (n : ℕ) (α : ℝ≥0) : ℝ≥0 := 4*((n : ℝ≥0)+1)*diameterFactor α

theorem denominator_pos (n : ℕ) (α : ℝ≥0) : 0<denominator n α :=
  mul_pos (by positivity) (diameter_pos α)

/-- Chentsov control level corresponding exactly to the scalar-field
threshold appearing in the genuine vector L2 exit probability bound. -/
def level (n : ℕ) (α : ℝ≥0) (p N : ℕ) : ℝ≥0 := ((N : ℝ≥0)/denominator n α)^p

theorem level_pos (n : ℕ) (α : ℝ≥0) (p N : ℕ) (hN : 0<N) : 0<level n α p N :=
  pow_pos (div_pos (by exact_mod_cast hN) (denominator_pos n α)) p

theorem amplitude_level (n : ℕ) (α : ℝ≥0) (p N : ℕ) (hp : 0<p) :
    KolmogorovFieldMaximum.amplitude (T := Parameter) (p : ℝ) α (level n α p N)=
      (N : ℝ)/(4*((n : ℝ)+1)) := by
  have hroot : (((level n α p N : ℝ≥0∞)^((p : ℝ)⁻¹)).toNNReal)=(N : ℝ≥0)/denominator n α := by
    unfold level
    rw [←ENNReal.coe_rpow_of_nonneg _ (inv_nonneg.mpr (Nat.cast_nonneg p)),ENNReal.toNNReal_coe]
    exact NNReal.pow_rpow_inv_natCast _ (Nat.ne_of_gt hp)
  unfold KolmogorovFieldMaximum.amplitude
  rw [hroot]
  simp only [NNReal.coe_div,NNReal.coe_natCast,denominator,NNReal.coe_mul,NNReal.coe_ofNat,
    NNReal.coe_add,NNReal.coe_one,diameterFactor]
  have hd : (max 1 (Metric.diam (Set.univ : Set Parameter)))^(α : ℝ)≠0 :=
    ne_of_gt (Real.rpow_pos_of_pos (zero_lt_one.trans_le (le_max_left _ _)) _)
  have hn : (n : ℝ)+1≠0 := by positivity
  change ((N : ℝ)/(4*((n : ℝ)+1)*(max 1 (Metric.diam (Set.univ : Set Parameter)))^(α : ℝ)))*
    (max 1 (Metric.diam (Set.univ : Set Parameter)))^(α : ℝ)=(N : ℝ)/(4*((n : ℝ)+1))
  field_simp

/-- Exact geometric rescaling of a finite stochastic tail constant. -/
theorem scaled_eq (n : ℕ) (α : ℝ≥0) (p : ℕ) (a : ℝ≥0∞) (ha : a≠⊤) (N : ℕ) (hn : 0<N) :
    a/(level n α p N : ℝ≥0∞)=(a/(N : ℝ≥0∞)^p)*(denominator n α : ℝ≥0∞)^p := by
  have hnp : (N : ℝ≥0)^p≠0 := pow_ne_zero p (by exact_mod_cast hn.ne')
  have hlevel : level n α p N≠0 := (level_pos n α p N hn).ne'
  have hden := (denominator_pos n α).ne'
  let A := (a).toNNReal
  have hA : (A : ℝ≥0∞)=a := ENNReal.coe_toNNReal (ha)
  have hnn : A/level n α p N=(A/(N : ℝ≥0)^p)*(denominator n α)^p := by
    unfold level
    rw [div_pow]
    field_simp
  have he : a/(level n α p N : ℝ≥0∞)=
      (a/(N : ℝ≥0∞)^p)*(denominator n α : ℝ≥0∞)^p := by
    calc
      _ = ((A/level n α p N : ℝ≥0) : ℝ≥0∞) := by rw [ENNReal.coe_div hlevel,hA]
      _ = (((A/(N : ℝ≥0)^p)*(denominator n α)^p : ℝ≥0) : ℝ≥0∞) := congrArg (fun x : ℝ≥0 => (x : ℝ≥0∞)) hnn
      _ = _ := by
        rw [ENNReal.coe_mul,ENNReal.coe_div hnp,ENNReal.coe_pow,ENNReal.coe_pow,hA]
        simp only [ENNReal.coe_natCast]
  exact he

/-- Rescaling an even-power threshold by the fixed geometric and
vector constants preserves the vanishing normalized tail estimate. -/
theorem scaled_tendsto (n : ℕ) (α : ℝ≥0) (p : ℕ) (a : ℕ → ℝ≥0∞)
    (ha : ∀ N,a N≠⊤) (hlim : Tendsto (fun N => a N/(N : ℝ≥0∞)^p) atTop (𝓝 0)) :
    Tendsto (fun N => a N/(level n α p N : ℝ≥0∞)) atTop (𝓝 0) := by
  have hl := ENNReal.Tendsto.mul_const (b := ((denominator n α : ℝ≥0∞)^p)) hlim
    (Or.inr (by finiteness))
  simp only [zero_mul] at hl
  apply hl.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  exact (scaled_eq n α p (a N) (ha N) N (lt_of_lt_of_le Nat.zero_lt_one hN)).symm

end SHEStochastic.HeatFieldThreshold
