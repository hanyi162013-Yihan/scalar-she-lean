module
public import SHE.ActualLinearMasterClosure
public import SHE.PastReferenceBandFrequency
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace SHE.ActualReferenceMasterClosure
open Filter Topology ZeroNativeDyadicMaster

abbrev Row:=Option MasterRow

def referenceExponent(β:ℝ):ℝ:=1-β/10
def referenceDamping(β:ℝ):ℝ:=β/100

def exponent(β:ℝ):Row→ℝ
  | none=>referenceExponent β
  | some i=>SHE.rowExponent β i

def damping(β:ℝ):Row→ℝ
  | none=>referenceDamping β
  | some i=>ZeroNativeDyadicMaster.rowDamping β i

def degree(β:ℝ)(i:Row):ℝ:=1/4-rho β/2+damping β i

theorem reference_admissible{β:ℝ}(hβ:0<β)(hβ1:β≤4/25):
    0<referenceExponent β ∧ referenceExponent β<1 ∧
      0<referenceDamping β ∧ degree β none=(31/100:ℝ)*β:=by
  dsimp [referenceExponent,referenceDamping,degree,damping,rho]
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  · ring

/-- The freely chosen reference interpolation row has ample strict
margin beyond the final damping-cost target. -/
theorem reference_rate{β:ℝ}(hβ:0<β):
    degree β none/(1-referenceExponent β)=31/10:=by
  dsimp [degree,damping,referenceDamping,referenceExponent,rho]
  field_simp [hβ.ne']
  <;> ring

theorem exponents_lt_one{β:ℝ}(hβ:0<β)(hβ1:β≤4/25)(i:Row):exponent β i<1:=by
  cases i with
  | none=>dsimp [exponent,referenceExponent];linarith
  | some i=>exact ZeroNativeDyadicMaster.row_exponents_lt_one hβ hβ1 i

theorem rates_exceed_target{β:ℝ}(hβ:0<β)(hβ1:β≤4/25)(i:Row):
    (5/4:ℝ)<degree β i/(1-exponent β i):=by
  cases i with
  | none=>change (5/4:ℝ)<degree β none/(1-referenceExponent β);rw [reference_rate hβ];norm_num
  | some i=>exact ZeroNativeDyadicMaster.row_rates_exceed_target hβ hβ1 i

def rows(β Λ m:ℝ)(δ η:Row→ℝ):ℝ:=
  ∑i:Row,Λ^(-damping β i+δ i)*m^(exponent β i-η i)

theorem rows_eq(β Λ m:ℝ)(δ η:Row→ℝ):
    rows β Λ m δ η=Λ^(-referenceDamping β+δ none)*m^(referenceExponent β-η none)+
      ZeroNativeDyadicMaster.rows β Λ m (fun i=>δ (some i)) (fun i=>η (some i)):=by
  simp only [rows,Fintype.sum_option,damping,exponent,ZeroNativeDyadicMaster.rows]

theorem scaled_rows{β Λ m:ℝ}(δ η:Row→ℝ)(hΛ:0<Λ):
    energyScale β Λ*rows β Λ m δ η=
      ∑i:Row,Λ^(-(degree β i-δ i))*m^(exponent β i-η i):=by
  unfold rows energyScale
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [←mul_assoc,←Real.rpow_add hΛ]
  congr 2
  dsimp [degree]
  ring

def constant(β C:ℝ):ℝ:=
  (∑i:Row,max 1 ((((Finset.univ:Finset Row).card+1:ℝ)*(2*C^2))^(1/(1-exponent β i))))+
    ((Finset.univ:Finset Row).card+1:ℝ)*(2*C)

/-- Deterministic master ledger with the additional actual reference
mean row. This records the numerical closure once the stochastic
comparison inequality has been assembled. -/
def Bound(β C Λ K m err a b:ℝ)(δ η:Row→ℝ):Prop:=
  K≤C*(a*K+b*m+rows β Λ m δ η)+err

theorem decay {β C : ℝ}
    (hβ : 0 < β) (hβsmall : β ≤ 4/25) (hC : 0 ≤ C) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (δ η : Row → ℝ) (Λ K m err a b : ℝ),
      (∀ i, 0 ≤ δ i ∧ δ i ≤ ε ∧ 0 ≤ η i ∧ η i ≤ ε) →
      1 ≤ Λ → 0 ≤ K → 0 ≤ m →
      m ≤ C * energyScale β Λ * K → 0≤b →
      C * a + C^2 * energyScale β Λ * b ≤ 1/2 →
      err ≤ Λ ^ (-(2:ℝ)) → Bound β C Λ K m err a b δ η →
      m ≤ constant β C * Λ ^ (-(5/4:ℝ)) := by
  obtain ⟨ε,hε,hclose⟩ := finite_lossy_ledger_closes (Finset.univ : Finset Row)
    (a:=degree β) (z:=exponent β) (C:=fun _ => 2*C^2) (E:=2*C)
    (by norm_num : (0:ℝ)≤5/4) (by positivity)
    (by intro i hi; positivity)
    (fun i _ => exponents_lt_one hβ hβsmall i)
    (fun i _ => rates_exceed_target hβ hβsmall i)
  refine ⟨ε,hε,?_⟩
  intro δ η Λ K m err a b hl hΛ hK hm henergy hb0 hsmall herr hmaster
  have hΛpos : 0 < Λ := lt_of_lt_of_le zero_lt_one hΛ
  have hs : 0 ≤ energyScale β Λ := Real.rpow_nonneg hΛpos.le _
  have hs1 : energyScale β Λ ≤ 1 := by
    have hρ := (admissible_parameters β hβ hβsmall).2.1
    exact Real.rpow_le_one_of_one_le_of_nonpos hΛ (by linarith)
  have hb : 0 ≤ C * b := mul_nonneg hC hb0
  have hK' : K ≤ (C * a) * K + (C * b) * m +
      (C * rows β Λ m δ η + err) := by
    simpa only [Bound, mul_add, mul_assoc, add_assoc] using hmaster
  have hsmall' : C * a + (C * b) * (C * energyScale β Λ) ≤ 1/2 := by
    nlinarith only [hsmall]
  have hKb := absorb_two_linear_slots hK' henergy hb hsmall' hK
  have hab : m ≤ 2*C^2 * (energyScale β Λ * rows β Λ m δ η) + 2*C*energyScale β Λ*err := by
    have hh := mul_le_mul_of_nonneg_left hKb (mul_nonneg hC hs)
    nlinarith only [hh,henergy]
  have htail : 2*C*energyScale β Λ*err ≤ 2*C*Λ ^ (-(2:ℝ)) := by
    have hh := mul_le_mul_of_nonneg_left herr (by positivity : 0≤2*C*energyScale β Λ)
    have hh' := mul_le_mul_of_nonneg_left hs1 (by positivity : 0≤2*C*Λ ^ (-(2:ℝ)))
    nlinarith only [hh,hh']
  rw [scaled_rows δ η hΛpos, Finset.mul_sum] at hab
  have hrow : m ≤ ∑ i : Row, (2*C^2) * Λ ^ (-(degree β i-δ i)) * m ^ (exponent β i-η i) +
      2*C*Λ ^ (-(2:ℝ)) := by
    simp only [mul_assoc] at hab ⊢
    linarith only [hab,htail]
  have he : 2*C*Λ ^ (-(2:ℝ)) ≤ 2*C*Λ ^ (-(5/4:ℝ)) :=
    mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hΛ (by norm_num)) (by positivity)
  exact hclose δ η m Λ (2*C*Λ ^ (-(2:ℝ))) (fun i _ => hl i) hm hΛ he hrow


/-- The actual linear coefficient need only tend to zero after the
proved energy scaling; no particular unperturbed polynomial rate is
required. The analytic comparison remains an explicit premise. -/
theorem cost_limit {β C : ℝ}
    (hβ : 0 < β) (hβsmall : β ≤ 4/25) (hC : 0 ≤ C) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (δ η : Row → ℝ) (K m err a b : ℝ → ℝ),
      (∀ i, 0 ≤ δ i ∧ δ i ≤ ε ∧ 0 ≤ η i ∧ η i ≤ ε) →
      Tendsto (fun Λ=>C*a Λ+C^2*energyScale β Λ*b Λ) atTop (𝓝 (0:ℝ)) →
      (∀ᶠ Λ in atTop,0≤b Λ) →
      (∀ᶠ Λ in atTop, 0 ≤ K Λ ∧ 0 ≤ m Λ ∧
        m Λ ≤ C * energyScale β Λ * K Λ ∧ err Λ ≤ Λ ^ (-(2:ℝ)) ∧
        Bound β C Λ (K Λ) (m Λ) (err Λ) (a Λ) (b Λ) δ η) →
      Tendsto (fun Λ => Λ ^ (2:ℕ) * m Λ ^ (2:ℕ)) atTop (𝓝 0) := by
  obtain ⟨ε,hε,hclose⟩ := decay hβ hβsmall hC
  refine ⟨ε,hε,?_⟩
  intro δ η K m err a b hl hcoeff hbfull hfull
  have hsmall := hcoeff.eventually
    (gt_mem_nhds (by norm_num : (0:ℝ)<1/2))
  apply damping_cost_tends_to_zero (p:=(5/2:ℝ)) (C:=constant β C ^ (2:ℕ)) (by norm_num)
  filter_upwards [hfull,hsmall,eventually_ge_atTop (1:ℝ),hbfull] with Λ hΛ hs hΛ1 hb
  have hm := hclose δ η Λ (K Λ) (m Λ) (err Λ) (a Λ) (b Λ) hl hΛ1 hΛ.1 hΛ.2.1 hΛ.2.2.1 hb
    hs.le hΛ.2.2.2.1 hΛ.2.2.2.2
  refine ⟨sq_nonneg _, ?_⟩
  have hp := pow_le_pow_left₀ hΛ.2.1 hm 2
  have hΛ0 : 0 ≤ Λ := by linarith
  calc
    _ ≤ (constant β C * Λ ^ (-(5/4:ℝ))) ^ (2:ℕ) := hp
    _ = _ := by rw [mul_pow, ← Real.rpow_mul_natCast hΛ0]; norm_num
end SHE.ActualReferenceMasterClosure
