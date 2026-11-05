module

public import SHE.DyadicRemainderTail
public import SHE.RemainderBandCutoff

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace SHE.DyadicMasterRemainder
open Real Filter Topology

/-- The lower band cutoff can satisfy both every physical small-window
condition and the actual damping frequency threshold. -/
theorem exists_cutoff (P:CanonicalCovariance.ProfileParameters) (H:ℝ) (hH:0<H)
    (N:ℕ) (Λ:ℝ):
    ∃J:ℕ,Λ^(1/4:ℝ)≤(2:ℝ)^J ∧ ∀j,J≤j→
      (RemainderBandSpans.span P.exponent j:ℝ)≤H ∧
      (RemainderBandSpans.span P.exponent j:ℝ)≤P.horizon ∧
      ∀l,l<N→(RemainderBandSpans.span P.exponent j:ℝ)≤PhysicalScoreChain.uniformHorizon 1 l:=by
  obtain ⟨J0,hJ0⟩:=RemainderBandCutoff.exists_cutoff P H hH N
  obtain ⟨J1,hJ1⟩:=pow_unbounded_of_one_lt (Λ^(1/4:ℝ)) (by norm_num:(1:ℝ)<2)
  refine ⟨max J0 J1,?_,fun j hj=>hJ0 j ((le_max_left _ _).trans hj)⟩
  exact hJ1.le.trans (pow_le_pow_right₀ (by norm_num:(1:ℝ)≤2) (le_max_right _ _))

theorem threshold_energy {Λ:ℝ} (hΛ:0<Λ) (J:ℕ)
    (hJ:Λ^(1/4:ℝ)≤(2:ℝ)^J):
    ((2:ℝ)^J)^(-8:ℝ)≤Λ^(-2:ℝ):=by
  have hh:=Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hΛ (1/4:ℝ)) hJ (by norm_num:(-8:ℝ)≤0)
  rw [←Real.rpow_mul hΛ.le] at hh
  simpa only [show (1/4:ℝ)*(-8)=(-2) by ring] using hh

/-- Square-root conversion retains the genuine coupled energy power.
It applies directly to the actual retained-output Hilbert tail energy. -/
theorem rms_bound {E C Λ ρ M χ:ℝ} (hE:0≤E) (hC:0≤C) (hΛ:0<Λ) (hM:0≤M)
    (he:E≤Λ^(-ρ)*C*(256/225:ℝ)*Λ^(-2:ℝ)*M^χ):
    sqrt E≤(16/15:ℝ)*sqrt C*Λ^(-ρ/2-1)*(sqrt M)^χ:=by
  let A:ℝ:=(16/15:ℝ)*sqrt C*Λ^(-ρ/2-1)*(sqrt M)^χ
  have hA:0≤A:=by dsimp only[A];positivity
  have hpow:(Λ^(-ρ/2-1))^2=Λ^(-ρ-2):=by
    rw [←Real.rpow_mul_natCast hΛ.le]
    congr 1
    ring
  have hmean:((sqrt M)^χ)^2=M^χ:=by
    rw [←Real.rpow_natCast,←Real.rpow_mul (sqrt_nonneg M),sqrt_eq_rpow,
      ←Real.rpow_mul hM]
    congr 1
    ring
  have hs:A^2=Λ^(-ρ)*C*(256/225:ℝ)*Λ^(-2:ℝ)*M^χ:=by
    dsimp only[A]
    rw [mul_pow,mul_pow,mul_pow,sq_sqrt hC,hpow,hmean]
    rw [show -ρ-2=(-ρ)+(-2) by ring,Real.rpow_add hΛ]
    ring
  have hEE:(sqrt E)^2≤A^2:=by rw [sq_sqrt hE,hs];exact he
  change sqrt E≤A
  nlinarith [sqrt_nonneg E]

end SHE.DyadicMasterRemainder
