module
public import SHE.NativeGaussianBesselCost
public import SHE.Parameters
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SHE.NativeFrozenBesselScale
open Real

def constant(s κ ρ:ℝ):ℝ:=
  NativeGaussianCircleMass.mass s (κ/128)+(κ/128)^(-s)+
    (1/ρ+1/(1/2-ρ))/Real.Gamma ρ*
      (NativeGaussianBesselCost.heatFactor*NativeGaussianCircleMass.mass s (κ/128))^(2*ρ)

theorem mass_scale {s κ r:ℝ}(hκ:0<κ)(hr:0<r):
    NativeGaussianCircleMass.mass s (κ/(128*r^2))=
      NativeGaussianCircleMass.mass s (κ/128)*r^2:=by
  unfold NativeGaussianCircleMass.mass
  have hc:0<2*Real.pi*(κ/128):=by positivity
  have he:2*Real.pi*(κ/(128*r^2))=(2*Real.pi*(κ/128))/r^2:=by field_simp
  rw [he,inv_div]
  ring

theorem tail_scale {s κ r δ ρ:ℝ}(hκ:0<κ)(hr:0<r)(hr1:r≤1)
    (hdegree:4*ρ≤s*(2-δ/2)):
    GaussianCircleMass.decay s (κ/(128*r^2)) (Real.sqrt (r^δ))≤
      (κ/128)^(-s)*r^(4*ρ):=by
  have hc:0<κ/128:=by positivity
  have hsqrt:Real.sqrt (r^δ)=r^(δ/2):=by
    rw [Real.sqrt_eq_rpow,←Real.rpow_mul hr.le]
    congr 1
    ring
  have he:(κ/(128*r^2))*Real.sqrt (r^δ)=(κ/128)*r^(-(2-δ/2)):=by
    rw [hsqrt,show κ/(128*r^2)=(κ/128)/r^2 by ring]
    have hinv:(r^2)⁻¹=r^(-(2:ℝ)):=by rw [Real.rpow_neg hr.le,Real.rpow_two]
    rw [div_eq_mul_inv,hinv,mul_assoc,←Real.rpow_add hr]
    congr 1
    ring
  unfold GaussianCircleMass.decay
  calc
    _≤((κ/(128*r^2))*Real.sqrt (r^δ))^(-s):=min_le_right _ _
    _=(κ/128)^(-s)*r^(s*(2-δ/2)):=by
      rw [he,Real.mul_rpow hc.le (Real.rpow_nonneg hr.le _),←Real.rpow_mul hr.le]
      congr 1
      ring
    _≤_:=mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hr hr1 hdegree)
      (Real.rpow_nonneg hc.le _)

/-- Polynomial cancellation of the actual Gaussian bands suffices for
the full native r^(4rho) gain; no Fourier-annulus assumption is used. -/
theorem bound {s κ r δ Λ ρ:ℝ}(hs:1<s)(hκ:0<κ)(hr:0<r)(hr1:r≤1)
    (hΛ:1≤Λ)(hρ:0<ρ)(hρhalf:ρ<1/2)(hdegree:4*ρ≤s*(2-δ/2)):
    NativeGaussianBesselCost.bound s (κ/(128*r^2)) Λ ρ
      (GaussianCircleMass.decay s (κ/(128*r^2)) (Real.sqrt (r^δ)))≤
        constant s κ ρ*r^(4*ρ):=by
  let m:=NativeGaussianCircleMass.mass s (κ/128)
  let tail:=GaussianCircleMass.decay s (κ/(128*r^2)) (Real.sqrt (r^δ))
  have hm:0<m:=NativeGaussianBesselCost.mass_pos hs (by positivity)
  have hg:0<Real.Gamma ρ:=Real.Gamma_pos_of_pos hρ
  have hh:0<1/2-ρ:=by linarith
  have hc:0≤(1/ρ+1/(1/2-ρ))/Real.Gamma ρ:=by positivity
  have ht:tail≤(κ/128)^(-s)*r^(4*ρ):=tail_scale hκ hr hr1 hdegree
  have htail:0≤tail:=GaussianCircleMass.decay_nonneg (by positivity) (Real.sqrt_nonneg _)
  have hmass:NativeGaussianCircleMass.mass s (κ/(128*r^2))≤m*r^(4*ρ):=by
    rw [mass_scale hκ hr]
    simpa only [Real.rpow_two] using mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hr hr1 (by linarith :4*ρ≤2)) hm.le
  have hpow:Λ^(-ρ)≤1:=Real.rpow_le_one_of_one_le_of_nonpos hΛ (by linarith)
  have hscale:(NativeGaussianBesselCost.heatFactor*NativeGaussianCircleMass.mass s (κ/(128*r^2)))^(2*ρ)=
      (NativeGaussianBesselCost.heatFactor*m)^(2*ρ)*r^(4*ρ):=by
    rw [mass_scale hκ hr,←mul_assoc,Real.mul_rpow
      (mul_nonneg NativeGaussianBesselCost.heatFactor_pos.le hm.le) (sq_nonneg r),
      ←Real.rpow_natCast_mul hr.le]
    congr 1
    ring
  unfold NativeGaussianBesselCost.bound
  calc
    _≤(NativeGaussianCircleMass.mass s (κ/(128*r^2))+tail)+
        (1/ρ+1/(1/2-ρ))/Real.Gamma ρ*
          (NativeGaussianBesselCost.heatFactor*NativeGaussianCircleMass.mass s (κ/(128*r^2)))^(2*ρ):=by
      have hf:=(mul_le_of_le_one_right (add_nonneg (show 0≤NativeGaussianCircleMass.mass s (κ/(128*r^2)) from by rw [mass_scale hκ hr];positivity) htail) hpow)
      dsimp only [tail] at *
      linarith
    _≤(m*r^(4*ρ)+(κ/128)^(-s)*r^(4*ρ))+
        (1/ρ+1/(1/2-ρ))/Real.Gamma ρ*
          ((NativeGaussianBesselCost.heatFactor*m)^(2*ρ)*r^(4*ρ)):=by
      rw [hscale]
      linarith
    _=constant s κ ρ*r^(4*ρ):=by unfold constant;dsimp [m];ring

theorem printed {κ r Λ β:ℝ}(hκ:0<κ)(hr:0<r)(hr1:r≤1)(hΛ:1≤Λ)
    (hβ:0<β)(hβsmall:β≤4/25):
    NativeGaussianBesselCost.bound (2-β) (κ/(128*r^2)) Λ (SHE.rho β)
      (GaussianCircleMass.decay (2-β) (κ/(128*r^2)) (Real.sqrt (r^(3*β))))≤
        constant (2-β) κ (SHE.rho β)*r^(4*SHE.rho β):=by
  have hρ:0<SHE.rho β:=by unfold SHE.rho;linarith
  have hρhalf:SHE.rho β<1/2:=by unfold SHE.rho;linarith
  apply bound (by linarith) hκ hr hr1 hΛ hρ hρhalf
  unfold SHE.rho
  nlinarith [sq_nonneg β]
end SHE.NativeFrozenBesselScale
