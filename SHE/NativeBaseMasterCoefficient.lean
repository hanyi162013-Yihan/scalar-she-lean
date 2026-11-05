module
public import SHE.ActualReferenceMasterClosure
public import SHE.GammaDyadicWindowScale
public import SHE.StateBands
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SHE.NativeBaseMasterCoefficient
open Real Filter Topology
open scoped BigOperators

/-- The exact four scalar pieces in the actual finite Gaussian RMS bound. -/
def value(β Λ m K:ℝ)(J:ℕ)(Clow Cfr Cin Cgamma Cleaf:ℝ):ℝ:=
  Clow*Λ^(-(SHE.rho β)/2)*((2:ℝ)^J)^(1-β)*m+
  Cfr*(sqrt (Cin*m^2))^(SHE.alpha β)+
  Cgamma*(StateBands.geometricConstant β*Λ^(-β/4)*K+
    StateBands.rootConstant (SHE.alpha β)*m^(SHE.alpha β)+
    StateBands.geometricConstant (SHE.qGamma β)*Λ^(-SHE.qGamma β/4)*m)+
  Cleaf*Λ^(-(SHE.rho β)/2)*((2:ℝ)^(J+1))^(-4:ℝ)*(m^2)^(β/4)

def constant(β Clow Cfr Cin Cgamma Cleaf:ℝ):ℝ:=
  1+|Clow*2^(1-β)|+|Cfr*(sqrt Cin)^(SHE.alpha β)+Cgamma*StateBands.rootConstant (SHE.alpha β)|+
  |Cgamma*StateBands.geometricConstant β|+|Cgamma*StateBands.geometricConstant (SHE.qGamma β)|+|Cleaf|

theorem constant_pos(β Clow Cfr Cin Cgamma Cleaf:ℝ):
    0<constant β Clow Cfr Cin Cgamma Cleaf:=by
  unfold constant
  positivity

private theorem rows_formula(β Λ m:ℝ):ActualReferenceMasterClosure.rows β Λ m 0 0=
    Λ^(-β/100)*m^(1-β/10)+m^(SHE.alpha β)+m^(SHE.chi β)+
      Λ^(-(SHE.rho β)/2-1)*m^(SHE.chiR β):=by
  simp only [ActualReferenceMasterClosure.rows_eq,Pi.zero_apply,sub_zero,add_zero,
    ActualReferenceMasterClosure.referenceDamping,ActualReferenceMasterClosure.referenceExponent,
    ZeroNativeDyadicMaster.rows]
  simp only [show (Finset.univ:Finset SHE.MasterRow)=
    {.gaussian,.native,.remainder} from rfl,Finset.sum_insert,Finset.mem_insert,
    Finset.mem_singleton,reduceCtorEq,or_self,not_false_eq_true,Finset.sum_singleton,
    ZeroNativeDyadicMaster.rowDamping,SHE.rowExponent,neg_zero,rpow_zero,one_mul]
  rw [show -(SHE.rho β/2+1)=-(SHE.rho β)/2-1 by ring]
  ring

/-- The low block, frozen field, complete Gamma and finite-depth leaf
fit the actual four-row ledger with constants fixed before damping,
energy, smoothing index and the common cutoff. -/
theorem cap{β Λ m K:ℝ}(J:ℕ)(Clow Cfr Cin Cgamma Cleaf:ℝ)
    (hβ:0<β)(hβsmall:β≤4/25)(hΛ:1≤Λ)(hm:0≤m)(hK:0≤K)
    (hClow:0≤Clow)(hCfr:0≤Cfr)(hCin:0≤Cin)(hCgamma:0≤Cgamma)(hCleaf:0≤Cleaf)
    (hlow:(2:ℝ)^J≤2*Λ^(1/4:ℝ))(hhigh:Λ^(1/4:ℝ)≤(2:ℝ)^(J+1)):
    value β Λ m K J Clow Cfr Cin Cgamma Cleaf≤
      constant β Clow Cfr Cin Cgamma Cleaf*
        (Λ^(-β/4)*K+SHE.linearM β (SHE.depth β) Λ*m+
          ActualReferenceMasterClosure.rows β Λ m 0 0):=by
  have hΛ0:0<Λ:=zero_lt_one.trans_le hΛ
  let B:=Λ^(-(SHE.rho β)/2+(1-β)/4)
  let D:=Λ^(-SHE.qGamma β/4)
  let A:=Λ^(-β/4)*K
  let G:=m^(SHE.alpha β)
  let R:=Λ^(-(SHE.rho β)/2-1)*m^(SHE.chiR β)
  let C:=constant β Clow Cfr Cin Cgamma Cleaf
  have hC:0≤C:=(constant_pos β Clow Cfr Cin Cgamma Cleaf).le
  have hb:0≤B:=rpow_nonneg hΛ0.le _
  have hd:0≤D:=rpow_nonneg hΛ0.le _
  have ha:0≤A:=mul_nonneg (rpow_nonneg hΛ0.le _) hK
  have hg:0≤G:=rpow_nonneg hm _
  have hr:0≤R:=mul_nonneg (rpow_nonneg hΛ0.le _) (rpow_nonneg hm _)
  have hlowpow:((2:ℝ)^J)^(1-β)≤2^(1-β)*Λ^((1-β)/4):=by
    calc
      _≤(2*Λ^(1/4:ℝ))^(1-β):=rpow_le_rpow (by positivity) hlow (by linarith)
      _=_:=by rw [mul_rpow (by norm_num:(0:ℝ)≤2) (rpow_nonneg hΛ0.le _),←rpow_mul hΛ0.le];congr 1;ring
  have hlo:Clow*Λ^(-(SHE.rho β)/2)*((2:ℝ)^J)^(1-β)*m≤(Clow*2^(1-β))*(B*m):=by
    calc
      _≤Clow*Λ^(-(SHE.rho β)/2)*(2^(1-β)*Λ^((1-β)/4))*m:=by gcongr
      _=_:=by dsimp [B];rw [show Clow*Λ^(-(SHE.rho β)/2)*(2^(1-β)*Λ^((1-β)/4))*m=
        (Clow*2^(1-β))*(Λ^(-(SHE.rho β)/2)*Λ^((1-β)/4))*m by ring,←rpow_add hΛ0];ring
  have hfreq:((2:ℝ)^(J+1))^(-4:ℝ)≤Λ^(-1:ℝ):=by
    calc
      _≤(Λ^(1/4:ℝ))^(-4:ℝ):=rpow_le_rpow_of_nonpos (rpow_pos_of_pos hΛ0 _) hhigh (by norm_num)
      _=_:=by rw [←rpow_mul hΛ0.le];norm_num
  have hmleaf:(m^2)^(β/4)=m^(SHE.chiR β):=by
    rw [←rpow_natCast_mul hm]
    congr 1
    dsimp [SHE.chiR]
    ring
  have hle:Cleaf*Λ^(-(SHE.rho β)/2)*((2:ℝ)^(J+1))^(-4:ℝ)*(m^2)^(β/4)≤Cleaf*R:=by
    rw [hmleaf]
    calc
      _≤Cleaf*Λ^(-(SHE.rho β)/2)*Λ^(-1:ℝ)*m^(SHE.chiR β):=by gcongr
      _=_:=by
        dsimp [R]
        rw [show Cleaf*Λ^(-(SHE.rho β)/2)*Λ^(-1:ℝ)*m^(SHE.chiR β)=
          Cleaf*(Λ^(-(SHE.rho β)/2)*Λ^(-1:ℝ))*m^(SHE.chiR β) by ring,←rpow_add hΛ0]
        rw [show -(SHE.rho β)/2+(-1)=-(SHE.rho β)/2-1 by ring]
        ring
  have hf:Cfr*(sqrt (Cin*m^2))^(SHE.alpha β)=Cfr*(sqrt Cin)^(SHE.alpha β)*G:=by
    rw [sqrt_mul hCin,sqrt_sq hm,mul_rpow (sqrt_nonneg _) hm]
    dsimp [G]
    ring
  have hcoef0:Clow*2^(1-β)≤C:=by dsimp [C,constant];nlinarith [le_abs_self (Clow*2^(1-β)),abs_nonneg (Cfr*(sqrt Cin)^(SHE.alpha β)+Cgamma*StateBands.rootConstant (SHE.alpha β)),abs_nonneg (Cgamma*StateBands.geometricConstant β),abs_nonneg (Cgamma*StateBands.geometricConstant (SHE.qGamma β)),abs_nonneg Cleaf]
  have hcoef1:Cfr*(sqrt Cin)^(SHE.alpha β)+Cgamma*StateBands.rootConstant (SHE.alpha β)≤C:=by dsimp [C,constant];nlinarith [le_abs_self (Cfr*(sqrt Cin)^(SHE.alpha β)+Cgamma*StateBands.rootConstant (SHE.alpha β)),abs_nonneg (Clow*2^(1-β)),abs_nonneg (Cgamma*StateBands.geometricConstant β),abs_nonneg (Cgamma*StateBands.geometricConstant (SHE.qGamma β)),abs_nonneg Cleaf]
  have hcoef2:Cgamma*StateBands.geometricConstant β≤C:=by dsimp [C,constant];nlinarith [le_abs_self (Cgamma*StateBands.geometricConstant β),abs_nonneg (Clow*2^(1-β)),abs_nonneg (Cfr*(sqrt Cin)^(SHE.alpha β)+Cgamma*StateBands.rootConstant (SHE.alpha β)),abs_nonneg (Cgamma*StateBands.geometricConstant (SHE.qGamma β)),abs_nonneg Cleaf]
  have hcoef3:Cgamma*StateBands.geometricConstant (SHE.qGamma β)≤C:=by dsimp [C,constant];nlinarith [le_abs_self (Cgamma*StateBands.geometricConstant (SHE.qGamma β)),abs_nonneg (Clow*2^(1-β)),abs_nonneg (Cfr*(sqrt Cin)^(SHE.alpha β)+Cgamma*StateBands.rootConstant (SHE.alpha β)),abs_nonneg (Cgamma*StateBands.geometricConstant β),abs_nonneg Cleaf]
  have hcoef4:Cleaf≤C:=by dsimp [C,constant];nlinarith [le_abs_self Cleaf,abs_nonneg (Clow*2^(1-β)),abs_nonneg (Cfr*(sqrt Cin)^(SHE.alpha β)+Cgamma*StateBands.rootConstant (SHE.alpha β)),abs_nonneg (Cgamma*StateBands.geometricConstant β),abs_nonneg (Cgamma*StateBands.geometricConstant (SHE.qGamma β))]
  have hmid:value β Λ m K J Clow Cfr Cin Cgamma Cleaf≤C*(A+(B+D)*m+G+R):=by
    unfold value
    rw [hf]
    have h0:=mul_le_mul_of_nonneg_right hcoef0 (mul_nonneg hb hm)
    have h1:=mul_le_mul_of_nonneg_right hcoef1 hg
    have h2:=mul_le_mul_of_nonneg_right hcoef2 ha
    have h3:=mul_le_mul_of_nonneg_right hcoef3 (mul_nonneg hd hm)
    have h4:=mul_le_mul_of_nonneg_right hcoef4 hr
    dsimp only [A,G,D] at *
    nlinarith only [hlo,hle,h0,h1,h2,h3,h4]
  have hlinear:B+D≤SHE.linearM β (SHE.depth β) Λ:=by
    unfold SHE.linearM
    dsimp only [B,D]
    have hsum:0≤∑j∈Finset.Icc 2 (SHE.depth β+1),Λ^(-SHE.p β j/4):=
      Finset.sum_nonneg (fun _ _=>rpow_nonneg hΛ0.le _)
    have hz:=mul_nonneg (rpow_nonneg hΛ0.le (-(SHE.rho β)/2)) hsum
    nlinarith [rpow_nonneg hΛ0.le (-SHE.qProfile β 2/4)]
  have hrows:G+R≤ActualReferenceMasterClosure.rows β Λ m 0 0:=by
    rw [rows_formula]
    dsimp [G,R]
    nlinarith [mul_nonneg (rpow_nonneg hΛ0.le (-β/100)) (rpow_nonneg hm (1-β/10)),rpow_nonneg hm (SHE.chi β)]
  apply hmid.trans
  apply mul_le_mul_of_nonneg_left _ hC
  nlinarith only [mul_le_mul_of_nonneg_right hlinear hm,hrows]

theorem scaled_linear_limit{β:ℝ}(hβ:0<β)(hβsmall:β≤4/25):
    Tendsto (fun Λ=>SHE.energyScale β Λ*SHE.linearM β (SHE.depth β) Λ) atTop (𝓝 0):=
  SHE.scaled_linearM_tends_zero hβ hβsmall _

theorem gamma_linear_limit{β:ℝ}(hβ:0<β):
    Tendsto (fun Λ:ℝ=>Λ^(-β/4)) atTop (𝓝 0):=by
  exact SHE.rpow_tends_zero_of_neg (by linarith)

/-- Direct specialization to the literal actual energy E, with the
same numerical constants and no replacement of the true current mass. -/
theorem energy_cap{β Λ E K:ℝ}(J:ℕ)(Clow Cfr Cin Cgamma Cleaf:ℝ)
    (hβ:0<β)(hβsmall:β≤4/25)(hΛ:1≤Λ)(hE:0≤E)(hK:0≤K)
    (hClow:0≤Clow)(hCfr:0≤Cfr)(hCin:0≤Cin)(hCgamma:0≤Cgamma)(hCleaf:0≤Cleaf)
    (hlow:(2:ℝ)^J≤2*Λ^(1/4:ℝ))(hhigh:Λ^(1/4:ℝ)≤(2:ℝ)^(J+1)):
    Clow*Λ^(-(SHE.rho β)/2)*((2:ℝ)^J)^(1-β)*sqrt E+
    Cfr*(sqrt (Cin*E))^(SHE.alpha β)+
    Cgamma*(StateBands.geometricConstant β*Λ^(-β/4)*K+
      StateBands.rootConstant (SHE.alpha β)*(sqrt E)^(SHE.alpha β)+
      StateBands.geometricConstant (SHE.qGamma β)*Λ^(-SHE.qGamma β/4)*sqrt E)+
    Cleaf*Λ^(-(SHE.rho β)/2)*((2:ℝ)^(J+1))^(-4:ℝ)*E^(β/4)≤
      constant β Clow Cfr Cin Cgamma Cleaf*
        (Λ^(-β/4)*K+SHE.linearM β (SHE.depth β) Λ*sqrt E+
          ActualReferenceMasterClosure.rows β Λ (sqrt E) 0 0):=by
  simpa only [value,sq_sqrt hE] using cap J Clow Cfr Cin Cgamma Cleaf
    hβ hβsmall hΛ (sqrt_nonneg E) hK hClow hCfr hCin hCgamma hCleaf hlow hhigh

end SHE.NativeBaseMasterCoefficient
