module

public import SHE.RawTraceTimeEnvelope

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1700000
noncomputable section

namespace SHE.RawTraceTimeEnvelope
open Real SignedKernelTruncation NormalizedKernelSplit

def goodAmplitude (J ρ η R D δ w : ℝ) : ℝ :=
  sqrt (2*J*nativeCostConstant ρ*logLossConstant η)*R*D*
    δ^(-freshExponent ρ η)*w^((ρ+η)/2)

def badAmplitude (U C D δ lam tail : ℝ) : ℝ :=
  sqrt (8*U*C*heatMassConstant)*D*δ^(-(1/2:ℝ))*lam^(-tail/2)

theorem goodAmplitude_nonneg (J ρ η : ℝ) {R D δ w : ℝ}
    (hR : 0 ≤ R) (hD : 0 ≤ D) (hδ : 0 ≤ δ) (hw : 0 ≤ w) :
    0 ≤ goodAmplitude J ρ η R D δ w :=
  mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (sqrt_nonneg _) hR) hD)
    (Real.rpow_nonneg hδ _)) (Real.rpow_nonneg hw _)

theorem badAmplitude_nonneg (U C tail : ℝ) {D δ lam : ℝ}
    (hD : 0 ≤ D) (hδ : 0 ≤ δ) (hlam : 0 ≤ lam) :
    0 ≤ badAmplitude U C D δ lam tail :=
  mul_nonneg (mul_nonneg (mul_nonneg (sqrt_nonneg _) hD)
    (Real.rpow_nonneg hδ _)) (Real.rpow_nonneg hlam _)

theorem goodAmplitude_sq {J η δ w : ℝ} (hJ : 0 ≤ J) (hη : 0 < η)
    (hδ : 0 < δ) (hw : 0 < w) (ρ R D : ℝ) :
    (goodAmplitude J ρ η R D δ w)^2=
      2*J*nativeCostConstant ρ*logLossConstant η*R^2*D^2*δ^(-1-ρ-η)*w^(ρ+η) := by
  have hc : 0 ≤ 2*J*nativeCostConstant ρ*logLossConstant η :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hJ) (nativeCostConstant_pos ρ).le)
      (logLossConstant_pos hη).le
  have hd : (δ^(-freshExponent ρ η))^2=δ^(-1-ρ-η) := by
    rw [←Real.rpow_mul_natCast hδ.le]
    congr 1
    unfold freshExponent
    ring
  have hw' : (w^((ρ+η)/2))^2=w^(ρ+η) := by
    rw [←Real.rpow_mul_natCast hw.le]
    congr 1
    ring
  simp only [goodAmplitude,mul_pow,Real.sq_sqrt hc,hd,hw']

theorem badAmplitude_sq {U C δ lam : ℝ} (hU : 0 ≤ U) (hC : 0 ≤ C)
    (hδ : 0 < δ) (hlam : 0 < lam) (D tail : ℝ) :
    (badAmplitude U C D δ lam tail)^2=
      8*U*C*heatMassConstant*D^2*δ^(-1:ℝ)*lam^(-tail) := by
  have hc : 0 ≤ 8*U*C*heatMassConstant :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hU) hC) heatMassConstant_pos.le
  have hd : (δ^(-(1/2:ℝ)))^2=δ^(-1:ℝ) := by
    rw [←Real.rpow_mul_natCast hδ.le]
    norm_num
  have hl : (lam^(-tail/2))^2=lam^(-tail) := by
    rw [←Real.rpow_mul_natCast hlam.le]
    congr 1
    ring
  simp only [badAmplitude,mul_pow,Real.sq_sqrt hc,hd,hl]

/-- The signed trace estimate has a genuine L1 old-time RMS envelope.
The actual input energy stays correlated with the current process and
is never replaced by a product of unrelated expectations. -/
theorem energy_envelope {J η δ w U C R D lam E I : ℝ}
    (hJ : 0 ≤ J) (hη : 0 < η) (hδ : 0 < δ) (hδw : δ ≤ w)
    (hU : 0 ≤ U) (hC : 0 ≤ C) (hR : 0 ≤ R) (hD : 0 ≤ D)
    (hlam : 0 < lam) (hE : 0 ≤ E) (ρ tail : ℝ)
    (hI : I ≤ 2*goodCost J ρ δ w R (heatAmplitude D δ w)*E+
      8*U*C*heatMassConstant*D^2*δ^(-1:ℝ)*lam^(-tail)) :
    I ≤ (goodAmplitude J ρ η R D δ w*sqrt E+badAmplitude U C D δ lam tail)^2 := by
  have hw : 0 < w := hδ.trans_le hδw
  have hg : 2*goodCost J ρ δ w R (heatAmplitude D δ w)*E ≤
      (goodAmplitude J ρ η R D δ w*sqrt E)^2 := by
    rw [mul_pow,Real.sq_sqrt hE,goodAmplitude_sq hJ hη hδ hw]
    have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (goodCost_loss hδ hδw hη hJ ρ R D) (by norm_num : 0 ≤ (2:ℝ))) hE
    convert! hh using 1 <;> ring
  have hbad := badAmplitude_sq hU hC hδ hlam D tail
  have hga : 0 ≤ goodAmplitude J ρ η R D δ w*sqrt E :=
    mul_nonneg (goodAmplitude_nonneg J ρ η hR hD hδ.le hw.le) (sqrt_nonneg E)
  have hba : 0 ≤ badAmplitude U C D δ lam tail := badAmplitude_nonneg U C tail hD hδ.le hlam.le
  calc
    I ≤ (goodAmplitude J ρ η R D δ w*sqrt E)^2+badAmplitude U C D δ lam tail^2 :=
      hI.trans (add_le_add hg (le_of_eq hbad.symm))
    _ ≤ _ := by nlinarith [mul_nonneg hga hba]

def freshDegree (ρ η : ℝ) : ℝ := 1-freshExponent ρ η

theorem freshDegree_pos {ρ η : ℝ} (h : ρ+η < 1) : 0 < freshDegree ρ η := by
  unfold freshDegree
  linarith [freshExponent_lt_one h]

theorem freshDegree_le_one {ρ η : ℝ} (hρ : 0 ≤ ρ) (hη : 0 ≤ η) : freshDegree ρ η ≤ 1 := by
  unfold freshDegree
  linarith [freshExponent_pos hρ hη]

theorem goodAmplitude_half_gap (J ρ η R D w : ℝ) {g : ℝ} (hg : 0 < g) :
    goodAmplitude J ρ η R D (g/2) w=
      (2:ℝ)^(freshExponent ρ η)*goodAmplitude J ρ η R D g w := by
  have hd : (g/2)^(-freshExponent ρ η)=(2:ℝ)^(freshExponent ρ η)*g^(-freshExponent ρ η) := by
    rw [Real.div_rpow hg.le (by norm_num : 0 ≤ (2:ℝ)),div_eq_mul_inv,
      ←Real.rpow_neg (by norm_num : 0 ≤ (2:ℝ)),neg_neg]
    ring
  unfold goodAmplitude
  rw [hd]
  ring

theorem badAmplitude_half_gap (U C D lam tail : ℝ) {g : ℝ} (hg : 0 < g) :
    badAmplitude U C D (g/2) lam tail=
      (2:ℝ)^(1/2:ℝ)*badAmplitude U C D g lam tail := by
  have hd : (g/2)^(-(1/2:ℝ))=(2:ℝ)^(1/2:ℝ)*g^(-(1/2:ℝ)) := by
    rw [Real.div_rpow hg.le (by norm_num : 0 ≤ (2:ℝ)),div_eq_mul_inv,
      ←Real.rpow_neg (by norm_num : 0 ≤ (2:ℝ)),neg_neg]
    ring
  unfold badAmplitude
  rw [hd]
  ring

/-- The explicit outside output gain cancels exactly the reserved
fresh-gap loss after the genuine ordered-time integral. -/
theorem integrated_degree (ρ η a : ℝ) (b : ℕ) :
    freshDegree ρ η+a*(b:ℝ)-1+(ρ+η)/2=a*(b:ℝ)-1/2 := by
  unfold freshDegree freshExponent
  ring

end SHE.RawTraceTimeEnvelope
