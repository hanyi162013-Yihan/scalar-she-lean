module

public import SHEStochastic.ScalarPhysicalDriftClock
public import SHEStochastic.ScalarStoppedMildMoment
public import SHEStochastic.ScalarUnitTorusFourierEquation

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section

namespace SHEStochastic.ScalarPhysicalStoppedEquation
open MeasureTheory Set SHE SHE.PredictableL2 SHE.PredictableTimeDilation SHE.DyadicApproximation AddCircle
open UnboundedNativeHeatEquation
open scoped NNReal ENNReal

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local instance : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
local notation "r" => NativeClock.rate
local notation "hr" => NativeClock.rate_pos
local notation "clk" => clock r hr
local notation "ν" => haarAddCircle (T := 2*Real.pi)
local notation "Noise" => Lp ℝ 2 ν
local notation "φ" => NativeFourierHeatCoordinate.coordinate
local instance : MeasurableSpace Noise := borel _
local instance : BorelSpace Noise := ⟨rfl⟩

variable {Ω : Type*} [MeasurableSpace Ω]
  (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (μ : Measure Ω) [IsProbabilityMeasure μ] (H : ℝ≥0)
  {g : ℝ → ℝ} {C β : ℝ≥0} (hg : HolderWith C β g) (hβ : 0<β) (hβ₁ : β≤1)
  (b : ScalarLinearGrowthDriftField.Data H) (u₀ : RealL2)

def row (W : ℝ≥0→Ω→RealL2) (N : ℕ) (t : ℝ≥0) (ψ : ℂ →L[ℝ] ℝ) (n : ℤ) :
    ℝ≥0×Ω → Noise :=
  (ScalarStoppedHeatFourierInput.before W N t).indicator
    (fun p => Real.exp (-((r : ℝ)*((t : ℝ)-(p.1 : ℝ)))*(n : ℝ)^2) •
      StateNoiseCovariance.row ν hβ hβ₁ hg (NativeFourierHeatCoordinate.weight ψ n) (physical W p))

/-- The original scalar stochastic Fourier mild equation on the unit
torus, with physical heat generator ∂², literal Borel Bochner drift
and the original shared cylindrical noise. -/
def Equation (W : ℝ≥0→Ω→RealL2) (J : StandardTerminalIto (C := Noise) (E := ℝ) F μ H) : Prop :=
  ∀ (N : ℕ) (t : ℝ≥0),t≤H → ∀ (ψ : ℂ →L[ℝ] ℝ) (n : ℤ),
    ∃ v : Process (E := Noise) F μ H,
      v =ᵐ[energyMeasure μ H] row hg hβ hβ₁ W N t ψ n ∧
      ∀ᵐ ω ∂μ,(t : WithTop ℝ≥0)<ContinuousNormExit.exit W N ω →
        φ ψ n (W t ω-RealHeat.realHeat (t : ℝ) u₀-
          ScalarPhysicalDriftClock.physicalConvolution b W N ω t) = J.integral v ω

local notation "Fn" => filtration F (clk)
local notation "Hn" => r*H
local notation "hgn" => ScalarUnitTorusFourierClock.holder hg

private theorem row_scale (k : C(AddCircle (2*Real.pi),ℝ)) (x : Noise) :
    Real.sqrt (r : ℝ) • StateNoiseCovariance.row ν hβ hβ₁ hgn k x =
      StateNoiseCovariance.row ν hβ hβ₁ hg k x := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_smul (Real.sqrt (r : ℝ))
      (StateNoiseCovariance.row ν hβ hβ₁ hgn k x),
    StateNoiseCovariance.row_ae ν hβ hβ₁ hgn k x,
    StateNoiseCovariance.row_ae ν hβ hβ₁ hg k x] with y hs hn hp
  rw [hs,Pi.smul_apply,hn,hp]
  change Real.sqrt (r : ℝ)*(k y*(ScalarUnitTorusFourierClock.scale*g (x y)))=k y*g (x y)
  unfold ScalarUnitTorusFourierClock.scale
  field_simp [(Real.sqrt_pos.mpr (show (0 : ℝ)<r from hr)).ne']

variable (U : ℝ≥0→Ω→RealL2)
  (hU : StronglyMeasurable[(filtration F (clk)).predictable] (Function.uncurry U))
  (hc : ∀ ω,Continuous (fun t => U t ω))

local notation "W" => pullPath r hr U
local notation "vn" => ScalarStoppedHeatFourierInput.input Fn μ Hn U hU hc hgn hβ hβ₁
local notation "vp" => processIsometry F μ r hr H

/-- The normalized Brownian time Jacobian cancels exactly on the
stopped physical noise row. The age and strict state exit are unchanged. -/
theorem input_ae (N : ℕ) (t : ℝ≥0) (ψ : ℂ →L[ℝ] ℝ) (n : ℤ) :
    vp (vn N (clk t) ψ n) =ᵐ[energyMeasure μ H] row hg hβ hβ₁ W N t ψ n := by
  let v := vn N (clk t) ψ n
  filter_upwards [processIsometry_ae F μ r hr H v,
    ClockedItoAlgebra.ae_clock μ r hr H
      (ScalarStoppedHeatFourierInput.input_ae Fn μ Hn U hU hc hgn hβ hβ₁ N (clk t) ψ n)]
    with p hv hn
  change vp v p=_ at hv
  change v (clk p.1,p.2)=_ at hn
  rw [hv,hn,ScalarStoppedHeatFourierInput.row,row]
  have hh : (clk p.1,p.2)∈ScalarStoppedHeatFourierInput.before U N (clk t) ↔
      p∈ScalarStoppedHeatFourierInput.before W N t := by
    change ((clk p.1 : ℝ≥0) : ℝ)<(clk t : ℝ≥0) ∧
      ((clk p.1 : ℝ≥0) : WithTop ℝ≥0)<ContinuousNormExit.exit U N p.2 ↔
      (p.1 : ℝ)<t ∧ (p.1 : WithTop ℝ≥0)<ContinuousNormExit.exit W N p.2
    rw [ScalarPhysicalDriftClock.before_iff U hc N p.1 p.2]
    simp only [NNReal.coe_lt_coe,OrderIso.lt_iff_lt]
  by_cases hp : p∈ScalarStoppedHeatFourierInput.before W N t
  · rw [indicator_of_mem hp,indicator_of_mem (hh.mpr hp),smul_comm (Real.sqrt (r : ℝ)),
      row_scale hg hβ hβ₁]
    congr 2
    change -((r : ℝ)*(t : ℝ)-(r : ℝ)*(p.1 : ℝ))*(n : ℝ)^2 =
      -((r : ℝ)*((t : ℝ)-(p.1 : ℝ)))*(n : ℝ)^2
    ring
  · rw [indicator_of_notMem hp,indicator_of_notMem (mt hh.mp hp),smul_zero]

/-- Exact two-way clock transport of the actual stopped scalar mild
equation, including both the original drift and diffusion. -/
theorem iff_native
    (Jn : StandardTerminalIto (C := Noise) (E := ℝ) Fn μ Hn)
    (Jp : StandardTerminalIto (C := Noise) (E := ℝ) F μ H)
    (hJ : ∀ v : Process (E := Noise) Fn μ Hn,Jn.integral v=Jp.integral (vp v)) :
    Equation F μ H hg hβ hβ₁ b u₀ W Jp ↔
      ScalarStoppedMildMoment.Equation Fn μ Hn U hU hc hgn hβ hβ₁ Jn
        (ScalarPhysicalDriftClock.native b) (fun _ _ => 1) u₀ := by
  constructor
  · intro he N s hs ψ n
    let t := (clk).symm s
    have hst : clk t=s := (clk).apply_symm_apply s
    have ht : t≤H := (clk).symm.monotone hs |>.trans_eq ((clk).symm_apply_apply H)
    obtain ⟨v,hv,he⟩ := he N t ht ψ n
    have hV : v=vp (vn N (clk t) ψ n) :=
      PastItoAlgebra.eq_of_ambient_ae F μ H (hv.trans (input_ae F μ H hg hβ hβ₁ U hU hc N t ψ n).symm)
    have h0 := ScalarUnitTorusFourierClock.heat t
    have h1 := ScalarPhysicalDriftClock.convolution b U hc N
    rw [←hst]
    filter_upwards [he] with ω hω hBefore
    rw [hJ,h0,h1]
    exact hV ▸ hω ((ScalarPhysicalDriftClock.before_iff U hc N t ω).mp hBefore)
  · intro he N t ht ψ n
    refine ⟨vp (vn N (clk t) ψ n),input_ae F μ H hg hβ hβ₁ U hU hc N t ψ n,?_⟩
    filter_upwards [he N (clk t) ((clk).monotone ht) ψ n] with ω hω hBefore
    have h := hω ((ScalarPhysicalDriftClock.before_iff U hc N t ω).mpr hBefore)
    rw [hJ,ScalarUnitTorusFourierClock.heat t,ScalarPhysicalDriftClock.convolution b U hc N ω t] at h
    exact h

end SHEStochastic.ScalarPhysicalStoppedEquation
